use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        Operand::{Constant, Copy, Move},
        TerminatorKind,
    },
    ty::{TyKind, TypingEnv},
};

use std::collections::{HashMap, HashSet};

use super::{block::Term, graph::*, *};

impl<'tcx> MopGraph<'tcx> {
    pub fn split_check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        /* duplicate the status before visiting a path; */
        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.constants.clone();
        let backup_alias_set = self.alias_set.clone();
        self.check(bb_idx, fn_map, recursion_set);
        /* restore after visit */
        self.alias_set = backup_alias_set;
        self.values = backup_values;
        self.constants = backup_constant;
    }
    pub fn split_check_with_cond(
        &mut self,
        bb_idx: usize,
        path_discr_id: usize,
        path_discr_val: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        /* duplicate the status before visiting a path; */
        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.constants.clone();
        let backup_alias_set = self.alias_set.clone();
        /* add control-sensitive indicator to the path status */
        self.constants.insert(path_discr_id, path_discr_val);
        self.check(bb_idx, fn_map, recursion_set);
        /* restore after visit */
        self.alias_set = backup_alias_set;
        self.values = backup_values;
        self.constants = backup_constant;
    }

    // the core function of the alias analysis algorithm.
    pub fn check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopAAResultMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        self.visit_times += 1;
        if self.visit_times > VISIT_LIMIT {
            return;
        }
        let scc_idx = self.scc_indices[bb_idx];
        let cur_block = self.blocks[bb_idx].clone();
        self.alias_bb(self.scc_indices[bb_idx]);
        self.alias_bbcall(self.scc_indices[bb_idx], fn_map, recursion_set);

        if bb_idx == scc_idx {
            let mut paths_in_scc = vec![];

            /* Handle cases if the current block is a merged scc block with sub block */
            self.calculate_scc_order(
                scc_idx,
                bb_idx,
                &mut cur_block.dominated_scc_bbs.clone(),
                &mut vec![],
                &mut HashMap::new(),
                &mut HashSet::new(),
                &mut paths_in_scc,
            );

            let backup_values = self.values.clone(); // duplicate the status when visiteding different paths;
            let backup_constant = self.constants.clone();
            let backup_alias_set = self.alias_set.clone();
            let backup_fn_map = fn_map.clone();
            let backup_recursion_set = recursion_set.clone();
            for each_path in paths_in_scc {
                self.alias_set = backup_alias_set.clone();
                self.values = backup_values.clone();
                self.constants = backup_constant.clone();
                *fn_map = backup_fn_map.clone();
                *recursion_set = backup_recursion_set.clone();

                if !each_path.is_empty() {
                    for idx in each_path {
                        self.alias_bb(idx);
                        self.alias_bbcall(idx, fn_map, recursion_set);
                    }
                }
            }

            match cur_block.next.len() {
                0 => {
                    let results_nodes = self.values.clone();
                    self.merge_results(results_nodes);
                    return;
                }
                1 => {
                    /*
                     * Equivalent to self.check(cur_block.next[0]..);
                     * We cannot use [0] for FxHashSet.
                     */
                    for next in cur_block.next {
                        self.check(next, fn_map, recursion_set);
                    }
                    return;
                }
                _ => {}
            }
        }

        /* Begin: handle the SwitchInt statement. */
        let mut single_target = false;
        let mut sw_val = 0;
        let mut sw_target = 0; // Single target
        let mut path_discr_id = 0; // To avoid analyzing paths that cannot be reached with one enum type.
        let mut sw_targets = None; // Multiple targets of SwitchInt
        if let Term::Switch(switch) = cur_block.terminator
        //if let Some(switch) = cur_block.switch
            && cur_block.dominated_scc_bbs.is_empty()
        {
            if let TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } = switch.kind
            {
                match discr {
                    Copy(p) | Move(p) => {
                        let place = self.projection(false, *p);
                        let local_decls = &self.tcx.optimized_mir(self.def_id).local_decls;
                        let place_ty = (*p).ty(local_decls, self.tcx);
                        rap_debug!("place {:?}", place);
                        match place_ty.ty.kind() {
                            TyKind::Bool => {
                                if let Some(constant) = self.constants.get(&place) {
                                    if *constant != usize::MAX {
                                        single_target = true;
                                        sw_val = *constant;
                                    }
                                }
                                path_discr_id = place;
                                sw_targets = Some(targets.clone());
                            }
                            _ => {
                                if let Some(father) =
                                    self.discriminants.get(&self.values[place].local)
                                {
                                    if let Some(constant) = self.constants.get(father) {
                                        if *constant != usize::MAX {
                                            single_target = true;
                                            sw_val = *constant;
                                        }
                                    }
                                    if self.values[place].local == place {
                                        path_discr_id = *father;
                                        sw_targets = Some(targets.clone());
                                    }
                                }
                            }
                        }
                    }
                    Constant(c) => {
                        single_target = true;
                        let ty_env = TypingEnv::post_analysis(self.tcx, self.def_id);
                        if let Some(val) = c.const_.try_eval_target_usize(self.tcx, ty_env) {
                            sw_val = val as usize;
                        }
                    }
                }
                if single_target {
                    /* Find the target based on the value;
                     * Since sw_val is a const, only one target is reachable.
                     * Filed 0 is the value; field 1 is the real target.
                     */
                    for iter in targets.iter() {
                        if iter.0 as usize == sw_val {
                            sw_target = iter.1.as_usize();
                            break;
                        }
                    }
                    /* No target found, choose the default target.
                     * The default targets is not included within the iterator.
                     * We can only obtain the default target based on the last item of all_targets().
                     */
                    if sw_target == 0 {
                        let all_target = targets.all_targets();
                        sw_target = all_target[all_target.len() - 1].as_usize();
                    }
                }
            }
        }
        /* End: finish handling SwitchInt */
        // fixed path since a constant switchInt value
        if single_target {
            self.check(sw_target, fn_map, recursion_set);
        } else {
            // Other cases in switchInt terminators
            if let Some(targets) = sw_targets {
                for iter in targets.iter() {
                    if self.visit_times > VISIT_LIMIT {
                        continue;
                    }
                    let next_index = iter.1.as_usize();
                    let path_discr_val = iter.0 as usize;
                    self.split_check_with_cond(
                        next_index,
                        path_discr_id,
                        path_discr_val,
                        fn_map,
                        recursion_set,
                    );
                }
                let all_targets = targets.all_targets();
                let next_index = all_targets[all_targets.len() - 1].as_usize();
                let path_discr_val = usize::MAX; // to indicate the default path;
                self.split_check_with_cond(
                    next_index,
                    path_discr_id,
                    path_discr_val,
                    fn_map,
                    recursion_set,
                );
            } else {
                for i in cur_block.next {
                    if self.visit_times > VISIT_LIMIT {
                        continue;
                    }
                    let next_index = i;
                    self.split_check(next_index, fn_map, recursion_set);
                }
            }
        }
    }

    ///This function performs a DFS traversal across the SCC, extracting all possible orderings
    /// that respect the control-flow structure and SwitchInt branching, taking into account
    /// enum discriminants and constant branches.
    pub fn calculate_scc_order(
        &mut self,
        start: usize,
        cur: usize,
        scc: &Vec<usize>,
        path: &mut Vec<usize>,
        stacked_discriminants: &mut HashMap<usize, usize>,
        visited: &mut HashSet<usize>, // for cycle detection.
        paths_in_scc: &mut Vec<Vec<usize>>,
    ) {
        // If we have returned to the start and the path is non-empty, we've found a cycle/path.
        if cur == start && !path.is_empty() {
            paths_in_scc.push(path.clone());
            return;
        }
        // Mark the current block as visited in this path to avoid cycles in this DFS.
        visited.insert(cur);
        // Retrieve the terminator for this block (the outgoing control flow).
        let term = &self.terminators[cur].clone();

        match term {
            TerminatorKind::SwitchInt { discr, targets } => {
                match discr {
                    // Case 1: The discriminant is a place (value held in memory, e.g., enum field)
                    Copy(p) | Move(p) => {
                        let place = self.projection(false, *p);
                        if let Some(real_discr_local) =
                            self.discriminants.get(&self.values[place].local)
                        {
                            let real_discr_local = *real_discr_local;
                            // There are already restrictions related to the discriminant;
                            // Only the branch that meets the restriction can be taken.
                            if let Some(constant) = stacked_discriminants.get(&real_discr_local) {
                                let constant = *constant;
                                for branch in targets.iter() {
                                    // branch is a tupele (value, target)
                                    if branch.0 as usize == constant {
                                        let target = branch.1.as_usize();
                                        if path.contains(&target) {
                                            continue;
                                        }
                                        path.push(target);
                                        self.calculate_scc_order(
                                            start,
                                            target,
                                            scc,
                                            path,
                                            stacked_discriminants,
                                            visited,
                                            paths_in_scc,
                                        );
                                        path.pop();
                                    }
                                }
                            } else {
                                // No restrictions yet;
                                // Visit each branch with new condition add to the
                                // stacked_discriminants.
                                for branch in targets.iter() {
                                    let constant = branch.0 as usize;
                                    let target = branch.1.as_usize();
                                    if path.contains(&target) {
                                        continue;
                                    }
                                    path.push(target);
                                    stacked_discriminants.insert(real_discr_local, constant);
                                    self.calculate_scc_order(
                                        start,
                                        target,
                                        scc,
                                        path,
                                        stacked_discriminants,
                                        visited,
                                        paths_in_scc,
                                    );
                                    stacked_discriminants.remove(&real_discr_local);
                                    path.pop();
                                }
                            }
                        } else {
                            if let Some(constant) = stacked_discriminants.get(&place) {
                                let constant = *constant;
                                for t in targets.iter() {
                                    if t.0 as usize == constant {
                                        let target = t.1.as_usize();
                                        if path.contains(&target) {
                                            continue;
                                        }
                                        path.push(target);
                                        self.calculate_scc_order(
                                            start,
                                            target,
                                            scc,
                                            path,
                                            stacked_discriminants,
                                            visited,
                                            paths_in_scc,
                                        );
                                        path.pop();
                                    }
                                }
                            } else {
                                for t in targets.iter() {
                                    let constant = t.0 as usize;
                                    let target = t.1.as_usize();
                                    if path.contains(&target) {
                                        continue;
                                    }
                                    path.push(target);
                                    stacked_discriminants.insert(place, constant);
                                    self.calculate_scc_order(
                                        start,
                                        target,
                                        scc,
                                        path,
                                        stacked_discriminants,
                                        visited,
                                        paths_in_scc,
                                    );
                                    stacked_discriminants.remove(&place);
                                    path.pop();
                                }

                                let constant = targets.iter().len();
                                let target = targets.otherwise().as_usize();
                                if !path.contains(&target) {
                                    path.push(target);
                                    stacked_discriminants.insert(place, constant);
                                    self.calculate_scc_order(
                                        start,
                                        target,
                                        scc,
                                        path,
                                        stacked_discriminants,
                                        visited,
                                        paths_in_scc,
                                    );
                                    stacked_discriminants.remove(&place);
                                    path.pop();
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            _ => {
                for next in self.blocks[cur].next.clone() {
                    if !scc.contains(&next) && next != start {
                        continue;
                    }
                    if next != start {
                        path.push(next);
                        self.calculate_scc_order(
                            start,
                            next,
                            scc,
                            path,
                            stacked_discriminants,
                            visited,
                            paths_in_scc,
                        );
                        path.pop();
                    } else {
                        self.calculate_scc_order(
                            start,
                            next,
                            scc,
                            path,
                            stacked_discriminants,
                            visited,
                            paths_in_scc,
                        );
                    }
                }
            }
        }

        visited.remove(&cur);
    }
}
