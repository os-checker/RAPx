use super::graph::*;
use crate::analysis::core::alias_analysis::default::MopAAResultMap;
use rustc_middle::{
    mir::{
        Operand::{self, Constant, Copy, Move},
        Place, TerminatorKind,
    },
    ty::{TyCtxt, TyKind, TypingEnv},
};
use std::{
    collections::{HashMap, HashSet},
    vec,
};

pub const VISIT_LIMIT: usize = 1000;

impl<'tcx> SafeDropGraph<'tcx> {
    // analyze the drop statement and update the liveness for nodes.
    pub fn drop_check(&mut self, bb_idx: usize, tcx: TyCtxt<'tcx>) {
        let cur_block = self.mop_graph.blocks[bb_idx].clone();
        let is_cleanup = cur_block.is_cleanup;
        for drop in cur_block.drops {
            match drop.kind {
                TerminatorKind::Drop {
                    ref place,
                    target: _,
                    unwind: _,
                    replace: _,
                    drop: _,
                    async_fut: _,
                } => {
                    if !self.drop_heap_item_check(place, tcx) {
                        continue;
                    }
                    let birth = self.mop_graph.scc_indices[bb_idx];
                    let local = self.projection(false, place.clone());
                    let info = drop.source_info.clone();
                    self.add_to_drop_record(local, local, birth, &info, false, bb_idx, is_cleanup);
                }
                TerminatorKind::Call {
                    func: _, ref args, ..
                } => {
                    if args.len() > 0 {
                        let birth = self.mop_graph.scc_indices[bb_idx];
                        let place = match args[0].node {
                            Operand::Copy(place) => place,
                            Operand::Move(place) => place,
                            _ => {
                                rap_error!("Constant operand exists: {:?}", args[0]);
                                return;
                            }
                        };
                        let local = self.projection(false, place.clone());
                        let info = drop.source_info.clone();
                        self.add_to_drop_record(
                            local, local, birth, &info, false, bb_idx, is_cleanup,
                        );
                    }
                }
                _ => {}
            }
        }
    }

    pub fn drop_heap_item_check(&self, place: &Place<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
        let place_ty = place.ty(&tcx.optimized_mir(self.mop_graph.def_id).local_decls, tcx);
        match place_ty.ty.kind() {
            TyKind::Adt(adtdef, ..) => match self.adt_owner.get(&adtdef.did()) {
                None => true,
                Some(owenr_unit) => {
                    let idx = match place_ty.variant_index {
                        Some(vdx) => vdx.index(),
                        None => 0,
                    };
                    if owenr_unit[idx].0.is_onheap() || owenr_unit[idx].1.contains(&true) {
                        true
                    } else {
                        false
                    }
                }
            },
            _ => true,
        }
    }

    pub fn split_check(&mut self, bb_idx: usize, tcx: TyCtxt<'tcx>, fn_map: &MopAAResultMap) {
        /* duplicate the status before visiteding a path; */
        let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiteding different paths;
        let backup_constant = self.mop_graph.constants.clone();
        let backup_alias_set = self.mop_graph.alias_set.clone();
        let backup_drop_record = self.drop_record.clone();
        self.check(bb_idx, tcx, fn_map);
        /* restore after visited */
        self.mop_graph.values = backup_values;
        self.mop_graph.constants = backup_constant;
        self.mop_graph.alias_set = backup_alias_set;
        self.drop_record = backup_drop_record;
    }

    pub fn split_check_with_cond(
        &mut self,
        bb_idx: usize,
        path_discr_id: usize,
        path_discr_val: usize,
        tcx: TyCtxt<'tcx>,
        fn_map: &MopAAResultMap,
    ) {
        /* duplicate the status before visiteding a path; */
        let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiteding different paths;
        let backup_constant = self.mop_graph.constants.clone();
        let backup_alias_set = self.mop_graph.alias_set.clone();
        let backup_drop_record = self.drop_record.clone();
        /* add control-sensitive indicator to the path status */
        self.mop_graph
            .constants
            .insert(path_discr_id, path_discr_val);
        self.check(bb_idx, tcx, fn_map);
        /* restore after visited */
        self.mop_graph.values = backup_values;
        self.mop_graph.constants = backup_constant;
        self.mop_graph.alias_set = backup_alias_set;
        self.drop_record = backup_drop_record;
    }

    // the core function of the safedrop.
    pub fn check(&mut self, bb_idx: usize, tcx: TyCtxt<'tcx>, fn_map: &MopAAResultMap) {
        self.mop_graph.visit_times += 1;
        if self.mop_graph.visit_times > VISIT_LIMIT {
            return;
        }
        let scc_idx = self.mop_graph.scc_indices[bb_idx];
        let cur_block = self.mop_graph.blocks[bb_idx].clone();
        rap_info!(
            "Checking bb: {}, scc_idx: {}, scc: {:?}, child_scc: {:?}",
            bb_idx,
            scc_idx,
            cur_block.dominated_scc_bbs.clone(),
            self.mop_graph.child_scc.get(&scc_idx)
        );
        self.alias_bb(self.mop_graph.scc_indices[bb_idx]);
        self.alias_bbcall(self.mop_graph.scc_indices[bb_idx], tcx, fn_map);
        self.drop_check(self.mop_graph.scc_indices[bb_idx], tcx);

        if bb_idx == scc_idx {
            //if self.mop_graph.child_scc.get(&bb_idx).is_some() {
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
            rap_info!("Paths in scc: {:?}", paths_in_scc);

            let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiteding different paths;
            let backup_constant = self.mop_graph.constants.clone();
            let backup_alias_set = self.mop_graph.alias_set.clone();
            for each_path in paths_in_scc {
                self.mop_graph.alias_set = backup_alias_set.clone();
                self.mop_graph.values = backup_values.clone();
                self.mop_graph.constants = backup_constant.clone();

                if !each_path.is_empty() {
                    for idx in each_path {
                        self.alias_bb(idx);
                        self.alias_bbcall(idx, tcx, fn_map);
                        self.drop_check(idx, tcx);
                    }
                }
            }
        /* Reach a leaf node, check bugs */
        rap_info!("cur_block.next: {:?}", cur_block.next);
        match cur_block.next.len() {
            0 => {
                if Self::should_check(self.mop_graph.def_id) {
                    self.dp_check(cur_block.is_cleanup);
                }
                return;
            }
            1 => {
                /*
                 * Equivalent to self.check(cur_block.next[0]..);
                 * We cannot use [0] for FxHashSet.
                 */
                for next in cur_block.next {
                    self.check(next, tcx, fn_map);
                }
                return;
            }
            _ => { // multiple blocks
            }
        }
        } //else {
            /* Begin: handle the SwitchInt statement. */
            let mut single_target = false;
            let mut sw_val = 0;
            let mut sw_target = 0; // Single target
            let mut path_discr_id = 0; // To avoid analyzing paths that cannot be reached with one enum type.
            let mut sw_targets = None; // Multiple targets of SwitchInt
            if let Some(ref switch_stmt) = cur_block.switch_stmt
                && cur_block.dominated_scc_bbs.is_empty()
            {
                rap_info!("Handle switchInt in bb {:?}", cur_block);
                if let TerminatorKind::SwitchInt {
                    ref discr,
                    ref targets,
                } = switch_stmt.kind
                {
                    rap_debug!("{:?}", switch_stmt);
                    rap_debug!("{:?}", self.mop_graph.constants);
                    match discr {
                        Copy(p) | Move(p) => {
                            let place = self.projection(false, *p);
                            let local_decls = &tcx.optimized_mir(self.mop_graph.def_id).local_decls;
                            let place_ty = (*p).ty(local_decls, tcx);
                            rap_debug!("place {:?}", place);
                            match place_ty.ty.kind() {
                                TyKind::Bool => {
                                    rap_debug!("SwitchInt via Bool");
                                    if let Some(constant) = self.mop_graph.constants.get(&place) {
                                        if *constant != usize::MAX {
                                            single_target = true;
                                            sw_val = *constant;
                                        }
                                    }
                                    path_discr_id = place;
                                    sw_targets = Some(targets.clone());
                                }
                                _ => {
                                    if let Some(father) = self
                                        .mop_graph
                                        .discriminants
                                        .get(&self.mop_graph.values[place].local)
                                    {
                                        if let Some(constant) = self.mop_graph.constants.get(father)
                                        {
                                            if *constant != usize::MAX {
                                                single_target = true;
                                                sw_val = *constant;
                                            }
                                        }
                                        if self.mop_graph.values[place].local == place {
                                            path_discr_id = *father;
                                            sw_targets = Some(targets.clone());
                                        }
                                    }
                                }
                            }
                        }
                        Constant(c) => {
                            single_target = true;
                            let ty_env =
                                TypingEnv::post_analysis(self.mop_graph.tcx, self.mop_graph.def_id);
                            if let Some(val) =
                                c.const_.try_eval_target_usize(self.mop_graph.tcx, ty_env)
                            {
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
                self.check(sw_target, tcx, fn_map);
            } else {
                // Other cases in switchInt terminators
                if let Some(targets) = sw_targets {
                    for iter in targets.iter() {
                        if self.mop_graph.visit_times > VISIT_LIMIT {
                            continue;
                        }
                        let next_idx = iter.1.as_usize();
                        let path_discr_val = iter.0 as usize;
                        self.split_check_with_cond(
                            next_idx,
                            path_discr_id,
                            path_discr_val,
                            tcx,
                            fn_map,
                        );
                    }
                    let all_targets = targets.all_targets();
                    let next_idx = all_targets[all_targets.len() - 1].as_usize();
                    let path_discr_val = usize::MAX; // to indicate the default path;
                    self.split_check_with_cond(
                        next_idx,
                        path_discr_id,
                        path_discr_val,
                        tcx,
                        fn_map,
                    );
                } else {
                    for i in &cur_block.next {
                        if self.mop_graph.visit_times > VISIT_LIMIT {
                            continue;
                        }
                        let next_idx = i;
                        self.split_check(*next_idx, tcx, fn_map);
                    }
                }
            }
        //}

        rap_debug!("Values: {:?}", self.mop_graph.values);
        rap_debug!("Alias: {:?}", self.mop_graph.alias_set);
    }

    ///This function performs a DFS traversal across the SCC, extracting all possible orderings
    /// that respect the control-flow structure and SwitchInt branching, taking into account
    /// enum discriminants and constant branches.
    pub fn calculate_scc_order(
        &mut self,
        start_bb: usize,
        cur_bb: usize,
        scc: &Vec<usize>,
        path: &mut Vec<usize>,
        stacked_discriminants: &mut HashMap<usize, usize>,
        visited: &mut HashSet<usize>, // for cycle detection.
        paths_in_scc: &mut Vec<Vec<usize>>,
    ) {
        // If we have returned to the start_bb and the path is non-empty, we've found a cycle/path.
        if cur_bb == start_bb && !path.is_empty() {
            paths_in_scc.push(path.clone());
            return;
        }
        // Mark the current block as visited in this path to avoid cycles in this DFS.
        visited.insert(cur_bb);
        // Retrieve the terminator for this block (the outgoing control flow).
        let term = &self.mop_graph.terminators[cur_bb].clone();

        match term {
            TerminatorKind::SwitchInt { discr, targets } => {
                match discr {
                    // Case 1: The discriminant is a place (value held in memory, e.g., enum field)
                    Copy(p) | Move(p) => {
                        let place = self.projection(false, *p);
                        if let Some(real_discr_local) = self
                            .mop_graph
                            .discriminants
                            .get(&self.mop_graph.values[place].local)
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
                                            start_bb,
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
                                        start_bb,
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
                                            start_bb,
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
                                        start_bb,
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
                                        start_bb,
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
                for next in self.mop_graph.blocks[cur_bb].next.clone() {
                    if !scc.contains(&next) && next != start_bb {
                        continue;
                    }
                    if next != start_bb {
                        path.push(next);
                        self.calculate_scc_order(
                            start_bb,
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
                            start_bb,
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

        visited.remove(&cur_bb);
    }
}
