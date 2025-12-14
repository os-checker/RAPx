use super::graph::*;
use crate::analysis::core::alias_analysis::default::{graph::SccHelper,MopAAResultMap};
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::{
    mir::{
        Operand::{self, Constant, Copy, Move},
        Place, TerminatorKind,
    },
    ty::{TyCtxt, TyKind, TypingEnv},
};
use std::collections::{HashMap, HashSet};

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
        /* duplicate the status before visiting a path; */
        let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.mop_graph.constants.clone();
        let backup_alias_set = self.mop_graph.alias_set.clone();
        let backup_drop_record = self.drop_record.clone();
        self.check(bb_idx, tcx, fn_map);
        /* restore after visit */
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
        /* duplicate the status before visiting a path; */
        let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.mop_graph.constants.clone();
        let backup_alias_set = self.mop_graph.alias_set.clone();
        let backup_drop_record = self.drop_record.clone();
        /* add control-sensitive indicator to the path status */
        self.mop_graph
            .constants
            .insert(path_discr_id, path_discr_val);
        self.check(bb_idx, tcx, fn_map);
        /* restore after visit */
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
        let cur_block = self.mop_graph.blocks[self.mop_graph.scc_indices[bb_idx]].clone();
        self.alias_bb(self.mop_graph.scc_indices[bb_idx]);
        self.alias_bbcall(self.mop_graph.scc_indices[bb_idx], tcx, fn_map);
        self.drop_check(self.mop_graph.scc_indices[bb_idx], tcx);

        if self
            .mop_graph
            .child_scc
            .get(&self.mop_graph.scc_indices[bb_idx])
            .is_some()
        {
            let init_idx = self.mop_graph.scc_indices[bb_idx];
            let (init_block, cur_targets, scc_block_set) =
                self.mop_graph.child_scc.get(&init_idx).unwrap().clone();

            for enum_idx in cur_targets.all_targets() {
                let backup_values = self.mop_graph.values.clone();
                let backup_constant = self.mop_graph.constants.clone();

                let mut block_node = if bb_idx == init_idx {
                    init_block.clone()
                } else {
                    self.mop_graph.blocks[bb_idx].clone()
                };

                if let Some(switch_stmt) = block_node.switch_stmt {
                    match &switch_stmt.kind {
                        TerminatorKind::SwitchInt { targets, .. } => {
                            if cur_targets == *targets {
                                block_node.next = FxHashSet::default();
                                block_node.next.insert(enum_idx.index());
                            }
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                }

                let mut work_list = Vec::new();
                let mut work_set = FxHashSet::<usize>::default();
                work_list.push(bb_idx);
                work_set.insert(bb_idx);
                while !work_list.is_empty() {
                    let current_node = work_list.pop().unwrap();
                    block_node.dominated_scc_bbs.push(current_node);
                    let real_node = if current_node != init_idx {
                        self.mop_graph.blocks[current_node].clone()
                    } else {
                        init_block.clone()
                    };

                    match real_node.switch_stmt {
                        Some(ref switch_stmt) => {
                            let TerminatorKind::SwitchInt { ref targets, .. } = switch_stmt.kind
                            else {
                                unreachable!();
                            };

                            if cur_targets == *targets {
                                block_node.next.insert(enum_idx.index());
                            } else {
                                for next in &real_node.next {
                                    block_node.next.insert(*next);
                                }
                            }
                        }
                        None => {
                            for next in &real_node.next {
                                block_node.next.insert(*next);
                            }
                        }
                    }

                    match real_node.switch_stmt {
                        Some(ref switch_stmt) => {
                            let TerminatorKind::SwitchInt { ref targets, .. } = switch_stmt.kind
                            else {
                                unreachable!();
                            };

                            if cur_targets == *targets {
                                let next_idx = enum_idx.index();
                                if scc_block_set.contains(&next_idx)
                                    && !work_set.contains(&next_idx)
                                {
                                    work_set.insert(next_idx);
                                    work_list.push(next_idx);
                                }
                            } else {
                                for next in &real_node.next {
                                    if scc_block_set.contains(next) && !work_set.contains(next) {
                                        work_set.insert(*next);
                                        work_list.push(*next);
                                    }
                                }
                            }
                        }
                        None => {
                            for next in &real_node.next {
                                if scc_block_set.contains(next) && !work_set.contains(next) {
                                    work_set.insert(*next);
                                    work_list.push(*next);
                                }
                            }
                        }
                    }
                }

                /* remove next nodes which are already in the current SCC */
                let scc_indices = self.mop_graph.scc_indices().to_vec();
                self.mop_graph.blocks_mut()[init_idx]
                    .next
                    .retain(|i| scc_indices[*i] != init_idx);

                for i in block_node.dominated_scc_bbs.clone() {
                    self.alias_bb(i);
                    self.alias_bbcall(i, tcx, fn_map);
                    self.drop_check(i, tcx);
                }
                /* Reach a leaf node, check bugs */
                match block_node.next.len() {
                    0 => {
                        // check the bugs.
                        if Self::should_check(self.mop_graph.def_id) {
                            self.dp_check(cur_block.is_cleanup);
                        }
                        return;
                    }
                    _ => {
                        /*
                         * Equivalent to self.check(cur_block.next[0]..);
                         * We cannot use [0] for FxHashSet.
                         */
                        for next in block_node.next {
                            self.check(next, tcx, fn_map);
                        }
                    }
                }

                self.mop_graph.values = backup_values;
                self.mop_graph.constants = backup_constant;
            }

            return;
        }

        let mut order = vec![];
        order.push(vec![]);

        /* Handle cases if the current block is a merged scc block with sub block */
        if !cur_block.dominated_scc_bbs.is_empty() {
            match std::env::var_os("SAFEDROP") {
                Some(val) if val == "0" => {
                    order.push(cur_block.dominated_scc_bbs.clone());
                }
                _ => {
                    self.calculate_scc_order(
                        &mut cur_block.dominated_scc_bbs.clone(),
                        &mut vec![],
                        &mut order,
                        &mut HashMap::new(),
                        bb_idx,
                        bb_idx,
                        &mut HashSet::new(),
                    );
                }
            }
        }

        let backup_values = self.mop_graph.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.mop_graph.constants.clone();
        let backup_alias_set = self.mop_graph.alias_set.clone();
        for scc_each in order {
            self.mop_graph.alias_set = backup_alias_set.clone();
            self.mop_graph.values = backup_values.clone();
            self.mop_graph.constants = backup_constant.clone();

            if !scc_each.is_empty() {
                for idx in scc_each {
                    self.alias_bb(idx);
                    self.alias_bbcall(idx, tcx, fn_map);
                }
            }

            let cur_block = cur_block.clone();
            /* Reach a leaf node, check bugs */
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

            /* Begin: handle the SwitchInt statement. */
            let mut single_target = false;
            let mut sw_val = 0;
            let mut sw_target = 0; // Single target
            let mut path_discr_id = 0; // To avoid analyzing paths that cannot be reached with one enum type.
            let mut sw_targets = None; // Multiple targets of SwitchInt
            if let Some(switch_stmt) = cur_block.switch_stmt
                && cur_block.dominated_scc_bbs.is_empty()
            {
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
                    for i in cur_block.next {
                        if self.mop_graph.visit_times > VISIT_LIMIT {
                            continue;
                        }
                        let next_idx = i;
                        self.split_check(next_idx, tcx, fn_map);
                    }
                }
            }
        }
        rap_debug!("Values: {:?}", self.mop_graph.values);
        rap_debug!("Alias: {:?}", self.mop_graph.alias_set);
    }

    pub fn calculate_scc_order(
        &mut self,
        scc: &Vec<usize>,
        path: &mut Vec<usize>,
        ans: &mut Vec<Vec<usize>>,
        discriminants: &mut HashMap<usize, usize>,
        cur_bb: usize,
        root_bb: usize,
        visit: &mut HashSet<usize>,
    ) {
        if cur_bb == root_bb && !path.is_empty() {
            ans.push(path.clone());
            return;
        }
        visit.insert(cur_bb);
        let term = &self.mop_graph.terminators[cur_bb].clone();

        match term {
            TerminatorKind::SwitchInt { discr, targets } => match discr {
                Copy(p) | Move(p) => {
                    let place = self.projection(false, *p);
                    if let Some(father) = self
                        .mop_graph
                        .discriminants
                        .get(&self.mop_graph.values[place].local)
                    {
                        let father = *father;
                        if let Some(constant) = discriminants.get(&father) {
                            let constant = *constant;
                            for t in targets.iter() {
                                if t.0 as usize == constant {
                                    let target = t.1.as_usize();
                                    if path.contains(&target) {
                                        continue;
                                    }
                                    path.push(target);
                                    self.calculate_scc_order(
                                        scc,
                                        path,
                                        ans,
                                        discriminants,
                                        target,
                                        root_bb,
                                        visit,
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
                                discriminants.insert(father, constant);
                                self.calculate_scc_order(
                                    scc,
                                    path,
                                    ans,
                                    discriminants,
                                    target,
                                    root_bb,
                                    visit,
                                );
                                discriminants.remove(&father);
                                path.pop();
                            }
                        }
                    } else {
                        if let Some(constant) = discriminants.get(&place) {
                            let constant = *constant;
                            for t in targets.iter() {
                                if t.0 as usize == constant {
                                    let target = t.1.as_usize();
                                    if path.contains(&target) {
                                        continue;
                                    }
                                    path.push(target);
                                    self.calculate_scc_order(
                                        scc,
                                        path,
                                        ans,
                                        discriminants,
                                        target,
                                        root_bb,
                                        visit,
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
                                discriminants.insert(place, constant);
                                self.calculate_scc_order(
                                    scc,
                                    path,
                                    ans,
                                    discriminants,
                                    target,
                                    root_bb,
                                    visit,
                                );
                                discriminants.remove(&place);
                                path.pop();
                            }

                            let constant = targets.iter().len();
                            let target = targets.otherwise().as_usize();
                            if !path.contains(&target) {
                                path.push(target);
                                discriminants.insert(place, constant);
                                self.calculate_scc_order(
                                    scc,
                                    path,
                                    ans,
                                    discriminants,
                                    target,
                                    root_bb,
                                    visit,
                                );
                                discriminants.remove(&place);
                                path.pop();
                            }
                        }
                    }
                }
                _ => {}
            },
            _ => {
                for next in self.mop_graph.blocks[cur_bb].next.clone() {
                    if !scc.contains(&next) && next != root_bb {
                        continue;
                    }
                    if next != root_bb {
                        path.push(next);
                        self.calculate_scc_order(scc, path, ans, discriminants, next, root_bb, visit);
                        path.pop();
                    } else {
                        self.calculate_scc_order(scc, path, ans, discriminants, next, root_bb, visit);
                    }
                }
            }
        }

        visit.remove(&cur_bb);
    }
}
