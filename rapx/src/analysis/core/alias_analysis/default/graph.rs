use super::{MopAAResult, assign::*, block::*, types::*, value::*};
use crate::{analysis::graphs::scc::Scc, utils::source::*};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        BasicBlock, Const, Operand, Rvalue, StatementKind, SwitchTargets,
        TerminatorKind, UnwindAction,
    },
    ty::{TyCtxt, TypingEnv},
};
use rustc_span::{Span, def_id::DefId};
use std::vec::Vec;

pub struct MopGraph<'tcx> {
    pub def_id: DefId,
    pub tcx: TyCtxt<'tcx>,
    pub span: Span,
    // contains all varibles (including fields) as values.
    pub values: Vec<Value>,
    // contains all blocks in the CFG
    pub blocks: Vec<Block<'tcx>>,
    pub arg_size: usize,
    // we shrink a SCC into a node and use a scc node to represent the SCC.
    pub scc_indices: Vec<usize>,
    // record the constant value during safedrop checking, i.e., which id has what value.
    pub constant: FxHashMap<usize, usize>,
    // contains the return results for inter-procedure analysis.
    pub ret_alias: MopAAResult,
    // a threhold to avoid path explosion.
    pub visit_times: usize,
    pub alias_set: Vec<usize>,
    pub child_scc: FxHashMap<
        usize,
        (
            Block<'tcx>,
            rustc_middle::mir::SwitchTargets,
            FxHashSet<usize>,
        ),
    >,
    pub disc_map: FxHashMap<usize, usize>,
    pub terms: Vec<TerminatorKind<'tcx>>,
}

impl<'tcx> MopGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> MopGraph<'tcx> {
        let fn_name = get_fn_name(tcx, def_id);
        rap_debug!("Building a new MoP graph for: {:?}", fn_name);
        // handle variables
        let body = tcx.optimized_mir(def_id);
        let locals = &body.local_decls;
        let arg_size = body.arg_count;
        let mut values = Vec::<Value>::new();
        let mut alias = Vec::<usize>::new();
        let ty_env = TypingEnv::post_analysis(tcx, def_id);
        for (local, local_decl) in locals.iter_enumerated() {
            let need_drop = local_decl.ty.needs_drop(tcx, ty_env); // the type is drop
            let may_drop = !is_not_drop(tcx, local_decl.ty);
            let mut node = Value::new(
                local.as_usize(),
                local.as_usize(),
                need_drop,
                need_drop || may_drop,
            );
            node.kind = kind(local_decl.ty);
            alias.push(values.len());
            values.push(node);
        }

        let basicblocks = &body.basic_blocks;
        let mut blocks = Vec::<Block<'tcx>>::new();
        let mut scc_indices = Vec::<usize>::new();
        let mut disc_map = FxHashMap::default();
        let mut terms = Vec::new();

        // handle each basicblock
        for i in 0..basicblocks.len() {
            scc_indices.push(i);
            let iter = BasicBlock::from(i);
            let terminator = basicblocks[iter].terminator.clone().unwrap();
            let mut cur_bb = Block::new(i, basicblocks[iter].is_cleanup);

            // handle general statements
            for stmt in &basicblocks[iter].statements {
                /* Assign is a tuple defined as Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>) */
                let span = stmt.source_info.span;
                if let StatementKind::Assign(ref assign) = stmt.kind {
                    let lv_local = assign.0.local.as_usize(); // assign.0 is a Place
                    let lv = assign.0;
                    cur_bb.assigned_locals.insert(lv_local);
                    match assign.1 {
                        // assign.1 is a Rvalue
                        Rvalue::Use(ref x) => {
                            match x {
                                Operand::Copy(p) => {
                                    let rv_local = p.local.as_usize();
                                    if values[lv_local].may_drop && values[rv_local].may_drop {
                                        let rv = *p;
                                        let assign =
                                            Assignment::new(lv, rv, AssignType::Copy, span);
                                        cur_bb.assignments.push(assign);
                                    }
                                }
                                Operand::Move(p) => {
                                    let rv_local = p.local.as_usize();
                                    if values[lv_local].may_drop && values[rv_local].may_drop {
                                        let rv = *p;
                                        let assign =
                                            Assignment::new(lv, rv, AssignType::Move, span);
                                        cur_bb.assignments.push(assign);
                                    }
                                }
                                Operand::Constant(constant) => {
                                    /* We should check the correctness due to the update of rustc
                                     * https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.Const.html
                                     */
                                    match constant.const_ {
                                        Const::Ty(_ty, const_value) => {
                                            if let Some(val) = const_value.try_to_target_usize(tcx)
                                            {
                                                cur_bb.const_value.push((lv_local, val as usize));
                                            }
                                        }
                                        Const::Unevaluated(_const_value, _ty) => {}
                                        Const::Val(const_value, _ty) => {
                                            //if let Some(val) = const_value.try_to_target_usize(tcx) {
                                            if let Some(scalar) = const_value.try_to_scalar_int() {
                                                let val = scalar.to_uint(scalar.size());
                                                cur_bb.const_value.push((lv_local, val as usize));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        Rvalue::Ref(_, _, ref p)
                        | Rvalue::RawPtr(_, ref p)
                        | Rvalue::CopyForDeref(ref p) => {
                            let rv_local = p.local.as_usize();
                            if values[lv_local].may_drop && values[rv_local].may_drop {
                                let rv = *p;
                                let assign = Assignment::new(lv, rv, AssignType::Copy, span);
                                cur_bb.assignments.push(assign);
                            }
                        }
                        Rvalue::ShallowInitBox(ref x, _) => {
                            /*
                             * Original ShllowInitBox is a two-level pointer: lvl0 -> lvl1 -> lvl2
                             * Since our alias analysis does not consider multi-level pointer,
                             * We simplify it as: lvl0
                             */
                            if !values[lv_local].fields.contains_key(&0) {
                                let mut lvl0 = Value::new(values.len(), lv_local, false, true);
                                lvl0.field_id = 0;
                                values[lv_local].fields.insert(0, lvl0.index);
                                alias.push(values.len());
                                values.push(lvl0);
                            }
                            match x {
                                Operand::Copy(p) | Operand::Move(p) => {
                                    let rv_local = p.local.as_usize();
                                    if values[lv_local].may_drop && values[rv_local].may_drop {
                                        let rv = *p;
                                        let assign =
                                            Assignment::new(lv, rv, AssignType::InitBox, span);
                                        cur_bb.assignments.push(assign);
                                    }
                                }
                                Operand::Constant(_) => {}
                            }
                        }
                        Rvalue::Cast(_, ref x, _) => match x {
                            Operand::Copy(p) => {
                                let rv_local = p.local.as_usize();
                                if values[lv_local].may_drop && values[rv_local].may_drop {
                                    let rv = *p;
                                    let assign = Assignment::new(lv, rv, AssignType::Copy, span);
                                    cur_bb.assignments.push(assign);
                                }
                            }
                            Operand::Move(p) => {
                                let rv_local = p.local.as_usize();
                                if values[lv_local].may_drop && values[rv_local].may_drop {
                                    let rv = *p;
                                    let assign = Assignment::new(lv, rv, AssignType::Move, span);
                                    cur_bb.assignments.push(assign);
                                }
                            }
                            Operand::Constant(_) => {}
                        },
                        Rvalue::Aggregate(_, ref x) => {
                            for each_x in x {
                                match each_x {
                                    Operand::Copy(p) | Operand::Move(p) => {
                                        let rv_local = p.local.as_usize();
                                        if values[lv_local].may_drop && values[rv_local].may_drop {
                                            let rv = *p;
                                            let assign =
                                                Assignment::new(lv, rv, AssignType::Copy, span);
                                            cur_bb.assignments.push(assign);
                                        }
                                    }
                                    Operand::Constant(_) => {}
                                }
                            }
                        }
                        Rvalue::Discriminant(ref p) => {
                            let rv = *p;
                            let assign = Assignment::new(lv, rv, AssignType::Variant, span);
                            cur_bb.assignments.push(assign);
                            disc_map.insert(lv_local, p.local.as_usize());
                        }
                        _ => {}
                    }
                }
            }

            terms.push(terminator.kind.clone());
            // handle terminator statements
            match terminator.kind {
                TerminatorKind::Goto { ref target } => {
                    cur_bb.add_next(target.as_usize());
                }
                TerminatorKind::SwitchInt {
                    discr: _,
                    ref targets,
                } => {
                    cur_bb.switch_stmt = Some(terminator.clone());
                    for (_, ref target) in targets.iter() {
                        cur_bb.add_next(target.as_usize());
                    }
                    cur_bb.add_next(targets.otherwise().as_usize());
                }
                TerminatorKind::UnwindResume
                | TerminatorKind::Return
                | TerminatorKind::UnwindTerminate(_)
                | TerminatorKind::CoroutineDrop
                | TerminatorKind::Unreachable => {}
                TerminatorKind::Drop {
                    place: _,
                    ref target,
                    ref unwind,
                    replace: _,
                    drop: _,
                    async_fut: _,
                } => {
                    cur_bb.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Call {
                    func: _,
                    args: _,
                    destination: _,
                    ref target,
                    ref unwind,
                    call_source: _,
                    fn_span: _,
                } => {
                    if let Some(tt) = target {
                        cur_bb.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cur_bb.add_next(tt.as_usize());
                    }
                    cur_bb.calls.push(terminator.clone());
                }
                TerminatorKind::TailCall { .. } => todo!(),
                TerminatorKind::Assert {
                    cond: _,
                    expected: _,
                    msg: _,
                    ref target,
                    ref unwind,
                } => {
                    cur_bb.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Yield {
                    value: _,
                    ref resume,
                    resume_arg: _,
                    ref drop,
                } => {
                    cur_bb.add_next(resume.as_usize());
                    if let Some(target) = drop {
                        cur_bb.add_next(target.as_usize());
                    }
                }
                TerminatorKind::FalseEdge {
                    ref real_target,
                    imaginary_target: _,
                } => {
                    cur_bb.add_next(real_target.as_usize());
                }
                TerminatorKind::FalseUnwind {
                    ref real_target,
                    unwind: _,
                } => {
                    cur_bb.add_next(real_target.as_usize());
                }
                TerminatorKind::InlineAsm {
                    template: _,
                    operands: _,
                    options: _,
                    line_spans: _,
                    ref unwind,
                    targets,
                    asm_macro: _,
                } => {
                    for target in targets {
                        cur_bb.add_next(target.as_usize());
                    }
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                }
            }
            blocks.push(cur_bb);
        }

        MopGraph {
            def_id,
            tcx,
            span: body.span,
            blocks,
            values,
            arg_size,
            scc_indices,
            alias_set: alias,
            constant: FxHashMap::default(),
            ret_alias: MopAAResult::new(arg_size),
            visit_times: 0,
            child_scc: FxHashMap::default(),
            disc_map,
            terms,
        }
    }

    pub fn dfs_on_spanning_tree(
        &self,
        index: usize,
        stack: &mut Vec<usize>,
        paths: &mut Vec<Vec<usize>>,
    ) {
        let curr_scc_index = self.scc_indices[index];
        if self.blocks[curr_scc_index].next.is_empty() {
            paths.push(stack.to_vec());
        } else {
            for child in self.blocks[curr_scc_index].next.iter() {
                stack.push(*child);
                self.dfs_on_spanning_tree(*child, stack, paths);
            }
        }
        stack.pop();
    }

    pub fn get_paths(&self) -> Vec<Vec<usize>> {
        let mut paths: Vec<Vec<usize>> = Vec::new();
        let mut stack: Vec<usize> = vec![0];
        self.dfs_on_spanning_tree(0, &mut stack, &mut paths);
        paths
    }
    pub fn get_all_branch_sub_blocks_paths(&self) -> Vec<Vec<usize>> {
        // 1. Get all execution paths
        let all_paths = self.get_paths();

        // Use FxHashSet to collect all unique lists of dominated_scc_bbs.
        // Vec<usize> implements Hash, so it can be inserted directly into the set.
        let mut unique_branch_sub_blocks = FxHashSet::<Vec<usize>>::default();

        // 2. Iterate over each path
        for path in all_paths {
            // 3. For the current path, get the corresponding dominated_scc_bbs for branch nodes
            let branch_blocks_for_this_path = self.get_branch_sub_blocks_for_path(&path);
            rap_debug!(
                "Branch blocks for path {:?}: {:?}",
                path,
                branch_blocks_for_this_path
            );
            // 4. Add these dominated_scc_bbs to the set
            //    Use insert to avoid duplicates
            unique_branch_sub_blocks.insert(branch_blocks_for_this_path);
        }

        // 5. Convert the set of unique results back to a Vec and return
        unique_branch_sub_blocks.into_iter().collect()
    }

    pub fn get_branch_sub_blocks_for_path(&self, path: &[usize]) -> Vec<usize> {
        let mut expanded_path = Vec::new();
        // Use FxHashSet to track which SCCs have already been expanded in this path,
        // preventing repeated expansion due to cycles.
        let mut processed_scc_indices = FxHashSet::default();

        for &block_idx in path {
            // 1. Get the representative SCC index of the current basic block
            let scc_idx = self.scc_indices[block_idx];

            // 2. Try inserting scc_idx into the set. If successful (returns true),
            // it means this SCC is encountered for the first time.
            if processed_scc_indices.insert(scc_idx) {
                // First time encountering this SCC: perform full expansion

                // a. First, add the SCC representative itself to the path
                expanded_path.push(scc_idx);

                // b. Then, retrieve the SCC node information
                let scc_node = &self.blocks[scc_idx];

                // c. If it has sub-blocks (i.e., it’s a multi-node SCC),
                // append all sub-blocks to the path.
                // dominated_scc_bbs are already ordered (topologically or near-topologically)
                if !scc_node.dominated_scc_bbs.is_empty() {
                    expanded_path.extend_from_slice(&scc_node.dominated_scc_bbs);
                }
            } else {
                // SCC already seen before (e.g., due to a cycle in the path):
                // Only add the representative node as a connector, skip internal blocks.
                expanded_path.push(scc_idx);
            }
        }

        expanded_path
    }

    pub fn get_switch_conds(&mut self, block_index: usize) -> Option<usize> {
        let block = &self.blocks[block_index];
        let switch_stmt = block.switch_stmt.as_ref()?;

        let TerminatorKind::SwitchInt { discr, .. } = &switch_stmt.kind else {
            return None;
        };

        match discr {
            Operand::Copy(p) | Operand::Move(p) => Some(self.projection(false, *p)),
            _ => None,
        }
    }
}

pub trait SccHelper<'tcx> {
    fn blocks(&self) -> &Vec<Block<'tcx>>; // or whatever the actual type is
    fn blocks_mut(&mut self) -> &mut Vec<Block<'tcx>>;
    fn scc_indices(&self) -> &[usize];
    fn scc_indices_mut(&mut self) -> &mut [usize];
    fn child_scc(&self) -> &FxHashMap<usize, (Block<'tcx>, SwitchTargets, FxHashSet<usize>)>;
    fn child_scc_mut(
        &mut self,
    ) -> &mut FxHashMap<usize, (Block<'tcx>, SwitchTargets, FxHashSet<usize>)>;
    fn switch_conds(&mut self, node: usize) -> Option<usize>;
}

impl<'tcx> SccHelper<'tcx> for MopGraph<'tcx> {
    fn blocks(&self) -> &Vec<Block<'tcx>> {
        &self.blocks
    }
    fn blocks_mut(&mut self) -> &mut Vec<Block<'tcx>> {
        &mut self.blocks
    }
    fn scc_indices(&self) -> &[usize] {
        &self.scc_indices
    }
    fn scc_indices_mut(&mut self) -> &mut [usize] {
        &mut self.scc_indices
    }
    fn child_scc(&self) -> &FxHashMap<usize, (Block<'tcx>, SwitchTargets, FxHashSet<usize>)> {
        &self.child_scc
    }
    fn child_scc_mut(
        &mut self,
    ) -> &mut FxHashMap<usize, (Block<'tcx>, SwitchTargets, FxHashSet<usize>)> {
        &mut self.child_scc
    }
    fn switch_conds(&mut self, node: usize) -> Option<usize> {
        self.get_switch_conds(node)
    }
}

pub fn scc_handler<'tcx, T: SccHelper<'tcx>>(graph: &mut T, root: usize, scc_components: &[usize]) {
    let mut assigned_locals = FxHashSet::<usize>::default();
    for value in &graph.blocks()[root].assigned_locals {
        assigned_locals.insert(*value);
    }
    let mut switch_conds = Vec::new();
    let mut scc_block_set = FxHashSet::<usize>::default();
    let original_root_block = graph.blocks()[root].clone();
    for &node in &scc_components[1..] {
        graph.scc_indices_mut()[node] = root;
        graph.blocks_mut()[root].dominated_scc_bbs.push(node);
        scc_block_set.insert(node);

        // If the node contains a SwitchInt instruction, we should also consider the
        // condition in the SwitchInt instruction of the SCC diminator.
        // Example :
        //  let p = ...
        //  while x {
        //      use(p)
        //      if y {
        //          drop(p);
        //      }
        //      x -= 1;
        //  }
        if let Some(place) = graph.switch_conds(node) {
            if let Some(switch_stmt) = graph.blocks()[root].switch_stmt.clone() {
                switch_conds.push((place, switch_stmt));
            }
        }

        let nexts = graph.blocks()[node].next.clone();
        for i in nexts {
            graph.blocks_mut()[root].next.insert(i);
        }
    }

    switch_conds.retain(|v| !assigned_locals.contains(&(v.0)));

    if !switch_conds.is_empty() && switch_conds.len() == 1 {
        let target_terminator = switch_conds[0].1.clone();

        let TerminatorKind::SwitchInt { discr: _, targets } = target_terminator.kind else {
            unreachable!();
        };

        graph
            .child_scc_mut()
            .insert(root, (original_root_block, targets, scc_block_set));
    }

    /* remove next nodes which are already in the current SCC */
    let scc_indices = graph.scc_indices().to_vec();
    graph.blocks_mut()[root]
        .next
        .retain(|i| scc_indices[*i] != root);

    /* To ensure a resonable order of blocks within one SCC,
     * so that the scc can be directly used for followup analysis without referencing the
     * original graph.
     * */
    graph.blocks_mut()[root].dominated_scc_bbs.reverse();
}

impl<'tcx> Scc for MopGraph<'tcx> {
    fn on_scc_found(&mut self, root: usize, scc_components: &[usize]) {
        scc_handler(self, root, scc_components);
    }
    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.blocks[root].next.clone()
    }
    fn get_size(&mut self) -> usize {
        self.blocks.len()
    }
}
