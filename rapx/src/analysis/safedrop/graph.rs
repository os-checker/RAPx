use super::bug_records::*;
use crate::{
    analysis::{
        core::alias_analysis::default::{assign::*, block::*, types::*, value::*},
        core::ownedheap_analysis::OHAResultMap,
    },
    def_id::*,
};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{
    BasicBlock, Body, Const, Operand, Rvalue, StatementKind, TerminatorKind, UnwindAction,
};
use rustc_middle::ty::{self, TyCtxt, TypingEnv};
use rustc_span::{Span, def_id::DefId};
use std::{cmp::min, usize, vec::Vec};

#[derive(Debug, Copy, Clone)]
pub struct DropRecord {
    pub is_dropped: bool,
    pub drop_at_bb: usize,
    pub drop_via_local: usize,
}

impl DropRecord {
    pub fn new(is_dropped: bool, drop_at_bb: usize, drop_via_local: usize) -> Self {
        DropRecord {
            is_dropped,
            drop_at_bb,
            drop_via_local,
        }
    }
    pub fn false_record() -> Self {
        DropRecord {
            is_dropped: false,
            drop_at_bb: usize::MAX,
            drop_via_local: usize::MAX,
        }
    }
}

/// We represent each target function with the `SafeDropGraph` struct and then perform analysis
/// based on the struct.
pub struct SafeDropGraph<'tcx> {
    pub def_id: DefId,
    pub tcx: TyCtxt<'tcx>,
    // The field is used to detect dangling pointers in arguments after the function returns.
    pub arg_size: usize, 
    pub span: Span,
    // All values (including fields) of the function. 
    // For general variables, we use its Local as the value index;
    // For fields, the value index is determined via auto increment.
    pub values: Vec<Value>,
    // All blocks of the function; 
    // Each block is initialized as a basic block of the mir;
    // The blocks are then aggregated into strongly-connected components.
    pub blocks: Vec<SccBlock<'tcx>>,
    // The scc index of each basic block..
    pub scc_indices: Vec<usize>,
    // We record the constant value for path sensitivity.
    pub constants: FxHashMap<usize, usize>,
    // We record the decision of enumerate typed values for path sensitivity.
    pub discriminants: FxHashMap<usize, usize>,
    // record the information of bugs for the function.
    pub bug_records: BugRecords,
    // a threhold to avoid path explosion.
    pub visit_times: usize,
    pub alias_set: Vec<usize>,
    pub drop_record: Vec<DropRecord>,
    // analysis of heap item
    pub adt_owner: OHAResultMap,
    pub child_scc: FxHashMap<
        usize,
        (
            SccBlock<'tcx>,
            rustc_middle::mir::SwitchTargets,
            FxHashSet<usize>,
        ),
    >,
    pub terminators: Vec<TerminatorKind<'tcx>>,
}

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn new(
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        adt_owner: OHAResultMap,
    ) -> SafeDropGraph<'tcx> {
        // handle variables
        let locals = &body.local_decls;
        let arg_size = body.arg_count;
        let mut values = Vec::<Value>::new();
        let mut alias = Vec::<usize>::new();
        let mut drop_record = Vec::<DropRecord>::new();
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
            alias.push(alias.len());
            drop_record.push(DropRecord::false_record());
            values.push(node);
        }

        let basicblocks = &body.basic_blocks;
        let mut blocks = Vec::<SccBlock<'tcx>>::new();
        let mut scc_indices = Vec::<usize>::new();
        let mut discriminants = FxHashMap::default();
        let mut terminators = Vec::new();

        // handle each basicblock
        for i in 0..basicblocks.len() {
            scc_indices.push(i); // we temporarily assign the scc id of ith basicblock with i.
            let iter = BasicBlock::from(i);
            let mut cur_bb = SccBlock::new(i, basicblocks[iter].is_cleanup);

            // handle general statements
            for stmt in &basicblocks[iter].statements {
                let span = stmt.source_info.span;
                match &stmt.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        let lv_place = *place;
                        let lv_local = place.local.as_usize();
                        cur_bb.assigned_locals.insert(lv_local);
                        match rvalue.clone() {
                            Rvalue::Use(operand) => {
                                match operand {
                                    Operand::Copy(rv_place) => {
                                        let rv_local = rv_place.local.as_usize();
                                        if values[lv_local].may_drop && values[rv_local].may_drop {
                                            let assign = Assignment::new(
                                                lv_place,
                                                rv_place,
                                                AssignType::Copy,
                                                span,
                                            );
                                            cur_bb.assignments.push(assign);
                                        }
                                    }
                                    Operand::Move(rv_place) => {
                                        let rv_local = rv_place.local.as_usize();
                                        if values[lv_local].may_drop && values[rv_local].may_drop {
                                            let assign = Assignment::new(
                                                lv_place,
                                                rv_place,
                                                AssignType::Move,
                                                span,
                                            );
                                            cur_bb.assignments.push(assign);
                                        }
                                    }
                                    Operand::Constant(constant) => {
                                        /* We should check the correctness due to the update of rustc */
                                        match constant.const_ {
                                            Const::Ty(_ty, const_value) => {
                                                if let Some(val) =
                                                    const_value.try_to_target_usize(tcx)
                                                {
                                                    cur_bb
                                                        .const_value
                                                        .push((lv_local, val as usize));
                                                }
                                            }
                                            Const::Unevaluated(_unevaluated, _ty) => {}
                                            Const::Val(const_value, _ty) => {
                                                if let Some(scalar) =
                                                    const_value.try_to_scalar_int()
                                                {
                                                    let val = scalar.to_uint(scalar.size());
                                                    cur_bb
                                                        .const_value
                                                        .push((lv_local, val as usize));
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            Rvalue::Ref(_, _, rv_place) | Rvalue::RawPtr(_, rv_place) => {
                                let rv_local = rv_place.local.as_usize();
                                if values[lv_local].may_drop && values[rv_local].may_drop {
                                    let assign =
                                        Assignment::new(lv_place, rv_place, AssignType::Copy, span);
                                    cur_bb.assignments.push(assign);
                                }
                            }
                            Rvalue::ShallowInitBox(operand, _) => {
                                /*
                                 * Original ShllowInitBox is a two-level pointer: lvl0 -> lvl1 -> lvl2
                                 * Since our alias analysis does not consider multi-level pointer,
                                 * We simplify it as: lvl0
                                 */
                                #[allow(clippy::map_entry)]
                                if !values[lv_local].fields.contains_key(&0) {
                                    let mut lvl0 = Value::new(values.len(), lv_local, false, true);
                                    lvl0.birth = values[lv_local].birth;
                                    lvl0.field_id = 0;
                                    values[lv_local].fields.insert(0, lvl0.index);
                                    alias.push(alias.len());
                                    drop_record.push(drop_record[lv_local]);
                                    values.push(lvl0);
                                }
                                match operand {
                                    Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                                        let rv_local = rv_place.local.as_usize();
                                        if values[lv_local].may_drop && values[rv_local].may_drop {
                                            let assign = Assignment::new(
                                                lv_place,
                                                rv_place,
                                                AssignType::InitBox,
                                                span,
                                            );
                                            cur_bb.assignments.push(assign);
                                        }
                                    }
                                    Operand::Constant(_) => {}
                                }
                            }
                            Rvalue::Cast(_, operand, _) => match operand {
                                Operand::Copy(rv_place) => {
                                    let rv_local = rv_place.local.as_usize();
                                    if values[lv_local].may_drop && values[rv_local].may_drop {
                                        let assign = Assignment::new(
                                            lv_place,
                                            rv_place,
                                            AssignType::Copy,
                                            span,
                                        );
                                        cur_bb.assignments.push(assign);
                                    }
                                }
                                Operand::Move(rv_place) => {
                                    let rv_local = rv_place.local.as_usize();
                                    if values[lv_local].may_drop && values[rv_local].may_drop {
                                        let assign = Assignment::new(
                                            lv_place,
                                            rv_place,
                                            AssignType::Move,
                                            span,
                                        );
                                        cur_bb.assignments.push(assign);
                                    }
                                }
                                Operand::Constant(_) => {}
                            },
                            Rvalue::Aggregate(_, operand_vec) => {
                                for operand in operand_vec {
                                    match operand {
                                        Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                                            let rv_local = rv_place.local.as_usize();
                                            if values[lv_local].may_drop
                                                && values[rv_local].may_drop
                                            {
                                                let assign = Assignment::new(
                                                    lv_place,
                                                    rv_place,
                                                    AssignType::Copy,
                                                    span,
                                                );
                                                cur_bb.assignments.push(assign);
                                            }
                                        }
                                        Operand::Constant(_) => {}
                                    }
                                }
                            }
                            Rvalue::Discriminant(rv_place) => {
                                let assign =
                                    Assignment::new(lv_place, rv_place, AssignType::Variant, span);
                                cur_bb.assignments.push(assign);
                                discriminants.insert(lv_local, rv_place.local.as_usize());
                            }
                            _ => {}
                        }
                    },
                    StatementKind::SetDiscriminant { place: _, variant_index: _ } => {
                        rap_warn!("SetDiscriminant: {:?} is not handled in RAPx!", stmt);
                    },
                    _ => {}
                }
            }

            let terminator = basicblocks[iter].terminator.clone().unwrap();
            terminators.push(terminator.kind.clone());
            // handle terminator statements
            match terminator.kind {
                TerminatorKind::Goto { target } => {
                    cur_bb.add_next(target.as_usize());
                }
                TerminatorKind::SwitchInt {
                    discr: _,
                    ref targets,
                } => {
                    cur_bb.switch_stmts.push(terminator.clone());
                    for (_, target) in targets.iter() {
                        cur_bb.add_next(target.as_usize());
                    }
                    cur_bb.add_next(targets.otherwise().as_usize());
                }
                TerminatorKind::Drop {
                    place: _,
                    target,
                    unwind,
                    replace: _,
                    drop: _,
                    async_fut: _,
                } => {
                    cur_bb.add_next(target.as_usize());
                    cur_bb.drops.push(terminator.clone());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Call {
                    ref func,
                    args: _,
                    destination: _,
                    ref target,
                    ref unwind,
                    call_source: _,
                    fn_span: _,
                } => {
                    if let Operand::Constant(c) = func {
                        if let &ty::FnDef(id, ..) = c.ty().kind() {
                            // for no_std crates without using alloc,
                            // dealloc will be never found, thus call dealloc_opt here
                            if id == drop()
                                || id == drop_in_place()
                                || id == manually_drop()
                                || dealloc_opt().map(|f| f == id).unwrap_or(false)
                            {
                                cur_bb.drops.push(terminator.clone());
                            }
                        }
                    }

                    if let Some(tt) = target {
                        cur_bb.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cur_bb.add_next(tt.as_usize());
                    }
                    cur_bb.calls.push(terminator.clone());
                }
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
                _ => {}
            }
            blocks.push(cur_bb);
        }

        rap_debug!("Values: {:?}", values);

        SafeDropGraph {
            def_id,
            tcx,
            span: body.span,
            blocks,
            values,
            arg_size,
            scc_indices,
            constants: FxHashMap::default(),
            discriminants,
            bug_records: BugRecords::new(),
            visit_times: 0,
            alias_set: alias,
            drop_record,
            adt_owner,
            child_scc: FxHashMap::default(),
            terminators,
        }
    }

    /// This the default tarjan algorithm for SCC detection.
    pub fn tarjan(
        &mut self,
        current: usize,
        stack: &mut Vec<usize>,
        dfn: &mut Vec<usize>,
        low: &mut Vec<usize>,
        time: &mut usize,
    ) {
        dfn[current] = *time; // the earlist arriving time of each node;
        low[current] = *time; // the earlist arriving time of each node's next nodes;
        *time += 1;
        stack.push(current);
        let nexts = self.blocks[current].next.clone();
        for next in nexts {
            if dfn[next] == 0 { // the node has not been visited yet; 
                self.tarjan(next, stack, dfn, low, time);
                low[current] = min(low[current], low[next]);
            } else if stack.contains(&next) {
                low[current] = min(low[current], dfn[next]);
            }
        }

        // generate SCC
        if dfn[current] == low[current] {
            let mut assigned_locals = FxHashSet::<usize>::default();
            let mut switch_target = Vec::new();
            let mut scc_block_set = FxHashSet::<usize>::default();
            let init_block = self.blocks[current].clone();
            loop {
                let node = stack.pop().unwrap();
                self.scc_indices[node] = current;
                if node == current {
                    // we have found all nodes of the current scc.
                    break;
                }
                self.blocks[current].basic_blocks.push(node);
                scc_block_set.insert(node);

                for local in &self.blocks[current].assigned_locals {
                    assigned_locals.insert(*local);
                }
                if let Some(target) = self.switch_target(self.tcx, node) {
                    if !self.blocks[current].switch_stmts.is_empty() {
                        switch_target.push((target, self.blocks[current].switch_stmts[0].clone()));
                    }
                }
                let nexts = self.blocks[node].next.clone();
                for i in nexts {
                    self.blocks[current].next.insert(i);
                }
            }
            switch_target.retain(|v| !assigned_locals.contains(&(v.0)));

            if !switch_target.is_empty() && switch_target.len() == 1 {
                let target_terminator = switch_target[0].1.clone();

                let TerminatorKind::SwitchInt { discr: _, targets } = target_terminator.kind else {
                    unreachable!();
                };

                self.child_scc
                    .insert(current, (init_block, targets, scc_block_set));
            }

            /* remove next nodes which are already in the current SCC */
            let mut to_remove = Vec::new();
            for i in self.blocks[current].next.iter() {
                if self.scc_indices[*i] == current {
                    to_remove.push(*i);
                }
            }
            for i in to_remove {
                self.blocks[current].next.remove(&i);
            }
            /* To ensure a resonable order of blocks within one SCC,
             * so that the scc can be directly used for followup analysis without referencing the
             * original graph.
             * */
            self.blocks[current].basic_blocks.reverse();
        }
    }

    // handle SCC
    pub fn solve_scc(&mut self) {
        let mut stack = Vec::<usize>::new();
        let mut dfn = vec![0; self.blocks.len()];
        let mut low = vec![0; self.blocks.len()];
        let mut time = 0;
        self.tarjan(0, &mut stack, &mut dfn, &mut low, &mut time);
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

    pub fn switch_target(&mut self, tcx: TyCtxt<'tcx>, block_index: usize) -> Option<usize> {
        let block = &self.blocks[block_index];
        if block.switch_stmts.is_empty() {
            return None;
        }

        if let TerminatorKind::SwitchInt { discr, .. } = &block.switch_stmts[0].kind {
            match discr {
                Operand::Copy(p) | Operand::Move(p) => {
                    let place = self.projection(tcx, false, *p);
                    Some(place)
                }
                _ => None,
            }
        } else {
            None
        }
    }
}
