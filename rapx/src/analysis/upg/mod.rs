/*
 * This module generates the unsafety propagation graph for each Rust module in the target crate.
 */
pub mod fn_collector;
pub mod generate_dot;
pub mod hir_visitor;
pub mod render_module_dot;
pub mod std_upg;
pub mod upg_graph;

use crate::analysis::utils::{draw_dot::render_dot_graphs, fn_info::*};
use fn_collector::FnCollector;
use generate_dot::{NodeType, UPGUnit};
use hir_visitor::ContainsUnsafe;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty,
    ty::TyCtxt,
};
use std::collections::{HashSet, VecDeque};
use upg_graph::IsolationGraphNode;

#[derive(PartialEq)]
pub enum TargetCrate {
    Std,
    Other,
}

pub struct UPGAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub nodes: Vec<IsolationGraphNode>,
    pub related_func_def_id: Vec<DefId>,
    pub uigs: Vec<UPGUnit>,
    pub single: Vec<UPGUnit>,
}

impl<'tcx> UPGAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            nodes: Vec::new(),
            related_func_def_id: Vec::new(),
            uigs: Vec::new(),
            single: Vec::new(),
        }
    }

    pub fn start(&mut self, ins: TargetCrate) {
        match ins {
            TargetCrate::Std => {
                self.audit_std_unsafe();
                return;
            }
            _ => {
                /* Type of collected data: FxHashMap<Option<HirId>, Vec<(BodyId, Span)>>;
                 * For a function, the Vec contains only one entry;
                 * For implementations of structs and traits, the Vec contains all associated 
                 * function entries.
                 */
                let fns = FnCollector::collect(self.tcx);
                for vec in fns.values() {
                    for (body_id, _span) in vec { // each function or associated function in
                                                  // structs and traits
                        let (fn_unsafe, block_unsafe) =
                            ContainsUnsafe::contains_unsafe(self.tcx, *body_id);
                        // map the function body_id back to its def_id;
                        let def_id = self.tcx.hir_body_owner_def_id(*body_id).to_def_id();
                        if fn_unsafe | block_unsafe {
                            self.insert_upg(
                                def_id,
                                get_callees(self.tcx, def_id),
                                get_cons(self.tcx, def_id),
                            );
                        }
                    }
                }
                self.render_module_dot();
            }
        }
    }

    pub fn render_dot(&mut self) {
        let mut dot_strs = Vec::new();
        for uig in &self.uigs {
            let dot_str = uig.generate_dot_str();
            let caller_name = get_cleaned_def_path_name(self.tcx, uig.caller.0);
            dot_strs.push((caller_name, dot_str));
        }
        for uig in &self.single {
            let dot_str = uig.generate_dot_str();
            let caller_name = get_cleaned_def_path_name(self.tcx, uig.caller.0);
            dot_strs.push((caller_name, dot_str));
        }
        render_dot_graphs(dot_strs);
    }

    pub fn filter_and_extend_unsafe(&mut self) {
        let related_items = FnCollector::collect(self.tcx);
        let mut queue = VecDeque::new();
        let mut visited = std::collections::HashSet::new();

        //'related_items' is used for recording whether this api is in crate or not
        //then init the queue, including all unsafe func and interior unsafe func
        for vec in related_items.values() {
            for (body_id, _) in vec {
                let (function_unsafe, block_unsafe) =
                    ContainsUnsafe::contains_unsafe(self.tcx, *body_id);
                let body_did = self.tcx.hir_body_owner_def_id(*body_id).to_def_id();
                if function_unsafe || block_unsafe {
                    let node_type = get_type(self.tcx, body_did);
                    let name = self.get_name(body_did);
                    let mut new_node =
                        IsolationGraphNode::new(body_did, node_type, name, function_unsafe, true);
                    if node_type == 1 {
                        new_node.constructors = self.search_constructor(body_did);
                    }
                    self.nodes.push(new_node);
                    self.related_func_def_id.push(body_did);
                    if visited.insert(body_did) {
                        queue.push_back(body_did);
                    }
                }
            }
        }

        // BFS handling the queue
        while let Some(body_did) = queue.pop_front() {
            if !self.is_crate_api_node(body_did) {
                continue;
            }
            // get all unsafe callees in current crate api and insert to queue
            let callees = self.visit_node_callees(body_did);
            for &callee_id in &callees {
                if visited.insert(callee_id) {
                    queue.push_back(callee_id);
                }
            }
        }
    }

    pub fn check_if_node_exists(&self, body_did: DefId) -> bool {
        if let Some(_node) = self.nodes.iter().find(|n| n.node_id == body_did) {
            return true;
        }
        false
    }

    pub fn get_name(&self, body_did: DefId) -> String {
        let tcx = self.tcx;
        let mut name = String::new();
        if let Some(assoc_item) = tcx.opt_associated_item(body_did) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct name
                let ty = tcx.type_of(impl_id).skip_binder();
                let type_name = ty.to_string();
                let type_name = type_name.split('<').next().unwrap_or("").trim();
                // get method name
                let method_name = tcx.def_path(body_did).to_string_no_crate_verbose();
                let method_name = method_name.split("::").last().unwrap_or("");
                name = format!("{}.{}", type_name, method_name);
            }
        } else {
            let verbose_name = tcx.def_path(body_did).to_string_no_crate_verbose();
            name = verbose_name.split("::").last().unwrap_or("").to_string();
        }
        name
    }

    pub fn search_constructor(&mut self, def_id: DefId) -> Vec<DefId> {
        let tcx = self.tcx;
        let mut constructors = Vec::new();
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct ty
                let ty = tcx.type_of(impl_id).skip_binder();
                if let Some(adt_def) = ty.ty_adt_def() {
                    let adt_def_id = adt_def.did();
                    let impl_vec = get_impls_for_struct(self.tcx, adt_def_id);
                    for impl_id in impl_vec {
                        let associated_items = tcx.associated_items(impl_id);
                        for item in associated_items.in_definition_order() {
                            if let ty::AssocKind::Fn {
                                name: _,
                                has_self: _,
                            } = item.kind
                            {
                                let item_def_id = item.def_id;
                                if get_type(self.tcx, item_def_id) == 0 {
                                    constructors.push(item_def_id);
                                    self.check_and_insert_node(item_def_id);
                                    self.set_method_for_constructor(item_def_id, def_id);
                                }
                            }
                        }
                    }
                }
            }
        }
        constructors
    }

    pub fn get_cons_counts(&self, def_id: DefId) -> Vec<DefId> {
        let tcx = self.tcx;
        let mut constructors = Vec::new();
        let mut methods = Vec::new();
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct ty
                let ty = tcx.type_of(impl_id).skip_binder();
                if let Some(adt_def) = ty.ty_adt_def() {
                    let adt_def_id = adt_def.did();
                    let impl_vec = get_impls_for_struct(self.tcx, adt_def_id);
                    for impl_id in impl_vec {
                        let associated_items = tcx.associated_items(impl_id);
                        for item in associated_items.in_definition_order() {
                            if let ty::AssocKind::Fn {
                                name: _,
                                has_self: _,
                            } = item.kind
                            {
                                let item_def_id = item.def_id;
                                if get_type(self.tcx, item_def_id) == 0 {
                                    constructors.push(item_def_id);
                                } else if get_type(self.tcx, item_def_id) == 1 {
                                    methods.push(item_def_id);
                                }
                            }
                        }
                    }
                }
                print!("struct:{:?}", ty);
            }
        }
        println!("--------methods:{:?}", methods.len());
        constructors
    }

    // visit the func body and record all its unsafe callees and modify visited_tag
    pub fn visit_node_callees(&mut self, def_id: DefId) -> Vec<DefId> {
        let mut callees = Vec::new();
        let tcx = self.tcx;
        if tcx.is_mir_available(def_id) {
            let body = tcx.optimized_mir(def_id);
            for bb in body.basic_blocks.iter() {
                if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
                    if let Operand::Constant(func_constant) = func {
                        if let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() {
                            if check_safety(self.tcx, *callee_def_id) {
                                if !callees.contains(callee_def_id) {
                                    callees.push(*callee_def_id);
                                    if !self.check_if_node_exists(*callee_def_id) {
                                        self.check_and_insert_node(*callee_def_id);
                                        self.set_caller_for_callee(def_id, *callee_def_id);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if let Some(node) = self.nodes.iter_mut().find(|n| n.node_id == def_id) {
            node.callees = callees.clone();
            node.visited_tag = true;
        }
        callees
    }

    pub fn is_crate_api_node(&self, body_did: DefId) -> bool {
        self.related_func_def_id.contains(&body_did)
    }

    pub fn check_and_insert_node(&mut self, body_did: DefId) {
        if self.check_if_node_exists(body_did) {
            return;
        }
        let node_type = get_type(self.tcx, body_did);
        let name = self.get_name(body_did);
        let is_crate_api = self.is_crate_api_node(body_did);
        let node_safety = check_safety(self.tcx, body_did);
        let mut new_node =
            IsolationGraphNode::new(body_did, node_type, name, node_safety, is_crate_api);
        if node_type == 1 {
            new_node.constructors = self.search_constructor(body_did);
        }
        new_node.visited_tag = false;
        self.nodes.push(new_node);
    }

    pub fn set_method_for_constructor(&mut self, constructor_did: DefId, method_did: DefId) {
        if let Some(node) = self
            .nodes
            .iter_mut()
            .find(|node| node.node_id == constructor_did)
        {
            if !node.methods.contains(&method_did) {
                node.methods.push(method_did);
            }
        }
    }

    pub fn set_caller_for_callee(&mut self, caller_did: DefId, callee_did: DefId) {
        if let Some(node) = self
            .nodes
            .iter_mut()
            .find(|node| node.node_id == callee_did)
        {
            if !node.callers.contains(&caller_did) {
                node.callers.push(caller_did);
            }
        }
    }

    pub fn show_nodes(&self) {
        for node in &self.nodes {
            println!(
                "name:{:?},safety:{:?},calles:{:?}",
                node.node_name, node.node_unsafety, node.callees
            );
        }
    }

    pub fn insert_upg(
        &mut self,
        caller: DefId,
        callee_set: HashSet<DefId>,
        caller_cons: Vec<NodeType>,
    ) {
        let mut pairs = HashSet::new();
        for callee in &callee_set {
            let callee_cons = Vec::new();
            pairs.insert((generate_node_ty(self.tcx, *callee), callee_cons));
        }
        if !check_safety(self.tcx, caller) && callee_set.is_empty() {
            return;
        }
        let mut_methods_set = get_all_mutable_methods(self.tcx, caller);
        let mut_methods = mut_methods_set.keys().copied().collect();
        let uig = UPGUnit::new_by_pair(
            generate_node_ty(self.tcx, caller),
            caller_cons,
            pairs,
            mut_methods,
        );
        if !callee_set.is_empty() {
            self.uigs.push(uig);
        } else {
            self.single.push(uig);
        }
    }
}
