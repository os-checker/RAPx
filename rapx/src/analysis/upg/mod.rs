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
use generate_dot::UPGUnit;
use hir_visitor::ContainsUnsafe;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    ty,
    ty::TyCtxt,
};
use std::collections::HashSet;
use upg_graph::IsolationGraphNode;

use super::utils::types::FnType;

#[derive(PartialEq)]
pub enum TargetCrate {
    Std,
    Other,
}

pub struct UPGAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub nodes: Vec<IsolationGraphNode>, // This field seems reserved for senryx;
    pub related_func_def_id: Vec<DefId>,
    pub upgs: Vec<UPGUnit>,
}

impl<'tcx> UPGAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            nodes: Vec::new(),
            related_func_def_id: Vec::new(),
            upgs: Vec::new(),
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
                    for (body_id, _span) in vec {
                        // each function or associated function in
                        // structs and traits
                        let (fn_unsafe, block_unsafe) =
                            ContainsUnsafe::contains_unsafe(self.tcx, *body_id);
                        // map the function body_id back to its def_id;
                        let def_id = self.tcx.hir_body_owner_def_id(*body_id).to_def_id();
                        if fn_unsafe | block_unsafe {
                            let callees = get_callees(self.tcx, def_id);
                            let constructors = get_cons(self.tcx, def_id);
                            self.insert_upg(def_id, callees, constructors);
                        }
                    }
                }
                self.render_module_dot();
            }
        }
    }

    pub fn render_dot(&mut self) {
        let mut dot_strs = Vec::new();
        for upg in &self.upgs {
            let dot_str = upg.generate_dot_str();
            let caller_name = get_cleaned_def_path_name(self.tcx, upg.caller.0);
            dot_strs.push((caller_name, dot_str));
        }
        render_dot_graphs(dot_strs);
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
                                if get_type(self.tcx, item_def_id) == FnType::Constructor {
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
        if node_type == FnType::Method {
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

    pub fn is_crate_api_node(&self, body_did: DefId) -> bool {
        self.related_func_def_id.contains(&body_did)
    }

    pub fn insert_upg(&mut self, caller: DefId, callees: HashSet<DefId>, caller_cons: Vec<DefId>) {
        let caller_typed = append_fn_with_types(self.tcx, caller);
        let mut callees_typed = HashSet::new();
        for callee in &callees {
            callees_typed.insert(append_fn_with_types(self.tcx, *callee));
        }
        let mut cons_typed = HashSet::new();
        for con in &caller_cons {
            cons_typed.insert(append_fn_with_types(self.tcx, *con));
        }
        if !check_safety(self.tcx, caller) && callees.is_empty() {
            return;
        }
        let mut_methods_set = get_all_mutable_methods(self.tcx, caller);
        let mut_methods = mut_methods_set.keys().copied().collect();
        let upg = UPGUnit::new(caller_typed, callees_typed, cons_typed, mut_methods);
        self.upgs.push(upg);
    }
}
