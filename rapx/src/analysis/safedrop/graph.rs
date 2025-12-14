use super::bug_records::*;
use crate::analysis::core::{
    alias_analysis::default::graph::MopGraph, ownedheap_analysis::OHAResultMap,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use std::{fmt, usize, vec::Vec};

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
    pub mop_graph: MopGraph<'tcx>,
    pub bug_records: BugRecords,
    // a threhold to avoid path explosion.
    pub drop_record: Vec<DropRecord>,
    // analysis of heap item
    pub adt_owner: OHAResultMap,
}

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, adt_owner: OHAResultMap) -> Self {
        let mop_graph = MopGraph::new(tcx, def_id);
        let mut drop_record = Vec::<DropRecord>::new();
        for _v in &mop_graph.values {
            drop_record.push(DropRecord::false_record());
        }

        SafeDropGraph {
            mop_graph,
            bug_records: BugRecords::new(),
            drop_record,
            adt_owner,
        }
    }
}

impl<'tcx> std::fmt::Display for SafeDropGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SafeDropGraph {{")?;
        writeln!(f, "  MopGraph: {}", self.mop_graph)?;
        write!(f, "}}")
    }
}
