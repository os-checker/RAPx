use super::assign::*;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::Terminator;
use std::cell::RefCell;

/// Each block is a strongly-connected component on the control-flow graph.
#[derive(Debug, Clone)]
pub struct Block<'tcx> {
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub assignments: Vec<Assignment<'tcx>>,
    pub calls: Vec<Terminator<'tcx>>,
    pub drops: Vec<Terminator<'tcx>>,
    //store the index of the basic blocks of the SCC.
    pub const_value: Vec<(usize, usize)>,
    //store switch stmts in current block for the path filtering in path-sensitive analysis.
    pub switch_stmt: Option<Terminator<'tcx>>,
    pub assigned_locals: FxHashSet<usize>,
    // If this block is the dominitor of a SCC, we record all basic blocks of the SCC.
    pub dominated_scc_bbs: Vec<usize>,
    //store const values defined in this block, i.e., which id has what value;
    // (SwitchInt target, enum index) -> outside nodes.
    pub scc_outer: SccOuter,
}

pub type SccOuter = RefCell<Option<FxHashMap<(usize, usize), Vec<usize>>>>;

impl<'tcx> Block<'tcx> {
    pub fn new(index: usize, is_cleanup: bool) -> Block<'tcx> {
        Block {
            index,
            is_cleanup,
            next: FxHashSet::<usize>::default(),
            assignments: Vec::<Assignment<'tcx>>::new(),
            calls: Vec::<Terminator<'tcx>>::new(),
            drops: Vec::<Terminator<'tcx>>::new(),
            dominated_scc_bbs: Vec::<usize>::new(),
            const_value: Vec::<(usize, usize)>::new(),
            switch_stmt: None,
            assigned_locals: FxHashSet::<usize>::default(),
            scc_outer: RefCell::new(None),
        }
    }

    pub fn add_next(&mut self, index: usize) {
        self.next.insert(index);
    }
}
