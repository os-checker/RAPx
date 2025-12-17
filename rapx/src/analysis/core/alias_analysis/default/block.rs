use super::assign::*;
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::Terminator;

/// Each block is a strongly-connected component on the control-flow graph.
#[derive(Debug, Clone)]
pub struct Block<'tcx> {
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub assignments: Vec<Assignment<'tcx>>,
    pub const_value: Vec<(usize, usize)>,
    pub assigned_locals: FxHashSet<usize>,
    pub terminator: Term<'tcx>,
    // If this block is the dominitor of a SCC, we record all basic blocks of the SCC.
    pub dominated_scc_bbs: Vec<usize>,
}

#[derive(Debug, Clone)]
pub enum Term<'tcx> {
    Call(Terminator<'tcx>),
    Drop(Terminator<'tcx>),
    Switch(Terminator<'tcx>),
    None,
}

impl<'tcx> Block<'tcx> {
    pub fn new(index: usize, is_cleanup: bool) -> Block<'tcx> {
        Block {
            index,
            is_cleanup,
            next: FxHashSet::<usize>::default(),
            assignments: Vec::<Assignment<'tcx>>::new(),
            const_value: Vec::<(usize, usize)>::new(),
            assigned_locals: FxHashSet::<usize>::default(),
            terminator: Term::None,
            dominated_scc_bbs: Vec::<usize>::new(),
            //scc_outer: RefCell::new(None),
        }
    }

    pub fn add_next(&mut self, index: usize) {
        self.next.insert(index);
    }
}
