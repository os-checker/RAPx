use rustc_data_structures::fx::FxHashSet;
use std::cmp;

pub trait Scc {
    fn find_scc(&mut self) {
        let mut stack = Vec::new();
        let mut instack = FxHashSet::<usize>::default(); // for fast query only
        let mut dfn = vec![0; self.get_size()];
        let mut low = vec![0; self.get_size()];
        let mut time = 0;
        self.tarjan(0, &mut stack, &mut instack, &mut dfn, &mut low, &mut time);
    }

    fn on_scc_found(&mut self, root: usize, scc_components: &[usize]); // callback 
    fn get_next(&mut self, root: usize) -> FxHashSet<usize>; //
    fn get_size(&mut self) -> usize; //
    //
    fn tarjan(
        &mut self,
        index: usize,
        stack: &mut Vec<usize>,
        instack: &mut FxHashSet<usize>,
        dfn: &mut Vec<usize>,
        low: &mut Vec<usize>,
        time: &mut usize,
    ) {
        dfn[index] = *time;
        low[index] = *time;
        *time += 1;
        stack.push(index);
        instack.insert(index);
        let nexts = self.get_next(index);
        for next in nexts {
            if dfn[next] == 0 {
                self.tarjan(next, stack, instack, dfn, low, time);
                low[index] = cmp::min(low[index], low[next]);
            } else if instack.contains(&next) {
                low[index] = cmp::min(low[index], dfn[next]);
            }
        }
        if dfn[index] == low[index] {
            let mut component = vec![index];
            while let Some(top) = stack.pop() {
                instack.remove(&top);
                if top == index {
                    break;
                }
                component.push(top);
            }
            self.on_scc_found(index, &component);
        }
    }
}
