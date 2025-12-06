#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum FnKind {
    Fn,
    Method,
    Constructor,
}
