#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum FnType {
    Fn,
    Method,
    Constructor,
}
