use crate::def_id::*;
use rustc_span::def_id::DefId;

pub fn is_corner_case(def_id: DefId) -> bool {
    if def_id == call_mut() || def_id == clone() || def_id == take() {
        return true;
    }
    return false;
}
