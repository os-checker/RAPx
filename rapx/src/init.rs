use crate::{
    rap_info,
    utils::source::{get_crate_num, get_fn_name, get_fn_name_byid},
};
use rustc_hir::def_id::DefId;
use rustc_middle::{middle::exported_symbols::ExportedSymbol::*, ty::TyCtxt};
use rustc_span::def_id::CrateNum;
use std::sync::OnceLock;

pub static DEALLOC: OnceLock<usize> = OnceLock::new();
pub static MANUALLYDROP: OnceLock<usize> = OnceLock::new();
pub static ASSUME_INIT_DROP: OnceLock<usize> = OnceLock::new();
pub static DROP: OnceLock<usize> = OnceLock::new();
pub static COPY_TO: OnceLock<usize> = OnceLock::new();
pub static COPY_TO_NONOVERLAPPING: OnceLock<usize> = OnceLock::new();
pub static COPY_FROM: OnceLock<usize> = OnceLock::new();
pub static COPY_FROM_NONOVERLAPPING: OnceLock<usize> = OnceLock::new();
pub static DROP_IN_PLACE: OnceLock<usize> = OnceLock::new();
pub static CLONE: OnceLock<usize> = OnceLock::new();
pub static CALL_MUT: OnceLock<usize> = OnceLock::new();

fn set_id(tcx: TyCtxt, def_id: DefId) {
    if let Some(fn_name) = get_fn_name(tcx, def_id) {
        rap_info!("{}: {}", def_id.index.as_usize(), fn_name);
        let _ = match fn_name.as_str() {
            s if s.contains("alloc::dealloc") => DEALLOC.set(def_id.index.as_usize()),
            s if s.contains("ManuallyDrop::<std::boxed::Box<i32>>::drop") => {
                MANUALLYDROP.set(def_id.index.as_usize())
            }
            s if s.contains("assume_init_drop") => ASSUME_INIT_DROP.set(def_id.index.as_usize()),
            s if s.contains("mem::drop") => DROP.set(def_id.index.as_usize()),
            s if s.contains("copy_to") => COPY_TO.set(def_id.index.as_usize()),
            s if s.contains("copy_to_nonoverlapping") => {
                COPY_TO_NONOVERLAPPING.set(def_id.index.as_usize())
            }
            s if s.contains("copy_from") => COPY_FROM.set(def_id.index.as_usize()),
            s if s.contains("copy_from_nonoverlapping") => {
                COPY_FROM_NONOVERLAPPING.set(def_id.index.as_usize())
            }
            s if s.contains("ptr::drop_in_place") => DROP_IN_PLACE.set(def_id.index.as_usize()),
            s if s.contains("clone::Clone") => CLONE.set(def_id.index.as_usize()),
            s if s.contains("call_mut") => CALL_MUT.set(def_id.index.as_usize()),
            _ => Ok(()),
        };
    }
}

pub fn set_crate_fn(tcx: TyCtxt, crate_num: CrateNum) {
    let generic_sym = tcx.exported_generic_symbols(crate_num);
    let non_generic_sym = tcx.exported_non_generic_symbols(crate_num);
    for sym in non_generic_sym {
        match sym.0 {
            NonGeneric(def_id) => {
                set_id(tcx, def_id);
            }
            _ => {}
        }
    }
    for sym in generic_sym {
        match sym.0 {
            Generic(def_id, _) => {
                set_id(tcx, def_id);
            }
            _ => {}
        }
    }
}

pub fn set_intrinsic_fn(tcx: TyCtxt) {
    rap_info!("Init fns");
    if let Some(crate_num) = get_crate_num(tcx, "alloc") {
        rap_info!("find crate alloc, num {:?}", crate_num);
        set_crate_fn(tcx, crate_num);
    }
    if let Some(crate_num) = get_crate_num(tcx, "core") {
        rap_info!("find crate core, num {:?}", crate_num);
        set_crate_fn(tcx, crate_num);
    }
    if let Some(crate_num) = get_crate_num(tcx, "std") {
        rap_info!("find crate std, num {:?}", crate_num);
        set_crate_fn(tcx, crate_num);
    }
}
