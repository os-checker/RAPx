use super::doc_attr;
use rustc_ast::*;
use rustc_span::{DUMMY_SP, symbol::Ident};
use thin_vec::ThinVec;

pub(crate) fn create_dummy_ptr_deref_fn(krate: &mut Crate) {
    let ident = Ident::from_str("__raw_ptr_deref_dummy");

    let fn_decl = FnDecl {
        inputs: ThinVec::new(),
        output: FnRetTy::Default(DUMMY_SP),
    };

    let fn_sig = FnSig {
        decl: Box::new(fn_decl),
        header: FnHeader {
            safety: Safety::Unsafe(DUMMY_SP),
            constness: Const::No,
            ext: Extern::None,
            coroutine_kind: None,
        },
        span: DUMMY_SP,
    };
    let block = Block {
        stmts: ThinVec::new(),
        id: DUMMY_NODE_ID,
        rules: BlockCheckMode::Default,
        span: DUMMY_SP,
        tokens: None,
    };
    let ast_fn = Fn {
        defaultness: Defaultness::Final,
        ident,
        generics: Generics::default(),
        sig: fn_sig,
        contract: None,
        define_opaque: None,
        body: Some(Box::new(block)),
    };

    let item = Box::new(Item {
        attrs: ThinVec::from([doc_attr()]),
        id: DUMMY_NODE_ID,
        kind: ItemKind::Fn(Box::new(ast_fn)),
        vis: Visibility {
            span: DUMMY_SP,
            kind: VisibilityKind::Public,
            tokens: None,
        },
        span: DUMMY_SP,
        tokens: None,
    });
    krate.items.push(item);
}
