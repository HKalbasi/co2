use rustc_public_generative::rustc_public::{
    DefId,
    ty::{AdtDef, FnDef, Span},
};

pub enum MirOwnerInfo {
    CloneMethod(AdtDef),
    StaticZeroed,
    EnumConstZeroed,
    EnumConstPrevPlus(DefId, Span),
    EnumConstExplicit {
        initializer: co2_parser::Spanned<co2_parser::Expression>,
    },
    Static {
        initializer: co2_parser::Spanned<co2_parser::Initializer>,
    },
    Fn {
        def: FnDef,
        param_names: Vec<String>,
        body_tokens: Vec<co2_parser::Spanned<co2_parser::Token>>,
    },
}
