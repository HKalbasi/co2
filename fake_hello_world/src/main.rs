#![feature(rustc_private)]

use rustc_public_generative as gen;

fn main() {
    gen::generate(|ctx, _deps| {
        let file = ctx.add_custom_file("<generated>", "hello world");
        let span = ctx.span(file, 0, 1);

        let body = gen::MirBody {
            locals: vec![
                gen::MirLocalDecl {
                    ty: gen::MirTy::Unit,
                    mutability: gen::MirMutability::Not,
                    span,
                    name: None,
                },
                gen::MirLocalDecl {
                    ty: gen::MirTy::Isize,
                    mutability: gen::MirMutability::Not,
                    span,
                    name: None,
                },
            ],
            arg_count: 0,
            blocks: vec![
                gen::MirBasicBlock {
                    statements: vec![],
                    terminator: gen::MirTerminator::Call {
                        func: gen::MirOperand::Const(gen::MirConst::Fn {
                            name: "write".to_string(),
                        }),
                        args: vec![
                            gen::MirOperand::Const(gen::MirConst::I32(1)),
                            gen::MirOperand::Const(gen::MirConst::ByteStr(
                                b"Hello ggg world\n".to_vec(),
                            )),
                            gen::MirOperand::Const(gen::MirConst::Usize(16)),
                        ],
                        destination: Some((
                            gen::MirPlace {
                                local: 1,
                                projection: vec![],
                            },
                            1,
                        )),
                    },
                },
                gen::MirBasicBlock {
                    statements: vec![],
                    terminator: gen::MirTerminator::Return,
                },
            ],
            span,
        };

        gen::CurrentCrateInfo {
            crate_name: "fake_hello_world".to_string(),
            functions: vec![gen::FunctionInfo {
                name: "main".to_string(),
                body,
            }],
        }
    });
}
