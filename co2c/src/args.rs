use clap::{ArgAction, Parser};

#[derive(Debug, Parser)]
#[command(
    name = "cc-wrapper",
    version,
    about = "A simple C compiler wrapper using clap"
)]
pub struct CcFlags {
    /// Include directories (`-I <dir>`)
    #[arg(short = 'I', value_name = "DIR", num_args = 1.., action = ArgAction::Append)]
    pub include_dirs: Vec<String>,

    /// Library search paths (`-L <dir>`)
    #[arg(short = 'L', value_name = "DIR", num_args = 1.., action = ArgAction::Append)]
    pub library_dirs: Vec<String>,

    /// Preprocessor defines (`-DNAME` or `-DNAME=VALUE`)
    #[arg(short = 'D', value_name = "DEFINE", num_args = 1.., action = ArgAction::Append)]
    pub defines: Vec<String>,

    /// Undefine preprocessor macros (`-U NAME`)
    #[arg(short = 'U', value_name = "NAME", num_args = 1.., action = ArgAction::Append)]
    pub undefines: Vec<String>,

    /// Linked libraries (`-l <lib>`)
    #[arg(short = 'l', value_name = "LIB", num_args = 1.., action = ArgAction::Append)]
    pub libs: Vec<String>,

    /// Optimization level (`-O0`, `-O1`, `-O2`, `-O3`, `-Ofast`, etc.)
    #[arg(short = 'O', value_name = "LEVEL", default_value = "0")]
    pub optimization: String,

    /// Output file (`-o <file>`)
    #[arg(short = 'o', value_name = "FILE")]
    pub output: Option<String>,

    /// Enable Position Independent Code (`-fPIC`)
    #[arg(long = "fPIC", action = ArgAction::SetTrue)]
    pub fpic: bool,

    /// Enable all warnings (`-Wall`)
    #[arg(long = "Wall", action = ArgAction::SetTrue)]
    pub wall: bool,

    /// Treat warnings as errors (`-Werror`)
    #[arg(long = "Werror", action = ArgAction::SetTrue)]
    pub werror: bool,

    /// Specify target triple (`--target <triple>`)
    #[arg(long = "target", value_name = "TRIPLE")]
    pub target: Option<String>,

    /// Specify system root (`--sysroot <dir>`)
    #[arg(long = "sysroot", value_name = "DIR")]
    pub sysroot: Option<String>,

    /// Set language standard (`-std=<standard>`)
    #[arg(long = "std", value_name = "STANDARD")]
    pub std: Option<String>,

    /// Enable debug info (`-g`)
    #[arg(short = 'g', action = ArgAction::SetTrue)]
    pub debug: bool,

    /// Extra unrecognized flags (e.g. `-pthread`, `-fno-exceptions`)
    #[arg(
        value_name = "EXTRA_FLAGS",
        trailing_var_arg = true,
        allow_hyphen_values = true,
        num_args = 0..
    )]
    pub extra_flags: Vec<String>,

    /// Input source files
    #[arg(value_name = "SOURCE", num_args = 1..)]
    pub sources: Vec<String>,
}
