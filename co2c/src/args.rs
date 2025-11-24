//! Handles parsing cli-arguments without library.

use std::path::PathBuf;

use anyhow::bail;

// const VERSION: &str = concat!(
//     env!("CARGO_PKG_NAME"),
//     " ",
//     env!("CARGO_PKG_VERSION"),
//     "\nPhilipp Rados\n",
//     "https://github.com/PhilippRados/wrecc"
// );

const VERSION: &str = r#"gcc (GCC) 15.2.1 20251112
Copyright (C) 2025 Free Software Foundation, Inc.
This is free software; see the source for copying conditions.  There is NO
warranty; not even for MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
"#;

const USAGE: &str = "\
usage: wrecc [-o <file>] [-I <dir>] [-D <name>=<value>]
             [-L <dir>] [-l <name>] [-E] [-S] [-c] [--dump-ast]
             [--no-color] [-h | --help] [-v] <file>";

const HELP: &str = "usage: wrecc [options] <file>
options:
    -o | --output <file>                Specifies the output-file to write to
    -I | --include-dir <dir>            Adds <dir> to the directories to be searched for using #include
    -D | --define <macro-name>=<value>  Defines a new object-like macro
    -L | --library-path <dir>           Adds <dir> to the directories to the library search paths (passed as -L<dir> to linker)
    -l | --library <name>               Looks for shared libraries with <name> in library search paths (passed as -l<name> to linker)
    -E | --preprocess-only              Stops evaluation after preprocessing printing the preprocessed source
    -S | --compile-only                 Stops evaluation after compiling resulting in a .s file
    -c | --no-link                      Stops evaluation after assembling resulting in a .o file
         --dump-ast                     Displays the AST produced by the parser while also compiling program as usual
         --no-color                     Errors are printed without color
    -h                                  Prints usage information
    --help                              Prints elaborate help information
    -v | --version                      Prints version information

file:
    One or more C source files to be compiled";

fn sys_info(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(0);
}

/// Struct holding all possible cli-args to be passed when running `wrecc`
#[derive(Debug)]
pub struct CliOptions {
    /// Required argument specifying file to compile
    pub files: Vec<PathBuf>,

    /// Optional argument specifying output-file to write to
    pub output_path: Option<PathBuf>,

    /// Stops evaluation after preprocessing printing the preprocessed source
    pub preprocess_only: bool,

    /// Stops evaluation after compiling resulting in a .s file
    pub compile_only: bool,

    /// Stops evaluation after assembling resulting in an .o file
    pub no_link: bool,

    /// Displays AST while also compiling program as usual
    pub dump_ast: bool,

    /// Errors are printed without color
    pub no_color: bool,

    /// Directories specified by user to be searched after `#include "..."` and before `#include <...>`
    pub user_include_dirs: Vec<PathBuf>,

    /// All definitions passed as cli-arguments
    /// INFO: duplicate definitions are caught in preprocessor
    pub defines: Vec<(String, String)>,

    /// Adds a path to the directories to be searched during linking (passed as `-L<dir>` to linker)
    pub lib_paths: Vec<PathBuf>,

    /// Adds name to the shared libraries going to be linked (passed as `-l<name>` to linker)
    pub shared_libs: Vec<String>,

    pub optimize: bool,
    pub debug_info: bool,
}
impl CliOptions {
    fn new() -> CliOptions {
        CliOptions {
            files: Vec::new(),
            user_include_dirs: Vec::new(),
            defines: Vec::new(),
            lib_paths: Vec::new(),
            shared_libs: Vec::new(),
            output_path: None,
            preprocess_only: false,
            compile_only: false,
            no_link: false,
            dump_ast: false,
            no_color: false,
            optimize: false,
            debug_info: false,
        }
    }
    /// Parses all passed cli-args and builds [CliOptions] with them.<br>
    /// INFO: every argument needs to be seperated by whitespace meaning that options requiring a
    /// following argument like in `wrecc -L` have to be seperated by a whitespace:<br>
    /// `wrecc -Iinclude` => error invalid argument `-Iinclude`<br>
    /// `wrecc -I include` => valid<br>
    /// I am planning to allow this in the future though.
    pub fn parse() -> anyhow::Result<CliOptions> {
        let mut cli_options = CliOptions::new();
        let mut args = std::env::args()
            .collect::<Vec<String>>()
            .into_iter()
            .skip(1)
            .flat_map(|arg| {
                if let Some(rest) = arg.strip_prefix("-I")
                    && !rest.is_empty()
                {
                    vec!["-I".to_owned(), rest.to_owned()]
                } else if let Some(rest) = arg.strip_prefix("-D")
                    && !rest.is_empty()
                {
                    vec!["-D".to_owned(), rest.to_owned()]
                } else {
                    vec![arg]
                }
            });

        while let Some(arg) = args.next() {
            if arg.starts_with('-') {
                match arg.as_str() {
                    "-o" | "--output" => {
                        if let Some(file) = args.next() {
                            cli_options.output_path = Some(PathBuf::from(file));
                        } else {
                            bail!("expected file following '{}' option", arg);
                        }
                    }
                    "-I" | "--include-dir" => {
                        if let Some(dir) = args.next() {
                            cli_options.user_include_dirs.push(PathBuf::from(dir))
                        } else {
                            bail!("expected dir following '{}' option", arg);
                        }
                    }
                    "-D" | "--define" => {
                        let Some(arg) = args.next() else {
                            bail!("expected macro-definition following '{}' option", arg);
                        };

                        let (macro_name, value) = arg
                            .split_once('=')
                            // if no '=' found then `-D foo`, same as `-D foo=1`
                            .unwrap_or((&arg, "1"));

                        cli_options
                            .defines
                            .push((macro_name.to_string(), value.to_string()));
                    }
                    "-L" | "--library-path" => {
                        if let Some(path) = args.next() {
                            cli_options.lib_paths.push(PathBuf::from(path));
                        } else {
                            bail!("expected directory path following '{}' option", arg);
                        }
                    }
                    "-l" | "--library" => {
                        if let Some(lib_name) = args.next() {
                            cli_options.shared_libs.push(lib_name);
                        } else {
                            bail!("expected library name following '{}' option", arg);
                        }
                    }
                    "-E" | "--preprocess-only" => cli_options.preprocess_only = true,
                    "-S" | "--compile-only" => cli_options.compile_only = true,
                    "-c" | "--no-link" => cli_options.no_link = true,
                    "-g" => cli_options.debug_info = true,
                    "-O2" => cli_options.optimize = true,
                    "--dump-ast" => cli_options.dump_ast = true,
                    "--no-color" => cli_options.no_color = true,
                    "-h" => sys_info(USAGE),
                    "--help" => sys_info(HELP),
                    "-v" | "--version" => sys_info(VERSION),
                    "-fno-builtin" | "-fPIC" => (),
                    _ => bail!("illegal option '{}'", arg),
                }
            } else {
                cli_options.files.push(PathBuf::from(arg));
            }
        }

        if cli_options.output_path.is_some() && cli_options.files.len() > 1 {
            if cli_options.preprocess_only || cli_options.compile_only || cli_options.no_link {
                bail![
                    "cannot specify '-o' with '-E', '-S' or '-c' when compiling multiple files"
                        .to_string(),
                ];
            }
        }

        if cli_options.files.is_empty() {
            bail!["no input files given"]
        } else if let Some(file) = cli_options
            .files
            .iter()
            .find(|f| !matches!(f.extension().map(|e| e.to_str()), Some(Some("c"))))
        {
            bail!("file '{}' is not a valid C source file", file.display());
        } else {
            Ok(cli_options)
        }
    }
}
