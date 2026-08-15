use clap::Parser;

#[derive(Parser, Debug)]
#[command(name = "co2_test_harness")]
pub struct Cli {
    /// Optional glob matched against the workspace-relative test path.
    pub filter: Option<String>,

    /// Read glob filters from this file (one per line; blank lines and `#` comments
    /// are ignored). Tests matching any of the filters are run.
    #[arg(long, conflicts_with = "filter")]
    pub filter_file: Option<std::path::PathBuf>,

    /// Write the workspace-relative paths of failing tests to this file
    /// (default: `fail_list.txt` in the workspace root). Consume later with --filter-file.
    #[arg(long)]
    pub fail_list: Option<std::path::PathBuf>,

    /// Run tests with code coverage instrumented.
    #[arg(long)]
    pub coverage: bool,

    /// Dump MIR of the test using RUSTFLAGS="-Zdump-mir=all".
    #[arg(long)]
    pub dump_mir: bool,

    /// Update snapshot files with actual output instead of comparing.
    #[arg(short, long)]
    pub update_snapshots: bool,

    #[arg(short, long)]
    pub verbose: bool,

    /// Use installed toolchain binaries from PATH instead of building from source.
    #[arg(long)]
    pub installed: bool,

    /// Use optimization for building the compiler. Generally slower in a clean setup,
    /// and provides less debug utility, so off by default.
    #[arg(long)]
    pub optimized: bool,
}
