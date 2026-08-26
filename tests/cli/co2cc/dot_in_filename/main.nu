#@ run-status: 0

let test_dir = $env.CO2_TEST_DIR
let source = ($test_dir | path join "hello.world.c")
let binary = ($test_dir | path join "hello.world")

let compile = (do { ^co2cc $source -o $binary } | complete)
if $compile.exit_code != 0 {
    print $"co2cc failed to build a C file with a dot in its name: ($compile.stderr)"
    exit 1
}

let run = (do { ^$binary } | complete)
if $run.exit_code != 0 {
    print $"binary exited with ($run.exit_code): ($run.stderr)"
    exit 1
}

if ($run.stdout | str trim) != "hello world" {
    print $"unexpected output: ($run.stdout)"
    exit 1
}

exit 0
