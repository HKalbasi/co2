#@ run-status: 0

# ABI compatibility test. lib (lib.c + lib.h) and the driver (main.c) are
# compiled by co2cc and/or gcc in all four combinations, linked with co2cc
# (whose linker supplies the Rust panic runtime that co2cc objects reference),
# and run. Every resulting binary must exit 0.

let test_dir = $env.CO2_TEST_DIR
let lib_src = ($test_dir | path join "lib.c")
let main_src = ($test_dir | path join "main.c")

# [name, lib compiler, main compiler]
let cases = [
    { name: "gcc-gcc", lib_cc: "gcc", main_cc: "gcc" }
    { name: "gcc-co2cc", lib_cc: "gcc", main_cc: "co2cc" }
    { name: "co2cc-gcc", lib_cc: "co2cc", main_cc: "gcc" }
    { name: "co2cc-co2cc", lib_cc: "co2cc", main_cc: "co2cc" }
]

for case in $cases {
    let name = $case.name
    let lib_cc = $case.lib_cc
    let main_cc = $case.main_cc
    let lib_o = ($test_dir | path join $"lib_($name).o")
    let main_o = ($test_dir | path join $"main_($name).o")
    let app = ($test_dir | path join $"app_($name)")

    let cc_lib = (do { ^$lib_cc -c $lib_src -o $lib_o } | complete)
    if $cc_lib.exit_code != 0 {
        print $"($name): compile lib.c with ($lib_cc) failed: ($cc_lib.stderr)"
        exit 1
    }

    let cc_main = (do { ^$main_cc -c $main_src -o $main_o } | complete)
    if $cc_main.exit_code != 0 {
        print $"($name): compile main.c with ($main_cc) failed: ($cc_main.stderr)"
        exit 2
    }

    let link = (do { ^co2cc $lib_o $main_o -o $app } | complete)
    if $link.exit_code != 0 {
        print $"($name): co2cc link failed: ($link.stderr)"
        exit 3
    }

    let run = (do { ^$app } | complete)
    if $run.exit_code != 0 {
        print $"($name): binary exited with ($run.exit_code): ($run.stderr)"
        exit 4
    }
    print $"($name): all ABI checks passed"
}

exit 0
