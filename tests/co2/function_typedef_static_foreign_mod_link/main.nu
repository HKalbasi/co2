#@ run-status: 0

let test_dir = $env.CO2_TEST_DIR
cd ($test_dir | path join "demo")

$env.RUSTFLAGS = "-C codegen-units=16"

let build = (do { ^co2cargo build } | complete)
if $build.exit_code != 0 {
    print "BUG: co2cargo build failed:"
    print ($build.stdout | str join "\n")
    print ($build.stderr | str join "\n")
    exit 1
}

let run = (do { ^($test_dir | path join "demo" "target" "debug" "demo") } | complete)
if $run.exit_code != 0 {
    print $"BUG: binary failed with exit ($run.exit_code)"
    print ($run.stdout | str join "\n")
    print ($run.stderr | str join "\n")
    exit 2
}

print "OK: crate compiled and ran successfully"
exit 0
