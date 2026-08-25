#!/usr/bin/env nu

# Rustup bundle: reuses the rustup-installed rustc toolchain at runtime
# instead of bundling all libraries and stdlib crates.
# Only bundles the co2 binary and an env.sh that points back to the
# rustup toolchain. C headers come from the host system.

source "prepare-payload.nu"

def main [--version: string, --zstd] {
    checkpoint "Starting rustup bundle build"

    cargo build -p co2-multicall --release

    checkpoint "Build successfully"

    let payload_dir = (mktemp -d)
    mkdir ($payload_dir | path join "bin")

    cp target/release/co2-multicall ($payload_dir | path join "bin" "co2-multicall")

    for applet in ["co2rustc", "co2rustdoc", "co2cc", "co2cargo", "co2miri", "co2fmt"] {
        ln -s co2-multicall ($payload_dir | path join "bin" $applet)
    }

    # Read the required nightly from rust-toolchain.toml
    let toolchain_channel = (open --raw ($env.FILE_PWD | path join ".." "rust-toolchain.toml") | from toml | get toolchain.channel)

    # Use the rustup env.sh that points to the installed toolchain at runtime
    let env_template = ($env.FILE_PWD | path join "env-rustup.sh")
    open $env_template
    | str replace "@CO2_VERSION@" $version
    | str replace "@CO2_RUSTUP_TOOLCHAIN@" $toolchain_channel
    | save -f ($payload_dir | path join "env.sh")

    checkpoint "Prepared rustup payload dir"

    # Create self-extracting archive
    let compress_flag = if $zstd { "--zstd" } else { "-z" }
    if $zstd {
        print "Using zstd compression"
    } else {
        print "Using gzip compression"
    }

    let tarball = (mktemp)
    tar -C $payload_dir -c $compress_flag -f $tarball .

    checkpoint "Created tarball"

    let hash = (open --raw $tarball | hash sha256)

    checkpoint "Evaluated hash"

    let out_file = "target/co2-multicall-rustup.run"
    mkdir target

    let script_header = ([
        '#!/bin/bash'
        ''
        ($"HASH=\"($hash)\"")
        'CACHE_DIR="$HOME/.cache/co2/$HASH"'
        ''
        '# Self-extraction: extract tarball on first run'
        'if [ ! -d "$CACHE_DIR" ]; then'
        '    PAYLOAD_LINE=$(grep -a -n "^__PAYLOAD_BELOW__" "$0" | head -n 1 | cut -d: -f1)'
        '    PAYLOAD_START=$((PAYLOAD_LINE + 1))'
        '    mkdir -p "$CACHE_DIR"'
        ('    tail -n +$PAYLOAD_START "$0" | tar -x ' + $compress_flag + ' -C "$CACHE_DIR"')
        'fi'
        ''
        '# Set up environment via the extracted env.sh'
        'export CO2_CACHE_DIR="$CACHE_DIR"'
        'source "$CACHE_DIR/env.sh" || exit 1'
        ''
        '# Multicall dispatch'
        'ARG0="$0"'
        'export CO2_RUN_SCRIPT="$(readlink -f "$0")"'
        ''
        'exec -a "$ARG0" "$CACHE_DIR/bin/co2-multicall" "$@"'
    ] | str join (char newline))

    $script_header | save -f $out_file

    checkpoint "Created self extracting script"

    $"(char newline)__PAYLOAD_BELOW__(char newline)" | save --append $out_file
    open --raw $tarball | save --append $out_file

    chmod +x $out_file

    rm -rf $payload_dir $tarball

    checkpoint "Finished"

    print $"Created rustup bundle: ($out_file)"
}
