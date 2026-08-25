#!/usr/bin/env nu

source "host-include-dirs.nu"

def main [--version: string] {
    cd $env.FILE_PWD
    cd ..

    let bundle = "target/co2-multicall.run"
    let stable_cargo = (rustup which --toolchain stable cargo | str trim)

    print $"Rebuilding bundle ..."
    nu ./bundler/build-bundle.nu --version $version --zstd

    print "Testing bundle in bwrap container..."

    # Bind the host's C header directories so co2cc can find system headers.
    let include_dirs = (host-include-dirs)
    print $"Binding include dirs: ($include_dirs)"

    mut binds = [
        --ro-bind /usr/lib /usr/lib
        --ro-bind /usr/bin /usr/bin
        --ro-bind /lib /lib
        --ro-bind /etc /etc
        --ro-bind /lib64 /lib64
        --ro-bind /bin /bin
        --dev /dev
        --proc /proc
        --tmpfs /tmp
        --tmpfs /home
        --setenv HOME /home/testuser
        --setenv CO2_EXPECTED_VERSION $version
        --dir /home/testuser
        --bind $bundle /test/co2-multicall.run
        --ro-bind $stable_cargo /test/stable-cargo
        --ro-bind ./bundler/bundle-smoke-test.nu /test/bundle-smoke-test.nu
        --chdir /test
    ]
    for dir in $include_dirs {
        $binds = ($binds | append [--ro-bind $dir $dir] | flatten)
    }

    ^bwrap ...$binds ...[
        nu /test/bundle-smoke-test.nu
    ]
}
