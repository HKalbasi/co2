#!/usr/bin/env nu

def main [--version: string] {
    cd $env.FILE_PWD
    cd ..

    let bundle = "target/co2-multicall-rustup.run"
    let stable_cargo = (rustup which --toolchain stable cargo | str trim)
    let rustc_bin = (which rustc | get path.0)
    let rustup_bin = (which rustup | get path.0)
    let rustup_home = (rustup show home | str trim)
    let toolchain_dir = (rustc --print sysroot | str trim)

    print $"Rebuilding rustup bundle ..."
    nu ./bundler/build-rustup-bundle.nu --version $version --zstd

    print "Testing rustup bundle in bwrap container..."

    ^bwrap ...[
        --ro-bind /usr/lib /usr/lib
        --ro-bind /usr/bin /usr/bin
        --ro-bind /usr/include /usr/include
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
        --setenv RUSTUP_HOME $rustup_home
        --setenv PATH /opt/rust-bin:/usr/bin:/bin
        --dir /home/testuser
        --dir /opt/rust-bin
        --bind $bundle /test/co2-multicall.run
        --ro-bind $stable_cargo /test/stable-cargo
        --ro-bind $rustc_bin /opt/rust-bin/rustc
        --ro-bind $rustup_bin /opt/rust-bin/rustup
        --ro-bind $toolchain_dir $toolchain_dir
        --ro-bind ./bundler/bundle-smoke-test.nu /test/bundle-smoke-test.nu
        --chdir /test
        nu /test/bundle-smoke-test.nu
    ]
}
