#!/bin/bash
# Source this script to set up the environment for co2 tools.
# This variant reuses your rustup-installed rustc toolchain
# instead of bundling the entire sysroot.
# CO2_CACHE_DIR can be pre-set; otherwise it is derived from this script's location.

export CO2_VERSION="@CO2_VERSION@"
export CO2_CACHE_DIR="${CO2_CACHE_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"

# The exact nightly this co2 build was compiled against.
export CO2_REQUIRED_TOOLCHAIN="@CO2_RUSTUP_TOOLCHAIN@"

if ! command -v rustup > /dev/null 2>&1; then
    echo "Error: co2 rustup bundle requires rustup." >&2
    echo "See https://rustup.rs for installation instructions." >&2
    echo "Then install the required toolchain: rustup toolchain install $CO2_REQUIRED_TOOLCHAIN" >&2
    return 1
fi

CO2_SYSROOT="$(rustup run "$CO2_REQUIRED_TOOLCHAIN" rustc --print sysroot 2>/dev/null)"
if [ -z "$CO2_SYSROOT" ]; then
    echo "Error: required toolchain '$CO2_REQUIRED_TOOLCHAIN' not found." >&2
    echo "Install it with: rustup toolchain install $CO2_REQUIRED_TOOLCHAIN" >&2
    return 1
fi

export CO2_SYSROOT
export LD_LIBRARY_PATH="$CO2_SYSROOT/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

if [[ ! "$RUSTFLAGS" =~ "--sysroot" ]]; then
    export RUSTFLAGS="--sysroot=$CO2_SYSROOT $RUSTFLAGS"
fi

if [ -z "${MIRI_LIB_SRC}" ] && [ -d "$CO2_SYSROOT/lib/rustlib/src/rust/library" ]; then
    export MIRI_LIB_SRC="$CO2_SYSROOT/lib/rustlib/src/rust/library"
fi

# Let rustup subcommands (cargo, rustc, etc.) pick the right toolchain
export RUSTUP_TOOLCHAIN="$CO2_REQUIRED_TOOLCHAIN"
