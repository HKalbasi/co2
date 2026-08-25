# Discover the system C header directories by asking gcc where it searches,
# so bwrap-based tests can bind exactly those paths into the container.
#
# Returns the list of directories from gcc's `#include <...>` search list
# that exist on this host (e.g. /usr/include, /usr/local/include,
# /usr/include/x86_64-linux-gnu, /usr/lib/gcc/<triple>/<ver>/include).

export def host-include-dirs [] {
    let probe = (do { printf '' | ^gcc -E -Wp,-v - } | complete)

    if $probe.exit_code != 0 {
        error make { msg: $"gcc include-path probe failed with exit code ($probe.exit_code)" }
    }

    let lines = ($probe.stderr | lines)
    let start = ($lines
        | enumerate
        | where {|r| ($r.item | str contains "#include <...> search starts here")}
        | first
        | get index)

    $lines
    | skip ($start + 1)
    | take while {|line| $line != "End of search list."}
    | each {|line| $line | str trim}
    | where {|dir| ($dir | path type) == "dir"}
    | uniq
}
