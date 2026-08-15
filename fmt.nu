#!/usr/bin/env nu

# stage 1: format workspace crates
cargo fmt

# stage 2: strip trailing whitespace and ensure every file ends with a newline,
# skipping anything matched by fmt-exclude
let exclude = (try { open --raw fmt-exclude } catch { "" } | lines | each {|l| $l | str trim } | where {|l| $l != "" and not ($l | str starts-with "#")})
let excluded = ($exclude | each {|p| if ($p | str ends-with "/") { glob $"($p)**" -D } else { glob $p -D } } | flatten | path expand | uniq)

idx init . --wait
for f in (idx files .) {
    let f = $f.full_path
    if ($excluded | any {|e| $e == ($f | path expand) }) {
        continue
    }
    let content = (open --raw $f)
    let clean = ($content | str replace --all --regex "(?m)[ \t]+$" "")
    let clean = if ($clean | str ends-with "\n") { $clean } else { $clean + "\n" }
    if $clean != $content {
        $clean | save --force $f
    }
}
