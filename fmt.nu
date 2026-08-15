#!/usr/bin/env nu

# stage 1: format workspace crates
cargo fmt

# stage 2: strip trailing whitespace and ensure every text file ends with a newline
idx init . --wait
for f in (idx files .) {
    let f = $f.full_path
    let ft = (ls -m $f).0.type
    if ($ft | str starts-with "text/") {
        let content = (open --raw $f)
        let clean = ($content | str replace --all --regex "(?m)[ \t]+$" "")
        let clean = if ($clean | str ends-with "\n") { $clean } else { $clean + "\n" }
        if $clean != $content {
            $clean | save --force $f
        }
    }
}
