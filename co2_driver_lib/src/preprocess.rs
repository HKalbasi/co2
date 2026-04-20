use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn preprocess(input: &Path, cpp_args: &[String]) -> String {
    let rewritten_input = rewrite_main_source_for_preprocess(input);
    let mut cmd = Command::new("gcc");
    cmd.arg("-E");
    cmd.arg(&rewritten_input);
    for arg in cpp_args {
        cmd.arg(arg);
    }

    let out = cmd.output().expect("failed to execute gcc -E");
    let _ = fs::remove_file(&rewritten_input);
    if !out.status.success() {
        eprintln!("{}", String::from_utf8_lossy(&out.stderr));
        panic!("gcc -E failed with status {}", out.status);
    }
    String::from_utf8(out.stdout).expect("gcc -E produced non-utf8 output")
}

pub fn rewrite_main_source_for_preprocess(input: &Path) -> PathBuf {
    let source = fs::read_to_string(input).expect("failed to read C input for preprocessing");
    let mut rewritten = String::from("#define __CO2__ 1\n");
    for line in source.lines() {
        if line.trim_start().starts_with('#') {
            rewritten.push_str(&line.replace("__GNUC__", "__CO2_HIDDEN_GNUC__").replace(
                "__clang__",
                "__CO2_HIDDEN_CLANG__",
            ));
        } else {
            rewritten.push_str(line);
        }
        rewritten.push('\n');
    }

    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before unix epoch")
        .as_nanos();
    let rewritten_path = input.with_file_name(format!(
        ".co2c-preprocess-{}-{unique}.c",
        std::process::id()
    ));
    fs::write(&rewritten_path, rewritten).expect("failed to write rewritten C input");
    rewritten_path
}

pub fn normalize_preprocessed(text: &str) -> String {
    let text = strip_line_markers(text);
    let text = strip_gnu_attributes(&text);
    let text = strip_gnu_asm_annotations(&text);
    let text = replace_gnu_typeof_with_usize(&text);
    strip_extension_keywords(&text)
}

fn strip_line_markers(preprocessed: &str) -> String {
    let mut out = String::new();
    for line in preprocessed.lines() {
        if !is_line_marker(line) {
            out.push_str(line);
        }
        out.push('\n');
    }
    out
}

fn is_line_marker(line: &str) -> bool {
    let trimmed = line.trim_start();
    trimmed.starts_with('#')
}

fn strip_gnu_attributes(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0usize;

    while i < bytes.len() {
        if src[i..].starts_with("__attribute__") {
            let mut j = i + "__attribute__".len();
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'(' {
                let mut depth = 0usize;
                while j < bytes.len() {
                    let b = bytes[j];
                    if b == b'(' {
                        depth += 1;
                    } else if b == b')' {
                        depth = depth.saturating_sub(1);
                        if depth == 0 {
                            j += 1;
                            break;
                        }
                    }
                    j += 1;
                }
                out.push(' ');
                i = j;
                continue;
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}

fn strip_extension_keywords(src: &str) -> String {
    fn is_ident_start(b: u8) -> bool {
        b.is_ascii_alphabetic() || b == b'_'
    }
    fn is_ident_continue(b: u8) -> bool {
        b.is_ascii_alphanumeric() || b == b'_'
    }

    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0usize;

    while i < bytes.len() {
        if is_ident_start(bytes[i]) {
            let start = i;
            i += 1;
            while i < bytes.len() && is_ident_continue(bytes[i]) {
                i += 1;
            }
            let ident = &src[start..i];
            let strip = matches!(
                ident,
                "__extension__"
                    | "__inline"
                    | "__inline__"
                    | "__restrict"
                    | "__restrict__"
                    | "_Complex"
                    | "_Noreturn"
            );
            if strip {
                out.push(' ');
            } else {
                out.push_str(ident);
            }
        } else {
            out.push(bytes[i] as char);
            i += 1;
        }
    }

    out
}

fn strip_gnu_asm_annotations(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0usize;

    while i < bytes.len() {
        if src[i..].starts_with("__asm__") || src[i..].starts_with("__asm") {
            let kw_len = if src[i..].starts_with("__asm__") {
                "__asm__".len()
            } else {
                "__asm".len()
            };
            let mut j = i + kw_len;
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'(' {
                let mut depth = 0usize;
                while j < bytes.len() {
                    let b = bytes[j];
                    if b == b'(' {
                        depth += 1;
                    } else if b == b')' {
                        depth = depth.saturating_sub(1);
                        if depth == 0 {
                            j += 1;
                            break;
                        }
                    }
                    j += 1;
                }
                out.push(' ');
                i = j;
                continue;
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}

fn replace_gnu_typeof_with_usize(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0usize;

    while i < bytes.len() {
        let kw_len = if src[i..].starts_with("__typeof__") {
            Some("__typeof__".len())
        } else if src[i..].starts_with("__typeof") {
            Some("__typeof".len())
        } else if src[i..].starts_with("typeof") {
            Some("typeof".len())
        } else {
            None
        };
        if let Some(kw_len) = kw_len {
            let mut j = i + kw_len;
            while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'(' {
                let mut depth = 0usize;
                while j < bytes.len() {
                    let b = bytes[j];
                    if b == b'(' {
                        depth += 1;
                    } else if b == b')' {
                        depth = depth.saturating_sub(1);
                        if depth == 0 {
                            j += 1;
                            break;
                        }
                    }
                    j += 1;
                }
                out.push_str("usize");
                i = j;
                continue;
            }
        }
        out.push(bytes[i] as char);
        i += 1;
    }

    out
}
