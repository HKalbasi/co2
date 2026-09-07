use std::any::Any;
use std::path::PathBuf;
use std::sync::{
    Arc, Mutex, Once,
    atomic::{AtomicBool, AtomicUsize, Ordering},
};

use annotate_snippets::{
    AnnotationKind, Group, Level as AnnotateLevel, Renderer, Snippet, renderer::DecorStyle,
};
use serde_json::json;

use crate::{FileId, Span, Token};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rich<'a, T = String, S = Span> {
    span: S,
    msg: String,
    _marker: std::marker::PhantomData<(&'a (), T)>,
}

impl<'a, T, S> Rich<'a, T, S> {
    pub fn custom<M: ToString>(span: S, msg: M) -> Self {
        Self {
            span,
            msg: msg.to_string(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn span(&self) -> &S {
        &self.span
    }

    pub fn reason(&self) -> &str {
        &self.msg
    }

    pub fn map_token<U>(self, _f: impl FnMut(T) -> U) -> Rich<'a, U, S> {
        Rich {
            span: self.span,
            msg: self.msg,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<T, S> std::fmt::Display for Rich<'_, T, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}

static ERRORS: Mutex<Vec<Rich<'static, Token, Span>>> = Mutex::new(Vec::new());
static DIAGNOSTICS_EMITTED: AtomicBool = AtomicBool::new(false);
/// TODO: Remove this and do proper error tracking for single bodies.
static DIAGNOSTIC_ERROR_COUNT: AtomicUsize = AtomicUsize::new(0);
static FORCE_JSON_DIAGNOSTICS: AtomicBool = AtomicBool::new(false);
static INSTALL_HOOK: Once = Once::new();
static SOURCE_MAP: Mutex<Option<Arc<dyn SourceMap>>> = Mutex::new(None);

pub trait SourceMap: Send + Sync {
    fn get_file_info(&self, id: FileId) -> Option<(String, Arc<str>)>;
}

pub(crate) fn get_source_text(span: Span) -> Option<String> {
    let guard = SOURCE_MAP.try_lock().ok()?;
    let sm = guard.as_ref()?;
    let data = span.data();
    let (_, source) = sm.get_file_info(data.context)?;
    if data.end <= source.len() {
        Some(source[data.start..data.end].to_string())
    } else {
        None
    }
}

#[derive(Clone)]
pub struct DiagnosticSpan {
    pub file_name: String,
    pub source: Arc<str>,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug)]
pub struct DiagnosticAbort;

pub fn take_errors() -> Vec<Rich<'static, Token, Span>> {
    let mut guard = ERRORS.try_lock().unwrap();
    std::mem::take(&mut *guard)
}

pub fn byte_to_line_col(src: &str, byte_pos: usize) -> (usize, usize) {
    let byte_pos = byte_pos.min(src.len());
    let mut line = 1;
    let mut col = 1;
    for (i, c) in src.char_indices() {
        if i >= byte_pos {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

pub fn safe_range(span: Span, src_len: usize) -> std::ops::Range<usize> {
    let span = span.data();
    let mut start = span.start.min(src_len);
    let mut end = span.end.min(src_len);
    if end < start {
        std::mem::swap(&mut start, &mut end);
    }
    start..end
}

/// Widen a byte range so both ends land on UTF-8 character boundaries of `src`.
///
/// The snippet renderer slices the source at the raw byte offsets when rendering, and panics
/// if an offset falls inside a multibyte character. Diagnostic spans can legitimately
/// point inside a multibyte character (e.g. an invalid identifier), so snap the range
/// outward to the nearest surrounding boundaries purely for rendering.
fn snap_to_char_boundaries(src: &str, range: std::ops::Range<usize>) -> std::ops::Range<usize> {
    let mut start = range.start.min(src.len());
    let mut end = range.end.min(src.len());
    while start > 0 && !src.is_char_boundary(start) {
        start -= 1;
    }
    while end < src.len() && !src.is_char_boundary(end) {
        end += 1;
    }
    if end < start {
        end = start;
    }
    start..end
}

pub fn reset_diagnostic_state() {
    install_diagnostic_panic_hook();
    DIAGNOSTICS_EMITTED.store(false, Ordering::SeqCst);
    DIAGNOSTIC_ERROR_COUNT.store(0, Ordering::SeqCst);
}

pub fn set_source_map(source_map: Arc<dyn SourceMap>) {
    *SOURCE_MAP.try_lock().unwrap() = Some(source_map);
}

pub fn set_force_json_diagnostics(force: bool) {
    FORCE_JSON_DIAGNOSTICS.store(force, Ordering::SeqCst);
}

pub fn diagnostics_were_emitted() -> bool {
    DIAGNOSTICS_EMITTED.load(Ordering::SeqCst)
}

pub fn diagnostic_error_count() -> usize {
    DIAGNOSTIC_ERROR_COUNT.load(Ordering::SeqCst)
}

pub fn panic_with_diagnostic_abort() -> ! {
    install_diagnostic_panic_hook();
    std::panic::panic_any(DiagnosticAbort);
}

pub fn is_diagnostic_abort(payload: &(dyn Any + Send)) -> bool {
    payload.is::<DiagnosticAbort>()
}

fn install_diagnostic_panic_hook() {
    INSTALL_HOOK.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if info.payload().is::<DiagnosticAbort>() {
                return;
            }
            previous(info);
        }));
    });
}

pub fn print_errors_and_terminate(
    filename: &str,
    src: &'static str,
    errs: Vec<Rich<'_, char, Span>>,
) -> ! {
    let errs = errs
        .into_iter()
        .map(|e| e.map_token(|c| c.to_string()))
        .chain(
            take_errors()
                .into_iter()
                .map(|e| e.map_token(|tok| tok.to_string())),
        )
        .collect();
    emit_mapped_errors_and_terminate(filename, src, errs);
}

pub fn emit_errors_and_terminate(errs: Vec<Rich<'_, String, Span>>) -> ! {
    emit_mapped_diagnostics("<unknown>", "", errs, DiagnosticLevel::Error, true);
    unreachable!("fatal diagnostics should abort");
}

pub fn emit_errors(errs: Vec<Rich<'_, String, Span>>) {
    emit_mapped_diagnostics("<unknown>", "", errs, DiagnosticLevel::Error, false);
}

pub fn emit_warnings(warnings: Vec<Rich<'_, String, Span>>) {
    emit_mapped_diagnostics("<unknown>", "", warnings, DiagnosticLevel::Warning, false);
}

fn emit_mapped_errors_and_terminate(
    filename: &str,
    src: &'static str,
    errs: Vec<Rich<'_, String, Span>>,
) -> ! {
    emit_mapped_diagnostics(filename, src, errs, DiagnosticLevel::Error, true);
    unreachable!("fatal diagnostics should abort");
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum DiagnosticLevel {
    Error,
    Warning,
}

impl DiagnosticLevel {
    fn annotate_level(self) -> AnnotateLevel<'static> {
        match self {
            DiagnosticLevel::Error => AnnotateLevel::ERROR,
            DiagnosticLevel::Warning => AnnotateLevel::WARNING,
        }
    }

    fn json_level(self) -> &'static str {
        match self {
            DiagnosticLevel::Error => "error",
            DiagnosticLevel::Warning => "warning",
        }
    }
}

fn snippet_group<'a>(
    level: AnnotateLevel<'a>,
    title: &'a str,
    path: &'a str,
    src: &'a str,
    range: std::ops::Range<usize>,
    label: &'a str,
) -> Group<'a> {
    if src.is_empty() {
        return Group::with_title(level.primary_title(title));
    }
    level.primary_title(title).element(
        Snippet::source(src)
            .path(path)
            .line_start(1)
            .annotation(AnnotationKind::Primary.span(range).label(label)),
    )
}

fn emit_mapped_diagnostics(
    filename: &str,
    src: &'static str,
    diagnostics: Vec<Rich<'_, String, Span>>,
    level: DiagnosticLevel,
    terminate: bool,
) {
    // Only errors count as emitted diagnostics. Warnings must not set (or
    // clear) this flag.
    if level == DiagnosticLevel::Error {
        DIAGNOSTICS_EMITTED.store(true, Ordering::SeqCst);
        DIAGNOSTIC_ERROR_COUNT.fetch_add(1, Ordering::SeqCst);
    }
    if FORCE_JSON_DIAGNOSTICS.load(Ordering::SeqCst)
        || std::env::var_os("CO2_FORCE_JSON_DIAGNOSTICS").is_some()
    {
        for e in diagnostics {
            emit_json_diagnostic(filename, src, &e, level);
        }
    } else {
        for e in diagnostics {
            emit_human_diagnostic(filename, src, &e, level);
        }
    }
    if terminate {
        panic_with_diagnostic_abort();
    }
}

static DIAGNOSTIC_BASE_PATH: Mutex<Option<PathBuf>> = Mutex::new(None);

pub fn set_diagnostic_base_path(path: Option<PathBuf>) {
    let mut guard = DIAGNOSTIC_BASE_PATH.lock().unwrap();
    *guard = path;
}

fn relativize_path(path: &str) -> String {
    use std::path::{Component, Path};
    let path = Path::new(path);
    let guard = DIAGNOSTIC_BASE_PATH.lock().unwrap();
    if let Some(base) = guard.as_ref() {
        if let Ok(relative) = path.strip_prefix(base) {
            return relative.display().to_string();
        }
        // strip_prefix failed, try computing a relative path component by component
        let pc: Vec<_> = path.components().collect();
        let bc: Vec<_> = base.components().collect();
        let common = pc.iter().zip(&bc).take_while(|(a, b)| a == b).count();
        if common > 0 {
            let mut result = PathBuf::new();
            for _ in common..bc.len() {
                result.push(Component::ParentDir);
            }
            for c in &pc[common..] {
                result.push(c);
            }
            return result.display().to_string();
        }
    }
    path.display().to_string()
}

fn emit_human_diagnostic(
    filename: &str,
    src: &str,
    e: &Rich<'_, String, Span>,
    level: DiagnosticLevel,
) {
    let renderer = Renderer::styled().decor_style(DecorStyle::Unicode);
    let title = e.to_string();
    if let Some(mapped) = get_diagnostic_info(*e.span()) {
        let display_name = relativize_path(&mapped.file_name);
        let render_range = snap_to_char_boundaries(&mapped.source, mapped.start..mapped.end);
        let report = [snippet_group(
            level.annotate_level(),
            &title,
            &display_name,
            &mapped.source,
            render_range,
            e.reason(),
        )];
        eprintln!("{}", renderer.render(&report));
        return;
    }

    let range = snap_to_char_boundaries(src, safe_range(*e.span(), src.len()));
    let display_name = relativize_path(filename);
    let report = [snippet_group(
        level.annotate_level(),
        &title,
        &display_name,
        src,
        range,
        e.reason(),
    )];
    eprintln!("{}", renderer.render(&report));
}

fn emit_json_diagnostic(
    filename: &str,
    src: &str,
    e: &Rich<'_, String, Span>,
    level: DiagnosticLevel,
) {
    let renderer = Renderer::plain().decor_style(DecorStyle::Unicode);
    let title = e.to_string();
    if let Some(mapped) = get_diagnostic_info(*e.span()) {
        let range = mapped.start..mapped.end;
        let display_name = relativize_path(&mapped.file_name);
        let (ls, cs) = byte_to_line_col(&mapped.source, mapped.start);
        let (le, ce) = byte_to_line_col(&mapped.source, mapped.end);
        let render_range = snap_to_char_boundaries(&mapped.source, range.clone());
        let report = [snippet_group(
            level.annotate_level(),
            &title,
            &display_name,
            &mapped.source,
            render_range,
            e.reason(),
        )];
        let rendered = renderer.render(&report);
        let label = e.reason().to_string();
        let diagnostic = json!({
            "$message_type": "diagnostic",
            "message": e.to_string(),
            "code": null,
            "level": level.json_level(),
            "spans": [json_span(&display_name, range, true, Some(&label), ls, cs, le, ce)],
            "children": [],
            "rendered": rendered,
        });
        eprintln!("{diagnostic}");
        return;
    }

    let range = safe_range(*e.span(), src.len());
    let display_name = relativize_path(filename);
    let (ls, cs) = byte_to_line_col(src, range.start);
    let (le, ce) = byte_to_line_col(src, range.end);
    let primary_label = e.reason().to_string();
    let spans = vec![json_span(
        &display_name,
        range.clone(),
        true,
        Some(&primary_label),
        ls,
        cs,
        le,
        ce,
    )];
    let render_range = snap_to_char_boundaries(src, range.clone());
    let report = [snippet_group(
        level.annotate_level(),
        &title,
        &display_name,
        src,
        render_range,
        e.reason(),
    )];
    let rendered = renderer.render(&report);

    let diagnostic = json!({
        "$message_type": "diagnostic",
        "message": e.to_string(),
        "code": null,
        "level": level.json_level(),
        "spans": spans,
        "children": [],
        "rendered": rendered,
    });
    eprintln!("{diagnostic}");
}

fn json_span(
    filename: &str,
    range: std::ops::Range<usize>,
    is_primary: bool,
    label: Option<&str>,
    line_start: usize,
    col_start: usize,
    line_end: usize,
    col_end: usize,
) -> serde_json::Value {
    json!({
        "file_name": filename,
        "byte_start": range.start,
        "byte_end": range.end,
        "line_start": line_start,
        "line_end": line_end,
        "column_start": col_start,
        "column_end": col_end,
        "is_primary": is_primary,
        "text": [],
        "label": label,
        "suggested_replacement": null,
        "suggestion_applicability": null,
        "expansion": null,
    })
}

fn get_diagnostic_info(span: Span) -> Option<DiagnosticSpan> {
    let guard = SOURCE_MAP.try_lock().unwrap();
    let sm = guard.as_ref()?;
    let span = span.data();
    let (file_name, source) = sm.get_file_info(span.context)?;
    Some(DiagnosticSpan {
        file_name,
        source,
        start: span.start,
        end: span.end,
    })
}
