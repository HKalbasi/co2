use std::collections::HashMap;
use std::path::{Path, PathBuf};

use annotate_snippets::{AnnotationKind, Group, Level, Renderer, Snippet, renderer::DecorStyle};

#[derive(Debug, Clone)]
pub struct TestError {
    pub source: String,
    pub span: Option<(usize, usize)>,
    pub message: String,
}

impl std::fmt::Display for TestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for TestError {}

#[derive(Debug, Clone)]
pub struct UiTestError {
    pub path: PathBuf,
    pub sources: HashMap<String, String>,
    pub issues: Vec<UiTestIssue>,
}

#[derive(Debug, Clone)]
pub struct UiTestIssue {
    pub span: Option<crate::ui::UiSpanExpectation>,
    pub reason: String,
}

impl std::fmt::Display for UiTestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} issue(s)", self.issues.len())
    }
}

impl std::error::Error for UiTestError {}

pub fn render_ui_error(err: &UiTestError) {
    let main_path = &err.path;
    let main_name = main_path.display().to_string();

    for issue in &err.issues {
        if let Some(span) = &issue.span {
            let mut source = err.sources.get(&span.file_name);
            let mut name = &span.file_name;

            if source.is_none() {
                // Try finding by base name
                if let Some(base_name) = Path::new(&span.file_name)
                    .file_name()
                    .and_then(|n| n.to_str())
                    && let Some(found_source) = err.sources.get(base_name)
                {
                    source = Some(found_source);
                    name = err.sources.keys().find(|k| *k == base_name).unwrap();
                }
            }

            if let Some(source) = source {
                if span.byte_start < source.len() && span.byte_end <= source.len() {
                    let report = [Level::ERROR.primary_title(&issue.reason).element(
                        Snippet::source(source.as_str())
                            .path(name.as_str())
                            .line_start(1)
                            .annotation(
                                AnnotationKind::Primary
                                    .span(span.byte_start..span.byte_end)
                                    .label(&issue.reason),
                            ),
                    )];
                    eprintln!(
                        "{}",
                        Renderer::styled()
                            .decor_style(DecorStyle::Unicode)
                            .render(&report)
                    );
                } else {
                    eprintln!(
                        "Error: {}\n  at {} (byte offsets out of range)",
                        issue.reason, name
                    );
                }
            } else {
                eprintln!("Error: {}\n  at {} (source not found)", issue.reason, name);
            }
        } else {
            eprintln!("Error: {}\n  at {}", issue.reason, main_name);
        }
    }
}

pub fn render_test_error(path: &Path, err: &TestError) {
    let source = &err.source;
    if let Some((start, end)) = err.span {
        let name = path.display().to_string();
        let report: [Group; 1] = [Level::ERROR.primary_title(&err.message).element(
            Snippet::source(source.as_str())
                .path(name.as_str())
                .line_start(1)
                .annotation(
                    AnnotationKind::Primary
                        .span(start..end)
                        .label(&err.message),
                ),
        )];
        eprintln!(
            "{}",
            Renderer::styled()
                .decor_style(DecorStyle::Unicode)
                .render(&report)
        );
    } else {
        eprintln!("Error: {}", err.message);
        eprintln!("  at {}", path.display());

        if let Some(first_code_line) = source
            .lines()
            .map(str::trim)
            .find(|line| !line.is_empty() && !line.starts_with("//@") && !line.starts_with("#@"))
        {
            eprintln!("  source: {first_code_line}");
        }
    }
}
