use std::sync::Mutex;
use std::time::{Duration, Instant};

static TIMER: Mutex<Option<TimeState>> = Mutex::new(None);

struct TimeState {
    preprocess: Duration,
    parse: Duration,
    parse_slack: Duration,
    body_parse: Duration,
    hir_lowering: Duration,
    mir_lowering: Duration,
    sig_call: Duration,
    borrowck: Duration,
    lowering: Duration,
    codegen: Duration,
    mark: Instant,
}

pub fn enable_timing() {
    *TIMER.try_lock().unwrap() = Some(TimeState {
        preprocess: Duration::ZERO,
        parse: Duration::ZERO,
        parse_slack: Duration::ZERO,
        body_parse: Duration::ZERO,
        hir_lowering: Duration::ZERO,
        mir_lowering: Duration::ZERO,
        sig_call: Duration::ZERO,
        borrowck: Duration::ZERO,
        lowering: Duration::ZERO,
        codegen: Duration::ZERO,
        mark: Instant::now(),
    });
}

pub fn timing_enabled() -> bool {
    TIMER.try_lock().unwrap().is_some()
}

pub fn mark_preprocess_done() {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        let now = Instant::now();
        t.preprocess = now.duration_since(t.mark);
        t.mark = now;
    }
}

pub fn record_parse(duration: Duration) {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        t.parse = duration;
        let now = Instant::now();
        t.parse_slack = now.duration_since(t.mark) - t.parse;
        t.mark = now;
    }
}

pub fn accumulate_body_parse(duration: Duration) {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        t.body_parse += duration;
    }
}

pub fn accumulate_hir_lowering(duration: Duration) {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        t.hir_lowering += duration;
    }
}

pub fn accumulate_mir_lowering(duration: Duration) {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        t.mir_lowering += duration;
    }
}

pub fn accumulate_sig_call(duration: Duration) {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        t.sig_call += duration;
    }
}

pub fn accumulate_borrowck(duration: Duration) {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        t.borrowck += duration;
    }
}

/// Called from the `after_analysis` rustc callback.
/// Records the lowering phase (parse-end to after_analysis) and starts codegen.
pub fn mark_codegen_start() {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        let now = Instant::now();
        t.lowering = now.duration_since(t.mark);
        t.mark = now;
    }
}

/// Called after `generate_with_args` returns (end of rustc compilation).
pub fn finalize_timing() {
    if let Some(ref mut t) = *TIMER.try_lock().unwrap() {
        let now = Instant::now();
        t.codegen = now.duration_since(t.mark);
    }
}

pub struct PhaseTiming {
    pub preprocess: Duration,
    pub parse: Duration,
    pub parse_slack: Duration,
    pub body_parse: Duration,
    pub hir_lowering: Duration,
    pub mir_lowering: Duration,
    pub sig_call: Duration,
    pub borrowck: Duration,
    pub lowering: Duration,
    pub codegen: Duration,
}

pub fn take_timing() -> Option<PhaseTiming> {
    TIMER.try_lock().unwrap().take().map(|t| PhaseTiming {
        preprocess: t.preprocess,
        parse: t.parse,
        parse_slack: t.parse_slack,
        body_parse: t.body_parse,
        hir_lowering: t.hir_lowering,
        mir_lowering: t.mir_lowering,
        sig_call: t.sig_call,
        borrowck: t.borrowck,
        lowering: t.lowering,
        codegen: t.codegen,
    })
}
