use std::collections::BTreeMap;

use rustc_data_structures::fx::FxHashSet;

use polonius_engine::{AllFacts, Atom};
use rustc_public_generative::rustc_public::mir::{Body, RETURN_LOCAL, TerminatorKind};
use rustc_public_generative::rustc_public::ty::{
    FloatTy, IntTy, RigidTy, Span, Ty, TyKind, UintTy,
};
use rustc_public_generative::rustc_public::{CrateDef, CrateDefType};

use crate::facts::{LocationTable, Path, Point, RustFacts, generate_facts, local_count};

pub struct BorrowckWarning {
    pub span: Span,
    pub message: String,
}

/// Why a read of a local is a move error.
#[derive(Copy, Clone, PartialEq, Eq)]
enum UseKind {
    /// The local was never initialized on this path.
    Uninit,
    /// The local was initialized and then moved on this path.
    Moved,
}

pub fn check(body: &Body) -> Vec<BorrowckWarning> {
    let start = std::time::Instant::now();
    let location_table = LocationTable::new(body);
    let output = generate_facts(body, &location_table);
    let facts_elapsed = start.elapsed();
    let compute_start = std::time::Instant::now();
    let (move_errors, leaks) = analyze(
        &output.facts,
        &output.borrows,
        &output.written,
        body,
        &location_table,
    );
    let compute_elapsed = compute_start.elapsed();
    let diag_start = std::time::Instant::now();
    let warnings = collect_diagnostics(body, &location_table, &move_errors, &leaks);
    let diag_elapsed = diag_start.elapsed();
    if std::env::var_os("CO2_TIMING").is_some() {
        eprintln!(
            "[borrowck] locals={} blocks={} stmts={} move_errors={} leaks={} \
             facts_gen={:?} dataflow={:?} diag={:?} warnings={}",
            body.local_decls().count(),
            body.blocks.len(),
            body.blocks
                .iter()
                .map(|b| b.statements.len())
                .sum::<usize>(),
            move_errors.len(),
            leaks.len(),
            facts_elapsed,
            compute_elapsed,
            diag_elapsed,
            warnings.len(),
        );
    }
    warnings
}

#[derive(Default)]
struct Events {
    assigned: Vec<Path>,
    moved: Vec<Path>,
    accessed: Vec<Path>,
    borrowed: Vec<Path>,
    written: Vec<Path>,
}

/// Forward gen/kill bitset dataflow over three local states:
/// - "possibly-uninitialized",
/// - "possibly-moved",
/// - "owned" (the local definitely holds a drop-needing value).
///
/// Returns the move errors (a path accessed while possibly-uninitialized or
/// moved, per point) and the leaks (drop-needing locals that are definitely
/// still owned when the function returns).
fn analyze(
    facts: &AllFacts<RustFacts>,
    borrows: &[(Path, Point)],
    written: &[(Path, Point)],
    body: &Body,
    location_table: &LocationTable,
) -> (BTreeMap<Point, Vec<(Path, UseKind)>>, Vec<(Span, String)>) {
    let mut events: BTreeMap<Point, Events> = BTreeMap::new();
    for &(path, point) in &facts.path_assigned_at_base {
        events.entry(point).or_default().assigned.push(path);
    }
    for &(path, point) in &facts.path_moved_at_base {
        events.entry(point).or_default().moved.push(path);
    }
    for &(path, point) in &facts.path_accessed_at_base {
        events.entry(point).or_default().accessed.push(path);
    }
    for &(path, point) in borrows {
        events.entry(point).or_default().borrowed.push(path);
    }
    for &(path, point) in written {
        events.entry(point).or_default().written.push(path);
    }

    let words = local_count(body).div_ceil(64);
    // Per-block in-state: (possibly-uninitialized, possibly-moved, owned).
    let mut entry: Vec<(Vec<u64>, Vec<u64>, Vec<u64>)> =
        vec![(vec![0; words], vec![0; words], vec![0; words]); body.blocks.len()];

    // bb0 entry: every non-argument local is possibly uninitialized; arguments
    // are initialized and own the values passed in; nothing has been moved.
    let arg_count = body.arg_locals().len();
    for (local, _) in body.local_decls() {
        if (1..=arg_count).contains(&local) {
            set_bit(&mut entry[0].2, local);
        } else {
            set_bit(&mut entry[0].0, local);
        }
    }

    let needs_drop = compute_needs_drop(body);
    let mut last_assign: Vec<Option<Span>> = vec![None; local_count(body)];

    let mut errors: BTreeMap<Point, Vec<(Path, UseKind)>> = BTreeMap::new();
    let mut leaks: Vec<(Span, String)> = Vec::new();
    let mut worklist = vec![0usize];
    while let Some(block) = worklist.pop() {
        let n = body.blocks[block].statements.len();
        let (mut uninit, mut moved, mut owned) = entry[block].clone();
        for i in 0..=n {
            let mid = location_table.mid_index(block, i);
            let is_terminator = i == n;
            let span = if is_terminator {
                body.blocks[block].terminator.source_info.span
            } else {
                body.blocks[block].statements[i].source_info.span
            };
            if let Some(ev) = events.get(&mid) {
                // Accesses are checked against the state before this point's
                // own writes, matching polonius (which checks against the
                // source of the cfg edge entering the point).
                for &path in &ev.accessed {
                    if is_set(&uninit, path.index()) {
                        let kind = if is_set(&moved, path.index()) {
                            UseKind::Moved
                        } else {
                            UseKind::Uninit
                        };
                        errors.entry(mid).or_default().push((path, kind));
                    }
                }
                // Borrowing a moved local is a use-after-move. Borrowing a
                // merely-uninitialized local is allowed (C `&x` idiom).
                for &path in &ev.borrowed {
                    if is_set(&moved, path.index()) {
                        errors.entry(mid).or_default().push((path, UseKind::Moved));
                    }
                }
                // A move marks the path possibly-uninitialized and no longer
                // owned; an assignment (which also covers writes through raw
                // pointers and escaped pointers, as recorded by fact
                // generation) initializes it. The assignment wins if both
                // happen at the same point.
                for &path in &ev.moved {
                    set_bit(&mut uninit, path.index());
                    set_bit(&mut moved, path.index());
                    clear_bit(&mut owned, path.index());
                }
                // A pointer write initializes but does not transfer ownership.
                for &path in &ev.written {
                    clear_bit(&mut uninit, path.index());
                    clear_bit(&mut moved, path.index());
                }
                for &path in &ev.assigned {
                    clear_bit(&mut uninit, path.index());
                    clear_bit(&mut moved, path.index());
                    set_bit(&mut owned, path.index());
                    last_assign[path.index()] = Some(span);
                }
            }
            if is_terminator
                && matches!(&body.blocks[block].terminator.kind, TerminatorKind::Return)
            {
                // Leaks are collected below, once the dataflow has converged,
                // using the final entry state of each return block.
            }
        }
        for &succ in &body.blocks[block].terminator.successors() {
            let (t_uninit, t_moved, t_owned) = &mut entry[succ];
            let mut changed = false;
            for (t, s) in t_uninit.iter_mut().zip(&uninit) {
                let new = *t | s;
                changed |= new != *t;
                *t = new;
            }
            for (t, s) in t_moved.iter_mut().zip(&moved) {
                let new = *t | s;
                changed |= new != *t;
                *t = new;
            }
            for (t, s) in t_owned.iter_mut().zip(&owned) {
                let new = *t | s;
                changed |= new != *t;
                *t = new;
            }
            if changed {
                worklist.push(succ);
            }
        }
    }

    // The dataflow has converged; `entry[block]` holds the final in-state of
    // every block. A local leaks if on *some* path reaching a return it is
    // still owned (assigned and never moved/dropped afterwards): CO2 has no
    // implicit drop, so a drop-needing value that reaches the end of the
    // function without being dropped or moved out is a leak, even if it was
    // only created on one side of a branch.
    //
    // We replay each return block's statements from its converged in-state so
    // that effects of statements *inside* the return block itself (e.g. a
    // `v = Move(t)` that reborrows a temporary) are visible at the return.
    for (block, block_data) in body.blocks.iter().enumerate() {
        if !matches!(&block_data.terminator.kind, TerminatorKind::Return) {
            continue;
        }
        let (mut uninit, mut moved, mut owned) = entry[block].clone();
        let n = block_data.statements.len();
        for i in 0..=n {
            let mid = location_table.mid_index(block, i);
            if let Some(ev) = events.get(&mid) {
                for &path in &ev.moved {
                    set_bit(&mut uninit, path.index());
                    set_bit(&mut moved, path.index());
                    clear_bit(&mut owned, path.index());
                }
                for &path in &ev.written {
                    clear_bit(&mut uninit, path.index());
                    clear_bit(&mut moved, path.index());
                }
                for &path in &ev.assigned {
                    clear_bit(&mut uninit, path.index());
                    clear_bit(&mut moved, path.index());
                    set_bit(&mut owned, path.index());
                    last_assign[path.index()] = Some(if i == n {
                        block_data.terminator.source_info.span
                    } else {
                        block_data.statements[i].source_info.span
                    });
                }
            }
        }
        check_leaks(body, &owned, &needs_drop, &last_assign, &mut leaks);
    }

    (errors, leaks)
}

/// A local that owns memory or a resource (its type needs drop) and is
/// still owned on some path reaching a return has leaked: CO2 has no
/// automatic drop at scope exit, so it must be dropped or moved out
/// explicitly. This includes temporaries (statement-expression values,
/// discarded call results, and so on), which are never auto-dropped either.
fn check_leaks(
    body: &Body,
    owned: &[u64],
    needs_drop: &[bool],
    last_assign: &[Option<Span>],
    leaks: &mut Vec<(Span, String)>,
) {
    for (local, decl) in body.local_decls() {
        if local == RETURN_LOCAL {
            continue;
        }
        if !needs_drop[local] {
            continue;
        }
        // The value is leaked if there is a path to this return on which it is
        // still owned. `owned` is a may-set, so a branch-local value created
        // on only one side of an if/ternary is still flagged (it leaks
        // whenever that side is taken). `uninit` does not matter here: a local
        // that may be owned is necessarily initialized on the owning path.
        if !is_set(owned, local) {
            continue;
        }
        let span = last_assign[local].unwrap_or(decl.span);
        let message = match local_display_name(body, local) {
            Some(name) => format!(
                "value leaked: `{name}` (of type `{}`, never dropped)",
                format_ty(decl.ty)
            ),
            None => format!(
                "value leaked: a temporary (of type `{}`, never dropped)",
                format_ty(decl.ty)
            ),
        };
        leaks.push((span, message));
    }
}

fn collect_diagnostics(
    body: &Body,
    location_table: &LocationTable,
    move_errors: &BTreeMap<Point, Vec<(Path, UseKind)>>,
    leaks: &[(Span, String)],
) -> Vec<BorrowckWarning> {
    let mut warnings: Vec<BorrowckWarning> = leaks
        .iter()
        .map(|(span, message)| BorrowckWarning {
            span: *span,
            message: message.clone(),
        })
        .collect();
    let mut points: Vec<&Point> = move_errors.keys().collect();
    points.sort();
    for point in points {
        let errors = &move_errors[point];
        let (block, statement_index) = location_table.to_location(*point);
        let is_terminator = statement_index == body.blocks[block].statements.len();
        let span = if is_terminator {
            body.blocks[block].terminator.source_info.span
        } else {
            body.blocks[block].statements[statement_index]
                .source_info
                .span
        };
        let is_return =
            is_terminator && matches!(&body.blocks[block].terminator.kind, TerminatorKind::Return);
        let mut errors = errors.clone();
        errors.sort_by_key(|(path, _)| path.index());
        for (path, kind) in errors {
            let message = if path.index() == RETURN_LOCAL && is_return {
                "function returns without a value".to_string()
            } else if kind == UseKind::Moved {
                format!("use of moved value: `{}`", local_name(body, path.index()))
            } else {
                format!(
                    "possible use of uninitialized value: `{}`",
                    local_name(body, path.index())
                )
            };
            warnings.push(BorrowckWarning { span, message });
        }
    }
    // A leak can be reported at several return points of the same function;
    // keep a single warning per (span, message).
    let mut seen = FxHashSet::default();
    warnings.retain(|w| seen.insert((w.span, w.message.clone())));
    warnings
}

fn local_name(body: &Body, local: usize) -> String {
    for vdi in &body.var_debug_info {
        if vdi.local() == Some(local) {
            return vdi.name.clone();
        }
    }
    format!("_{local}")
}

/// The user-visible name of a local, or `None` for compiler-generated
/// temporaries (which have no `var_debug_info`).
fn local_display_name(body: &Body, local: usize) -> Option<String> {
    body.var_debug_info
        .iter()
        .find(|vdi| vdi.local() == Some(local))
        .map(|vdi| vdi.name.clone())
}

fn compute_needs_drop(body: &Body) -> Vec<bool> {
    body.local_decls()
        .map(|(_, decl)| ty_needs_drop(decl.ty))
        .collect()
}

/// std/alloc/core types that own memory or OS resources and must be dropped.
const DROP_TYPES: &[&str] = &[
    "Vec",
    "Box",
    "String",
    "MutexGuard",
    "RwLockReadGuard",
    "RwLockWriteGuard",
    "Ref",
    "RefMut",
    "HashMap",
    "HashSet",
    "BTreeMap",
    "BTreeSet",
    "VecDeque",
    "LinkedList",
    "BinaryHeap",
    "Arc",
    "Rc",
    "CString",
    "OsString",
    "PathBuf",
    "File",
    "TcpStream",
    "TcpListener",
    "UdpSocket",
    "Mutex",
    "RwLock",
    "Condvar",
    "CondvarGuard",
    "ReentrantLockGuard",
    "Thread",
];

fn ty_needs_drop(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(adt, _)) => {
            if adt.is_box() {
                return true;
            }
            let name = adt.name();
            let is_known_stdlib = name.starts_with("std::")
                || name.starts_with("alloc::")
                || name.starts_with("core::");
            if is_known_stdlib
                && name
                    .rsplit("::")
                    .next()
                    .is_some_and(|last| DROP_TYPES.contains(&last))
            {
                return true;
            }
            // A struct containing a drop-needing field needs dropping too.
            adt.variants_iter()
                .flat_map(|variant| variant.fields())
                .any(|field| ty_needs_drop(field.ty()))
        }
        TyKind::RigidTy(RigidTy::Tuple(tys)) => tys.iter().any(|ty| ty_needs_drop(*ty)),
        TyKind::RigidTy(RigidTy::Array(ty, _) | RigidTy::Slice(ty) | RigidTy::Pat(ty, _)) => {
            ty_needs_drop(ty)
        }
        _ => false,
    }
}

fn format_ty(ty: Ty) -> String {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(adt, _)) => adt.trimmed_name(),
        TyKind::RigidTy(RigidTy::Int(it)) => match it {
            IntTy::Isize => "isize".to_string(),
            IntTy::I8 => "i8".to_string(),
            IntTy::I16 => "i16".to_string(),
            IntTy::I32 => "i32".to_string(),
            IntTy::I64 => "i64".to_string(),
            IntTy::I128 => "i128".to_string(),
        },
        TyKind::RigidTy(RigidTy::Uint(it)) => match it {
            UintTy::Usize => "usize".to_string(),
            UintTy::U8 => "u8".to_string(),
            UintTy::U16 => "u16".to_string(),
            UintTy::U32 => "u32".to_string(),
            UintTy::U64 => "u64".to_string(),
            UintTy::U128 => "u128".to_string(),
        },
        TyKind::RigidTy(RigidTy::Float(ft)) => match ft {
            FloatTy::F16 => "f16".to_string(),
            FloatTy::F32 => "f32".to_string(),
            FloatTy::F64 => "f64".to_string(),
            FloatTy::F128 => "f128".to_string(),
        },
        TyKind::RigidTy(RigidTy::Bool) => "bool".to_string(),
        TyKind::RigidTy(RigidTy::Char) => "char".to_string(),
        TyKind::RigidTy(RigidTy::Str) => "str".to_string(),
        TyKind::RigidTy(RigidTy::Never) => "!".to_string(),
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            let inner = tys
                .iter()
                .map(|ty| format_ty(*ty))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({inner})")
        }
        TyKind::RigidTy(RigidTy::Ref(_, ty, _)) => format!("&{}", format_ty(ty)),
        TyKind::RigidTy(RigidTy::RawPtr(ty, _)) => format!("*{}", format_ty(ty)),
        TyKind::RigidTy(RigidTy::Array(ty, _) | RigidTy::Slice(ty)) => {
            format!("[{}]", format_ty(ty))
        }
        TyKind::RigidTy(RigidTy::FnDef(..) | RigidTy::FnPtr(_)) => "fn".to_string(),
        _ => format!("{:?}", ty.kind()),
    }
}

fn is_set(bits: &[u64], local: usize) -> bool {
    bits[local / 64] & (1 << (local % 64)) != 0
}

fn set_bit(bits: &mut [u64], local: usize) {
    bits[local / 64] |= 1 << (local % 64);
}

fn clear_bit(bits: &mut [u64], local: usize) {
    bits[local / 64] &= !(1 << (local % 64));
}
