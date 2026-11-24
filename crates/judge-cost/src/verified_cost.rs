//! Declared cost selection and coordinate admission for the production report.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

#[cfg_attr(not(verus_keep_ghost), derive(Debug, serde::Deserialize))]
pub struct CostFile {
    pub path: String,
    pub owner: String,
    pub cost: String,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, serde::Deserialize))]
pub struct TestCost {
    pub test: String,
    pub cost: String,
}

pub trait Declaration {
    spec fn name(&self) -> Seq<char>;
    fn key(&self) -> (out: &str)
        ensures out@ == self.name();
}

impl Declaration for CostFile {
    open spec fn name(&self) -> Seq<char> { self.path@ }
    fn key(&self) -> &str { self.path.as_str() }
}

impl Declaration for TestCost {
    open spec fn name(&self) -> Seq<char> { self.test@ }
    fn key(&self) -> &str { self.test.as_str() }
}

/// Preserve the first declaration and hence its JSON pointer at this endpoint.
pub fn first_declaration<D: Declaration>(rows: &[D], key: &str) -> (found: Option<usize>)
    ensures match found {
        Some(i) => i < rows.len() && rows@[i as int].name() == key@
            && forall|j: int| 0 <= j < i ==> (#[trigger] rows@[j]).name() != key@,
        None => forall|j: int| 0 <= j < rows.len() ==> (#[trigger] rows@[j]).name() != key@,
    },
{
    let mut i = 0;
    while i < rows.len()
        invariant i <= rows.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] rows@[j]).name() != key@,
        decreases rows.len() - i,
    {
        if <&str>::exec_eq(rows[i].key(), key) { return Some(i); }
        i += 1;
    }
    None
}

pub open spec fn owned_rows(rows: Seq<CostFile>, owner: Seq<char>, end: nat) -> Seq<usize>
    recommends end <= rows.len(),
    decreases end,
{
    if end == 0 { seq![] } else {
        let previous = owned_rows(rows, owner, (end - 1) as nat);
        if rows[end - 1].owner@ == owner { previous.push((end - 1) as usize) } else { previous }
    }
}

/// Select every original row for this owner, including equal paths at distinct positions.
pub fn owner_members(rows: &[CostFile], owner: &str) -> (members: Vec<usize>)
    ensures members@ == owned_rows(rows@, owner@, rows.len() as nat),
{
    let mut members = Vec::new();
    let mut i = 0;
    while i < rows.len()
        invariant i <= rows.len(), members@ == owned_rows(rows@, owner@, i as nat),
        decreases rows.len() - i,
    {
        if <&str>::exec_eq(rows[i].owner.as_str(), owner) { members.push(i); }
        i += 1;
    }
    members
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct CostFinding {
    pub code: &'static str,
    pub level: &'static str,
    pub message: &'static str,
    pub delta_refs: [&'static str; 1],
    pub causes: [&'static str; 1],
}

pub struct ReportDecision {
    pub status: &'static str,
    pub findings: Vec<CostFinding>,
}

/// The report adapter passes the actual published unknown entries.
pub fn report_decision<T>(unknown: &[T]) -> (decision: ReportDecision)
    ensures
        decision.status@ == if unknown.len() == 0 { "pass"@ } else { "warn"@ },
        decision.findings.len() == if unknown.len() == 0 { 0usize } else { 1usize },
        unknown.len() > 0 ==> {
            let f = decision.findings@[0];
            &&& f.code@ == "W_COST_UNKNOWN"@
            &&& f.level@ == "warning"@
            &&& f.message@ == "Affected declared costs contain unknown coordinates; see costs.unknown"@
            &&& f.delta_refs@[0]@ == "/impact"@
            &&& f.causes@[0]@ == "/outputs/costs/unknown"@
        },
{
    if unknown.len() == 0 {
        ReportDecision { status: "pass", findings: Vec::new() }
    } else {
        let warning = CostFinding {
            code: "W_COST_UNKNOWN",
            level: "warning",
            message: "Affected declared costs contain unknown coordinates; see costs.unknown",
            delta_refs: ["/impact"],
            causes: ["/outputs/costs/unknown"],
        };
        ReportDecision { status: "warn", findings: vec![warning] }
    }
}

/// A cost declaration is unknown when any of its four coordinates is absent.
pub open spec fn unknown_coordinate(
    cpu_missing: bool,
    wall_missing: bool,
    peak_rss_missing: bool,
    io_missing: bool,
) -> bool {
    cpu_missing || wall_missing || peak_rss_missing || io_missing
}

/// The production judge uses this result to emit the warning and preserve the
/// exact missing coordinate list in its JSON adapter.
pub fn has_unknown_coordinate(
    cpu_missing: bool,
    wall_missing: bool,
    peak_rss_missing: bool,
    io_missing: bool,
) -> (unknown: bool)
    ensures unknown == unknown_coordinate(
        cpu_missing, wall_missing, peak_rss_missing, io_missing,
    ),
{
    cpu_missing || wall_missing || peak_rss_missing || io_missing
}

pub open spec fn coordinate_names(names: Seq<&str>) -> Seq<Seq<char>> {
    names.map(|i: int, name: &str| name@)
}

pub open spec fn missing_names(cpu: bool, wall: bool, peak: bool, io: bool) -> Seq<Seq<char>> {
    (if cpu { seq!["cpu_ms"@] } else { Seq::empty() })
        + (if wall { seq!["wall_ms"@] } else { Seq::empty() })
        + (if peak { seq!["peak_rss_bytes"@] } else { Seq::empty() })
        + (if io { seq!["io_bytes"@] } else { Seq::empty() })
}

/// 输出固定顺序的完整缺失坐标；已知值不加入，不排序或合并坐标。
pub fn missing_coordinate_names(cpu: bool, wall: bool, peak: bool, io: bool)
    -> (out: Vec<&'static str>)
    ensures coordinate_names(out@) == missing_names(cpu, wall, peak, io),
        out.len() == missing_names(cpu, wall, peak, io).len(),
        forall|i: int| 0 <= i < out.len() ==> (#[trigger] out@[i])@
            == missing_names(cpu, wall, peak, io)[i],
{
    let mut names = Vec::new();
    if cpu { names.push("cpu_ms"); }
    if wall { names.push("wall_ms"); }
    if peak { names.push("peak_rss_bytes"); }
    if io { names.push("io_bytes"); }
    assert(coordinate_names(names@) =~= missing_names(cpu, wall, peak, io));
    names
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct PresenceError {
    pub message: &'static str,
    pub subject: String,
}

/// 两端都缺失时拒绝；仅基线存在时记入删除列表，其余保持原列表。
pub fn record_subject_presence(
    before: bool, after: bool, subject: String, removed: &mut Vec<String>,
) -> (out: Result<(), PresenceError>)
    ensures match out {
        Err(error) => !before && !after
            && error.message@ == "E_COST_REFERENCE: no declaration at either endpoint for "@
            && error.subject@ == subject@
            && removed@ == old(removed)@,
        Ok(()) => (before || after)
            && removed@ == if before && !after { old(removed)@.push(subject) } else { old(removed)@ },
    },
{
    if !before && !after {
        return Err(PresenceError {
            message: "E_COST_REFERENCE: no declaration at either endpoint for ", subject,
        });
    }
    if before && !after { removed.push(subject); }
    Ok(())
}

}
