//! Declared cost selection and coordinate admission for the production report.
#![allow(unexpected_cfgs)]
use std::collections::BTreeSet;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::string::StringExecFns;

verus! {

/// The RFC 6901 reference-token encoding emits one or two Unicode scalars.
pub fn pointer_token(c: char) -> (token: [Option<char>; 2])
    ensures
        token[0] == Some(if c == '/' || c == '~' { '~' } else { c }),
        token[1] == if c == '/' { Some('1') } else if c == '~' { Some('0') } else { None },
{
    match c {
        '~' => [Some('~'), Some('0')],
        '/' => [Some('~'), Some('1')],
        _ => [Some(c), None],
    }
}

/// Delta entries supplied by the FILEMAP decoder expose their changed path.
pub trait ChangedFile {
    spec fn path_text(&self) -> Seq<char>;
    fn path(&self) -> (text: &str)
        ensures text@ == self.path_text();
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Deserialize))]
pub struct Changed {
    pub path: String,
}
impl ChangedFile for Changed {
    open spec fn path_text(&self) -> Seq<char> { self.path@ }
    fn path(&self) -> &str { self.path.as_str() }
}

fn has_prefix(text: &str, prefix: &str) -> (found: bool)
    ensures found == prefix@.is_prefix_of(text@),
{
    let mut chars = text.chars();
    let mut expected = prefix.chars();
    loop
        invariant
            chars@.1 == text@, expected@.1 == prefix@,
            0 <= chars@.0 <= text@.len(), 0 <= expected@.0 <= prefix@.len(),
            chars@.0 == expected@.0,
            forall|i:int| 0 <= i < chars@.0 ==> text@[i] == prefix@[i],
        decreases prefix@.len() - expected@.0 + 1,
    {
        let c = match expected.next() {
            None => {
                assert(prefix@ =~= text@.subrange(0, prefix@.len() as int));
                return true;
            }
            Some(c) => c,
        };
        match chars.next() {
            Some(seen) if seen == c => {},
            _ => return false,
        }
    }
}

#[derive(Clone, Copy)]
pub enum CostKind { File, Test, Project, Script }

impl CostKind {
    pub open spec fn tag(self) -> Seq<char> {
        match self {
            Self::File => "file:"@, Self::Test => "test:"@,
            Self::Project => "project:"@, Self::Script => "script:"@,
        }
    }
    fn prefix(self) -> (s: &'static str)
        ensures s@ == self.tag(),
    {
        match self {
            Self::File => "file:", Self::Test => "test:",
            Self::Project => "project:", Self::Script => "script:",
        }
    }
}

pub open spec fn classification(text: Seq<char>) -> Option<CostKind> {
    if CostKind::File.tag().is_prefix_of(text) { Some(CostKind::File) }
    else if CostKind::Project.tag().is_prefix_of(text) { Some(CostKind::Project) }
    else if CostKind::Script.tag().is_prefix_of(text) { Some(CostKind::Script) }
    else if CostKind::Test.tag().is_prefix_of(text) { Some(CostKind::Test) }
    else { None }
}

fn cost_kind(text: &str) -> (kind: Option<CostKind>)
    ensures kind == classification(text@),
{
    if has_prefix(text, CostKind::File.prefix()) { Some(CostKind::File) }
    else if has_prefix(text, CostKind::Project.prefix()) { Some(CostKind::Project) }
    else if has_prefix(text, CostKind::Script.prefix()) { Some(CostKind::Script) }
    else if has_prefix(text, CostKind::Test.prefix()) { Some(CostKind::Test) }
    else { None }
}

pub open spec fn reached_subject(text: Seq<char>) -> bool {
    "file:"@.is_prefix_of(text) || "project:"@.is_prefix_of(text) || "script:"@.is_prefix_of(text)
}

/// The end of any complete character prefix splits the original UTF-8 bytes.
proof fn prefix_encoding(a: Seq<char>, b: Seq<char>)
    ensures
        vstd::utf8::encode_utf8(a + b) == vstd::utf8::encode_utf8(a) + vstd::utf8::encode_utf8(b),
        vstd::utf8::is_char_boundary(vstd::utf8::encode_utf8(a + b), vstd::utf8::encode_utf8(a).len() as int),
    decreases a.len(),
{
    use vstd::utf8::*;
    let text = a + b;
    encode_utf8_valid_utf8(text);
    if a.len() == 0 {
        assert(text =~= b);
    } else {
        assert(text.drop_first() =~= a.drop_first() + b);
        prefix_encoding(a.drop_first(), b);
        encode_utf8_first_scalar(text);
        assert(pop_first_scalar(encode_utf8(text)) =~= encode_utf8(text.drop_first()));
    }
}

pub fn cost_subject(text: &str) -> (part: Option<(CostKind, &str)>)
    ensures
        match part {
            Some((kind, id)) => classification(text@) == Some(kind) && text@ == kind.tag() + id@
                && id@ == text@.skip(kind.tag().len() as int),
            None => classification(text@).is_none(),
        },
{
    #[cfg(verus_keep_ghost)]
    use vstd::string::StringSliceAdditionalSpecFns;
    #[cfg(verus_keep_ghost)]
    use vstd::utf8::*;
    let Some(kind) = cost_kind(text) else { return None; };
    let prefix = kind.prefix();
    let n = prefix.as_bytes().len();
    let ghost suffix = text@.skip(prefix@.len() as int);
    proof {
        assert(prefix@.is_prefix_of(text@));
        assert(text@ =~= prefix@ + suffix);
        prefix_encoding(prefix@, suffix);
        assert(n == encode_utf8(prefix@).len());
        assert(text.spec_bytes() == encode_utf8(text@));
        assert(is_char_boundary(text.spec_bytes(), n as int));
    }
    let (_, id) = text.split_at(n);
    proof {
        assert(id.spec_bytes() =~= encode_utf8(suffix));
        encode_utf8_decode_utf8(suffix);
        encode_utf8_decode_utf8(id@);
    }
    Some((kind, id))
}

pub open spec fn subject_names(set: Set<String>) -> Set<Seq<char>> {
    set.map(|s: String| s@)
}

fn add_subject(set: &mut BTreeSet<String>, subject: String)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures subject_names(set@) == subject_names(old(set)@).insert(subject@),
{
    let ghost previous = set@;
    set.insert(subject);
    assert forall|text: Seq<char>| #[trigger] subject_names(set@).contains(text)
        <==> subject_names(previous).insert(subject@).contains(text) by {
        if text == subject@ {
            assert(set@.contains(subject));
            assert(exists|s:String| set@.contains(s) && text == s@);
        } else if subject_names(set@).contains(text) {
            let s = choose|s:String| set@.contains(s) && text == s@;
            assert(previous.contains(s));
            assert(exists|old_key:String| previous.contains(old_key) && text == old_key@);
        } else if subject_names(previous).contains(text) {
            let s = choose|s:String| previous.contains(s) && text == s@;
            assert(set@.contains(s));
            assert(exists|new_key:String| set@.contains(new_key) && text == new_key@);
        }
    }
    assert(subject_names(set@) =~= subject_names(previous).insert(subject@));
}

/// Prefix fold of the actual input rows. The report iterates the ordered set returned here.
pub open spec fn changed_names<D: ChangedFile>(rows: Seq<D>, n: nat) -> Set<Seq<char>>
    decreases n,
{
    if n == 0 { Set::empty() } else {
        changed_names(rows, (n-1) as nat).insert("file:"@ + rows[n-1].path_text())
    }
}
pub open spec fn node_names(rows: Seq<String>, n: nat, reached: bool) -> Set<Seq<char>>
    decreases n,
{
    if n == 0 { Set::empty() } else {
        let prev = node_names(rows, (n-1) as nat, reached);
        let name = rows[n-1]@;
        if !reached || reached_subject(name) { prev.insert(name) } else { prev }
    }
}

fn add_nodes(set: &mut BTreeSet<String>, rows: &[String], reached: bool)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures subject_names(set@) == subject_names(old(set)@).union(node_names(rows@,rows@.len(),reached)),
{
    let mut i = 0;
    while i < rows.len()
        invariant i <= rows.len(), vstd::laws_cmp::obeys_cmp::<String>(),
            subject_names(set@) == subject_names(old(set)@).union(node_names(rows@,i as nat,reached)),
        decreases rows.len() - i,
    {
        let name = rows[i].as_str();
        if !reached || matches!(cost_kind(name), Some(CostKind::File | CostKind::Project | CostKind::Script)) {
            add_subject(set, rows[i].clone());
        }
        assert(subject_names(set@) =~= subject_names(old(set)@).union(node_names(rows@,(i+1) as nat,reached)));
        i += 1;
    }
}

/// The ordered set uses Rust's standard String total order. The pinned Verus
/// library exposes its BTreeSet model under the Ord/Eq consistency contract.
pub fn cost_subjects<D: ChangedFile>(schema: &str, delta: &[D], reached: &[String], required: &[String])
    -> (subjects: Result<BTreeSet<String>, &'static str>)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures match subjects {
        Err(err) => schema@ != "chrono-filemap-impact/v6"@ && err@ == "E_IMPACT: unsupported cost input schema"@,
        Ok(set) => schema@ == "chrono-filemap-impact/v6"@ && subject_names(set@) ==
            changed_names(delta@,delta@.len()).union(node_names(reached@,reached@.len(),true))
                .union(node_names(required@,required@.len(),false)),
    },
{
    if !<&str>::exec_eq(schema,"chrono-filemap-impact/v6") {
        return Err("E_IMPACT: unsupported cost input schema");
    }
    let mut set = BTreeSet::new();
    let mut i = 0;
    while i < delta.len()
        invariant i <= delta.len(), vstd::laws_cmp::obeys_cmp::<String>(),
            subject_names(set@) == changed_names(delta@,i as nat),
        decreases delta.len() - i,
    {
        add_subject(&mut set, "file:".to_string().concat(delta[i].path()));
        i += 1;
    }
    add_nodes(&mut set,reached,true);
    add_nodes(&mut set,required,false);
    Ok(set)
}

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
