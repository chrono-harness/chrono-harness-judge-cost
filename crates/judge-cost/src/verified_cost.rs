//! Declared cost selection and coordinate admission for the production report.
#![allow(unexpected_cfgs)]
use std::collections::BTreeSet;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::string::StringExecFns;

#[cfg(verus_keep_ghost)]
#[path = "lib.rs"]
pub mod cost_model;

#[cfg(verus_keep_ghost)]
#[path = "report.rs"]
pub mod report;

verus! {

pub const MAX_REPORT_BYTES: usize = 64 * 1024 * 1024;

/// The reader obtains at most one extra byte to distinguish the inclusive limit.
pub fn check_report_size(length: usize) -> (out: Result<(), &'static str>)
    ensures
        out.is_ok() == (length <= 67108864),
        out matches Err(message) ==> message@ == "E_INPUT: report input exceeds 64 MiB"@,
{
    if length > MAX_REPORT_BYTES { Err("E_INPUT: report input exceeds 64 MiB") } else { Ok(()) }
}

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

#[derive(Clone, Copy)]
pub enum Endpoint { Base, Candidate }

impl Endpoint {
    fn label(self) -> (name: &'static str)
        ensures name@ == match self { Endpoint::Base => "base"@, Endpoint::Candidate => "candidate"@ },
    {
        match self { Endpoint::Base => "base", Endpoint::Candidate => "candidate" }
    }
}

/// A registered project or script with zero members has no model reference.
#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct NoMembers<'a> {
    pub endpoint: &'static str,
    pub node: &'a str,
    pub reference: (),
    pub coordinates: Vec<&'static str>,
    pub reason: &'static str,
}

pub fn no_members(endpoint: Endpoint, node: &str) -> (out: NoMembers<'_>)
    ensures out.endpoint@ == match endpoint { Endpoint::Base => "base"@, Endpoint::Candidate => "candidate"@ },
        out.node == node, out.reason@ == "no declared member cost references"@,
        coordinate_names(out.coordinates@) == missing_names(true, true, true, true),
{
    NoMembers {
        endpoint: endpoint.label(), node, reference: (),
        coordinates: missing_coordinate_names(true, true, true, true),
        reason: "no declared member cost references",
    }
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct UnknownMember<'a, V> {
    pub endpoint: &'static str,
    pub node: &'a str,
    pub member: &'a V,
    pub reference: &'a V,
    pub source: &'a V,
    pub coordinates: Vec<&'static str>,
    pub reason: &'a V,
}

/// The publication decision and the published names use one coordinate list.
pub fn unknown_member<'a, V>(
    endpoint: Endpoint, node: &'a str, member: &'a V, reference: &'a V, source: &'a V, basis: &'a V,
    missing: (bool, bool, bool, bool),
) -> (out: Option<UnknownMember<'a, V>>)
    ensures out.is_some() == (missing.0 || missing.1 || missing.2 || missing.3),
        out matches Some(entry) ==> {
            &&& entry.endpoint@ == match endpoint { Endpoint::Base => "base"@, Endpoint::Candidate => "candidate"@ }
            &&& entry.node == node && entry.member == member && entry.reference == reference
            &&& entry.source == source && entry.reason == basis
            &&& coordinate_names(entry.coordinates@) == missing_names(missing.0, missing.1, missing.2, missing.3)
            &&& entry.coordinates.len() == missing_names(missing.0, missing.1, missing.2, missing.3).len()
            &&& forall|i:int| 0 <= i < entry.coordinates.len() ==> (#[trigger] entry.coordinates@[i])@
                == missing_names(missing.0, missing.1, missing.2, missing.3)[i]
        },
{
    let (cpu, wall, peak, io) = missing;
    let coordinates = missing_coordinate_names(cpu, wall, peak, io);
    if coordinates.is_empty() { return None; }
    Some(UnknownMember {endpoint: endpoint.label(), node, member, reference, source, coordinates, reason: basis})
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
pub fn direct_report(name: Option<&str>, count: usize) -> (chosen: bool)
    ensures chosen == (count == 1 && (name matches Some(s) && s@ == "report-v1"@)),
{
    count == 1 && match name { Some(s) => <&str>::exec_eq(s, "report-v1"), None => false }
}
pub enum Arg<'a, P> { Text(&'a str), Path(&'a P) }
pub struct Invocation<'a,P,A> {
    pub program: &'static str, pub prefix: [Arg<'a,P>;7], pub forwarded: &'a [A],
}
pub fn invocation<'a,P,A>(executable: &'a P, version: &'a str, args: &'a [A]) -> (out: Invocation<'a,P,A>)
    ensures out.program@=="chrono-harness"@ && out.forwarded==args,
        out.prefix[0] matches Arg::Text(s) && s@=="judge-pipeline"@,
        out.prefix[1] matches Arg::Text(s) && s@=="chrono-judge-cost"@,
        out.prefix[2] matches Arg::Text(s) && s==version,
        out.prefix[3] matches Arg::Text(s) && s@=="chrono-judge-filemap"@,
        out.prefix[4] matches Arg::Text(s) && s@=="cost-inputs-v1"@,
        out.prefix[5] matches Arg::Path(p) && p==executable,
        out.prefix[6] matches Arg::Text(s) && s@=="report-v1"@,
{
    Invocation { program:"chrono-harness",prefix:[
        Arg::Text("judge-pipeline"),Arg::Text("chrono-judge-cost"),Arg::Text(version),
        Arg::Text("chrono-judge-filemap"),Arg::Text("cost-inputs-v1"),Arg::Path(executable),Arg::Text("report-v1")
    ],forwarded:args}
}
pub fn delegation_error<P,E,L,X>(locate:L,execute:X)->(out:(u8,&'static str,E))
    where L:FnOnce()->Result<P,E>,X:FnOnce(P)->E,
    requires locate.requires(()),forall|p:P| execute.requires((p,)),
    ensures out.0==2 && ((locate.ensures((),Err::<P,E>(out.2)) && out.1@=="chrono-judge-cost"@)
        || (exists|p:P| #[trigger] locate.ensures((),Ok::<P,E>(p)) && execute.ensures((p,),out.2) && out.1@=="chrono-harness"@)),
{
    match locate() {Err(e)=>(2,"chrono-judge-cost",e),Ok(p)=>(2,"chrono-harness",execute(p))}
}
pub fn exit_report<E>(result:Result<(),E>)->(out:(u8,Option<E>))
    ensures match result {Ok(())=>out==(0u8,None::<E>),Err(e)=>out==(2u8,Some(e))},
{ match result {Ok(())=>(0,None),Err(e)=>(2,Some(e))} }

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Location<'a> {pub registry:&'a str,pub pointer:String}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct ModelReference<'a,V> {
    pub reference:&'a str,pub member:&'a str,pub value:&'a V,pub source:Location<'a>,pub declaration:Location<'a>,
}
pub fn model_reference<'a,V>(model:Option<&'a V>,id:&'a str,member:&'a str,registry:&'a str,source:String,declaration:String)
    ->(out:Option<ModelReference<'a,V>>)
    ensures out.is_some()==model.is_some(), out matches Some(r) ==> Some(r.value)==model
        && r.reference==id && r.member==member && r.source.registry==registry && r.declaration.registry==registry
        && r.source.pointer==source && r.declaration.pointer==declaration,
{
    match model {None=>None,Some(value)=>Some(ModelReference {
        reference:id,member,value,source:Location{registry,pointer:source},declaration:Location{registry,pointer:declaration}
    })}
}

pub enum Selection { Missing, MissingTest, File(usize), Test(usize), Owner(&'static str,Vec<usize>) }
pub fn declaration(files:&[CostFile], tests:&[TestCost],kind:CostKind,id:&str,registered:bool)->(out:Selection)
    ensures match kind {
        CostKind::File => match out {
            Selection::Missing=>forall|i:int| 0<=i<files.len() ==> (#[trigger] files@[i]).path@!=id@,
            Selection::File(i)=> i<files.len() && files@[i as int].path@==id@ && forall|j:int| 0<=j<i ==> (#[trigger] files@[j]).path@!=id@,
            _=>false,
        },
        CostKind::Test => if !registered {out is Missing} else {match out {
            Selection::MissingTest=>forall|i:int| 0<=i<tests.len() ==> (#[trigger] tests@[i]).test@!=id@,
            Selection::Test(i)=>i<tests.len() && tests@[i as int].test@==id@ && forall|j:int| 0<=j<i ==> (#[trigger] tests@[j]).test@!=id@,
            _=>false,
        }},
        _=>if !registered {out is Missing} else {out matches Selection::Owner(label,rows)
            && label@==(if kind is Project {"project"@} else {"script"@}) && rows@==owned_rows(files@,id@,files.len() as nat)},
    },
{
    match kind {
        CostKind::File=>match first_declaration(files,id) {Some(i)=>Selection::File(i),None=>Selection::Missing},
        CostKind::Test=>if !registered {Selection::Missing} else {match first_declaration(tests,id) {Some(i)=>Selection::Test(i),None=>Selection::MissingTest}},
        CostKind::Project=>if registered {Selection::Owner("project",owner_members(files,id))} else {Selection::Missing},
        CostKind::Script=>if registered {Selection::Owner("script",owner_members(files,id))} else {Selection::Missing},
    }
}

pub fn endpoints<'a,T,E,R,F>(base:&'a R,candidate:&'a R,entry:F)->(out:Result<(T,T),E>)
    where F:Fn(&'a R)->Result<T,E>,
    requires entry.requires((base,)),entry.requires((candidate,)),
    ensures match out {
        Ok((a,b))=>entry.ensures((base,),Ok::<T,E>(a)) && entry.ensures((candidate,),Ok::<T,E>(b)),
        Err(e)=>entry.ensures((base,),Err::<T,E>(e)) ||
            ((exists|a:T| #[trigger] entry.ensures((base,),Ok::<T,E>(a))) && entry.ensures((candidate,),Err::<T,E>(e))),
    },
{
    let a=entry(base)?;let b=entry(candidate)?;Ok((a,b))
}
#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct CostDocument<'a,M,U> {
    pub schema:&'static str, pub declared_before:&'a M,pub declared_after:&'a M,
    pub affected_tests:&'a [String],pub retired_tests:&'a [String],pub removed_nodes:&'a [String],
    pub unknown:&'a [U],pub measured:(),pub measurement_status:&'static str,pub aggregation:&'static str,
}
pub const COST_SCHEMA:&'static str="chrono-costs/v1";
pub fn document<'a,M,U>(before:&'a M,after:&'a M,affected:&'a [String],retired:&'a [String],removed:&'a [String],unknown:&'a [U])
    ->(out:CostDocument<'a,M,U>)
    ensures out.schema@=="chrono-costs/v1"@ && out.declared_before==before && out.declared_after==after
        && out.affected_tests==affected && out.retired_tests==retired && out.removed_nodes==removed && out.unknown==unknown
        && out.measurement_status@=="not measured; declarations are estimates, not process measurements"@
        && out.aggregation@=="none; member references are retained without summing resource peaks or parallel wall time"@,
{
    CostDocument { schema:COST_SCHEMA,declared_before:before,declared_after:after,affected_tests:affected,retired_tests:retired,
        removed_nodes:removed,unknown,measured:(),measurement_status:"not measured; declarations are estimates, not process measurements",
        aggregation:"none; member references are retained without summing resource peaks or parallel wall time" }
}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Bound<'a,M,U,B> {
    #[cfg_attr(not(verus_keep_ghost),serde(flatten))]
    pub document:CostDocument<'a,M,U>,pub binding:B,
}
#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Outputs<'a,M,U,B> {pub costs:Bound<'a,M,U,B>}
#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Report<'a,M,U,B> {
    pub status:&'static str,pub findings:Vec<CostFinding>,pub outputs:Outputs<'a,M,U,B>,
}
pub fn report<'a,M,U,B>(document:CostDocument<'a,M,U>,binding:B)->(out:Report<'a,M,U,B>)
    ensures out.outputs.costs.document==document && out.outputs.costs.binding==binding,
        out.status@==if document.unknown.len()==0 {"pass"@}else{"warn"@},
        out.findings.len()==if document.unknown.len()==0 {0usize}else{1usize},
        document.unknown.len()>0 ==> {
            let finding=out.findings@[0];
            &&& finding.code@=="W_COST_UNKNOWN"@ && finding.level@=="warning"@
            &&& finding.message@=="Affected declared costs contain unknown coordinates; see costs.unknown"@
            &&& finding.delta_refs@[0]@=="/impact"@ && finding.causes@[0]@=="/outputs/costs/unknown"@
        },
{
    let decision=report_decision(document.unknown);
    Report {status:decision.status,findings:decision.findings,outputs:Outputs{costs:Bound{document,binding}}}
}
pub open spec fn pointer_suffix(chars:Seq<char>,n:int)->Seq<char>
    decreases n,
{
    if n<=0 {Seq::empty()} else {let prev=pointer_suffix(chars,n-1);match chars[n-1] {
        '~'=>prev.push('~').push('0'),'/'=>prev.push('~').push('1'),c=>prev.push(c),
    }}
}

pub fn escaped_model_token(key:&str)->(out:Vec<char>)
    ensures out@==pointer_suffix(key@,key@.len() as int),
{
    let mut output:Vec<char>=Vec::new();let mut chars=key.chars();
    loop
        invariant chars@.1==key@,0<=chars@.0<=key@.len(),output@==pointer_suffix(key@,chars@.0),
        ensures output@==pointer_suffix(key@,key@.len() as int),
        decreases key@.len()-chars@.0,
    {
        let ghost previous=chars@.0;
        match chars.next(){
            None=>break,
            Some(c)=>{
                let token=pointer_token(c);
                if let Some(first)=token[0] {output.push(first);}
                if let Some(extra)=token[1] {output.push(extra);}
                assert(key@[previous]==c);
            }
        }
    }
    output
}
pub struct SubjectRow<V,U> {pub before:Option<V>,pub after:Option<V>,pub unknown:Vec<U>}
pub struct Entries<V,U> {
    pub before:std::collections::BTreeMap<String,Option<V>>,pub after:std::collections::BTreeMap<String,Option<V>>,
    pub unknown:Vec<U>,pub removed:Vec<String>,
}
pub open spec fn visited<V,U,E,F:Fn(&String)->Result<SubjectRow<V,U>,E>>(keys:Seq<String>,n:int,visit:F,rows:Seq<SubjectRow<V,U>>)->bool {
    &&& rows.len()==n
    &&& forall|i:int| 0<=i<n ==> visit.ensures((&keys[i],),Ok::<SubjectRow<V,U>,E>(#[trigger] rows[i]))
}
pub open spec fn declared<V,U>(keys:Seq<String>,rows:Seq<SubjectRow<V,U>>,base:bool)->Map<String,Option<V>>
    decreases rows.len(),
{
    if rows.len()==0 {Map::empty()} else {let end=rows.len()-1;
        declared(keys,rows.drop_last(),base).insert(keys[end],if base {rows[end].before}else{rows[end].after})}
}
pub open spec fn missing_entries<V,U>(rows:Seq<SubjectRow<V,U>>)->Seq<U>
    decreases rows.len(),
{if rows.len()==0 {Seq::empty()} else {missing_entries(rows.drop_last())+rows.last().unknown@}}
pub open spec fn removed_subjects<V,U>(keys:Seq<String>,rows:Seq<SubjectRow<V,U>>)->Seq<String>
    decreases rows.len(),
{if rows.len()==0 {Seq::empty()} else {let previous=removed_subjects(keys,rows.drop_last());let i=rows.len()-1;
    if rows[i].before.is_some() && rows[i].after.is_none() {previous.push(keys[i])} else {previous}}}

pub fn collect<V,U,E,F,M>(keys:&[String],visit:F,missing:M)->(out:Result<Entries<V,U>,E>)
    where F:Fn(&String)->Result<SubjectRow<V,U>,E>, M:Fn(PresenceError)->E,
    requires vstd::laws_cmp::obeys_cmp::<String>(),forall|s:&String| visit.requires((s,)), forall|e:PresenceError| missing.requires((e,)),
    ensures match out {
        Ok(v)=>exists|rows:Seq<SubjectRow<V,U>>| #[trigger] visited(keys@,keys.len() as int,visit,rows)
            && v.before@==declared(keys@,rows,true) && v.after@==declared(keys@,rows,false)
            && v.unknown@==missing_entries(rows) && v.removed@==removed_subjects(keys@,rows),
        Err(e)=>exists|i:int,rows:Seq<SubjectRow<V,U>>| 0<=i<keys.len() && #[trigger] visited(keys@,i,visit,rows)
            && (visit.ensures((&keys@[i],),Err::<SubjectRow<V,U>,E>(e))
                || exists|row:SubjectRow<V,U>,why:PresenceError| #[trigger] visit.ensures((&keys@[i],),Ok::<SubjectRow<V,U>,E>(row))
                    && row.before.is_none() && row.after.is_none() && why.subject@==keys@[i]@
                    && why.message@=="E_COST_REFERENCE: no declaration at either endpoint for "@ && #[trigger] missing.ensures((why,),e)),
    },
{
    let mut before=std::collections::BTreeMap::new();let mut after=std::collections::BTreeMap::new();
    let mut unknown=Vec::new();let mut removed=Vec::new();let mut i=0;let ghost mut rows=Seq::empty();
    while i<keys.len()
        invariant i<=keys.len(),visited(keys@,i as int,visit,rows),before@==declared(keys@,rows,true),after@==declared(keys@,rows,false),
            unknown@==missing_entries(rows),removed@==removed_subjects(keys@,rows),vstd::laws_cmp::obeys_cmp::<String>(),
            forall|s:&String| visit.requires((s,)),forall|e:PresenceError| missing.requires((e,)),
        decreases keys.len()-i,
    {
        let k=&keys[i];let mut row=match visit(k) {Ok(r)=>r,Err(e)=>{assert(visited(keys@,i as int,visit,rows));return Err(e)}};
        let ghost next=rows.push(row);assert(next.drop_last() =~= rows);
        if let Err(reason)=record_subject_presence(row.before.is_some(),row.after.is_some(),k.clone(),&mut removed) {
            let error=missing(reason);
            assert(visited(keys@,i as int,visit,rows));
            assert(exists|r:SubjectRow<V,U>,why:PresenceError| #[trigger] visit.ensures((k,),Ok::<SubjectRow<V,U>,E>(r))
                && r.before.is_none() && r.after.is_none() && why.subject@==k@
                && why.message@=="E_COST_REFERENCE: no declaration at either endpoint for "@ && #[trigger] missing.ensures((why,),error));
            return Err(error);
        }
        before.insert(k.clone(),row.before);after.insert(k.clone(),row.after);unknown.append(&mut row.unknown);
        proof {rows=next;} i+=1;
    }
    assert(visited(keys@,keys.len() as int,visit,rows));
    Ok(Entries{before,after,unknown,removed})
}
/// Map actual model references to the ordered list of unknown members.
pub open spec fn chosen<T>(items:Seq<Option<T>>)->Seq<T>
    decreases items.len(),
{ if items.len()==0 {Seq::empty()} else {let prefix=chosen(items.drop_last());match items.last(){None=>prefix,Some(v)=>prefix.push(v)}} }

pub open spec fn projected<A,T,F:Fn(&A)->Option<T>>(models:Seq<A>,n:int,emit:F,items:Seq<Option<T>>)->bool {
    items.len()==n && forall|i:int| 0<=i<n ==> emit.ensures((&models[i],),#[trigger] items[i])
}
pub fn unknown_entries<A,T,F,N>(members:Option<&[A]>,emit:F,no_members:N)->(out:Vec<T>)
    where F:Fn(&A)->Option<T>,N:FnOnce()->T,
    requires forall|a:&A| emit.requires((a,)),no_members.requires(()),
    ensures match members {
        None=>out.len()==0,
        Some(m)=>if m.len()==0 {out.len()==1 && no_members.ensures((),out@[0])} else {
            exists|items:Seq<Option<T>>| #[trigger] projected(m@,m.len() as int,emit,items) && out@==chosen(items)
        },
    },
{
    let Some(m)=members else {return Vec::new()};
    if m.is_empty() {return vec![no_members()];}
    let mut out=Vec::new();let mut i=0;let ghost mut items=Seq::empty();
    while i<m.len()
        invariant i<=m.len(),projected(m@,i as int,emit,items),out@==chosen(items),forall|a:&A| emit.requires((a,)),
        decreases m.len()-i,
    {
        let item=emit(&m[i]);let ghost next=items.push(item);assert(next.drop_last() =~= items);
        if let Some(x)=item {out.push(x);}
        assert forall|j:int| 0<=j<i+1 implies emit.ensures((&m@[j],),#[trigger] next[j]) by {
            if j<i {assert(next[j]==items[j]);}
        }
        proof {items=next;} i+=1;
    }
    assert(projected(m@,m.len() as int,emit,items));
    out
}
pub fn ordered_sides<T,U,F>(before:&T,after:&T,visit:F)->(out:Vec<U>)
    where F:Fn(Endpoint,&T)->Vec<U>,
    requires visit.requires((Endpoint::Base,before)),visit.requires((Endpoint::Candidate,after)),
    ensures exists|a:Vec<U>,b:Vec<U>| #[trigger] visit.ensures((Endpoint::Base,before),a)
        && #[trigger] visit.ensures((Endpoint::Candidate,after),b) && out@==a@+b@,
{
    let mut a=visit(Endpoint::Base,before);
    let mut b=visit(Endpoint::Candidate,after);
    let ghost x=a;let ghost y=b;
    a.append(&mut b);a
}

}
