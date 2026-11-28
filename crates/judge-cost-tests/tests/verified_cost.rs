//! Independent boundary expectations for the declared-cost Verus policy.
#![allow(unexpected_cfgs)]
#[path = "../../judge-cost/src/verified_cost.rs"]
mod policy;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::string::StringExecFns;
#[cfg(verus_keep_ghost)]
use vstd::vpanic as panic;

#[cfg(not(verus_keep_ghost))]
use chrono_judge_cost::model_fields;
#[cfg(not(verus_keep_ghost))]
use chrono_judge_cost::report::read_report_bytes;
#[cfg(verus_keep_ghost)]
use policy::cost_model::model_fields;
#[cfg(verus_keep_ghost)]
use policy::report::read_report_bytes;

#[path = "../../../.chrono-harness/ci/roadmap.rs"]
mod roadmap;

verus! {

#[cfg(verus_keep_ghost)]
fn diagnostic_delivery_preserves_the_business_status() {
    let readable = policy::cli::finish(2, Some(String::new()), |_message: String| true);
    let closed = policy::cli::finish(2, Some(String::new()), |_message: String| false);
    let success = policy::cli::finish(0, None, |_message: String| false);
    assert(readable == 2 && closed == 2 && success == 0);
}

/// Each missing field must set exactly its own report coordinate.
fn check_model_field(key: &'static str) {
    let read = |name: &'static str| -> (absent: bool)
        ensures absent == (name@ == key@),
    { <&str>::exec_eq(name, key) };
    let mask = model_fields(read);
    expect(mask.0 == <&str>::exec_eq(key, "cpu_ms"));
    expect(mask.1 == <&str>::exec_eq(key, "wall_ms"));
    expect(mask.2 == <&str>::exec_eq(key, "peak_rss_bytes"));
    expect(mask.3 == <&str>::exec_eq(key, "io_bytes"));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn each_model_key_reaches_its_own_coordinate() {
    check_model_field("cpu_ms");
    check_model_field("wall_ms");
    check_model_field("peak_rss_bytes");
    check_model_field("io_bytes");
    check_model_field("other");
    let all = model_fields(|_name: &'static str| -> (absent: bool)
        ensures absent, { true });
    expect(all.0 && all.1 && all.2 && all.3);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn unknown_reads_basis_and_coordinates_from_the_referenced_model() {
    let value = 7u8;
    let basis = 11u8;
    let unrelated = 19u8;
    let Ok(cost) = policy::model_reference(
        Some(&value), "original", String::from_str("file:z"), "registry",
        String::from_str("/cost_models/original"), String::from_str("/files/2/cost"),
    ) else { expect(false); return; };
    let missing = |observed: &u8, key: &'static str| -> (absent: bool)
        ensures absent == (*observed == 7 && key@ == "wall_ms"@),
    { *observed == 7 && <&str>::exec_eq(key, "wall_ms") };
    let field = |observed: &u8, key: &'static str| -> (result: &u8)
        ensures *result == if *observed == 7 && key@ == "basis"@ { 11u8 } else { 19u8 },
    {
        if *observed == 7 && <&str>::exec_eq(key, "basis") { &basis } else { &unrelated }
    };
    let unknown = policy::model_unknown(policy::Endpoint::Candidate, "project:p", &cost, missing, field)
        .unwrap();
    expect_name(unknown.endpoint, "candidate");
    expect_name(unknown.node, "project:p");
    expect_name(unknown.member.as_str(), "file:z");
    expect_name(*unknown.reference, "original");
    expect_name(unknown.source.pointer.as_str(), "/cost_models/original");
    expect(*unknown.reason == 11);
    proof {
        let (cpu, wall, peak, io) = choose|cpu: bool, wall: bool, peak: bool, io: bool|
            #[trigger] missing.ensures((cost.value, "cpu_ms"), cpu)
            && #[trigger] missing.ensures((cost.value, "wall_ms"), wall)
            && #[trigger] missing.ensures((cost.value, "peak_rss_bytes"), peak)
            && #[trigger] missing.ensures((cost.value, "io_bytes"), io)
            && unknown.coordinates.len() == policy::missing_names(cpu, wall, peak, io).len()
            && forall|i: int| 0 <= i < unknown.coordinates.len() ==>
                (#[trigger] unknown.coordinates@[i])@ == policy::missing_names(cpu, wall, peak, io)[i];
        reveal_strlit("cpu_ms");
        reveal_strlit("wall_ms");
        reveal_strlit("peak_rss_bytes");
        reveal_strlit("io_bytes");
        assert(missing.ensures((cost.value, "cpu_ms"), cpu));
        assert(missing.ensures((cost.value, "wall_ms"), wall));
        assert(missing.ensures((cost.value, "peak_rss_bytes"), peak));
        assert(missing.ensures((cost.value, "io_bytes"), io));
        assert("cpu_ms"@[0] != "wall_ms"@[0]);
        assert("peak_rss_bytes"@[0] != "wall_ms"@[0]);
        assert("io_bytes"@[0] != "wall_ms"@[0]);
        assert(!cpu && wall && !peak && !io);
    }
    expect(unknown.coordinates.len() == 1);
    expect_name(unknown.coordinates[0], "wall_ms");
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn sort_keys_keep_original_rows_and_resolution_stops_at_the_first_missing_model() {
    let files = [file("z", "p"), file("a", "p"), file("a", "p")];
    let keys = policy::member_sort_keys(&files, &[0, 1, 2]);
    expect(keys.len() == 3);
    expect_name(keys[0].0, "z");
    expect_name(keys[1].0, "a");
    expect_name(keys[2].0, "a");
    expect(keys[0].1 == 0 && keys[1].1 == 1 && keys[2].1 == 2);

    // This literal is the external sort's expected output for those keys.
    let ordered = [("a", 1usize), ("a", 2usize), ("z", 0usize)];
    let resolve = |row: usize| -> (result: Result<usize, usize>)
        ensures result == if row == 1 { Ok(row) } else { Err(row) },
    { if row == 1 { Ok(row) } else { Err(row) } };
    let result = policy::resolve_members(&ordered, resolve);
    proof {
        match result {
            Err(error) => {
                let prefix = choose|prefix: Seq<usize>| prefix.len() < ordered.len()
                    && #[trigger] resolve.ensures((ordered@[prefix.len() as int].1,), Err(error))
                    && policy::resolved_prefix(ordered@, resolve, prefix);
                if prefix.len() == 2 {
                    assert(resolve.ensures((ordered@[1].1,), Ok(prefix[1])));
                }
            },
            Ok(ref values) => {
                assert(resolve.ensures((ordered@[1].1,), Ok(values@[1])));
            },
        }
    }
    expect(matches!(result, Err(2)));
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn dispatch_and_pipeline_keep_native_tail_and_child_identity() {
    expect(policy::direct_report(Some("report-v1"),1));
    expect(!policy::direct_report(Some("report-v1"),2));
    expect(!policy::direct_report(None,1));
    proof {reveal_strlit("--version");reveal_strlit("report-v1");assert("--version"@[0]!= "report-v1"@[0]);}
    expect(!policy::direct_report(Some("--version"),1));
    let path=7u8;let argv=[0x80u8,0xffu8];
    let invocation=policy::invocation(&path,"1",&argv);
    expect_name(invocation.program,"chrono-harness");
    match &invocation.prefix[0] {policy::Arg::Text(v)=>expect_name(v,"judge-pipeline"),_=>expect(false)}
    match &invocation.prefix[1] {policy::Arg::Text(v)=>expect_name(v,"chrono-judge-cost"),_=>expect(false)}
    match &invocation.prefix[2] {policy::Arg::Text(v)=>expect_name(v,"1"),_=>expect(false)}
    match &invocation.prefix[3] {policy::Arg::Text(v)=>expect_name(v,"chrono-judge-filemap"),_=>expect(false)}
    match &invocation.prefix[4] {policy::Arg::Text(v)=>expect_name(v,"cost-inputs-v1"),_=>expect(false)}
    match &invocation.prefix[5] {policy::Arg::Path(v)=>expect(**v==7),_=>expect(false)}
    match &invocation.prefix[6] {policy::Arg::Text(v)=>expect_name(v,"report-v1"),_=>expect(false)}
    expect(invocation.forwarded.len()==2 && invocation.forwarded[0]==0x80 && invocation.forwarded[1]==0xff);
    expect(matches!(policy::exit_report(Err::<(),u8>(5)),(2,Some(5))));
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn copied_reports_keep_both_declarations_test_lists_original_sources_and_binding() {
    let a=4u8;let b=9u8;
    let affected=vec![String::from_str("new")];
    let retired=vec![String::from_str("old")];
    let document=policy::document(&a,&b,&affected,&retired,&[],&[1u8]);
    let report=policy::report(document,13u8);
    expect_name(report.status,"warn");expect(report.outputs.costs.binding==13);
    let d=&report.outputs.costs.document;
    expect(*d.declared_before==4 && *d.declared_after==9);
    expect_name(d.affected_tests[0].as_str(),"new");expect_name(d.retired_tests[0].as_str(),"old");
    expect_name(d.schema,"chrono-costs/v1");expect(d.unknown.len()==1 && d.unknown[0]==1);
    let Ok(r)=policy::model_reference(Some(&b),"id",String::from_str("member"),"fm",String::from_str("/source"),String::from_str("/row")) else { expect(false); return; };
    expect_name(r.member.as_str(),"member");expect_name(r.reference,"id");expect(*r.value==9);
    expect_name(r.source.pointer.as_str(),"/source");expect_name(r.declaration.pointer.as_str(),"/row");
    expect_name(r.source.registry,"fm");expect_name(r.declaration.registry,"fm");
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn original_endpoint_order_and_memberless_state_are_distinct() {
    let old=2u8;let new=3u8;
    let render=|x:&u8|->(v:Result<u8,u8>) ensures v==Ok::<u8,u8>(*x), {Ok(*x)};
    expect(matches!(policy::endpoints(&old,&new,render),Ok((2,3))));
    let side=|side:policy::Endpoint,n:&u8|->(v:Vec<u8>) ensures v.len()==1 && v@[0]==(if side is Base {*n}else{9u8}), {
        match side {policy::Endpoint::Base=>vec![*n],policy::Endpoint::Candidate=>vec![9u8]}
    };
    let both=policy::ordered_sides(&old,&new,side);
    proof { let (a,b)=choose|a:Vec<u8>,b:Vec<u8>| #[trigger] side.ensures((policy::Endpoint::Base,&old),a)
        && #[trigger] side.ensures((policy::Endpoint::Candidate,&new),b) && both@==a@+b@;
        assert(both@ =~= seq![2u8,9u8]); }
    expect(both.len()==2 && both[0]==2 && both[1]==9);
    let visit=|a:&u8|->(item:Option<u8>) ensures item==Some(*a),{Some(*a)};
    let missing=||->(x:u8) ensures x==5, {5u8};
    expect(policy::unknown_entries(None::<&policy::DeclaredCost<u8>>,visit,missing).len()==0);
    let empty=policy::DeclaredCost::<u8> { kind: "project", costs: Vec::new() };
    let one=policy::unknown_entries(Some(&empty),visit,missing);
    expect(one.len()==1 && one[0]==5);
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn registered_test_missing_row_and_unregistered_owner_have_different_results() {
    let files:[policy::CostFile;0]=[];let tests:[policy::TestCost;0]=[];
    expect(matches!(policy::declaration(&files,&tests,policy::CostKind::Test,"t",true),policy::Selection::MissingTest));
    expect(matches!(policy::declaration(&files,&tests,policy::CostKind::Test,"t",false),policy::Selection::Missing));
    expect(matches!(policy::declaration(&files,&tests,policy::CostKind::File,"f",true),policy::Selection::Missing));
    expect(matches!(policy::declaration(&files,&tests,policy::CostKind::Project,"p",false),policy::Selection::Missing));
    match policy::declaration(&files,&tests,policy::CostKind::Script,"s",true) {
        policy::Selection::Owner(kind,rows)=>{expect_name(kind,"script");expect(rows.len()==0);}
        _=>expect(false),
    }
}


fn expect(actual: bool)
    requires actual,
{
    if !actual { panic!(); }
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn bounded_report_read_preserves_the_reader_result() {
    let read = |limit: u64| -> (out: Result<Vec<u8>, String>)
        ensures match out { Ok(bytes) => limit == 67108865 && bytes@ == seq![81u8],
            Err(_) => limit != 67108865 },
    {
        if limit == 67108865 {
            let mut bytes = Vec::new();
            bytes.push(81);
            Ok(bytes)
        } else { Err("wrong read limit".to_string()) }
    };
    match read_report_bytes(read) {
        Ok(bytes) => { expect(bytes.len() == 1); expect(bytes[0] == 81); },
        Err(_) => expect(false),
    }
    let failure = |_limit: u64| -> (out: Result<Vec<u8>, String>)
        ensures out matches Err(reason) && reason@ == "reader failed"@,
    { Err("reader failed".to_string()) };
    match read_report_bytes(failure) {
        Err(reason) => expect_name(&reason, "reader failed"),
        Ok(_) => expect(false),
    }
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn cost_report_size_includes_the_last_byte() {
    expect(policy::check_report_size(0).is_ok());
    expect(policy::check_report_size(67108863).is_ok());
    expect(policy::check_report_size(67108864).is_ok());
    expect(policy::check_report_size(67108865).is_err());
}

fn expect_name(actual: &str, expected: &str)
    requires actual@ == expected@,
{
    let equal = <&str>::exec_eq(actual, expected);
    expect(equal);
}

/// A decoder can recover every original Unicode scalar from its emitted token.
#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
fn pointer_token_recovers_original(character: char) {
    let token = policy::pointer_token(character);
    let recovered = match (token[0], token[1]) {
        (Some('~'), Some('0')) => '~',
        (Some('~'), Some('1')) => '/',
        (Some(c), None) if c != '~' && c != '/' => c,
        _ => { expect(false); return; }
    };
    expect(recovered == character);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn pointer_tokens_distinguish_controls_digits_and_unicode() {
    pointer_token_recovers_original('~');
    pointer_token_recovers_original('/');
    pointer_token_recovers_original('0');
    pointer_token_recovers_original('1');
    pointer_token_recovers_original('路');
    pointer_token_recovers_original('\0');
}

/// For every identifier, including an empty one, the report recovers all its characters.
#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
fn all_four_tags_recover_the_original_id(id: &str) {
    proof {
        reveal_strlit("file:"); reveal_strlit("project:"); reveal_strlit("script:"); reveal_strlit("test:");
        assert("file:"@[0] != "project:"@[0] && "file:"@[0] != "script:"@[0] && "file:"@[0] != "test:"@[0]);
        assert("project:"@[0] != "script:"@[0] && "project:"@[0] != "test:"@[0] && "script:"@[0] != "test:"@[0]);
    }
    let file = "file:".to_string().concat(id);
    let project = "project:".to_string().concat(id);
    let script = "script:".to_string().concat(id);
    let test = "test:".to_string().concat(id);
    assert("file:"@.is_prefix_of(file@) && "project:"@.is_prefix_of(project@)
        && "script:"@.is_prefix_of(script@) && "test:"@.is_prefix_of(test@));
    let f = policy::cost_subject(file.as_str()).unwrap();
    let p = policy::cost_subject(project.as_str()).unwrap();
    let s = policy::cost_subject(script.as_str()).unwrap();
    let t = policy::cost_subject(test.as_str()).unwrap();
    expect(matches!(f.0, policy::CostKind::File));
    expect(matches!(p.0, policy::CostKind::Project));
    expect(matches!(s.0, policy::CostKind::Script));
    expect(matches!(t.0, policy::CostKind::Test));
    assert(f.1@ =~= id@); assert(p.1@ =~= id@);
    assert(s.1@ =~= id@); assert(t.1@ =~= id@);
    expect_name(f.1, id); expect_name(p.1, id); expect_name(s.1, id); expect_name(t.1, id);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn subject_kind_and_original_identifier() {
    all_four_tags_recover_the_original_id("");
    all_four_tags_recover_the_original_id("目录:β/一");
    proof {
        reveal_strlit("files:x"); reveal_strlit("file"); reveal_strlit("File:x"); reveal_strlit("");
        reveal_strlit("file:"); reveal_strlit("project:"); reveal_strlit("script:"); reveal_strlit("test:");
        assert("files:x"@[4] != "file:"@[4] && "files:x"@[0] != "project:"@[0]
            && "files:x"@[0] != "script:"@[0] && "files:x"@[0] != "test:"@[0]);
        assert("File:x"@[0] != "file:"@[0] && "File:x"@[0] != "project:"@[0]
            && "File:x"@[0] != "script:"@[0] && "File:x"@[0] != "test:"@[0]);
    }
    let near = policy::cost_subject("files:x");
    let bare = policy::cost_subject("file");
    let upper = policy::cost_subject("File:x");
    let empty = policy::cost_subject("");
    expect(near.is_none()); expect(bare.is_none()); expect(upper.is_none()); expect(empty.is_none());
}

/// Any changed path produces exactly one file object even when the path occurs twice.
#[cfg_attr(not(verus_keep_ghost), test)]
fn duplicate_changes_have_one_prefixed_subject()
    requires vstd::laws_cmp::obeys_cmp::<String>(),
{
    let rows = [policy::Changed { path: "目录/源".to_string() },
                policy::Changed { path: "目录/源".to_string() }];
    let result = policy::cost_subjects("chrono-filemap-impact/v6",&rows,&[],&[]);
    expect(result.is_ok());
    let set = result.unwrap();
    proof {
        reveal_with_fuel(policy::changed_names, 3);
        assert(policy::subject_names(set@) =~= Set::empty().insert("file:"@ + "目录/源"@));
    }
    let wrong = policy::cost_subjects("v5",&rows,&[],&[]);
    proof {
        reveal_strlit("v5"); reveal_strlit("chrono-filemap-impact/v6");
        assert("v5"@.len() != "chrono-filemap-impact/v6"@.len());
    }
    expect(wrong.is_err());
}

fn file(path: &str, owner: &str) -> (row: policy::CostFile)
    ensures row.path@ == path@, row.owner@ == owner@, row.cost@ == "estimate"@,
{
    policy::CostFile { path: path.to_string(), owner: owner.to_string(), cost: "estimate".to_string() }
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn lookup_retains_first_row_and_all_members_in_original_order() {
    proof {
        reveal_strlit("");
        reveal_strlit("费用");
        reveal_strlit("费用/一");
        assert(""@.len() == 0 && "费用"@.len() == 2 && "费用/一"@.len() == 4);
    }
    let rows = vec![file("", ""), file("费用", "费用"), file("", ""), file("费用", "费用")];
    let hit = policy::first_declaration(&rows, "费用");
    expect(hit == Some(1));
    expect_name(rows[hit.unwrap()].cost.as_str(), "estimate");
    let miss = policy::first_declaration(&rows, "费用/一");
    expect(miss.is_none());
    let selected = policy::owner_members(&rows, "费用");
    proof { reveal_with_fuel(policy::owned_rows, 5); }
    expect(selected.len() == 2);
    expect(selected[0] == 1 && selected[1] == 3);
    let empty = policy::owner_members(&rows, "费用/一");
    expect(empty.len() == 0);
    let tests = vec![policy::TestCost { test: "test".to_string(), cost: "old".to_string() },
        policy::TestCost { test: "test".to_string(), cost: "later".to_string() }];
    let first = policy::first_declaration(&tests, "test");
    expect(first == Some(0));
    expect_name(tests[first.unwrap()].cost.as_str(), "old");
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn report_publishes_one_warning_for_one_or_more_entries() {
    let none: [u8; 0] = [];
    let known = policy::report_decision(&none);
    expect_name(known.status, "pass");
    expect(known.findings.len() == 0);
    let single = policy::report_decision(&[5u8]);
    expect_name(single.status, "warn");
    expect(single.findings.len() == 1);
    let several = policy::report_decision(&[2u8, 2u8, 9u8]);
    expect_name(several.status, "warn");
    expect(several.findings.len() == 1);
    let warning = &several.findings[0];
    expect_name(warning.code, "W_COST_UNKNOWN");
    expect_name(warning.level, "warning");
    expect_name(warning.message, "Affected declared costs contain unknown coordinates; see costs.unknown");
    expect_name(warning.delta_refs[0], "/impact");
    expect_name(warning.causes[0], "/outputs/costs/unknown");
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn missing_member_keeps_its_endpoint_original_evidence_and_coordinate_order() {
    let member=3u8; let reference=5u8; let source=7u8; let basis=9u8;
    let entry=policy::unknown_member(policy::Endpoint::Candidate,"file:README.md",&member,&reference,&source,&basis,
        (true,false,true,false)).unwrap();
    expect_name(entry.endpoint,"candidate"); expect_name(entry.node,"file:README.md");
    expect(*entry.member==3 && *entry.reference==5 && *entry.source==7 && *entry.reason==9);
    expect(entry.coordinates.len()==2);
    expect_name(entry.coordinates[0],"cpu_ms"); expect_name(entry.coordinates[1],"peak_rss_bytes");
    let entry=policy::no_members(policy::Endpoint::Base,"project:a");
    expect_name(entry.endpoint,"base"); expect_name(entry.node,"project:a");
    expect_name(entry.reason,"no declared member cost references");
    proof {assert(policy::coordinate_names(entry.coordinates@).len()==entry.coordinates.len());}
    expect(entry.coordinates.len()==4);
    let known=policy::unknown_member(policy::Endpoint::Base,"file:README.md",&member,&reference,&source,&basis,
        (false,false,false,false));
    expect(known.is_none());
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn missing_names_preserve_each_coordinate_and_fixed_order() {
    let known = policy::missing_coordinate_names(false, false, false, false);
    expect(known.len() == 0);
    let cpu = policy::missing_coordinate_names(true, false, false, false);
    expect(cpu.len() == 1);
    expect_name(cpu[0], "cpu_ms");
    let wall = policy::missing_coordinate_names(false, true, false, false);
    expect(wall.len() == 1);
    expect_name(wall[0], "wall_ms");
    let peak = policy::missing_coordinate_names(false, false, true, false);
    expect(peak.len() == 1);
    expect_name(peak[0], "peak_rss_bytes");
    let io = policy::missing_coordinate_names(false, false, false, true);
    expect(io.len() == 1);
    expect_name(io[0], "io_bytes");
    let mixed = policy::missing_coordinate_names(true, false, true, true);
    expect(mixed.len() == 3);
    expect_name(mixed[0], "cpu_ms");
    expect_name(mixed[1], "peak_rss_bytes");
    expect_name(mixed[2], "io_bytes");
    let all = policy::missing_coordinate_names(true, true, true, true);
    expect(all.len() == 4);
    expect_name(all[0], "cpu_ms");
    expect_name(all[1], "wall_ms");
    expect_name(all[2], "peak_rss_bytes");
    expect_name(all[3], "io_bytes");
}

#[cfg(verus_keep_ghost)]
fn presence_and_all_coordinates_follow_the_observed_mask(cpu:bool,wall:bool,peak:bool,io:bool) {
    let v=0u8;
    let out=policy::unknown_member(policy::Endpoint::Base,"test:t",&v,&v,&v,&v,(cpu,wall,peak,io));
    assert(out.is_some()==(cpu || wall || peak || io));
    if let Some(entry)=out {
        assert(policy::coordinate_names(entry.coordinates@) == (
            (if cpu {seq!["cpu_ms"@]} else {Seq::empty()}) +
            (if wall {seq!["wall_ms"@]} else {Seq::empty()}) +
            (if peak {seq!["peak_rss_bytes"@]} else {Seq::empty()}) +
            (if io {seq!["io_bytes"@]} else {Seq::empty()})));
    }
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn absent_endpoints_preserve_subject_and_existing_removals() {
    let mut removed = vec!["previous".to_string()];
    let result = policy::record_subject_presence(false, false, "成本\0尾".to_string(), &mut removed);
    expect(result.is_err());
    let error = result.unwrap_err();
    expect_name(error.message, "E_COST_REFERENCE: no declaration at either endpoint for ");
    expect_name(error.subject.as_str(), "成本\0尾");
    expect(removed.len() == 1);
    expect_name(removed[0].as_str(), "previous");
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn only_removed_subjects_append_without_losing_existing_entries() {
    let mut removed = vec!["previous".to_string()];
    let added = policy::record_subject_presence(false, true, "new".to_string(), &mut removed);
    expect(added.is_ok());
    expect(removed.len() == 1);
    let retained = policy::record_subject_presence(true, true, "same".to_string(), &mut removed);
    expect(retained.is_ok());
    expect(removed.len() == 1);
    let deleted = policy::record_subject_presence(true, false, "成本\0尾".to_string(), &mut removed);
    expect(deleted.is_ok());
    expect(removed.len() == 2);
    expect_name(removed[0].as_str(), "previous");
    expect_name(removed[1].as_str(), "成本\0尾");
}

}

#[cfg(not(verus_keep_ghost))]
#[allow(dead_code, unexpected_cfgs)]
#[path = "../../judge-cost/src/main.rs"]
mod cli;

#[cfg(not(verus_keep_ghost))]
#[test]
fn a_diagnostic_write_preserves_the_selected_status() {
    use std::io::{self, Write};

    struct Closed;
    impl Write for Closed {
        fn write(&mut self, _: &[u8]) -> io::Result<usize> {
            Err(io::ErrorKind::BrokenPipe.into())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let mut open = Vec::new();
    assert_eq!(
        cli::finish(2, Some("invalid report".into()), |msg| {
            cli::write_diagnostic(&mut open, msg)
        }),
        2
    );
    assert_eq!(open, b"invalid report\n");
    let mut attempted = false;
    assert_eq!(
        cli::finish(2, Some("original".into()), |msg| {
            attempted = true;
            assert_eq!(msg, "original");
            cli::write_diagnostic(&mut Closed, msg)
        }),
        2
    );
    assert!(attempted);
    assert_eq!(cli::finish(0, None, |_| panic!("unexpected diagnostic")), 0);
}

#[cfg(not(verus_keep_ghost))]
#[test]
fn report_preserves_the_first_missing_model_in_sorted_member_order() {
    use serde_json::{Value, json};

    let base: Value = serde_json::from_str(include_str!("fixtures/filemap-view.json")).unwrap();
    let mut candidate = base.clone();
    candidate["filemap"]["files"] = json!([
        {"path":"z","owner":"p","cost":"first-registry-row"},
        {"path":"a","owner":"p","cost":"declared"},
        {"path":"a","owner":"p","cost":"first-missing"},
        {"path":"a","owner":"p","cost":"later-duplicate"}
    ]);
    candidate["filemap"]["cost_models"]["declared"] = json!({});
    let binding = json!({
        "base":"base","candidate":"candidate","candidate_tree":"tree",
        "registry_digest":"registry","context_digest":"context"
    });
    let impact = json!({
        "schema":"chrono-filemap-impact/v6","delta":[],"reached":["project:p"],
        "required_tests":[],"tests":[],"retired_tests":[]
    });
    let input = json!({"base":base,"candidate":candidate,"impact":impact,"binding":binding});
    let mut output = Vec::new();
    let error = chrono_judge_cost::report::write_report(
        &serde_json::to_vec(&input).unwrap()[..],
        &mut output,
    )
    .unwrap_err();
    assert_eq!(
        error,
        "E_COST_REFERENCE: missing cost model first-missing for file:a"
    );
    assert!(output.is_empty());
}
