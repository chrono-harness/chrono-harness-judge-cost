//! Independent boundary expectations for the declared-cost Verus policy.
#![allow(unexpected_cfgs)]
#[path = "../../judge-cost/src/verified_cost.rs"]
mod policy;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::vpanic as panic;

verus! {

fn expect(actual: bool)
    requires actual,
{
    if !actual { panic!(); }
}

fn expect_name(actual: &str, expected: &str)
    requires actual@ == expected@,
{
    let equal = <&str>::exec_eq(actual, expected);
    expect(equal);
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
fn no_missing_coordinate_is_known() {
    let known = policy::has_unknown_coordinate(false, false, false, false);
    expect(!known);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn each_coordinate_independently_makes_the_declaration_unknown() {
    let cpu = policy::has_unknown_coordinate(true, false, false, false);
    let wall = policy::has_unknown_coordinate(false, true, false, false);
    let peak_rss = policy::has_unknown_coordinate(false, false, true, false);
    let io = policy::has_unknown_coordinate(false, false, false, true);
    expect(cpu && wall && peak_rss && io);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn combinations_are_monotone_in_missing_coordinates() {
    let none = policy::has_unknown_coordinate(false, false, false, false);
    let cpu_wall = policy::has_unknown_coordinate(true, true, false, false);
    let peak_io = policy::has_unknown_coordinate(false, false, true, true);
    let all = policy::has_unknown_coordinate(true, true, true, true);
    expect(!none && cpu_wall && peak_io && all);
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
