//! Explicit declared costs for the already-selected FILEMAP impact. No cost inference.
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

/// Read the four model fields in the order consumed by the published report.
pub fn model_fields<F>(missing: F) -> (observed: (bool, bool, bool, bool))
    where F: Fn(&'static str) -> bool,
    requires
        missing.requires(("cpu_ms",)),
        missing.requires(("wall_ms",)),
        missing.requires(("peak_rss_bytes",)),
        missing.requires(("io_bytes",)),
    ensures
        missing.ensures(("cpu_ms",), observed.0),
        missing.ensures(("wall_ms",), observed.1),
        missing.ensures(("peak_rss_bytes",), observed.2),
        missing.ensures(("io_bytes",), observed.3),
{
    (missing("cpu_ms"), missing("wall_ms"), missing("peak_rss_bytes"), missing("io_bytes"))
}

}

#[cfg(not(verus_keep_ghost))]
pub use registry::CostRegistry;
#[cfg(not(verus_keep_ghost))]
use verified_cost::CostKind;
#[cfg(not(verus_keep_ghost))]
mod registry;
#[cfg(not(verus_keep_ghost))]
pub mod report;
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use std::collections::BTreeMap;
#[cfg(not(verus_keep_ghost))]
use verified_cost as policy;
#[cfg(not(verus_keep_ghost))]
pub use verified_cost::{
    Arg, COST_SCHEMA, ChangedFile, delegation_error, direct_report, exit_report, invocation,
};

#[cfg(not(verus_keep_ghost))]
mod verified_cost;

/// The public FILEMAP impact-summary fields used by the declared-cost report.
#[cfg(not(verus_keep_ghost))]
#[derive(serde::Deserialize)]
pub struct FilemapImpact<D> {
    pub schema: String,
    pub delta: Vec<D>,
    pub reached: Vec<String>,
    pub required_tests: Vec<String>,
    pub tests: Vec<String>,
    pub retired_tests: Vec<String>,
}

#[cfg(not(verus_keep_ghost))]
type DeclaredCost<'a> = policy::DeclaredCost<policy::ModelReference<'a, Value>>;

#[cfg(not(verus_keep_ghost))]
fn entry<'a>(
    r: &'a CostRegistry,
    node: &str,
    kind: CostKind,
    id: &str,
) -> Result<Option<DeclaredCost<'a>>, String> {
    let files = &r.filemap.files;
    let tests = &r.filemap.test_costs;
    policy::resolve_declaration(
        files,
        tests,
        policy::declaration(files, tests, kind, id, r.nodes.contains(node)),
        node,
        &r.path,
        |key| r.filemap.cost_models.get(key),
        |chars| chars.into_iter().collect(),
        |mut keys| {
            keys.sort_unstable();
            keys
        },
    )
}

/// Declaration-only report over FILEMAP's existing impact. No operations or resource measurement.
#[cfg(not(verus_keep_ghost))]
pub fn produce<D: ChangedFile>(
    base: &CostRegistry,
    candidate: &CostRegistry,
    impact: &FilemapImpact<D>,
) -> Result<Value, String> {
    let entries = collect_costs(base, candidate, impact)?;
    serde_json::to_value(document(&entries, impact)).map_err(|e| e.to_string())
}
#[cfg(not(verus_keep_ghost))]
type CostEntries<'a> = policy::Entries<DeclaredCost<'a>, Value>;
#[cfg(not(verus_keep_ghost))]
type Declared<'a> = BTreeMap<String, Option<DeclaredCost<'a>>>;
#[cfg(not(verus_keep_ghost))]
fn document<'a, 'r, D>(
    entries: &'a CostEntries<'r>,
    impact: &'a FilemapImpact<D>,
) -> policy::CostDocument<'a, Declared<'r>, Value> {
    policy::document(
        &entries.before,
        &entries.after,
        &impact.tests,
        &impact.retired_tests,
        &entries.removed,
        &entries.unknown,
    )
}

#[cfg(not(verus_keep_ghost))]
fn collect_costs<'a, D: ChangedFile>(
    base: &'a CostRegistry,
    candidate: &'a CostRegistry,
    impact: &FilemapImpact<D>,
) -> Result<CostEntries<'a>, String> {
    let subjects = verified_cost::cost_subjects(
        &impact.schema,
        &impact.delta,
        &impact.reached,
        &impact.required_tests,
    )?;
    let keys: Vec<_> = subjects.into_iter().collect();
    policy::collect(
        &keys,
        |subject| {
            let (kind, id) = policy::require_subject(subject)?;
            let (a, b) = policy::endpoints(base, candidate, |endpoint| {
                entry(endpoint, subject, kind, id)
            })?;
            let unknown = policy::ordered_sides(&a, &b, |endpoint, value| {
                policy::unknown_entries(
                    value.as_ref(),
                    |cost| {
                        policy::model_unknown(
                            endpoint,
                            subject,
                            cost,
                            |model, key| model[key].is_null(),
                            |model, key| &model[key],
                        )
                        .map(|entry| json!(entry))
                    },
                    || json!(policy::no_members(endpoint, subject)),
                )
            });
            Ok(policy::SubjectRow {
                before: a,
                after: b,
                unknown,
            })
        },
        policy::presence_message,
    )
}
