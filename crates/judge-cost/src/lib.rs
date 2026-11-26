//! Explicit declared costs for the already-selected FILEMAP impact. No cost inference.
pub use registry::CostRegistry;
use verified_cost::{CostFile, CostKind};
mod registry;
pub mod report;
use serde_json::{Map, Value, json};
pub use verified_cost::ChangedFile;

mod verified_cost;

/// The public FILEMAP impact-summary fields used by the declared-cost report.
#[derive(serde::Deserialize)]
pub struct FilemapImpact<D> {
    pub schema: String,
    pub delta: Vec<D>,
    pub reached: Vec<String>,
    pub required_tests: Vec<String>,
    pub tests: Vec<String>,
    pub retired_tests: Vec<String>,
}

pub const COST_SCHEMA: &str = "chrono-costs/v1";
fn model_pointer(id: &str) -> String {
    let mut pointer = String::from("/cost_models/");
    pointer.extend(id.chars().flat_map(verified_cost::pointer_token).flatten());
    pointer
}
fn reference(r: &CostRegistry, id: &str, member: &str, pointer: String) -> Result<Value, String> {
    let model = r
        .filemap
        .cost_models
        .get(id)
        .ok_or_else(|| format!("E_COST_REFERENCE: missing cost model {id} for {member}"))?;
    let registry = &r.path;
    Ok(json!({"reference":id,"member":member,"value":model,
        "source":{"registry":registry,"pointer":model_pointer(id)},
        "declaration":{"registry":registry,"pointer":pointer}}))
}
fn file_cost(r: &CostRegistry, index: usize, file: &CostFile) -> Result<Value, String> {
    reference(
        r,
        &file.cost,
        &format!("file:{}", file.path),
        format!("/files/{index}/cost"),
    )
}
fn entry(r: &CostRegistry, node: &str, kind: CostKind, id: &str) -> Result<Value, String> {
    let files = &r.filemap.files;
    let kind = match kind {
        CostKind::File => {
            let Some(i) = verified_cost::first_declaration(files, id) else {
                return Ok(Value::Null);
            };
            return Ok(json!({"kind":"file","costs":[file_cost(r,i,&files[i])?]}));
        }
        CostKind::Test => {
            if !r.nodes.contains(node) {
                return Ok(Value::Null);
            }
            let test_costs = &r.filemap.test_costs;
            let i = verified_cost::first_declaration(test_costs, id)
                .ok_or_else(|| format!("E_COST_REFERENCE: missing test cost {node}"))?;
            let row = &test_costs[i];
            return Ok(json!({"kind":"test","costs":[reference(r,&row.cost,node,
                format!("/test_costs/{i}/cost"))?]}));
        }
        CostKind::Project => "project",
        CostKind::Script => "script",
    };
    // The candidate decoder retains obsolete definitions in the historical view.
    // Their declared member costs remain meaningful without executing old code.
    if !r.nodes.contains(node) {
        return Ok(Value::Null);
    }
    // Ownership is declared data. Keep each member and its source; costs are not additive by default.
    let mut members = verified_cost::owner_members(files, id);
    members.sort_by_key(|&i| files[i].path.as_str());
    let costs = members
        .into_iter()
        .map(|i| file_cost(r, i, &files[i]))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({"kind":kind,"costs":costs}))
}

/// Declaration-only report over FILEMAP's existing impact. No operations or resource measurement.
pub fn produce<D: ChangedFile>(
    base: &CostRegistry,
    candidate: &CostRegistry,
    impact: &FilemapImpact<D>,
) -> Result<Value, String> {
    Ok(collect_costs(base, candidate, impact)?.document(impact))
}

struct CostEntries {
    before: Map<String, Value>,
    after: Map<String, Value>,
    unknown: Vec<Value>,
    removed: Vec<String>,
}

impl CostEntries {
    fn document<D>(&self, impact: &FilemapImpact<D>) -> Value {
        json!({"schema":COST_SCHEMA,"declared_before":self.before,"declared_after":self.after,
            "affected_tests":impact.tests,"retired_tests":impact.retired_tests,"removed_nodes":self.removed,
            "unknown":self.unknown,"measured":null,
            "measurement_status":"not measured; declarations are estimates, not process measurements",
            "aggregation":"none; member references are retained without summing resource peaks or parallel wall time"})
    }
}

fn collect_costs<D: ChangedFile>(
    base: &CostRegistry,
    candidate: &CostRegistry,
    impact: &FilemapImpact<D>,
) -> Result<CostEntries, String> {
    let subjects = verified_cost::cost_subjects(
        &impact.schema,
        &impact.delta,
        &impact.reached,
        &impact.required_tests,
    )?;
    let mut before = Map::new();
    let mut after = Map::new();
    let mut unknown = vec![];
    let mut removed = vec![];
    for subject in subjects {
        let (kind, id) = verified_cost::cost_subject(&subject)
            .ok_or_else(|| format!("E_COST_REFERENCE: unsupported cost subject {subject}"))?;
        let a = entry(base, &subject, kind, id)?;
        let b = entry(candidate, &subject, kind, id)?;
        verified_cost::record_subject_presence(
            !a.is_null(),
            !b.is_null(),
            subject.clone(),
            &mut removed,
        )
        .map_err(|error| format!("{}{}", error.message, error.subject))?;
        for (endpoint, value) in [
            (verified_cost::Endpoint::Base, &a),
            (verified_cost::Endpoint::Candidate, &b),
        ] {
            let Some(costs) = value["costs"].as_array() else {
                continue;
            };
            if costs.is_empty() {
                unknown.push(json!(verified_cost::no_members(endpoint, &subject)));
            }
            for cost in costs {
                let model = &cost["value"];
                if let Some(entry) = verified_cost::unknown_member(
                    endpoint,
                    &subject,
                    &cost["member"],
                    &cost["reference"],
                    &cost["source"],
                    &model["basis"],
                    model["cpu_ms"].is_null(),
                    model["wall_ms"].is_null(),
                    model["peak_rss_bytes"].is_null(),
                    model["io_bytes"].is_null(),
                ) {
                    unknown.push(json!(entry));
                }
            }
        }
        before.insert(subject.clone(), a);
        after.insert(subject, b);
    }
    Ok(CostEntries {
        before,
        after,
        unknown,
        removed,
    })
}
