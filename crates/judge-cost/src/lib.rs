//! Explicit declared costs for the already-selected FILEMAP impact. No cost inference.
use chrono_harness::wire::{Finding, Request, Response, Status};
use registry::CostFile;
pub use registry::CostRegistry;
mod registry;
use serde_json::{Map, Value, json};
use std::collections::BTreeSet;

mod verified_cost;

mod impact;
pub use impact::CostImpact;

pub const COST_SCHEMA: &str = "chrono-costs/v1";
fn escape(s: &str) -> String {
    s.replace('~', "~0").replace('/', "~1")
}
fn reference(r: &CostRegistry, id: &str, member: &str, pointer: String) -> Result<Value, String> {
    let model = r
        .filemap
        .cost_models
        .get(id)
        .ok_or_else(|| format!("E_COST_REFERENCE: missing cost model {id} for {member}"))?;
    let registry = &r.path;
    Ok(json!({"reference":id,"member":member,"value":model,
        "source":{"registry":registry,"pointer":format!("/cost_models/{}",escape(id))},
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
fn entry(r: &CostRegistry, node: &str) -> Result<Value, String> {
    let files = &r.filemap.files;
    if let Some(path) = node.strip_prefix("file:") {
        let Some((i, f)) = files.iter().enumerate().find(|(_, f)| f.path == path) else {
            return Ok(Value::Null);
        };
        return Ok(json!({"kind":"file","costs":[file_cost(r,i,f)?]}));
    }
    if let Some(id) = node.strip_prefix("test:") {
        if !r.nodes.contains(node) {
            return Ok(Value::Null);
        }
        let (i, row) = r
            .filemap
            .test_costs
            .iter()
            .enumerate()
            .find(|(_, row)| row.test == id)
            .ok_or_else(|| format!("E_COST_REFERENCE: missing test cost {node}"))?;
        return Ok(json!({"kind":"test","costs":[reference(r,&row.cost,node,
            format!("/test_costs/{i}/cost"))?]}));
    }
    let (kind, id) = if let Some(id) = node.strip_prefix("project:") {
        ("project", id)
    } else if let Some(id) = node.strip_prefix("script:") {
        ("script", id)
    } else {
        return Err(format!("E_COST_REFERENCE: unsupported cost subject {node}"));
    };
    // The candidate decoder retains obsolete definitions in the historical view.
    // Their declared member costs remain meaningful without executing old code.
    if !r.nodes.contains(node) {
        return Ok(Value::Null);
    }
    // Ownership is declared data. Keep each member and its source; costs are not additive by default.
    let mut members: Vec<_> = files
        .iter()
        .enumerate()
        .filter(|(_, f)| f.owner == id)
        .collect();
    members.sort_by_key(|(_, f)| f.path.as_str());
    let costs = members
        .into_iter()
        .map(|(i, f)| file_cost(r, i, f))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({"kind":kind,"costs":costs}))
}

/// Declaration-only report over FILEMAP's existing impact. No operations or resource measurement.
pub fn produce(
    base: &CostRegistry,
    candidate: &CostRegistry,
    impact: &CostImpact,
) -> Result<Value, String> {
    if impact.schema != "chrono-filemap-impact/v6" {
        return Err("E_IMPACT: unsupported cost input schema".into());
    }
    let mut subjects: BTreeSet<String> = impact
        .delta
        .iter()
        .map(|d| format!("file:{}", d.path))
        .collect();
    subjects.extend(
        impact
            .reached
            .iter()
            .filter(|n| {
                n.starts_with("file:") || n.starts_with("project:") || n.starts_with("script:")
            })
            .cloned(),
    );
    subjects.extend(impact.required_tests.iter().cloned());
    let mut before = Map::new();
    let mut after = Map::new();
    let mut unknown = vec![];
    let mut removed = vec![];
    for subject in subjects {
        let a = entry(base, &subject)?;
        let b = entry(candidate, &subject)?;
        verified_cost::record_subject_presence(
            !a.is_null(),
            !b.is_null(),
            subject.clone(),
            &mut removed,
        )
        .map_err(|error| format!("{}{}", error.message, error.subject))?;
        for (endpoint, value) in [("base", &a), ("candidate", &b)] {
            let Some(costs) = value["costs"].as_array() else {
                continue;
            };
            if costs.is_empty() {
                unknown.push(json!({"endpoint":endpoint,"node":subject,"reference":null,
                    "coordinates":verified_cost::missing_coordinate_names(true, true, true, true),
                    "reason":"no declared member cost references"}));
            }
            for cost in costs {
                let cpu_missing = cost["value"]["cpu_ms"].is_null();
                let wall_missing = cost["value"]["wall_ms"].is_null();
                let peak_rss_missing = cost["value"]["peak_rss_bytes"].is_null();
                let io_missing = cost["value"]["io_bytes"].is_null();
                let coordinates = verified_cost::missing_coordinate_names(
                    cpu_missing,
                    wall_missing,
                    peak_rss_missing,
                    io_missing,
                );
                if verified_cost::has_unknown_coordinate(
                    cpu_missing,
                    wall_missing,
                    peak_rss_missing,
                    io_missing,
                ) {
                    unknown.push(json!({"endpoint":endpoint,"node":subject,"member":cost["member"],
                        "reference":cost["reference"],"source":cost["source"],"coordinates":coordinates,
                        "reason":cost["value"]["basis"]}));
                }
            }
        }
        before.insert(subject.clone(), a);
        after.insert(subject, b);
    }
    Ok(
        json!({"schema":COST_SCHEMA,"declared_before":before,"declared_after":after,
        "affected_tests":impact.tests,"retired_tests":impact.retired_tests,"removed_nodes":removed,
        "unknown":unknown,"measured":null,
        "measurement_status":"not measured; declarations are estimates, not process measurements",
        "aggregation":"none; member references are retained without summing resource peaks or parallel wall time"}),
    )
}

pub fn judge(req: &Request) -> Response {
    let mut response = req.response(Status::Pass);
    let result = evaluate(req, &mut response);
    match result {
        Ok(costs) => {
            if !costs["unknown"].as_array().unwrap().is_empty() {
                chrono_harness::wire::append_finding(
                    &mut response.status,
                    &mut response.findings,
                    Status::Warn,
                    Finding {
                        code: "W_COST_UNKNOWN".into(),
                        level: "warning".into(),
                        message:
                            "Affected declared costs contain unknown coordinates; see costs.unknown"
                                .into(),
                        delta_refs: vec!["/impact".into()],
                        causes: vec!["/outputs/costs/unknown".into()],
                    },
                );
            }
            response.outputs.insert("costs".into(), costs);
        }
        Err(message) => {
            chrono_harness::wire::append_finding(
                &mut response.status,
                &mut response.findings,
                Status::Error,
                Finding {
                    code: message
                        .split(':')
                        .next()
                        .filter(|s| s.starts_with("E_"))
                        .unwrap_or("E_INPUT")
                        .into(),
                    level: "error".into(),
                    message,
                    delta_refs: vec!["/request".into()],
                    causes: vec![],
                },
            );
        }
    }
    response
}
fn evaluate(req: &Request, response: &mut Response) -> Result<Value, String> {
    req.validate()?;
    let config = chrono_harness::load_selected_config(&req.candidate.root, &req.config_path)?;
    let protocol = &config["protocol"];
    let environment = &req.observations["environment"]["effective"];
    let run = |command: &chrono_harness::CommandSpec, input: &[u8]| {
        let result = chrono_harness::run_process(&req.candidate.root, command, input)?;
        Ok((result.exit_code, result.stdout_bytes, result.stderr_bytes))
    };
    let reply = registry::query(&req.canonical()?, protocol, environment, run)?;
    if reply.request_id != req.request_id {
        return Err("E_PROTOCOL: registration query identity".into());
    }
    if let Some(facts) = reply.git_facts {
        response.outputs.insert("git_facts".into(), facts);
    }
    let (base, candidate) = reply.views.into_result()?;
    let impact = impact::decode(&req.impact, protocol, environment, run)?;
    let sources: Vec<_> = req
        .prior_results
        .iter()
        .filter_map(|r| r.outputs.get("impact"))
        .collect();
    if sources.is_empty() || sources.iter().any(|v| **v != req.impact) || impact.delta != req.delta
    {
        return Err("E_IMPACT: missing or conflicting bound FILEMAP output".into());
    }
    let mut costs = produce(&base, &candidate, &impact)?;
    costs["binding"] = json!({"base":req.base.commit,"candidate":req.candidate.commit,
        "candidate_tree":req.candidate.tree,"registry_digest":req.registries.digest,"context_digest":req.context.sha256});
    Ok(costs)
}
