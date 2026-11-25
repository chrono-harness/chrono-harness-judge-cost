//! Product input for a declared-cost report, after both producers have decoded their documents.
use crate::verified_cost::{Changed, MAX_REPORT_BYTES, check_report_size, report_decision};
use crate::{CostRegistry, FilemapImpact, collect_costs};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::io::{Read, Write};

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Binding {
    base: String,
    candidate: String,
    candidate_tree: String,
    registry_digest: String,
    context_digest: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    base: CostRegistry,
    candidate: CostRegistry,
    impact: FilemapImpact<Changed>,
    binding: Binding,
}

pub fn write_report(input: impl Read, mut output: impl Write) -> Result<(), String> {
    let mut bytes = Vec::new();
    input
        .take(MAX_REPORT_BYTES as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    check_report_size(bytes.len())?;
    let query: Input = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    let entries = collect_costs(&query.base, &query.candidate, &query.impact)?;
    let decision = report_decision(&entries.unknown);
    let mut costs = entries.document(&query.impact);
    costs["binding"] = serde_json::to_value(query.binding).map_err(|error| error.to_string())?;
    let report =
        json!({"status":decision.status,"findings":decision.findings,"outputs":{"costs":costs}});
    serde_json::to_writer(&mut output, &report).map_err(|e| e.to_string())?;
    output.flush().map_err(|e| e.to_string())
}
