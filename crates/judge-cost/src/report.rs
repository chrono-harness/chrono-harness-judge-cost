//! Product input for a declared-cost report, after both producers have decoded their documents.
use crate::verified_cost::Changed;
use crate::{CostRegistry, FilemapImpact, produce};
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
        .take(64 * 1024 * 1024 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > 64 * 1024 * 1024 {
        return Err("E_INPUT: report input exceeds 64 MiB".into());
    }
    let query: Input = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    let mut costs = produce(&query.base, &query.candidate, &query.impact)?;
    costs["binding"] = serde_json::to_value(query.binding).map_err(|error| error.to_string())?;
    let unknown = costs["unknown"]
        .as_array()
        .ok_or("invalid cost unknown coordinates")?;
    let decision = crate::verified_cost::report_decision(unknown);
    let report =
        json!({"status":decision.status,"findings":decision.findings,"outputs":{"costs":costs}});
    serde_json::to_writer(&mut output, &report).map_err(|e| e.to_string())?;
    output.flush().map_err(|e| e.to_string())
}
