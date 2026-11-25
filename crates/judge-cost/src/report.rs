//! Product input for a declared-cost report, after both producers have decoded their documents.
use crate::verified_cost::{Changed, MAX_REPORT_BYTES, check_report_size, report_decision};
use crate::{CostRegistry, FilemapImpact, collect_costs};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::fs::File;
use std::io::{BufWriter, Read, Write};
use std::os::fd::AsFd;

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

/// Use a native file writer so a read-only destination reports its OS write error.
pub fn write_report_to_fd(input: impl Read, output: impl AsFd) -> Result<(), String> {
    let fd = output
        .as_fd()
        .try_clone_to_owned()
        .map_err(|error| error.to_string())?;
    write_report(input, BufWriter::new(File::from(fd)))
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
