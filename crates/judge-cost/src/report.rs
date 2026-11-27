//! Input admission and serialization for the declared-cost report.
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::{MAX_REPORT_BYTES, check_report_size};
#[cfg(not(verus_keep_ghost))]
use crate::verified_cost::{MAX_REPORT_BYTES, check_report_size};

verus! {
/// Read one extra byte so exactly 64 MiB is distinguishable from truncated input.
pub fn read_report_bytes<R>(read: R) -> (out: Result<Vec<u8>, String>)
    where R: FnOnce(u64) -> Result<Vec<u8>, String>,
    requires read.requires((67108865u64,)),
    ensures
        match out {
            Ok(bytes) => bytes.len() <= 67108864 && read.ensures((67108865u64,), Ok(bytes)),
            Err(error) => read.ensures((67108865u64,), Err(error))
                || (error@ == "E_INPUT: report input exceeds 64 MiB"@ &&
                    exists|bytes: Vec<u8>| #[trigger] read.ensures((67108865u64,), Ok(bytes))
                        && bytes.len() > 67108864),
        },
{
    let bytes = match read(MAX_REPORT_BYTES as u64 + 1) {
        Ok(bytes) => bytes,
        Err(error) => return Err(error),
    };
    match check_report_size(bytes.len()) {
        Ok(()) => Ok(bytes),
        Err(message) => Err(message.to_string()),
    }
}
}

#[cfg(not(verus_keep_ghost))]
use crate::verified_cost::Changed;
#[cfg(not(verus_keep_ghost))]
use crate::{CostRegistry, FilemapImpact, collect_costs};
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

#[cfg(not(verus_keep_ghost))]
use std::fs::File;
#[cfg(not(verus_keep_ghost))]
use std::io::{BufWriter, Read, Write};
#[cfg(not(verus_keep_ghost))]
use std::os::fd::AsFd;

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Binding {
    base: String,
    candidate: String,
    candidate_tree: String,
    registry_digest: String,
    context_digest: String,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    base: CostRegistry,
    candidate: CostRegistry,
    impact: FilemapImpact<Changed>,
    binding: Binding,
}

/// Use a native file writer so a read-only destination reports its OS write error.
#[cfg(not(verus_keep_ghost))]
pub fn write_report_to_fd(input: impl Read, output: impl AsFd) -> Result<(), String> {
    let fd = output
        .as_fd()
        .try_clone_to_owned()
        .map_err(|error| error.to_string())?;
    write_report(input, BufWriter::new(File::from(fd)))
}

#[cfg(not(verus_keep_ghost))]
pub fn write_report(input: impl Read, mut output: impl Write) -> Result<(), String> {
    let bytes = read_report_bytes(|limit| {
        let mut bytes = Vec::new();
        input
            .take(limit)
            .read_to_end(&mut bytes)
            .map_err(|e| e.to_string())?;
        Ok(bytes)
    })?;
    let query: Input = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    let entries = collect_costs(&query.base, &query.candidate, &query.impact)?;
    let report =
        crate::verified_cost::report(crate::document(&entries, &query.impact), query.binding);
    // Value preserves the published JSON object's canonical key order.
    let value = serde_json::to_value(report).map_err(|e| e.to_string())?;
    serde_json::to_writer(&mut output, &value).map_err(|e| e.to_string())?;
    output.flush().map_err(|e| e.to_string())
}
