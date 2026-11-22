use chrono_harness::CommandSpec;
use serde::Deserialize;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Deserialize)]
pub struct CostRegistry {
    pub(crate) path: String,
    pub(crate) filemap: CostFilemap,
    pub(crate) nodes: BTreeSet<String>,
}

#[derive(Debug, Deserialize)]
pub(crate) struct CostFilemap {
    pub files: Vec<CostFile>,
    pub cost_models: BTreeMap<String, Value>,
    pub test_costs: Vec<TestCost>,
}

#[derive(Debug, Deserialize)]
pub(crate) struct CostFile {
    pub path: String,
    pub owner: String,
    pub cost: String,
}
#[derive(Debug, Deserialize)]
pub(crate) struct TestCost {
    pub test: String,
    pub cost: String,
}

#[derive(Deserialize)]
pub(crate) struct Reply {
    pub request_id: String,
    pub git_facts: Option<Value>,
    #[serde(flatten)]
    pub views: ViewResult,
}
#[derive(Deserialize)]
#[serde(untagged)]
pub(crate) enum ViewResult {
    Error {
        error: String,
    },
    Ready {
        base: CostRegistry,
        candidate: CostRegistry,
    },
}
impl ViewResult {
    pub fn into_result(self) -> Result<(CostRegistry, CostRegistry), String> {
        match self {
            Self::Ready { base, candidate } => Ok((base, candidate)),
            Self::Error { error } => Err(error),
        }
    }
}

pub(crate) fn query(
    request: &[u8],
    protocol: &Value,
    environment: &Value,
    invoke: impl FnOnce(&CommandSpec, &[u8]) -> Result<(i32, Vec<u8>, Vec<u8>), String>,
) -> Result<Reply, String> {
    let cmd = CommandSpec {
        program: "chrono-judge-registration".into(),
        args: vec!["filemap-views".into()],
        env: serde_json::from_value(environment.clone()).map_err(|e| e.to_string())?,
        timeout_seconds: protocol["timeout_seconds"]
            .as_u64()
            .ok_or("invalid registration timeout")?,
        output_limit_bytes: protocol["stdout_limit_bytes"]
            .as_u64()
            .and_then(|n| usize::try_from(n).ok())
            .ok_or("invalid registration output bound")?,
    };
    let (code, output, diagnostic) = invoke(&cmd, request)?;
    if code != 0 {
        let error = std::str::from_utf8(&diagnostic).map_err(|e| e.to_string())?;
        return Err(if error.is_empty() {
            format!("registration filemap-views exited with {code}")
        } else {
            error.strip_suffix('\n').unwrap_or(error).into()
        });
    }
    serde_json::from_slice(&output).map_err(|e| format!("invalid registration filemap views: {e}"))
}
