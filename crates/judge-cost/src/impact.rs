use chrono_harness::{CommandSpec, wire::Delta};
use serde::Deserialize;
use serde_json::Value;
/// The public FILEMAP impact-summary fields used by the declared-cost report.
#[derive(Deserialize)]
pub struct CostImpact {
    pub schema: String,
    pub delta: Vec<Delta>,
    pub reached: Vec<String>,
    pub required_tests: Vec<String>,
    pub tests: Vec<String>,
    pub retired_tests: Vec<String>,
}

pub(crate) fn decode(
    input: &Value,
    protocol: &Value,
    environment: &Value,
    run: impl FnOnce(&CommandSpec, &[u8]) -> Result<(i32, Vec<u8>, Vec<u8>), String>,
) -> Result<CostImpact, String> {
    let spec = CommandSpec {
        program: "chrono-judge-filemap".into(),
        args: vec!["impact-summary".into()],
        env: serde_json::from_value(environment.clone()).map_err(|e| e.to_string())?,
        timeout_seconds: protocol["timeout_seconds"]
            .as_u64()
            .ok_or("invalid protocol timeout")?,
        output_limit_bytes: protocol["stdout_limit_bytes"]
            .as_u64()
            .and_then(|n| usize::try_from(n).ok())
            .ok_or("invalid protocol output bound")?,
    };
    let (code, stdout, stderr) = run(
        &spec,
        &serde_json::to_vec(input).map_err(|e| e.to_string())?,
    )
    .map_err(|e| format!("E_IMPACT: {e}"))?;
    if code != 0 {
        let text = String::from_utf8(stderr).map_err(|e| format!("E_IMPACT: {e}"))?;
        let text = text.strip_suffix('\n').unwrap_or(&text);
        return Err(if text.is_empty() {
            format!("E_IMPACT: FILEMAP impact-summary exited with {}", code)
        } else {
            format!("E_IMPACT: {text}")
        });
    }
    serde_json::from_slice(&stdout).map_err(|e| format!("E_IMPACT: {e}"))
}
