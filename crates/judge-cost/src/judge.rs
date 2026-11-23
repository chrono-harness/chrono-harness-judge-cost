use super::{ChangedFile, FilemapImpact, impact, produce, query, registration_query};
use chrono_harness::wire::{Delta, Finding, Request, Response, Status};
use serde_json::{Value, json};

pub type CostImpact = FilemapImpact<Delta>;

impl ChangedFile for Delta {
    fn path(&self) -> &str {
        &self.path
    }
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
    let run = |query: query::Command, input: &[u8]| {
        let [program, operation] = query.argv;
        let command = chrono_harness::CommandSpec {
            program: program.into(),
            args: vec![operation.into()],
            env: query.env,
            timeout_seconds: query.timeout_seconds,
            output_limit_bytes: query.output_limit_bytes,
        };
        let result = chrono_harness::run_process(&req.candidate.root, &command, input)?;
        Ok((result.exit_code, result.stdout_bytes, result.stderr_bytes))
    };
    let reply = registration_query::query(&req.canonical()?, protocol, environment, run)?;
    if reply.request_id != req.request_id {
        return Err("E_PROTOCOL: registration query identity".into());
    }
    if let Some(facts) = reply.git_facts {
        response.outputs.insert("git_facts".into(), facts);
    }
    let (base, candidate) = reply.views.into_result()?;
    let impact: CostImpact = impact::decode(&req.impact, protocol, environment, run)?;
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
