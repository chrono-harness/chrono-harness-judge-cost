#[path = "../../judge-cost/src/impact.rs"]
mod impact;
#[path = "../../judge-cost/src/query.rs"]
mod query;

use chrono_judge_cost::FilemapImpact;
use serde_json::{Value, json};

#[test]
fn the_filemap_command_distinguishes_input_rejections_from_absent_or_broken_output() {
    let input = json!({"schema":"value passed through","closure":{}});
    let protocol = json!({"timeout_seconds":3,"stdout_limit_bytes":800});
    let env = json!({"PATH":"/tools"});
    let summary = impact::decode::<FilemapImpact<Value>>(&input, &protocol, &env, |spec, stdin| {
        assert_eq!(spec.argv, ["chrono-judge-filemap", "impact-summary"]);
        assert_eq!(spec.env["PATH"], "/tools");
        assert_eq!((spec.timeout_seconds, spec.output_limit_bytes), (3,800));
        assert_eq!(serde_json::from_slice::<Value>(stdin).unwrap(), input);
        let out = json!({"schema":"future","delta":[],"reached":["file:a"],"required_tests":["test:t"],
                         "tests":["t"],"retired_tests":["old"]});
        Ok((0,serde_json::to_vec(&out).unwrap(), Vec::new()))
    }).unwrap();
    assert_eq!(summary.schema, "future");
    assert!(summary.delta.is_empty());
    assert_eq!(summary.reached, ["file:a"]);
    assert_eq!(summary.required_tests, ["test:t"]);
    assert_eq!(summary.tests, ["t"]);
    assert_eq!(summary.retired_tests, ["old"]);
    for (result, error) in [
        (
            Ok((2, Vec::new(), b"unknown edge kind\n".to_vec())),
            "E_IMPACT: unknown edge kind",
        ),
        (
            Err("process timed out".into()),
            "E_IMPACT: process timed out",
        ),
        (
            Ok((0, b"{}".to_vec(), Vec::new())),
            "E_IMPACT: missing field",
        ),
    ] {
        let diagnostics =
            impact::decode::<FilemapImpact<Value>>(&input, &protocol, &env, |_, _| result)
                .err()
                .unwrap();
        assert!(diagnostics.starts_with(error), "{diagnostics}");
    }
}
