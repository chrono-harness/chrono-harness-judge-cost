#[path = "../../judge-cost/src/query.rs"]
mod query;
#[path = "../../judge-cost/src/registration_query.rs"]
mod registration_query;
#[allow(dead_code)]
#[path = "../../judge-cost/src/registry.rs"]
mod registry;
use serde_json::{Value, json};

#[test]
fn forwards_sealed_input_and_recovers_views_or_original_git_failure() {
    let raw = br#"{"request_id":"sealed"}"#;
    let protocol = json!({"timeout_seconds":5,"stdout_limit_bytes":65536});
    let env = json!({"PATH":"/installed"});
    let view: Value = serde_json::from_str(include_str!("fixtures/filemap-view.json")).unwrap();
    let result = registration_query::query(raw, &protocol, &env, |cmd, input| {
        assert_eq!(cmd.argv, ["chrono-judge-registration", "filemap-views"]);
        assert_eq!(cmd.env["PATH"], "/installed");
        assert_eq!((cmd.timeout_seconds, cmd.output_limit_bytes), (5, 65536));
        assert_eq!(input, raw);
        Ok((
            0,
            serde_json::to_vec(&json!({"request_id":"sealed","base":view,"candidate":view}))
                .unwrap(),
            vec![],
        ))
    })
    .unwrap();
    assert_eq!(result.request_id, "sealed");
    assert!(result.git_facts.is_none());
    let (base, current) = result.views.into_result().unwrap();
    assert_eq!(base.path, ".chrono-harness/FILEMAP.json");
    assert!(current.nodes.contains("test:t"));
    let original = json!({"processes":[{"exit_code":9}]});
    let failed = json!({
        "request_id": "sealed",
        "error": "registration view binding mismatch",
        "git_facts": original,
    });
    let rejected = registration_query::query(raw, &protocol, &env, |_, _| {
        Ok((0, serde_json::to_vec(&failed).unwrap(), vec![]))
    })
    .unwrap();
    assert_eq!(rejected.git_facts, Some(original));
    assert_eq!(
        rejected.views.into_result().unwrap_err(),
        "registration view binding mismatch"
    );
    for (result, expected) in [
        (Ok((2, vec![], b"bad JSON\n".to_vec())), "bad JSON"),
        (Err("timeout".into()), "timeout"),
        (
            Ok((0, b"{}".to_vec(), vec![])),
            "invalid registration filemap views:",
        ),
    ] {
        assert!(
            registration_query::query(raw, &protocol, &env, |_, _| result)
                .err()
                .unwrap()
                .starts_with(expected)
        );
    }
}
