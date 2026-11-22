use chrono_judge_cost::{CostImpact, produce};
use serde_json::{Value, json};

const FM: &str = ".chrono-harness/FILEMAP.json";
fn values() -> Value {
    serde_json::from_str(include_str!("fixtures/filemap-view.json")).unwrap()
}

// The FILEMAP v0.1.0-alpha.1 impact-summary output for these endpoint fixtures.
fn report(a: &Value, b: &Value, scenario: &str) -> Result<Value, String> {
    let samples: std::collections::BTreeMap<String, CostImpact> =
        serde_json::from_str(include_str!("fixtures/impact-summaries.json")).unwrap();
    produce(
        &serde_json::from_value(a.clone()).unwrap(),
        &serde_json::from_value(b.clone()).unwrap(),
        &samples[scenario],
    )
}
fn known() -> Value {
    let mut v = values();
    let fm = v.get_mut("filemap").unwrap();
    fm["cost_models"]["known"] = json!({"cpu_ms":10,"wall_ms":20,"peak_rss_bytes":30,"io_bytes":40,"basis":"declared estimate from fixture sample"});
    for f in fm["files"].as_array_mut().unwrap() {
        f["cost"] = "known".into();
        if f["path"] == "src.bin" || f["path"].as_str().unwrap().starts_with("p/") {
            f["owner"] = "p".into();
        }
        if f["path"].as_str().unwrap().starts_with("t/") {
            f["owner"] = "t".into();
        }
    }
    fm["test_costs"][0]["cost"] = "known".into();
    v
}

#[test]
fn distinct_endpoints_preserve_four_coordinates_basis_and_sources() {
    let a = known();
    let mut b = a.clone();
    b.get_mut("filemap").unwrap()["cost_models"]["known"]["cpu_ms"] = 12.into();
    let r = report(&a, &b, "changed_model").unwrap();
    assert_eq!(r["schema"], "chrono-costs/v1");
    for (endpoint, cpu) in [("declared_before", 10), ("declared_after", 12)] {
        let file = &r[endpoint]["file:src.bin"]["costs"][0];
        assert_eq!(file["reference"], "known");
        assert_eq!(file["value"]["cpu_ms"], cpu);
        assert_eq!(file["value"]["wall_ms"], 20);
        assert_eq!(file["value"]["peak_rss_bytes"], 30);
        assert_eq!(file["value"]["io_bytes"], 40);
        assert_eq!(file["source"]["registry"], FM);
        assert_eq!(file["source"]["pointer"], "/cost_models/known");
        assert_eq!(
            file["value"]["basis"],
            "declared estimate from fixture sample"
        );
        let members = r[endpoint]["project:p"]["costs"].as_array().unwrap();
        assert_eq!(members.len(), 3);
        assert!(members.iter().any(|m| m["member"] == "file:src.bin"));
    }
    assert_eq!(r["affected_tests"], json!(["test:t"]));
    assert!(r["unknown"].as_array().unwrap().is_empty());
    assert!(r["measured"].is_null());
    assert!(
        r.get("total").is_none(),
        "independent resources must not be summed"
    );
}

#[test]
fn unknown_coordinates_remain_null_and_known_coordinates_survive() {
    let mut a = known();
    a.get_mut("filemap").unwrap()["cost_models"]["known"]["cpu_ms"] = Value::Null;
    let r = report(&a, &a, "source_change").unwrap();
    let cost = &r["declared_after"]["test:t"]["costs"][0]["value"];
    assert!(cost["cpu_ms"].is_null());
    assert_eq!(cost["wall_ms"], 20);
    assert!(
        r["unknown"]
            .as_array()
            .unwrap()
            .iter()
            .any(|u| u["node"] == "test:t"
                && u["endpoint"] == "candidate"
                && u["coordinates"] == json!(["cpu_ms"]))
    );
}

#[test]
fn deleted_file_and_required_removed_test_keep_old_cost_references() {
    let a = known();
    let mut b = a.clone();
    b.get_mut("filemap").unwrap()["files"]
        .as_array_mut()
        .unwrap()
        .retain(|f| f["path"] != "src.bin");
    b.get_mut("filemap").unwrap()["test_costs"] = json!([]);
    b["nodes"]
        .as_array_mut()
        .unwrap()
        .retain(|node| node != "test:t" && node != "project:t");
    let r = report(&a, &b, "retired_test").unwrap();
    assert_eq!(
        r["declared_before"]["file:src.bin"]["costs"][0]["reference"],
        "known"
    );
    assert!(r["declared_after"]["file:src.bin"].is_null());
    assert_eq!(r["retired_tests"], json!(["test:t"]));
    assert_eq!(
        r["declared_before"]["test:t"]["costs"][0]["value"]["io_bytes"],
        40
    );
    assert!(r["declared_after"]["test:t"].is_null());
}

#[test]
fn disconnected_docs_and_empty_delta_do_not_add_other_nodes() {
    let a = known();
    let r = report(&a, &a, "docs_only").unwrap();
    assert_eq!(
        r["declared_after"]
            .as_object()
            .unwrap()
            .keys()
            .collect::<Vec<_>>(),
        ["file:doc.txt"]
    );
    assert_eq!(r["affected_tests"], json!([]));
    let r = report(&a, &a, "empty").unwrap();
    assert_eq!(r["declared_before"], json!({}));
    assert_eq!(r["declared_after"], json!({}));
}

#[test]
fn shared_test_has_one_identity_and_equal_cost_models_do_not_merge_members() {
    let a = known();
    let r = report(&a, &a, "shared_test").unwrap();
    assert_eq!(r["affected_tests"], json!(["test:t"]));
    assert_eq!(
        r["declared_after"]["project:p"]["costs"]
            .as_array()
            .unwrap()
            .len(),
        3
    );
    assert_eq!(
        r["declared_after"]["test:t"]["costs"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
}

#[test]
fn dangling_cost_reference_is_an_error_not_an_unknown_value() {
    let a = known();
    let mut b = a.clone();
    b.get_mut("filemap").unwrap()["cost_models"]
        .as_object_mut()
        .unwrap()
        .remove("known");
    assert!(
        report(&a, &b, "changed_model")
            .unwrap_err()
            .contains("E_COST_REFERENCE")
    );
}

#[test]
fn declaration_only_cost_change_reports_the_affected_file() {
    let a = known();
    let mut b = a.clone();
    b.get_mut("filemap").unwrap()["cost_models"]["docs"] = json!({"cpu_ms":2,"wall_ms":3,"peak_rss_bytes":4,"io_bytes":5,"basis":"updated documentation estimate"});
    b.get_mut("filemap").unwrap()["files"][1]["cost"] = "docs".into();
    let r = report(&a, &b, "cost_declaration").unwrap();
    assert_eq!(
        r["declared_before"]["file:doc.txt"]["costs"][0]["value"]["cpu_ms"],
        10
    );
    assert_eq!(
        r["declared_after"]["file:doc.txt"]["costs"][0]["value"]["cpu_ms"],
        2
    );
    assert_eq!(r["affected_tests"], json!([]));
}

#[test]
fn project_without_declared_member_costs_stays_unknown() {
    let a = values();
    let r = report(&a, &a, "source_change").unwrap();
    assert_eq!(r["declared_after"]["project:p"]["costs"], json!([]));
    assert!(
        r["unknown"]
            .as_array()
            .unwrap()
            .iter()
            .any(|u| u["node"] == "project:p"
                && u["endpoint"] == "candidate"
                && u["reference"].is_null()
                && u["coordinates"] == json!(["cpu_ms", "wall_ms", "peak_rss_bytes", "io_bytes"]))
    );
}

#[test]
fn grouped_test_costs_keep_original_and_new_endpoint_identities() {
    let old = known();
    let mut new = old.clone();
    new["nodes"]
        .as_array_mut()
        .unwrap()
        .push(json!("test:opaque"));
    new.get_mut("filemap").unwrap()["test_costs"]
        .as_array_mut()
        .unwrap()
        .push(json!({"test":"opaque","cost":"known"}));
    let costs = report(&old, &new, "test_groups").unwrap();
    assert!(costs["declared_before"]["test:opaque"].is_null());
    assert_eq!(
        costs["declared_after"]["test:opaque"]["costs"][0]["member"],
        "test:opaque"
    );
    assert_eq!(
        costs["declared_after"]["test:opaque"]["costs"][0]["value"]["wall_ms"],
        20
    );
    assert_eq!(
        costs["declared_before"]["test:t"]["costs"][0]["member"],
        "test:t"
    );
}
