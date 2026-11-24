use chrono_judge_cost::{ChangedFile, FilemapImpact, produce};
use serde_json::{Value, json};

#[derive(serde::Deserialize)]
struct ChangedPath {
    path: String,
}

impl ChangedFile for ChangedPath {
    fn path(&self) -> &str {
        &self.path
    }
}

const FM: &str = ".chrono-harness/FILEMAP.json";
fn values() -> Value {
    serde_json::from_str(include_str!("fixtures/filemap-view.json")).unwrap()
}

// The FILEMAP v0.1.0-alpha.1 impact-summary output for these endpoint fixtures.
fn report(a: &Value, b: &Value, scenario: &str) -> Result<Value, String> {
    let samples: std::collections::BTreeMap<String, FilemapImpact<ChangedPath>> =
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

#[test]
fn report_command_publishes_the_warning_and_exact_supplied_binding() {
    let binding = json!({"base":"base","candidate":"candidate","candidate_tree":"tree","registry_digest":"registry","context_digest":"context"});
    let summaries: Value =
        serde_json::from_str(include_str!("fixtures/impact-summaries.json")).unwrap();
    let input = json!({"base":values(),"candidate":values(),"impact":summaries["changed_model"],"binding":binding});
    let mut output = Vec::new();
    chrono_judge_cost::report::write_report(&serde_json::to_vec(&input).unwrap()[..], &mut output)
        .unwrap();
    let decision: Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(decision["status"], "warn");
    assert_eq!(decision["findings"][0]["code"], "W_COST_UNKNOWN");
    assert_eq!(decision["outputs"]["costs"]["binding"], binding);
    let mut malformed = input;
    malformed["impact"]["schema"] = json!("unsupported");
    output.clear();
    assert!(
        chrono_judge_cost::report::write_report(
            &serde_json::to_vec(&malformed).unwrap()[..],
            &mut output
        )
        .unwrap_err()
        .contains("unsupported cost input schema")
    );
    assert!(output.is_empty());
}

#[test]
fn report_retains_endpoint_row_pointers_after_sorting_and_model_escaping() {
    let a = known();
    let mut b = a.clone();
    b["nodes"].as_array_mut().unwrap().push(json!("script:p"));
    let files = b["filemap"]["files"].as_array_mut().unwrap();
    files.reverse();
    let source_row = files.iter().position(|f| f["path"] == "src.bin").unwrap();
    files[source_row]["cost"] = json!("updated~/");
    files.push(json!({"path":"src.bin","owner":"p","cost":"known"}));
    let known_model = b["filemap"]["cost_models"]["known"].clone();
    b["filemap"]["cost_models"]["updated~/"] = known_model;
    b["filemap"]["test_costs"]
        .as_array_mut()
        .unwrap()
        .insert(0, json!({"test":"another","cost":"known"}));
    let mut impacts: Value =
        serde_json::from_str(include_str!("fixtures/impact-summaries.json")).unwrap();
    let impact = &mut impacts["source_change"];
    impact["reached"]
        .as_array_mut()
        .unwrap()
        .push(json!("script:p"));
    let binding = json!({"base":"base","candidate":"candidate","candidate_tree":"tree","registry_digest":"registry","context_digest":"context"});
    let input = json!({"base":a,"candidate":b,"impact":impact,"binding":binding});
    let mut output = Vec::new();
    chrono_judge_cost::report::write_report(&serde_json::to_vec(&input).unwrap()[..], &mut output)
        .unwrap();
    let decision: Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(decision["status"], "pass");
    let costs = &decision["outputs"]["costs"];
    for (endpoint, view) in [
        ("declared_before", &input["base"]),
        ("declared_after", &input["candidate"]),
    ] {
        for subject in ["file:src.bin", "test:t", "project:p", "script:p"] {
            if endpoint == "declared_before" && subject == "script:p" {
                assert!(costs[endpoint][subject].is_null());
                continue;
            }
            for row in costs[endpoint][subject]["costs"].as_array().unwrap() {
                for key in ["declaration", "source"] {
                    assert_eq!(row[key]["registry"], FM);
                }
                let fm = &view["filemap"];
                assert_eq!(
                    fm.pointer(row["declaration"]["pointer"].as_str().unwrap()),
                    Some(&row["reference"])
                );
                assert_eq!(
                    fm.pointer(row["source"]["pointer"].as_str().unwrap()),
                    Some(&row["value"])
                );
            }
        }
    }
    assert_eq!(
        costs["declared_before"]["test:t"]["costs"][0]["declaration"]["pointer"],
        "/test_costs/0/cost"
    );
    let after = &costs["declared_after"];
    assert_eq!(
        after["test:t"]["costs"][0]["declaration"]["pointer"],
        "/test_costs/1/cost"
    );
    assert_eq!(
        after["file:src.bin"]["costs"][0]["source"]["pointer"],
        "/cost_models/updated~0~1"
    );
    for subject in ["project:p", "script:p"] {
        let members = after[subject]["costs"].as_array().unwrap();
        assert_eq!(
            members
                .iter()
                .map(|m| m["member"].as_str().unwrap())
                .collect::<Vec<_>>(),
            [
                "file:p/Cargo.lock",
                "file:p/Cargo.toml",
                "file:src.bin",
                "file:src.bin"
            ]
        );
        assert_eq!(members[2]["reference"], "updated~/");
        assert_eq!(members[3]["reference"], "known");
    }
}
