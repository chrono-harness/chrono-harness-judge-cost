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
    assert_eq!(
        decision["findings"],
        json!([{
            "code":"W_COST_UNKNOWN", "level":"warning",
            "message":"Affected declared costs contain unknown coordinates; see costs.unknown",
            "delta_refs":["/impact"], "causes":["/outputs/costs/unknown"]
        }])
    );
    let source = decision["findings"][0]["causes"][0].as_str().unwrap();
    assert!(
        !decision
            .pointer(source)
            .unwrap()
            .as_array()
            .unwrap()
            .is_empty()
    );
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
    assert_eq!(decision["findings"], json!([]));
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

#[test]
fn model_pointers_resolve_distinct_names_in_the_original_registry() {
    let base = known();
    let mut candidate = base.clone();
    let names = [
        "",
        "/",
        "~",
        "~1",
        "~0",
        "//",
        "~~",
        "~/~1",
        "𝄞/模型~",
        "\0",
    ];
    for (i, name) in names.iter().enumerate() {
        let mut model = base["filemap"]["cost_models"]["known"].clone();
        model["cpu_ms"] = json!(i);
        candidate["filemap"]["cost_models"][name] = model;
    }
    let row = candidate["filemap"]["files"]
        .as_array()
        .unwrap()
        .iter()
        .position(|f| f["path"] == "src.bin")
        .unwrap();
    for (i, name) in names.iter().enumerate() {
        candidate["filemap"]["files"][row]["cost"] = json!(name);
        let costs = report(&base, &candidate, "source_change").unwrap();
        let source = &costs["declared_after"]["file:src.bin"]["costs"][0];
        let pointer = source["source"]["pointer"].as_str().unwrap();
        assert_eq!(source["reference"], *name);
        assert_eq!(source["value"]["cpu_ms"], i);
        assert_eq!(
            candidate["filemap"].pointer(pointer),
            Some(&source["value"])
        );
    }
}

#[test]
fn report_keys_are_the_union_of_delta_reached_owners_and_required_tests() {
    let mut source = known();
    let fm = &mut source["filemap"];
    let mut row = fm["files"][0].clone();
    row["path"] = json!("目录/一.bin");
    row["owner"] = json!("only-script");
    fm["files"].as_array_mut().unwrap().push(row);
    source["nodes"]
        .as_array_mut()
        .unwrap()
        .push(json!("script:only-script"));
    let base = serde_json::from_value(source.clone()).unwrap();
    let candidate = serde_json::from_value(source).unwrap();
    let mut impact = FilemapImpact {
        schema: "chrono-filemap-impact/v6".into(),
        delta: vec![
            ChangedPath {
                path: "目录/一.bin".into(),
            },
            ChangedPath {
                path: "目录/一.bin".into(),
            },
        ],
        reached: [
            "file:src.bin",
            "project:p",
            "script:only-script",
            "test:ignore",
            "files:skip",
            "scripted:skip",
        ]
        .into_iter()
        .map(String::from)
        .collect(),
        required_tests: vec!["test:t".into(), "test:t".into()],
        tests: vec!["test:unselected".into()],
        retired_tests: vec!["test:unselected".into()],
    };
    let report = produce(&base, &candidate, &impact).unwrap();
    for endpoint in ["declared_before", "declared_after"] {
        let keys: std::collections::BTreeSet<_> = report[endpoint]
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect();
        assert_eq!(
            keys,
            [
                "file:目录/一.bin",
                "file:src.bin",
                "project:p",
                "script:only-script",
                "test:t"
            ]
            .into_iter()
            .collect()
        );
    }
    impact.schema.push('x');
    assert_eq!(
        produce(&base, &candidate, &impact).unwrap_err(),
        "E_IMPACT: unsupported cost input schema"
    );
}

#[test]
fn report_read_write_and_flush_failures_reach_the_caller() {
    use chrono_judge_cost::report::write_report;
    use std::io::{self, Read, Write};

    struct FailedRead;
    impl Read for FailedRead {
        fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
            Err(io::Error::other("read interrupted by producer"))
        }
    }

    #[derive(Default)]
    struct Sink {
        fail_write: bool,
        bytes: Vec<u8>,
        flushes: usize,
    }
    impl Write for Sink {
        fn write(&mut self, input: &[u8]) -> io::Result<usize> {
            if self.fail_write {
                return Err(io::Error::other("write refused by consumer"));
            }
            self.bytes.extend_from_slice(input);
            Ok(input.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            self.flushes += 1;
            Err(io::Error::other("consumer flush failed"))
        }
    }

    let mut sink = Sink::default();
    assert_eq!(
        write_report(FailedRead, &mut sink).unwrap_err(),
        "read interrupted by producer"
    );
    assert!(sink.bytes.is_empty());
    assert_eq!(sink.flushes, 0);

    let summaries: Value =
        serde_json::from_str(include_str!("fixtures/impact-summaries.json")).unwrap();
    let binding = json!({"base":"base","candidate":"candidate","candidate_tree":"tree","registry_digest":"registry","context_digest":"context"});
    let bytes = serde_json::to_vec(&json!({"base":values(),"candidate":values(),"impact":summaries["changed_model"],"binding":binding})).unwrap();
    sink.fail_write = true;
    assert_eq!(
        write_report(bytes.as_slice(), &mut sink).unwrap_err(),
        "write refused by consumer"
    );
    assert!(sink.bytes.is_empty());
    assert_eq!(sink.flushes, 0);

    sink.fail_write = false;
    assert_eq!(
        write_report(bytes.as_slice(), &mut sink).unwrap_err(),
        "consumer flush failed"
    );
    assert_eq!(sink.flushes, 1);
    let report: Value = serde_json::from_slice(&sink.bytes).unwrap();
    assert_eq!(report["outputs"]["costs"]["binding"], binding);
}
