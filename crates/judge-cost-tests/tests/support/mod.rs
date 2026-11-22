use chrono_harness::wire::Delta;
pub use chrono_registration_fixture::*;
pub fn delta(path: &str) -> Delta {
    Delta {
        kind: "M".into(),
        path: path.into(),
        old_blob: Some("a".repeat(40)),
        new_blob: Some("b".repeat(40)),
        old_mode: Some("100644".into()),
        new_mode: Some("100644".into()),
    }
}
