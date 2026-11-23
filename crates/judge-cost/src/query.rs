//! One request to either of the two installed producers used by the cost judge.
use std::collections::BTreeMap;

pub(crate) struct Command {
    pub argv: [&'static str; 2],
    pub env: BTreeMap<String, String>,
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}
