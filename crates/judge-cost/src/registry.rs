use crate::verified_cost::{CostFile, TestCost};
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
