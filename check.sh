#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p target
scratch=$(mktemp -d "$(pwd -P)/target/check.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export TMPDIR="$scratch"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/cargo}"
cargo fmt --check --manifest-path crates/judge-cost/Cargo.toml
product=crates/judge-cost/Cargo.toml
cargo build --locked --message-format=json-render-diagnostics --manifest-path "$product" > "$scratch/build.jsonl"
cargo fmt --check --manifest-path crates/judge-cost-tests/Cargo.toml
cargo test --locked --manifest-path crates/judge-cost-tests/Cargo.toml
coverage_failure() {
  echo "E_VERUS_COVERAGE: $*" >&2
  exit 1
}

prove() {
  local label=$1 root=$2
  local output="$scratch/$label.rlib" report="$scratch/$label.json"
  "${VERUS:-verus}" --crate-type=lib --no-cheating --no-external-by-default --num-threads 2 \
    --output-json --compile "--emit=link=$output,dep-info=$output.d" "$root" -o "$output" \
    -Zchecksum-hash-algorithm=sha256 > "$report" || { cat "$report" >&2; coverage_failure "$label: verifier failed"; }
}

admit_proof() {
  local label=$1
  shift
  local output="$scratch/$label.rlib" report="$scratch/$label.json"
  test -s "$report" && test -s "$output" && test -s "$output.d" ||
    coverage_failure "$label: missing required proof result"
  cat "$report"
  jq -e '.verus.version == "0.2026.04.24.f8e1704" and
    .verus.commit == "f8e17045c4ac17a02e566b8997070f2eecc255be" and
    (."verification-results" | .success == true and ."is-verifying-entire-crate" == true and
    ."encountered-error" == false and ."encountered-vir-error" == false and
    .errors == 0 and .verified > 0)' "$report" >/dev/null || coverage_failure "$label: unexpected verifier report"
  chrono-host-bootstrap check-compiler-sources proof "$output" "$@" || coverage_failure "$label: compiled sources differ from required inputs"
}

# Read the exact library selected by Cargo in the build of the tested executable.
metadata=$(jq -ers --arg manifest "$(pwd -P)/$product" '
  [.[] | select(.reason == "compiler-artifact" and .manifest_path == $manifest
                 and .target.kind == ["lib"]) | .filenames[] | select(endswith(".rmeta"))]
  | if length == 1 then .[0] else error("expected the product library") end
' "$scratch/build.jsonl") || coverage_failure "native library was not identified"
filename=${metadata##*/}
stem=${filename#lib}
stem=${metadata%/*}/${stem%.rmeta}
chrono-host-bootstrap check-compiler-sources native "$stem" src/verified_cost.rs src/lib.rs ||
  coverage_failure "native library differs from required sources"

policy=crates/judge-cost/src/verified_cost.rs
expectations=crates/judge-cost-tests/tests/verified_cost.rs
product_operation=verify.judge-cost
test_operation=verify.judge-cost-tests

prove "$product_operation" "$policy"
prove "$test_operation" "$expectations"

admit_proof "$product_operation" "$policy"
admit_proof "$test_operation" "$expectations" crates/judge-cost-tests/tests/../../judge-cost/src/verified_cost.rs
