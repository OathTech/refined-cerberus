#!/usr/bin/env bash
# Inspect a real one-TU/no-libc frontend/link/convert result and execute it.
# The JSON is a diagnostic report, not a full-file serialization/certificate.
# All Lean commands select the package toolchain and use the repository cap.
set -euo pipefail

inspection_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ ( $# -ne 3 && $# -ne 5 && $# -ne 6 && $# -ne 7 ) || ! "${3:-}" =~ ^[0-9]+$ ||
      ( $# -ge 6 && "$6" != --check-data ) ||
      ( $# -eq 7 && "$7" != --selftest ) ]]; then
  echo "usage: $0 CABS.json OUTPUT.json AMBIENT_FUEL [DATA.lean NAMESPACE [--check-data [--selftest]]]" >&2
  exit 2
fi
inspection_input="$(realpath -e -- "$1")"
inspection_output="$(realpath -m -- "$2")"
[[ -d "$(dirname "$inspection_output")" ]] || {
  echo "inspection output directory does not exist: $inspection_output" >&2
  exit 2
}
inspection_fuel="$3"
inspection_data_output=""
inspection_check_data=false
inspection_selftest=false
if [[ $# -ge 6 ]]; then inspection_check_data=true; fi
if [[ $# -eq 7 ]]; then inspection_selftest=true; fi
if [[ $# -ge 5 ]]; then
  inspection_data_output="$(realpath -m -- "$4")"
  [[ -d "$(dirname "$inspection_data_output")" && "$inspection_data_output" != "$inspection_output" ]] || {
    echo "data output needs an existing parent and must differ from the report path" >&2
    exit 2
  }
  [[ "$5" =~ ^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]] || {
    echo "data namespace must contain dot-separated ASCII identifiers" >&2
    exit 2
  }
  export CERB_DEMO_DATA_NAMESPACE="$5"
  if "$inspection_check_data" && [[ ! -f "$inspection_data_output" ]]; then
    echo "data file to check does not exist: $inspection_data_output" >&2
    exit 2
  fi
fi
export CERB_MEM_MAX="${CERB_MEM_MAX:-40G}"

"$inspection_root/scripts/setup-cerberus-dep.sh" --check
mkdir -p "$inspection_root/cerberus-heaplang/.lake/tmp"
inspection_tmp="$(mktemp -d "$inspection_root/cerberus-heaplang/.lake/tmp/emitted-inspection.XXXXXX")"
trap 'rm -rf -- "$inspection_tmp"' EXIT
export TMPDIR="$inspection_tmp"

cd "$inspection_root/cerberus-heaplang"
# The interpreter resolves Lean's generated wrapper symbols, not just the
# raw C externs. Build those wrappers from the pinned module through Lake.
../scripts/capped "$HOME/.elan/bin/lake" build +CerberusFresh:c \
  CerberusHeapLang.EmittedStdCore CerberusHeapLang.EmittedMapChecks
mkdir -p "$inspection_tmp/scripts"
../scripts/capped "$HOME/.elan/bin/lake" env lean \
  -o "$inspection_tmp/scripts/emitted_frontend.olean" scripts/emitted_frontend.lean
../scripts/capped "$HOME/.elan/bin/lake" env lean \
  -o "$inspection_tmp/scripts/derive_file_to_expr.olean" scripts/derive_file_to_expr.lean
../scripts/capped "$HOME/.elan/bin/lake" env lean \
  -o "$inspection_tmp/scripts/derive_file_beq.olean" scripts/derive_file_beq.lean
export LEAN_PATH="$inspection_tmp${LEAN_PATH:+:$LEAN_PATH}"
if "$inspection_selftest"; then
  ../scripts/capped "$HOME/.elan/bin/lake" env lean scripts/test_file_beq.lean
fi
if [[ -n "$inspection_data_output" ]] && ! "$inspection_check_data"; then
  export CERB_DEMO_DATA_OUTPUT="$inspection_tmp/data.lean"
else
  unset CERB_DEMO_DATA_OUTPUT
fi
inspection_lean_prefix="$(../scripts/capped "$HOME/.elan/bin/lake" env lean --print-prefix)"
inspection_fresh_c="$inspection_root/.cerberus-ws/lean_frontend/.lake/build/ir/CerberusFresh.c"
inspection_md5_c="$inspection_root/.cerberus-ws/lean_frontend/native/md5.c"
cc -shared -fPIC -I "$inspection_lean_prefix/include" \
  "$inspection_fresh_c" "$inspection_md5_c" \
  -o "$inspection_tmp/CerberusFresh.so"

CERB_DEMO_CABS_INPUT="$inspection_input" \
CERB_DEMO_INSPECTION_OUTPUT="$inspection_tmp/report.json" \
CERB_DEMO_RUNTIME="../.cerberus-ws/runtime/libcore" \
CERB_DEMO_FUEL="$inspection_fuel" \
  ../scripts/capped "$HOME/.elan/bin/lake" env lean \
    "--load-dynlib=$inspection_tmp/CerberusFresh.so" \
    scripts/inspect_emitted_file.lean

if [[ -n "$inspection_data_output" ]]; then
  if "$inspection_check_data"; then
    cp -- "$inspection_data_output" "$inspection_tmp/data.lean"
  fi
  ../scripts/capped "$HOME/.elan/bin/lake" env lean -R "$inspection_tmp" \
    -o "$inspection_tmp/data.olean" "$inspection_tmp/data.lean" || {
      head -n 16 "$inspection_tmp/data.lean" >&2
      exit 1
    }
  cat > "$inspection_tmp/verify.lean" <<LEAN
import data
import scripts.emitted_frontend
import scripts.derive_file_to_expr
import scripts.derive_file_beq
import CerberusHeapLang.EmittedMapChecks

open CerberusHeapLang

structure DataComparison where
  structural : Bool
  quotation : Bool
  supply : Bool

def compareData (actual expected : CerberusHeapLang.EmittedFile.Data)
    (actualSupply expectedSupply : Nat) : DataComparison :=
  { structural := EmittedFileStructural.equal actual expected
    quotation := Lean.toExpr actual == Lean.toExpr expected
    supply := actualSupply == expectedSupply }

#eval do
  let input ← EmittedFileInspection.requiredEnv "CERB_DEMO_CABS_INPUT"
  let runtime ← EmittedFileInspection.requiredEnv "CERB_DEMO_RUNTIME"
  let fuelText ← EmittedFileInspection.requiredEnv "CERB_DEMO_FUEL"
  let some fuel := fuelText.toNat? | throw (IO.userError "invalid ambient fuel")
  let _ : LemFuel := ⟨fuel⟩
  let (actual, supply, _) ← EmittedFileInspection.loadLinkedFile runtime input
  let captured := CerberusHeapLang.EmittedFile.captureData actual
  let expected := $CERB_DEMO_DATA_NAMESPACE.data
  let expectedSupply := $CERB_DEMO_DATA_NAMESPACE.frontendSupply
  let result := compareData captured expected supply expectedSupply
  unless result.structural do
    throw (IO.userError "emitted-file structural-data comparison failed")
  unless result.quotation do
    throw (IO.userError "emitted-file quotation comparison failed")
  unless result.supply do
    throw (IO.userError "emitted-file supply comparison failed")
  -- Check the comparators on this very frontend instance as well as on
  -- the earlier inspection run; comparator functions are excluded from Data.
  let reference := fun (a b : sym) => Lem_Basic_classes.ordCompare a b
  let stdCmp := EmittedFile.mapComparator reference actual.stdlib
  let funCmp := EmittedFile.mapComparator reference actual.funs
  let some entry := actual.main | throw (IO.userError "compared file has no main")
  -- Resolve the same callee names as EmittedStdCore.findStdFun from the
  -- compared data. Importing that adapter here would also import its t1
  -- declaration, colliding with a separately elaborated retained t1 input.
  let libraryMatch := ["is_representable_integer", "conv_int", "conv_loaded_int"].all fun name =>
    match captured.stdlib.bind (fun tree => (Pmap.bindings tree).find? fun
        (pair : sym × generic_fun_map_decl Unit core_run_annotation) =>
      match pair.1 with
      | sym.Symbol _ _ (.SD_Id text) => text == name
      | _ => false) with
    | some (key, .Fun _ _ _) => EmittedFile.mapLookupCheck stdCmp reference key captured.stdlib
    | _ => false
  let comparatorsMatch := libraryMatch &&
    EmittedFile.mapLookupCheck funCmp reference entry captured.funs &&
    EmittedMapChecks.mapUnionCheck stdCmp funCmp reference captured.stdlib captured.funs
  unless comparatorsMatch do
    throw (IO.userError "compared frontend instance failed captured-comparator checks")
  IO.println "emitted-file data round-trip: independent structural data, quotation and supply match"
  IO.println "ok: emitted-file comparison — all three captured-comparator checks pass on the compared instance"
  let mut negativeChecks := Lean.Json.mkObj []
  if $inspection_selftest then
    let changedMain := compareData captured { expected with main := none } supply expectedSupply
    unless !changedMain.structural && !changedMain.quotation && changedMain.supply do
      throw (IO.userError "main perturbation did not fail both data comparisons as intended")
    IO.println "ok: emitted-file negative check — main := none rejected by structural and quotation comparisons"
    let changedSupply := compareData captured expected supply (expectedSupply + 1)
    unless changedSupply.structural && changedSupply.quotation && !changedSupply.supply do
      throw (IO.userError "supply perturbation did not fail only the supply comparison as intended")
    IO.println "ok: emitted-file negative check — frontendSupply + 1 rejected by supply comparison"
    negativeChecks := Lean.Json.mkObj [("main", Lean.toJson true), ("supply", Lean.toJson true)]
  let comparisonOutput ← EmittedFileInspection.requiredEnv "CERB_DEMO_COMPARISON_OUTPUT"
  IO.FS.writeFile comparisonOutput ((Lean.Json.mkObj [
    ("structural_data_match", Lean.toJson result.structural),
    ("quotation_and_supply_match", Lean.toJson (result.quotation && result.supply)),
    ("captured_comparator_checks_match", Lean.toJson comparatorsMatch),
    ("negative_checks", negativeChecks)]).pretty ++ "\n")
LEAN
  CERB_DEMO_CABS_INPUT="$inspection_input" \
  CERB_DEMO_RUNTIME="../.cerberus-ws/runtime/libcore" \
  CERB_DEMO_FUEL="$inspection_fuel" \
  CERB_DEMO_COMPARISON_OUTPUT="$inspection_tmp/comparison.json" \
    ../scripts/capped "$HOME/.elan/bin/lake" env lean \
      "--load-dynlib=$inspection_tmp/CerberusFresh.so" "$inspection_tmp/verify.lean"
fi

# Install only a successfully generated report. Record the actual input,
# runtime library and producer source hashes beside its observations.
python3 - "$inspection_root" "$inspection_input" "$inspection_tmp/report.json" <<'PY'
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

root, input_path, output = map(Path, sys.argv[1:])
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
report = json.loads(output.read_text())
assert report['format'] == 'cerberus-demo-file-inspection-v1'
report['provenance'] = {
    'cabs_sha256': sha(input_path),
    'semantics_commit': subprocess.check_output(
        ['git', '-C', str(root / '.cerberus-ws'), 'rev-parse', 'HEAD'], text=True).strip(),
    'lean_version': (root / 'cerberus-heaplang/lean-toolchain').read_text().strip(),
    'runtime_path': '../.cerberus-ws/runtime/libcore',
    'sources_sha256': {
        path: sha(root / path) for path in [
            '.cerberus-ws/runtime/libcore/std.core',
            '.cerberus-ws/runtime/libcore/impls/gcc_4.9.0_x86_64-apple-darwin10.8.0.impl',
            '.cerberus-ws/lean_frontend/Main.lean',
            '.cerberus-ws/lean_frontend/CerberusFresh.lean',
            '.cerberus-ws/lean_frontend/native/md5.c',
            '.cerberus-ws/lean_frontend/.lake/build/ir/CerberusFresh.c',
            'cerberus-heaplang/scripts/inspect_emitted_file.lean',
            'cerberus-heaplang/scripts/derive_file_to_expr.lean',
            'cerberus-heaplang/scripts/derive_file_beq.lean',
            'cerberus-heaplang/scripts/emitted_frontend.lean',
            'cerberus-heaplang/CerberusHeapLang/EmittedFile.lean',
            'cerberus-heaplang/CerberusHeapLang/EmittedMapChecks.lean',
            'cerberus-heaplang/CerberusHeapLang/EmittedStdCore.lean',
            'cerberus-heaplang/CerberusHeapLang/Examples/EmittedT1Data.lean',
            'scripts/inspect-emitted-file.sh',
        ]
    },
}
data_path = output.parent / 'data.lean'
if data_path.exists():
    report['data_export'] = {
        **json.loads((output.parent / 'comparison.json').read_text()),
        'sha256': sha(data_path),
        'namespace': os.environ['CERB_DEMO_DATA_NAMESPACE'],
        'comparators': 'retained by captureComparators; not serialized or assumed canonical',
    }
output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
PY
if [[ -n "$inspection_data_output" ]]; then
  if ! "$inspection_check_data"; then
    mv -- "$inspection_tmp/data.lean" "$inspection_data_output"
  fi
  echo "verified emitted-file data: $inspection_data_output"
fi
mv -- "$inspection_tmp/report.json" "$inspection_output"
echo "inspection report: $inspection_output"
