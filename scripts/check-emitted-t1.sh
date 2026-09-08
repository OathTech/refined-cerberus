#!/usr/bin/env bash
# Whole-file t1 executable speedbump: fresh Cabs, complete retained data,
# captured-comparator checks, supply, observations and focused negative checks.
# This tests the frontend connection; it does not prove C compilation correct.
set -euo pipefail
[[ $# -eq 0 ]] || { echo "usage: $0" >&2; exit 2; }

check_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Same primary-checkout/container convention as setup-cerberus-dep.sh.
check_primary="${check_root%%/worktrees/*}"
check_container="$(dirname "$check_primary")"
check_oracle="$check_container/cerberus-lean/_build/default/backend/driver/main.exe"
check_runtime="$check_container/cerberus-lean/_build/install/default"
[[ -x "$check_oracle" && -d "$check_runtime" ]] || {
  echo "whole-file t1: existing read-only OCaml oracle/runtime unavailable" >&2
  exit 1
}

export CERB_MEM_MAX="${CERB_MEM_MAX:-40G}"
mkdir -p "$check_root/cerberus-heaplang/.lake/tmp"
check_tmp="$(mktemp -d "$check_root/cerberus-heaplang/.lake/tmp/check-emitted-t1.XXXXXX")"
trap 'rm -rf -- "$check_tmp"' EXIT
export TMPDIR="$check_tmp"
cd "$check_root"

# Preserve the relative path: it is retained in Cabs source locations.
scripts/capped "$check_oracle" --runtime="$check_runtime" \
  --nolibc --cabs-json docs/corpus-e0/t1.c > "$check_tmp/t1.cabs.json"
if ! cmp -s docs/corpus-a7/t1.cabs.json "$check_tmp/t1.cabs.json"; then
  echo "whole-file t1: fresh Cabs differs from docs/corpus-a7/t1.cabs.json" >&2
  exit 1
fi
echo "ok: whole-file t1 — fresh Cabs matches retained fixture"

# --selftest uses the same comparisons on main := none and supply + 1
# without another frontend load, and runs scripts/test_file_beq.lean.
scripts/inspect-emitted-file.sh "$check_tmp/t1.cabs.json" "$check_tmp/report.json" 50 \
  cerberus-heaplang/CerberusHeapLang/Examples/EmittedT1Data.lean \
  CerberusHeapLang.CorpusA7.T1 --check-data --selftest

python3 - "$check_tmp/report.json" "$check_tmp/t1.cabs.json" <<'PY'
import json
from pathlib import Path
import sys

report = json.loads(Path(sys.argv[1]).read_text())
cabs = json.loads(Path(sys.argv[2]).read_text())

def require(condition, message):
    if not condition:
        raise SystemExit('whole-file t1: ' + message)

require(report['format'] == 'cerberus-demo-file-inspection-v1', 'unexpected report format')
require(report['ambient_fuel'] == 50 and report['frontend_supply'] == 36
        and report['after_driver_initialization_supply'] == 37, 'fuel/supply metadata drift')
require(report['source_digest'] == cabs['digest'], 'source digest drift')
require(report['file'] == {
    'main': {'digest': cabs['digest'], 'number': 19, 'printed_name': 'main'},
    'calling_convention': 'normal', 'tagDefs_entries': 0, 'stdlib_entries': 110,
    'impl_entries': 6, 'globs_entries': 0, 'funs_entries': 11, 'extern_entries': 11,
    'funinfo_entries': 11, 'loop_attributes_entries': 0, 'visible_objects_env_entries': 0,
}, 'whole-file metadata drift')
require(report['integer_library']['stdlib_quotation_match'] is True
        and report['integer_library']['captured_comparator_paths_match'] is True
        and report['main_lookup']['captured_comparator_path_match'] is True
        and report['label_collection']['captured_union_comparisons_match'] is True,
        'captured comparator or library comparison failed')
require(report['data_export']['structural_data_match'] is True
        and report['data_export']['quotation_and_supply_match'] is True
        and report['data_export']['captured_comparator_checks_match'] is True
        and report['data_export']['negative_checks'] == {'main': True, 'supply': True},
        'data/supply comparison or negative checks failed')
require(report['outcomes'] == [{
    'status': 'active', 'value': 'Specified(4)', 'blocked': False,
    'stdout': '', 'stderr': '', 'trace': [],
}], 'complete-file execution observation drift')
require(report['uncovered_body_kinds'] == [], 'unexpected body syntax')
print('ok: whole-file t1 — metadata, all three comparator checks and singleton return 4 checked')
PY

echo "ok: whole-file t1 — independent structural data, quotation, supply and negative checks passed"
