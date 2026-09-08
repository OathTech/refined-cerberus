#!/usr/bin/env bash
# Whole-file corpus executable speedbump: fresh Cabs, complete retained data,
# captured-comparator checks, supply, observations and focused negative checks.
# This tests the frontend connection; it does not prove C compilation correct.
set -euo pipefail
if [[ $# -eq 0 ]]; then
  check_programs=(t1 t5 t6 t4)
elif [[ $# -eq 1 && "$1" =~ ^t(1|4|5|6)$ ]]; then
  check_programs=("$1")
else
  echo "usage: $0 [t1|t4|t5|t6]" >&2
  exit 2
fi

check_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Same primary-checkout/container convention as setup-cerberus-dep.sh.
check_primary="${check_root%%/worktrees/*}"
check_container="$(dirname "$check_primary")"
check_oracle="$check_container/cerberus-lean/_build/default/backend/driver/main.exe"
check_runtime="$check_container/cerberus-lean/_build/install/default"
[[ -x "$check_oracle" && -d "$check_runtime" ]] || {
  echo "whole-file corpus: existing read-only OCaml oracle/runtime unavailable" >&2
  exit 1
}

export CERB_MEM_MAX="${CERB_MEM_MAX:-40G}"
mkdir -p "$check_root/cerberus-heaplang/.lake/tmp"
check_tmp="$(mktemp -d "$check_root/cerberus-heaplang/.lake/tmp/check-emitted-corpus.XXXXXX")"
trap 'rm -rf -- "$check_tmp"' EXIT
export TMPDIR="$check_tmp"
cd "$check_root"

# Report the external build actually used. Its hash is provenance, not a
# new pin: the fresh-Cabs byte comparison below detects relevant drift.
check_oracle_sha="$(sha256sum "$check_oracle")"
check_oracle_sha="${check_oracle_sha%% *}"
printf 'whole-file corpus: OCaml oracle SHA-256: %s\n' "$check_oracle_sha"
printf 'whole-file corpus: OCaml oracle binary: %s\n' "$check_oracle"
printf 'whole-file corpus: OCaml oracle runtime: %s\n' "$check_runtime"
check_oracle_version="$(scripts/capped "$check_oracle" --version)"
printf 'whole-file corpus: OCaml oracle version: %s\n' "$check_oracle_version"

for check_program in "${check_programs[@]}"; do
  # Fixed capture/comparison settings, distinct from proved execution bounds.
  case "$check_program" in
    t1) check_source=t1.c;        check_supply=36; check_value=4;  check_fuel=50;   check_loops=0 ;;
    t5) check_source=t5_ifelse.c; check_supply=47; check_value=1;  check_fuel=1000; check_loops=0 ;;
    t6) check_source=t6_switch.c; check_supply=51; check_value=20; check_fuel=1000; check_loops=0 ;;
    t4) check_source=t4_while.c;  check_supply=92; check_value=10; check_fuel=1000; check_loops=1 ;;
  esac
  check_index="${check_program#t}"
  # Preserve the relative path: it is retained in Cabs source locations.
  scripts/capped "$check_oracle" --runtime="$check_runtime" \
    --nolibc --cabs-json "docs/corpus-e0/$check_source" > "$check_tmp/$check_program.cabs.json"
  if ! cmp -s "docs/corpus-a7/$check_program.cabs.json" "$check_tmp/$check_program.cabs.json"; then
    echo "whole-file $check_program: fresh Cabs differs from docs/corpus-a7/$check_program.cabs.json" >&2
    exit 1
  fi
  echo "ok: whole-file $check_program — fresh Cabs matches retained fixture"

  # --selftest uses the same comparisons on main := none and supply + 1
  # without another frontend load, and runs scripts/test_file_beq.lean.
  scripts/inspect-emitted-file.sh "$check_tmp/$check_program.cabs.json" "$check_tmp/$check_program.json" "$check_fuel" \
    "cerberus-heaplang/CerberusHeapLang/Examples/EmittedT${check_index}Data.lean" \
    "CerberusHeapLang.CorpusA7.T${check_index}" --check-data --selftest

  python3 - "$check_tmp/$check_program.json" "$check_tmp/$check_program.cabs.json" "$check_program" "$check_supply" "$check_value" "$check_fuel" "$check_loops" <<'PY'
import json
from pathlib import Path
import sys

report = json.loads(Path(sys.argv[1]).read_text())
cabs = json.loads(Path(sys.argv[2]).read_text())
program = sys.argv[3]
supply, value, fuel, loops = map(int, sys.argv[4:])

def require(condition, message):
    if not condition:
        raise SystemExit(f'whole-file {program}: ' + message)

require(report['format'] == 'cerberus-demo-file-inspection-v1', 'unexpected report format')
require(report['ambient_fuel'] == fuel and report['frontend_supply'] == supply
        and report['after_driver_initialization_supply'] == supply + 1, 'fuel/supply metadata drift')
require(report['source_digest'] == cabs['digest'], 'source digest drift')
require(report['file'] == {
    'main': {'digest': cabs['digest'], 'number': 19, 'printed_name': 'main'},
    'calling_convention': 'normal', 'tagDefs_entries': 0, 'stdlib_entries': 110,
    'impl_entries': 6, 'globs_entries': 0, 'funs_entries': 11, 'extern_entries': 11,
    'funinfo_entries': 11, 'loop_attributes_entries': loops, 'visible_objects_env_entries': 0,
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
    'status': 'active', 'value': f'Specified({value})', 'blocked': False,
    'stdout': '', 'stderr': '', 'trace': [],
}], 'complete-file execution observation drift')
# The legacy diagnostic marks case/if uncovered. The new exact-body Frag
# theorems, rather than this diagnostic, establish their membership.
if program == 't1':
    require(report['uncovered_body_kinds'] == [], 'unexpected body syntax')
print(f'ok: whole-file {program} — metadata, all three comparator checks and singleton return {value} checked')
PY

  echo "ok: whole-file $check_program — independent structural data, quotation, supply and negative checks passed"
done
