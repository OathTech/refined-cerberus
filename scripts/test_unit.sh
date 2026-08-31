#!/usr/bin/env bash
# refined-cerberus minimal gate runner (arc-0).
# Gates are minimal by ruling (rules-of-engagement §5/§6): the builds
# of BOTH packages (root RefinedCerberus + the cerberus-heaplang
# demo development, each of which elaborates its own Audit.lean —
# the in-build axiom-cone sweep + curated pins) plus the
# kernel-method grep ban. New gates only for load-bearing TRUST
# properties.
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0

echo "== gate 1: kernel-method grep ban =="
# Banned proof methods (operator ruling, imported): native_decide,
# bv_decide, ofReduce*. Scope: all project .lean sources in BOTH
# packages (root RefinedCerberus + the cerberus-heaplang demo)
# EXCEPT the Audit.lean files, which document the ban by name and
# are themselves covered by the in-build sweeps (a real ofReduce*
# use enters a cone there and fails the build).
if grep -rnE 'native_decide|bv_decide|ofReduceBool|ofReduceNat' \
    --include='*.lean' \
    --exclude=Audit.lean \
    RefinedCerberus RefinedCerberus.lean \
    cerberus-heaplang/CerberusHeapLang cerberus-heaplang/CerberusHeapLang.lean; then
  echo "FAIL: banned proof method reference found (above)" >&2
  fail=1
else
  echo "ok: no banned proof-method references"
fi

echo "== gate 2: capped build, root package (elaborates its in-build axiom audit) =="
if scripts/capped "$HOME/.elan/bin/lake" build; then
  echo "ok: root build green (axiom sweep + pins passed in-build)"
else
  echo "FAIL: root build red" >&2
  fail=1
fi

echo "== gate 3: capped build, cerberus-heaplang demo (its own audit rides) =="
if (cd cerberus-heaplang && ../scripts/capped "$HOME/.elan/bin/lake" build); then
  echo "ok: cerberus-heaplang build green (axiom sweep + pins passed in-build)"
else
  echo "FAIL: cerberus-heaplang build red" >&2
  fail=1
fi

if [[ $fail -ne 0 ]]; then
  echo "GATE FAILURE" >&2
  exit 1
fi
echo "ALL GATES GREEN"
