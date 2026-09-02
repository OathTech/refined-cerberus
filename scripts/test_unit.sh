#!/usr/bin/env bash
# refined-cerberus gate runner.
#
# The TRUST BASE is gates 1-3: the banned-methods grep and the two
# capped builds, each of which elaborates its package's in-build axiom
# sweep (Audit.lean: exact export pins + exhaustive bound + banned-axiom
# sweep). Everything after that is a SPEEDBUMP ([USER 2026-09-02]): a
# claim-point report that catches honest drift; it is not designed to
# survive adversarial attack.
#   default : gates 1-3 + the capability-manifest speedbump (the claim gate)
#   --fast  : gates 1-3 only (intermediate commits; say fast-gate in the message)
set -euo pipefail
cd "$(dirname "$0")/.."

fast=0
for arg in "$@"; do
  case "$arg" in
    --fast) fast=1 ;;
    *) echo "usage: $0 [--fast]" >&2; exit 2 ;;
  esac
done
fail=0

echo "== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) =="
# Audit.lean files name the ban and are excluded; a real use there
# enters a cone and fails the in-build sweep.
if grep -rnE 'native_decide|bv_decide|ofReduceBool|ofReduceNat' \
    --include='*.lean' --exclude=Audit.lean \
    RefinedCerberus RefinedCerberus.lean \
    cerberus-heaplang/CerberusHeapLang cerberus-heaplang/CerberusHeapLang.lean; then
  echo "FAIL: banned proof method reference found (above)" >&2; fail=1
else
  echo "ok: no banned proof-method references"
fi

echo "== gate 2: capped build, root package (elaborates its axiom audit) =="
if scripts/capped "$HOME/.elan/bin/lake" build; then
  echo "ok: root build green"
else
  echo "FAIL: root build red" >&2; fail=1
fi

echo "== gate 3: capped build, cerberus-heaplang (elaborates its axiom audit) =="
if (cd cerberus-heaplang && ../scripts/capped "$HOME/.elan/bin/lake" build); then
  echo "ok: cerberus-heaplang build green"
else
  echo "FAIL: cerberus-heaplang build red" >&2; fail=1
fi

if [[ $fast -eq 0 ]]; then
  echo "== speedbump: capability manifest (regenerate; red on a red row or drift) =="
  manifest=cerberus-heaplang/docs/CAPABILITY_MANIFEST.md
  tmp="$(mktemp "${TMPDIR:-/tmp}/capability_manifest.XXXXXX")"
  if (cd cerberus-heaplang && ../scripts/capped "$HOME/.elan/bin/lake" env lean \
        scripts/capability_manifest.lean > "$tmp"); then
    if [[ -f "$manifest" ]] && diff -u "$manifest" "$tmp"; then
      echo "ok: capability manifest regenerated, no drift"
    else
      echo "FAIL (speedbump): capability manifest drift/missing (diff above) —" \
        "regenerate docs/CAPABILITY_MANIFEST.md deliberately, same commit" >&2; fail=1
    fi
  else
    echo "FAIL (speedbump): capability manifest generator red (a MISSING/red row);" \
      "generator output:" >&2
    cat "$tmp" >&2; fail=1
  fi
  rm -f "$tmp"
fi

if [[ $fail -ne 0 ]]; then
  echo "GATE FAILURE" >&2
  exit 1
fi
if [[ $fast -eq 1 ]]; then
  echo "FAST-GATE GREEN (gates 1-3 only — not a claim-point result; say fast-gate in the commit)"
else
  echo "ALL GATES GREEN"
fi
