#!/usr/bin/env bash
# refined-cerberus gate runner.
#
# The TRUST BASE is gates 1-2: the banned-methods grep and the two
# capped builds, each of which elaborates its package's in-build axiom
# sweep (Audit.lean: exact export pins + exhaustive bound + banned-axiom
# sweep). Everything after that is a SPEEDBUMP ([USER 2026-09-02]): a
# claim-point report that catches honest drift; it is not designed to
# survive adversarial attack.
#   default : gates 1-2 + the speedbumps (the rule-use and classification
#             manifest, the import direction, the client-boundary check) —
#             the claim gate
#   --fast  : gates 1-2 only (intermediate commits; say fast-gate in the message)
# The module classification every speedbump reads is the one file
# cerberus-heaplang/scripts/module_classes.tsv (ar5-manifest 2026-09-04).
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
    cerberus-heaplang/CerberusHeapLang cerberus-heaplang/CerberusHeapLang.lean; then
  echo "FAIL: banned proof method reference found (above)" >&2; fail=1
else
  echo "ok: no banned proof-method references"
fi

echo "== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) =="
if (cd cerberus-heaplang && ../scripts/capped "$HOME/.elan/bin/lake" build); then
  echo "ok: cerberus-heaplang build green"
else
  echo "FAIL: cerberus-heaplang build red" >&2; fail=1
fi

if [[ $fast -eq 0 ]]; then
  echo "== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) =="
  manifest=cerberus-heaplang/docs/CAPABILITY_MANIFEST.md
  tmp="$(mktemp "${TMPDIR:-/tmp}/capability_manifest.XXXXXX")"
  if (cd cerberus-heaplang && ../scripts/capped "$HOME/.elan/bin/lake" env lean \
        scripts/capability_manifest.lean > "$tmp"); then
    if [[ -f "$manifest" ]] && diff -u "$manifest" "$tmp"; then
      echo "ok: capability manifest regenerated, no drift"
    else
      echo "FAIL (speedbump): manifest drift/missing (diff above) —" \
        "regenerate docs/CAPABILITY_MANIFEST.md deliberately, same commit" >&2; fail=1
    fi
  else
    echo "FAIL (speedbump): manifest generator red (a red row / an unclassified constructor or module /" \
      "a stale claim-matrix name); generator output:" >&2
    cat "$tmp" >&2; fail=1
  fi
  rm -f "$tmp"

  echo "== speedbump: import direction (semantics → heap → rules → adequacy → clients) =="
  # No core module may import an exhibit, example-support or production module.
  # The core set is the class `core` of the one module classification (a
  # missing core file, or an empty class, is red too).
  tsv=cerberus-heaplang/scripts/module_classes.tsv
  files=()
  tsv_bad=0
  while IFS=$'\t' read -r module cls _allow _note || [[ -n "$module" ]]; do
    [[ -z "$module" || "$module" == \#* ]] && continue
    if [[ -z "$cls" || -z "$_allow" || -z "$_note" ]]; then
      echo "FAIL (speedbump): $tsv: malformed row for module $module (need 4 cells)" >&2; tsv_bad=1; continue
    fi
    [[ "$cls" != core ]] && continue
    files+=("cerberus-heaplang/${module//./\/}.lean")
  done < "$tsv"
  [[ $tsv_bad -eq 1 ]] && fail=1
  if [[ ${#files[@]} -eq 0 ]] || ! ls "${files[@]}" > /dev/null || \
      grep -nE '^import CerberusHeapLang\.([A-Za-z]*Exhibit|Examples\.|Prod)' "${files[@]}"; then
    echo "FAIL (speedbump): a core module is missing, the core class is empty, or a core module imports an exhibit/example/production module (above)" >&2; fail=1
  else
    echo "ok: import direction — ${#files[@]} core modules, none imports an exhibit/example/production module"
  fi

  echo "== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) =="
  if scripts/boundary_check.sh; then
    echo "ok: client boundary — no unallowlisted internals mention"
  else
    echo "FAIL (speedbump): client boundary — an internals mention in a client module without an allowance (above)" >&2; fail=1
  fi
fi

if [[ $fail -ne 0 ]]; then
  echo "GATE FAILURE" >&2
  exit 1
fi
if [[ $fast -eq 1 ]]; then
  echo "FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)"
else
  echo "ALL GATES GREEN"
fi
