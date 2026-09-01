#!/usr/bin/env bash
# refined-cerberus minimal gate runner (arc-0).
# Gates are minimal by ruling (rules-of-engagement §5/§6): the builds
# of BOTH packages (root RefinedCerberus + the cerberus-heaplang
# demo development, each of which elaborates its own Audit.lean —
# the in-build axiom-cone sweep + curated pins) plus the
# kernel-method grep ban, plus (foundations arc Phase 0) the
# capability-manifest coverage gate — a load-bearing TRUST property:
# claims surfaces cannot outrun proved per-construct coverage. New
# gates only for load-bearing TRUST properties.
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

echo "== gate 4: capability manifest (drift + README certified-scope tie) =="
# Foundations arc (2026-08-31 audit F-01/F-09; Phase 0, upgraded to
# the CONE-DERIVED form in Phase-1 S1c): the generated capability
# manifest is THE authoritative per-construct scope statement, and
# its row set is DERIVED from the unified cone — the generator
# enumerates `Frag`'s constructors out of the built environment (a
# cone constructor without a row mapping is a generator throw) and
# derives `Step` mirror coverage the same way (every Step
# constructor must be claimed by exactly one row). This gate (a)
# regenerates the manifest and fails on any drift against the
# committed copy (the generator itself fails closed on an unmapped
# cone/mirror constructor or a missing checked rule/match/consumer
# name — so a new or deleted constructor without a manifest row is
# red here), and (b) ties the README's certified-scope token list
# to the manifest's ADEQUACY-EXPORTABLE set: a construct claimed as
# certified without a manifest row at that level is red.
manifest=cerberus-heaplang/docs/CAPABILITY_MANIFEST.md
if [[ ! -f "$manifest" ]]; then
  echo "FAIL: committed capability manifest missing ($manifest)" >&2
  fail=1
else
  tmpman="$(mktemp "${TMPDIR:-/tmp}/capability_manifest.XXXXXX")" || {
    echo "FAIL: mktemp failed for manifest regeneration" >&2; exit 1; }
  if (cd cerberus-heaplang && \
      ../scripts/capped "$HOME/.elan/bin/lake" env lean \
        scripts/capability_manifest.lean > "$tmpman"); then
    if diff -u "$manifest" "$tmpman"; then
      echo "ok: capability manifest regenerated, no drift"
    else
      echo "FAIL: capability manifest drift (diff above) — regenerate" \
        "docs/CAPABILITY_MANIFEST.md deliberately, same commit" >&2
      fail=1
    fi
  else
    echo "FAIL: capability manifest generator red (an unmapped Step/Frag" \
      "constructor or a missing checked name); generator output:" >&2
    cat "$tmpman" >&2
    fail=1
  fi
  rm -f "$tmpman"
  # README tie: every token the README claims as certified scope must
  # be in the manifest's ADEQUACY-EXPORTABLE set. Fail-closed: missing
  # markers or missing machine line are failures, not skips.
  readme_tokens="$(sed -n '/MANIFEST-SCOPE-BEGIN/,/MANIFEST-SCOPE-END/p' \
    cerberus-heaplang/README.md | sed -n 's/^tokens: //p')"
  allowed="$(sed -n 's/^ADEQUACY-EXPORTABLE: //p' "$manifest")"
  if [[ -z "$readme_tokens" ]]; then
    echo "FAIL: README MANIFEST-SCOPE token block missing/empty" >&2
    fail=1
  elif [[ -z "$allowed" ]]; then
    echo "FAIL: manifest ADEQUACY-EXPORTABLE line missing/empty" >&2
    fail=1
  else
    tie_ok=1
    for t in $readme_tokens; do
      hit=0
      for a in $allowed; do
        [[ "$t" == "$a" ]] && hit=1
      done
      if [[ $hit -eq 0 ]]; then
        echo "FAIL: README claims certified scope token '$t' but the" \
          "manifest does not list it as adequacy-exportable" >&2
        tie_ok=0
        fail=1
      fi
    done
    [[ $tie_ok -eq 1 ]] && echo "ok: README certified-scope tokens all" \
      "within the manifest's adequacy-exportable set"
  fi
fi

echo "== gate 5: statement-surface census freeze (pinned-export statement surfaces) =="
# Acceptance-suite slice (2026-09-01; the census's formerly
# registered future gate — Audit.lean header "Adjacent instruments",
# audit acceptance test 8's statement-surface arm): re-run the
# statement census and fail on any drift against the committed
# expected output. Load-bearing TRUST property: a statement-surface
# change to a pinned public export (its readout/spec vocabulary)
# cannot land silently — it forces a deliberate same-commit
# re-baseline of docs/STATEMENT_CENSUS.txt. Fail-closed: a missing
# committed file, a red generator run (e.g. a pinned theorem
# missing/renamed), and drift are each failures, never skips.
census=cerberus-heaplang/docs/STATEMENT_CENSUS.txt
if [[ ! -f "$census" ]]; then
  echo "FAIL: committed statement census missing ($census)" >&2
  fail=1
else
  tmpcen="$(mktemp "${TMPDIR:-/tmp}/statement_census.XXXXXX")" || {
    echo "FAIL: mktemp failed for census regeneration" >&2; exit 1; }
  if (cd cerberus-heaplang && \
      ../scripts/capped "$HOME/.elan/bin/lake" env lean \
        scripts/statement_census.lean > "$tmpcen"); then
    if diff -u "$census" "$tmpcen"; then
      echo "ok: statement census regenerated, no drift"
    else
      echo "FAIL: statement census drift (diff above) — a pinned" \
        "export's statement surface changed; re-baseline" \
        "docs/STATEMENT_CENSUS.txt deliberately, same commit" >&2
      fail=1
    fi
  else
    echo "FAIL: statement census generator red (a pinned theorem" \
      "missing or not a theorem); generator output:" >&2
    cat "$tmpcen" >&2
    fail=1
  fi
  rm -f "$tmpcen"
fi

if [[ $fail -ne 0 ]]; then
  echo "GATE FAILURE" >&2
  exit 1
fi
echo "ALL GATES GREEN"
