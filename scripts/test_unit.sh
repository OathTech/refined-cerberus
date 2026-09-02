#!/usr/bin/env bash
# refined-cerberus gate runner.
#
# TWO TIERS ([USER 2026-09-01] — the ACL2Lean two-tier gating policy,
# adopted to avoid gate cruft):
#   FULL  (default; THE CLAIM GATE): every check below. Required at
#         claim points — phase/arc exits, merge candidates, and any
#         commit that claims green.
#   FAST  (`--fast`; intermediate commits only): the HARD checks only
#         — gate 1, the affected package build(s) (gates 2/3), and the
#         manifest generator's HARD checks in check-only mode (gate 4h)
#         — with the SPEEDBUMPS skipped. A commit gated this way MUST
#         say `fast-gate` in its message; tiers may not masquerade.
#
# HARD vs SPEEDBUMP ([USER 2026-09-01]): a HARD gate is fail-closed
# in both tiers and exists to stop adversarial/unsound states — it is
# reserved for trust-load-bearing properties; a SPEEDBUMP catches
# drift/carelessness (report-and-require-regeneration bookkeeping) and
# runs in the FULL tier only. Classification of every check:
#
#   | Check                                              | Tier      | Why                                                          |
#   |----------------------------------------------------|-----------|--------------------------------------------------------------|
#   | gate 1  kernel-method grep ban                     | HARD      | non-kernel proof methods = unsound trust                      |
#   | gate 2  root build + in-build axiom sweep          | HARD      | sorry/axiom growth = unsound trust                            |
#   | gate 3  demo build + in-build axiom sweeps         | HARD      | same                                                         |
#   | gate 4h manifest HARD checks (generator throws):   | HARD      | the R-04 class: a construct claimed certified whose consumer  |
#   |         cone-derived row set + exact Step mirror   |           | cone lacks its rule, or a lane member without its launcher,   |
#   |         coverage; name/kind checks; PROOF-FLOW     |           | is the exact masquerade that let R-01 pass; the layer cut /   |
#   |         (rule/launcher/witness/prodRequires cones);|           | direct-reference ban is the R-02 bypass class; an unmapped    |
#   |         LAYER CUT + direct-reference ban; pruning  |           | Frag/Step constructor is silent coverage loss                 |
#   |         soundness assertion                        |           |                                                              |
#   | gate 4s manifest DRIFT (committed ≠ regenerated)   | SPEEDBUMP | bookkeeping: "did you regenerate the claims surface"          |
#   | gate 4s README certified-scope token tie           | SPEEDBUMP | claims-surface consistency (prose vs manifest), not soundness |
#   | gate 5  statement-census freeze                    | SPEEDBUMP | "did you notice a pinned statement surface changed"           |
#
# The HARD generator checks are separable from the regeneration:
# CAPABILITY_MANIFEST_CHECK_ONLY=1 makes the generator run every check
# and skip the rendering (same import + traversal cost; the drift
# diff is what is skipped). Measured cost (2026-09-01, P3): gate 4
# ≈ 130 s wall-clock, of which ≈ 88 s is the environment import and
# ≈ 40 s the memoized single-pass cone traversal (dependency table
# filled lazily once, shared by every row check and the layer cut).
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
t_start=$(date +%s)
gate_t0=$t_start
mark() {  # mark <label>: print the elapsed wall-clock of the gate just finished
  local now; now=$(date +%s)
  echo "   [$1: $((now - gate_t0)) s]"
  gate_t0=$now
}

if [[ $fast -eq 1 ]]; then
  echo "== TIER: FAST (--fast) — HARD checks only; SPEEDBUMPS skipped; the commit must say fast-gate =="
else
  echo "== TIER: FULL — the claim gate (HARD checks + speedbumps) =="
fi

echo "== gate 1 [HARD]: kernel-method grep ban =="
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
mark "gate 1"

# Affected packages (FAST tier): the package(s) with working-tree
# changes vs HEAD (tracked + untracked). Fail-closed: if nothing is
# detected as changed, BOTH are built (a no-op replay is cheap).
build_root=1
build_demo=1
if [[ $fast -eq 1 ]]; then
  changed="$( { git diff --name-only HEAD --; git ls-files --others --exclude-standard; } | sort -u)"
  if [[ -n "$changed" ]]; then
    build_root=0; build_demo=0
    if grep -qE '^(RefinedCerberus|lakefile|lake-manifest|lean-toolchain)' <<<"$changed"; then build_root=1; fi
    if grep -qE '^cerberus-heaplang/' <<<"$changed"; then build_demo=1; fi
    if [[ $build_root -eq 0 && $build_demo -eq 0 ]]; then
      echo "(fast tier: changes outside both packages — building both anyway, fail-closed)"
      build_root=1; build_demo=1
    fi
  fi
fi

echo "== gate 2 [HARD]: capped build, root package (elaborates its in-build axiom audit) =="
if [[ $build_root -eq 1 ]]; then
  if scripts/capped "$HOME/.elan/bin/lake" build; then
    echo "ok: root build green (axiom sweep + pins passed in-build)"
  else
    echo "FAIL: root build red" >&2
    fail=1
  fi
else
  echo "(fast tier: root package unaffected by the working-tree changes — skipped)"
fi
mark "gate 2"

echo "== gate 3 [HARD]: capped build, cerberus-heaplang demo (its own audit rides) =="
if [[ $build_demo -eq 1 ]]; then
  if (cd cerberus-heaplang && ../scripts/capped "$HOME/.elan/bin/lake" build); then
    echo "ok: cerberus-heaplang build green (axiom sweep + pins passed in-build)"
  else
    echo "FAIL: cerberus-heaplang build red" >&2
    fail=1
  fi
else
  echo "(fast tier: demo package unaffected by the working-tree changes — skipped)"
fi
mark "gate 3"

# Foundations arc (2026-08-31 audit F-01/F-09; Phase 0, upgraded to
# the CONE-DERIVED form in Phase-1 S1c, to the DEPENDENCY-CERTIFIED
# form in alloc arc P3 — the 2026-09-01 re-audit's R-04): the
# generated capability manifest is THE authoritative per-construct
# scope statement, and its row set is DERIVED from the unified cone
# — the generator enumerates `Frag`'s constructors out of the built
# environment (a cone constructor without a row mapping is a
# generator throw) and derives `Step` mirror coverage the same way
# (every Step constructor must be claimed by exactly one row). Since
# P3 the generator additionally THROWS unless every listed consumer
# is dependency-certified in the built environment — its proof cone
# contains the row's public rule and its lane's approved adequacy
# launcher (production consumers also the row's required
# abstractions, e.g. wpt_create + launchResources for create), its
# statement contains the construct's syntax through program-valued
# definitions — and unless the LAYER CUT holds over every declaration
# of the positive-exhibit modules (no path to Step.*/the engine-round
# projections/driveJ_step/driverDone_step except through the
# logic/adequacy layer; no direct reference). Those throws are the
# HARD part (gate 4h, both tiers). The FULL tier additionally (a)
# regenerates the manifest and fails on any drift against the
# committed copy, and (b) ties the README's certified-scope token
# list to the manifest's ADEQUACY-EXPORTABLE set (gate 4s, both
# SPEEDBUMPS). Plant transcripts:
# cerberus-heaplang/docs/2026-09-01_p3-notes.md.
manifest=cerberus-heaplang/docs/CAPABILITY_MANIFEST.md
if [[ $fast -eq 1 ]]; then
  echo "== gate 4h [HARD]: capability manifest HARD checks (check-only; drift/README tie skipped) =="
  if (cd cerberus-heaplang && \
      CAPABILITY_MANIFEST_CHECK_ONLY=1 ../scripts/capped "$HOME/.elan/bin/lake" env lean \
        scripts/capability_manifest.lean); then
    echo "ok: manifest HARD checks passed (dependency certification + layer cut)"
  else
    echo "FAIL: capability manifest HARD checks red (an unmapped Step/Frag" \
      "constructor, a missing checked name, a dependency-certification" \
      "failure, or a layer-cut violation) — output above" >&2
    fail=1
  fi
  mark "gate 4h"
else
  echo "== gate 4 [HARD 4h + SPEEDBUMP 4s]: capability manifest (dependency-certified; drift + README certified-scope tie) =="
  if [[ ! -f "$manifest" ]]; then
    echo "FAIL: committed capability manifest missing ($manifest)" >&2
    fail=1
  else
    tmpman="$(mktemp "${TMPDIR:-/tmp}/capability_manifest.XXXXXX")" || {
      echo "FAIL: mktemp failed for manifest regeneration" >&2; exit 1; }
    if (cd cerberus-heaplang && \
        ../scripts/capped "$HOME/.elan/bin/lake" env lean \
          scripts/capability_manifest.lean > "$tmpman"); then
      echo "ok: manifest HARD checks passed inside the regeneration (gate 4h)"
      if diff -u "$manifest" "$tmpman"; then
        echo "ok: capability manifest regenerated, no drift (gate 4s)"
      else
        echo "FAIL (speedbump 4s): capability manifest drift (diff above) — regenerate" \
          "docs/CAPABILITY_MANIFEST.md deliberately, same commit" >&2
        fail=1
      fi
    else
      echo "FAIL (HARD 4h): capability manifest generator red (an unmapped Step/Frag" \
        "constructor, a missing checked name, a dependency-certification" \
        "failure, or a layer-cut violation); generator output:" >&2
      cat "$tmpman" >&2
      fail=1
    fi
    rm -f "$tmpman"
    # README tie (SPEEDBUMP 4s): every token the README claims as
    # certified scope must be in the manifest's ADEQUACY-EXPORTABLE
    # set. Fail-closed: missing markers or missing machine line are
    # failures, not skips.
    readme_tokens="$(sed -n '/MANIFEST-SCOPE-BEGIN/,/MANIFEST-SCOPE-END/p' \
      cerberus-heaplang/README.md | sed -n 's/^tokens: //p')"
    allowed="$(sed -n 's/^ADEQUACY-EXPORTABLE: //p' "$manifest")"
    if [[ -z "$readme_tokens" ]]; then
      echo "FAIL (speedbump 4s): README MANIFEST-SCOPE token block missing/empty" >&2
      fail=1
    elif [[ -z "$allowed" ]]; then
      echo "FAIL (speedbump 4s): manifest ADEQUACY-EXPORTABLE line missing/empty" >&2
      fail=1
    else
      tie_ok=1
      for t in $readme_tokens; do
        hit=0
        for a in $allowed; do
          [[ "$t" == "$a" ]] && hit=1
        done
        if [[ $hit -eq 0 ]]; then
          echo "FAIL (speedbump 4s): README claims certified scope token '$t' but the" \
            "manifest does not list it as adequacy-exportable" >&2
          tie_ok=0
          fail=1
        fi
      done
      [[ $tie_ok -eq 1 ]] && echo "ok: README certified-scope tokens all" \
        "within the manifest's adequacy-exportable set (gate 4s)"
    fi
  fi
  mark "gate 4"

  echo "== gate 5 [SPEEDBUMP]: statement-surface census freeze (pinned-export statement surfaces) =="
  # Acceptance-suite slice (2026-09-01; the census's formerly
  # registered future gate — Audit.lean header "Adjacent instruments",
  # audit acceptance test 8's statement-surface arm): re-run the
  # statement census and fail on any drift against the committed
  # expected output. A statement-surface change to a pinned public
  # export (its readout/spec vocabulary) cannot land silently — it
  # forces a deliberate same-commit re-baseline of
  # docs/STATEMENT_CENSUS.txt. Fail-closed within its tier: a missing
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
        echo "FAIL (speedbump): statement census drift (diff above) — a pinned" \
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
  mark "gate 5"
fi

echo "   [total: $(( $(date +%s) - t_start )) s]"
if [[ $fail -ne 0 ]]; then
  echo "GATE FAILURE" >&2
  exit 1
fi
if [[ $fast -eq 1 ]]; then
  echo "FAST-GATE GREEN (HARD checks only — not a claim-point result; say fast-gate in the commit)"
else
  echo "ALL GATES GREEN"
fi
