#!/usr/bin/env bash
# boundary_check.sh — THE NEGATIVE ARCHITECTURAL CHECK (a claim-point
# SPEEDBUMP, [USER 2026-09-02] "speedbumps, not adversarial gates"; landed
# at ar5-manifest 2026-09-04 as the external audit's remediation 3:
# docs/2026-09-04_reynolds-ohearn-separation-logic-audit.md, Finding 2).
#
# WHAT IT CHECKS: a module classified `positive-client`, `declared-smoke`
# or `example-support` in cerberus-heaplang/scripts/module_classes.tsv (the
# one authoritative module classification) must not MENTION, outside
# comments, any of the logic's internals: the coupling invariant and the
# state interpretation (`CohG`, `metaInterp`, `byteInterp`, `cursorInterp`,
# `budgetInterp`, `budgetAuth`, `stateInterp_iff`/`_eq`), the judgment
# unfoldings (`wps.pre`, `wpt.pre`, `wps_unfold`, `wpt_unfold`), the mirror
# transition (`Step.<constructor or lemma>`), and the generated engine's
# transition / driver definitions (`step_ctx`, `one_step0`, `step_action`,
# `drive_nonmemory_steps*`, `driver2`, `loop_step_frag*`,
# `engine_step_matchU`, `CerberusRound`/`cerberusRound*`). A client reasons
# through the public rules (API.lean); a mention of an internal is a
# finding about the public surface, remedied by a new PUBLIC lemma.
# Modules of every other class are EXEMPT by classification (semantic-test,
# engine-mirror-test, production-wrapper, negative-test name the transition
# or the driver lane by design; core/production-core/audit ARE the logic).
#
# HOW: block comments (nested) and `--` line comments are stripped (perl),
# then `grep -nE` for the pattern. TEXT-BASED: it catches honest drift
# (a helper written over `CohG` in an exhibit), not an adversary; the
# proof-term measurement is scripts/parametric_inventory.lean (on demand).
#
# ALLOWLIST: a module whose `internals-allow` cell in the TSV is not `-`
# has its CURRENT hits tolerated (printed as ALLOWLISTED with the reason);
# an allowlisted module with NO hits left prints a WARNING to remove the
# entry (not red — so the check is green on either ordering of the slice
# that removes the hits and the slice that removes the entry).
#
# EXIT: 0 = no unallowlisted hit; 1 = a hit in a checked module without
# an allowance, a checked module's source file missing, a malformed TSV,
# or an empty checked set (fail-closed, fail-noisy).
#
# Run from the repository root:  scripts/boundary_check.sh
set -euo pipefail
cd "$(dirname "$0")/.."

tsv=cerberus-heaplang/scripts/module_classes.tsv
[[ -f "$tsv" ]] || { echo "boundary FAIL: $tsv missing" >&2; exit 1; }

pattern='\b(CohG|metaInterp|byteInterp|cursorInterp|budgetInterp|budgetAuth|stateInterp_iff|stateInterp_eq|wps\.pre|wpt\.pre|wps_unfold|wpt_unfold|step_ctx|one_step0|step_action|drive_nonmemory_steps[A-Za-z0-9_]*|driver2|loop_step_frag[A-Za-z0-9_'"'"']*|engine_step_matchU|CerberusRound|cerberusRound[A-Za-z0-9_]*)\b|\bStep\.[A-Za-z_][A-Za-z0-9_'"'"']*'

# strip nested block comments (keeping their newlines, so reported line
# numbers are the source's) and -- line comments
strip() {
  perl -0777 -pe 's{/-(?:[^/-]|/(?!-)|-(?!/)|(?R))*-/}{ ($& =~ tr/\n//cdr) }gse; s{--[^\n]*}{}g' "$1"
}

fail=0; checked=0; hits_total=0
while IFS=$'\t' read -r module cls allow note; do
  [[ -z "$module" || "$module" == \#* ]] && continue
  case "$cls" in
    positive-client|declared-smoke|example-support) ;;
    core|production-core|audit|semantic-test|engine-mirror-test|production-wrapper|negative-test) continue ;;
    *) echo "boundary FAIL: $tsv: module $module has unknown class '$cls'" >&2; fail=1; continue ;;
  esac
  file="cerberus-heaplang/${module//./\/}.lean"
  if [[ ! -f "$file" ]]; then
    echo "boundary FAIL: classified module $module has no source file $file" >&2; fail=1; continue
  fi
  checked=$((checked+1))
  hits="$(strip "$file" | grep -nE "$pattern" || true)"
  n=0; [[ -n "$hits" ]] && n="$(printf '%s\n' "$hits" | wc -l)"
  hits_total=$((hits_total+n))
  short="${module#CerberusHeapLang.}"
  if [[ $n -eq 0 ]]; then
    if [[ "$allow" != "-" ]]; then
      echo "ok:   $short — 0 internals mentions; WARNING: allowlist entry unused, remove it ($allow)"
    else
      echo "ok:   $short — 0 internals mentions"
    fi
  elif [[ "$allow" != "-" ]]; then
    echo "ALLOWLISTED: $short — $n internals mention(s): $allow"
    printf '%s\n' "$hits" | sed "s|^|      $short:|"
  else
    echo "FAIL: $short — $n internals mention(s) in a $cls module (no allowance):" >&2
    printf '%s\n' "$hits" | sed "s|^|      $short:|" >&2
    fail=1
  fi
done < "$tsv"

if [[ $checked -eq 0 ]]; then echo "boundary FAIL: no module checked (TSV empty of client classes?)" >&2; exit 1; fi
echo "BOUNDARY: $checked modules checked, $hits_total internals mention(s) in total, exit=$fail"
exit $fail
