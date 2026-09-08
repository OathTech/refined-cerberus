# Whole-file corpus implementation record

Status: IMPLEMENTED and fully verified on `demo-whole-file-corpus`, main
baseline `4bc0a98`; fresh final independent review pending.
Charter: [whole-file corpus](2026-09-08_whole-file-corpus-charter.md).
No merge or push authorized. All `.lake/whole-file-corpus-evidence/` paths
are relative to this feature worktree root; ignored logs are ephemeral.
This committed record and snapshots retain the useful evidence.

## Baseline

The new worktree was created by `scripts/new-worktree.sh` from main.
Its pinned workspace and package Lake cache were copied from the verified
primary checkout; `scripts/setup-cerberus-dep.sh --check` passed, including
the pin/stamp and 37 hand-written seams. No sibling repository was edited.

Full gate, from feature root:

```bash
CERB_MEM_MAX=40G TMPDIR="$PWD/.tmp" scripts/test_unit.sh \
  > .lake/whole-file-corpus-evidence/baseline-gate.log 2>&1
```

Exit0. Selected verbatim output:

```text
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang export pins: 918 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6816 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (10261 constants of every kind swept, internal details included — count informational, environment-dependent)
ALL GATES GREEN
```

DERIVED: 66 demo warning occurrences / 33 distinct, the existing baseline.
The subsequent capped `lake env lean scripts/signature_snapshot.lean`
produced `cerberus-heaplang/docs/2026-09-08_whole-file-corpus-baseline.txt`:
5,569 declarations, byte-identical to the committed t1 final snapshot.

The proposal and t5 scout were adopted from the separate scout branch
`2f180e8`; fresh t4/t6 JSON reports are preserved under
`docs/evidence/2026-09-08_whole-file-expansion/`. They establish executable
feasibility, not the new theorems. Pre-launch review precedes source work.

## Shared support checkpoint

Pre-launch review `bf88f83` (adopted as `8299988`) is PASS with Notes;
the charter clarification at `f6045fd` records arbitrary fs/arguments.
The comparison-based `wpt_neg_bound_compare` replaces the sole strong
extern-identity use with a checked frame lookup. The old theorem is a
specialization with its signature preserved. `EmittedIntSupport` adds a
typed, fully annotated binder/load rule at arbitrary fraction and exact
footprint; a signed-int assignment face with evaluated operands; annotated
integer memory facts and symbol evaluation. Existing t1 now consumes the
common symbol/type facts with unchanged theorem statements.

Targeted module builds passed; six public interfaces were measured to
have the exact classical trio and added to Audit. The subsequent full
library fast gate passed. Selected verbatim output:

```text
info: CerberusHeapLang/Audit.lean:1160:0: CerberusHeapLang export pins: 924 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1160:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6829 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1160:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (10276 constants of every kind swept, internal details included — count informational, environment-dependent)
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

Logs: `shared-fast-gate.log`, `shared-axioms.log`, `int-support.log`,
`wpt-compare-4.32.2.log` in the root evidence directory. A first targeted
invocation incorrectly ran Lake from the repo root with `--dir`, selecting
the machine's4.33 toolchain; it failed in dependencies and was interrupted.
Its caches were moved aside, correct caches restored from verified main,
the pinned workspace rechecked, and all successful builds above ran from
the package directory at4.32.2. No wrong-toolchain result is counted as
evidence; no source pin or sibling repository changed.

## Literal operands and exact body checkpoints

The actual frontend uses literal `PEval` operands where the earlier wrappers
used constructed values. `EmittedIntSupport.wpt_unseq_value_right` exposes
the derived unsequenced rule for a right operand already in value form,
retaining annotations and merged footprints. It charges the left proof
budget plus three completion units. `symPe` is an abbreviation to match
existing symbol syntax transparently. Its public type is unchanged.

Parent independently built the adopted t5 and t6 data/body shape modules
(`665a0f5`, `a9c6ba0`) alongside this helper. The subsequent fast gate
passed; selected verbatim output (`value-right-fast-gate.log`):

```text
info: CerberusHeapLang/Audit.lean:1161:0: CerberusHeapLang export pins: 925 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1161:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6830 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1161:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (10277 constants of every kind swept, internal details included — count informational, environment-dependent)
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

The t5/t6 modules are not yet root imports at this checkpoint; their
separate targeted builds, not this sweep, verify those data/body facts.
Program total proofs remain in progress.

## t5/t6 integration and four-file comparison checkpoint

Green worker commits adopted: t5 `5f2c045` as `73200a4`; t6 `eaf2e15`
as `864937a`. T4's exact body/continuation and public comparison checkpoint
`b30ac7d` is adopted as `312d6e2`; its loop proof remains in progress.
Parent independently built T4's checkpoint, then the integrated library
with t5/t6 shipped corollaries, exact audit pins and all new module classes.
The fast gate passed (`t5-t6-integration-fast.log`); selected verbatim output:

```text
✔ [495/500] Built CerberusHeapLang.EmittedT6Exhibit (8.4s)
✔ [496/500] Built CerberusHeapLang.EmittedT5Exhibit (11s)
info: CerberusHeapLang/Audit.lean:1213:0: CerberusHeapLang export pins: 971 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1213:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (7195 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1213:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (10907 constants of every kind swept, internal details included — count informational, environment-dependent)
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

The consolidated `scripts/check-emitted-corpus.sh` completed successfully
for t1/t5/t6/t4, independently of the new total proofs. It regenerates
Cabs from each exact relative C source path; checks retained data by the
independent structural comparator and quotation; checks original comparator
paths on the same frontend instance; checks exact supplies and intended
main/supply perturbations. Selected verbatim output (`corpus-comparison.log`):

```text
ok: whole-file t1 — metadata, all three comparator checks and singleton return 4 checked
ok: whole-file t1 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t5 — metadata, all three comparator checks and singleton return 1 checked
ok: whole-file t5 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t6 — metadata, all three comparator checks and singleton return 20 checked
ok: whole-file t6 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t4 — metadata, all three comparator checks and singleton return 10 checked
ok: whole-file t4 — independent structural data, quotation, supply and negative checks passed
```

The observed producer hash/version match the fixture README. The full gate
now calls the cohort runner; the original t1-only command is a compatibility
wrapper. `--fast` still excludes these executable comparisons. The existing
main/supply and structural-comparator selftests are reused without adding
a new certification mechanism. T6's worker also read the runner independently
and found no substantive issue; it suggested the adopted wording "captured
Core producer" to avoid implying frontend certification.

The client-boundary report passed all44 modules with zero internal mentions.
The capability manifest was deliberately regenerated, including the new
derived sequencing/assignment names. This is an intermediate fast-gate plus
selected speedbump checkpoint; the full final gate, signature census, final
doc claims and fresh adversarial review remain required for the candidate.

## Complete cohort verification before final review

T4's loop checkpoint `1c8275e` and final complete-file checkpoint
`2584247` were adopted as `676dd97` and `bee59b7`. Parent independently
built the complete T4 module (14 seconds) and all final integration.
The total budgets are 48/88/78/915 for t1/t5/t6/t4, with the driver
margin giving 50/90/80/917. Exact captured supplies are 36/47/51/92.
Every new production/capture twin quantifies filesystem and arguments.
The T5/T4 body proofs protect their two live source pointers using
`22 < M.runState.sym_supply`. T6's label contracts and driver proof use
the sufficient bound `51 ≤ M.runState.sym_supply`; its `mainBody_wpt`
jumps into the label contract without a separate supply premise. Each
exported equation discharges its bound at the exact captured supply.
Actual annotations, cell types, save contexts and cleanup
are retained. T4's invariant and decreasing budget are in its public proof.

Shared arithmetic required no new evaluator: the actual T1 and T4
`addBranch_eval` proofs both consume the existing annotation-parametric
`IntRules.evalPexpr_conv_int_int` and `evalPexpr_catch_add_int`. Their
operands and signed-range premises are explicit and their file/environment
are unrestricted. This intrinsic conversion/catch route is distinct from
captured-library calls discharged through `EmittedStdCore.HasIntLibrary`.
The shared load, assignment, symbol, memory and literal-right sequencing
helpers have multiple actual consumers. An independent read-only check by
the completed t5 worker confirmed this arithmetic reuse; no additional
framework or duplicated semantics was needed.

Final commands (Lean/Lake run from the package directory, all capped40G):

```bash
# From cerberus-heaplang, with CERB_MEM_MAX=40G and TMPDIR in the worktree:
../scripts/capped ~/.elan/bin/lake env lean scripts/capability_manifest.lean > docs/CAPABILITY_MANIFEST.md
../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean > docs/2026-09-08_whole-file-corpus-final.txt
# From the worktree root:
CERB_MEM_MAX=40G TMPDIR="$PWD/.tmp" scripts/test_unit.sh > .lake/whole-file-corpus-evidence/full-final-gate.log 2>&1
```

The full gate exited0. Selected verbatim output:

```text
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang export pins: 991 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (7356 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (11097 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: import direction — 19 core modules, none imports an exhibit/example/production module
BOUNDARY: 44 modules checked, 0 internals mention(s) in total, exit=0
ALL GATES GREEN
```

All four fresh Cabs/data/supply/comparator/negative/outcome checks passed
again in this full run. The regenerated manifest reports 47 RULE, zero
undemonstrated rule rows, 24 NO-RULE, 7 OUT-OF-SCOPE, zero red and
30 consumer modules. Its claim-name check covers 19 rows, 219 theorem-cell
names and 376 declaration-shaped spans. DERIVED: 165 demo warning
occurrences / 33 distinct, unchanged distinct baseline (one library build
and four nested comparison builds replay the same warnings).

The committed signature census compares exact kind/name/pretty-printed
type blocks: baseline 5,569, final 6,081, ADDED512, REMOVED0, CHANGED0.
Every previous public signature is unchanged, including the original
negative-assignment theorem and all four wrapper/shipped statements.
The old `600` census remains 18 code sites: 15 named hsup premises
(including the later partial corollary), plus three shipped premises.
The master plan keeps their restatement and named fuel costs in V1-4a.

Pin/contract diff against main4bc0a98 is empty for the semantics pin,
Lean toolchain, Lake manifest/dependency declarations, and frozen
Step/Round/Soundness/Fragment/Heap/Lang/Wps/ProdEntry/ProdLoop files.
Primary main remains clean at4bc0a98. All writes stayed in this repository;
no merge, push or tag occurred. The only core rule edit is the named
comparison-premise generalization in Wpt, with the old API preserved.

Citation reports ran on eight detailed claim/plan documents plus the root
and fixture READMEs, all exit0
and no NOFILE entries. The source anchors moved in this slice were checked
and corrected (Wpt, Shipped, Audit, the corpus wrapper rows, gate script
and manifest). Existing heuristic/manual queues remain disclosed in KOI;
we do not call them an empty queue. Final report tallies:

| Document | EXACT | DECL | USE | HAND | PIN |
|---|---:|---:|---:|---:|---:|
| ARCHITECTURE | 250 | 17 | 12 | 23 | 13 |
| README (package) | 31 | 0 | 1 | 1 | 11 |
| FUEL | 55 | 9 | 2 | 3 | 21 |
| WALKTHROUGH | 1 | 1 | 0 | 0 | 1 |
| KNOWN-OPEN-ITEMS | 5 | 2 | 0 | 0 | 4 |

CLAIMS, master plan, requests register and the root/fixture READMEs
contain no parsed file:line cites. The README manifest-tail citation was checked directly at line199;
the heuristic attributes it to an earlier PtrEq identifier.

The whole V1-1 option-(b) implementation is now a green candidate. A
fresh adversarial full-range review remains required before pausing for
external review. No review verdict or merge authorization is inferred
from the successful build.
