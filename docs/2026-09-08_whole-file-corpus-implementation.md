# Whole-file corpus implementation record

Status: IN PROGRESS on `demo-whole-file-corpus`, main baseline `4bc0a98`.
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
