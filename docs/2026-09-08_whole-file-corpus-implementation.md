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
