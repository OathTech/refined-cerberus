# Whole-file t1 implementation record

Status: IN PROGRESS on `demo-whole-file-t1`; no merge or push authorized.
Charter: [whole-file t1](2026-09-07_whole-file-t1-charter.md).
Baseline main `7040406`; proposal `969281f`; charter/baseline `5bcbdd1`.

## Phase A — proof port

Re-cut G2 `520654f..5bfe992` onto current main. No G3 scheduler work,
provider edits, dependency changes, or edits to the frozen proof core.
The current driver-step proof body retains D7's shared head derivations.
The generalized rounds and allocation launcher use syntactic `Frag` with
explicit `evalDepth`; internal induction helpers use `FragFuel`. Existing
empty-extern contracts specialize the generalized implementation.

The complete-file client has fuel-independent `mainBody_frag` and separate
`mainBody_evalDepth`. Its memory-value witnesses are local, and its tuple
update uses the existing generic `update_env_tuple2_mixed`; it needs no
import of the legacy t1 wrapper exhibit.

Validation, 2026-09-08, from this worktree (all Lean commands capped):

```sh
CERB_MEM_MAX=40G TMPDIR="$PWD/.tmp" scripts/test_unit.sh --fast
```

Verbatim final lines (ignored log `.lake/whole-file-evidence/phase-a-fast.log`):

```text
CerberusHeapLang export pins: 917 trio-exact, 6 axiom-free-exact
Build completed successfully (490 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

This is an intermediate build result. Full frontend checks, additional
representation-proof pins, claim surfaces, and fresh range review follow.
