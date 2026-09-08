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

Verbatim verdict excerpts (ignored log `.lake/whole-file-evidence/phase-a-fast.log`):

```text
info: CerberusHeapLang/Audit.lean:1137:0: CerberusHeapLang export pins: 917 trio-exact, 6 axiom-free-exact
Build completed successfully (490 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

This is an intermediate build result. Full frontend checks, additional
representation-proof pins, claim surfaces, and fresh range review follow.

## Phase B — integration and verification plan

Comparator worker commits `7c36b18` and `cd45c3f` supply the independent
constructor comparison and the capture/inspection speedbump. The former was
cherry-picked as `4920268`; the latter's two scripts were extracted because
its branch already contained the old G2 wrapper. The unchanged G2
loader/quoter/inspector and retained Cabs were adopted explicitly from
`5bfe992`. Parent verification follows below; worker success is not the
claim-point result.

The shipped interface is an additive
`CorpusA7.T1.certified_production_shipped`. The actual existing name is
`t1_certified_production_shipped` (the charter abbreviated it as
`t1_shipped`); its old wrapper contract is preserved and labelled regression,
so no replacement alias or changed existing statement is needed.
The corpus table is a text/transcription regression table, not a certificate
name table: its shape and entries stay intact, with its t1 role clarified.

The representation audit now asserts seven exact `[propext]` cones and the
axiom-free fold transfer, as measured by `#print axioms`. These are subsets
of the existing trust bound, not new boundary axioms. The new execution
corollary is pinned separately. The exhaustive and banned-axiom sweeps
remain unchanged.

Parent integrated fast gate, 2026-09-08, exited 0. Verbatim verdict excerpts
from `.lake/whole-file-evidence/phase-b-fast.log`:

```text
info: CerberusHeapLang/Audit.lean:1152:0: CerberusHeapLang export pins: 918 trio-exact, 7 propext-exact, 7 axiom-free-exact
Build completed successfully (490 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```
