# cerberus-heaplang restructure notes (2026-08-31)

[USER 2026-08-31] mission: the spike (branch `spike-minilog`,
records under `docs/2026-08-30_spike-*.md` here) becomes a
standalone DEMO Lean development — "call it something like
Cerberus-heaplang… make it a separate Lean development" — alongside
the future RefinedC port, whose home remains the repo's root
`RefinedCerberus` package. This note records the mechanics and the
re-run gate evidence.

## What moved (mechanical only)

- `RefinedCerberus/Spike/*.lean` → `CerberusHeapLang/*.lean` (this
  package), namespace `RefinedCerberus.Spike` → `CerberusHeapLang`
  by textual rename; ZERO proof-content changes — the first build
  after the rename was green with the sweep count unchanged modulo
  the two root smoke lemmas (root 287 = 285 here + smoke +
  semantics_smoke, derived tally).
- The spike docs moved here unchanged; a one-line stub remains at
  the old plan path.
- The audit split: this package's `CerberusHeapLang/Audit.lean`
  carries the spike's full curated pin set + the module-scoped
  `runEffectful` boundary (now `CerberusHeapLang.ProdEntry` /
  `CerberusHeapLang.ProdExhibit`) + the [USER 2026-08-31] upstream-
  retirement note; the root `RefinedCerberus/Audit.lean` is slimmed
  to the pre-spike pins (smoke, semantics_smoke — the latter
  re-baselined to its actual `[propext]` cone, entering via the
  statement's `CerbMem.overlapping` definition cone) and a trio-only
  sweep with NO boundary.

## Boundary-gate plant test, re-run after the move (both directions)

Direction 1 — a `runEffectful`-carrying theorem OUTSIDE the boundary
modules (planted at the end of `CerberusHeapLang/Exhibit.lean`:
`theorem plant_boundary_leak {α : Type} (t : Unit → BaseIO α) :
runEffectful t = runEffectful t := rfl`). Build output (verbatim):

```
error: CerberusHeapLang/Audit.lean:201:0: CerberusHeapLang axiom sweep FAILED: theorem CerberusHeapLang.plant_boundary_leak carries axiom runEffectful, outside the declared boundary [propext,
 Classical.choice,
 Quot.sound]. Either the proof is wrong (sorry / a non-kernel method) or a boundary decision is being made implicitly — boundary changes happen in Audit.lean, same commit, with provenance.
error: Lean exited with code 1
Some required targets logged failures:
- CerberusHeapLang.Audit
error: build failed
```

Direction 2 — a sorry INSIDE a boundary module (planted at the end
of `CerberusHeapLang/ProdExhibit.lean`:
`theorem plant_sorry_in_boundary : True := sorry`). Build output
(verbatim):

```
error: CerberusHeapLang/Audit.lean:201:0: CerberusHeapLang axiom sweep FAILED: theorem CerberusHeapLang.plant_sorry_in_boundary carries axiom sorryAx, outside the declared boundary [propext,
 Classical.choice,
 Quot.sound,
 runEffectful]. Either the proof is wrong (sorry / a non-kernel method) or a boundary decision is being made implicitly — boundary changes happen in Audit.lean, same commit, with provenance.
error: Lean exited with code 1
Some required targets logged failures:
- CerberusHeapLang.Audit
error: build failed
```

Both plants reverted; the post-revert build is green (verbatim):

```
info: CerberusHeapLang/Audit.lean:201:0: CerberusHeapLang axiom sweep: 285 theorems within the declared boundary (34 in the production-entry boundary modules, trio + runEffectful; all others trio-exact)
Build completed successfully (424 jobs).
```

## Dependency wiring

Same pins as the root package (require blocks copied verbatim);
`CerberusLean` via path `../.cerberus-ws/lean_frontend` (the shared
pinned+primed workspace; pin in `scripts/semantics-pin.env`, bumped
to 07a7fca29 this slice). The manifest was generated fully offline
(`GIT_CONFIG_GLOBAL=<container>/deps/gitconfig lake update` — all
four git deps resolved through the local redirects; no network);
the dep clones were primed from the root package's built
`.lake/packages` (same revs, olean reuse — the house offline
priming pattern).

## 2026-08-31 (merge-audit fixes): the banned-axiom sweep over every constant kind, plant-tested

[AGENT 2026-08-31] The merge audit
(`../../docs/2026-08-31_heaplang-merge-audit.md`, finding 3) planted
`def plant_def_sorry_audit : Nat := sorry` and rode a green build:
the exhaustive sweep checked only `thmInfo` constants, so a hole in
a bare definitional artifact referenced by no theorem escaped —
and the demo's claim surface includes bare defs (`drive`,
`prodFile`, `prodMem₀`). Fix: BOTH packages' `Audit.lean` sweeps
gained a second pass over ALL constants of our modules (every
constant kind, not just theorems): any cone containing `sorryAx`,
`ofReduceBool`, or `ofReduceNat` fails the build. Trio-bounding
stays theorems-only (pass 1); pass 2 is the banned-axiom check for
every constant kind.

Plant test, both directions, this package (the audit's own plant
re-planted):

Direction RED — `def plant_def_sorry_audit : Nat := sorry` at the
end of `CerberusHeapLang/Exhibit.lean`. Build output (verbatim,
lines relevant to the gate):

```
warning: CerberusHeapLang/Exhibit.lean:803:4: declaration uses `sorry`
✖ [422/424] Building CerberusHeapLang.Audit (1.1s)
info: CerberusHeapLang/Audit.lean:208:0: CerberusHeapLang axiom sweep: 285 theorems within the declared boundary (34 in the production-entry boundary modules, trio + runEffectful; all others trio-exact)
error: CerberusHeapLang/Audit.lean:208:0: CerberusHeapLang banned-axiom sweep FAILED: constant CerberusHeapLang.plant_def_sorry_audit carries banned axiom sorryAx. sorryAx / ofReduceBool / ofReduceNat are never in any boundary, for ANY constant kind — a def-level hole is still a hole; remove it (there is no register route for these).
error: Lean exited with code 1
Some required targets logged failures:
- CerberusHeapLang.Audit
error: build failed
```

Direction GREEN — plant reverted; build output (verbatim):

```
info: CerberusHeapLang/Audit.lean:208:0: CerberusHeapLang axiom sweep: 285 theorems within the declared boundary (34 in the production-entry boundary modules, trio + runEffectful; all others trio-exact)
info: CerberusHeapLang/Audit.lean:208:0: CerberusHeapLang banned-axiom sweep: 589 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (424 jobs).
```

The root package's pass reports (verbatim):
`RefinedCerberus banned-axiom sweep: 3 constants of every kind
checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones`
(derived tally: the 2 smoke theorems + the audit file's own
`allowedAxioms` def — a small package; the plant mechanism is
identical code and was exercised in the demo package above).

Engine-side observation, from the audit (theirs to fix, recorded
here for the trust story): the pinned engine itself carries a
data-level sorry — `(sorry : String)` inside the concurrency-model
debug-log message of `auxAddToRfLoad` (`generated/Cmm_op.lean`, def
at :283; the sorry expressions at :292 in this checkout), in the
parked cmm instantiation (engine TODO.md). It is provably outside
every demo cone: the audit's 14 cone probes are trio(-+runEffectful)
exact, and the new banned-axiom pass — green over all 589 demo
constants, whose cones traverse the engine definitions they use —
confirms no demo constant reaches it. An engine-repo concern, owned
by the cerberus-lean register, not this package.
