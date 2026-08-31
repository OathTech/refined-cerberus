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
