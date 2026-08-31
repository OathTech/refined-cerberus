# Foundations arc — slice notes

Arc plan: `2026-08-31_foundations-arc-plan.md`; work order: the
foundational audit
(`2026-08-31_cerberus-heaplang-foundational-audit.md` — the
findings F-01..F-10 cited below are its numbering). RECORD FIX
[AGENT, this slice]: the arc-plan commit's message says "audit doc
committed", but no commit on any branch carried the file — it
existed only in the primary checkout's working tree
(`refined-cerberus/docs/`). It is committed HERE, verbatim
(sha256 `7339d338…ad7435` matches the working-tree original), at
the path the arc plan's header cites.

## Phase 0 — claims corrected, coverage gated (this slice)

Worker slice, [AGENT] execution of the Phase-0 plan section as
briefed by the orchestrator. Docs + one instrument + one gate; ZERO
proof-content changes (proof below: the signature-snapshot diff).

### Fix list, by audit finding

- **F-01 (claims half)** — value-scrutinee `Ecase` OUT of the
  certified scope everywhere:
  - README certified-fragment enumeration: `Ecase` removed from the
    list; explicit LOCAL-RULE-ONLY paragraph added ("not
    adequacy-exportable — RED in the manifest until Phase 1 exports
    it"); Step.lean module row tagged "(local rule only —
    manifest)".
  - README divergence register: new row for the value-scrutinee
    `Ecase` cone gap (previously only the EVAL arm was registered).
  - `Step.lean` header SCOPE paragraph: the local-rule-only status
    stated at source, with the F-01 citation.
  - The capability manifest row for `Ecase` is RED at cone /
    partial-adequacy / consumer (Notes 1 there); the RED is CHECKED,
    not narrated — the generator asserts the full `FragJ`
    constructor list, which has no case entry.
  - Structural export (cone constructor + decompJ/match extension +
    adequacy regression) is Phase 1, per the plan.
- **F-02 (claims half)** — `fib_certified_total` reclassified as an
  OPERATIONAL ENGINE THEOREM on every surface; the variant-rule
  narrative removed from all claims surfaces:
  - README exhibit table row, "Scope of the claims" passage, and
    FibExhibit module row: now state the proof is a direct
    operational induction (explicit `Step`/`driveJ_step` rewrites),
    consuming neither `fib_wps` nor `blockSpecs_intro_variant` nor
    any total WP; "the loop variant's step bound" phrasing replaced
    by "the concrete step bound 2·n+4" everywhere.
  - README Wps module row: `blockSpecs_intro_variant` described
    honestly (optional smaller-measure hypotheses, NO termination
    consequence, no consumer; total lane is Phase 3).
  - Walkthrough §3.1 ("invariant-plus-variant rule for total loops"
    — deleted; replaced by the honest partial-correctness-only
    statement), §3.2 partial-correctness bullet, §5.1 (title
    changed; classification note leads the section), §7 item 6.
  - `FibExhibit.lean` header + section comment + docstring of
    `fib_certified_total` (COMMENTS only — statement untouched);
    `Audit.lean` pin comment for the theorem.
  - Structural remediation (total WP; measure-required back edges)
    is Phase 3, per the plan.
- **F-05** — `counter_loop_certified_production` is called the
  REGISTRATION theorem on every docs surface (README exhibit table,
  scope section, ProdEntry module row, divergence register row,
  manifest Notes 3). **The Lean declaration is NOT renamed this
  phase** — see "Naming debt", below.
- **F-07 (wording half)** — sweep language corrected to
  "exhaustively bounded; headline cones exactly pinned" everywhere:
  README trust story ("exact axiom cone asserted in-build" →
  bounded + pinned wording), walkthrough §4 tier 1, README
  DriverCollapse module row ("entirely trio-exact" → bounded, three
  headline equations exact-pinned), `Audit.lean` header (check 1 now
  states it is an upper-bound containment check, with the F-07
  citation) and — the info-line itself, a `logInfo` string, not
  proof content — the sweep summary now reads "… theorems BOUNDED by
  the declared upper bounds (… bounded by trio + runEffectful; all
  others bounded by the trio; exact cones pinned only for the
  curated headline list above)". Both quoted expected build tails
  (README "How to build", walkthrough §6) updated to the real new
  output, pasted verbatim from this checkout's green build.
  The structural half (boundary-module minimization, per-theorem
  exact pins for public boundary exports) is Phase 5, per the plan.
- **F-09** — the mirror slogan ("a wrong mirror can only make
  theorems unprovable, never false") qualified at every occurrence
  (grepped: README:123-area, walkthrough §4 tier 3, walkthrough
  §5.1's absent-machinery paragraph, `Step.lean` header): the
  guarantee is relative to a faithful specification idiom (a wrong
  drive/discharge/readout definition yields a true-but-irrelevant
  theorem) and is fail-open for coverage (a missing rule/cone case
  makes rules silently dead — realized instance: Ecase). Both
  caveats now point at the capability manifest as the coverage
  authority. The stale `Lang.lean` README row fixed: no
  `Language.Context`/wp_bind instance exists (the module header
  proves why — the jump rule falsifies the frame law); the row now
  says what IS there (primStep over the runtime tuple, value
  protocol, pure-determinism facts, `SpikeGF` witness) and that
  sequencing is proved directly. One authoritative coverage matrix
  (the F-09 remediation's core ask) = the capability manifest,
  below.

### The capability manifest (the instrument)

`scripts/capability_manifest.lean` (statement-census pattern)
generates `docs/CAPABILITY_MANIFEST.md`: 18 rows, columns mirror /
logic / cone / engine-match / partial-adequacy / total / production
/ consumer. CHECKED vs DECLARED is documented in the script header
and the generated file: `OK` cells are name-and-kind checked
against the built environment, and the FULL `Step` and `FragJ`
constructor lists are asserted verbatim (16 FragJ / 21 Step ctors)
— so a deleted cone case fails the generator; lane attributions and
consumer-exercises-construct claims are DECLARED pending the
Phase-1 cone-derived upgrade (registered in the script header and
the gate comment).

What generation surfaced (rows weaker than a naive reading of the
old README would suggest — the instrument doing its job):

- `Ecase` (value scrutinee): LOCAL RULE ONLY — RED at cone,
  partial adequacy, consumer (the F-01 finding, now permanent
  red-ink until Phase 1).
- `create`: ADEQUACY-EXPORTABLE but NO LOGIC RULE (no
  `wp_create`/`wps_create` — registered D26), and its only example
  consumer is the PRODUCTION exhibit (`exhibitA_prod`) — no
  drive-lane-only theorem executes a create.
- The TOTAL lane is RED for every construct: the logic has no total
  WP or total judgment; `fib_certified_total` sits outside the
  manifest's lanes as an operational engine theorem (Notes 2
  there).
- The PRODUCTION lane is RED for every loop-profile construct
  (save/if/run/pure-sym/spec+sym binders/memops/operand-eval):
  what exists is the registration tie only. Straight-line
  constructs (value/store/load/create/sseq-wild/annot) reach the
  shipped pipeline via `exhibitA_prod`.
- The `value` and `pure-operands` rows have DECLARED mirror cells
  (the value protocol and the evaluator tower have no single
  per-construct rule name) — honest instrument granularity, listed
  as such.

### The coverage gate (test_unit.sh gate 4)

Two checks, fail-closed (missing markers/lines are failures, not
skips): (a) the generator re-runs and its output must be
byte-identical to the committed `docs/CAPABILITY_MANIFEST.md`
(drift = red; generator failure = red, generator output printed);
(b) the README's certified-scope token block
(`MANIFEST-SCOPE-BEGIN/END` markers) must be a subset of the
manifest's `ADEQUACY-EXPORTABLE:` machine line — a construct listed
as certified in the README without a manifest row at that level is
red. Grep-level tie for Phase 0 by design; the Phase-1 upgrade
(fully mechanical, generated from the unified capability predicate)
is registered in the gate comment and the script header.

### Plant tests (both directions, this checkout)

Plant A — fake certified claim: `case-value` added to the README
token block; full `./scripts/test_unit.sh` run:

```
FAIL: README claims certified scope token 'case-value' but the manifest does not list it as adequacy-exportable
GATE FAILURE
```
(exit 1). Reverted.

Plant B — manifest drift: `case-value` hand-added to the committed
manifest's `ADEQUACY-EXPORTABLE:` line; full run:

```
FAIL: capability manifest drift (diff above) — regenerate docs/CAPABILITY_MANIFEST.md deliberately, same commit
GATE FAILURE
```
(exit 1). Reverted.

Plant C — deleted-cone-case stand-in (no proof content touched:
`FragJ.store` removed from the generator's asserted constructor
list, simulating the mismatch a real deletion produces); full run:

```
FAIL: capability manifest generator red (a checked name or the Step/FragJ constructor list changed); generator output:
scripts/capability_manifest.lean:362:0: error: manifest FAIL: constructor list of CerberusHeapLang.FragJ changed.
expected: [CerberusHeapLang.FragJ.annot, ..., CerberusHeapLang.FragJ.sseq_sym, CerberusHeapLang.FragJ.store_op, CerberusHeapLang.FragJ.val_pure]
actual:   [CerberusHeapLang.FragJ.annot, ..., CerberusHeapLang.FragJ.sseq_sym, CerberusHeapLang.FragJ.store, CerberusHeapLang.FragJ.store_op, CerberusHeapLang.FragJ.val_pure]
A cone/mirror constructor was added or removed — regenerate docs/CAPABILITY_MANIFEST.md deliberately (and update the expected list here) or restore the constructor.
GATE FAILURE
```
(exit 1; expected/actual lists abbreviated here with `...` — the
gate prints them in full). Reverted.

Green direction after all reverts — full run:

```
ok: no banned proof-method references
ok: root build green (axiom sweep + pins passed in-build)
ok: cerberus-heaplang build green (axiom sweep + pins passed in-build)
ok: capability manifest regenerated, no drift
ok: README certified-scope tokens all within the manifest's adequacy-exportable set
ALL GATES GREEN
```
(exit 0).

### Naming debt (registered)

`counter_loop_certified_production` (ProdEntry.lean) keeps its Lean
name this phase: renaming it is statement-surface churn under the
frozen-signature discipline, for a declaration Phase 5 will
supersede with a real production (`runND`) theorem — the rename to
`_registration` (or retirement into the real theorem) lands there.
Until then every docs surface calls it the registration theorem
(manifest Notes 3; README divergence-register row).

### Zero statement drift (the frozen-signature proof)

The signature snapshot was regenerated at this slice's head and
diffed against the committed baseline (the listrev phase-A post
snapshot, unchanged through the docs-only phase-B/C commits):

```
$ ../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean \
    > /tmp/claude-1000/phase0-signatures-post.txt
$ diff -q docs/2026-08-31_listrev-signatures-post.txt \
    /tmp/claude-1000/phase0-signatures-post.txt && echo "ZERO STATEMENT DRIFT"
ZERO STATEMENT DRIFT
```

Byte-identical — no statement, definition, or kind changed; the
snapshot is therefore not re-committed (the committed listrev post
file remains the current truth).

### Verify-me re-runs (every touched block, this checkout)

README "How to verify me" block, re-run verbatim (unchanged from
the committed observed output — the docs' observed block stands):

```
'CerberusHeapLang.semantic_triple_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.engine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.array_sum_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified_production' depends on axioms: [propext,
 runEffectful,
 Classical.choice,
 Quot.sound]
```

Build tail (README/walkthrough expected-tail blocks updated to
exactly this, pasted from the green build of this checkout):

```
info: CerberusHeapLang/Audit.lean:384:0: CerberusHeapLang axiom sweep: 755 theorems BOUNDED by the declared upper bounds (40 in the production-entry boundary modules, bounded by trio + runEffectful; all others bounded by the trio; exact cones pinned only for the curated headline list above)
info: CerberusHeapLang/Audit.lean:384:0: CerberusHeapLang banned-axiom sweep: 1499 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (434 jobs).
```

### What Phase 0 does NOT claim

No structural change: Ecase is still outside the cone (Phase 1);
the total lane is still absent from the logic (Phase 3); the loop
production equation is still open (Phase 5); the interior-rule
modularity defect (F-04) and list-theorem strength (F-06) are
untouched (Phases 2/4). This slice makes the repository say so, in
one authoritative place, with a gate.

## Phase 1 — S1a, the architecture probe (this slice)

Worker slice, [AGENT] execution of the S1a probe brief (arc plan
Phase 1; kill criteria pre-registered there). Deliverables: the
DESIGN RECORD `docs/2026-08-31_phase1-design-record.md` (the
[USER] Phase-1 checkpoint document — unified MachineCtx
configuration, alternatives rejected, per-construct two-sidedness,
findings, migration prescription) and the probe implementation
`CerberusHeapLang/Phase1Probe/{Machine,Match,Lang,Adequacy}.lean`
(+ umbrella), PROBE-ONLY: lives alongside the existing cones,
consumed by nothing exported; S1b replaces the old cones with this
shape and retires the probe modules.

### What the probe proved (summary; the design record is the account)

- `MachineCtx` (11 explicit fields = every immutable of the engine
  configuration) × unchanged live state; frozen profiles =
  instances (`spikeCtx`/`procCtx`, rfl ties); label map DERIVED
  from the context — the `LabeledAt` tie hypothesis disappears.
- `StepU M` re-indexes store/run/case; ONE cone `FragU` (case
  JOINS it — F-01) with one closure theorem; the existing `DecompJ`
  is already the single decomposition (S1b deletes the P-variants).
- Characterization: store TWO-SIDED at any context
  (`engine_step_matchU` + `engine_complete_storeU`); case
  TWO-SIDED (new `step_ctx_case_illtyped` + `engine_complete_caseU`
  — the RED row's engine pair now exists); run ONE-SIDED
  (match-given-step, the direction adequacy consumes;
  audit-sanctioned, documented in the probe manifest row).
- Language instance over `CoreRtU = (e, ρ, M)`; `primStep` = the
  unified relation; Heap/ghost layer shared unchanged; `wp_storeU`
  re-proves the store small axiom near-verbatim.
- Adequacy chain re-derived at any context (`spike_step_adequacyU`
  → `drive_classifyU` → `engine_adequacyU`); ONE drive `driveU M`
  with `drive`/`driveJ` as proved instances (`driveU_spike`,
  `driveU_procJ`).
- THE ORACLE (K1): `exhibitB_semantic_unified` re-proves the
  exported `exhibitB_semantic` statement VERBATIM through the
  unified route — zero statement diff.
- ECASE regression: `case_regression_engine` (any SeqWF context) /
  `case_regression_drive` (over the OLD `drive`) — an engine-facing
  theorem whose program executes the value-scrutinee case rule.
- K4: `scripts/phase1_probe_manifest.lean` enumerates the manifest
  rows FROM `FragU`'s constructor list (no hand row list); plant
  run recorded below.

### Kill assessment

K1/K2/K3/K4 all NOT TRIGGERED — details + evidence: design record
§7. Registered probe restrictions (explicit hypotheses, named
movers, design record §5): `M.extern = fmapEmpty` on the run
characterization (S1b threads extern through the evaluator bridge);
`SeqWF` (permanent — the value protocol reads stack/parent); the
`esize`-has-no-Ecase-arm finding (S1b measure extension, flagged as
statement-change class (E) for operator sanction).

### Audit-sweep coverage + docs tallies

`Audit.lean` gained `import CerberusHeapLang.Phase1Probe` — without
it the probe's constants would have escaped the in-build sweep (no
internal trust gaps). New sweep tallies, quoted verbatim from this
checkout's green build (README "How to build" + walkthrough §6
expected-tail blocks updated to exactly this):

```
info: CerberusHeapLang/Audit.lean:385:0: CerberusHeapLang axiom sweep: 827 theorems BOUNDED by the declared upper bounds (40 in the production-entry boundary modules, bounded by trio + runEffectful; all others bounded by the trio; exact cones pinned only for the curated headline list above)
info: CerberusHeapLang/Audit.lean:385:0: CerberusHeapLang banned-axiom sweep: 1670 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (439 jobs).
```

All probe theorems are trio-bounded (none in a boundary module).

### K4 plant run (this checkout, reverted)

The `FragU.case_value → row` mapping deleted from
`scripts/phase1_probe_manifest.lean`; run:

```
scripts/phase1_probe_manifest.lean:82:0: error: probe manifest FAIL: cone constructor CerberusHeapLang.FragU.case_value has NO manifest row mapping — the cone was extended without the manifest (fail-closed by design; add the row).
```

Reverted; green run enumerates 5 cone constructors and emits the
table (reproduced in full by running the script).

### Signature discipline (probe additions only)

Pre-snapshot regenerated before probe work and diffed against the
committed baseline:

```
$ diff -q docs/2026-08-31_listrev-signatures-post.txt \
    /tmp/claude-1000/phase1-probe-signatures-pre.txt && echo "PRE == COMMITTED BASELINE"
PRE == COMMITTED BASELINE
```

Post-snapshot diff vs pre: 0 lines removed or changed, 1496 lines
added (163 declarations, all `Phase1Probe`/`*U`/`MachineCtx` —
derived tally from the diff; the post snapshot is committed as
`docs/2026-08-31_phase1-probe-signatures-post.txt`). The existing
corpus's statement surface is untouched; the one re-proved export
(`exhibitB_semantic_unified`) is a NEW name with the OLD statement
body, per the probe charter (the migration, not the probe, replaces
the old proofs).

### What S1a does NOT claim

The migration is unpaid: the exported corpus still runs on the old
cones; only exhibit (b)'s semantic statement has a unified-route
proof; Ecase's manifest row stays LOCAL RULE ONLY until S1b lands
the full row (wps consumer + binder patterns + esize extension).
The S1b/S1c prescription and slice estimate: design record §8.
