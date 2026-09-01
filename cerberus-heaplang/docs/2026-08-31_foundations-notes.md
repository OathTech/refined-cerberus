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

## Phase 1 — S1b, the migration (four worker slices, 2026-08-31 → 2026-09-01)

[AGENT] execution of the design record §8 S1b prescription, four
commits. Two workers died mid-slice from API-credit exhaustion
(infrastructure, not technical kills); each successor triaged the
predecessor's uncommitted work before proceeding — the per-commit
WIP-triage provenance is IN the commit messages (2/4's two-file
coherent diff kept-and-completed; 3/n's CaseExhibit resumed from
verified WIP, gate re-verified by the resuming worker, never
carried over on the predecessor's claim).

The per-slice records are the commit messages (detailed by design):

- **1/4 THE SWAP** (`7dcb497`): Step re-indexed `Step Q` → `Step M`
  over the explicit `MachineCtx`; frozen profiles = instances; ONE
  cone/decomposition (FragP/Redex(P)/Decomp(P) DELETED
  prune-don't-merge, FragJ/RedexJ/DecompJ renamed in); Ecase joins
  the cone (F-01) with the esize Ecase extension (sanctioned class
  (E)); characterization + strata re-proved; drive/driveJ =
  definitional driveU instances; Phase1Probe modules DELETED (their
  content IS the migrated code; StmtProbe is NOT probe debt — the
  S0 toy is kept by charter as a design record). Registered
  deviation-with-reason: StraightRoot/StraightFrag survive as the
  straight-line completeness DOMAIN (not a capability cone).
- **2/4 S1b′ extern** (`d4f4084`): the registered S1a probe
  restriction `M.extern = fmapEmpty` (design record §5.2, named
  mover) REMOVED; extern threaded through evalPexpr + the bridge
  tower; `resolveExtern` mirrors Core_eval.lean:142 verbatim.
- **3/n Ecase consumer** (`e3cb802`): `case_certified`
  (CaseExhibit) — BINDER-pattern case program, the substitution TAU
  genuinely fires; manifest row LOCAL-RULE-ONLY → CERTIFIED (drive
  lane). Design-record §5.1 correction recorded in the module
  header: the generic substitution-closure lemma
  `Frag e → Frag (subst_sym_expr x v e)` is FALSE on this cone
  (value-shape-sensitive premises); the cone carries branch closure
  as explicit per-branch premises instead, discharged by
  computation at the exhibit.
- **4/n THE DRIFT TEST** (`4d3e99e`): Ewseq WILDCARD through the
  generic route end-to-end. [AGENT] pick between the design
  record's two candidates (no pick had been recorded): the
  genuinely NEW construct over the new-guard-shape option. The
  generic-route demonstration came out exactly as prescribed: the
  Rules/Adequacy strata and the Language instance needed ZERO
  changes; the manifest generator FAILED CLOSED until the row
  landed. Verbatim, pre-row:

```
scripts/capability_manifest.lean:367:0: error: manifest FAIL: constructor list of CerberusHeapLang.Step changed.
```

  Spec-idiom extensions carried by the drift construct, same
  discipline as class (E): `esize` Ewseq arm, `jumpRedex?`
  Ewseq-left arm — each documented in-code with the
  per-pre-existing-constructor `rfl` conservativity note (the
  pre-existing simp equations `esize_sseq`/`jumpRedex?_sseq` etc.
  still close by `rfl`; they compile unchanged).

### THE ORACLE (design record §8 item 6; prescription item K1)

Baseline: `docs/2026-08-31_phase1-probe-signatures-post.txt` (the
committed post-S1a snapshot — the notes above record it equal to
the pre-probe corpus plus probe-only additions). Post:
`docs/2026-09-01_s1b-signatures-post.txt`, generated by
`scripts/signature_snapshot.lean` on this checkout. Name-level
comparison (derived tallies from the two committed files):

- Baseline 1670 entries; post 1610. REMOVED 227, ADDED 167,
  CHANGED 263 (of which 61 are auto-generated recursor/equation
  surface — `rec`/`casesOn`/`below`/`brecOn`/`injEq`/`eq_def` —
  implied by the inductive/structure changes, carrying no
  independent claim; 202 hand-written).

**HEADLINE (K1): every exported certified statement is
byte-identical between baseline and post.** Checked by name over
the headline list — `drive`, `driveJ`, `exhibitA_engine`,
`exhibitB_engine`, `exhibitB_semantic`, `exhibitC_engine`,
`counter_loop_certified`, `fib_certified`, `fib_certified_total`,
`array_sum_certified`, `list_reverse_certified`, `exhibitA_prod`,
`counter_loop_certified_production` — none appears in the
changed/removed sets (`case_certified`, `wseq_certified` are NEW).

REMOVED, by family (derived): Phase1Probe deletions (FragU 20,
StepU 14, CoreRValU 16, CoreRtU 15, probe driveU instances,
ReachU/progCase/semantic*U/wp_storeU/wp_wandU/toValRtU — the
probe's content is the migrated code, prune-don't-merge); the
deleted parallel cone (FragP 25); the renamed-out J-families
(FragJ 43, DecompJ 26, RedexJ 17 → the unified names); interior
classifier replacements (`drive_classify`/`drive_classifyJ` →
`drive_classifyU`); `drive.eq_def`/`driveJ.eq_def` (auto-generated,
no longer forced — the defs' TYPES are unchanged; their bodies are
now driveU instances, which is exactly the sanctioned mechanism).

CHANGED (202 hand-written), itemized by sanctioned class (§6 of the
design record; representative verbatim spot-checks reproduced from
the snapshot diff during this slice's gate work):

- **(A) index plumbing** — the bulk: `Q : LabelMap` slots become
  `M : MachineCtx` (all 21+ Step rules and inversions, the
  step_ctx/stepDischarge/engineSteps equation families' extern
  slot, `evalPexpr`(s) extern argument, the wp/wps rule families,
  exhibit-interior lemmas `arr_*`/`fib_*`/`lr_*`/`loop_*`,
  `CoreRt`/`CoreRVal` carrying `M`).
- **(B) tie-hypothesis deletion**: `engine_adequacyU` and
  `drive_classifyU` lose `M.extern = fmapEmpty` (the S1b′ mover —
  hypothesis deletion = theorem strengthening); `LabeledAt`/`hQ`
  ties gone from the interior theorems (1/4; `engine_adequacyJ`
  keeps its exported `LabeledAt rs p Q` shape verbatim).
- **(C) frozen-constant naming**: `fmapEmpty`-as-tagDefs becomes
  `M.tagDefs` inside rule statements (`Step.store`, `wp_store`,
  `wps_store`, the store step_ctx family).
- **(D) explicit WF hypotheses**: `SeqWF` appears in the unified
  adequacy statements where the frozen profiles silently assumed
  empty stack/no parent.
- **(E) spec-idiom measure extension**: `esize` (Ecase arm in 1/4,
  Ewseq arm in 4/n) + the 4/n `jumpRedex?` Ewseq arm — meaning-
  preserving on the pre-existing corpus (per-constructor `rfl`
  equations unchanged), operator-sanctioned (the standing sanction
  carried by this slice's brief).
- **Renames** (sanctioned by §8.3 explicitly): `FragJ`→`Frag` etc.
  appear inside otherwise-verbatim exported statements
  (`engine_adequacyJ`'s cone hypothesis vocabulary).

Nothing outside these classes was found; no stop-and-ask item
remained open at the gate.

### Gate record (this checkout)

`./scripts/test_unit.sh` ALL GATES GREEN at each of `e3cb802`,
`4d3e99e`, and the oracle/record commit (grep ban; root + demo
builds with in-build axiom sweeps; manifest regenerated no-drift;
README scope tie). Claims surfaces trued where the manifest
changed: README certified-scope prose + token list (+`case-value`,
+`wseq-wild`), the discharged Ecase register entry pruned, the
Step.lean header de-staled, the walkthrough's F-09 coverage
parenthetical moved to past tense.

### What S1b does NOT claim

No total lane (Phase 3), no production-lane movement (the drift and
case rows are drive-lane certified, outside the production
exhibit's lane); Ewseq at spec/sym binder patterns and Ecase's EVAL
arm remain registered divergences; the manifest's Step/Frag
constructor lists are still hand-asserted mirrors of the
inductives — S1c derives the rows from the cone (K4's demonstrated
mechanism, design record §4).

## Phase 1 — S1c, instruments + claims surfaces (this slice, 2026-09-01)

[AGENT] execution of the design record §8 S1c prescription (the
light closing slice): the cone-derived manifest (K4's demonstrated
mechanism at full-cone scale), the RelSem two-presentations
paragraph (arc plan Phase-1 item 6), and the Phase-1 exit-criteria
sweep.

### The cone-derived manifest (gate-4 upgrade)

`scripts/capability_manifest.lean` rebuilt on the S1a probe's
enumeration shape (`phase1_probe_manifest.lean`, retired with the
probe — recovered from `d42a77a` as the donor pattern):

- THE ROW SET IS DERIVED: rows are enumerated from `Frag`'s
  constructor list read out of the built environment, through a
  `Name → Option RowSpec` mapping. A cone constructor without a
  mapping arm throws (fail-closed). The hand-asserted
  `expectedFragCtors` list is DELETED — there is no list to drift.
- STEP COVERAGE IS DERIVED: after row generation, every `Step`
  constructor read out of the environment must be claimed by
  EXACTLY ONE row's mirror cell; an unclaimed constructor, a claim
  of a non-`Step` constructor, and a double claim each throw. The
  hand-asserted `expectedStepCtors` list is DELETED.
- The cone CELL is the enumeration key itself (`RowSpec` carries no
  cone cell; the generator fills it) — a row cannot claim cone
  membership the cone does not have.
- The supplementary evaluator-tower row (`pure-operands` — premises,
  not a capability; it owns no constructor) is mechanically barred
  from claiming any constructor, so it can never absorb a cone or
  mirror extension.
- Kept from Phase 0: every `OK` cell name-and-kind checked. Still
  DECLARED (documented instrument granularity, no registered mover):
  lane attributions and consumer-exercises-construct claims.
- Row order is now cone declaration order (the enumeration is the
  row set) + the supplementary row last; the machine-readable token
  SETS are unchanged (derived check this slice: old vs new
  `ADEQUACY-EXPORTABLE` lines sorted and diffed — identical as
  sets). `docs/CAPABILITY_MANIFEST.md` regenerated, same commit;
  gate-4 comments in `scripts/test_unit.sh` trued to the derived
  form.

What the derivation surfaced: NOTHING LATENT — the enumeration
reproduced the retired hand lists exactly (18 `Frag` rows, 24
`Step` constructors, each claimed exactly once, every cone
constructor mapped), so no row was silently weaker than the hand
lists claimed. The derivation does CLOSE two failure modes the hand
lists never checked: (a) a mirror cell claiming a constructor of a
DIFFERENT inductive (previously only existence+kind was checked;
now the constructor's parent inductive must be `Step`), and
(b) two rows claiming the same `Step` constructor (previously the
asserted list would still pass; now a double claim throws — one
semantic coverage point per constructor, the audit F-03 acceptance
wording). Neither fired on the current corpus.

### Plant tests (all this checkout, all reverted)

Plant method note ([AGENT], per the S1a probe's precedent): a
hypothetical NEW `Step`/`Frag` constructor is simulated
mechanically, not planted as proof content (a real constructor
would force inversion-proof edits) — the failure state the gate
must catch is "an environment constructor no manifest row covers",
and deleting one row-side claim/mapping reproduces exactly that
state through the identical code path (the derived-coverage loop).

Plant A — new mirror constructor without a row (simulated:
`Step.wseq_ctx` removed from the wseq row's mirror cell); generator
run:

```
scripts/capability_manifest.lean:389:0: error: manifest FAIL: mirror constructor CerberusHeapLang.Step.wseq_ctx has NO manifest row — the Step relation was extended without the manifest (fail-closed by design; add it to a row's mirror cell, or give the new construct its own row).
```

(exit 1). Reverted.

Plant B — new cone constructor without a mapping (the probe's exact
plant: the `Frag.case_value → rowSpec` arm deleted); generator run:

```
scripts/capability_manifest.lean:374:0: error: manifest FAIL: cone constructor CerberusHeapLang.Frag.case_value has NO manifest row mapping — the cone was extended without the manifest (fail-closed by design; add the rowSpec arm).
```

(exit 1). Reverted.

Plant C — manifest drift (existing plant re-run at the upgraded
gate: `bogus-token` hand-added to the committed manifest's
`ADEQUACY-EXPORTABLE` line); full `./scripts/test_unit.sh`:

```
FAIL: capability manifest drift (diff above) — regenerate docs/CAPABILITY_MANIFEST.md deliberately, same commit
GATE FAILURE
```

(exit 1). Reverted.

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

Claims surfaces trued with the instrument (same commit): README
manifest paragraph + trust-story coverage caveat, walkthrough §4
tier-3 coverage caveat — each now states the row set is
cone-derived and a constructor without a row is a failed gate.

### Direction documentation trued (found by the exit sweep)

The exit sweep found arc-plan item 3's tail under-documented: the
one-sided/two-sided DIRECTION was recorded in the design record and
the Soundness comments but not per-construct on the manifest (the
audit-sanctioned home for it). The THEOREMS all exist; only cell
notes were missing — closed in-slice (claims-surface work, S1c's
charter): the store row's engine-match cell now carries
`engine_complete_storeU` with the TWO-SIDED note (case already
carried its pair), the run row carries the ONE-SIDED
match-given-step note, and manifest Notes 7 states the direction
semantics of the whole column (`engine_step_matchU` =
match-given-step over the full cone at any MachineCtx — the
direction the WP-driven adequacy consumes; `engine_complete` = the
straight-line classification completeness over `StraightFrag`; rows
without a completeness entry are one-sided, deliberately). Manifest
regenerated, same commit.

### The RelSem two-presentations paragraph (arc plan Phase-1 item 6)

Landed where the naive reader's trust path passes the pinned
semantics workspace: README "What you are asked to take on faith"
item 2 gains the "two presentations, one engine" paragraph (the
workspace's `relsemcore` — `RelSem` machine `Step`, `runND_sound`,
`HarnessAdequate` — is the SEMANTICS REPO'S validation instrument
for its own runner, NOT part of this package's chain; no bridging
theorem exists or is claimed; this package's chain is exactly the
trust story's; a bridge is recorded OUT of scope for this phase),
and walkthrough §4 tier 1 gains the compact parenthetical pointing
at it. Names verified against the workspace this checkout:
`relsemcore/RelSem/Machine.lean:131` (`Step`),
`RelSem/RunND.lean:190` (`runND_sound`),
`RelSem/Cerberus.lean:268` (`HarnessAdequate`).

### PHASE-1 EXIT CRITERIA — the checklist against this tree

Arc plan Phase-1 items 1-7, each verified at source this slice
(file:line as of this checkout):

1. **Design decision recorded, operator-visible** — MET:
   `docs/2026-08-31_phase1-design-record.md` (S1a; now carrying the
   CLOSED status update).
2. **One capability predicate, one decomposition, closure
   theorems; manifest generates FROM it** — MET: `Frag`
   (Soundness.lean:3578; FragP/Redex/Decomp deleted and
   FragJ/RedexJ/DecompJ renamed in at S1b 1/4), closure under steps
   `Frag.step` (Soundness.lean:3918, label-cone side hypothesis
   `hQf`), decomposition `Frag.decomp` (Soundness.lean:3698).
   REGISTERED DEVIATION (S1b 3/n, recorded in the CaseExhibit
   header and the S1b notes): the arc plan's generic
   substitution-closure lemma is FALSE on this cone
   (value-shape-sensitive premises) — branch closure is carried as
   explicit per-branch premises on `Frag.case_value` (`hbr`/`hbsz`),
   discharged by computation at consumers. Manifest generated FROM
   the cone: this slice (above).
3. **Engine characterization against the unified relation;
   directions documented** — MET: `engine_step_matchU`
   (Soundness.lean:4396 — full cone, any MachineCtx); two-sided
   where obtained: `engine_complete` (Soundness.lean:2058, the
   straight-line classification over `StraightFrag`),
   `engine_complete_storeU` (:4809), `engine_complete_caseU`
   (:4905); per-construct direction notes on the manifest (above).
4. **Iris Language over the unified relation; primStep IS the
   authoritative relation** — MET: `instance : Language CoreRt Mem
   Empty CoreRVal` (Lang.lean:43) defines `primStep` AS `Step` at
   the tuple's own MachineCtx (successor context pinned);
   `primStep_eq` (Lang.lean:69) is the definitional tie
   (`Iff.rfl`).
5. **Ecase (value) joins the cone properly** — MET: `Step.case_value`
   (Step.lean), `Frag.case_value` (branch-closure + branch-size
   premises over the extended `esize`), `wps_case_value`
   (Wps.lean:964), engine pair `step_ctx_case_value` /
   `step_ctx_case_illtyped` / `engine_complete_caseU`, and the
   adequacy-level regression `case_certified` (CaseExhibit.lean:136
   — BINDER pattern; the substitution TAU genuinely fires; program
   executes the rule).
6. **RelSem documented honestly, bridge out of scope** — MET this
   slice (above).
7. **Oracle + drift test** — MET: the S1b oracle (headline exports
   byte-identical baseline→post; the S1b notes section is the
   record); drift construct Ewseq wildcard through the generic
   route: `Step.wseq_pure`/`wseq_annot`/`wseq_ctx`, `Frag.wseq`,
   `wps_wseq` (Wps.lean:721), `step_ctx_wseq_pure`/`_annot`,
   consumer `wseq_certified` (WseqExhibit.lean:105); the manifest
   generator failed closed until the row landed (verbatim transcript
   in the S1b notes).

The exit line, verbatim criteria:

- **"One theorem ties primStep to the engine relation on the
  fragment"** — `engine_step_matchU`: wherever the mirror steps at
  a `Frag` configuration (any MachineCtx, in-budget esize), the
  engine's discharged behavior list is exactly the matching
  singleton; `primStep` is `Step` definitionally (`primStep_eq`,
  `Iff.rfl`), so the theorem IS about primStep on the fragment.
- **"Cones cannot diverge without a failed check"** — one cone
  (`Frag`, the only capability predicate in the tree since S1b) and
  the cone-derived gate (this slice): a cone constructor without a
  manifest row, a mirror constructor without a row, a stale or
  double claim, a missing checked rule/match/consumer name,
  committed-manifest drift, and a README scope token outside the
  exportable set EACH fail gate 4 — plant transcripts above.
- **"Ecase + the new construct through the generic route"** — items
  5 and 7's theorem chains, both ending at adequacy-level consumers
  (`case_certified`, `wseq_certified`) in engine vocabulary.

### Verify-me re-runs + statement surface (this checkout)

No `CerberusHeapLang/*.lean` library source changed in S1c
(instruments + docs only), so the committed S1b signature snapshot
(`docs/2026-09-01_s1b-signatures-post.txt`) remains the current
truth and the build tallies are unchanged (827 theorems / 1670
constants — the expected-tail blocks stand). The README verify-me
axiom block was re-run verbatim at this tree: output IDENTICAL to
the committed observed block (trio everywhere; trio + `runEffectful`
on the two production-entry statements). Gate record: full
`./scripts/test_unit.sh` ALL GATES GREEN at each S1c commit
(re-verified below by the committing worker).
