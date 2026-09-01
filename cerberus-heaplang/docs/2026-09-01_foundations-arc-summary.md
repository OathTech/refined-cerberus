# The foundations arc — summary (the re-auditor's entry document)

The arc: [USER 2026-08-31] "we're going to get cerberus-heaplang
right, we're not kicking off refinedC until this is perfect." Input:
the foundational audit
(`docs/2026-08-31_cerberus-heaplang-foundational-audit.md`, verdict
retain-and-refactor, findings F-01..F-10); plan:
`docs/2026-08-31_foundations-arc-plan.md` (the audit's phase
structure + its 8-test acceptance suite as the ARC EXIT GATE).
This document is the arc's close-out summary: one paragraph per
phase (finding → what landed → oracle result), the finding
disposition table, the acceptance-suite record pointer, and the
remaining registered items with owners. The per-phase design
records and oracles are the authoritative detail; every claim here
is a pointer into them.

**Arc exit status**: the 8-test suite is closed — evidence, test by
test, re-run on this tree:
`docs/2026-09-01_acceptance-suite-record.md`. What remains of the
arc close is the FRESH FOUNDATIONAL RE-AUDIT (new auditor, the
original audit's brief + suite as its terms; no High findings =
arc done, port unblocks) — a [USER] checkpoint, not a work slice.

## The phases

**Phase 0 — claims corrected, coverage gated** (F-01/F-02 claims
halves, F-05 wording, F-07 wording, F-09; record:
`docs/2026-08-31_foundations-notes.md` §Phase 0). Finding: public
claims outran proved coverage (Ecase advertised but not
adequacy-exportable; an operational side proof presented as logic
totality; "production"/"exact cone" overstatements; no
authoritative coverage matrix). Landed: every claims surface
corrected to the honest state, and THE CAPABILITY MANIFEST
installed — a generated per-construct scope table with a gate
(test_unit.sh gate 4: drift + README scope-token tie),
plant-tested both directions; Ecase shown RED until Phase 1.
Oracle: the signature snapshot diffed clean — zero proof-content
changes; docs/instrument/gate only.

**Phase 1 — one authoritative relation, one coverage cone** (F-03,
F-01 root cause; records: `docs/2026-08-31_phase1-design-record.md`,
`docs/2026-08-31_foundations-notes.md` S1a/S1b/S1c,
`docs/2026-08-31_phase1-notes.md`). Finding: the attachment
relation was a manually duplicated, frozen projection — six
parallel cones, frozen example profiles, coverage divergence
possible without a failed check. Landed (probe S1a, migration S1b,
instruments S1c): the one relation `Step (M : MachineCtx)` over an
explicit configuration naming every immutable engine slot (11
fields, per-field read table in the design record), live state
`(expr × env × Mem)` with the label map DERIVED; ONE capability
cone `Frag` + one decomposition with closure theorems; Iris
`primStep` IS the relation (definitional tie); the step-match
characterization at ANY context (`engine_step_matchU`; two-sided
where obtained: straight-line profile, store, case); Ecase
properly in the cone with an adequacy consumer (`case_certified`);
`Ewseq` wildcard passed through the generic route as the drift
test (`wseq_certified`) — the manifest generator failed closed
until its row landed; the manifest upgraded to the CONE-DERIVED
form (row set enumerated from the environment). Oracle: the S1b
frozen-corpus regression — every exported headline statement
byte-identical pre→post; the probe/S1c snapshots add-only.

**Phase 2 — the generic memory layer; examples become clients**
(F-04, F-10; record: `docs/2026-09-01_phase2-notes.md`). Finding:
flagship examples extended the logic with their own layout rules;
whole-allocation-only ownership; no allocation rule. Landed: the
ownership split (per-byte heap + fractional metadata authority,
donor-shaped after Caesium's ghost state) with typed subrange VIEWS
and real split/join; the generic in-bounds typed load and
full-ownership store (`wps_load_at`/`wps_store_at` + whole-cell
forms), certified ONCE against loadM/storeM — the six example-local
interior rules DELETED; the allocator-cursor resource and sound
`wps_create` (the D26 dodge retired; the OOM arm excluded by a pure
guard on owned state); the fresh-client acceptance test built and
passed (`StructExhibit`, zero core edits, commit-diff evidence).
Oracle: 8 deleted (exactly the F-04 evidence list + the old carrier
fields), 32 changed (all inside the sanctioned Iris-interior
plumbing class), 172 added; the exported engine-facing statement
face verbatim-frozen.

**Phase 3 — total correctness into the logic** (F-02 structural;
record: `docs/2026-09-01_phase3-notes.md`). Finding: totality was
an operational side proof (explicit Step/driveJ_step induction),
not a logic result; the "variant" lemma had no consumer and no
termination consequence. Landed: the total statement judgment
`wpt` (structural recursion on a step budget; the back-edge
decrease `1 + m ≤ k` MANDATORY in the jump clause — never an
optional hypothesis; `blockSpecs_intro_variant` deleted, replaced
by `blockSpecsT`), the collapse into the pinned Iris
TotalWeakestPre (`wpt_sound` — TWP's first consumer), and BOTH
adequacy halves separated per the audit: termination
(`wpt_strongly_normalizing` via `twp_total` as-is) and the generic
measure→drive-fuel simulation (`wpt_engine_boundU/J`). fib totality
re-derived as a corollary (statement VERBATIM; the operational
proof retired), total list-reverse at the DERIVED bound `13·|ns|+7`,
and the negative test (`diverge_total_unprovable` — a diverging
loop's total derivation is semantically FALSE). Oracle: 2 deleted
(both sanctioned: the variant lemma, the operational fib proof),
ZERO exported statements changed, ~102 added.

**Phase 4 — flagships at full strength** (F-06; record:
`docs/2026-09-01_phase4-notes.md`). Finding: the list theorem was
weaker than the standard in-place-reversal spec (no identity, no
footprint equality, no frame). Landed: identity-indexed predicates
(`isList`/`ChainAt`/`SeedChain` over (allocation id × value)
lists), the flagship restated to literal same-footprint + in-place
+ frame + termination in one public statement
(`list_reverse_certified_total`), the frame exported through the
loop invariant (the jump-lane analog of `SemTriple`'s
∀R-quantifier), GF binders dropped from all flagship statements,
and the SECOND CLIENT — binary-tree rotation, structurally
different on every axis (third layout, branching recursion,
non-reversal permutation), ZERO core edits (3-file commit).
Oracle: 2 deleted (the interior readouts, replaced by the core
combinator route), 22 changed (ALL in the sanctioned list-reverse
family), 124 added.

**Phase 5 — production attachment completed; boundary endgame**
(F-05, F-08 + F-07 strengthening; record:
`docs/2026-09-01_phase5-notes.md`). Finding: no loop theorem
reached the shipped runner ("production" was a registration tie);
runEffectful's allowance was module-scoped but not origin-checked.
Landed: the loop scheduler/driver collapse at proc-carrying,
populated-label threads over the FULL cone (`loop_step_frag`; the
total-judgment-driven driver simulation `wpt_driver_done`); THREE
production exports concluding about the shipped
`CerbND.runND (Driver.drive …) (initial_driver_state …)` composite
from the cold start (fib; the self-contained heap-effecting
counter; the flagship's self-contained two-node reversal instance);
the F-05 rename paid (`counter_loop_certified_registration`); the
boundary narrowed to the minimal statement-carrying module set with
the ORIGIN DISCIPLINE in-build (runEffectful reachable only through
statement constants — proof-borne is a build failure; plant-tested)
— every boundary cone exact-by-construction; GF binders removed
from the remaining loop exports. The upstream retirement had NOT
landed, so this is the arc plan's documented fallback, with the
mover unchanged. Oracle: 0 deleted, 4 changed (exactly the
sanctioned list), 80 added; sweep 1123 theorems / boundary 71 / 13
statement-borne carriers.

**The acceptance-suite slice** (this close; record:
`docs/2026-09-01_acceptance-suite-record.md`). Landed: the census
freeze-gate (test_unit.sh gate 5 — the registered future gate,
implemented and plant-tested both directions), five pins completing
"exact pins for all public exports", the test-8 mutation plants
(all four mutations red on named gates, transcripts verbatim,
reverted green), the test-3 perturbation actually run (layout
constant swapped; the package rebuilt GREEN with zero further
edits; reverted), and two stale-claims findings fixed (the
expected-tail blocks and the walkthrough GF-binder note, both
overtaken by Phase 5).

## Finding disposition (F-01..F-10)

| Finding | Fix | Evidence (on this tree) |
|---|---|---|
| F-01 `Ecase` cannot reach adequacy (High) | Phase 0: out of claimed scope, RED row. Phase 1: proper cone membership + two-sided engine pair + adequacy consumer | manifest row `case-value` FULL-ROW (`Frag.case_value`, `engine_complete_caseU`, `case_certified`); pin added this slice |
| F-02 totality operational, not logic (High) | Phase 0: reclassified on all surfaces. Phase 3: `wpt` + mandatory decrease + Iris TWP collapse + generic cost simulation; fib a corollary, statement verbatim | zero Step/driveJ_step in loop exhibits (suite record test 4); `wpt_sound`/`wpt_engine_boundJ`/`wpt_strongly_normalizing` pinned trio |
| F-03 duplicated frozen projection (High) | Phase 1: MachineCtx configuration, one cone, primStep authoritative, cone-derived manifest | `engine_step_matchU` at any ctx (pinned); gate 4 fail-closed plants; suite record tests 1, 5, 8a |
| F-04 example-local layout rules (High) | Phase 2: generic typed-subrange rules; interior rules deleted; exhibits are clients | phase-2 oracle deletion list; fresh-client + perturbation (suite record tests 2, 3) |
| F-05 "production" misnomer (Medium) | Phase 0: docs. Phase 5: rename + the real production theorems | the three `*_production` runND theorems (suite record test 6); `counter_loop_certified_registration` |
| F-06 weak list spec (Medium) | Phase 4: identity-indexed same-footprint + in-place + frame + termination in one statement; second client | `list_reverse_certified_total` statement; `tree_rotate_certified{,_total}` |
| F-07 upper-bound audit overstated (Medium) | Phase 0: wording. Phase 5: origin discipline (boundary exact-by-construction). This slice: pin completion | the sweep line (suite record test 7); 62 curated pins |
| F-08 runEffectful boundary (Known blocker) | Phase 5 fallback: minimal statement-carrying boundary, statement-borne origin-checked in-build; retirement upstream | sweep line: 13 carriers, each statement-borne; mover registered (Audit.lean header) |
| F-09 doc contradictions, no matrix (Medium) | Phase 0: the manifest is the authoritative matrix, gated; surfaces trued each phase; this slice fixed two Phase-5 staleness misses | gates 4 + 5; suite record findings 1-2 |
| F-10 whole-alloc ownership, no alloc rule (Known limitation) | Phase 2: ownership split + views + `wps_create` via allocator cursor | manifest `create` row (logic-rule cell green); `struct_create_store_wps` |

## Remaining registered items (honest, named, with owners)

1. **`runEffectful` upstream retirement** — the one boundary axiom;
   statement-borne only, origin-checked in-build. OWNER: the
   cerberus-lean/lem-lean register (upstream); on landing, the
   boundary here shrinks to the trio at a pin bump, no restatement
   (Audit.lean header carries provenance + status).
2. **`hfuel2`** — the second in-budget fuel hypothesis on the
   PARTIAL driveJ-lane loop exports (`counter_loop_certified`,
   `counter_loop_certified_registration`, `fib_certified`). The
   total lane has no fuel hypotheses; the partial lane's
   label-budget hypothesis stays. OWNER: this package (phase-5
   notes §7); mechanically removable if the partial lane ever
   rides the total lane's budget accounting.
3. **GF binder on `semantic_triple_sound`** (and `ProvenTriple`) —
   PERMANENT, load-bearing: the hypothesis is an Iris judgment, so
   the ghost-functor quantifier is the statement's honest type
   (walkthrough §5.4; census). Not scheduled for removal; recorded
   so the re-auditor does not read it as an oversight.
4. **Census freeze-gate** — CLOSED this slice (gate 5); listed here
   because the phase-4/5 notes carry it as open.
5. **`Ecase` EVAL arm (non-value scrutinees) and `Ewseq` at
   spec/sym binder patterns** — registered divergences (README
   register; Step.lean header): mechanical per-construct extensions
   through the generic route, path named. OWNER: this package, on
   demand.
6. **Cursor-owning adequacy LAUNCH variant** — `wps_create` is
   consumed at the wps level (`struct_create_store_wps`) and the
   production lane crosses creates as certified driver rounds; a
   cursor-emitting adequacy launch (`spikeGhost_init`-style lemma
   from initial-state health) is the named mechanical extension
   (phase-2 notes §3). OWNER: this package, on demand. Related:
   in-judgment `wpt_create` (manifest Notes 2 RED cell) with the
   same mover.
7. **Total rules for create/Ecase/Ewseq** — mechanical analogs of
   their wps rules, no consumer yet (manifest Notes 2 names them).
8. **Fuel parametricity of the production equations** — the
   `esize/pot ≤ lemDefaultFuel` side conditions; a fuel-irrelevance
   theorem or graceful-exhaustion argument would remove them
   (README divergence register).
9. **Quantified-seed production reversal** — structurally
   unavailable at the cold start (programs are finite artifacts;
   the initial memory is the shipped constructor); the quantified
   flagship theorems live on the drive lane
   (`list_reverse_certified{,_total}`), the production instance is
   the self-contained demo (phase-5 notes §2, design note).
10. **`stateInert` conservatism** (excludes memops/loads) — one
    predicate arm + one lemma arm per construct to extend
    (phase-3 notes §7).

## Where to start, re-auditor

The brief and terms: the original audit + its acceptance suite.
The claims surfaces to hold against the tree: README + walkthrough
+ the generated `docs/CAPABILITY_MANIFEST.md` (gate 4) + the
committed `docs/STATEMENT_CENSUS.txt` (gate 5). The trust
instruments: `CerberusHeapLang/Audit.lean` (sweep + origin
discipline + 62 exact pins), `scripts/test_unit.sh` (five gates).
The suite evidence: `docs/2026-09-01_acceptance-suite-record.md`.
The per-phase records: the dated notes cited above, in order.

## Arc close (2026-09-01)

The fresh foundational re-audit landed:
`docs/2026-09-01_foundational-re-audit.md` (repository-root `docs/`;
new auditor, every claim re-derived on this tree @ `4dc79a3`, gates
re-run independently, two mutation plants + one perturbation
re-executed end-to-end). **Verdict: ZERO High findings — the arc's
exit criterion is met.** Three Low findings (documentation /
instrument precision, none touching a theorem, a cone, or a gate's
soundness), all fixed in the arc-close commit ("foundations arc
CLOSED: …" — the commit that also commits the re-audit record and
this section): L2 — the statement census extended from the 12
verify-me theorems to 15, adding the three Phase-5 production
exports (`fib/counter_loop/list_reverse_certified_production`), so
gate 5's freeze now covers the arc's headline statement surfaces;
L1 — walkthrough §5.4 trued to the extended census (the extension
showed the production exports' IRIS bins are census-witnessed
EMPTY, so the old `counter_loop_certified_production` finite-map
cite was removed as wrong, correction noted in place); L3 — the
acceptance record's pin-coverage sentence trued (every EXPORTED
exhibit-table theorem exactly-pinned; the interior
`wp_store`/`wp_load` row sweep-BOUNDED only). Plus the re-audit's
cosmetic observation: the duplicate `wps_sound` pin in Audit.lean
deduped (63 → 62 `#guard_msgs` blocks, one per distinct theorem;
the sweep's source position moved to `Audit.lean:622`, expected-tail
quotes in README/walkthrough re-baselined to the re-run build's
verbatim output). Gate suite after the fixes: `ALL GATES GREEN`
(all five, manifest and census drift-free). **The foundations arc
is CLOSED; the port is unblocked.**

[AGENT 2026-09-01, alloc-arc P0]: the re-audit above is STRUCK as
acceptance record per the 2026-09-01 skeptical re-audit (it
validated names, not proof flow); see the R-01..R-11 closure table
in `docs/2026-09-01_alloc-arc-plan.md`.
