# cerberus-heaplang

A demonstration separation logic for the Cerberus Core engine — the
HeapLang-analog of the cerberus-lean semantics. A small Iris program
logic (points-to, the store/load small axioms, frame, sequencing,
consequence) is built over a tight fragment of the Core AST and then
**certified against the production cerberus-lean pipeline from cold
start**: the STRAIGHT-LINE exports quantify over the shipped
`initial_driver_state` and conclude equations about the very
`CerbND.runND (Driver.drive …)` composite that the cerberus-lean
executable runs; the LOOP exports certify against the engine's own
stepper lane, with the full-pipeline loop equation a registered
residual (see "Scope of the claims"). The exported theorems carry a definite qualifier
set, stated in full under "Scope of the claims" below; the analogy
to Iris HeapLang is in the ROLE (the demonstration language the
logic is exercised on), not the extent — unlike HeapLang this
package has no concurrency, no prophecy variables, no allocation
rule in the logic yet (the allocator-cursor resource is the
registered growth step), and a small lemma suite rather than
HeapLang's full library.

Phase 2 of the two-phase arc extends the fragment to a WHILE
LANGUAGE: branching (`Eif`, value-scrutinee `Ecase`), block entry
(`Esave`), the context-discarding jump (`Erun`), pure-expression
evaluation, binding via Core's own `Specified`-pattern lets, and
pointer arithmetic (`PEarray_shift`) — with a statement-stratified
WP (the classical label-context judgment), per-label invariant and
invariant+variant loop rules, and LOOP EXHIBITS certified through
the real engine end-to-end (the counter loop, iterative fib, and an
array-sum walk; fib additionally TOTAL and unconditional at the
drive lane).

**What this is NOT**: the RefinedC port. That development — the
Lean-native RefinedC-architecture verifier — lives alongside, in
this repository's root `RefinedCerberus` package, and is the actual
product; this package is a self-contained demo that the attachment
pattern (mirror step relation → Iris logic → per-rule engine
certification → production-entry export) works end-to-end.

## The trust story

The only trusted semantics is the cerberus-lean operational
semantics (the Lean port of Cerberus Core, pinned by commit in
`../scripts/semantics-pin.env` and differentially validated upstream
against the OCaml oracle); everything in this package is derived and
proved down into that engine. Every theorem is kernel-checked with
its exact axiom cone asserted in-build (`CerberusHeapLang/Audit.lean`,
the last import of the library root): all cones are exactly the
classical trio (`propext`, `Classical.choice`, `Quot.sound`), except
in the two production-entry modules (`ProdEntry`, `ProdExhibit`)
whose statements mention the shipped initial driver state and
therefore additionally carry the semantics repo's one residual axiom
`runEffectful` — a declared TEMPORAL boundary, entering through the
statements only, whose upstream retirement is planned (after which
this boundary vanishes at a pin bump with no restatement here).
Non-kernel proof methods (`native_decide`, `bv_decide`, `ofReduce*`)
are banned by a grep gate and would in any case enter a cone and
fail the audit — a build that weakens any of this fails.

## Scope of the claims

THE LOOP CLAIMS (phase 2). `counter_loop_certified`
(LoopExhibit.lean), `fib_certified` (FibExhibit.lean) and
`array_sum_certified` (ArrayExhibit.lean) certify authored Core
LOOPS — save entry, big-step guards, context-discarding back edges,
and (array-sum) interior loads with real pointer arithmetic —
against the engine's own `{step_ctx → sequential discharge}` loop
(`driveJ`, Adequacy.lean) at a proc-carrying thread whose label map
is tied to `core_run_state.labeled`: the engine never kills, never
derails, and a delivered value satisfies the data-dependent
postcondition (`fib n` from the Lean-side `fibSpec`; `vs.sum` with
the array preserved). These are PARTIAL-correctness statements with
in-budget fuel hypotheses — and, for `array_sum_certified`, stated
pre-state hypotheses: the coherence-seeded one-allocation array
(`hcoh`), per-element decode premises (`hdec`, rfl-dischargeable at
concrete engine-serialized bytes), and size/location side conditions
(`hsz`/`hlib`) — except `fib_certified_total`, which is
TOTAL AND UNCONDITIONAL: at the loop variant's step bound `2·n + 4`,
`driveJ` DELIVERS `fib n`, with no fuel hypotheses at all. Scope
honesty for all of them: the drive lane is the sequential driver's
loop projected to (thread_state, MemState) with the run state a
constant parameter (certified faithful for this fragment — the real
driver additionally ticks `aid_supply`, which the fragment ignores);
the PRODUCTION-pipeline export of a loop run (the `runND` equation)
is NOT yet established — the production tie delivered this phase is
the REGISTRATION equation (`fib_labeledAt_production` /
`loop_labeledAt_production`, ProdEntry.lean): the exhibits' label
maps are exactly what the shipped `collect_labeled_continuations_NEW
∘ initial_core_run_state` computes, so `LabeledAt` at the production
initial run state is derived, not hypothesized, and
`counter_loop_certified_production` re-exports the counter loop with
NOTHING hand-built in the label plumbing.

The flagship phase-1 demonstration is unconditional: `exhibitA_prod`
(ProdExhibit.lean) quantifies over nothing but the file-system state
`fs` and the argument list `args` — every other hypothesis is
discharged concretely — and concludes that the production run of its
create/store/load program IS the singleton Active execution
delivering 7 with the exact final bytes.

The GENERAL production-entry theorems are conditioned, and the
conditions are part of the claim. `sem_triple_prod` and
`prod_run_eq` (ProdEntry.lean) conclude their `runND` equation only
under: `hterm`, a proved in-budget-termination hypothesis for the
compute part (∀ aids, the drive completes to `.done v σfin` in k
steps); `hpre`, a proved setup-prefix alignment equation (the
program's prefix drives the production cold-start memory to the
footprint-satisfying configuration); and the fuel side conditions
`hfuel`/`hfuelc` (`esize … ≤ lemDefaultFuel = 10^6`, the engine's
own budget). `SemTriple` itself (Adequacy.lean) is PARTIAL
correctness — fuel exhaustion (`.more`) is unconstrained — under the
same fuel cap, and its conclusion constrains only the P ⊎ R split it
quantifies (untracked cells outside it are not claimed preserved by
the general statements; the production equation does pin the full
final `layout_state`). Everything is single-threaded, over the
certified fragment only (`store`/`load`/`create`, strong sequencing
`Esseq` at wildcard and `Specified`-binder patterns, `Esave`/`Eif`/
`Erun`, value-scrutinee `Ecase`, `PEsym`-shaped pure exits, the
`Load0` operand-evaluation step, `PEval`/`PEsym`/integer-`PEop`/
`PEarray_shift` operands, plus the run-time annotation residue), and the
logic has no `wp_create` small axiom (registered:
ProdEntry.lean:42-53 — a sound one needs the allocator-cursor
resource, the registered growth step). Each qualifier is registered
at source (module headers; `docs/2026-08-30_spike-report.md`); this
section is the summary the claims above are read under.

## Registered divergences and seams

Acceptable qualifiers are clear, known divergences with retirement
or growth paths. The register (each entry's home is authoritative):

| Divergence / seam | Discharge / path | Registered at |
|---|---|---|
| `runEffectful` in the production-entry statement cones | Temporal boundary; upstream retirement planned — vanishes at a pin bump, no restatement | `Audit.lean` header |
| tagDefs argument: the theorems pin `drive`'s tagDefs to `fmapEmpty`; the shipped `Main.lean:871` passes `CerbTags.tagDefs ()` after `setTagDefsIO` | Semantically forced equal for the synthetic file: `(prodFile e).tagDefs = fmapEmpty` by `rfl`; the effectful set-then-read global is inert here (scalar layout paths provably never read it; struct/union paths would) | This table + the spike report register (2026-08-31 merge audit) |
| Memory orders accepted arbitrarily: `Step.store`/`wp_store` hold at ANY `memory_order` | Mirror-true: the sequential driver drops `mo` (`action_request_sequential2`, Driver.lean:273 — `mo1` unused); NA-only side conditions would be a divergence FROM the engine | This table + the spike report register (2026-08-31 merge audit) |
| Whole-allocation byte-list cells (no per-byte split) | Registered growth step for structs | `Heap.lean` header; report R2 |
| `Ewseq` still outside the fragment; `Ecase`'s EVAL arm (non-value scrutinees) unmirrored | Mechanical per-construct extension, path named | `Step.lean` header; report "Honestly open" |
| PURE exits certified at `PEsym` shape only (general `PePure` exits are a bounded matcher extension) | Extend `stepDischarge_pure_sym` per-constructor when needed | `Soundness.lean` (S4); S4 slice notes |
| The array exhibit's pre-state is ONE allocation (not the amendment's ∗-of-cells): the engine's loads bounds-check against the pointer's PROVENANCE allocation and `arrayShiftPtrval` preserves provenance, so distinct-allocation "arrays" are not walkable in the engine — C's object model | Forcing fact about Cerberus, recorded; per-element structure lives in the index-partitioned invariant + decode premises | `ArrayExhibit.lean` header; S4 slice notes |
| LIST-REVERSE: registered STRETCH, not started (null encoding + node encoding + recursive representation predicate, each priced small) | Named prerequisites in the acceptance amendment | arc plan amendment; S4 slice notes |
| Production-face loop export (`runND` equation for a loop run) | The DriverCollapse scheduler equations are phase-1-profile-pinned; the drive-lane step bound (`fib_certified_total`) is the in-budget discharge waiting for it | `ProdEntry.lean` (S4 section); S4 slice notes |
| Fuel side condition (no fuel parametricity) | Fuel-irrelevance theorem for `get_ctx` or graceful driver exhaustion would remove it | report "What remains"; `ProdEntry.lean` header |
| No `wp_create` in the logic | Allocator-cursor resource in the state interpretation (registered growth step) | `ProdEntry.lean:42-53`; report D26 |
| D1 REMOVE-ANNOT value protocol; D3 canonical-annotation subrelation | Deliberate, engine-faithful readout composition | `Step.lean` header; slice notes |

## How to build

From the repository root (offline; deps resolve through the
container's git redirects, which `scripts/capped` self-loads):

```bash
scripts/setup-cerberus-dep.sh        # once: the pinned semantics workspace
cd cerberus-heaplang
../scripts/capped ~/.elan/bin/lake build
```

A green build is the verification run for exactly what the sweeps
check: it elaborates every proof through the Lean kernel and then
`Audit.lean`, which (1) bounds the transitive axiom cone of every
theorem in the package by the declared boundary, (2) pins the
headline theorems' exact cones, and (3) checks every constant of
every kind — defs included — for the banned axioms
(`sorryAx`/`ofReduceBool`/`ofReduceNat`). It certifies nothing
beyond that: in particular it does not discharge the scope
qualifiers above — they are part of the theorem statements. Expected
tail:

```
info: CerberusHeapLang/Audit.lean:342:0: CerberusHeapLang axiom sweep: 643 theorems within the declared boundary (40 in the production-entry boundary modules, trio + runEffectful; all others trio-exact)
info: CerberusHeapLang/Audit.lean:342:0: CerberusHeapLang banned-axiom sweep: 1319 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (433 jobs).
```

Or run both packages plus the grep gate: `scripts/test_unit.sh` from
the repository root.

## How to verify me

Spot-check the headline cones yourself (from `cerberus-heaplang/`):

```bash
../scripts/capped ~/.elan/bin/lake env lean --stdin <<'EOF'
import CerberusHeapLang
#print axioms CerberusHeapLang.semantic_triple_sound
#print axioms CerberusHeapLang.engine_complete
#print axioms CerberusHeapLang.counter_loop_certified
#print axioms CerberusHeapLang.fib_certified
#print axioms CerberusHeapLang.fib_certified_total
#print axioms CerberusHeapLang.array_sum_certified
#print axioms CerberusHeapLang.exhibitA_prod
#print axioms CerberusHeapLang.counter_loop_certified_production
EOF
```

Observed output (2026-08-31, this checkout):

```
'CerberusHeapLang.semantic_triple_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.engine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.array_sum_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified_production' depends on axioms: [propext,
 runEffectful,
 Classical.choice,
 Quot.sound]
```

Expected: everything reports exactly
`[propext, Classical.choice, Quot.sound]` except the two
production-entry statements, which additionally carry
`runEffectful` (the one declared temporal boundary, above).
`sorryAx` appearing anywhere is a failure.

## Worked tour (the modules, in build order)

| Module | Contents | Headline |
|--------|----------|----------|
| `Step.lean` | The fragment's mirror small-step over the ENGINE's generated AST/state types (values, `store`/`load`/`create`, strong sequencing at wildcard and `Specified`-binder patterns, `Esave`/`Eif`/`Ecase`, the global context-discarding `Erun`, pure/operand evaluation, the annotation residue; the runtime tuple carries the live env stack and the per-procedure label map) — hand-written, zero authority until certified | `Step` |
| `Heap.lean` | Points-to over the engine's memory state via iris-lean GenHeap (allocation-rooted byte-list cells); the memM-level store/load facts | `pointsToCell` (`↦c`), `storeM_success`, `loadM_success` |
| `Lang.lean` | The iris-lean `Language` instance over Step (evaluation contexts, wp_bind for real `Esseq`) | `instance : Language CoreExpr Mem Empty SpikeVal` |
| `EnvLaws.lean` | The env-map seam, closed (S4): lawfulness of the engine's symbol order (`Std.TransCmp` via the String×Nat lexicographic characterization) and the lookup-after-add law over reachable frames — loop invariants carry `SymFrame` instead of frame-shape pins | `envAdd_lookup` |
| `Rules.lean` | The base logic: small axioms, sequencing, frame, consequence, wand — plus the compositional exhibit-C triple and the interior-load memM fact | `wp_store`, `wp_load`, `wp_sseq`, `triple_frame`, `triple_seq`, `loadM_interior_int` |
| `Wps.lean` | The statement-stratified WP (the classical label-context judgment as a package-local guarded fixpoint): value/jump/step clauses, the jump-aware sequencing rules, the branch/entry rules, the small axioms at the stratum, the per-label invariant and invariant+variant loop rules, and the Löb-tied collapse into the base WP | `wps`, `wps_seq`, `wps_seq_spec`, `blockSpecs_intro(_variant)`, `wps_sound` |
| `Soundness.lean` | Per-construct certification of Step against the engine's own `step_ctx` + request discharge (context-undisturbed shape; refusals classified; the jump layer: the evaluator bridge, the factor theorem with the jump disjunct, the context-discard certification, the step-match completeness at the jump profile) | `engine_complete`, `stepDischarge_run`, `DecompJ.step_factor`, `engine_step_matchJ` |
| `Adequacy.lean` | The exported semantic face over engine configurations: triples with an arbitrary framed rest, driven by the engine's step function; the jump-profile drive lane (`driveJ`) with its adequacy and the S4 per-step drive equations | `semantic_triple_sound`, `semantic_frame`, `spike_engine_adequacy`, `engine_adequacyJ`, `driveJ_step` |
| `Exhibit.lean` | End-to-end exhibits at the engine level: store-then-load returns 7; the frame exhibit; termination of the probe as a theorem | `exhibitA_engine`, `exhibitB_engine`, `exhibitC_engine`, `exhibitA_terminates` |
| `LoopExhibit.lean` | THE FIRST LOOP (S3): the counter loop — save entry, real `x > 0` guard, a store under the loop, the context-discarding back edge — certified end-to-end through `driveJ` with a data-dependent post | `counter_loop_certified` |
| `FibExhibit.lean` | ACCEPTANCE EXHIBIT 1 (S4): iterative two-accumulator fib with the data-dependent invariant `a = fib i ∧ b = fib (i+1)`; partial via `engine_adequacyJ`, and TOTAL AND UNCONDITIONAL at the variant's step bound | `fib_certified`, `fib_certified_total` |
| `ArrayExhibit.lean` | ACCEPTANCE EXHIBIT 2 (S4): the array-sum walk — real pointer arithmetic, operand-evaluated loads, interior reads of the seeded array allocation, the `Specified`-binder unwrap, the index-partitioned invariant; the array preserved in the conclusion | `array_sum_certified` |
| `DriverCollapse.lean` | The production scheduler/ND/readout collapsed onto the demo's drive loop — proved from the driver's OWN round functions; entirely trio-exact | `prod_loop_done`, `driver2_done`, `finalize_done` |
| `ProdEntry.lean` | Cold start from the SHIPPED `initial_driver_state` (errno allocated by the real allocator) + the production-entry theorem; S4: the REGISTRATION TIE — `LabeledAt` derived from the shipped `collect_labeled_continuations_NEW` for the authored loop programs, and the counter loop re-exported at the derived tie | `sem_triple_prod`, `prod_run_eq`, `fib_labeledAt_production`, `counter_loop_certified_production` |
| `ProdExhibit.lean` | The demonstration: a self-contained program (create/store/load) run through the production pipeline delivers 7 with the exact final bytes | `exhibitA_prod` |
| `Audit.lean` | The in-build axiom gate: curated exact-cone pins + the exhaustive theorem sweep with the module-scoped `runEffectful` boundary + the banned-axiom sweep over every constant kind (all plant-tested both directions — see `docs/2026-08-31_restructure-notes.md`) | the sweeps |

History and design findings: the spike records in `docs/`
(`2026-08-30_spike-report.md` is the closing report; plan, recon and
slice notes alongside).

---

Built by AI agents (Claude, Anthropic) under the direction and
review of Mike Dodds.
