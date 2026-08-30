# Spike report: a minimal separation logic over the real Core semantics

[AGENT 2026-08-30] The spike's closing report (plan:
`2026-08-30_spike-minilog-plan.md`; records: `…_spike-recon.md`,
`…_spike-sliceA-notes.md`, `…_spike-sliceB-notes.md`). Everything
below is committed and gated on this branch (`spike-minilog`,
semantics pin 8fb380c9c): 196 theorems in the sweep, all axiom cones
exactly the classical trio, no sorries, no non-kernel methods, no
fuel/recursion-limit bumps. (Since amended: exhibit C brought the
sweep to 209; Extension D — the production-driver coupling, §Extension
D below — brings it to 287, of which 34 sit in the two declared
production-entry boundary modules whose cones are trio +
`runEffectful`; everything else remains trio-exact.)

## The headline theorem ([USER 2026-08-30], the required shape)

For the fragment (pure values; positive strong `store`/`load`;
wildcard `Esseq`; the run-time `Eannot` residue), semantic triples
over ENGINE configurations, verbatim from `Spike/Adequacy.lean`:

```lean
def SemTriple (e : CoreExpr) (P : CellMap)
    (post : value → CellMap → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat σ (Iris.Std.PartialMap.union P R) →
  ∀ (n : Nat) (aids : Nat → Nat), esize e + n ≤ lemDefaultFuel →
    (∀ r, drive aids n (spikeThread e) σ ≠ .killed r) ∧
    (drive aids n (spikeThread e) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), drive aids n (spikeThread e) σ = .done v σ' →
      ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧ Sat σ' (Iris.Std.PartialMap.union Q R))

theorem semantic_triple_sound {GF : BundledGFunctors} [SpikeGpreS GF]
    {e : CoreExpr} (hfrag : FragP e) {P : CellMap}
    {post : value → CellMap → Prop}
    (hwp : ProvenTriple GF e P post) :
    SemTriple e P post

theorem semantic_frame {GF : BundledGFunctors} [SpikeGpreS GF]
    {e : CoreExpr} (hfrag : FragP e) {P : CellMap} (F : CellMap)
    {post : value → CellMap → Prop} (hPF : P ##ₘ F)
    (hwp : ProvenTriple GF e P post) :
    SemTriple e (Iris.Std.PartialMap.union P F)
      (fun v Q => ∃ Q₀ : CellMap, post v Q₀ ∧ Q₀ ##ₘ F ∧
        Q = Iris.Std.PartialMap.union Q₀ F)
```

Reading: for any cerberus configuration whose memory splits as
P ⊎ R — footprint P satisfied (`Sat` = the Coh coupling: cells live,
writable, in-bounds, exact bytes, range-disjoint, side-table-inert),
rest R ARBITRARY — driving the ENGINE (`drive` = iterate `step_ctx` +
the sequential driver's request discharge, Driver.lean:273) never
kills (no UB, no error-kill, no ILLTYPED) and any delivered value v
satisfies the post with THE SAME R verbatim. Pre/post obey the frame
rule (`semantic_frame`; the R-quantifier is itself the unnamed-frame
closure). `drive`, `Sat`, `CellMap`, `esize` are engine/footprint
vocabulary; the Iris WP appears only inside `ProvenTriple`, the
interior "the derived logic proved it" judgment. Partial correctness:
fuel exhaustion (`.more`) is unconstrained; the fuel side condition
is the engine's own get_ctx budget (opaque exhaustion leaf —
fail-closed), with `esize` growing ≤ 1 per step.

The acceptance package (small axioms, FRAME, SEQ, CONSEQUENCE,
wp_wand, the operator's exhibit, the anti-frame negative test) was
proved in slice A over the mirror `Step`; slice B gives it this
engine-level meaning.

## Certification direction (artifact 4) — what is proved and why it suffices

ENGINE-COMPLETENESS ON THE FRAGMENT, per construct
(`Spike/Soundness.lean`, `engine_complete`): at every fragment
configuration the engine's step list is a SINGLETON whose discharge
is matched by `Step` — a Step-transition, the value protocol
(PROGRAM-DONE / the REMOVE-ANNOT tau that Step treats as a value —
the D1 readout composition), or a REFUSAL (NDkilled / Step_error2) at
a configuration where Step provably has NO step. This direction
suffices for adequacy: the WP's NotStuck obligation keeps every
reachable configuration Step-reducible-or-value, so the engine's one
behavior is always Step-matched (staying in the WP-covered cone) —
refusals would contradict NotStuck. The converse (every Step is
engine-realizable) is NOT claimed and was not needed; the per-rule
active-path equalities are exact, so nothing rests on Step
over-approximating. K1 (the pre-registered "no seam without whole-run
machinery" kill) did NOT fire: the judgments contain no runner, no
fuel-runner, no driver_state.

The per-rule statements are in the operator's "context undisturbed"
shape: all non-expression, non-memory machine components quantified
and returned VERBATIM (the locality conditions of abstract separation
logic, proved of the engine's own step function), with the measured
untouched / read-only-under-WF / touched partition per component in
the slice-B notes (D14) — tagDefs read only by store's operand
encoding, env read only by the betas (nonemptiness premise, wildcard
update = identity), stack/parent read only by PROGRAM-DONE,
everything else inert; memory touched only through the request
discharge; the run state returned verbatim (∀ rs), with the driver's
per-action aid tick mirrored as a quantified parameter.

## What was settled (decision → where it lives)

- Coupling seam: memM one-level application for the small axioms +
  step_ctx/discharge certification for Step — recon §5.4's two-level
  recommendation, now THEOREMS (Heap.lean storeM_success/
  loadM_success; Soundness.lean).
- The boundary architecture: decomposition judgment `Decomp` +
  per-rule engine equations + `engine_complete` (slice-B notes D13).
- The exported face: `SemTriple`/`ProvenTriple`/`semantic_triple_sound`/
  `semantic_frame` (Adequacy.lean; D16-D17).
- Ghost-state construction: `SpikeGS` built inside adequacy by
  `genHeap_init` over the initial cell map (spike_step_adequacy) —
  slice A's D11 honest gap CLOSED.
- Side tables: symbolic with per-cell inertness premises (D18) — no
  global pins in the exported theorem.
- Fuel honesty: `esize … ≤ lemDefaultFuel` side conditions (D19).
- The engine drive: `drive` (Adequacy.lean) = the recon's discharge
  loop as a definition; the three projections from
  action_request_sequential2 each cited (D15).

## The exhibits (Spike/Exhibit.lean)

- `exhibitA_semantic` : SemTriple for `lets _ = store(x,7) in load(x)`
  at footprint {x-cell}: any delivery is `Specified(7)` with x's cell
  updated. `exhibitA_engine` instantiates it at the recon's seeded
  state (two engine `allocateObject`s from `{}` — the seeded state is
  a TEST INSTANCE only, absent from exported quantifiers), and
  `exhibitA_terminates` is the recon probe AS A THEOREM: six drive
  steps end in `.done Specified(7)` (termination by simulation from
  the same certification lemmas; safety+value uniqueness by
  adequacy).
- `exhibitB_semantic` : THE OPERATOR'S FRAME EXHIBIT end-to-end —
  `semantic_frame` applied to the store's footprint triple with y's
  cell as the named frame: ⦃x ↦ - ∗ y ↦ a⦄ store(x,7) ⦃x ↦ 7 ∗ y ↦ a⦄
  over engine configurations. `exhibitB_engine` reads it back at the
  seeded instance: the final bytemap holds 7's image at x and y's
  bytes UNCHANGED.

## What was found (beyond the plan)

- The annotation layer is real but bounded (slice A D8): Eannot is
  NOT an evaluation context; the Löb reindexing pair
  (wp_annot_reindex/wp_annot) is the reusable asset.
- K2 (step_ctx symbolic-unfolding perf) did NOT fire: with the
  decomposition-equation staging, each per-rule proof reduces the
  step_ctx body in well under a second (D13). The real perf hazard is
  elsewhere: TreeMap-backed state is defeq-opaque, and unstaged rfl
  near it hits recursion limits — the staging discipline is D22 (the
  defeq sibling of slice A's D12 matcher finding).
- The engine's ILLTYPED store arm is certified as a refusal with its
  verbatim message; Step's stuckness there is a theorem (D23).
- Engine memory locality needed NO new lemma: writeBytesTo's
  range-locality + the untouched allocation table (already slice A's
  Coh.store) carry the verbatim-rest conclusion (D17).
- get_ctx's opaque fuel leaf forces (and honestly documents) the
  fuel side condition (D19).
- Recon corrections already recorded in slice A stand; slice B adds:
  the frozen-context instruction itself was superseded by the
  ∀-context forms (the freeze survives only as the adequacy drive's
  launch profile), and the "seeded initial MemState" adequacy
  phrasing was operator-corrected to the splitting form before
  landing (D17).

## Honestly open

- Ewseq: still out (slice A D6) — mechanical extension (LETW rules
  are shape-identical), plus a second Context instance.
- The soundness direction (Step ⊆ engine) is unclaimed (not needed
  for adequacy; see above). If a future consumer wants "Step-traces
  are engine-realizable", the active-path per-rule equations are
  already iff-grade — the work is only assembling them.
- `EngineOutcome.offFragment`: that storeM/loadM never produce
  ND-fork nodes is asserted by recon body-inspection, deliberately
  unproved (refusal-classification made it unnecessary; D15).
- Termination is not claimed in SemTriple (partial correctness);
  exhibit (a)'s termination is by per-instance simulation.
- The fuel side condition (`esize e + n ≤ 10^6`) is an honest engine
  artifact; a fuel-irrelevance theorem for get_ctx (stability above
  the spine depth) would remove it from the statement and is routine
  but was not needed at spike scale.
- The de-pin's full-build shape — ghost ownership of the
  union-member/function-pointer tables (funptrmap ↔ the donor's
  fntbl_entry analog) — is specified but not built; `dec_indep` is
  its degenerate case (D18).

## Derisk register: CLOSED

- R1 (coupling seam): RETIRED. Two-level seam proved end-to-end:
  memM one-level facts under the WP, step_ctx+discharge certification
  above, semantic triples exported; no driver_state/fs/trace anywhere
  in judgments.
- R2 (points-to basis): RETIRED at spike scale. The allocation-rooted
  byte-list cell carried the small axioms, frame, the type-compat
  discharge, AND the engine readout; per-byte splitting remains the
  registered growth step for structs (unchanged).
- R3 (WP form): RETIRED (slice A) — iris-lean WP with full mask/fupd
  discipline in live use; adequacy consumed wp_strong_adequacy_gen
  as-is.
- R4 (UB channel): RETIRED. UB-exclusion = NotStuck is now an ENGINE
  fact: SemTriple's no-kill covers the full recon §2.6 vocabulary
  including the non-UB `Other` arms and the ILLTYPED refusal.
- R5 (provenance honesty): RETIRED (slice A; unchanged) — x is a real
  PointerValue; the certification consumed it as-is.
- R6 (bind story): RETIRED (slice A) — Iris bind over real Esseq;
  slice B adds the engine-certified beta/congruence lemmas beneath
  it. Named residual cost: the annotation layer (D8), now with its
  engine-side counterpart certified (LETS-ANNOT/ANNOTS/REMOVE-ANNOT).

## Stretch S1: skipped

Not attempted, per the gate ("only if 1-4 land green with headroom"):
the three mid-slice statement upgrades (context-undisturbed forms,
the semantic-triple face, the side-table de-pin) consumed the
headroom. The substrate S1 wants is confirmed present: `StorableAt`
(now with decode-side inertness) is the `v ◁ᵥ ty` precursor, and
`ProvenTriple`'s footprint interface is where `intT`'s
ty_deref/ty_ref factorization would sit.

## What this means for the full build (short, factual)

- The attachment pattern is validated end-to-end at minimum scale:
  hand-written mirror Step → Iris logic over it → per-rule engine
  certification → configuration-level semantic triples with frame.
  Nothing in the chain needed whole-run machinery, new axioms, or
  non-classical tricks.
- The per-construct certification cost is real but linear and
  mechanical: one decomposition case + one engine equation + one
  discharge lemma per construct; adding a Core construct does not
  disturb existing rules. Ewseq/Eif are next and look routine.
- The three known recurring costs to budget: the annotation layer
  (once per continuation-rewrapping construct), staging discipline
  around defeq-opaque generated state (D12/D22), and WF premises
  surfacing per rule (env nonemptiness, encoding facts) — each is
  the kind of premise the future typing stratum discharges.
- The exported SemTriple shape is what the RefinedC-style typing
  layer should target; its footprint/inertness premises are the
  degenerate forms of ghost state the full build will own
  (side tables, allocation metadata).

## Extension D: the production-driver coupling ([USER 2026-08-30], "extend this to cover the real engine, not our hand-rolled driver")

The drive-vs-production delta is retired: the semantic triples are
re-exported against the SHIPPED pipeline — `CerbND.runND` of
`Driver.drive` from `initial_driver_state` (Driver.lean:435, the
production constructor; the exact composite Main.lean:857-885 runs),
through the `finalize`/`Driver.hack` readout. New modules:
`Spike/DriverCollapse.lean` (D1-D3), `Spike/ProdEntry.lean` (D4 cold
start + the theorem), `Spike/ProdExhibit.lean` (the demonstration);
`create` joined the fragment (Step.lean rule + full certification in
Soundness.lean).

### The production-entry theorem (verbatim, `Spike/ProdEntry.lean`)

```lean
theorem sem_triple_prod
    (e : CoreExpr) (hfrag : FragP e)
    -- the compute part and its exported triple
    (ec : CoreExpr) (P : CellMap) (post : value → CellMap → Prop)
    (hsem : SemTriple ec P post)
    -- the frame quantifier, as in SemTriple
    (R : CellMap) (hdisj : P ##ₘ R)
    -- the program's prefix drives the production cold-start memory to
    -- a configuration satisfying P ⊎ R in j steps (engine vocabulary)
    (σc : Mem) (j : Nat)
    (hpre : ∀ (aids : Nat → Nat) (n : Nat),
      drive aids (j + n) (spikeThread e) prodMem₀ =
        drive (fun i => aids (i + j)) n (spikeThread ec) σc)
    (hsat : Sat σc (Iris.Std.PartialMap.union P R))
    -- termination of the compute part within the production budget
    (v : value) (σfin : Mem) (k : Nat)
    (hterm : ∀ aids : Nat → Nat,
      drive aids k (spikeThread ec) σc = .done v σfin)
    (hfuel : esize e + (j + k) + 2 ≤ lemDefaultFuel)
    (hfuelc : esize ec + k ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args)
          (initial_driver_state (prodFile e) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = v ∧
      dst'.layout_state = σfin ∧
      ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧
        Sat σfin (Iris.Std.PartialMap.union Q R)
```

`prodFile e` is the synthetic one-procedure file (main := a
parameterless Proc with body `e`); `prodMem₀` is the production
cold-start memory (initialMemState + the driver's own errno
allocate-and-zero, derived through engine functions only). Nothing
hand-built enters the quantifiers: the initial state is literally
`initial_driver_state (prodFile e) fs`. The conclusion is an
EQUATION: the production run IS the singleton Active execution —
killed/stuck productions are excluded by the equation itself, and
completed runs' value and final memory satisfy the postcondition
with the frame `R` verbatim, exactly SemTriple's splitting
quantifier. The engine-only supporting form (`prod_run_eq`) pins
additionally `dres_blocked = false`, `dres_stdout = dres_stderr = ""`.

### The demonstration (`Spike/ProdExhibit.lean`)

Exhibit A re-exported at this level on a fully SELF-CONTAINED
program (D4's cold start — the program creates its own cell with the
engine's `create` at the address the production allocator
deterministically mints; errno is production allocation id 0, the
program's cell id 1):

```lean
theorem exhibitA_prod (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile progAProd) args)
          (initial_driver_state (prodFile progAProd) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = sevenVal ∧
      CerbMem.readBytesFrom dst'.layout_state pxAddr 4 =
        (CerbMem.memValueToBytes [] sevenMval).2
```

where `progAProd = lets _ = create(4, int) in (lets _ = store(x,7)
in load(x))` at x = the production cell. The compute part goes
through the UNCHANGED slice-B logic (wp_store/wp_sseq/wp_load →
semantic_triple_sound); the create prefix and termination are
concrete engine facts on the cold-start states.

### The obligations, discharged

- **D1 scheduler collapse** (`DriverCollapse.lean`): one iteration
  of the production per-thread loop `drive_nonmemory_steps_aux2`
  (Driver.lean:346-351) = the spike drive-loop body, proved by
  unfolding the driver's own round functions (`loop_step_tau`/
  `loop_step_action`/`loop_step_done`; the action path goes
  advance_step → liftCore_run → perform_action_request2 (the
  fresh_action_id' draw, Driver.lean:283) →
  action_request_sequential2 (Driver.lean:273) — the exact composite
  `dischargeStep` mirrors). Iterated: `prod_loop_done` — production
  driving = the spike drive, for fragment configurations. The outer
  `driver2` round (`driver2_done`) routes PROGRAM-DONE through
  `process_core_step2`/`prepare_exit`; the opaque execution-mode
  read (`CerbGlobal.current_execution_mode`, an `opaque` constant)
  is handled by CASES — both scheduler branches reduce to the same
  singleton pick on a one-thread fragment state.
- **D2 ND collapse**: the fragment path of the whole driver
  computation is a one-layer NDactive tree (`runOne` layer:
  bind/liftND/liftCore_run composition lemmas — each bind spends one
  layer of its own fresh fuel budget, never accumulating; `pick` on
  a singleton is `NDactive`, no ND node);
  `runND_active` (an EMPTY axiom cone) lifts it to the runner:
  exactly one execution.
- **D3 readout**: `hack_value` (`step_eval_pexpr`'s PEval arm is the
  identity, `valueFromPexpr` reads it back — one fuel layer) +
  `finalize_done` (the PROGRAM-DONE parked state reads out to the
  delivered value, io streams folded from the untouched initial io).
  The annot value form never reaches `hack`: the REMOVE-ANNOT tau
  precedes PROGRAM-DONE (the D20 value protocol, composed inside
  `prod_loop_done`).
- **D4 cold start**: `create` joined the fragment mirroring the
  store pattern (Step rule + createRedex/Redex/Decomp +
  `step_ctx_create` context-undisturbed + `dischargeStep` Create arm
  + engine_complete case); the production setup prefix
  (spawn/main-lookup/errno) is collapsed by `drive_after_setup` with
  the errno allocation done by the real
  `allocateObject`/`storeM` on the cold state.

### The cone answer (D5): the known unknown, resolved

`runEffectful` DOES enter — exactly where anticipated, and ONLY
there. Which definition drags it in: `initial_driver_state`
(Driver.lean:435) → `initial_core_run_state`
(Core_run_aux.lean:395), whose `sym_supply` is
`runEffectful (fun () => CerberusFresh.freshIntIO ())` —
`runEffectful` is LemLib's one residual axiom (lem-lean
lean-lib/LemLib.lean:54; the semantics repo's TODO/DESIGN register
owns its removal). It enters through the theorem STATEMENTS (the
constant's definition cone), not through any proof step, and the
theorems hold for every value of the seam (the fragment never reads
sym_supply — the D14 partition's row). Cones, pinned in Audit.lean:

- the ENTIRE collapse layer (`DriverCollapse.lean`: prod_loop_done,
  driver2_done, finalize_done, the loop/discharge lemmas):
  EXACT TRIO (`runND_active`: empty cone);
- the entry theorems (`prod_run_eq`, `sem_triple_prod`,
  `exhibitA_prod`): exactly
  `[propext, runEffectful, Classical.choice, Quot.sound]`.

Audit.lean declares the boundary per its header discipline: a
module-scoped boundary (ONLY `Spike.ProdEntry`/`Spike.ProdExhibit`
may carry `runEffectful`; every other module is held to the trio by
the sweep), with provenance TEMPORAL and the mover named (the
semantics repo's register owns `runEffectful`; when its deletion
lands there, the boundary here shrinks back to the trio with no
statement change on our side). The modified sweep is plant-tested in
both directions (a runEffectful statement outside the boundary
modules fails; a sorry inside them fails).

### Design finding: no unconditional `wp_create`

An unconditional `wp_create` small axiom is UNPROVABLE in the
slice-B logic: `allocateObject` can kill ("out of memory",
CerbMem.lean:1479) from configurations the footprint does not
constrain, so the WP's NotStuck obligation cannot be established
from cell ownership alone. A sound `wp_create` needs an
allocator-cursor resource in the state interpretation (the
registered full-build shape; `genHeap_alloc` is then its ghost
step). Extension D therefore adds `create` at the
Step/certification level only, and cold-start programs run their
create prefix on the production-pinned initial memory, where
allocation success is a theorem. Recorded in
`ProdEntry.lean`'s header and slice-B notes D26.

### What remains (out of Extension D's scope, named)

- **Fuel parametricity.** The production loop's fuel-exhaustion leaf
  is the opaque `fuelExhausted` (fail-closed, D19): at insufficient
  fuel nothing about the production value is provable, so
  `sem_triple_prod` carries a termination-within-budget hypothesis
  (`hterm` — for the exhibits a 6-step simulation; the budget is
  10^6). Removing it needs either graceful exhaustion in the driver
  or fuel-parametric drive statements.
- **Ewseq** (and Eif): still outside the fragment; per-construct
  certification cost is linear and mechanical, but each new
  construct now also adds one loop-iteration case to
  `prod_loop_done`.
- **Untracked-preservation export**: the production equation pins
  layout_state and the driver_result; the remaining driver_state
  components (trace contents, dr_step_counter, core_run_state0) are
  existentially absorbed — exporting their exact values (the trace
  as a checkable execution record) is unclaimed.
- **The allocator-cursor resource** (above): the ghost-side create
  story for arbitrary configurations.
