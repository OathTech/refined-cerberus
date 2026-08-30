# Spike report: a minimal separation logic over the real Core semantics

[AGENT 2026-08-30] The spike's closing report (plan:
`2026-08-30_spike-minilog-plan.md`; records: `…_spike-recon.md`,
`…_spike-sliceA-notes.md`, `…_spike-sliceB-notes.md`). Everything
below is committed and gated on this branch (`spike-minilog`,
semantics pin 8fb380c9c): 196 theorems in the sweep, all axiom cones
exactly the classical trio, no sorries, no non-kernel methods, no
fuel/recursion-limit bumps.

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
