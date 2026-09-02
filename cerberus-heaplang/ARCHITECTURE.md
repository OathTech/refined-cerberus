# cerberus-heaplang — the architecture, normatively

What this package proves, and where each claim rests. Every sentence
names its theorem. The [README](README.md) carries the exhibits table,
the register of limitations and the build recipe; the
[walkthrough](docs/WALKTHROUGH.md) quotes the definitions.

## 1. The semantic authority: the engine

The only semantics is the cerberus-lean engine: the generated Core
types and the functions `step_ctx`, `action_request_sequential2`,
`loadM`/`storeM`/`allocateObject`, and the shipped driver composite
`CerbND.runND (drive fmapEmpty false file args) (initial_driver_state
sup file fs).1`. Nothing in this package has semantic authority of its
own: every exported theorem is a statement about the engine's
execution and memory states, and a disagreement between any
definition here and the engine is a defect here. The engine is
trusted as a policy decision — the Lean port is differentially
validated against the OCaml Cerberus, not proved equivalent to it
(README, "What you are asked to take on faith").

## 2. The mirror, and its one-directional certification

Iris needs a fuel-free small-step relation; the engine's `step_ctx` is
fuelled and monadic. `Step M` (Step.lean) is the hand-written mirror —
a relation on (Core expression, environment stack, memory) covering
the fragment `Frag` (Soundness.lean) — and it is the `primStep` of the
iris-lean `Language` instance (Lang.lean). The mirror has no
authority; its certification is `engine_step_matchU` (Soundness.lean):
on `Frag`, at a `SeqWF` context with `esize e ≤ lemDefaultFuel`, every
mirror step is exactly the engine's singleton successful round,
`outcomesU M aid e ρ σ = [.next (M.thread e' ρ') σ']` — the relation
`CerberusRound M aid` (Round.lean), the graph of one discharged
`step_ctx` round. That round is the mirror's only reference: no other
relational semantics is referenced or bridged, and none is needed for
the root of trust, which is the engine (§1).

The certification is ONE-DIRECTIONAL: mirror step ⇒ engine round.
`step_iff_cerberusRound` is two-sided only under the hypothesis that a
mirror step exists. `cerberusRound_classify` sorts every `Frag`
configuration into `value_done`/`value_annot`/`step`/`refused`, and its
`refused` arm records only that the mirror is stuck: no engine fact is
proved there, except at the store/load/create/case redexes
(`cerberusRound_refused_store`/`_load`/`_create`/`_case`). So the logic
is SOUND (§4) but not proved COMPLETE for the fragment — a
configuration the mirror refuses may be one the engine executes; no
export says anything about it. Mirror completeness on the fragment is
the registered open item (§7). What is established, in the auditor's
words: "a sound Iris program logic for the package's restricted
relational mirror, with a verified forward connection to successful
Cerberus engine rounds on proved-safe executions".

## 3. The two judgments

The small axioms are proved once as atomic step specifications
(`AtomicStep`, Rules.lean: `store_atomic`, `load_atomic`,
`storeAt_atomic`, `loadAt_atomic`, `create_atomic`), each against
`Step` and the real `storeM`/`loadM`/`allocateObject`, and lifted by
`wp_of_atomic` (raw WP), `wps_of_atomic` and `wpt_of_atomic`. `wps`
(Wps.lean) is the partial label-context judgment, a guarded fixpoint
over iris-lean's WP; `wpt` (Wpt.lean) is the total judgment by
recursion on a step budget with the mandatory back-edge decrease
(`1 + m ≤ k` in `wpt.pre`). Frame across back edges:
`wps_frame_labels`/`wpt_frame_labels`; loops: `blockSpecs_intro`/
`blockSpecsT_intro`; collapses: `wps_sound` (Löb) into WP, `wpt_sound`
into TWP (a metatheorem no export consumes). There is no raw-WP
sequencing rule: at a populated label map it is false (Rules.lean).

## 4. Adequacy

Partial: `spike_step_adequacy` (Adequacy.lean) is iris-lean's
`wp_strong_adequacy_gen` with the ghost state constructed
(`genHeap_init`, `spikeCells_alloc`; `launchResources` under
`LaunchCoh` for allocating programs), and `engine_adequacyU`
(`_alloc`) turns it into the engine fact: `driveU` never kills, never
gets stuck, and `.done v σ'` implies the readout `ψ v σ'`, at every
drive length. Total: `wpt_drive_aux` and `wpt_engine_boundU`
(`_alloc`, TotalAdequacy.lean) realize the budget as a drive length:
`driveU M aids k … = .done v σ'`. Both are stated over `driveU`
(Adequacy.lean), this package's loop {`step_ctx` → `dischargeStep`}.
Why the mirror suffices: `NotStuck` supplies a mirror step at every
reachable configuration and `engine_step_matchU` makes it the
engine's round (`drive_classifyU`).

## 5. The projection

`project_triple_pure` (Adequacy.lean): any Iris triple whose
precondition is footprint ownership and whose framed post pure-entails
`ψ R w.val σ'` under the coupling invariant projects to the Iris-free
`MemTripleU M ρ e P ψ` — memory splits as P ⊎ R, `driveU` never kills
or derails, every delivered `(v, σ')` satisfies `ψ R v σ'`.
`project_triple_pure_alloc` is the allocating twin (`allocCap reqs` in
the precondition, `MemTripleU_alloc` under `LaunchCoh`). The one
Iris-shaped hypothesis is discharged by `cellOwn_consequence`,
`pointsToCell_consequence`, `cellsOwn_consequence`,
`cells_consequence` and the `pure_`/`sep_`/`or_`/`exists_consequence`
combinators; the pure memory view they deliver is `CellCoh`/`Sat`.

## 6. The two trust claims, and the two lanes

(1) The closed-program exports have Iris-free statements; iris-lean
appears only inside kernel-checked proof terms and contributes no
axiom — every export's axiom set is exactly `propext`,
`Classical.choice`, `Quot.sound` (Audit.lean). (2) The reusable rules
are stated in Iris; `pointsToCell`, `cellOwn`, `allocCap`, the WP and
BI connectives, and `CohG` (in the one hypothesis `hpost`) are
definitions to read, not axioms to accept.

THE ROOT-OF-TRUST LANE (total): `exhibitA_prod` (ProdExhibit.lean),
`fib_certified_production`, `counter_loop_certified_production`,
`list_reverse_certified_production` (ProdLoopExhibit.lean), through
`wpt_driver_done_alloc` (ProdLoop.lean) and `prod_run_eqJ`
(ProdEntry.lean). Their execution function is the shipped composite
of §1; no package definition appears in their statements except the
authored programs and the pure readout predicates. The headline claim
of this package rests on them.

THE PROVISIONAL LANE: `MemTripleU`, `MemTripleU_alloc`, `SemTripleU`,
`project_triple`, `project_triple_pure`, `project_triple_alloc`,
`project_triple_pure_alloc`, `semantic_triple_soundU`,
`semantic_frameU`, `engine_adequacyU`, `engine_adequacyU_alloc`,
`wpt_engine_boundU`, `wpt_engine_boundU_alloc`, and every exhibit
stated over `driveU` (`*_certified`, `*_total`, `*_engine`,
`*_adequacy`, `*_launch_smoke`, `counter_loop_certified_registration`).
PROVISIONAL means exactly: a sound fact about `driveU`, this package's
loop around the engine's `step_ctx`; not yet the root-of-trust
statement, which is over the shipped driver and awaits the
cerberus-lean fuel-exhaustion outcome
(`../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`);
restated with no other change when it lands. The obstacle: the
shipped driver's out-of-fuel arm is LemLib's kernel-opaque
`fuelExhaustedWith`, so no statement quantifying over all fuels can
classify its outcomes; `driveU` is tied to the shipped driver by
`loop_step_frag` (DriverCollapse.lean) only where the mirror steps,
which is what the total lane consumes.

## 7. Open items

- Mirror completeness on the fragment (§2): for every `Frag`
  constructor, mirror stuck ⇒ an engine refusal or kill fact.
- The fuel-exhaustion request (§6): a transparent, distinguished
  fuel-exhaustion outcome in the engine's driver monad.
- Footprint-relative freshness: `LaunchCoh` (Adequacy.lean)
  constrains tracked cells only (`id_lt`, `addr_lo`), so a `create`
  (`wps_create`/`wpt_create`) is fresh from the logical footprint, not
  from untracked allocations an arbitrary concrete state may carry
  below the cursor; the production cold-start state is globally well
  formed (`prodMem₀_launchCoh`, ProdEntry.lean). A global memory
  well-formedness invariant is registered for the malloc/free
  extension.
- The deferred parametric semantics interfaces: the rules are proved
  directly against `Step` and the memory state (walkthrough §7).
