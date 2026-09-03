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
own. Every exported execution theorem is either explicitly provisional
over driveU or reaches the shipped engine; every public logical rule
has a kernel-checked adequacy path through the package mirror to the
engine. (The reusable rules and assertion laws are statements in Iris
over the mirror `Step` and the ghost resources, §3, §6; what makes them
statements about the engine is that adequacy path, not their own
text.) A disagreement between any definition here and the engine is a
defect here. The engine is trusted as a policy decision — the Lean port is differentially
validated against the OCaml Cerberus, not proved equivalent to it
(README, "What you are asked to take on faith").

## 2. The mirror, and its one-directional certification

Iris needs a fuel-free small-step relation; the engine's `step_ctx` is
fuelled and monadic. `Step M` (Step.lean) is the hand-written mirror —
a relation on (Core expression, environment stack, memory) covering
the fragment `Frag` (Soundness.lean) — and it is the `primStep` of the
iris-lean `Language` instance (Lang.lean). The mirror has no
authority; its certification is `engine_step_matchU` (Round.lean): on
`Frag`, at a `SeqWF` context with `esize e ≤ lemDefaultFuel`, every
mirror step is exactly ONE ITERATION OF THE SHIPPED DRIVER'S THREAD LOOP
— the relation `CerberusRound M` (Round.lean): at every driver state
embedding the context and the configuration (`MachineCtx.Embeds`), the
engine's step list is a singleton `s`, `s` is advanceable
(`can_advance`), and the shipped `advance_step` on it is one active
wakeup-free transition to the state embedding the mirror's successor.
The round is stated at the loop body (no fuel dependency; its
loop-level reading `CerberusRound.loop_step` holds at every fuel), in
the driver's own vocabulary only: the hand-written discharge
`dischargeStep`/`outcomesU` is a proof device of the `driveU` lane and
appears in no export's statement (the trust rule of 2026-09-02). That
round is the mirror's only reference: no other relational semantics is
referenced or bridged, and none is needed for the root of trust, which
is the engine (§1).

The certification is ONE-DIRECTIONAL: mirror step ⇒ shipped round;
`step_iff_cerberusRound` is two-sided under the hypothesis that a
mirror step exists. COMPLETENESS is the other direction, per
constructor: `frag_round_complete` (Round.lean) states that at every
non-value `Frag` configuration the mirror steps, or the shipped round is
a classified REFUSAL (`ShippedRefusal`: ILLTYPED — the step list is
`[Step_error2 msg]`; KILL — the shipped `advance_step` returns
`NDkilled r` for an engine `kill_reason` — memory kills through
`liftMem`, pure-evaluator kills `Other (DErr_core_run err)` through
`liftCore_run`; ILLTYPED AT DISTANCE ONE — a successful round into a
configuration whose next step list is `[Step_error2 msg]`, the
load/store ACTION_EVAL at a non-pointer value; FORK — the shipped runner
`CerbND.runND` delivers at least two executions; PANIC — the redex's
monad, the successor's environment, or the jump's label-lookup key IS
the engine's own `failwithI`), or the configuration is in the RESIDUAL
(`OpenRound`, two arms, each recording that the mirror is stuck, the
engine step's shape and a mirror-side witness; §7). One lemma per redex
root (`complete_store` … `complete_memop_vals`) carries the
classification; `cerberusRound_classify` sorts every well-sized `Frag`
configuration into `value_done` / `value_annot` / `step` (two-sided
given the mirror step) / `refused` (with its `ShippedRefusal`) /
`open_` (with its `OpenRound`). The fragment is DECLARED as exactly what
the mirror covers ([USER 2026-09-02], the fragment-closure ruling): the
plain-symbol binder's head is restricted to bare-value producers
(`BareHead`), and every evaluating constructor's operands lie in the
mirror evaluator's exact domain (`PePure`, the eight mirrored binops).
So the logic is SOUND (§4) and COMPLETE for the declared fragment up to
the residual: mirror steps iff the engine has a successful deterministic
round, and every stuck configuration is classified — a configuration
the mirror refuses is one the engine refuses too, in the engine's own
vocabulary, except at the residual's two shapes (an operand the engine
ACCEPTS where the mirror evaluator does not evaluate — a procedure-
named symbol, a binop at two floats, `OpEq` at two ctypes; a jump with
surplus arguments), where the engine's step is stated by shape and the
class is named exactly. What is established, in the auditor's words: "a
sound Iris program logic for the package's restricted relational
mirror, with a verified forward connection to successful Cerberus
engine rounds on proved-safe executions" — now with the backward
classification at every fragment refusal outside the residual.

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

THE ONE KNOWN ADMISSION IN THE PINNED SEMANTICS TREE. The pinned
cerberus-lean tree declares no `axiom`, but it contains one generated
admission: two `(sorry : String)` terms in the debug-log branch of
`auxAddToRfLoad` in the generated concurrency model (`Cmm_op.lean`;
Lean reports `declaration uses sorry` for it during the build). It is
outside every current export cone: the package sweep (Audit.lean)
establishes that `sorryAx` reaches no `CerberusHeapLang` constant.
Concurrency is out of scope for this package (`drive fmapEmpty false
…` in every production statement). The admission must be closed
upstream or separately bounded before any concurrency or whole-engine
claim is made on this semantics; it is reported to the cerberus-lean
team in `../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`.

THE ROOT-OF-TRUST LANE (total): the four closed shipped-driver
statements — `exhibitA_prod` (ProdExhibit.lean),
`fib_certified_production`, `counter_loop_certified_production`,
`list_reverse_certified_production` (ProdLoopExhibit.lean). Their
execution function is the shipped composite of §1, applied to the
authored program wrapped as a synthetic one-procedure file by
`prodFile` (ProdEntry.lean); their conclusions are pure readout
predicates on the delivered `driver_result`; they carry no termination
hypothesis (where the certified step count depends on an input, the
in-budget bound is an explicit hypothesis: `fib_certified_production`'s
`hfuel : 2 * n.toNat + 6 ≤ lemDefaultFuel`,
`counter_loop_certified_production`'s `hfuel : 6 * n.toNat + 8 ≤
lemDefaultFuel`). "Closed shipped-driver statement" means exactly these
four; the headline claim of this package rests on them. They are
reached through `wpt_driver_done`/`wpt_driver_done_alloc`
(ProdLoop.lean) and `prod_run_eqJ` (ProdEntry.lean), which is generic
collapse machinery, not a closed statement: its premise `hdd` is the
package-defined delivery fact `DriverDoneAt` (ProdLoop.lean) that the
total judgment supplies, its premise `hQe` is the package-defined label
tie `LabeledAt`, and it carries the in-budget bound `k + 2 ≤
lemDefaultFuel` on the certified step count. The four statements
discharge the delivery and label premises (and the bound, by
computation, where the step count is fixed) and are what remains.

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

The first two are the explicit open ACCEPTANCE items (the 2026-09-02
re-review's next action 1; mirror completeness landed 2026-09-02 and was
closed fail-closed on the declared fragment the same day, up to the
residual below): each stays open until the named theorem exists, and the
PROVISIONAL label is not removed before then.

- The residual of mirror completeness (§2, `OpenRound`,
  `docs/2026-09-02_fragment-closure-notes.md`): `eval_uncovered` — an
  operand in the covered grammar that the engine's evaluator ACCEPTS
  where the mirror evaluator does not evaluate (a symbol unbound in the
  environment but naming a `Proc` of the file, evaluated by the engine
  to the null function pointer; one of the eight mirrored binops at two
  floating-point operands; `OpEq` at two ctypes) — environment- and
  file-dependent, so not removable by a syntactic narrowing of `Frag`;
  the mover is a mirror evaluator complete relative to
  `eval_pexpr_aux2` on `PePure` (`M.file` threaded into `evalPexpr`, the
  float/ctype arms), which moves the arm into `Step`. `run_surplus` — a
  jump with more arguments than the registered label's parameters whose
  zipped arguments evaluate and whose surplus does not (the engine's
  fold truncates, the mirror's `Step.run` evaluates every argument) —
  label-map-dependent; the mover is a prefix-evaluating `Step.run`. Of
  the four gaps registered on 2026-09-02, (a) and (c)'s grammar were
  closed by narrowing `Frag` (`BareHead`, `PePure` everywhere), (b) and
  (d) by classification (`ShippedRefusal.error_next`, `panic_noproc`),
  and (c)'s engine rejections by the KILL bridge (EvalClass.lean).
- The shipped-driver generic adequacy theorem (§6). Today
  `MemTripleU`, the projection theorems and `wpt_engine_boundU` are
  about `driveU`, and only the four closed production statements reach
  `CerbND.runND (drive …) (initial_driver_state …).1`. Closes when a
  generic theorem takes an arbitrary proved public triple to a
  statement over that shipped composite — which needs the
  fuel-exhaustion request below (a transparent, distinguished
  fuel-exhaustion outcome in the engine's driver monad) to land, so
  that a statement quantifying over all fuels can classify the
  driver's outcomes. The PROVISIONAL lane is then restated with no
  other change.
- Footprint-relative freshness: `LaunchCoh` (Adequacy.lean)
  constrains tracked cells only (`id_lt`, `addr_lo`), so a `create`
  (`wps_create`/`wpt_create`) is fresh from the logical footprint, not
  from untracked allocations an arbitrary concrete state may carry
  below the cursor. The production cold-start state `prodMem₀`
  contains only the allocator-created errno allocation and no dead
  allocations (`prodMem₀_allocations`, `prodMem₀_deadAllocations`,
  ProdEntry.lean); `prodMem₀_launchCoh` proves `LaunchCoh` for the
  empty footprint and any fitting plan, and no more. "Globally well
  formed" is reserved for the future `MemWF` invariant (allocation-id
  discipline, live/dead consistency, range disjointness of all live
  allocations, cursor bounds) and its initialization proof, registered
  for the malloc/free extension.
- The deferred parametric semantics interfaces: the rules are proved
  directly against `Step` and the memory state (walkthrough §7).
