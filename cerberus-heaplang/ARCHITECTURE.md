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
own. Every exported execution theorem reaches the shipped engine — the
closed statements through that composite, the generic ones through the
driver's own per-thread loop `drive_nonmemory_steps_aux2_lemFuel` at
every fuel (§4, §6) — and every public logical rule has a kernel-checked
adequacy path through the package mirror to the engine. (The reusable rules and assertion laws are statements in Iris
over the mirror `Step` and the ghost resources, §3, §6; what makes them
statements about the engine is that adequacy path, not their own
text.) A disagreement between any definition here and the engine is a
defect here. The engine is trusted as a policy decision — the Lean port is differentially
validated against the OCaml Cerberus, not proved equivalent to it
(README, "What you are asked to take on faith").

## 2. The mirror, and its one-directional certification

Iris needs a fuel-free small-step relation; the engine's `step_ctx` is
fuelled and monadic. `Step M` (Step.lean) is the hand-written mirror —
a relation on configurations `Config := CoreExpr × EnvStack × Ctl ×
Mem` (Core expression, environment stack, the thread's LIVE CONTROL
`Ctl` — call stack `κ`, current procedure `proc`, execution location
`execLoc`, the three `thread_state` fields the engine's PCALL/RETURN
arms write; calls arc C1 made them live, C2 added the two rules that
write them: `Step.call` — stated at the WHOLE expression like the jump,
the captured context computed by the syntactic search `callRedex?`,
certified against get_ctx's decomposition — pushes `(ctl.proc, ctx)`,
`Step.ret` pops it, every other rule threads the control
(`Step.ctl_cases`) — and memory) covering the fragment `Frag`
(Soundness.lean) — and it is
the `primStep` of the iris-lean `Language` instance (Lang.lean). The
mirror has no authority; its certification is `engine_step_matchU`
(Round.lean), stated exactly as `theorem engine_step_matchU {M :
MachineCtx} … (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel) (hs : Step
M (e, ev0 :: evs, ctl, σ) (e', ρ', ctl', σ')) : CerberusRound M (e, ev0 ::
evs, ctl, σ) (e', ρ', ctl', σ')` — on `Frag`, at a cons-shaped
environment, at ANY control and ANY successor control (the call and
return rounds write it), with `esize e ≤ lemDefaultFuel`, and no
well-formedness premise (`SeqWF` and the empty-stack control `ctl.κ =
[]` are premises of `cerberusRound_classify` only, for its `value_done`
arm): every
mirror step is exactly ONE ITERATION OF THE SHIPPED DRIVER'S THREAD LOOP
— the relation `CerberusRound M` (Round.lean): at every driver state
embedding the context and the configuration (`MachineCtx.Embeds`), the
engine's step list is a singleton `s`, `s` is advanceable
(`can_advance`), and the shipped `advance_step` on it is one active
wakeup-free transition to the state embedding the mirror's successor.
The round is stated at the loop body (no fuel dependency; its
loop-level reading `CerberusRound.loop_step` holds at every fuel), in
the driver's own vocabulary only. The hand-written discharge
`dischargeStep`/`outcomesU` (Soundness.lean) is a proof device of this
module's classification: no EXPORT's statement mentions it — the lemmas
that do (`stepDischarge_run` over `dischargeStep`, `outcomesU_of_step`
over `outcomesU`) are proof devices, unpinned and internal, bounded by
the package sweep but not exported (the trust rule of 2026-09-02; the
2026-09-03 standards-audit response), and since the fuel-lane
restatement (2026-09-03) no adequacy lane consumes them at all. That
round is the mirror's only reference: no other relational semantics is
referenced or bridged, and none is needed for the root of trust, which
is the engine (§1). The round is the REFERENCE RELATION the
certification and the completeness below are stated over; it is
consumed by NO adequacy export — the adequacy chain does not go through
it: BOTH adequacy lanes consume the shipped round `loop_step_frag`
(DriverCollapse.lean — the live-control round that ties the mirror's
`ctl` to the driver thread's control fields and admits the call and
return rounds; its control-preserving core `loop_step_frag_same`, and
their generalizations `loop_step_frag'`/`loop_step_frag_same'`, which
ask for the current procedure's registration tie only at a jump),
proved independently of `CerberusRound` by its own per-redex case
analysis (Round.lean header, "WHAT CONSUMES WHAT"): the total lane
through `wpt_driver_aux`/`wpt_driver_cps` (ProdLoop.lean), the partial
lane through the fuel induction `drive_safe_aux` (Adequacy.lean).

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
(`BareHead` — a literal, `create`, `alloc`, the `PtrEq` memop and, since
calls arc C4, the procedure call: `lets x = f(args) in …`, whose RETURN
plugs a BARE value, `BareHead.call`), and every evaluating constructor's
operands lie in the mirror evaluator's exact domain (`PePure`, the eight
mirrored binops).
So the logic is SOUND (§4) and COMPLETE for the declared fragment up to
the residual: mirror steps iff the engine has a successful deterministic
round — with two disclosed exceptions to the iff: the REMOVE-ANNOT value
round (an annotated value's annotation is stripped by an engine round
the mirror treats as a value step, `value_annot`) and `error_next` (an
engine SUCCESS round into a configuration whose next round is ILLTYPED,
filed under refusals) — and every stuck configuration is classified: a
configuration the mirror refuses is one the engine refuses too, in the
engine's own vocabulary, except at the residual's two shapes, where the
engine's step is stated by shape only. The residual's operand arm is an
operand CONTAINING A LEAF the engine accepts where the mirror evaluator
does not evaluate (a procedure-named symbol, a binop at two floats,
`OpEq` at two ctypes); the classifier `evalClass` answers `.uncovered`
at the first such leaf and carries NO engine claim about the whole
operand, whose outcome is therefore NOT characterized — it may succeed,
kill on a later type error, or panic. Precisely: every operand the
classifier REJECTS is a proved engine KILL; operands the classifier
leaves UNCOVERED are not characterized (the residual is a SUPERSET of
the engine-accepted shapes). The other arm is a jump with surplus
arguments. What is established, in the auditor's words: "a
sound Iris program logic for the package's restricted relational
mirror, with a verified forward connection to successful Cerberus
engine rounds on proved-safe executions" — now with the backward
classification at every fragment refusal outside the residual.

## 3. The two judgments

The small axioms are proved once as atomic step specifications
(`AtomicStep`, Rules.lean: `store_atomic`, `load_atomic`,
`storeAt_atomic`, `loadAt_atomic`, `create_atomic`, `kill_atomic` —
the static dispose, kill/free arc K2 — and `alloc_atomic`/`free_atomic`
— dynamic allocation and free, K3), each against `Step` and the real
`storeM`/`loadM`/`allocateObject`/`allocateRegion`/`killM`, and lifted by
`wp_of_atomic` (raw WP), `wps_of_atomic` and `wpt_of_atomic`. `wps M p
Ls Θ Ψ e ρ` (Wps.lean) is the partial label-context judgment at the
current procedure `p` with the label specification `Ls` and the
PROCEDURE SPECIFICATION TABLE `Θ : ProcSpec GF` (calls arc C3), a
guarded fixpoint over iris-lean's WP with four clauses — value, jump
redex, CALL redex (the table's precondition now; a step later the
caller's continuation `apply_ctx ctx (pure ret)` at the caller's env, for
every `ret` meeting the postcondition), step (quantified over the call
stack and execution location); `wpt M p Ls Θ k Ψ e ρ` (Wpt.lean) is the
total judgment by well-founded recursion on a step budget with the
mandatory back-edge decrease (`1 + m ≤ k`) and the call clause's budget
split (`1 + m + k' ≤ k`: call round, callee incl. its return,
continuation). Frame across back edges and calls:
`wps_frame_labels`/`wpt_frame_labels`; loops: `blockSpecs_intro`/
`blockSpecsT_intro`; procedures: `procSpecs_intro`/`procSpecsT_intro`
(every declared body verified once, at every caller tail, assuming the
table — Hoare's rule for recursive procedures; no Löb in the
introduction); the call rule `wps_call`/`wps_call_root`,
`wpt_call`/`wpt_call_root`; collapses: `wps_sound_cps` (THE ONE LÖB, in
CPS over the ambient control — RefinedC's `stmt_wp_def` shape — whose
call case runs the callee under `procSpecs` and returns into the
caller's continuation, `wp_ret`/`wp_ret_annot`, the environment restored
by `SameTail`) with `wps_sound`/`wps_sound_empty` at the entry control,
and `wpt_sound_cps` (strong induction on the budget) with
`wpt_sound`/`wpt_sound_empty` into TWP (metatheorems no export
consumes). There is no raw-WP sequencing rule: at a populated label map
it is false (Rules.lean).

## 4. Adequacy

Both lanes are stated over the SHIPPED driver's own per-thread loop
`drive_nonmemory_steps_aux2_lemFuel` (Driver.lean:346; the shipped
`drive_nonmemory_steps_aux2` is its instance at `CerbFuel.driverFuel`,
`CerbND.drive_nonmemory_steps_aux2_wrapper_defeq`), from any driver state
holding the configuration at a live control, and both are proved by
iterating the shipped round `loop_step_frag`/`loop_step_frag'` (§2).

THE PARTIAL LANE (Adequacy.lean; the fuel-lane restatement, 2026-09-03):
`spike_step_adequacy` is iris-lean's `wp_strong_adequacy_gen` with the
ghost state constructed (`genHeap_init`, `spikeCells_alloc`;
`launchResources` under `LaunchCoh` for allocating programs), and
`engine_adequacy` (`_alloc`) turns it into the engine fact
`DriverSafeCtl M th₀ e ρ ctl σ ψ`: from any driver state whose singleton
thread holds `(e, ρ)` at the control `ctl` over `th₀`'s immutables, at
layout state `σ`, with empty extern, the context's file and the
registration ties (`LabeledProcs` for the callees, `CtlTied` for the
procedures already on the control), the loop with `fl` iterations
available — AT EVERY `fl` — either EXHAUSTS (its value is the kill
`CerbND.fuelExhaustedKill`, the cerberus-lean fuel arc's transparent
out-of-fuel arm, `CerbND.drive_nonmemory_steps_aux2_lemFuel_zero`) or
returns PROGRAM-DONE for a value satisfying the readout `ψ` at the final
memory, the final thread at the empty call stack; no other outcome (no
kill of any other reason, no ILLTYPED refusal, no off-protocol step).
Why the mirror suffices: `NotStuck` supplies a mirror step at every
reachable configuration and the shipped round `loop_step_frag'` makes it
the loop's unique next iteration (`drive_safe_aux`, an unpinned device: an
induction on the fuel, control-general under the invariant `ControlOk` —
the saved frames plug values into fragment terms — the env-depth
invariant `Step.env_depth`, and the premise `MachineCtx.FragProcs`, every
declared procedure body in the cone: the raw WP's NotStuck does not
exclude a call, so the partial lane follows the engine into the callee
and back through the driver's own PCALL and RETURN rounds); fuel 0 is
the exhaustion kill, fuel 1 at a delivered value is the exhaustion of the
drain iteration (`loop_step_done_exhaust`), fuel ≥ 2 there is
PROGRAM-DONE (`loop_step_done`). The shipped-round certification
`engine_step_matchU` (§2) is not consumed by either lane.

THE TOTAL LANE is the driver lane (ProdLoop.lean): the same loop,
delivery within `k + 2` iterations.

THE TOTAL DRIVER LANE THROUGH CALLS (ProdLoop.lean, calls arc C4):
`wpt_driver_cps` is the budget induction in CONTINUATION-PASSING form
over the ambient control — the driver-level twin of `wpt_sound_cps` —
concluding the pure delivery fact `DriverDoneCtl M₀ th₀ e ρ ctl σ ψ k` at
a LIVE control (the driver's per-thread loop, from any driver state
holding the configuration at `ctlThread th₀ e ρ ctl`, with the file tie
`dst.core_file = M₀.file` and the whole-file registration tie
`LabeledProcs M₀ dst.core_run_state0.labeled`, returns PROGRAM-DONE for a
value satisfying `ψ` within `k + 2` iterations), with the continuation
budget ADDED (`k + kc`): the call case applies the induction hypothesis to
the callee's body at the pushed control with continuation budget `k' +
kc`, whose continuation performs the RETURN round(s) — `Step.ret`, after
`Step.ret_annot` — into the caller's continuation `apply_ctx ctx (pure v)`
at the popped env (in the cone by the plug lemmas) and applies the
hypothesis to it at `k'`; the split `1 + m + k' ≤ k` pays for the call
round. Every round is `loop_step_frag` at the live control
(`driverDoneCtl_step`); the launcher is `wpt_driver_done_procs`
(allocation-aware, at a populated table, the entry control `⟨[], some p,
ℓ⟩` of a declared procedure `p`). The single-procedure lane
(`DriverDoneAt`, `wpt_driver_aux`, `wpt_driver_done(_alloc)`) is left as
it is — the seven earlier production statements' route, at a context
profile (`procCtx`, the default file) where the file tie is not
available; a restatement was weighed and declined (the C4 record, §9).

## 5. The projection

`project_triple_pure` (Adequacy.lean): any Iris triple whose
precondition is footprint ownership and whose framed post pure-entails
`ψ R w.val σ'` under the coupling invariant projects to the Iris-free
`MemTriple M ctl ρ e P ψ` — memory splits as P ⊎ R, and from any driver
state holding the configuration there the shipped loop at every fuel
exhausts or delivers (`DriverSafeCtl`), every delivered `(v, σ')`
satisfying `ψ R v σ'`. `project_triple_pure_alloc` is the allocating
twin (`allocBudget B` in the precondition, `MemTriple_alloc` under
`LaunchCoh … B`). The one
Iris-shaped hypothesis is discharged by `cellOwn_consequence`,
`pointsToCell_consequence`, `cellsOwn_consequence`,
`cells_consequence` and the `pure_`/`sep_`/`or_`/`exists_consequence`
combinators; the pure memory view they deliver is `CellCoh`/`Sat`.

## 6. The two trust claims, and the two lanes

(1) The closed-program exports have Iris-free statements; iris-lean
appears only inside kernel-checked proof terms and contributes no
axiom — every export's axiom set is exactly `propext`,
`Classical.choice`, `Quot.sound` (Audit.lean). (2) The reusable rules
are stated in Iris; `pointsToCell`, `cellOwn`, `allocBudget`, the WP and
BI connectives, and `CohG` (in the one hypothesis `hpost`) are
definitions to read, not axioms to accept.

ADMISSIONS IN THE PINNED SEMANTICS TREE: NONE (measured 2026-09-03).
The pinned cerberus-lean tree (`f95ef8d9c`, the fuel arc) declares no
`axiom`; until the 2026-09-03 re-pin it carried one generated admission
— two `(sorry : String)` terms in the debug-log branch of
`auxAddToRfLoad` in the generated concurrency model (`Cmm_op.lean`),
outside every export cone — which the fuel-arc head closes
(`cmm_op.lem`'s `sorry` target_rep replaced by
`CerbMem.stringFromMemValue`). Measured at this pin: `grep -rn '(sorry'`
over the primed `generated/*.lean` finds nothing, and the build log
contains no `declaration uses sorry` (README "The trust story";
`docs/2026-09-03_repin-fuel-notes.md`). The package sweep (Audit.lean)
stays in force: `sorryAx` reaches no `CerberusHeapLang` constant.
Concurrency is out of scope for this package (`drive fmapEmpty false
…` in every production statement).

THE ROOT-OF-TRUST LANE (total): the eight closed shipped-driver
statements — `exhibitA_prod` (ProdExhibit.lean),
`fib_certified_production`, `counter_loop_certified_production`,
`list_reverse_certified_production` (ProdLoopExhibit.lean),
`dispose_list_certified_production` (DisposeExhibit.lean),
`region_loop_certified_production` (RegionLoopExhibit.lean),
`malloc_list_certified_production` (MallocListExhibit.lean) and, since
calls arc C4, `fib_rec_certified_production` (FibRecExhibit.lean: RECURSIVE
fib — `main` calling `fib`, `fib` calling itself twice per activation,
on the synthetic TWO-PROCEDURE file `prodFileWith [(fib, [n], body)]
(fib(n₀))`; the first statement whose run makes the driver's PCALL and
RETURN rounds). Their
execution function is the shipped composite of §1, applied to the
authored program wrapped as a synthetic file — one procedure by
`prodFile`, `main` plus declared procedures by `prodFileWith`
(ProdEntry.lean; `prodFile e = prodFileWith [] e`, `rfl`); their
conclusions are pure readout
predicates on the delivered `driver_result`; they carry no termination
hypothesis (where the certified step count depends on an input, the
in-budget bound is an explicit hypothesis: `fib_certified_production`'s
`hfuel : 2 * n.toNat + 6 ≤ CerbFuel.driverFuel`,
`fib_rec_certified_production`'s `hfuel : fibRounds n.toNat + 4 ≤
CerbFuel.driverFuel` (the package's round-count function for the
recursive activation — `fibRounds 0 = fibRounds 1 = 3`, `fibRounds (n+2)
= fibRounds (n+1) + fibRounds n + 9`, closed form `fibRounds n + 9 = 12 ·
fib (n+1)`, derived — the second root-of-trust statement with a package
definition in its text, disclosed as `region_loop_certified_production`'s
budget premise is),
`counter_loop_certified_production`'s `hfuel : 6 * n.toNat + 8 ≤
CerbFuel.driverFuel`, `region_loop_certified_production`'s `hfuel : 7 *
n.toNat + 5 ≤ CerbFuel.driverFuel` together with its budget-fits-the-cold-
start premise `hB : n.toNat * regionCost al sz ≤ headroom
prodMem₀.lastAddress` — the package's cost function at the package's
cold-start cursor literal, the one root-of-trust statement with package
definitions beyond the program and `prodFile` in its text — a finding
of the K4 range audit, disclosed rather than hidden); and `malloc_list_certified_production`'s `hfuel : 25 *
n.toNat + 9 ≤ CerbFuel.driverFuel` with its budget premise in ENGINE
vocabulary, `hB : n.toNat * (15 + max al.toNat 1) ≤ 281474976710647`,
bridged to the package's `regionCost`/`headroom` inside the proof by
`ml_budget_bridge`). "Closed shipped-driver statement" means exactly these
eight (the DECISIONS register's "nine production statements" count the
generic pipeline theorem `prod_run_eqJ` as well — the same set); the
headline claim of this package rests on them. They are
reached through `wpt_driver_done`/`wpt_driver_done_alloc` and
`prod_run_eqJ` (the single-procedure lane) or, through calls,
`wpt_driver_done_procs` (ProdLoop.lean) and `prod_run_eqJ_procs`
(ProdEntry.lean), which are generic collapse machinery, not closed
statements: their delivery premise `hdd` is the package-defined fact
`DriverDoneAt`, resp. the live-control `DriverDoneCtl` (ProdLoop.lean),
that the total judgment supplies, their registration premise is the
package-defined tie `LabeledAt` (one procedure), resp. the whole-file
`LabeledProcs`, and they carry the in-budget bound `k + 2 ≤
CerbFuel.driverFuel` on the certified step count (`CerbFuel.driverFuel =
10^8` is the shipped driver's own budget since the cerberus-lean fuel
arc, pin `f95ef8d9c`; the bound is stated against the name the semantics
exports for exactly this purpose). The eight statements
discharge the delivery and registration premises (and the bound, by
computation, where the step count is fixed) and are what remains.

THE PARTIAL LANE (the fuel-lane restatement, 2026-09-03; record
`docs/2026-09-03_f1-notes.md`): `DriverSafeCtl`, `engine_adequacy`,
`engine_adequacy_alloc`, `MemTriple`, `MemTriple_alloc`, `SemTriple`,
`project_triple`, `project_triple_pure`, `project_triple_alloc`,
`project_triple_pure_alloc`, `semantic_triple_sound`, `semantic_frame`,
`SemTriple_iff_Mem`, `MemTriple_alloc_of_MemTriple`, and every exhibit
stated over them (`*_certified`, `*_engine`, `*_semantic`,
`*_adequacy`, `list_reverse_demo`, `call_smoke_engine`). Their referent
is the SHIPPED driver's per-thread loop `drive_nonmemory_steps_aux2_lemFuel
fl` (§4) at EVERY fuel `fl`, from any driver state holding the
configuration — the same loop, thread shape (`ctlThread`) and
registration ties (`LabeledProcs`, `CtlTied`; DriverCollapse.lean) as
the total lane's `DriverDoneCtl`, with exhaustion (`CerbND.fuelExhaustedKill`)
the admitted outcome beside delivery. The CLOSED partial form over the
pipeline is `prod_run_safe_procs` (ProdEntry.lean): at every `fuel`,
`CerbND.runND (CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith
procs e) args) (initial_driver_state sup (prodFileWith procs e) fs).1` is
EXACTLY ONE execution, either `nd_status.Killed dst' CerbND.fuelExhaustedKill`
or `nd_status.Active dres` with the postcondition; the shipped `drive` is
the instance at `fuel := CerbFuel.driverFuel` (`CerbND.drive_wrapper_defeq`,
`rfl`), and `fib_rec_certified` (FibRecExhibit.lean) is its client: every
`n ≥ 0`, no budget bound. MEASURED at the pin (the F1 record §3): the
`fuel` parameter of `drive_lemFuel` bounds the OUTER `driver2` rounds
only — `new_drive_core_threads` (Driver.lean:355) calls the per-thread
loop through its wrapper at the fixed `10^8` — so at every `fuel ≥ 1` the
closed statement is the one about the shipped `drive`, and the
"however long the run" content lives in the loop-level fact `DriverSafeCtl`
(∀ `fl`). Two honest qualifications: (i) the seeded exhibits (Exhibit A/B/C,
the counter loop, array sum, list reversal, tree rotation, the struct
update) start from a memory holding pre-seeded cells, which the cold start
never contains, so their engine statements are loop-level facts
(`DriverSafeCtl` at their profiles), not closed pipeline runs; (ii) the
straight-line exhibits keep the profile `spikeCtx`/`spikeCtl` (no current
procedure, the default file) — a thread state the shipped driver never
parks `main` in (it parks it at `current_proc_opt := some main_sym`,
Driver.lean:530), admitted by the loop-level fact because the round
lemma needs the current procedure only at a jump (`loop_step_frag'`'s
`hjmp`; `CtlTied.noproc`). The former package loop `driveU` around the
engine's `step_ctx`, and every statement over it, are deleted; the
former obstacle (the shipped driver's out-of-fuel arm was LemLib's
kernel-opaque `fuelExhaustedWith`) was lifted by the cerberus-lean fuel
arc (pin `f95ef8d9c`; the request:
`../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`).

## 7. Open items, and the acceptance goals

THE THREE ACCEPTANCE GOALS ([USER 2026-09-02], DECISIONS.md), with their
status at the close of the calls arc (2026-09-03):

- **Goal 1 — the shipped-driver generic adequacy theorem: CLOSED
  (2026-09-03, the fuel-lane restatement).** The generic theorems take
  an arbitrary proved public triple to a statement over the shipped
  driver: `project_triple_pure` (→ `MemTriple`, the shipped per-thread
  loop at every fuel from any driver state holding the configuration) and
  `prod_run_safe_procs` (→ the shipped composite `runND (drive_lemFuel
  fuel …) (initial_driver_state …).1` at every fuel, `drive` its instance
  at `CerbFuel.driverFuel`), with exhaustion the classified outcome
  `CerbND.fuelExhaustedKill`; no export carries an interim label; the
  package loop `driveU` is deleted. The semantics-side prerequisite
  landed in the cerberus-lean fuel arc (pin `f95ef8d9c`, re-pinned
  2026-09-03; `docs/2026-09-03_repin-fuel-notes.md`, scout
  `../docs/2026-09-03_repin-scout.md`); the ruled sequence (re-pin →
  calls arc C1–C4 → fuel-lane restatement) is complete. What the closure
  does NOT include, stated in §6: the seeded exhibits have no cold-start
  form (their statements are the loop-level facts), and `drive_lemFuel`'s
  fuel bounds only the outer `driver2` rounds (measured). Record:
  `docs/2026-09-03_f1-notes.md`.
- **Goal 2 — mirror completeness: CLOSED fail-closed on the declared
  fragment (2026-09-02), with two characterized residuals.** `OpenRound`
  (§2, `docs/2026-09-02_fragment-closure-notes.md`): `eval_uncovered` —
  an operand in the covered grammar CONTAINING A LEAF the engine's
  evaluator accepts where the mirror evaluator does not evaluate (a
  symbol unbound in the environment but naming a `Proc` of the file,
  evaluated by the engine to the null function pointer; one of the eight
  mirrored binops at two floating-point operands; `OpEq` at two ctypes).
  The classifier `evalClass` answers `.uncovered` at the FIRST such leaf
  and carries no engine claim about the whole operand, so the arm's
  whole-operand outcome is NOT characterized: it contains operands the
  engine SUCCEEDS on, operands it KILLS (`f + 1` with `f` a `Proc`-named
  unbound symbol is `PePure`, classified `.uncovered`, killed as
  `Illformed_program … ill-typed PEop` — 2026-09-03 audit, by
  execution) and operands it PANICS on (a float guard under `Eif`).
  Every operand the classifier REJECTS is a proved engine KILL;
  operands it leaves UNCOVERED are not characterized — the residual is
  a SUPERSET of the engine-accepted shapes. Environment- and
  file-dependent, so not removable by a syntactic narrowing of `Frag`;
  the mover for the characterization is `evalClass` computing the
  engine's value at the three leaf shapes (reserving `.uncovered` for
  the leaf itself, the downstream rejections falling under the KILL
  bridge); the mover that empties the arm is a mirror evaluator
  complete relative to `eval_pexpr_aux2` on `PePure` (`M.file` threaded
  into `evalPexpr`, the float/ctype arms), which moves it into `Step`.
  `run_surplus` — a jump with more arguments than the registered label's
  parameters whose zipped arguments evaluate and whose surplus does not
  (the engine's fold truncates, the mirror's `Step.run` evaluates every
  argument) — label-map-dependent; the mover is a prefix-evaluating
  `Step.run`. Of the four gaps registered on 2026-09-02, (a) and (c)'s
  grammar were closed by narrowing `Frag` (`BareHead`, `PePure`
  everywhere), (b) and (d) by classification
  (`ShippedRefusal.error_next`, `panic_noproc`), and (c)'s classifier
  rejections by the KILL bridge (EvalClass.lean). A third registered
  premise stays carried, not proved: `hbsz` inside `Frag.case_value`
  (README "Registered divergences and limitations").
- **Goal 3 — the global memory well-formedness invariant: CLOSED (K0–K3,
  2026-09-03).** `MemWF σ` (Heap.lean, section "The global memory
  well-formedness invariant": allocation-id discipline, live/dead
  consistency, pairwise range disjointness of ALL live allocations,
  cursor bounds incl. `la_pos : 0 < lastAddress` — a field added at K3
  on orchestrator direction, recorded [AGENT] in DECISIONS (a stronger
  launch premise: every allocating export's claim about arbitrary states
  is correspondingly narrower, by an engine invariant), the
  dynamic-address facts; ten components, each an engine fact with a
  `CerbMem.lean` cite) is a field of the state interpretation `CohG` (under cursor
  presence) and of the launch premise `LaunchCoh`; `prodMem₀_memWF` is
  the cold-start instance; `create_fresh_global` is "fresh means fresh
  in the concrete allocation model"; and EVERY memory operation of the
  fragment has its preservation theorem — `MemWF.loadM`, `MemWF.storeM`
  (either locking mode), `MemWF.allocateObject` (any initializer),
  `MemWF.killM` (both arms, K2), `MemWF.allocateRegion` (K3). Every
  stated obligation is a theorem; "fresh" and "dynamic" are exactly what
  the engine has: fresh = disjoint from every live allocation of the
  state, dynamic = the base was pushed by `allocateRegion` (coupled
  one-way to `dynamicAddrs`, which `killM` never cleans — the K0 range
  audit's finding). The former footprint-relative launch facts were retired as
  fields (K1 re-adds `cur_meta_lo`: dead metadata cells have no record
  for `MemWF.cursor_lo` to read).

THE OTHER OPEN ITEMS:

- **Loads and stores through a REGION pointer — CLOSED at K5 (2026-09-03;
  K4's finding).** `regionLoadAt_atomic`/`regionStoreAt_atomic`
  (Rules.lean) over the TYPED REGION VIEW `typedRegionView` (Heap.lean:
  `pointsToView` with `regionCell a n true` for the object cell and the
  region's size for the layout size; laws `typedRegionView_regionView`,
  `typedRegionView_split`/`_join`, `regionOwn_carve`/`_uncarve`),
  proved once through the seams `loadM_live`/`storeM_live` at the region
  cell — no coupling change, as predicted; faces `wps_load_region_at`/
  `wps_store_region_at`, the whole-region `wps_load_regionOwn_at`/
  `wps_store_regionOwn_at`, total twins; manifest rows `Frag.load`/
  `Frag.store` → the region rules (23 constructors, 25 rule rows, 0 red,
  16 exhibit modules). What the engine checks at an untyped allocation
  is type-blind — the dead list, the record, bounds against the record's
  size, writability, and `isAtomicMemberAccess = false` at `alloc.ty =
  none` (CerbMem.lean:1619); no effective-type or alignment check — so
  the rules hold at any type at any in-bounds offset. THE MALLOC'D
  LINKED LIST (MallocListExhibit.lean) is the chartered exhibit:
  `ml_wps`/`ml_wpt` (one label, two phases: `n` region nodes allocated
  from the split budget, written and linked through the region rules,
  then walked and freed) and `malloc_list_certified_production` (the seventh
  root-of-trust export). All four state `n.toNat` DISTINCT dead ids
  (`ids.Nodup`, K5.1 — the K5 range audit's finding: `deadRegion` is persistent,
  so without it the posts said only that some region is dead); the
  distinctness laws are the public `regionOwn_ne`/
  `regionOwn_deadRegion_ne` (`metaOwn_ne` at the region bundles),
  applied at each `alloc` and carried by the invariant `(ids ++
  done).Nodup` through each `free`. Records: `docs/2026-09-03_k5-notes.md`,
  `docs/2026-09-03_k5.1-notes.md`.
- **Two `save` labels in one program — the LAW landed at C4, the exhibit
  is still absent (found by the K5 range audit).** Every loop exhibit is
  single-label; the malloc'd list merges its two C loops into one Core
  label with two phases. The two-entry lookup law the two-label form
  needs is now the β-generic `symAdd_lookup`/`symAdd_lookup_two` (EnvLaws,
  calls arc C4 — the C3 smoke's local law moved and generalized;
  `envAdd_lookup` is its `value` instance; measured: the lookup reads the
  bucket head, so the add's `BEq` instance is irrelevant and the add
  comparator enters only as the captured tree comparator, `symOrd` —
  which the engine's `ordCompare`-built label maps have by definitional
  unfolding). A rule gap it never was (`wps_run`/`wps_save` are
  label-generic); what remains is a two-label exhibit.
- **The kill/free arc K0–K5.1 — CLOSED (2026-09-03).** Record:
  `docs/2026-09-03_kill-free-arc-record.md` (one paragraph per slice,
  commits, audit verdicts, the corrections to the design note, what
  remains). In one line each: K0 `MemWF` (goal 3); K1 the metadata cell
  `⟨base, optional type, size, alive, readonly, dynamic⟩` coupled by
  `MetaCoh`, the bundles `regionOwn`/`regionView`/`readonlyCell`/
  `deadObj`/`deadRegion`; K2 THE DISPOSE RULE `kill_atomic` →
  `wps_kill`/`wpt_kill` (+ `_emp`, `_eval`) over `pointsToCell … (.own
  1)` with post `deadObj`, the mirror `Step.kill`/`kill_eval`,
  `complete_kill`/`complete_kill_op`; K2.5 the ∗-splittable budget
  `allocBudget` (`allocBudget_split`), the create rules restated over
  it; K3 `alloc_atomic` → `wps_alloc`/`wpt_alloc` (+ `_eval`) over
  `allocBudget (regionCost al n)` delivering `regionOwn`, `free_atomic`
  → `wps_free`/`wpt_free` (+ `_emp`) over `regionOwn (.own 1)` with post
  `deadRegion`, the mirror `Step.alloc`/`alloc_eval`, `Frag.kill`'s kind
  restriction lifted, `complete_alloc`/`complete_alloc_op`, the decision
  raised by the K2 range audit (no rule for the static kill of a region
  and its three companions); K4 the exhibits — `dl_wps`/`dl_wpt`/
  `dispose_list_certified_production` (and, until the fuel-lane
  restatement of 2026-09-03, a `_total` twin over the package loop)
  (DisposeExhibit.lean) and `rl_wps`/`rl_wpt`/
  `region_loop_certified_production` (likewise)
  (RegionLoopExhibit.lean), every advertised kill/free/alloc law with an
  exhibit consumer; K5 THE REGION ACCESS RULES and the malloc'd linked
  list (above; the manifest now 23 constructors, 25 rule rows, 0 red, 16
  exhibit modules), plus the public `deadObj_readout`/`deadRegion_readout`
  (asked for by the K4 range audit). Follow-up still named in the record: the cursor
  ghost heap as a proof device (no client owns the cursor since K2.5 —
  fold it into the budget interpretation).
- **The calls arc C1–C4 — CLOSED (2026-09-03).** Records
  `docs/2026-09-03_c{1,2,3,4}-notes.md`, range audits
  `docs/2026-09-03_c{1,2}-audit.md`, `docs/2026-09-03_audit-c3-range.md`;
  design note `docs/2026-09-02_calls-design-spike.md`. In one line each:
  C1 the live control `Ctl` (call stack, current procedure, execution
  location) as the fourth configuration component; C2 the mirror's
  `Step.call`/`Step.ret`/`Step.ret_annot`, their certification at a free
  successor control and completeness rows, the live-control production
  round `loop_step_frag`, `FragProcs` on the partial adequacy exports; C3 the
  procedure-indexed judgments with the specification table `Θ`, the call
  clause, `wps_call(_root)`/`wpt_call(_root)`, `procSpecs(T)_intro`
  (Hoare's rule for recursive procedures), the CPS collapses
  `wps_sound_cps` (the one Löb)/`wpt_sound_cps`; C4 THE PRODUCTION LANE
  THROUGH CALLS — `BareHead.call` (a call's result bound at the
  plain-symbol binder), the CPS driver induction `wpt_driver_cps` over
  `DriverDoneCtl` with the whole-file tie `LabeledProcs`, the N-procedure
  entry `prodFileWith`/`prod_run_eqJ_procs`, the `exec_loc`/`current_loc`
  tie (`prodCtl`/`prodCtx`: the parked thread's control and
  `current_loc`, Driver.lean:530, what PCALL's `push_exec_loc` reads,
  Core_reduction.lean:484 col 18133 — the C2 record §3(f)/the C1 audit's
  M-1, closed), and RECURSIVE FIB as the eighth root-of-trust statement.
  Still open from the arc, by design: mutual recursion (the rule admits
  it — `procSpecs` assumes the table for every procedure — no exhibit);
  function pointers (`Eccall`, another scheduler path); a two-label
  exhibit (above). (The total `driveU` lane at the empty table, left at
  C4, was deleted with the loop in the fuel-lane restatement,
  2026-09-03.)
- The deferred parametric semantics interfaces: the rules are proved
  directly against `Step` and the memory state (walkthrough §7).
