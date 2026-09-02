/-
CerberusHeapLang.Round — THE SHIPPED ENGINE ROUND, NAMED.

`CerberusRound M c c'` is ONE ITERATION OF THE SHIPPED DRIVER'S THREAD
LOOP at a machine context, stated in the driver's own vocabulary and
nothing else: at every driver state that embeds the context and the
live configuration `c` (`MachineCtx.Embeds` — the single thread
`M.tid` holding `M.thread c.1 c.2.1`, the memory `c.2.2`, the file,
extern map and run state of `M`), the engine's step list read by the
loop body (`step_ctx`, Core_reduction.lean:484 — exactly the `nd_read`
of `drive_nonmemory_steps_aux2`, Driver.lean:346) is a singleton `s`,
`s` is advanceable (`can_advance`, Driver.lean:310 — the loop's
`find_can_advance` selects it), and the shipped `advance_step`
(Driver.lean:336) on it is ONE ACTIVE, WAKEUP-FREE transition to the
driver state that embeds `c'` (the run state's aid supply possibly
ticked — `labeled` untouched — the trace extended, the step counter
moved). `CerberusRound.loop_step` is the loop-level reading of the same
fact: `runOne (drive_nonmemory_steps_aux2_lemFuel (fl+1) …) dst =
runOne (drive_nonmemory_steps_aux2_lemFuel fl …) dst'` — the shape
`loop_step_frag` (DriverCollapse.lean) ships at the production profile.

NO FUEL DEPENDENCY. The round is stated at the loop BODY: the step
list, `find_can_advance` and `advance_step` are not fuelled (`nd_bind`
spends one layer of its own fresh budget per bind —
`runOne_bind_active`, DriverCollapse.lean — never accumulating). The
loop-level corollary holds for EVERY `fl`: the continuation at `fl` is
the same shipped function on both sides, and no fuel-zero arm is ever
evaluated by the statement.

THE REFERENT DISCIPLINE ([USER 2026-09-02], CLAUDE.md "The referent
of every export is the genuine semantics"). Before this slice the round
was `outcomesU … = [.next …]`, i.e. the graph of the hand-written
`dischargeStep` (Soundness.lean) — a package definition in an export's
referent. Now every constant in the statement of `CerberusRound`, of
the classification and of the refusal classes is either the engine's
(`step_ctx`, `can_advance`, `advance_step`, `perform_memop_request2`,
`update_thread_state`, `failwithI`, the `ndM`/`nd_action` types) or
context/embedding plumbing (`MachineCtx`, `MachineCtx.thread`,
`MachineCtx.Embeds`, `Config`). The one package name that is neither
is `runOne` (DriverCollapse.lean): `match m with | ND f => f s`, the
`ND` constructor's eliminator — the very operation `nd_bind` performs
on its left argument (Nondeterminism.lean:188). It carries no driver,
discharge or scheduler content; it is to `ndM` what `Prod.fst` is to
pairs. `dischargeStep`/`outcomesU`/`stepOutcomes` and the `outcomesU`
step-match (`outcomesU_of_step`, Soundness.lean) remain as PROOF
DEVICES — they are how the `driveU` lane's proofs go — and appear in
no export's statement here.

WHAT IS PROVED — the classification (`cerberusRound_classify`): for
every well-sized `Frag` configuration at a sequentially well-formed
context with a cons-shaped environment stack, EXACTLY ONE of

- `value_done`   — a bare value; the engine's step list is PROGRAM-DONE
                   (`[Step_done2 v]`, not advanceable: the loop records
                   it — `loop_step_done` — and `driver2` routes it to
                   `prepare_exit` — `driver2_done`, DriverCollapse.lean);
- `value_annot`  — an annotated value; the engine's round is the
                   REMOVE-ANNOT tau (a `CerberusRound` to the bare
                   value, env and memory verbatim) — NOT a mirror step,
                   by the mirror's value protocol (`toVal`);
- `step`         — the mirror steps, and then for EVERY c':
                   `Step M c c' ↔ CerberusRound M c c'` (two-sided GIVEN
                   the mirror step: the shipped round is exactly the
                   mirror's step, and conversely; mirror determinism
                   falls out);
- `refused`      — the mirror is STUCK at a non-value configuration.

The refusal vocabulary (`ShippedRefusal`) is stated here in the same
discipline: ILLTYPED (`[Step_error2 msg]`), KILL (the shipped
`advance_step` returns `NDkilled r` for an engine `kill_reason`), FORK
(the shipped exhaustive runner `CerbND.runND` returns ≥ 2 outcomes —
determinism is NOT baked in), PANIC (the round's monad is the engine's
own `failwithI msg` — LemLib's rendering of OCaml `failwith`, opaque
by design). `cerberusRound_refused_store`/`_load`/`_create`/`_case`
are the four instances proved in this module (memory kills and the two
ILLTYPED reports); the per-constructor completeness lemmas that make
the `refused` arm carry its engine fact are the next slice's content
(DECISIONS.md, "MIRROR COMPLETENESS — GO").

THE MIRROR'S ONLY REFERENCE is this round: no other relational
semantics is referenced or bridged, and none is needed for the root of
trust, which is the engine (`step_ctx` and the shipped driver).
-/
import CerberusHeapLang.DriverCollapse
import CerberusHeapLang.EnvLaws

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-- A Core configuration: expression, live environment stack, memory. -/
abbrev Config : Type := CoreExpr × EnvStack × Mem

/-- The driver states that EMBED a machine context and a live
    configuration: the single thread `M.tid` (parent `M.parent`) holds
    `M.thread c.1 c.2.1`, the memory is `c.2.2`, and the file, extern
    map and run state are the context's. Every other driver-state field
    (trace, step counter, concurrency and file-system state, …) is
    free: the fragment's rounds read none of them. -/
structure MachineCtx.Embeds (M : MachineCtx) (dst : driver_state) (c : Config) : Prop where
  thread : dst.core_state0.thread_states = [(M.tid, (M.parent, M.thread c.1 c.2.1))]
  layout : dst.layout_state = c.2.2
  file : dst.core_file = M.file
  extern : dst.core_extern = M.extern
  runState : dst.core_run_state0 = M.runState

/-- Every context and configuration is embedded by some driver state. -/
theorem MachineCtx.embeds_exists (M : MachineCtx) (c : Config) : ∃ dst, M.Embeds dst c :=
  ⟨{ (default : driver_state) with
      core_state0 := { (default : core_state) with
        thread_states := [(M.tid, (M.parent, M.thread c.1 c.2.1))] },
      layout_state := c.2.2, core_file := M.file, core_extern := M.extern,
      core_run_state0 := M.runState },
   ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- THE SHIPPED ROUND (module header): at every embedding driver state,
    the engine's step list is a singleton `s`, `s` is advanceable, and
    the shipped `advance_step` on it is one active wakeup-free
    transition to the state embedding `c'` — with the run state
    replaced by some `rs'` whose `labeled` fiber is untouched (the
    action rounds tick `aid_supply`, nothing else), the trace and the
    step counter arbitrary. -/
def CerberusRound (M : MachineCtx) (c c' : Config) : Prop :=
  ∀ dst : driver_state, M.Embeds dst c →
    ∃ s : core_step2,
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread c.1 c.2.1) = [s] ∧
      can_advance s = true ∧
      ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
        rs'.labeled = dst.core_run_state0.labeled ∧
        runOne (advance_step M.tagDefs M.tid s) dst =
          (NDactive NOWAKEUP,
           { dst with
              core_state0 := update_thread_state M.tid (M.thread c'.1 c'.2.1) dst.core_state0,
              layout_state := c'.2.2,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr })

/-- THE REFUSAL VOCABULARY, in the shipped driver's own terms (module
    header). Each arm is a fact about every embedding driver state;
    the payload (`msg`, `r`) is fixed by the configuration, not by the
    embedding. -/
inductive ShippedRefusal (M : MachineCtx) (c : Config) : Prop where
  /-- ILLTYPED: the engine's step list is the singleton `Step_error2
      msg` (one_step0's `ILLTYPED`/step_action's `ACTION_ILLTYPED`,
      Core_reduction.lean:353/424). The shipped driver's response to
      this step is the panic `failwithI ("can_advance: Step_error2 ==>
      " ++ msg)` (Driver.lean:310) — recorded, not modelled. -/
  | error (msg : String) :
      (∀ dst, M.Embeds dst c →
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) = [Step_error2 msg]) →
      ShippedRefusal M c
  /-- KILL: the step is advanceable and the shipped `advance_step`
      returns `NDkilled r` — `r` in the engine's own `kill_reason`
      vocabulary (`Undef0 loc ubs` for undefined behaviour, `Error0`,
      `Other err` for the driver's non-UB kills; memory kills arrive
      through `liftMem`'s `DErr_memory`, Driver.lean:218). -/
  | killed (r : kill_reason driver_error) :
      (∀ dst, M.Embeds dst c → ∃ (s : core_step2) (dst' : driver_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) = [s] ∧
        can_advance s = true ∧
        runOne (advance_step M.tagDefs M.tid s) dst = (NDkilled r, dst')) →
      ShippedRefusal M c
  /-- FORK: the step is advanceable and the shipped exhaustive runner
      delivers at least two outcomes for the advance (a nondeterministic
      node — `msum`, Nondeterminism.lean:245 — inside the memory
      operation). Determinism is not baked in: a later mirror may cover
      this class with a nondeterministic step. -/
  | fork :
      (∀ dst, M.Embeds dst c → ∃ s : core_step2,
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) = [s] ∧
        can_advance s = true ∧
        2 ≤ (CerbND.runND (advance_step M.tagDefs M.tid s) dst).length) →
      ShippedRefusal M c
  /-- PANIC (with-runstate): the step is `Step_with_runstate2 rsk m` and
      the engine's monad at the driver's run state IS the panic
      `failwithI msg` (LemLib's opaque rendering of OCaml `failwith`:
      the interpreter aborts; neither a kill nor a value). -/
  | panic (msg : String) :
      (∀ dst, M.Embeds dst c → ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) = [Step_with_runstate2 rsk m] ∧
        m dst.core_run_state0 = (failwithI msg : core_runM thread_state) dst.core_run_state0) →
      ShippedRefusal M c
  /-- PANIC (memop): the step is a memop request and the shipped
      `perform_memop_request2` (Driver.lean:288) on it is a bind whose
      head is the panic `failwithI msg` (its `INVALID memop request`
      arm). -/
  | panic_memop (msg : String) :
      (∀ dst, M.Embeds dst c →
        ∃ (loc : CerbLocation.Loc) (mop : memop) (cvals : List value) (uw : Bool)
          (k : value → thread_state)
          (g : thread_state → ndM Unit step_kind driver_error
            (mem_constraint CerbMem.IntegerValue) driver_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) = [Step_memop_request2 loc mop cvals M.tid uw k] ∧
        perform_memop_request2 M.tagDefs loc mop cvals M.tid k =
          nd_bind (failwithI msg) g) →
      ShippedRefusal M c

/-! ## Driver plumbing at a general thread id (the `0` instances live
in DriverCollapse.lean) -/

/-- The driver's thread-id equality test (the `instBEqOfEq0 → Eq0 →
    SetType-of-Ord → defaultCompare` chain, `lemNatBeq_iff`,
    EnvLaws.lean) is reflexive. -/
theorem lemNatBeq_self (n : Nat) :
    (@BEq.beq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1) n n) = true :=
  (lemNatBeq_iff n n).mpr rfl

/-- `lookupBy` (LemLib List.lean:256) at the singleton thread
    association list. -/
theorem lookupBy_single {β : Type} (k : Nat) (v : β) :
    lookupBy (fun (x y : Nat) => x == y) k [(k, v)] = some v := by
  simp only [lookupBy, find, lemNatBeq_self, if_true, Option.map]

/-- `update_thread_state` (Core_run.lean:99, via assoc_adjust
    Utils.lean:186) at the singleton thread list, any thread id. -/
theorem update_thread_state_single' (tid : Nat) (parent : Option Nat)
    (th th' : thread_state) (cs : core_state)
    (hth : cs.thread_states = [(tid, (parent, th))]) :
    update_thread_state tid th' cs =
      { cs with thread_states := [(tid, (parent, th'))] } := by
  unfold update_thread_state
  rw [hth]
  simp only [assoc_adjust, lemNatBeq_self, if_true]

/-! ## The shipped loop body, decomposed (Driver.lean:346-351):
{`nd_read` of the step list → `find_can_advance` → `advance_step`} -/

/-- ONE LOOP ITERATION from its three parts: a singleton advanceable
    step list whose shipped advance is active and wakeup-free continues
    the loop on the same thread list at the successor state. -/
theorem loop_step_of_advance {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {tid : Nat} {parent : Option Nat} {th : thread_state} {s : core_step2}
    {dst dst' : driver_state} (fl : Nat) (acc : Fmap thread_id (List core_step2))
    (hth : dst.core_state0.thread_states = [(tid, (parent, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern tid
      (parent, th) = [s])
    (hca : can_advance s = true)
    (hadv : runOne (advance_step tds tid s) dst = (NDactive NOWAKEUP, dst')) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [tid]) dst =
      runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [tid]) dst' := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active (z := [s]) (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) tid
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern tid th_info) = _
    rw [hth, lookupBy_single]
    exact hsteps
  · dsimp only [find_can_advance]
    rw [hca, if_pos rfl]
    refine (runOne_bind_active (z := NOWAKEUP) (s' := dst') hadv).trans ?_
    rfl

/-- `advance_step`'s tau arm (Driver.lean:336): thread updated,
    `dr_step_counter` ticked, no wakeup. -/
theorem advance_tau (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (tid : Nat)
    (s : String) (th' : thread_state) (dst : driver_state) :
    runOne (advance_step tds tid (Step_tau2 s TSK_Misc th')) dst =
      (NDactive NOWAKEUP,
       { { dst with dr_step_counter := dst.dr_step_counter + 1 }
           with core_state0 := update_thread_state tid th' dst.core_state0 }) := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
  rfl

/-- `advance_step`'s with-runstate arm, EVAL kind: `liftCore_run`
    writes the monad's run state back (verbatim here, `hm`), the thread
    is updated, the counter ticked. -/
theorem advance_withrs_eval (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (tid : Nat) (s : String) (m : core_runM thread_state)
    {th' : thread_state} {dst : driver_state}
    (hm : m dst.core_run_state0 = Result (Defined th', dst.core_run_state0)) :
    runOne (advance_step tds tid (Step_with_runstate2 (RSK_eval s) m)) dst =
      (NDactive NOWAKEUP,
       { { dst with dr_step_counter := dst.dr_step_counter + 1 }
           with core_state0 := update_thread_state tid th' dst.core_state0 }) := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  refine (runOne_bind_active (z := th') (s' := dst)
    (runOne_liftCore_run_of_eq hm)).trans ?_
  refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
  rfl

/-- `advance_step`'s with-runstate arm, TAU kind (`TSK_Misc`). -/
theorem advance_withrs_tau (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (tid : Nat) (s : String) (m : core_runM thread_state)
    {th' : thread_state} {dst : driver_state}
    (hm : m dst.core_run_state0 = Result (Defined th', dst.core_run_state0)) :
    runOne (advance_step tds tid (Step_with_runstate2 (RSK_tau s TSK_Misc) m)) dst =
      (NDactive NOWAKEUP,
       { { dst with dr_step_counter := dst.dr_step_counter + 1 }
           with core_state0 := update_thread_state tid th' dst.core_state0 }) := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  refine (runOne_bind_active (z := th') (s' := dst)
    (runOne_liftCore_run_of_eq hm)).trans ?_
  refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
  rfl

/-- `advance_step`'s action arm (sequential: the request is drawn from
    the request monad, the action id from `fresh_action_id'`, and
    `action_request_sequential2` discharges it — Driver.lean:273-285);
    the discharge outcome is the hypothesis. -/
theorem advance_action {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {tid : Nat} {s : String} {loc : CerbLocation.Loc}
    {req : action_request2 thread_state} {dst dst' : driver_state}
    (hars : runOne (action_request_sequential2 tds loc tid
        dst.core_run_state0.aid_supply req)
        { dst with core_run_state0 :=
            { dst.core_run_state0 with aid_supply :=
                dst.core_run_state0.aid_supply + 1 } } = (NDactive (), dst')) :
    runOne (advance_step tds tid (Step_action_request2 s loc tid false
        (stExceptUndef_return req))) dst = (NDactive NOWAKEUP, dst') := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst') ?_).trans (by rfl)
  refine (runOne_bind_active (z := req) (s' := dst)
    (runOne_liftCore_run_return req dst)).trans ?_
  unfold perform_action_request2
  dsimp only
  refine (runOne_bind_active
    (z := dst.core_run_state0.aid_supply)
    (s' := { dst with core_run_state0 :=
        { dst.core_run_state0 with aid_supply :=
            dst.core_run_state0.aid_supply + 1 } })
    (runOne_liftCore_run_aid dst)).trans ?_
  exact hars

/-- The action arm, KILLED discharge: the kill propagates through the
    remaining bind (`runOne_bind_killed`). -/
theorem advance_action_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {tid : Nat} {s : String} {loc : CerbLocation.Loc}
    {req : action_request2 thread_state} {dst dst' : driver_state}
    {r : kill_reason driver_error}
    (hars : runOne (action_request_sequential2 tds loc tid
        dst.core_run_state0.aid_supply req)
        { dst with core_run_state0 :=
            { dst.core_run_state0 with aid_supply :=
                dst.core_run_state0.aid_supply + 1 } } = (NDkilled r, dst')) :
    runOne (advance_step tds tid (Step_action_request2 s loc tid false
        (stExceptUndef_return req))) dst = (NDkilled r, dst') := by
  unfold advance_step
  dsimp only
  refine runOne_bind_killed (r := r) (s' := dst') ?_
  refine (runOne_bind_active (z := req) (s' := dst)
    (runOne_liftCore_run_return req dst)).trans ?_
  unfold perform_action_request2
  dsimp only
  refine (runOne_bind_active
    (z := dst.core_run_state0.aid_supply)
    (s' := { dst with core_run_state0 :=
        { dst.core_run_state0 with aid_supply :=
            dst.core_run_state0.aid_supply + 1 } })
    (runOne_liftCore_run_aid dst)).trans ?_
  exact hars

/-- `advance_step`'s memop arm (sequential: `perform_memop_request2`,
    Driver.lean:288; no aid draw, no counter tick). -/
theorem advance_memop {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {tid : Nat} {loc : CerbLocation.Loc} {mop : memop} {cvals : List value}
    {k : value → thread_state} {dst dst' : driver_state}
    (hars : runOne (perform_memop_request2 tds loc mop cvals tid k) dst =
      (NDactive (), dst')) :
    runOne (advance_step tds tid (Step_memop_request2 loc mop cvals tid false k)) dst =
      (NDactive NOWAKEUP, dst') := by
  unfold advance_step
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst') ?_).trans (by rfl)
  rw [if_neg (fun h => Bool.noConfusion h)]
  exact hars

/-! ## The memory operations are ONE-LAYER: active or killed
(the concrete model's `storeM`/`loadM`/`allocateObject` never produce
a nondeterministic node — CerbMem.lean:1504/1621/1667; `eqPtrval`'s
`msum` fork is the next slice's FORK instance). -/

/-- `storeM`'s one-layer result is active or killed. -/
theorem storeM_layer (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ty : ctype)
    (lk : Bool) (pv : CerbMem.PointerValue) (mv : CerbMem.MemValue) (σ : Mem) :
    (∃ fp σ', runOne (CerbMem.storeM tds loc ty lk pv mv) σ = (NDactive fp, σ')) ∨
    (∃ r σ', runOne (CerbMem.storeM tds loc ty lk pv mv) σ = (NDkilled r, σ')) := by
  unfold CerbMem.storeM runOne
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;>
    repeat' (first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩
      | split)

/-- `loadM`'s one-layer result is active or killed. -/
theorem loadM_layer (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ty : ctype)
    (pv : CerbMem.PointerValue) (σ : Mem) :
    (∃ p σ', runOne (CerbMem.loadM tds loc ty pv) σ = (NDactive p, σ')) ∨
    (∃ r σ', runOne (CerbMem.loadM tds loc ty pv) σ = (NDkilled r, σ')) := by
  unfold CerbMem.loadM runOne
  dsimp only
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only <;>
    repeat' (first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩
      | split)

/-- `allocateObject`'s one-layer result is active or killed (the
    out-of-memory kill, CerbMem.lean:1513). -/
theorem allocateObject_layer (tds : CerbTags.TagDefsMap) (tid : Nat) (pref : prefix0)
    (align : CerbMem.IntegerValue) (ty : ctype) (reqAddr : Option Int)
    (initOpt : Option CerbMem.MemValue) (σ : Mem) :
    (∃ pv σ', runOne (CerbMem.allocateObject tds tid pref align ty reqAddr initOpt) σ =
      (NDactive pv, σ')) ∨
    (∃ r σ', runOne (CerbMem.allocateObject tds tid pref align ty reqAddr initOpt) σ =
      (NDkilled r, σ')) := by
  unfold CerbMem.allocateObject runOne
  rcases align with ⟨_, alignN⟩
  dsimp only
  repeat' (first
    | exact Or.inl ⟨_, _, rfl⟩
    | exact Or.inr ⟨_, _, rfl⟩
    | split)

/-- `applyMemM` is the active projection of the one-layer result. -/
theorem applyMemM_eq_ndProj {α : Type} (m : CerbMem.memM α) (σ : Mem) :
    applyMemM m σ = ndProj (runOne m σ) := by
  rcases m with ⟨g⟩; rfl

/-- A one-layer memory operation that `applyMemM` refuses is KILLED. -/
theorem applyMemM_none_killed {α : Type} {m : CerbMem.memM α} {σ : Mem}
    (hlayer : (∃ z σ', runOne m σ = (NDactive z, σ')) ∨
      (∃ r σ', runOne m σ = (NDkilled r, σ')))
    (h : applyMemM m σ = none) : ∃ r σ', runOne m σ = (NDkilled r, σ') := by
  rcases hlayer with ⟨z, σ', hz⟩ | hk
  · rw [applyMemM_eq_ndProj, hz] at h
    cases h
  · exact hk

/-- `liftMem` (Driver.lean:218) of a KILLED one-layer memM computation:
    the kill is lifted by `liftAction`'s `DErr_memory` injection on the
    `Other` arm (Nondeterminism.lean:306), the memory written back. -/
theorem runOne_liftMem_killed {a : Type}
    {m : ndM a String mem_error (mem_constraint CerbMem.IntegerValue) CerbMem.MemState}
    {dst : driver_state} {r : kill_reason mem_error} {σ' : CerbMem.MemState}
    (h : runOne m dst.layout_state = (NDkilled r, σ')) :
    runOne (liftMem m) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  show runOne (liftND_lemFuel lemDefaultFuel _ _ _ _ (ND g)) dst = _
  rw [show lemDefaultFuel = Nat.succ 999999 from rfl]
  unfold liftND_lemFuel
  dsimp only [runOne]
  rw [h]
  rw [show (999999 : Nat) = Nat.succ 999998 from rfl]
  unfold liftAction_lemFuel
  cases r <;> rfl

/-- StoreRequest2 discharge, KILLED (Driver.lean:273): the kill is the
    lifted `storeM` kill at the request's own location. -/
theorem ars_store_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {mo : memory_order}
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue}
    {k : Nat → CerbMem.Footprint → thread_state} {tid aid : Nat}
    {dst : driver_state} {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.storeM tds loc ty lk pv mv) dst.layout_state = (NDkilled r, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (StoreRequest2 mo ty lk pv mv k)) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  unfold action_request_sequential2
  dsimp only
  exact runOne_bind_killed (runOne_liftMem_killed h)

/-- LoadRequest2 discharge, KILLED. -/
theorem ars_load_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {mo : memory_order}
    {ty : ctype} {pv : CerbMem.PointerValue}
    {k : Nat → CerbMem.Footprint → CerbMem.MemValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.loadM tds loc ty pv) dst.layout_state = (NDkilled r, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (LoadRequest2 mo ty pv k)) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  unfold action_request_sequential2
  dsimp only
  exact runOne_bind_killed (runOne_liftMem_killed h)

/-- CreateRequest2 discharge, KILLED (the out-of-memory kill;
    `allocateObject` discards the thread id, CerbMem.lean:1504). -/
theorem ars_create_killed {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {pref : prefix0}
    {align : CerbMem.IntegerValue} {ty : ctype} {reqAddr : Option Int}
    {initOpt : Option CerbMem.MemValue}
    {k : Nat → CerbMem.PointerValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {r : kill_reason mem_error} {σ' : Mem}
    (h : runOne (CerbMem.allocateObject tds 0 pref align ty reqAddr initOpt)
        dst.layout_state = (NDkilled r, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (CreateRequest2 pref align ty reqAddr initOpt k)) dst =
      (NDkilled (match r with
        | Undef0 l ubs => Undef0 l ubs
        | Error0 l s => Error0 l s
        | Other err => Other (DErr_memory err)),
       { dst with layout_state := σ' }) := by
  unfold action_request_sequential2
  dsimp only
  exact runOne_bind_killed (runOne_liftMem_killed h)

/-! ## The round's derived readings -/

/-- The thread literal is injective in (expression, env). -/
theorem MachineCtx.thread_inj {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    (h : M.thread e ρ = M.thread e' ρ') : e = e' ∧ ρ = ρ' :=
  ⟨congrArg thread_state.arena h, congrArg thread_state.env h⟩

/-- THE LOOP-LEVEL READING of a shipped round: one iteration of
    `drive_nonmemory_steps_aux2` at any fuel `fl` and accumulator
    continues at the successor state — the `loop_step_frag` shape,
    at the context's own tagDefs and thread id. -/
theorem CerberusRound.loop_step {M : MachineCtx} {c c' : Config}
    (h : CerberusRound M c c') {dst : driver_state} (hemb : M.Embeds dst c)
    (fl : Nat) (acc : Fmap thread_id (List core_step2)) :
    ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      rs'.labeled = dst.core_run_state0.labeled ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) M.tagDefs acc [M.tid]) dst =
        runOne (drive_nonmemory_steps_aux2_lemFuel fl M.tagDefs acc [M.tid])
          { dst with
              core_state0 := update_thread_state M.tid (M.thread c'.1 c'.2.1) dst.core_state0,
              layout_state := c'.2.2,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr } := by
  obtain ⟨s, hsteps, hca, rs', tr, ctr, hlab, hadv⟩ := h dst hemb
  exact ⟨rs', tr, ctr, hlab, loop_step_of_advance fl acc hemb.thread hsteps hca hadv⟩

/-- THE RUNNER-LEVEL READING: the shipped exhaustive runner
    (`CerbND.runND`, CerbND.lean:136) on the advance delivers exactly
    one `Active` execution. -/
theorem CerberusRound.runND {M : MachineCtx} {c c' : Config}
    (h : CerberusRound M c c') {dst : driver_state} (hemb : M.Embeds dst c) :
    ∃ s : core_step2,
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread c.1 c.2.1) = [s] ∧
      ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
        CerbND.runND (advance_step M.tagDefs M.tid s) dst =
          [(nd_status.Active NOWAKEUP, ([] : List String),
            { dst with
              core_state0 := update_thread_state M.tid (M.thread c'.1 c'.2.1) dst.core_state0,
              layout_state := c'.2.2,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr })] := by
  obtain ⟨s, hsteps, -, rs', tr, ctr, -, hadv⟩ := h dst hemb
  exact ⟨s, hsteps, rs', tr, ctr, runND_active hadv⟩

/-! ## THE CERTIFICATION: mirror step ⇒ shipped round -/

/-- THE UNIFIED STEP-MATCH OVER THE SHIPPED DRIVER: wherever the mirror
    steps at a `Frag` configuration (cons-shaped environment, `esize e ≤
    lemDefaultFuel`), the shipped driver's round at every embedding
    state is exactly that step — one case per redex root, each
    discharged by the engine equation of the redex (`step_ctx_*`,
    Soundness.lean / DriverCollapse.lean) and the matching
    `advance_step` arm. Stated at the context's OWN tagDefs and extern
    map (the driver functions take the reader argument; `loop_step_frag`
    is this theorem's instance at the production profile `fmapEmpty`). -/
theorem engine_step_matchU {M : MachineCtx}
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, σ) (e', ρ', σ')) :
    CerberusRound M (e, ev0 :: evs, σ) (e', ρ', σ') := by
  intro dst hemb
  obtain ⟨hth, hlay, hfile, hext, hrs⟩ := hemb
  simp only at hth hlay
  subst hlay
  have hnv : toVal e = none := hs.toVal_none
  obtain ⟨ctx, r, hd, hfr⟩ := hf.decomp hnv
  rcases hd.step_factor hs with ⟨r', ρr, σr, hnr, hr, heq⟩ |
    ⟨ra, l, pes, rfl, hr⟩
  · obtain ⟨he', hρ', hσ'⟩ : e' = apply_ctx ctx r' ∧ ρ' = ρr ∧ σ' = σr := by
      simpa [Prod.mk.injEq] using heq
    subst he' hρ' hσ'
    have hccall := hd.unseq_ccall_false
    have hrj := hd.redex
    cases hrj with
    | @store loc ann lk ty pv cv mo =>
      obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hr.store_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot [DA_pos [] fp]
          (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      have hsteps := step_ctx_store hd hsz M.tagDefs hmv
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs)) rfl
      rw [hccall] at hsteps
      refine ⟨_, hsteps, rfl, { dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_store (requestLoc (M.thread e (ev0 :: evs)) loc) none ty lk pv mv
          :: dst.trace, dst.dr_step_counter, rfl, ?_⟩
      exact advance_action (ars_store_active (tid := M.tid)
        (aid := dst.core_run_state0.aid_supply) hmem)
    | @load loc ann ty pv mo =>
      obtain ⟨fp, mval, σ'', hmem, hout⟩ := hr.load_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot [DA_pos [] fp]
          (Expr [] (Epure (Pexpr [] () (PEval
            (valueFromMemValue mval).2))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      have hsteps := step_ctx_load hd hsz M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs)) rfl
      rw [hccall] at hsteps
      refine ⟨_, hsteps, rfl, { dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_load (requestLoc (M.thread e (ev0 :: evs)) loc) none ty pv mval
          :: dst.trace, dst.dr_step_counter, rfl, ?_⟩
      exact advance_action (ars_load_active (tid := M.tid)
        (aid := dst.core_run_state0.aid_supply) hmem)
    | @create loc ann align ty pref =>
      obtain ⟨pv, σ'', hmem, hout⟩ := hr.create_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] ()
          (PEval (Vobject (OVpointer pv))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      have hsteps := step_ctx_create hd hsz M.tagDefs
        dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs)) rfl
      rw [hccall] at hsteps
      refine ⟨_, hsteps, rfl, { dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_allocate_object M.tid pref align ty none pv :: dst.trace,
        dst.dr_step_counter, rfl, ?_⟩
      exact advance_action (ars_create_active (tid := M.tid)
        (aid := dst.core_run_state0.aid_supply) hmem)
    | @beta_pure pa bty v e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
          ⟨_, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩
      · exact absurd hstep (fun h => Step.val_elim h)
      · obtain rfl : v' = v := by
          have : ofVal (.pure v') = ofVal (.pure v) := he1.symm
          simpa [ofVal] using this
        obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_beta_pure hd hsz M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · exact absurd he1 (by simp [ofVal])
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
    | @beta_annot pa bty ds v e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
          ⟨_, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩
      · exact absurd hstep (fun h => Step.val_elim h)
      · exact absurd he1 (by simp [ofVal])
      · obtain ⟨hds, hv⟩ : ds = ds' ∧ v = v' := by simpa [ofVal] using he1
        subst hds hv
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot ds e2) ∧
            ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_beta_annot hd hsz M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
    | @wbeta_pure pa bty v e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
          ⟨_, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩
      · exact absurd hstep (fun h => Step.val_elim h)
      · obtain rfl : v' = v := by
          have : ofVal (.pure v') = ofVal (.pure v) := he1.symm
          simpa [ofVal] using this
        obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_wseq_pure hd hsz M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · exact absurd he1 (by simp [ofVal])
      · rw [jumpRedex?_ofVal] at hj; cases hj
    | @wbeta_annot pa bty ds v e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
          ⟨_, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩
      · exact absurd hstep (fun h => Step.val_elim h)
      · exact absurd he1 (by simp [ofVal])
      · obtain ⟨hds, hv⟩ : ds = ds' ∧ v = v' := by simpa [ofVal] using he1
        subst hds hv
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot ds e2) ∧
            ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_wseq_annot hd hsz M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · rw [jumpRedex?_ofVal] at hj; cases hj
    | @merge ds1 ds2 b hirr =>
      rcases hr.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
          ⟨a2, ds2', c, hbeq, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
      · rw [show annotRooted (Expr ([] : List annot) (Eannot ds2 b)) = true
          from rfl] at hg
        cases hg
      · injection hbeq with hb1 hb2
        injection hb2 with hb3 hb4
        subst hb1 hb3 hb4
        obtain ⟨h1, h2, h3⟩ : r' = Expr ([] ++ []) (Eannot (ds1 ++ ds2) b) ∧
            ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_merge hd hirr hsz M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · rw [show annotRooted (Expr ([] : List annot) (Eannot ds2 b)) = true
          from rfl] at hg
        cases hg
    | save sb ps body =>
      have hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | save hdep _ => exact hdep
      rcases hr.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
          ⟨cvals, hnvS, hvals, hout⟩
      · obtain ⟨h1, h2, h3⟩ : r' = body ∧
            ρ' = bindSaveParams ps cvals (ev0 :: evs) ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_save hd hsz hvals M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · obtain ⟨h1, h2, h3⟩ : r' = saveRedex sb (saveParamsWithValues ps cvals) body ∧
            ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
          simpa [Prod.mk.injEq, saveRedex] using hout
        subst h1 h2 h3
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_save_eval_ws hd hsz hnvS hdep
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs)) rfl
          (by rw [hext]; exact hvals)
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
          dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | if_ g e2 e3 =>
      have hdg : peDepth g ≤ lemDefaultFuel := by
        cases hfr with
        | if_ hdg _ _ => exact hdg
      rcases hr.if_inv with ⟨hg, hout⟩ | ⟨hg, hout⟩
      · obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_true_ws hd hsz hdg
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs)) rfl
          (by rw [hext]; exact hg)
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
          dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_withrs_tau M.tagDefs M.tid s m (hm dst.core_run_state0)
      · obtain ⟨h1, h2, h3⟩ : r' = e3 ∧ ρ' = ev0 :: evs ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_false_ws hd hsz hdg
          M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs)) rfl
          (by rw [hext]; exact hg)
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
          dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_withrs_tau M.tagDefs M.tid s m (hm dst.core_run_state0)
    | case_ pe pats =>
      cases hfr with
      | case_value hbr hbsz =>
        obtain ⟨cval', e'', hv, hsel, hout⟩ := hr.case_inv
        obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
        obtain ⟨h1, h2, h3⟩ : r' = e'' ∧ ρ' = ev0 :: evs ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_case_value hd hsz hsel M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
    | run ra l pes =>
      exact absurd rfl (hnr ra l pes)
    | @pure_e pe hnv2 =>
      obtain ⟨pb, x, rfl⟩ : ∃ pb x, pe = Pexpr pb () (PEsym x) := by
        cases hfr with
        | val_pure v => rw [valueFromPexpr_val] at hnv2; cases hnv2
        | pure_sym => exact ⟨_, _, rfl⟩
      obtain ⟨v, -, hv, hout⟩ := hr.pure_inv
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] () (PEval v))) ∧
          ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_pure_sym_ws hd hsz
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs)) rfl
        (by rw [hext]; exact hv)
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
        dst.dr_step_counter + 1, rfl, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @load_op loc ann ty pe2 mo hnv2 =>
      obtain ⟨hp2, hd2⟩ : PePure pe2 ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | load =>
          rw [show valueFromPexpr (Pexpr [] () (PEval
            (Vobject (OVpointer _)))) = some _ from rfl] at hnv2
          cases hnv2
        | load_op hnv2' hp2 hd2 => exact ⟨hp2, hd2⟩
      obtain ⟨pv, hv2, hout⟩ := hr.load_op_inv hnv2
      obtain ⟨h1, h2, h3⟩ : r' = loadRedex loc ann ty pv mo ∧
          ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
        simpa [Prod.mk.injEq, loadRedex] using hout
      subst h1 h2 h3
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_load_eval_ws hd hsz hnv2 hp2 hd2
        M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs)) rfl
        (by rw [hext]; exact hv2)
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
        dst.dr_step_counter + 1, rfl, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @beta_spec pa pb x bty w e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', v', _, _, hpat, he1, _, hout⟩
      · exact absurd hstep (fun h => Step.val_elim h)
      · exact (specPat_ne_base hpat.symm).elim
      · exact (specPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl : w = .pure (Vloaded (LVspecified ov')) := by
          cases w with
          | pure v0 =>
            obtain rfl : v0 = Vloaded (LVspecified ov') := by
              simpa [ofVal] using he1
            rfl
          | annot ds0 v0 => exact absurd he1 (by simp [ofVal])
        obtain ⟨h1, h2, h3⟩ : r' = e2 ∧
            ρ' = update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov')) (ev0 :: evs) ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_beta_spec_pure hd hsz M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl : w = .annot ds' (Vloaded (LVspecified ov')) := by
          cases w with
          | pure v0 => exact absurd he1 (by simp [ofVal])
          | annot ds0 v0 =>
            obtain ⟨rfl, rfl⟩ : ds0 = ds' ∧ v0 = Vloaded (LVspecified ov') := by
              simpa [ofVal] using he1
            rfl
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot ds' e2) ∧
            ρ' = update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov')) (ev0 :: evs) ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_beta_spec_annot hd hsz M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
      · exact (symPat_ne_spec hpat).elim
    | @memop mop pes =>
      cases hfr with
      | memop_vals v1 v2 =>
        cases hr with
        | run hj hl hvs => simp [memopRedex] at hj
        | memop_eval hnv hv1' hv2' =>
          rw [valueFromPexprs_pair, valueFromPexpr_val,
            valueFromPexpr_val] at hnv
          cases hnv
        | @memop_ptreq _ _ _ pv1 pv2 b _ _ _ h1 h2 hmem =>
          rw [valueFromPexpr_val] at h1 h2
          obtain rfl : v1 = Vobject (OVpointer pv1) := Option.some.inj h1
          obtain rfl : v2 = Vobject (OVpointer pv2) := Option.some.inj h2
          have hsteps := step_ctx_memop hd hsz rfl rfl M.tagDefs
            dst.layout_state dst.core_file dst.core_extern M.tid M.parent
            (M.thread e (ev0 :: evs)) rfl
          rw [hccall] at hsteps
          refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
            dst.dr_step_counter, rfl, ?_⟩
          exact advance_memop (ars_memop_active M.tagDefs (by
            rw [eqPtrval_loc_irrel _ default pv1 pv2]; exact hmem))
      | memop_op hnvF hp1 hp2 hpd1 hpd2 =>
        obtain ⟨v1, v2, hv1', hv2', hout⟩ := hr.memop_op_inv hnvF
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Ememop PtrEq
            [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) ∧
            ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_memop_eval_ws hd hsz hnvF
          hpd1 hpd2 M.tagDefs dst.layout_state dst.core_file
          dst.core_extern M.tid M.parent
          (M.thread e (ev0 :: evs)) rfl
          (by rw [hext]; exact hv1') (by rw [hext]; exact hv2')
        refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
          dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @store_op loc ann ty pe2 pe3 mo hnvR =>
      obtain ⟨hp2, hp3, hpd2, hpd3⟩ :
          PePure pe2 ∧ PePure pe3 ∧
          peDepth pe2 ≤ lemDefaultFuel ∧ peDepth pe3 ≤ lemDefaultFuel := by
        cases hfr with
        | store =>
          rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvR
          cases hnvR
        | store_op hnv' hp2 hp3 hpd2 hpd3 =>
          exact ⟨hp2, hp3, hpd2, hpd3⟩
      obtain ⟨pv, cv, hv2, hv3, hout⟩ := hr.store_op_inv hnvR
      obtain ⟨h1, h2, h3⟩ : r' = storeRedex loc ann false ty pv cv mo ∧
          ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
        simpa [Prod.mk.injEq, storeRedex] using hout
      subst h1 h2 h3
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_store_eval_ws hd hsz hnvR
        hp2 hp3 hpd2 hpd3 M.tagDefs dst.layout_state dst.core_file
        dst.core_extern M.tid M.parent
        (M.thread e (ev0 :: evs)) rfl
        (by rw [hext]; exact hv2) (by rw [hext]; exact hv3)
      refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
        dst.dr_step_counter + 1, rfl, ?_⟩
      exact advance_withrs_eval M.tagDefs M.tid s m (hm dst.core_run_state0)
    | @beta_sym pa x bty w e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', v', _, _, hpat, he1, _, hout⟩
      · exact absurd hstep (fun h => Step.val_elim h)
      · exact (symPat_ne_base hpat.symm).elim
      · exact (symPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (symPat_ne_spec hpat.symm).elim
      · exact (symPat_ne_spec hpat.symm).elim
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl : w = .pure v' := by
          cases w with
          | pure v0 =>
            obtain rfl : v0 = v' := by simpa [ofVal] using he1
            rfl
          | annot ds0 v0 => exact absurd he1 (by simp [ofVal])
        obtain ⟨h1, h2, h3⟩ : r' = e2 ∧
            ρ' = update_env (symPat pa x bty) v' (ev0 :: evs) ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨_, step_ctx_beta_sym_pure hd hsz M.tagDefs dst.layout_state
            dst.core_file dst.core_extern M.tid M.parent _ rfl rfl,
          rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact advance_tau M.tagDefs M.tid _ _ dst
  · -- the jump disjunct: the context is discarded; the label read
    -- resolves in the driver's run state, which IS the context's
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hr.jump_inv (by rfl)
    have hdep : ∀ pe' ∈ pes, peDepth pe' ≤ lemDefaultFuel := by
      cases hfr with
      | run hdep => exact hdep
    obtain ⟨p, hp, hQ⟩ := MachineCtx.labels_lookup_some hl
    obtain ⟨h1, h2, h3⟩ : e' = cont ∧
        ρ' = bindArgs params vs (ev0 :: evs) ∧ σ' = dst.layout_state := by
      simpa [Prod.mk.injEq] using hout
    subst h1 h2 h3
    obtain ⟨s, m, hsteps, hm⟩ := step_ctx_run_ws hd hsz hl hdep
      M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid M.parent p
      (M.thread e (ev0 :: evs)) rfl hp
      (by rw [hext]; exact hvs)
    refine ⟨_, hsteps, rfl, dst.core_run_state0, dst.trace,
      dst.dr_step_counter + 1, rfl, ?_⟩
    exact advance_withrs_eval M.tagDefs M.tid s m
      (hm dst.core_run_state0 (by rw [hext, hrs]; exact hQ))

/-- MATCH-GIVEN-STEP as a relation inclusion (`engine_step_matchU`
    re-read at a configuration successor). -/
theorem Step.toCerberusRound {M : MachineCtx} {e : CoreExpr}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem} {c' : Config}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ev0 :: evs, σ) c') :
    CerberusRound M (e, ev0 :: evs, σ) c' := by
  obtain ⟨e', ρ', σ'⟩ := c'
  exact engine_step_matchU hf hsz hs

/-- THE TWO-SIDED ARM, GIVEN A MIRROR STEP: wherever the mirror steps
    at all, `Step` and the shipped round coincide (both directions), for
    every successor. The hypothesis `hstep` is load-bearing: at an
    annotated value the shipped round is the REMOVE-ANNOT tau while the
    mirror does not step (the value protocol) — see the classification. -/
theorem step_iff_cerberusRound {M : MachineCtx} {e : CoreExpr}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hstep : ∃ c', Step M (e, ev0 :: evs, σ) c') (c' : Config) :
    Step M (e, ev0 :: evs, σ) c' ↔ CerberusRound M (e, ev0 :: evs, σ) c' := by
  constructor
  · exact Step.toCerberusRound hf hsz
  · intro hr
    obtain ⟨c₀, hs₀⟩ := hstep
    have hr₀ := Step.toCerberusRound hf hsz hs₀
    obtain ⟨dst, hemb⟩ := M.embeds_exists (e, ev0 :: evs, σ)
    obtain ⟨s, hsteps, -, rs', tr, ctr, -, hadv⟩ := hr dst hemb
    obtain ⟨s₀, hsteps₀, -, rs₀, tr₀, ctr₀, -, hadv₀⟩ := hr₀ dst hemb
    obtain rfl : s₀ = s := by
      rw [hsteps₀] at hsteps
      exact (List.cons.inj hsteps).1
    rw [hadv₀] at hadv
    have hD := (Prod.mk.inj hadv).2
    obtain ⟨e', ρ', σ'⟩ := c'
    obtain ⟨e₀, ρ₀, σ₀⟩ := c₀
    have hcs := congrArg (fun d : driver_state => d.core_state0.thread_states) hD
    have hlay := congrArg (fun d : driver_state => d.layout_state) hD
    simp only at hcs hlay
    rw [update_thread_state_single' M.tid M.parent _ _ _ hemb.thread,
      update_thread_state_single' M.tid M.parent _ _ _ hemb.thread] at hcs
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hcs
    obtain ⟨rfl, rfl⟩ := MachineCtx.thread_inj hcs
    subst hlay
    exact hs₀

/-! ## The exhaustive per-configuration classification -/

/-- The classification (statement in the module header). -/
inductive RoundClass (M : MachineCtx) (c : Config) : Prop where
  | value_done (v : value) :
      c.1 = ofVal (.pure v) →
      (∀ dst, M.Embeds dst c →
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) = [Step_done2 v]) →
      RoundClass M c
  | value_annot (ds : List dyn_annotation) (v : value) :
      c.1 = ofVal (.annot ds v) →
      CerberusRound M c (ofVal (.pure v), c.2.1, c.2.2) →
      RoundClass M c
  | step (c' : Config) :
      Step M c c' →
      (∀ c'', Step M c c'' ↔ CerberusRound M c c'') →
      RoundClass M c
  | refused :
      toVal c.1 = none →
      (∀ c', ¬ Step M c c') →
      RoundClass M c

/-- PROGRAM-DONE at a bare value, in the shipped driver's terms (reads
    exactly `SeqWF`: empty stack selects PROGRAM-DONE over RETURN, no
    parent over THREAD-DONE). -/
theorem shipped_done {M : MachineCtx} (hwf : M.SeqWF) (v : value) (ρ : EnvStack)
    (dst : driver_state) :
    step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
      (M.parent, M.thread (ofVal (.pure v)) ρ) = [Step_done2 v] := by
  rw [hwf.parent]
  exact step_ctx_done v M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
    (M.thread (ofVal (.pure v)) ρ) rfl hwf.stack

/-- REMOVE-ANNOT at an annotated value is a shipped round to the bare
    value (env and memory verbatim; no context field read). -/
theorem shipped_remove_annot (M : MachineCtx) (ds : List dyn_annotation) (v : value)
    (ρ : EnvStack) (σ : Mem) :
    CerberusRound M (ofVal (.annot ds v), ρ, σ) (ofVal (.pure v), ρ, σ) := by
  intro dst hemb
  obtain ⟨hth, hlay, -, -, -⟩ := hemb
  simp only at hth hlay
  subst hlay
  refine ⟨_, step_ctx_remove_annot ds v M.tagDefs dst.layout_state dst.core_file
      dst.core_extern M.tid M.parent (M.thread (ofVal (.annot ds v)) ρ) rfl,
    rfl, dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
  exact advance_tau M.tagDefs M.tid _ _ dst

/-- THE CLASSIFICATION THEOREM (the exhaustive sum form): every
    well-sized `Frag` configuration at a sequentially well-formed
    context with a cons-shaped env stack falls into exactly one
    `RoundClass` arm; the `step` arm is two-sided given its mirror
    step. -/
theorem cerberusRound_classify {M : MachineCtx} (hwf : M.SeqWF)
    {e : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel) :
    RoundClass M (e, ev0 :: evs, σ) := by
  cases hv : toVal e with
  | some w =>
    have he : ofVal w = e := ofVal_of_toVal hv
    cases w with
    | pure v =>
      refine .value_done v he.symm ?_
      intro dst _
      rw [← he]
      exact shipped_done hwf v (ev0 :: evs) dst
    | annot ds v =>
      refine .value_annot ds v he.symm ?_
      show CerberusRound M (e, ev0 :: evs, σ) (ofVal (.pure v), ev0 :: evs, σ)
      rw [← he]
      exact shipped_remove_annot M ds v (ev0 :: evs) σ
  | none =>
    by_cases hstep : ∃ c', Step M (e, ev0 :: evs, σ) c'
    · obtain ⟨c', hs⟩ := hstep
      exact .step c' hs (step_iff_cerberusRound hf hsz ⟨c', hs⟩)
    · exact .refused hv (fun c' hs => hstep ⟨c', hs⟩)

/-- The arms are mutually exclusive (the classification is a
    partition, not merely a cover): a value is never a mirror step
    (value protocol), and `step`/`refused` contradict directly. -/
theorem RoundClass.value_not_step {M : MachineCtx} {c : Config} {w : SpikeVal}
    (he : c.1 = ofVal w) : ∀ c', ¬ Step M c c' := by
  intro c' hs
  obtain ⟨e, ρ, σ⟩ := c
  simp only at he
  subst he
  exact hs.val_elim

/-! ## Per-row REFUSAL classification, in the shipped driver's terms

Where the mirror is stuck at one of these redexes, the shipped round
is a KILL (the memory operation's `NDkilled`, lifted by `liftMem`) or
an ILLTYPED report — never a successful round. -/

/-- The refusal classification at a STORE redex: the ILLTYPED report
    when the value does not encode at the lvalue type
    (`step_action`'s Store0 arm, Core_reduction.lean:424), else
    `storeM`'s kill (CerbMem.lean:1667 — the `MerrAccess` UB kills
    arrive as `Undef0`, the ill-typed-memory-value/`MerrOther` kills as
    `Other (DErr_memory _)`), at the request's own location. -/
theorem cerberusRound_refused_store (M : MachineCtx)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
    {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order}
    (ρ : EnvStack) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (storeRedex loc ann lk ty pv cv mo, ρ, σ) c') :
    ShippedRefusal M (storeRedex loc ann lk ty pv cv mo, ρ, σ) := by
  have hsz : esize (storeRedex loc ann lk ty pv cv mo) ≤ lemDefaultFuel := by
    rw [show esize (storeRedex loc ann lk ty pv cv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  cases hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv with
  | none =>
    refine .error (String.append (CerbLocation.stringFromLocation loc)
        (String.append "the value of a store("
          (String.append (CerbPP.stringFromCore_ctype (Ctype [] (unatomic_ ty)))
            (String.append ") didn't match the lvalue type: "
              (CerbPP.stringFromCore_value cv))))) ?_
    intro dst hemb
    obtain ⟨-, hlay, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    exact step_ctx_store_illtyped (Decomp.root Redex.store) hsz M.tagDefs hmv
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ) rfl
  | some mv =>
    have hnone : applyMemM (CerbMem.storeM M.tagDefs
        (requestLoc (M.thread (storeRedex loc ann lk ty pv cv mo) ρ) loc) ty lk pv mv) σ =
        none := by
      rw [storeM_loc_irrel loc]
      cases hmem : applyMemM (CerbMem.storeM M.tagDefs loc ty lk pv mv) σ with
      | none => rfl
      | some fpσ =>
        obtain ⟨fp, σ'⟩ := fpσ
        exact absurd (Step.store_canonical hmv hmem) (hstuck _)
    obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (storeM_layer _ _ _ _ _ _ _) hnone
    apply ShippedRefusal.killed
    intro dst hemb
    obtain ⟨-, hlay, -, -, -⟩ := hemb
    simp only at hlay
    subst hlay
    have hsteps := step_ctx_store (Decomp.root Redex.store) hsz M.tagDefs hmv
      dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ) rfl
    rw [show is_unseq_with_ccall CTX = false from rfl] at hsteps
    exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_store_killed hk)⟩

/-- The refusal classification at a LOAD redex: `loadM`'s kill
    (CerbMem.lean:1621 — null/function/out-of-bounds/dead pointers are
    `MerrAccess` UB kills, `Undef0`; the trap representation and
    outside-lifetime kills likewise per `failReason`), at the request's
    own location. -/
theorem cerberusRound_refused_load (M : MachineCtx)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (ρ : EnvStack) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (loadRedex loc ann ty pv mo, ρ, σ) c') :
    ShippedRefusal M (loadRedex loc ann ty pv mo, ρ, σ) := by
  have hsz : esize (loadRedex loc ann ty pv mo) ≤ lemDefaultFuel := by
    rw [show esize (loadRedex loc ann ty pv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hnone : applyMemM (CerbMem.loadM M.tagDefs
      (requestLoc (M.thread (loadRedex loc ann ty pv mo) ρ) loc) ty pv) σ = none := by
    rw [loadM_loc_irrel loc]
    cases hmem : applyMemM (CerbMem.loadM M.tagDefs loc ty pv) σ with
    | none => rfl
    | some r =>
      obtain ⟨⟨fp, mval⟩, σ'⟩ := r
      exact absurd (Step.load_canonical hmem) (hstuck _)
  obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (loadM_layer _ _ _ _ _) hnone
  apply ShippedRefusal.killed
  intro dst hemb
  obtain ⟨-, hlay, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  have hsteps := step_ctx_load (Decomp.root Redex.load) hsz M.tagDefs
    dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ) rfl
  rw [show is_unseq_with_ccall CTX = false from rfl] at hsteps
  exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_load_killed hk)⟩

/-- The refusal classification at a CREATE redex: the out-of-memory
    kill (CerbMem.lean:1513, `Other (MerrOther "out of memory")`, lifted
    to `Other (DErr_memory _)`) — the arm `allocCap`'s plan-fit
    excludes. -/
theorem cerberusRound_refused_create (M : MachineCtx)
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (ρ : EnvStack) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (createRedex loc ann align ty pref, ρ, σ) c') :
    ShippedRefusal M (createRedex loc ann align ty pref, ρ, σ) := by
  have hsz : esize (createRedex loc ann align ty pref) ≤ lemDefaultFuel := by
    rw [show esize (createRedex loc ann align ty pref) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hnone : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ =
      none := by
    cases hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ with
    | none => rfl
    | some r =>
      obtain ⟨pv, σ'⟩ := r
      exact absurd (Step.create_canonical hmem) (hstuck _)
  obtain ⟨r, σ', hk⟩ := applyMemM_none_killed (allocateObject_layer _ _ _ _ _ _ _ _) hnone
  apply ShippedRefusal.killed
  intro dst hemb
  obtain ⟨-, hlay, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  have hsteps := step_ctx_create (Decomp.root Redex.create) hsz M.tagDefs
    dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ) rfl
  rw [show is_unseq_with_ccall CTX = false from rfl] at hsteps
  exact ⟨_, _, hsteps, rfl, advance_action_killed (ars_create_killed hk)⟩

/-- The refusal classification at a value-scrutinee CASE redex: the
    ILLTYPED no-match report (one_step0's Ecase value arm,
    Core_reduction.lean:353). -/
theorem cerberusRound_refused_case (M : MachineCtx)
    {b : List annot} {cval : value} {pats : List (pattern × CoreExpr)}
    (hsz : esize (caseRedex (Pexpr b () (PEval cval)) pats) ≤ lemDefaultFuel)
    (ρ : EnvStack) (σ : Mem)
    (hstuck : ∀ c', ¬ Step M (caseRedex (Pexpr b () (PEval cval)) pats, ρ, σ) c') :
    ShippedRefusal M (caseRedex (Pexpr b () (PEval cval)) pats, ρ, σ) := by
  have hsel : select_case subst_sym_expr cval pats = none := by
    cases hsel : select_case subst_sym_expr cval pats with
    | none => rfl
    | some e' =>
      exact absurd (Step.case_value (valueFromPexpr_val _ _) hsel) (hstuck _)
  refine .error (String.append "Ecase, mismatched ==> "
      (CerbPP.stringFromCore_expr (caseRedex (Pexpr b () (PEval cval)) pats))) ?_
  intro dst hemb
  obtain ⟨-, hlay, -, -, -⟩ := hemb
  simp only at hlay
  subst hlay
  exact step_ctx_case_illtyped (Decomp.root (Redex.case_ _ _)) hsz hsel M.tagDefs
    dst.layout_state dst.core_file dst.core_extern M.tid M.parent (M.thread _ ρ) rfl

/-! ## The discharge-device readings (PROOF DEVICES — `outcomesU`)

The four completeness pairs over the hand-written discharge (`store`
and `case` in Soundness.lean, `load` and `create` here) are kept as
proof devices: they are how the `driveU` lane's classification goes.
They appear in no export's statement. -/

/-- LOAD IS TWO-SIDED at the discharge device. -/
theorem engine_complete_loadU (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pv : CerbMem.PointerValue} {mo : memory_order}
    (ρ : EnvStack) (σ : Mem) :
    ∃ o, outcomesU M aid (loadRedex loc ann ty pv mo) ρ σ = [o] ∧
      EngineMatchU M (loadRedex loc ann ty pv mo) ρ σ o := by
  have hsz : esize (loadRedex loc ann ty pv mo) ≤ lemDefaultFuel := by
    rw [show esize (loadRedex loc ann ty pv mo) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  cases hmem : applyMemM (CerbMem.loadM M.tagDefs loc ty pv) σ with
  | some r =>
    obtain ⟨⟨fp, mval⟩, σ'⟩ := r
    refine ⟨_, ?_, .step (Step.load_canonical hmem)⟩
    unfold outcomesU engineStepsU loadRedex
    rw [step_ctx_load (Decomp.root (Redex.load)) hsz M.tagDefs σ
      M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_load_active hmem]
    rfl
  | none =>
    refine ⟨dischargeStep M.tagDefs aid M.runState σ (Step_action_request2
        "LoadRequest" (requestLoc (M.thread (loadRedex loc ann ty pv mo) ρ) loc) M.tid
        (is_unseq_with_ccall CTX)
        (stExceptUndef_return (LoadRequest2 mo ty pv (fun _ fp mval =>
          { M.thread (loadRedex loc ann ty pv mo) ρ with
            arena := apply_ctx CTX (Expr [] (Eannot [DA_pos [] fp]
              (Expr [] (Epure (Pexpr [] () (PEval
                (valueFromMemValue mval).2)))))) })))),
      ?_, ?_⟩
    · unfold outcomesU engineStepsU loadRedex
      rw [step_ctx_load (Decomp.root (Redex.load)) hsz M.tagDefs σ
        M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
      rfl
    · refine .refused (dischargeStep_load_refusal hmem) (fun out hstep => ?_) rfl
      obtain ⟨fp', mval', σ'', hmem', -⟩ := hstep.load_inv
      rw [hmem] at hmem'
      cases hmem'

/-- CREATE IS TWO-SIDED at the discharge device. -/
theorem engine_complete_createU (M : MachineCtx) (aid : Nat)
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0}
    (ρ : EnvStack) (σ : Mem) :
    ∃ o, outcomesU M aid (createRedex loc ann align ty pref) ρ σ = [o] ∧
      EngineMatchU M (createRedex loc ann align ty pref) ρ σ o := by
  have hsz : esize (createRedex loc ann align ty pref) ≤ lemDefaultFuel := by
    rw [show esize (createRedex loc ann align ty pref) = 1 from rfl]
    unfold lemDefaultFuel
    omega
  have hirr := allocateObject_arg_irrel M.tagDefs 0 0 pref align ty (get_with_address []) none none
  cases hmem : applyMemM (CerbMem.allocateObject M.tagDefs 0 pref align ty none none) σ with
  | some r =>
    obtain ⟨pv, σ'⟩ := r
    refine ⟨_, ?_, .step (Step.create_canonical hmem)⟩
    unfold outcomesU engineStepsU createRedex
    rw [step_ctx_create (Decomp.root (Redex.create)) hsz M.tagDefs σ
      M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_create_active (hirr ▸ hmem)]
    rfl
  | none =>
    refine ⟨dischargeStep M.tagDefs aid M.runState σ (Step_action_request2
        "CreateRequest" (requestLoc (M.thread (createRedex loc ann align ty pref) ρ) loc) M.tid
        (is_unseq_with_ccall CTX)
        (stExceptUndef_return (CreateRequest2 pref align ty
          (get_with_address []) none (fun _ pv =>
          { M.thread (createRedex loc ann align ty pref) ρ with
            arena := apply_ctx CTX (Expr [] (Epure (Pexpr [] ()
              (PEval (Vobject (OVpointer pv)))))) })))),
      ?_, ?_⟩
    · unfold outcomesU engineStepsU createRedex
      rw [step_ctx_create (Decomp.root (Redex.create)) hsz M.tagDefs σ
        M.file M.extern M.tid M.parent (M.thread _ ρ) rfl]
      rfl
    · refine .refused (dischargeStep_create_refusal (hirr ▸ hmem)) (fun out hstep => ?_) rfl
      obtain ⟨pv', σ'', hmem', -⟩ := hstep.create_inv
      rw [hmem] at hmem'
      cases hmem'

/-- From a discharge-device completeness pair to its refusal reading. -/
theorem EngineMatchU.refusal_of_stuck {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {o : EngineOutcome} (hm : EngineMatchU M e ρ σ o)
    (hnv : toVal e = none) (hstuck : ∀ c', ¬ Step M (e, ρ, σ) c') :
    o.isRefusal := by
  cases hm with
  | step hs => exact (hstuck _ hs).elim
  | removeAnnot he => subst he; simp [toVal, ofVal] at hnv
  | done he => subst he; simp [toVal, ofVal] at hnv
  | refused hr _ _ => exact hr

end CerberusHeapLang
