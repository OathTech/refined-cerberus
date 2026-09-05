/-
CerberusHeapLang.DriverCollapse — the PRODUCTION driver pipeline
(scheduler, nondeterminism monad, result readout) collapsed onto this
package's drive round, for fragment configurations: the bridge that
lets statements at the total judgment become statements about the
shipped `runND (Driver.drive …)` composite (ProdLoop.lean,
ProdEntry.lean). Every theorem here is proved by unfolding the
driver's OWN round functions.

- SCHEDULER COLLAPSE: the production driver's round structure is
  `driver2` (Driver.lean:381-386) → `new_drive_core_threads`
  (Driver.lean:355) → `drive_nonmemory_steps_aux2` (Driver.lean:346-351),
  the fuelled per-thread loop {step_ctx → find_can_advance →
  advance_step}. For a single-threaded state whose thread holds a
  fragment configuration, ONE iteration of that loop is exactly one
  mirror step: the step_ctx singleton (the per-rule
  context-undisturbed lemmas, Soundness.lean) is advanced in place —
  taus via `advance_step`'s Step_tau2 arm (Driver.lean:336, ticking
  dr_step_counter), actions via `advance_step` → `liftCore_run` (the
  request monad, returning the run state verbatim) →
  `perform_action_request2` (Driver.lean:277, drawing the action id
  from `fresh_action_id'`, Driver.lean:283/Core_run.lean:116) →
  `action_request_sequential2` (Driver.lean:273, the memM discharge +
  trace push) — the exact composite `dischargeStep` mirrors
  (Soundness.lean header). PROGRAM-DONE steps are not advanceable
  (`can_advance`, Driver.lean:310), so the loop returns the singleton
  step map and `driver2` routes it through `process_core_step2`'s
  Step_done2 arm (Driver.lean:377, `prepare_exit`). The iteration
  lemmas (`loop_step_tau`/`loop_step_action`/`loop_step_done`, and the
  with-runstate/memop rounds) prove this by unfolding the driver's own
  round functions; `loop_step_frag` is the ONE production round at any
  fragment configuration where the mirror `Step` steps
  (single-threaded, parent-less, stack-empty — the fields the fragment
  reads), and `wpt_driver_aux` (ProdLoop.lean) iterates it.

- ND COLLAPSE: on the fragment the whole driver computation is a
  branch-free ndM tree — every node the fragment path crosses is a
  single-layer `NDactive`/`NDkilled` state transformer (nd_return/
  nd_get/nd_update/nd_read: Nondeterminism.lean:184-215; the memM ops
  `loadM`/`storeM`/`allocateObject`/`eqPtrval` on their active arms;
  `pick` on a SINGLETON list: Nondeterminism.lean:276, `NDactive`, no
  NDnd node), and `nd_bind`/`liftND` compose such layers into one
  layer (`runOne_bind_active`/`runOne_liftMem_active` — each bind
  spends one layer of its own fresh `nd_bind_lemFuel` budget, never
  accumulating). `runND` (CerbND.lean:89-138) on a one-layer active
  tree is the singleton execution (`runND_active`). Branch-freeness
  per construct is `engine_step_matchU`'s singleton step list; these
  lemmas lift it through the ndM structure.

- READOUT: `finalize` (Driver.lean:423) on the PROGRAM-DONE state:
  `prepare_exit` (Driver.lean:372) parks the delivered value as
  `mk_value_e v` in the single surviving thread; `to_pure`
  (Core_aux.lean:570) strips the Epure node; `Driver.hack`
  (Driver.lean:390-395) steps `step_eval_pexpr` (Core_eval.lean:142),
  whose PEval arm returns the pexpr unchanged, and `valueFromPexpr`
  (Core_aux.lean:472) reads the value back — `hack_value`/
  `finalize_done`. The value delivered by Step_done2 is always the
  BARE value form (the REMOVE-ANNOT tau precedes PROGRAM-DONE), so
  the annotated form never reaches `hack`; composition with the
  REMOVE-ANNOT readout happens inside `wpt_driver_aux`'s value
  protocol (ProdLoop.lean) and the partial lane's `drive_safe_aux`
  (Adequacy.lean).

- `driver2_done`: the whole `driver2` computation from a PROGRAM-DONE
  thread is the singleton `Active` execution, for both values of the
  opaque `current_execution_mode` test (`cases` on it) — the one
  configuration read on a proved path.

FUEL: the driver functions run at their production budgets. Since the
cerberus-lean fuel arc (pin `f95ef8d9c`, 2026-09-03) the DRIVE CONE —
`driver2`, `drive_nonmemory_steps_aux2`, `print_eval_conv_aux`, `hack`,
`nd_bind`, `CerbND.ndDefaultFuel` — runs at `CerbFuel.driverFuel = 10^8`
(the wrapper `rfl`s `CerbND.driver2_wrapper_defeq`,
`CerbND.nd_bind_wrapper_defeq`, `CerbND.runND_eq`, … pin the generated
wrappers to that constant); `liftND`/`liftAction`, the memory workers
and the evaluator stay at `lemDefaultFuel = 10^6`. `nd_bind`/`liftND`
budgets are spent per LAYER of one bind and never accumulate across the
run; `drive_nonmemory_steps_aux2`'s budget is spent once per loop
iteration, so statements carry `n + 2 ≤ CerbFuel.driverFuel` (n drive
steps + the done-recording and drain iterations); `driver2`'s budget
is spent once per non-advanceable step (exactly one: Step_done2);
get_ctx budgets are the inherited `esize` side conditions
(Soundness.lean FUEL HONESTY). At insufficient fuel the ND-typed
workers' value is the kernel-TRANSPARENT kill
`CerbND.fuelExhaustedKill` (`CerbND.driver2_lemFuel_zero` etc.); the
production-entry theorems here are TOTAL statements at a certified
step count and so carry the in-budget hypothesis (README, "Registered
divergences and limitations"); the partial lane (Adequacy.lean,
`DriverSafeCtl`) states the kill arm as an admissible outcome at every
fuel, and the exhaustion rounds below (`loop_zero_exhausts`,
`loop_step_done_exhaust`, `driver2_killed`, `runND_killed`) are its
driver arms. Budget numerals are unfolded ONLY through the `_succ`
lemmas below (never a `show`-forced numeral defeq: 10^8 vs 10^6 hits
the recursion-depth limit — the 2026-09-03 re-pin's error class).
-/
import CerberusHeapLang.Soundness
import Driver
import CerbND

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-! ## The runOne layer (the ND collapse): one-layer application of
an ndM tree -/

/-! `runOne` — one-layer application of an ndM computation at the raw
`nd_action × state` level — lives in Step.lean beside `applyMemM`/
`ndProj` since K1 (the heap layer states the engine's KILLED store arm
with it, `storeM_readonly_kills`). -/

private theorem lemDefaultFuel_succ : lemDefaultFuel = Nat.succ 999999 := rfl
/-- The drive-cone budget as a successor (the exemplar's `budget_succ`
    idiom, cerberus-lean `test/Unit/FuelExemplar.lean`). -/
private theorem driverFuel_succ : CerbFuel.driverFuel = Nat.succ 99999999 := rfl

@[simp] theorem runOne_return {a b c d st : Type} (x : a) (s : st) :
    runOne (nd_return x : ndM a c b d st) s = (NDactive x, s) := rfl

@[simp] theorem runOne_get {a b c : Type} {st : Type} (s : st) :
    runOne (nd_get : ndM st c b a st) s = (NDactive s, s) := rfl

@[simp] theorem runOne_update {a b c st : Type} (f : st → st) (s : st) :
    runOne (nd_update f : ndM Unit c b a st) s = (NDactive (), f s) := rfl

@[simp] theorem runOne_read {a b c st r : Type} (f : st → r) (s : st) :
    runOne (nd_read f : ndM r c b a st) s = (NDactive (f s), s) := rfl

/-- Sequencing preserves one-layer activity: nd_bind
    (Nondeterminism.lean:188-192) spends one layer of its own fresh
    fuel budget and composes the two state functions. -/
theorem runOne_bind_active {a b cs err info st : Type}
    {m : ndM a info err cs st} {f : a → ndM b info err cs st} {s s' : st} {z : a}
    (h : runOne m s = (NDactive z, s')) :
    runOne (nd_bind m f) s = runOne (f z) s' := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  show runOne (nd_bind_lemFuel CerbFuel.driverFuel (ND g) f) s = _
  rw [driverFuel_succ]
  unfold nd_bind_lemFuel
  dsimp only [runOne]
  rw [h]
  dsimp only
  rcases hf : f z with ⟨g'⟩
  rfl

/-- A kill on the left of a bind kills the bind. -/
theorem runOne_bind_killed {a b cs err info st : Type}
    {m : ndM a info err cs st} {f : a → ndM b info err cs st} {s s' : st}
    {r : kill_reason err}
    (h : runOne m s = (NDkilled r, s')) :
    runOne (nd_bind m f) s = (NDkilled r, s') := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  show runOne (nd_bind_lemFuel CerbFuel.driverFuel (ND g) f) s = _
  rw [driverFuel_succ]
  unfold nd_bind_lemFuel
  dsimp only [runOne]
  rw [h]

/-- `liftMem` (Driver.lean:218-223, via liftND
    Nondeterminism.lean:306) of an active one-layer memM computation:
    runs on `layout_state`, writes it back, one layer. -/
theorem runOne_liftMem_active {a : Type}
    {m : ndM a String mem_error (mem_constraint CerbMem.IntegerValue) CerbMem.MemState}
    {dst : driver_state} {z : a} {σ' : CerbMem.MemState}
    (h : runOne m dst.layout_state = (NDactive z, σ')) :
    runOne (liftMem m) dst = (NDactive z, { dst with layout_state := σ' }) := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  show runOne (liftND_lemFuel lemDefaultFuel _ _ _ _ (ND g)) dst = _
  rw [lemDefaultFuel_succ]
  unfold liftND_lemFuel
  dsimp only [runOne]
  rw [h]
  rw [show (999999 : Nat) = Nat.succ 999998 from rfl]
  unfold liftAction_lemFuel
  rfl

/-- The applyMemM bridge: the spike's one-layer memM verdict is the
    runOne verdict. -/
theorem runOne_of_applyMemM {α : Type} {m : CerbMem.memM α} {σ σ' : Mem} {z : α}
    (h : applyMemM m σ = some (z, σ')) :
    runOne m σ = (NDactive z, σ') := by
  rcases m with ⟨g⟩
  unfold applyMemM at h
  dsimp only at h
  rcases hf : g σ with ⟨act, st⟩
  rw [hf] at h
  dsimp only [runOne]
  rw [hf]
  cases act <;> simp only [] at h ⊢
  case NDactive x =>
    obtain ⟨rfl, rfl⟩ : x = z ∧ st = σ' := by cases h; exact ⟨rfl, rfl⟩
    rfl
  all_goals cases h

/-- liftCore_run (Driver.lean:245-248) of a returned request: the run
    state comes back VERBATIM (the fragment's request monads are
    stExceptUndef_return — D14's core_run_state row). -/
theorem runOne_liftCore_run_return {a : Type} (z : a) (dst : driver_state) :
    runOne (liftCore_run (stExceptUndef_return z)) dst = (NDactive z, dst) := by
  refine (runOne_bind_active (z := dst) rfl).trans ?_
  refine (runOne_bind_active (z := ())
    (s' := { dst with core_run_state0 := dst.core_run_state0 }) (by rfl)).trans ?_
  rfl

/-- liftCore_run of the driver's action-id draw (fresh_action_id',
    Core_run.lean:116): returns the current aid_supply and ticks it —
    the ONE run-state component the production driver moves per action
    (D14). -/
theorem runOne_liftCore_run_aid (dst : driver_state) :
    runOne (liftCore_run (runS fresh_action_id')) dst =
      (NDactive dst.core_run_state0.aid_supply,
       { dst with core_run_state0 :=
          { dst.core_run_state0 with aid_supply :=
              dst.core_run_state0.aid_supply + 1 } }) := by
  refine (runOne_bind_active (z := dst) rfl).trans ?_
  refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
  rfl

/-! ## runND collapse (D2, the runner level) -/

/-- `runND` (CerbND.lean:136) of a computation whose one-layer
    application is active: EXACTLY ONE execution. This is the
    branch-free collapse at the runner level: no NDnd/NDstep node
    exists to fork on, so the exhaustive runner's list is the
    singleton. -/
theorem runND_active {a info err cs st : Type} [Inhabited a] [Inhabited st]
    {m : ndM a info err cs st} {s s' : st} {z : a}
    (h : runOne m s = (NDactive z, s')) :
    CerbND.runND m s = [(nd_status.Active z, ([] : List String), s')] := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  show CerbND.runNDFuel CerbFuel.driverFuel (ND g) s = _
  rw [driverFuel_succ]
  unfold CerbND.runNDFuel
  dsimp only
  rw [h]

/-! ## Thread-map helpers (the single-threaded shape) -/

/-- `update_thread_state` (Core_run.lean:99, via assoc_adjust
    Utils.lean:186) at the singleton thread list. -/
theorem update_thread_state_single (th th' : thread_state) (cs : core_state)
    (hth : cs.thread_states = [(0, (none, th))]) :
    update_thread_state 0 th' cs =
      { cs with thread_states := [(0, (none, th'))] } := by
  unfold update_thread_state
  rw [hth]
  simp [assoc_adjust]

/-- `prepare_exit` (Driver.lean:372) at the singleton parent-less
    thread: park the delivered value, empty the stack. -/
theorem prepare_exit_single (cs : core_state) (th : thread_state) (v : value)
    (hth : cs.thread_states = [(0, (none, th))]) :
    prepare_exit cs v =
      { cs with thread_states :=
          [(0, (none, { th with stack0 := Stack_empty, arena := mk_value_e v }))] } := by
  have hcs : cs = { thread_states := [(0, (none, th))], io := cs.io } := by
    rw [← hth]
  rw [hcs]
  rfl

/-! ## One production loop iteration (D1: the round = the drive-loop
body). `drive_nonmemory_steps_aux2_lemFuel` (Driver.lean:346-351):
{nd_read (step_ctx at the looked-up thread) → find_can_advance →
advance_step | record}. -/

section LoopIteration

variable (fl : Nat) (tds : Fmap sym (CerbLocation.Loc × tag_definition))
  (acc : Fmap thread_id (List core_step2))

/-- Tau round: the engine's Step_tau2 (kind TSK_Misc — the only kind
    the fragment produces) is advanced in place (advance_step,
    Driver.lean:336): thread updated, dr_step_counter ticked, loop
    continues on the same thread list. -/
theorem loop_step_tau {dst : driver_state} {th th' : thread_state} {s : String}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0
      (none, th) = [Step_tau2 s TSK_Misc th']) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [0]) dst =
      runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [0])
        { { dst with dr_step_counter := dst.dr_step_counter + 1 }
            with core_state0 := update_thread_state 0 th' dst.core_state0 } := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active (z := [Step_tau2 s TSK_Misc th'])
    (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) 0
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 th_info) = _
    rw [hth]
    exact hsteps
  · dsimp only [find_can_advance, can_advance]
    rw [if_pos rfl]
    unfold advance_step
    dsimp only
    refine (runOne_bind_active (z := NOWAKEUP)
      (s' := { { dst with dr_step_counter := dst.dr_step_counter + 1 }
          with core_state0 := update_thread_state 0 th' dst.core_state0 }) ?_).trans ?_
    · refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
      refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
      rfl
    · rfl

/-- One loop iteration from a singleton advanceable step whose shipped
    advance is active and wakeup-free (the thread-0 instance of Round.lean's
    `loop_step_of_advance`, stated here for the RETURN round). -/
theorem loop_step_of_advance0 {dst dst' : driver_state} {th : thread_state} {s0 : core_step2}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 (none, th) = [s0])
    (hca : can_advance s0 = true)
    (hadv : runOne (advance_step tds 0 s0) dst = (NDactive NOWAKEUP, dst')) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [0]) dst =
      runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [0]) dst' := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active (z := [s0]) (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) 0
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 th_info) = _
    rw [hth]
    exact hsteps
  · dsimp only [find_can_advance]
    rw [hca, if_pos rfl]
    refine (runOne_bind_active (z := NOWAKEUP) (s' := dst') hadv).trans ?_
    rfl

/-- `advance_step`'s tau arm at ANY task kind (Driver.lean:336): the
    `TSK_Return` kind pushes `ME_function_return` on the trace, the others
    leave it — the trace is existential; thread updated, counter ticked. -/
theorem advance_tau_tsk0 (s : String) (tsk : core_tau_step_kind) (th' : thread_state)
    (dst : driver_state) :
    ∃ tr : List trace_event,
      runOne (advance_step tds 0 (Step_tau2 s tsk th')) dst =
        (NDactive NOWAKEUP,
         { { { dst with trace := tr } with dr_step_counter := dst.dr_step_counter + 1 }
             with core_state0 := update_thread_state 0 th' dst.core_state0 }) := by
  unfold advance_step
  dsimp only
  cases tsk with
  | TSK_Return sym1 mval_opt =>
    refine ⟨ME_function_return sym1 mval_opt :: dst.trace, ?_⟩
    refine (runOne_bind_active (z := ())
      (s' := { dst with trace := ME_function_return sym1 mval_opt :: dst.trace })
      (by rfl)).trans ?_
    refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
    rfl
  | TSK_Ccall sym1 mvals =>
    refine ⟨dst.trace, ?_⟩
    refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
    refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
    rfl
  | TSK_Misc =>
    refine ⟨dst.trace, ?_⟩
    refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
    refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
    rfl

/-- Tau round at ANY task kind (calls arc C2 — the RETURN round's
    `Step_tau2 "end of procedure" tsk`, whose `tsk` is `TSK_Return` when
    `file.funinfo` names the procedure): as `loop_step_tau`, plus the
    trace push `advance_step` makes for `TSK_Return` (Driver.lean:336;
    existential — the trace is driver bookkeeping). -/
theorem loop_step_tau_tsk {dst : driver_state} {th th' : thread_state} {s : String}
    {tsk : core_tau_step_kind}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0
      (none, th) = [Step_tau2 s tsk th']) :
    ∃ tr : List trace_event,
      runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [0]) dst =
        runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [0])
          { { { dst with trace := tr } with dr_step_counter := dst.dr_step_counter + 1 }
              with core_state0 := update_thread_state 0 th' dst.core_state0 } := by
  obtain ⟨tr, hadv⟩ := advance_tau_tsk0 tds s tsk th' dst
  exact ⟨tr, loop_step_of_advance0 fl tds acc hth hsteps rfl hadv⟩

/-- Done round (two loop iterations): PROGRAM-DONE is not advanceable
    (can_advance, Driver.lean:310), so the singleton is recorded in
    the step map and the drained list returns it — the state
    untouched. -/
theorem loop_step_done {dst : driver_state} {th : thread_state} {v : value}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0
      (none, th) = [Step_done2 v]) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ (Nat.succ fl))
        tds acc [0]) dst =
      (NDactive (fmapAddBy defaultCompare 0 [Step_done2 v] acc), dst) := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active (z := [Step_done2 v]) (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) 0
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 th_info) = _
    rw [hth]
    exact hsteps
  · dsimp only [find_can_advance, can_advance]
    conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
    rfl

/-- Action round: the request is drawn from the request monad
    (verbatim run state), the action id is drawn (aid_supply ticked —
    perform_action_request2, Driver.lean:277-285), and the request is
    discharged sequentially. The discharge outcome is a hypothesis
    (`hars`) so the store/load/create instances below plug in. -/
theorem loop_step_action {dst dst' : driver_state} {th : thread_state}
    {s : String} {loc : CerbLocation.Loc}
    {req : action_request2 thread_state}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0
      (none, th) = [Step_action_request2 s loc 0 false
        (stExceptUndef_return req)])
    (hars : runOne (action_request_sequential2 tds loc 0
        dst.core_run_state0.aid_supply req)
        { dst with core_run_state0 :=
            { dst.core_run_state0 with aid_supply :=
                dst.core_run_state0.aid_supply + 1 } } = (NDactive (), dst')) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [0]) dst =
      runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [0]) dst' := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active
    (z := [Step_action_request2 s loc 0 false (stExceptUndef_return req)])
    (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) 0
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 th_info) = _
    rw [hth]
    exact hsteps
  · dsimp only [find_can_advance, can_advance]
    rw [if_pos (show (!false) = true from rfl)]
    unfold advance_step
    dsimp only
    refine (runOne_bind_active (z := NOWAKEUP) (s' := dst') ?_).trans ?_
    · refine (runOne_bind_active (z := ()) (s' := dst') ?_).trans (by rfl)
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
    · rfl

end LoopIteration

/-! ## The sequential request discharges (Driver.lean:273), active
paths. The killed paths are never needed: the production-entry
theorem's termination hypothesis routes every reachable discharge
through the active arm (a killed drive contradicts `.done`), so —
like slice B's storeM-shape fact (D15) — the killed-discharge
equations are deliberately unproved-as-unneeded. -/

/-- StoreRequest2 discharge, active: storeM writes, prefixOfPointer is
    `memReturn none` (CerbMem.lean:2064 — trace-only), the trace gets
    its ME_store event, the thread its continuation. No
    dr_step_counter tick on the action path (Driver.lean:273). -/
theorem ars_store_active {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {loc loc₀ : CerbLocation.Loc} {mo : memory_order}
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue}
    {k : Nat → CerbMem.Footprint → thread_state} {tid aid : Nat}
    {dst : driver_state} {fp : CerbMem.Footprint} {σ' : Mem}
    (happ : applyMemM (CerbMem.storeM tds loc₀ ty lk pv mv) dst.layout_state =
      some (fp, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (StoreRequest2 mo ty lk pv mv k)) dst =
      (NDactive (), { dst with
        layout_state := σ',
        trace := ME_store loc none ty lk pv mv :: dst.trace,
        core_state0 := update_thread_state tid (k aid fp) dst.core_state0 }) := by
  replace happ := (storeM_loc_irrel loc₀ loc).trans happ
  unfold action_request_sequential2
  dsimp only
  refine (runOne_bind_active (z := fp) (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (runOne_of_applyMemM happ))).trans ?_
  refine (runOne_bind_active (z := (none : Option String))
    (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (by rfl))).trans ?_
  rfl

/-- LoadRequest2 discharge, active. -/
theorem ars_load_active {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {loc loc₀ : CerbLocation.Loc} {mo : memory_order}
    {ty : ctype} {pv : CerbMem.PointerValue}
    {k : Nat → CerbMem.Footprint → CerbMem.MemValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {fp : CerbMem.Footprint}
    {mval : CerbMem.MemValue} {σ' : Mem}
    (happ : applyMemM (CerbMem.loadM tds loc₀ ty pv) dst.layout_state =
      some ((fp, mval), σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (LoadRequest2 mo ty pv k)) dst =
      (NDactive (), { dst with
        layout_state := σ',
        trace := ME_load loc none ty pv mval :: dst.trace,
        core_state0 := update_thread_state tid (k aid fp mval) dst.core_state0 }) := by
  replace happ := (loadM_loc_irrel loc₀ loc).trans happ
  unfold action_request_sequential2
  dsimp only
  refine (runOne_bind_active (z := (fp, mval))
    (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (runOne_of_applyMemM happ))).trans ?_
  dsimp only
  refine (runOne_bind_active (z := (none : Option String))
    (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (by rfl))).trans ?_
  rfl

/-- CreateRequest2 discharge, active. allocateObject discards the
    thread id (CerbMem.lean:1470), so the hypothesis is stated at 0
    and bridges to the driver's `tid1` definitionally. -/
theorem ars_create_active {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {loc : CerbLocation.Loc} {pref : prefix0}
    {align : CerbMem.IntegerValue} {ty : ctype} {reqAddr : Option Int}
    {initOpt : Option CerbMem.MemValue}
    {k : Nat → CerbMem.PointerValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {pv : CerbMem.PointerValue} {σ' : Mem}
    (happ : applyMemM (CerbMem.allocateObject tds 0 pref align ty reqAddr initOpt)
        dst.layout_state = some (pv, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (CreateRequest2 pref align ty reqAddr initOpt k)) dst =
      (NDactive (), { dst with
        layout_state := σ',
        trace := ME_allocate_object tid pref align ty initOpt pv :: dst.trace,
        core_state0 := update_thread_state tid (k aid pv) dst.core_state0 }) := by
  unfold action_request_sequential2
  dsimp only
  refine (runOne_bind_active (z := pv) (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (runOne_of_applyMemM happ))).trans ?_
  rfl

/-- KillRequest2 discharge, active (kill/free arc K2; Driver.lean:273,
    verbatim modulo whitespace: `nd_bind (liftMem (CerbMem.killM loc1
    is_dynamic1 ptr_val)) (fun _ => nd_update (fun dr_st => { { dr_st
    with trace := ME_kill loc1 is_dynamic1 ptr_val :: dr_st.trace } with
    core_state0 := update_thread_state tid1 (mk_th_st' aid1)
    dr_st.core_state0 }))`): `killM` runs on the layout state at the
    request's location (`killM_loc_irrel` transports the mirror's
    premise), the trace gets its `ME_kill` event, the thread its
    continuation at the drawn aid. -/
theorem ars_kill_active {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc loc₀ : CerbLocation.Loc} {isDyn : Bool} {pv : CerbMem.PointerValue}
    {k : Nat → thread_state} {tid aid : Nat} {dst : driver_state} {σ' : Mem}
    (happ : applyMemM (CerbMem.killM loc₀ isDyn pv) dst.layout_state = some ((), σ')) :
    runOne (action_request_sequential2 tds loc tid aid (KillRequest2 isDyn pv k)) dst =
      (NDactive (), { dst with
        layout_state := σ',
        trace := ME_kill loc isDyn pv :: dst.trace,
        core_state0 := update_thread_state tid (k aid) dst.core_state0 }) := by
  replace happ := (killM_loc_irrel loc₀ loc).trans happ
  unfold action_request_sequential2
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (runOne_of_applyMemM happ))).trans ?_
  rfl

/-- AllocRequest2 discharge, active (kill/free arc K3; Driver.lean:273,
    verbatim modulo whitespace: `nd_bind (liftMem (CerbMem.allocateRegion
    tid1 pref align_ival size_ival)) (fun ptrval => nd_update (fun dr_st
    => { { dr_st with trace := ME_allocate_region tid1 pref align_ival
    size_ival ptrval :: dr_st.trace } with core_state0 :=
    update_thread_state tid1 (mk_th_st' aid1 ptrval) dr_st.core_state0
    }))`): `allocateRegion` discards the thread id (CerbMem.lean:1533),
    so the hypothesis is stated at 0 and bridges to the driver's `tid1`
    definitionally; the trace gets its `ME_allocate_region` event, the
    thread its continuation at the drawn aid and the minted pointer. -/
theorem ars_alloc_active {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {loc : CerbLocation.Loc} {pref : prefix0}
    {align size : CerbMem.IntegerValue}
    {k : Nat → CerbMem.PointerValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {pv : CerbMem.PointerValue} {σ' : Mem}
    (happ : applyMemM (CerbMem.allocateRegion 0 pref align size)
        dst.layout_state = some (pv, σ')) :
    runOne (action_request_sequential2 tds loc tid aid
        (AllocRequest2 pref align size k)) dst =
      (NDactive (), { dst with
        layout_state := σ',
        trace := ME_allocate_region tid pref align size pv :: dst.trace,
        core_state0 := update_thread_state tid (k aid pv) dst.core_state0 }) := by
  unfold action_request_sequential2
  dsimp only
  refine (runOne_bind_active (z := pv) (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (runOne_of_applyMemM happ))).trans ?_
  rfl

/-! ## D3: the finalize/hack readout -/

/-- `Driver.hack` (Driver.lean:390-395) on an already-irreducible
    value pexpr returns the value: step_eval_pexpr's PEval arm
    (Core_eval.lean:142) is the identity and `valueFromPexpr`
    (Core_aux.lean:472) reads it off — one fuel layer, no recursion,
    context-independent (no argument other than the pexpr is read on
    this path). -/
theorem hack_value (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (ext : Fmap sym sym) (env : List (Fmap sym value)) (σ : Mem)
    (f : file core_run_annotation) (assoc : Fmap sym object_value) (v : value) :
    hack tds ext env σ f assoc (Pexpr [] () (PEval v)) = v := rfl

/-- `finalize` (Driver.lean:423) at the PROGRAM-DONE parked state:
    the single thread's arena is `mk_value_e v` (prepare_exit), which
    `to_pure` (Core_aux.lean:570, Epure arm) strips and `hack` reads
    back — the readout is exactly `v`, with the io streams folded out
    of the untouched core_state io. -/
theorem finalize_done (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (s : String) (dst : driver_state) (th : thread_state) (v : value)
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (harena : th.arena = mk_value_e v) :
    finalize tds s dst =
      { dres_blocked := dst.blocked,
        dres_concurrency_state := dst.concurrency_state,
        dres_driver_steps := dst.dr_step_counter,
        dres_core_value := v,
        dres_stdout := List.foldr String.append ""
          (toList dst.core_state0.io.stdout),
        dres_stderr := List.foldr String.append ""
          (toList dst.core_state0.io.stderr) } := by
  unfold finalize
  rw [hth]
  dsimp only
  rw [harena]
  rfl

/-! ## The driver2 round (D1's outer layer): at the PROGRAM-DONE step
map, one driver2 unfold routes through process_core_step2's Step_done2
arm (prepare_exit) and STOPS (no driver21 recursion — Driver.lean:377).
Both scheduler branches (the opaque execution-mode read,
CerbGlobal.current_execution_mode — an `opaque` constant, so the round
equation is proved by CASES on the mode test) take the same
singleton-pick path. -/

/-- process_core_step2 at Step_done2. -/
theorem process_done (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (cont : Bool → ndM Unit step_kind driver_error
      (mem_constraint CerbMem.IntegerValue) driver_state)
    (v : value) (dst : driver_state) (th : thread_state)
    (hth : dst.core_state0.thread_states = [(0, (none, th))]) :
    runOne (process_core_step2 tds false cont (Step_done2 v)) dst =
      (NDactive (), { dst with core_state0 :=
        { dst.core_state0 with thread_states :=
            [(0, (none, { th with stack0 := Stack_empty, arena := mk_value_e v }))] } }) := by
  unfold process_core_step2
  dsimp only
  refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
  rw [runOne_update]
  rw [prepare_exit_single dst.core_state0 th v hth]

/-! ## The outer driver2 round: PROGRAM-DONE routed through
process_core_step2/prepare_exit. The execution-mode read
(CerbGlobal.current_execution_mode — an `opaque` constant) selects
between the random-mode `bindExhaustive` branch and the exhaustive
branch (Driver.lean:384); on a SINGLETON non-blocked step list both
reduce to the same `pick`-the-one-step path, so the round equation is
proved by cases on the opaque mode test. -/

theorem driver2_done (fl : Nat)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (dst dstF : driver_state) (th thF : thread_state) (v : value)
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hloop : runOne (drive_nonmemory_steps_aux2_lemFuel CerbFuel.driverFuel tds
        fmapEmpty [0]) dst =
      (NDactive (fmapAddBy defaultCompare 0 [Step_done2 v] fmapEmpty), dstF))
    (hthF : dstF.core_state0.thread_states = [(0, (none, thF))]) :
    runOne (driver2_lemFuel (Nat.succ fl) tds false) dst =
      (NDactive (), { dstF with core_state0 :=
        { dstF.core_state0 with thread_states :=
            [(0, (none, { thF with stack0 := Stack_empty, arena := mk_value_e v }))] } }) := by
  conv => lhs; unfold driver2_lemFuel
  refine (runOne_bind_active (z := [((0 : Nat), some (Step_done2 v))])
    (s' := dstF) ?_).trans ?_
  · -- new_drive_core_threads: the whole fragment run happens inside
    -- the per-thread loop; the returned map is the PROGRAM-DONE
    -- singleton, picked deterministically.
    unfold new_drive_core_threads
    refine (runOne_bind_active (z := dst) (by rfl)).trans ?_
    dsimp only
    rw [hth]
    dsimp only [List.map]
    refine (runOne_bind_active
      (z := fmapAddBy defaultCompare 0 [Step_done2 v] fmapEmpty)
      (s' := dstF) hloop).trans ?_
    rw [show fmapElements (fmapAddBy defaultCompare (0 : Nat) [Step_done2 v]
      fmapEmpty) = [((0 : Nat), [Step_done2 v])] from rfl]
    unfold nd_mapM
    dsimp only [List.map, List.foldr]
    refine (runOne_bind_active (z := ((0 : Nat), some (Step_done2 v)))
      (s' := dstF) ?_).trans ?_
    · refine (runOne_bind_active (z := Step_done2 v) (s' := dstF)
        (by rfl)).trans (by rfl)
    · refine (runOne_bind_active
        (z := ([] : List (Nat × Option core_step2))) (by rfl)).trans (by rfl)
  · refine (runOne_bind_active (z := dstF) (by rfl)).trans ?_
    dsimp only
    cases hmode : maybeEqualBy (fun x y => x == y)
        (CerbGlobal.current_execution_mode ())
        (some CerbGlobal.ExecutionMode.random) with
    | true =>
      rw [if_pos rfl]
      unfold bindExhaustive
      refine (runOne_bind_active (z := ((0 : Nat), some (Step_done2 v)))
        (s' := dstF) (by rfl)).trans ?_
      dsimp only
      exact process_done tds _ v dstF thF hthF
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h)]
      refine (runOne_bind_active (z := ()) (s' := dstF) (by rfl)).trans ?_
      refine (runOne_bind_active (z := ((0 : Nat), some (Step_done2 v)))
        (s' := dstF) (by rfl)).trans ?_
      dsimp only
      exact process_done tds _ v dstF thF hthF

/-! ## Phase 5 — THE LOOP PRODUCTION COLLAPSE, part 1: the
with-runstate and memop rounds (the two step kinds the loop fragment
adds to the driver's round algebra), plus the raw with-runstate
singletons.

The straight-line collapse above needed only tau/action/done rounds;
the loop fragment's remaining constructs reach the driver as
- `Step_with_runstate2` (Eif, Erun, PURE, ACTION_EVAL, memop-EVAL:
  one_step0/step_ctx, Core_reduction.lean:353/484), advanced by
  `advance_step`'s with-runstate arm (Driver.lean:336) through
  `liftCore_run` (Driver.lean:245) — which WRITES THE MONAD'S
  RETURNED RUN STATE BACK into the driver state; and
- `Step_memop_request2` (PtrEq at value operands), advanced through
  `perform_memop_request2` (Driver.lean:288).

The raw singleton lemmas below therefore re-package the composite
`stepDischarge_*` certifications (Soundness.lean) WITH THE
`Step_with_runstate2` PAYLOAD EXPLICIT and the monad's VERBATIM
run-state return proved (∀ rs — the evaluator tower is `runEU`-lifted
and Erun's `labeled` read is `state_except_read`, both state-verbatim
by construction): the verbatim return is what keeps the driver's
run-state `labeled` fiber — and with it every later jump — intact
across a production round. -/

/-- `liftCore_run` (Driver.lean:245) of a with-runstate monad that
    returns the current run state verbatim: the write-back is the
    identity and the successor is delivered — one active layer. -/
theorem runOne_liftCore_run_of_eq {a : Type}
    {m : core_run_state → exceptM ((t0 a) × core_run_state) core_run_cause}
    {dst : driver_state} {z : a}
    (hm : m dst.core_run_state0 = Result (Defined z, dst.core_run_state0)) :
    runOne (liftCore_run m) dst = (NDactive z, dst) := by
  unfold liftCore_run
  refine (runOne_bind_active (z := dst) (by rfl)).trans ?_
  rw [show stExceptUndef_run m dst.core_run_state0 =
    Result (Defined z, dst.core_run_state0) from hm]
  refine (runOne_bind_active (z := ())
    (s' := { dst with core_run_state0 := dst.core_run_state0 })
    (by rfl)).trans ?_
  rfl

section LoopIterationJ

variable (fl : Nat) (tds : Fmap sym (CerbLocation.Loc × tag_definition))
  (acc : Fmap thread_id (List core_step2))

/-- With-runstate round, EVAL kind (`RSK_eval` — Erun / PURE /
    ACTION_EVAL / memop-EVAL): the step is advanced in place via the
    liftCore_run protocol; the run state is written back VERBATIM
    (hypothesis `hm`, discharged by the raw singleton lemmas below),
    dr_step_counter ticked, loop continues. The `RSK_eval` kind makes
    `advance_step`'s TSK_Return trace arm a no-op. -/
theorem loop_step_withrs_eval {dst : driver_state} {th th' : thread_state}
    {s : String} {m : core_runM thread_state}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0
      (none, th) = [Step_with_runstate2 (RSK_eval s) m])
    (hm : m dst.core_run_state0 = Result (Defined th', dst.core_run_state0)) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [0]) dst =
      runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [0])
        { { dst with dr_step_counter := dst.dr_step_counter + 1 }
            with core_state0 := update_thread_state 0 th' dst.core_state0 } := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active (z := [Step_with_runstate2 (RSK_eval s) m])
    (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) 0
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 th_info) = _
    rw [hth]
    exact hsteps
  · dsimp only [find_can_advance, can_advance]
    rw [if_pos rfl]
    unfold advance_step
    dsimp only
    refine (runOne_bind_active (z := NOWAKEUP)
      (s' := { { dst with dr_step_counter := dst.dr_step_counter + 1 }
          with core_state0 := update_thread_state 0 th' dst.core_state0 }) ?_).trans ?_
    · refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
      refine (runOne_bind_active (z := th') (s' := dst)
        (runOne_liftCore_run_of_eq hm)).trans ?_
      refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
      rfl
    · rfl

/-- With-runstate round, TAU kind (`RSK_tau _ TSK_Misc` — Eif):
    identical round shape (the TSK_Misc kind skips the trace arm). -/
theorem loop_step_withrs_tau {dst : driver_state} {th th' : thread_state}
    {s : String} {m : core_runM thread_state}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0
      (none, th) = [Step_with_runstate2 (RSK_tau s TSK_Misc) m])
    (hm : m dst.core_run_state0 = Result (Defined th', dst.core_run_state0)) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [0]) dst =
      runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [0])
        { { dst with dr_step_counter := dst.dr_step_counter + 1 }
            with core_state0 := update_thread_state 0 th' dst.core_state0 } := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active (z := [Step_with_runstate2 (RSK_tau s TSK_Misc) m])
    (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) 0
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 th_info) = _
    rw [hth]
    exact hsteps
  · dsimp only [find_can_advance, can_advance]
    rw [if_pos rfl]
    unfold advance_step
    dsimp only
    refine (runOne_bind_active (z := NOWAKEUP)
      (s' := { { dst with dr_step_counter := dst.dr_step_counter + 1 }
          with core_state0 := update_thread_state 0 th' dst.core_state0 }) ?_).trans ?_
    · refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
      refine (runOne_bind_active (z := th') (s' := dst)
        (runOne_liftCore_run_of_eq hm)).trans ?_
      refine (runOne_bind_active (z := ()) (by rfl)).trans ?_
      rfl
    · rfl

/-- Memop round: the request is discharged sequentially
    (perform_memop_request2 — hypothesis `hars` so the PtrEq instance
    below plugs in); no aid draw, no counter tick (Driver.lean:336's
    memop arm). -/
theorem loop_step_memop {dst dst' : driver_state} {th : thread_state}
    {loc : CerbLocation.Loc} {mop : memop} {cvals : List value}
    {k : value → thread_state}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0
      (none, th) = [Step_memop_request2 loc mop cvals 0 false k])
    (hars : runOne (perform_memop_request2 tds loc mop cvals 0 k) dst =
      (NDactive (), dst')) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl) tds acc [0]) dst =
      runOne (drive_nonmemory_steps_aux2_lemFuel fl tds acc [0]) dst' := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active
    (z := [Step_memop_request2 loc mop cvals 0 false k])
    (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) 0
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 th_info) = _
    rw [hth]
    exact hsteps
  · dsimp only [find_can_advance, can_advance]
    rw [if_pos (show (!false) = true from rfl)]
    unfold advance_step
    dsimp only
    refine (runOne_bind_active (z := NOWAKEUP) (s' := dst') ?_).trans ?_
    · refine (runOne_bind_active (z := ()) (s' := dst') ?_).trans (by rfl)
      rw [if_neg (fun h => Bool.noConfusion h)]
      exact hars
    · rfl

end LoopIterationJ

/-- The sequential PtrEq memop discharge, active
    (perform_memop_request2's PtrEq arm, Driver.lean:288): liftMem
    eqPtrval, the continuation installed via update_core_state; no
    trace event. -/
theorem ars_memop_active
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    {loc : CerbLocation.Loc} {tid : Nat}
    {pv1 pv2 : CerbMem.PointerValue} {k : value → thread_state}
    {dst : driver_state} {b : Bool} {σ' : Mem}
    (happ : applyMemM (CerbMem.eqPtrval loc pv1 pv2) dst.layout_state =
      some (b, σ')) :
    runOne (perform_memop_request2 tds loc PtrEq
        [Vobject (OVpointer pv1), Vobject (OVpointer pv2)] tid k) dst =
      (NDactive (), { dst with
        layout_state := σ',
        core_state0 := update_thread_state tid (k (if b then Vtrue else Vfalse))
          dst.core_state0 }) := by
  unfold perform_memop_request2
  dsimp only
  refine (runOne_bind_active (z := k (if b then Vtrue else Vfalse))
    (s' := { dst with layout_state := σ' }) ?_).trans ?_
  · refine (runOne_bind_active (z := b) (s' := { dst with layout_state := σ' })
      ?_).trans (by rfl)
    refine (runOne_bind_active (z := ()) (s' := dst) (by rfl)).trans ?_
    exact runOne_liftMem_active (runOne_of_applyMemM happ)
  · rw [runOne_update]
    rfl

/-! ### The raw with-runstate singletons (per construct; the
composite `stepDischarge_*` scripts re-run with the payload kept). -/

/-- Eif (TRUE), raw: one `RSK_tau _ TSK_Misc` with-runstate step whose
    monad returns the true-branch successor and the run state
    VERBATIM, ∀ rs. -/
theorem step_ctx_if_true_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hg : evalPexpr tds ext th.env g = some Vtrue) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_tau s TSK_Misc) m] ∧
      ∀ rs, m rs =
        Result (Defined { locUpdTh an th with arena := apply_ctx ctx e2 }, rs) := by
  have hget : get_ctx th.arena = [(ctx, ifRedex an g e2 e3)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold ifRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an (Eif g e2 e3)) = false
       from rfl]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hg hdg σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     try rfl)

/-- Eif (FALSE), raw — symmetric. -/
theorem step_ctx_if_false_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex an g e2 e3))
    (hsz : esize e ≤ lemDefaultFuel)
    (hdg : peDepth g ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hg : evalPexpr tds ext th.env g = some Vfalse) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_tau s TSK_Misc) m] ∧
      ∀ rs, m rs =
        Result (Defined { locUpdTh an th with arena := apply_ctx ctx e3 }, rs) := by
  have hget : get_ctx th.arena = [(ctx, ifRedex an g e2 e3)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold ifRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an (Eif g e2 e3)) = false
       from rfl]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hg hdg σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     try rfl)

/-- PURE at a symbol, raw: one `RSK_eval` step, run state verbatim. -/
theorem step_ctx_pure_sym_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym} {v : value}
    (hd : Decomp e ctx (pureRedex an (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexpr tds ext th.env (Pexpr pb () (PEsym x)) = some v) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with arena :=
        (apply_ctx ctx (Expr an (Epure (Pexpr [] () (PEval v))))) }, rs) := by
  have hget : get_ctx th.arena =
      [(ctx, pureRedex an (Pexpr pb () (PEsym x)))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold pureRedex
  cases ctx <;>
    (dsimp only [one_step0, is_irreducible, valueFromPexpr]
     simp only [Bool.false_eq_true, if_false]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hv (peDepth_sym_le pb x) σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- THE JUMP, raw: one `RSK_eval` step whose monad reads the run
    state's `labeled` fiber (READ-ONLY — `state_except_read`) and
    returns the rebound continuation with the run state VERBATIM, for
    every run state carrying the tie. -/
theorem step_ctx_run_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex an ra l pes))
    (hsz : esize e ≤ lemDefaultFuel)
    {Q : LabelMap} {params : List (sym × core_base_type)} {cont : CoreExpr}
    {vs : List value}
    (hl : lookupLabel Q l = some (params, cont))
    (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (p : sym) (th : thread_state)
    (harena : th.arena = e)
    (hproc : th.current_proc_opt = some p)
    (hvs : evalPexprs tds ext th.env pes = some vs) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, LabeledAt rs (resolveExtern ext p) Q →
        m rs = Result (Defined { locUpdTh an th with
          env := (bindArgs params vs th.env), arena := cont }, rs) := by
  have hget : get_ctx th.arena = [(ctx, runRedex an ra l pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  have hl' : (fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
      Lem_Basic_classes.ordCompare sym1 sym2) l Q) = some (params, cont) := hl
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold runRedex
  cases ctx <;> (loc_split an) <;>
    (try dsimp only
     rw [hproc]
     refine ⟨_, _, rfl, fun rs hQ => ?_⟩
     replace hQ : (fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
       Lem_Basic_classes.ordCompare sym1 sym2) (resolveExtern ext p)
       rs.labeled) = some Q := hQ
     rw [stExceptUndef_bind_apply, runSE_read_apply]
     dsimp only []
     cases hres : fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
         Lem_Basic_classes.ordCompare sym1 sym2) p ext with
     | none =>
       rw [show resolveExtern ext p = p by
         unfold resolveExtern; rw [hres]] at hQ
       dsimp only []
       rw [hQ, bind0_some, hl']
       dsimp only []
       rw [stExceptUndef_bind_apply,
         foldM_args_bridge _ (fun _ _ _ _ _ => rfl) params pes vs th.env rs
           hvs hdep]
       dsimp only []
       rw [stExceptUndef_return_apply]
     | some y =>
       rw [show resolveExtern ext p = y by
         unfold resolveExtern; rw [hres]] at hQ
       dsimp only []
       rw [hQ, bind0_some, hl']
       dsimp only []
       rw [stExceptUndef_bind_apply,
         foldM_args_bridge _ (fun _ _ _ _ _ => rfl) params pes vs th.env rs
           hvs hdep]
       dsimp only []
       rw [stExceptUndef_return_apply])

/-- Load ACTION_EVAL, raw: one `RSK_eval` step rebuilding the
    canonical load redex, run state verbatim. -/
theorem step_ctx_load_eval_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (loadOpRedex an loc ann ty pe2 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv2 : valueFromPexpr pe2 = none)
    (hp2 : PePure pe2)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv2 : evalPexpr tds ext th.env pe2 = some (Vobject (OVpointer pv))) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (loadRedex an loc ann ty pv mo) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, loadOpRedex an loc ann ty pe2 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold loadOpRedex
  cases ctx <;>
    (dsimp only [step_action]
     rw [act_valueFromPexpr_none hp2 hnv2]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
       full_eval_bridge hv2 hd2 σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Kill ACTION_EVAL, raw (kill/free arc K2): one `RSK_eval` step
    rebuilding the canonical kill redex, run state verbatim. -/
theorem step_ctx_kill_eval_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
    {pe : generic_pexpr Unit sym} {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (killOpRedex an loc ann kind pe))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexpr pe = none)
    (hp : PePure pe)
    (hdp : peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexpr tds ext th.env pe = some (Vobject (OVpointer pv))) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (killRedex an loc ann kind pv) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, killOpRedex an loc ann kind pe)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold killOpRedex
  cases ctx <;>
    (dsimp only [step_action]
     rw [act_valueFromPexpr_none hp hnv]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hv hdp σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Store ACTION_EVAL, raw: one `RSK_eval` step rebuilding the
    canonical store redex, run state verbatim. -/
theorem step_ctx_store_eval_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {pv : CerbMem.PointerValue} {cv : value}
    (hd : Decomp e ctx (storeOpRedex an loc ann ty pe2 pe3 mo))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hp2 : PePure pe2) (hp3 : PePure pe3)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (hd3 : peDepth pe3 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv2 : evalPexpr tds ext th.env pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr tds ext th.env pe3 = some cv) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (storeRedex an loc ann false ty pv cv mo) },
        rs) := by
  have hget : get_ctx th.arena =
      [(ctx, storeOpRedex an loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  rw [valueFromPexprs_pair] at hnv
  rcases act_valueFromPexpr_cases hp2 with ⟨hn2, ha2⟩ | ⟨a2, v2', rfl⟩ <;>
  cases hp3
  all_goals try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [step_action]
       try rw [ha2]
       dsimp only [act_valueFromPexpr, valueFromPexpr]
       refine ⟨_, _, rfl, fun rs => ?_⟩
       rw [full_eval_bridge (v := Vctype ty) (evalPexpr_val _ _ _ _ _) (peDepth_val_le _ _) σ file,
         full_eval_bridge hv2 hd2 σ file,
         full_eval_bridge hv3 hd3 σ file]
       dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
         return1, except_return]
       rfl)

/-- Alloc ACTION_EVAL, raw (kill/free arc K3): one `RSK_eval` step
    rebuilding the canonical alloc redex, run state verbatim. -/
theorem step_ctx_alloc_eval_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {align size : CerbMem.IntegerValue}
    (hd : Decomp e ctx (allocOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv1 : evalPexpr tds ext th.env pe1 = some (Vobject (OVinteger align)))
    (hv2 : evalPexpr tds ext th.env pe2 = some (Vobject (OVinteger size))) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (allocRedex an loc ann align size pref) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, allocOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold allocOpRedex
  rw [valueFromPexprs_pair] at hnv
  rcases act_valueFromPexpr_cases hp1 with ⟨hn1, ha1⟩ | ⟨a1, v1', rfl⟩ <;>
  rcases act_valueFromPexpr_cases hp2 with ⟨hn2, ha2⟩ | ⟨a2, v2', rfl⟩
  all_goals try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv1))
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [step_action]
       try rw [ha1]
       try rw [ha2]
       try dsimp only [act_valueFromPexpr, valueFromPexpr]
       refine ⟨_, _, rfl, fun rs => ?_⟩
       rw [full_eval_bridge hv1 hd1 σ file, full_eval_bridge hv2 hd2 σ file]
       dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
         return1, except_return]
       rfl)


/-- E1: Create ACTION_EVAL, raw: one `RSK_eval` step rebuilding the
    canonical create redex (the emitted `create(Ivalignof(ty), ty)`
    evaluates its alignment), run state verbatim. -/
theorem step_ctx_create_eval_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation}
    {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
    {align : CerbMem.IntegerValue} {ty : ctype}
    (hd : Decomp e ctx (createOpRedex an loc ann pe1 pe2 pref))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hp1 : PePure pe1) (hp2 : PePure pe2)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv1 : evalPexpr tds ext th.env pe1 = some (Vobject (OVinteger align)))
    (hv2 : evalPexpr tds ext th.env pe2 = some (Vctype ty)) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (createRedex an loc ann align ty pref) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, createOpRedex an loc ann pe1 pe2 pref)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold createOpRedex
  rw [valueFromPexprs_pair] at hnv
  rcases act_valueFromPexpr_cases hp1 with ⟨hn1, ha1⟩ | ⟨a1, v1', rfl⟩ <;>
  rcases act_valueFromPexpr_cases hp2 with ⟨hn2, ha2⟩ | ⟨a2, v2', rfl⟩
  all_goals try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv1))
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [step_action]
       try rw [ha1]
       try rw [ha2]
       try dsimp only [act_valueFromPexpr, valueFromPexpr]
       refine ⟨_, _, rfl, fun rs => ?_⟩
       rw [full_eval_bridge hv1 hd1 σ file, full_eval_bridge hv2 hd2 σ file]
       dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
         return1, except_return]
       rfl)

/-- Esave PARAMETER EVALUATION, raw: one `RSK_eval` step rebuilding the
    Esave node with its evaluated initializers, run state verbatim
    (the driver-lane twin of `stepDischarge_save_eval`). -/
theorem step_ctx_save_eval_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {cvals : List value}
    (hd : Decomp e ctx (saveRedex an sb ps body))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexprs tds ext th.env (saveParamPexprs ps) = some cvals) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (saveRedex an sb (saveParamsWithValues ps cvals) body) },
        rs) := by
  have hget : get_ctx th.arena = [(ctx, saveRedex an sb ps body)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  have hnv' : valueFromPexprs
      (List.map (fun p => match p with | (_, (_, z)) => z) ps) = none := by
    rw [show (List.map (fun (p : sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
        => match p with | (_, (_, z)) => z) ps) = saveParamPexprs ps from rfl]
    exact hnv
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold saveRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an (Esave sb ps body)) = false from rfl]
     rw [hnv']
     simp only [Bool.false_eq_true, if_false]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       mapM_save_bridge (tds := tds) (σ := σ) (file := file)
         (fun pe => stExceptUndef_bind
           (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
           (fun x => match x with
             | Sum.inl pe' => stExceptUndef_return pe'
             | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)))
         (fun _ _ => rfl) _ ?_ ps hv hdep rs] <;>
       first
         | (intro p rs'
            rfl)
         | (loc_split an <;> rfl))

/-- Memop-operand EVAL, raw: one `RSK_eval` step rebuilding the
    value-operand memop redex, run state verbatim. -/
theorem step_ctx_memop_eval_ws {an : List _root_.annot} {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hd : Decomp e ctx (memopRedex an mop [pe1, pe2]))
    (hsz : esize e ≤ lemDefaultFuel)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hd1 : peDepth pe1 ≤ lemDefaultFuel)
    (hd2 : peDepth pe2 ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv1 : evalPexpr tds ext th.env pe1 = some v1)
    (hv2 : evalPexpr tds ext th.env pe2 = some v2) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { locUpdTh an th with
        arena := apply_ctx ctx (Expr an (Ememop mop
          [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)])) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, memopRedex an mop [pe1, pe2])] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold memopRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr an (Ememop mop [pe1, pe2]))
       = false from rfl]
     rw [hnv]
     simp only [Bool.false_eq_true, if_false]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       mapM_eval1_bridge (tds := tds) (σ := σ) (file := file)
         _ ?_ hv1 hd1 hv2 hd2 rs] <;>
       first
         | (intro pe rs'
            rfl)
         | (loc_split an <;> rfl))

/-! ## THE DRIVER STEP-MATCH (Phase 5): wherever the mirror steps at a
cone configuration, the production driver's per-thread round advances
the singleton thread to EXACTLY the mirror's successor — the
driver-level analog of `engine_step_matchU`, one case per redex root,
each discharged by the raw singleton lemma + the matching round
equation above. The mirror step is taken at ANY context `M₀` agreeing
with the driver's on the three projections `Step` reads (tagDefs,
extern — both empty on the production path — and the label map,
tied to the DRIVER'S CURRENT run state by `hQd`); the returned run
state either is untouched (taus, with-runstate verbatim, memop) or
gets its aid ticked (actions) — `labeled` is preserved either way,
which is what keeps the next round's jump certifiable.

E1: the driver thread's `current_loc` is TIED to the control's `curLoc`
(`hcl`), and the successor thread carries the SUCCESSOR control's —
the general arm's location write (`locUpdTh`, Core_reduction.lean:484)
is the mirror's `Ctl.upd` (`locUpdTh_ctl`). The control-preserving
rounds are those keeping the call stack (`hκ`). -/
theorem loop_step_frag_same' {M₀ : MachineCtx} {ctl ctl' : Ctl}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {th₀ : thread_state} (hcl : th₀.current_loc = ctl.curLoc)
    (fl : Nat) (acc : Fmap thread_id (List core_step2))
    {dst : driver_state} {e e' : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ρ' : EnvStack} {σ' : Mem}
    (hth : dst.core_state0.thread_states =
      [(0, (none, { th₀ with arena := e, env := ev0 :: evs }))])
    (hext : dst.core_extern = fmapEmpty)
    (hjmp : ∀ l params cont, lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont) →
      ∃ p, th₀.current_proc_opt = some p ∧
        LabeledAt dst.core_run_state0 p (M₀.labelsAt ctl.proc))
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M₀ (e, ev0 :: evs, ctl, dst.layout_state) (e', ρ', ctl', σ'))
    (hκ : ctl'.κ = ctl.κ) :
    ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      rs'.labeled = dst.core_run_state0.labeled ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl)
          fmapEmpty acc [0]) dst =
        runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0])
          { dst with
              core_state0 := update_thread_state 0
                { th₀ with arena := e', env := ρ', current_loc := ctl'.curLoc } dst.core_state0,
              layout_state := σ',
              core_run_state0 := rs', trace := tr,
              dr_step_counter := ctr } := by
  cases hv : toVal e with
  | some w =>
    obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
    cases wa with
    | pure a b v => exact (Step.pure_val_elim hs hκ).elim
    | annot a a2 b ds v =>
      -- REMOVE-ANNOT at a non-empty call stack (`Step.ret_annot`): the
      -- engine's tau, in place (no location write — the value arm)
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := Step.annot_val_inv hs hκ
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
      rw [← hcl]
      exact loop_step_tau fl fmapEmpty acc hth
        (step_ctx_remove_annot ds v fmapEmpty dst.layout_state dst.core_file
          dst.core_extern 0 none
          { th₀ with arena := ofValA (.annot a a2 b ds v), env := ev0 :: evs } rfl)
  | none =>
  have hnv : toVal e = none := hv
  obtain ⟨ctx, r, hd, hfr⟩ := hf.decomp hnv
  rcases hd.step_factor hs with ⟨r', ρr, ctlr, σr, hnr, hnc, hr, heq⟩ |
    ⟨an, ra, l, pes, rfl, hr⟩ | ⟨an, ra, f, pes, params, body, vs, rfl, -, -, -, hcout⟩
  · obtain ⟨he', hρ', hc', hσ'⟩ := Config.mk_inj heq
    subst he' hρ' hc' hσ'
    have hccall := hd.unseq_ccall_false
    have hrj := hd.redex
    cases hrj with
    | @call an ra f pes => exact absurd rfl (hnc an ra f pes)
    | @store an loc ann lk ty pv cv mo =>
      obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hr.store_inv
      rw [htd] at hmv hmem
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_store hd hsz fmapEmpty hmv
        dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
      rw [hccall, MachineCtx.locUpdTh_ctl hcl] at hsteps
      refine ⟨{ dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_store (requestLoc { th₀ with arena := e, env := ev0 :: evs, current_loc := (ctl.upd an).curLoc } loc)
          none ty lk pv mv :: dst.trace,
        dst.dr_step_counter, rfl, ?_⟩
      exact loop_step_action fl fmapEmpty acc hth hsteps
        (ars_store_active (tid := 0)
          (aid := dst.core_run_state0.aid_supply) hmem)
    | @load an loc ann ty pv mo =>
      obtain ⟨fp, mval, σ'', hmem, hout⟩ := hr.load_inv
      rw [htd] at hmem
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_load hd hsz fmapEmpty
        dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
      rw [hccall, MachineCtx.locUpdTh_ctl hcl] at hsteps
      refine ⟨{ dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_load (requestLoc { th₀ with arena := e, env := ev0 :: evs, current_loc := (ctl.upd an).curLoc } loc)
          none ty pv mval :: dst.trace,
        dst.dr_step_counter, rfl, ?_⟩
      exact loop_step_action fl fmapEmpty acc hth hsteps
        (ars_load_active (tid := 0)
          (aid := dst.core_run_state0.aid_supply) hmem)
    | @create an loc ann align ty pref =>
      obtain ⟨pv, σ'', hmem, hout⟩ := hr.create_inv
      rw [htd] at hmem
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_create hd hsz fmapEmpty
        dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
      rw [hccall, MachineCtx.locUpdTh_ctl hcl] at hsteps
      refine ⟨{ dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_allocate_object 0 pref align ty none pv :: dst.trace,
        dst.dr_step_counter, rfl, ?_⟩
      exact loop_step_action fl fmapEmpty acc hth hsteps
        (ars_create_active (tid := 0)
          (aid := dst.core_run_state0.aid_supply) hmem)
    | @create_op an loc ann pref pe1 pe2 hnvC =>
      obtain ⟨hp1, hp2, hd1, hd2⟩ : PePure pe1 ∧ PePure pe2 ∧
          peDepth pe1 ≤ lemDefaultFuel ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | create =>
          rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvC
          cases hnvC
        | create_op hnvC' hp1 hp2 hd1 hd2 => exact ⟨hp1, hp2, hd1, hd2⟩
      obtain ⟨al, ty, hv1, hv2, hout⟩ := hr.create_op_inv hnvC
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      rw [htd, hex] at hv1 hv2
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_create_eval_ws hd hsz hnvC hp1 hp2 hd1 hd2
        fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv1) (by rw [hext]; exact hv2)
      rw [MachineCtx.locUpdTh_ctl hcl] at hm
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
        rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
    | @kill an loc ann kind pv =>
      obtain ⟨σ'', hmem, hout⟩ := hr.kill_inv
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_kill hd hsz fmapEmpty
        dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
      rw [hccall, MachineCtx.locUpdTh_ctl hcl] at hsteps
      refine ⟨{ dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_kill (requestLoc { th₀ with arena := e, env := ev0 :: evs, current_loc := (ctl.upd an).curLoc } loc)
          (is_dynamic kind) pv :: dst.trace,
        dst.dr_step_counter, rfl, ?_⟩
      exact loop_step_action fl fmapEmpty acc hth hsteps
        (ars_kill_active (tid := 0)
          (aid := dst.core_run_state0.aid_supply) hmem)
    | @kill_op an loc ann kind pe hnvK =>
      obtain ⟨hpK, hdK⟩ : PePure pe ∧ peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | kill =>
          rw [show valueFromPexpr (Pexpr [] () (PEval
            (Vobject (OVpointer _)))) = some _ from rfl] at hnvK
          cases hnvK
        | kill_op hnvK' hpK hdK => exact ⟨hpK, hdK⟩
      obtain ⟨pv, hv, hout⟩ := hr.kill_op_inv hnvK
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      rw [htd, hex] at hv
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_kill_eval_ws hd hsz hnvK hpK hdK
        fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv)
      rw [MachineCtx.locUpdTh_ctl hcl] at hm
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
        rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
    | @alloc an loc ann align size pref =>
      obtain ⟨pv, σ'', hmem, hout⟩ := hr.alloc_inv
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      have hsteps := step_ctx_alloc hd hsz fmapEmpty
        dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
      rw [hccall, MachineCtx.locUpdTh_ctl hcl] at hsteps
      refine ⟨{ dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_allocate_region 0 pref align size pv :: dst.trace,
        dst.dr_step_counter, rfl, ?_⟩
      exact loop_step_action fl fmapEmpty acc hth hsteps
        (ars_alloc_active (tid := 0)
          (aid := dst.core_run_state0.aid_supply) hmem)
    | @alloc_op an loc ann pref pe1 pe2 hnvA =>
      obtain ⟨hp1, hp2, hd1, hd2⟩ : PePure pe1 ∧ PePure pe2 ∧
          peDepth pe1 ≤ lemDefaultFuel ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | alloc =>
          rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnvA
          cases hnvA
        | alloc_op hnvA' hp1 hp2 hd1 hd2 => exact ⟨hp1, hp2, hd1, hd2⟩
      obtain ⟨al, sz, hv1, hv2, hout⟩ := hr.alloc_op_inv hnvA
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      rw [htd, hex] at hv1 hv2
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_alloc_eval_ws hd hsz hnvA hp1 hp2 hd1 hd2
        fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv1) (by rw [hext]; exact hv2)
      rw [MachineCtx.locUpdTh_ctl hcl] at hm
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
        rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
    | @beta_pure an pa a1 b1 bty v e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, a1', b1', v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ v = v' := by
          simpa using ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_pure hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · cases ofValA_inj he1
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · exact (hcall.ne_same_κ hκ).elim
    | @beta_annot an pa a1 a2 b1 bty ds v e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, a1', a2', b1', ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · cases ofValA_inj he1
      · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ v = v' := by
          simpa using ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_annot hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · exact (hcall.ne_same_κ hκ).elim
    | @wbeta_pure an pa a1 b1 bty v e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, a1', b1', v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ v = v' := by
          simpa using ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_wseq_pure hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · cases ofValA_inj he1
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (symPat_ne_base hpatS1).elim
      · exact (symPat_ne_base hpatS2).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · exact (hcall.ne_same_κ hκ).elim
    | @wbeta_annot an pa a1 a2 b1 bty ds v e2 =>
      rcases hr.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, _, he1, _, hout⟩ |
          ⟨_, _, a1', a2', b1', ds', v', _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · cases ofValA_inj he1
      · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ v = v' := by
          simpa using ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_wseq_annot hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (symPat_ne_base hpatS1).elim
      · exact (symPat_ne_base hpatS2).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · exact (hcall.ne_same_κ hκ).elim
    | @merge an a2 ds1 ds2 b hirr =>
      rcases hr.annot_inv with ⟨hg, hnj, hnc', hnv', b', ρ'', ctl'', σ'', hstep, hout⟩ |
          ⟨a2', ds2', c, hbeq, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
          ⟨-, hcall⟩ | ⟨a2', b1', v', pc', κ', hb', hκ', hout'⟩
      · rw [show annotRooted (Expr a2 (Eannot ds2 b)) = true from rfl] at hg
        cases hg
      · injection hbeq with hb1 hb2
        injection hb2 with hb3 hb4
        subst hb1 hb3 hb4
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_merge hd hirr hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · rw [show annotRooted (Expr a2 (Eannot ds2 b)) = true from rfl] at hg
        cases hg
      · exact (hcall.ne_same_κ hκ).elim
      · cases hb'
    | @save an sb ps body =>
      have hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | save _ hdep _ => exact hdep
      rcases hr.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
          ⟨cvals, hnvS, hvals, hout⟩
      · obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_save hd hsz hvals fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        rw [htd, hex] at hvals
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_save_eval_ws hd hsz hnvS hdep
          fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
          (by rw [hext]; exact hvals)
        rw [MachineCtx.locUpdTh_ctl hcl] at hm
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
          (hm dst.core_run_state0)
    | @if_ an g e2 e3 =>
      have hdg : peDepth g ≤ lemDefaultFuel := by
        cases hfr with
        | if_ _ hdg _ _ => exact hdg
      rcases hr.if_inv with ⟨hg, hout⟩ | ⟨hg, hout⟩
      · obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        rw [htd, hex] at hg
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_true_ws hd hsz hdg
          fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
          (by rw [hext]; exact hg)
        rw [MachineCtx.locUpdTh_ctl hcl] at hm
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_withrs_tau fl fmapEmpty acc hth hsteps
          (hm dst.core_run_state0)
      · obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        rw [htd, hex] at hg
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_false_ws hd hsz hdg
          fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
          (by rw [hext]; exact hg)
        rw [MachineCtx.locUpdTh_ctl hcl] at hm
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_withrs_tau fl fmapEmpty acc hth hsteps
          (hm dst.core_run_state0)
    | @case_ an pe pats =>
      cases hfr with
      | case_value hbr hbsz =>
        obtain ⟨e'', hsel, hout⟩ := hr.case_value_inv (valueFromPexpr_val _ _)
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_case_value hd hsz hsel fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
    | @run an ra l pes =>
      exact absurd rfl (hnr an ra l pes)
    | @pure_e an pe hnv2 =>
      obtain ⟨pb, x, rfl⟩ : ∃ pb x, pe = Pexpr pb () (PEsym x) := by
        cases hfr with
        | val_pure v => rw [valueFromPexpr_val] at hnv2; cases hnv2
        | pure_sym => exact ⟨_, _, rfl⟩
      obtain ⟨v, -, hv, hout⟩ := hr.pure_inv hnv2
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      rw [htd, hex] at hv
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_pure_sym_ws hd hsz
        fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv)
      rw [MachineCtx.locUpdTh_ctl hcl] at hm
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
    | @load_op an loc ann ty pe2 mo hnv2 =>
      obtain ⟨hp2, hd2⟩ : PePure pe2 ∧ peDepth pe2 ≤ lemDefaultFuel := by
        cases hfr with
        | load =>
          rw [show valueFromPexpr (Pexpr [] () (PEval
            (Vobject (OVpointer _)))) = some _ from rfl] at hnv2
          cases hnv2
        | load_op hnv2' hp2 hd2 => exact ⟨hp2, hd2⟩
      obtain ⟨pv, hv2, hout⟩ := hr.load_op_inv hnv2
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      rw [htd, hex] at hv2
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_load_eval_ws hd hsz hnv2 hp2 hd2
        fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv2)
      rw [MachineCtx.locUpdTh_ctl hcl] at hm
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
    | @beta_spec an pa pb x bty wa e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', a1', b1', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', a1', a2', b1', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', b1', v', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', a2', b1', ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (specPat_ne_base hpat.symm).elim
      · exact (specPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_spec_pure hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_spec_annot hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · exact (symPat_ne_spec hpat).elim
      · exact (symPat_ne_spec hpat).elim
      · exact (specPat_ne_tuple hpatT1).elim
      · exact (specPat_ne_tuple hpatT2).elim
      · exact (hcall.ne_same_κ hκ).elim
    | @memop an mop pes =>
      cases hfr with
      | memop_vals v1 v2 =>
        obtain ⟨pv1, pv2, b, σ'', rfl, rfl, hmem, hout⟩ := hr.memop_vals_inv
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_memop hd hsz rfl rfl fmapEmpty
          dst.layout_state dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
        rw [hccall, MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter, rfl, ?_⟩
        exact loop_step_memop fl fmapEmpty acc hth hsteps
          (ars_memop_active fmapEmpty (by
            rw [eqPtrval_loc_irrel _ default pv1 pv2]; exact hmem))
      | memop_op hnvF hp1 hp2 hpd1 hpd2 =>
        obtain ⟨v1, v2, hv1', hv2', hout⟩ := hr.memop_op_inv hnvF
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        rw [htd, hex] at hv1' hv2'
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_memop_eval_ws hd hsz hnvF
          hpd1 hpd2 fmapEmpty dst.layout_state dst.core_file
          dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
          (by rw [hext]; exact hv1') (by rw [hext]; exact hv2')
        rw [MachineCtx.locUpdTh_ctl hcl] at hm
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
          (hm dst.core_run_state0)
    | @store_op an loc ann ty pe2 pe3 mo hnvR =>
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
      obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
      subst h1 h2 h3 h4
      rw [htd, hex] at hv2 hv3
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_store_eval_ws hd hsz hnvR
        hp2 hp3 hpd2 hpd3 fmapEmpty dst.layout_state dst.core_file
        dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv2) (by rw [hext]; exact hv3)
      rw [MachineCtx.locUpdTh_ctl hcl] at hm
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
    | @beta_sym an pa x bty wa e2 =>
      rcases hr.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', a1', b1', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', a1', a2', b1', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', b1', v', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', a1', a2', b1', ds', v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (symPat_ne_base hpat.symm).elim
      · exact (symPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (symPat_ne_spec hpat.symm).elim
      · exact (symPat_ne_spec hpat.symm).elim
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_sym_pure hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl := ofValA_inj he1
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_beta_sym_annot hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · exact (symPat_ne_tuple hpatT1).elim
      · exact (symPat_ne_tuple hpatT2).elim
      · exact (hcall.ne_same_κ hκ).elim
    | @bound_pure an a1 b1 v =>
      rcases hr.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨a1', b1', v', hb, hout⟩ | ⟨_, _, _, _, _, hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ | hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ v = v' := by
          simpa using ofValA_inj hb
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_bound_pure hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · cases ofValA_inj hb
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (hcall.ne_same_κ hκ).elim
    | @bound_annot an a1 a2 b1 ds v =>
      rcases hr.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
          ⟨_, _, _, hb, hout⟩ | ⟨a1', a2', b1', ds', v', hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ | hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · cases ofValA_inj hb
      · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ v = v' := by
          simpa using ofValA_inj hb
        obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
        subst h1 h2 h3 h4
        have hsteps := step_ctx_bound_annot hd hsz fmapEmpty dst.layout_state
          dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
        rw [MachineCtx.locUpdTh_ctl hcl] at hsteps
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth hsteps
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (hcall.ne_same_κ hκ).elim
  · -- the jump disjunct: the context is discarded, the label read
    -- resolves in the DRIVER'S run state through the tie hQd
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hr.jump_inv (by rfl)
    have hdep : ∀ pe' ∈ pes, peDepth pe' ≤ lemDefaultFuel := by
      cases hfr with
      | run _ hdep => exact hdep
    obtain ⟨p, hproc, hQd⟩ := hjmp l params cont hl
    rw [htd, hex] at hvs
    obtain ⟨h1, h2, h3, h4⟩ := Config.mk_inj hout
    subst h1 h2 h3 h4
    obtain ⟨s, m, hsteps, hm⟩ := step_ctx_run_ws hd hsz hl hdep
      fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none p
      { th₀ with arena := e, env := ev0 :: evs } rfl hproc
      (by rw [hext]; exact hvs)
    rw [MachineCtx.locUpdTh_ctl hcl] at hm
    refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
    exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
      (hm dst.core_run_state0
        (by rw [hext, resolveExtern_empty]; exact hQd))
  · obtain ⟨-, -, h3, -⟩ := Config.mk_inj hcout
    rw [h3] at hκ
    exact absurd hκ (by simp)

/-- The control-preserving round at a KNOWN current procedure (the calls
    arc C2 statement): `loop_step_frag_same'` with the jump tie supplied
    by the thread's `current_proc_opt` and the run-state tie `hQd` at the
    context's derived label map `hlb`. -/
theorem loop_step_frag_same {M₀ : MachineCtx} {ctl ctl' : Ctl}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labelsAt ctl.proc = Q)
    {p : sym} {th₀ : thread_state} (hproc : th₀.current_proc_opt = some p)
    (hcl : th₀.current_loc = ctl.curLoc)
    (fl : Nat) (acc : Fmap thread_id (List core_step2))
    {dst : driver_state} {e e' : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ρ' : EnvStack} {σ' : Mem}
    (hth : dst.core_state0.thread_states =
      [(0, (none, { th₀ with arena := e, env := ev0 :: evs }))])
    (hext : dst.core_extern = fmapEmpty)
    (hQd : LabeledAt dst.core_run_state0 p Q)
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M₀ (e, ev0 :: evs, ctl, dst.layout_state) (e', ρ', ctl', σ'))
    (hκ : ctl'.κ = ctl.κ) :
    ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      rs'.labeled = dst.core_run_state0.labeled ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl)
          fmapEmpty acc [0]) dst =
        runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0])
          { dst with
              core_state0 := update_thread_state 0
                { th₀ with arena := e', env := ρ', current_loc := ctl'.curLoc } dst.core_state0,
              layout_state := σ',
              core_run_state0 := rs', trace := tr,
              dr_step_counter := ctr } :=
  loop_step_frag_same' htd hex hcl fl acc hth hext
    (fun _ _ _ _ => ⟨p, hproc, by rw [hlb]; exact hQd⟩) hf hsz hs hκ

/-- THE DRIVER STEP-MATCH AT THE LIVE CONTROL (calls arc C2 — the C1
    range audit's M-1 obligation: the mirror's control TIED to the
    driver thread's control fields). The driver thread is `th₀` with the
    live `(e, ρ)` installed and its FOUR control fields equal to the
    mirror's `ctl` (`hstack`/`hproc`/`hel`/`hcl` — E1 added the current
    location, what the general arm writes and the PCALL arm pushes onto
    `exec_loc`); the file is the context's (`hfile`; what `call_proc`
    reads). Wherever the mirror steps at a cone configuration —
    control-preserving, CALL or RETURN — the production driver's
    per-thread round advances the singleton thread to EXACTLY the
    mirror's successor, the four control fields written to the successor
    control's. Proof: the control-preserving rounds are
    `loop_step_frag_same'`; the CALL round is `step_ctx_call_ws` +
    `loop_step_withrs_eval` (run state verbatim); the RETURN round is
    `step_ctx_ret` + `loop_step_tau_tsk` (trace existential). -/
theorem loop_step_frag' {M₀ : MachineCtx} {ctl ctl' : Ctl}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {th₀ : thread_state}
    (hstack : th₀.stack0 = ctl.toStack) (hproc : th₀.current_proc_opt = ctl.proc)
    (hel : th₀.exec_loc = ctl.execLoc) (hcl : th₀.current_loc = ctl.curLoc)
    (fl : Nat) (acc : Fmap thread_id (List core_step2))
    {dst : driver_state} {e e' : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ρ' : EnvStack} {σ' : Mem}
    (hth : dst.core_state0.thread_states =
      [(0, (none, { th₀ with arena := e, env := ev0 :: evs }))])
    (hext : dst.core_extern = fmapEmpty) (hfile : dst.core_file = M₀.file)
    (hjmp : ∀ l params cont, lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont) →
      ∃ p, th₀.current_proc_opt = some p ∧
        LabeledAt dst.core_run_state0 p (M₀.labelsAt ctl.proc))
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M₀ (e, ev0 :: evs, ctl, dst.layout_state) (e', ρ', ctl', σ')) :
    ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      rs'.labeled = dst.core_run_state0.labeled ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl)
          fmapEmpty acc [0]) dst =
        runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0])
          { dst with
              core_state0 := update_thread_state 0
                { th₀ with
                  arena := e'
                  env := ρ'
                  stack0 := ctl'.toStack
                  current_proc_opt := ctl'.proc
                  exec_loc := ctl'.execLoc
                  current_loc := ctl'.curLoc } dst.core_state0,
              layout_state := σ',
              core_run_state0 := rs', trace := tr,
              dr_step_counter := ctr } := by
  rcases hs.ctl_cases with ⟨a, rfl⟩ |
      ⟨ctx, f, pes, params, body, vs, hc, hvs, hfl, hlen, rfl, rfl, rfl, rfl⟩ |
      ⟨a1, b1, v, ev0', evs', pq, ctx, κ, q, ℓ, lc, sp, he, hρ, hctl, rfl, rfl, rfl, rfl⟩
  · -- control-preserving: the successor's control fields are th₀'s own,
    -- the location the updated control's
    obtain ⟨rs', tr, ctr, hlab, hrun⟩ :=
      loop_step_frag_same' htd hex hcl fl acc hth hext hjmp hf hsz hs rfl
    refine ⟨rs', tr, ctr, hlab, ?_⟩
    rw [hrun, Ctl.toStack_upd, Ctl.upd_proc, Ctl.upd_execLoc, ← hstack, ← hproc, ← hel]
  · -- THE CALL
    have hnv : toVal e = none := by
      cases hv : toVal e with
      | none => rfl
      | some w =>
        obtain ⟨wa, -, rfl⟩ := ofValA_of_toVal hv
        rw [callRedex?_ofValA] at hc
        cases hc
    obtain ⟨ctx', r, hd, hfr⟩ := hf.decomp hnv
    obtain ⟨rfl, an, ra, rfl⟩ := hd.callRedex?_inv hc
    have hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel := by
      cases hfr with
      | call _ hdep => exact hdep
    rw [htd, hex] at hvs
    obtain ⟨m, hsteps, hm⟩ := step_ctx_call_ws hd hsz hdep fmapEmpty dst.layout_state
      dst.core_file dst.core_extern 0 none { th₀ with arena := e, env := ev0 :: evs } rfl
      (by rw [hext]; exact hvs) (by rw [hfile, hext, ← hex]; exact hfl) hlen
    rw [MachineCtx.locUpdTh_ctl hcl] at hm
    refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1, rfl, ?_⟩
    rw [loop_step_withrs_eval fl fmapEmpty acc hth hsteps (hm dst.core_run_state0),
      hd.redexAnnots_eq, redexAnnots_callRedex]
    show _ = runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) _
    rw [show ({ th₀ with arena := e, env := ev0 :: evs } : thread_state).current_proc_opt =
        ctl.proc from hproc,
      show ({ th₀ with arena := e, env := ev0 :: evs } : thread_state).stack0 =
        ctl.toStack from hstack,
      show ({ th₀ with arena := e, env := ev0 :: evs } : thread_state).exec_loc =
        ctl.execLoc from hel]
    rcases dst with ⟨cf, ce, cs, crs, ls, cc, fs, tr0, sa, bl, ctr0⟩
    rfl
  · -- THE RETURN
    subst hctl
    injection hρ with h1 h2
    subst h1
    subst h2
    subst he
    obtain ⟨tsk, hsteps⟩ := step_ctx_ret v fmapEmpty dst.layout_state dst.core_file
      dst.core_extern 0 none
      { th₀ with arena := ofValA (.pure a1 b1 v), env := ev0 :: evs }
      rfl hstack rfl
    obtain ⟨tr, hrun⟩ := loop_step_tau_tsk fl fmapEmpty acc hth hsteps
    refine ⟨dst.core_run_state0, tr, dst.dr_step_counter + 1, rfl, ?_⟩
    rw [hrun]
    show _ = runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) _
    rw [show ({ th₀ with arena := ofValA (.pure a1 b1 v), env := ev0 :: evs } :
        thread_state).exec_loc = ℓ from hel,
      show ({ th₀ with arena := ofValA (.pure a1 b1 v), env := ev0 :: evs } :
        thread_state).current_loc = lc from hcl]
    rcases dst with ⟨cf, ce, cs, crs, ls, cc, fs, tr0, sa, bl, ctr0⟩
    rfl

/-- The live-control round at a KNOWN, TIED current procedure (the calls
    arc C2 statement; pinned): `loop_step_frag'` with the jump tie
    supplied by `hp`/`hproc`/`hlb`/`hQd`. -/
theorem loop_step_frag {M₀ : MachineCtx} {ctl ctl' : Ctl}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labelsAt ctl.proc = Q)
    {p : sym} (hp : ctl.proc = some p) {th₀ : thread_state}
    (hstack : th₀.stack0 = ctl.toStack) (hproc : th₀.current_proc_opt = ctl.proc)
    (hel : th₀.exec_loc = ctl.execLoc) (hcl : th₀.current_loc = ctl.curLoc)
    (fl : Nat) (acc : Fmap thread_id (List core_step2))
    {dst : driver_state} {e e' : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ρ' : EnvStack} {σ' : Mem}
    (hth : dst.core_state0.thread_states =
      [(0, (none, { th₀ with arena := e, env := ev0 :: evs }))])
    (hext : dst.core_extern = fmapEmpty) (hfile : dst.core_file = M₀.file)
    (hQd : LabeledAt dst.core_run_state0 p Q)
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M₀ (e, ev0 :: evs, ctl, dst.layout_state) (e', ρ', ctl', σ')) :
    ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      rs'.labeled = dst.core_run_state0.labeled ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl)
          fmapEmpty acc [0]) dst =
        runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0])
          { dst with
              core_state0 := update_thread_state 0
                { th₀ with
                  arena := e'
                  env := ρ'
                  stack0 := ctl'.toStack
                  current_proc_opt := ctl'.proc
                  exec_loc := ctl'.execLoc
                  current_loc := ctl'.curLoc } dst.core_state0,
              layout_state := σ',
              core_run_state0 := rs', trace := tr,
              dr_step_counter := ctr } :=
  loop_step_frag' htd hex hstack hproc hel hcl fl acc hth hext hfile
    (fun _ _ _ _ => ⟨p, by rw [hproc, hp], by rw [hlb]; exact hQd⟩) hf hsz hs

/-! ## The live-control vocabulary of BOTH driver lanes (moved here from
ProdLoop.lean in the fuel-lane restatement, 2026-09-03: the partial lane
in Adequacy.lean states its facts over the same thread shape and the same
registration ties as the total lane in ProdLoop.lean). -/

/-- The driver thread at a LIVE control over the immutables of `th₀`:
    the arena, the env and the FOUR control fields the rounds write
    (`stack0 := ctl.toStack`, `current_proc_opt := ctl.proc`, `exec_loc
    := ctl.execLoc` — PCALL/RETURN — and, E1, `current_loc := ctl.curLoc`
    — the general arm's location write); only `errno` is `th₀`'s.
    `loop_step_frag`'s successor record IS this shape. -/
def ctlThread (th₀ : thread_state) (e : CoreExpr) (ρ : EnvStack) (ctl : Ctl) : thread_state :=
  { th₀ with
    arena := e
    env := ρ
    stack0 := ctl.toStack
    current_proc_opt := ctl.proc
    exec_loc := ctl.execLoc
    current_loc := ctl.curLoc }

@[simp] theorem ctlThread_current_loc (th₀ : thread_state) (e : CoreExpr) (ρ : EnvStack)
    (ctl : Ctl) : (ctlThread th₀ e ρ ctl).current_loc = ctl.curLoc := rfl

/-- THE WHOLE-FILE REGISTRATION TIE: the run state's two-level `labeled`
    map has, at every DECLARED procedure (`lookupProc`, the stdlib-first
    read `call_proc` makes), exactly the context's derived fiber
    `M₀.labelsAt (some f)`. The single-procedure lane's `LabeledAt` is
    this at one procedure. -/
def LabeledProcs (M₀ : MachineCtx) (lab : Fmap sym LabelMap) : Prop :=
  ∀ f params body, lookupProc M₀.file M₀.extern f = some (params, body) →
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) f lab =
      some (M₀.labelsAt (some f))

/-- The tie holds at the context's OWN run state as soon as every
    declared procedure has SOME fiber there (the registration installs
    one per `Proc` of the file): the derived fiber is that fiber. -/
theorem LabeledProcs.of_fibers {M₀ : MachineCtx} (hex : M₀.extern = fmapEmpty)
    (h : ∀ f params body, lookupProc M₀.file M₀.extern f = some (params, body) →
      ∃ Q : LabelMap, fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2) f M₀.runState.labeled = some Q) :
    LabeledProcs M₀ M₀.runState.labeled := by
  intro f params body hf
  obtain ⟨Q, hQ⟩ := h f params body hf
  rw [hQ, MachineCtx.labelsAt_some, MachineCtx.resolveProc_of_extern_empty hex, hQ]

/-- THE CONTROL'S REGISTRATION TIE (the partial lane's tie for the
    procedures ALREADY ON the control): the run state's `labeled` map has,
    at the current procedure and at every procedure saved on the call
    stack, exactly the context's derived fiber — what the jump round reads
    (`loop_step_frag'`'s `hjmp`). Vacuous at a control with no current
    procedure and an empty stack (`CtlTied.noproc` — the straight-line
    profile, where the derived map is empty and no jump can fire); at a
    declared entry procedure it follows from the whole-file tie
    (`CtlTied.entry`); the callees entered by PCALL are tied by
    `LabeledProcs`, so the tie is preserved along a run. -/
def CtlTied (M₀ : MachineCtx) (lab : Fmap sym LabelMap) (ctl : Ctl) : Prop :=
  (∀ p, ctl.proc = some p →
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) p lab =
      some (M₀.labelsAt (some p))) ∧
  ∀ pc ∈ ctl.κ, ∀ p, pc.1 = some p →
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) p lab =
      some (M₀.labelsAt (some p))

theorem CtlTied.noproc (M₀ : MachineCtx) (lab : Fmap sym LabelMap) (ℓ : exec_location)
    (lc : CerbLocation.Loc) (sp : RunSup) :
    CtlTied M₀ lab ⟨[], none, ℓ, lc, sp⟩ :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem CtlTied.entry {M₀ : MachineCtx} {lab : Fmap sym LabelMap} (hlab : LabeledProcs M₀ lab)
    {p : sym} {params : List (sym × core_base_type)} {body : CoreExpr}
    (hq : lookupProc M₀.file M₀.extern p = some (params, body)) (ℓ : exec_location)
    (lc : CerbLocation.Loc) (sp : RunSup) :
    CtlTied M₀ lab ⟨[], some p, ℓ, lc, sp⟩ :=
  ⟨fun q hq' => (by cases hq'; exact hlab p params body hq), fun _ h => (by cases h)⟩

/-- A successful label lookup at the control's current procedure names a
    procedure the run state ties: the jump round's tie (`hjmp`) from the
    control's tie. -/
theorem CtlTied.jump {M₀ : MachineCtx} {lab : Fmap sym LabelMap} {ctl : Ctl}
    (h : CtlTied M₀ lab ctl) {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (hl : lookupLabel (M₀.labelsAt ctl.proc) l = some (params, cont)) :
    ∃ p, ctl.proc = some p ∧
      fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) p lab =
        some (M₀.labelsAt ctl.proc) := by
  cases hp : ctl.proc with
  | none =>
    rw [hp, MachineCtx.labelsAt_none, show lookupLabel fmapEmpty l = none from rfl] at hl
    cases hl
  | some p => exact ⟨p, rfl, h.1 p hp⟩

/-! ## The exhaustion rounds and the killed pipeline (the partial lane's
driver arms, fuel-lane restatement 2026-09-03). The shipped loop's
out-of-fuel value is the kernel-transparent kill `CerbND.fuelExhaustedKill`
(`CerbND.drive_nonmemory_steps_aux2_lemFuel_zero`, the cerberus-lean fuel
arc); an exhausted loop kills `driver2` through the ND bind's killed arm,
and a one-layer killed tree is the singleton killed execution of `runND`. -/

/-- The loop at fuel 0: the exhaustion kill, the state untouched. -/
theorem loop_zero_exhausts (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (acc : Fmap thread_id (List core_step2)) (xs : List Nat) (dst : driver_state) :
    runOne (drive_nonmemory_steps_aux2_lemFuel 0 tds acc xs) dst =
      (NDkilled CerbND.fuelExhaustedKill, dst) := by
  rw [CerbND.drive_nonmemory_steps_aux2_lemFuel_zero]
  rfl

/-- Done round at fuel EXACTLY ONE: PROGRAM-DONE is not advanceable, the
    singleton is recorded, and the drain iteration on the empty thread
    list has no fuel — the exhaustion kill (the reason the total lane's
    delivery needs `k + 2` iterations). -/
theorem loop_step_done_exhaust (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (acc : Fmap thread_id (List core_step2))
    {dst : driver_state} {th : thread_state} {v : value}
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hsteps : step_ctx tds dst.layout_state dst.core_file dst.core_extern 0
      (none, th) = [Step_done2 v]) :
    runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ 0) tds acc [0]) dst =
      (NDkilled CerbND.fuelExhaustedKill, dst) := by
  conv => lhs; unfold drive_nonmemory_steps_aux2_lemFuel
  refine (runOne_bind_active (z := [Step_done2 v]) (s' := dst) ?_).trans ?_
  · rw [runOne_read]
    refine congrArg (fun x => (NDactive x, dst)) ?_
    show (let th_info := match lookupBy (fun x y => x == y) 0
            dst.core_state0.thread_states with
          | some z => z
          | none => failwithI _;
        step_ctx tds dst.layout_state dst.core_file dst.core_extern 0 th_info) = _
    rw [hth]
    exact hsteps
  · dsimp only [find_can_advance, can_advance]
    exact loop_zero_exhausts tds _ _ dst

/-- `runND` (CerbND.lean) of a computation whose one-layer application
    is KILLED: exactly one execution, the killed one (the runner's
    `NDkilled` arm; the killed-side twin of `runND_active`). -/
theorem runND_killed {a info err cs st : Type}
    {m : ndM a info err cs st} {s s' : st} {r : kill_reason err}
    (h : runOne m s = (NDkilled r, s')) :
    CerbND.runND m s = [(nd_status.Killed s' r, ([] : List String), s')] := by
  rcases m with ⟨g⟩
  dsimp only [runOne] at h
  show CerbND.runNDFuel CerbFuel.driverFuel (ND g) s = _
  rw [driverFuel_succ]
  unfold CerbND.runNDFuel
  dsimp only
  rw [h]

/-- `driver2` when the per-thread loop KILLS (in the partial lane: the
    exhaustion kill at the shipped loop budget): `new_drive_core_threads`
    runs the loop on the singleton thread list and the ND bind's killed
    arm propagates the kill — the round is the kill, the state the
    loop's. -/
theorem driver2_killed (fl : Nat)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition))
    (dst dstK : driver_state) (th : thread_state) (r : kill_reason driver_error)
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hloop : runOne (drive_nonmemory_steps_aux2_lemFuel CerbFuel.driverFuel tds
        fmapEmpty [0]) dst = (NDkilled r, dstK)) :
    runOne (driver2_lemFuel (Nat.succ fl) tds false) dst = (NDkilled r, dstK) := by
  conv => lhs; unfold driver2_lemFuel
  refine runOne_bind_killed ?_
  unfold new_drive_core_threads
  refine (runOne_bind_active (z := dst) (by rfl)).trans ?_
  dsimp only
  rw [hth]
  dsimp only [List.map]
  exact runOne_bind_killed hloop

end CerberusHeapLang
