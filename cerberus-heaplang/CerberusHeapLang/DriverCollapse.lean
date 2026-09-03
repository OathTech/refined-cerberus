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
  `driveU` round: the step_ctx singleton (the per-rule
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
  protocol (ProdLoop.lean), exactly as in `driveU`.

- `driver2_done`: the whole `driver2` computation from a PROGRAM-DONE
  thread is the singleton `Active` execution, for both values of the
  opaque `current_execution_mode` test (`cases` on it) — the one
  configuration read on a proved path.

FUEL: the driver functions run at their production budgets
(lemDefaultFuel = 10^6). `nd_bind`/`liftND` budgets are spent per
LAYER of one bind and never accumulate across the run;
`drive_nonmemory_steps_aux2`'s budget is spent once per loop
iteration, so statements carry `n + 2 ≤ lemDefaultFuel` (n drive
steps + the done-recording and drain iterations); `driver2`'s budget
is spent once per non-advanceable step (exactly one: Step_done2);
get_ctx budgets are the inherited `esize` side conditions
(Soundness.lean FUEL HONESTY). At insufficient fuel the production
value is the opaque `fuelExhausted` leaf — nothing is provable there;
this is why the production-entry theorems carry a
termination-within-budget hypothesis (README, "Registered divergences
and limitations").
-/
import CerberusHeapLang.Adequacy
import Driver
import CerbND

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-! ## The runOne layer (the ND collapse): one-layer application of
an ndM tree -/

/-- One-layer application of an ndM computation — the driver-level
    analog of `applyMemM` (Step.lean), kept at the raw
    `nd_action × state` level so killed outcomes stay visible. -/
def runOne {a info err cs st : Type} (m : ndM a info err cs st) (s : st) :
    nd_action a info err cs st × st :=
  match m with | ND f => f s

private theorem lemDefaultFuel_succ : lemDefaultFuel = Nat.succ 999999 := rfl

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
  show runOne (nd_bind_lemFuel lemDefaultFuel (ND g) f) s = _
  rw [lemDefaultFuel_succ]
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
  show runOne (nd_bind_lemFuel lemDefaultFuel (ND g) f) s = _
  rw [lemDefaultFuel_succ]
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
  show CerbND.runNDFuel CerbND.ndDefaultFuel (ND g) s = _
  rw [show CerbND.ndDefaultFuel = Nat.succ 999999 from rfl]
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
    (hloop : runOne (drive_nonmemory_steps_aux2_lemFuel lemDefaultFuel tds
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
theorem step_ctx_if_true_ws {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex g e2 e3))
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
        Result (Defined { th with arena := apply_ctx ctx e2 }, rs) := by
  have hget : get_ctx th.arena = [(ctx, ifRedex g e2 e3)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold ifRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr ([] : List annot) (Eif g e2 e3)) = false
       from rfl]
     dsimp only [get_loc]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hg hdg σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return])

/-- Eif (FALSE), raw — symmetric. -/
theorem step_ctx_if_false_ws {e : CoreExpr} {ctx : context}
    {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
    (hd : Decomp e ctx (ifRedex g e2 e3))
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
        Result (Defined { th with arena := apply_ctx ctx e3 }, rs) := by
  have hget : get_ctx th.arena = [(ctx, ifRedex g e2 e3)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold ifRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr ([] : List annot) (Eif g e2 e3)) = false
       from rfl]
     dsimp only [get_loc]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hg hdg σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return])

/-- PURE at a symbol, raw: one `RSK_eval` step, run state verbatim. -/
theorem step_ctx_pure_sym_ws {e : CoreExpr} {ctx : context}
    {pb : List _root_.annot} {x : sym} {v : value}
    (hd : Decomp e ctx (pureRedex (Pexpr pb () (PEsym x))))
    (hsz : esize e ≤ lemDefaultFuel)
    (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = e)
    (hv : evalPexpr tds ext th.env (Pexpr pb () (PEsym x)) = some v) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = Result (Defined { th with arena :=
        (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v))))) }, rs) := by
  have hget : get_ctx th.arena =
      [(ctx, pureRedex (Pexpr pb () (PEsym x)))] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold pureRedex
  cases ctx <;>
    (dsimp only [one_step0, is_irreducible, valueFromPexpr]
     simp only [Bool.false_eq_true, if_false]
     dsimp only [get_loc]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge hv (peDepth_sym_le pb x) σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- THE JUMP, raw: one `RSK_eval` step whose monad reads the run
    state's `labeled` fiber (READ-ONLY — `state_except_read`) and
    returns the rebound continuation with the run state VERBATIM, for
    every run state carrying the tie. -/
theorem step_ctx_run_ws {e : CoreExpr} {ctx : context}
    {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)}
    (hd : Decomp e ctx (runRedex ra l pes))
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
        m rs = Result (Defined { th with
          env := (bindArgs params vs th.env), arena := cont }, rs) := by
  have hget : get_ctx th.arena = [(ctx, runRedex ra l pes)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  have hl' : (fmapLookupBy (fun (sym1 : sym) (sym2 : sym) =>
      Lem_Basic_classes.ordCompare sym1 sym2) l Q) = some (params, cont) := hl
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold runRedex
  cases ctx <;>
    (dsimp only [get_loc]
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
theorem step_ctx_load_eval_ws {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 : generic_pexpr Unit sym} {mo : memory_order}
    {pv : CerbMem.PointerValue}
    (hd : Decomp e ctx (loadOpRedex loc ann ty pe2 mo))
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
      ∀ rs, m rs = Result (Defined { th with
        arena := apply_ctx ctx (loadRedex loc ann ty pv mo) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, loadOpRedex loc ann ty pe2 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold loadOpRedex
  cases ctx <;>
    (dsimp only [get_loc]
     dsimp only [step_action]
     rw [act_valueFromPexpr_none hp2 hnv2]
     dsimp only [act_valueFromPexpr, valueFromPexpr]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [full_eval_bridge (v := Vctype ty) rfl (peDepth_val_le _ _) σ file,
       full_eval_bridge hv2 hd2 σ file]
     dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
       return1, except_return]
     rfl)

/-- Store ACTION_EVAL, raw: one `RSK_eval` step rebuilding the
    canonical store redex, run state verbatim. -/
theorem step_ctx_store_eval_ws {e : CoreExpr} {ctx : context}
    {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
    {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
    {pv : CerbMem.PointerValue} {cv : value}
    (hd : Decomp e ctx (storeOpRedex loc ann ty pe2 pe3 mo))
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
      ∀ rs, m rs = Result (Defined { th with
        arena := apply_ctx ctx (storeRedex loc ann false ty pv cv mo) },
        rs) := by
  have hget : get_ctx th.arena =
      [(ctx, storeOpRedex loc ann ty pe2 pe3 mo)] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold storeOpRedex
  rw [valueFromPexprs_pair] at hnv
  cases hp2 <;> cases hp3 <;>
    try (rw [valueFromPexpr_val, valueFromPexpr_val] at hnv; cases hnv)
  all_goals try (obtain rfl := Option.some.inj ((evalPexpr_val _ _ _ _ _).symm.trans hv2))
  all_goals
    cases ctx <;>
      (dsimp only [get_loc]
       dsimp only [step_action]
       dsimp only [act_valueFromPexpr, valueFromPexpr]
       refine ⟨_, _, rfl, fun rs => ?_⟩
       rw [full_eval_bridge (v := Vctype ty) rfl (peDepth_val_le _ _) σ file,
         full_eval_bridge hv2 hd2 σ file,
         full_eval_bridge hv3 hd3 σ file]
       dsimp only [stExceptUndef_bind, stExceptUndef_return, stExpect_return,
         return1, except_return]
       rfl)

/-- Esave PARAMETER EVALUATION, raw: one `RSK_eval` step rebuilding the
    Esave node with its evaluated initializers, run state verbatim
    (the driver-lane twin of `stepDischarge_save_eval`). -/
theorem step_ctx_save_eval_ws {e : CoreExpr} {ctx : context}
    {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} {cvals : List value}
    (hd : Decomp e ctx (saveRedex sb ps body))
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
      ∀ rs, m rs = Result (Defined { th with
        arena := apply_ctx ctx (saveRedex sb (saveParamsWithValues ps cvals) body) },
        rs) := by
  have hget : get_ctx th.arena = [(ctx, saveRedex sb ps body)] := by
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
     rw [show is_irreducible (Expr [] (Esave sb ps body)) = false from rfl]
     dsimp only [get_loc]
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
         | rfl
         | (intro p rs'
            rfl))

/-- Memop-operand EVAL, raw: one `RSK_eval` step rebuilding the
    value-operand memop redex, run state verbatim. -/
theorem step_ctx_memop_eval_ws {e : CoreExpr} {ctx : context}
    {mop : memop} {pe1 pe2 : generic_pexpr Unit sym} {v1 v2 : value}
    (hd : Decomp e ctx (memopRedex mop [pe1, pe2]))
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
      ∀ rs, m rs = Result (Defined { th with
        arena := apply_ctx ctx (Expr [] (Ememop mop
          [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)])) }, rs) := by
  have hget : get_ctx th.arena = [(ctx, memopRedex mop [pe1, pe2])] := by
    rw [harena]; exact hd.get_ctx_default hsz
  unfold step_ctx
  dsimp only
  rw [hget]
  simp only [List.map_cons, List.map_nil]
  unfold memopRedex
  cases ctx <;>
    (dsimp only [one_step0]
     rw [show is_irreducible (Expr ([] : List annot) (Ememop mop [pe1, pe2]))
       = false from rfl]
     dsimp only [get_loc]
     rw [hnv]
     simp only [Bool.false_eq_true, if_false]
     refine ⟨_, _, rfl, fun rs => ?_⟩
     rw [stExceptUndef_bind_apply, stExceptUndef_bind_apply,
       mapM_eval1_bridge (tds := tds) (σ := σ) (file := file)
         _ ?_ hv1 hd1 hv2 hd2 rs] <;>
       first
         | rfl
         | (intro pe rs'
            rfl))

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
which is what keeps the next round's jump certifiable. -/
theorem loop_step_frag {M₀ : MachineCtx}
    (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty)
    {Q : LabelMap} (hlb : M₀.labels = Q)
    {p : sym} {th₀ : thread_state} (hproc : th₀.current_proc_opt = some p)
    (fl : Nat) (acc : Fmap thread_id (List core_step2))
    {dst : driver_state} {e e' : CoreExpr} {ev0 : Fmap sym value}
    {evs : List (Fmap sym value)} {ρ' : EnvStack} {σ' : Mem}
    (hth : dst.core_state0.thread_states =
      [(0, (none, { th₀ with arena := e, env := ev0 :: evs }))])
    (hext : dst.core_extern = fmapEmpty)
    (hQd : LabeledAt dst.core_run_state0 p Q)
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M₀ (e, ev0 :: evs, dst.layout_state) (e', ρ', σ')) :
    ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
      rs'.labeled = dst.core_run_state0.labeled ∧
      runOne (drive_nonmemory_steps_aux2_lemFuel (Nat.succ fl)
          fmapEmpty acc [0]) dst =
        runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0])
          { dst with
              core_state0 := update_thread_state 0
                { th₀ with arena := e', env := ρ' } dst.core_state0,
              layout_state := σ',
              core_run_state0 := rs', trace := tr,
              dr_step_counter := ctr } := by
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
      rw [htd] at hmv hmem
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot [DA_pos [] fp]
          (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      have hsteps := step_ctx_store hd hsz fmapEmpty hmv
        dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
      rw [hccall] at hsteps
      refine ⟨{ dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_store (requestLoc { th₀ with arena := e, env := ev0 :: evs } loc) none ty lk pv mv
          :: dst.trace, dst.dr_step_counter,
        rfl, ?_⟩
      exact loop_step_action fl fmapEmpty acc hth hsteps
        (ars_store_active (tid := 0)
          (aid := dst.core_run_state0.aid_supply) hmem)
    | @load loc ann ty pv mo =>
      obtain ⟨fp, mval, σ'', hmem, hout⟩ := hr.load_inv
      rw [htd] at hmem
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Eannot [DA_pos [] fp]
          (Expr [] (Epure (Pexpr [] () (PEval
            (valueFromMemValue mval).2))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      have hsteps := step_ctx_load hd hsz fmapEmpty
        dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
      rw [hccall] at hsteps
      refine ⟨{ dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_load (requestLoc { th₀ with arena := e, env := ev0 :: evs } loc) none ty pv mval
          :: dst.trace, dst.dr_step_counter,
        rfl, ?_⟩
      exact loop_step_action fl fmapEmpty acc hth hsteps
        (ars_load_active (tid := 0)
          (aid := dst.core_run_state0.aid_supply) hmem)
    | @create loc ann align ty pref =>
      obtain ⟨pv, σ'', hmem, hout⟩ := hr.create_inv
      rw [htd] at hmem
      obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Epure (Pexpr [] ()
          (PEval (Vobject (OVpointer pv))))) ∧
          ρ' = ev0 :: evs ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2 h3
      have hsteps := step_ctx_create hd hsz fmapEmpty
        dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
      rw [hccall] at hsteps
      refine ⟨{ dst.core_run_state0 with aid_supply :=
          dst.core_run_state0.aid_supply + 1 },
        ME_allocate_object 0 pref align ty none pv :: dst.trace,
        dst.dr_step_counter, rfl, ?_⟩
      exact loop_step_action fl fmapEmpty acc hth hsteps
        (ars_create_active (tid := 0)
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
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_beta_pure hd hsz fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl rfl)
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
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_beta_annot hd hsz fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl rfl)
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
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_wseq_pure hd hsz fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl rfl)
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
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_wseq_annot hd hsz fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl rfl)
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
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_merge hd hirr hsz fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl)
      · rw [show annotRooted (Expr ([] : List annot) (Eannot ds2 b)) = true
          from rfl] at hg
        cases hg
    | save sb ps body =>
      have hdep : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel := by
        cases hfr with
        | save _ hdep _ => exact hdep
      rcases hr.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
          ⟨cvals, hnvS, hvals, hout⟩
      · obtain ⟨h1, h2, h3⟩ : r' = body ∧
            ρ' = bindSaveParams ps cvals (ev0 :: evs) ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_save hd hsz hvals fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl rfl)
      · obtain ⟨h1, h2, h3⟩ : r' = saveRedex sb (saveParamsWithValues ps cvals) body ∧
            ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
          simpa [Prod.mk.injEq, saveRedex] using hout
        subst h1 h2 h3
        rw [htd, hex] at hvals
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_save_eval_ws hd hsz hnvS hdep
          fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
          (by rw [hext]; exact hvals)
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
          (hm dst.core_run_state0)
    | if_ g e2 e3 =>
      have hdg : peDepth g ≤ lemDefaultFuel := by
        cases hfr with
        | if_ _ hdg _ _ => exact hdg
      rcases hr.if_inv with ⟨hg, hout⟩ | ⟨hg, hout⟩
      · obtain ⟨h1, h2, h3⟩ : r' = e2 ∧ ρ' = ev0 :: evs ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        rw [htd, hex] at hg
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_true_ws hd hsz hdg
          fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
          (by rw [hext]; exact hg)
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_withrs_tau fl fmapEmpty acc hth hsteps
          (hm dst.core_run_state0)
      · obtain ⟨h1, h2, h3⟩ : r' = e3 ∧ ρ' = ev0 :: evs ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        rw [htd, hex] at hg
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_if_false_ws hd hsz hdg
          fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
          (by rw [hext]; exact hg)
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_withrs_tau fl fmapEmpty acc hth hsteps
          (hm dst.core_run_state0)
    | case_ pe pats =>
      cases hfr with
      | case_value hbr hbsz =>
        obtain ⟨cval', e'', hv, hsel, hout⟩ := hr.case_inv
        obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
        obtain ⟨h1, h2, h3⟩ : r' = e'' ∧ ρ' = ev0 :: evs ∧
            σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_case_value hd hsz hsel fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl)
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
      rw [htd, hex] at hv
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_pure_sym_ws hd hsz
        fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv)
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
        rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
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
      rw [htd, hex] at hv2
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_load_eval_ws hd hsz hnv2 hp2 hd2
        fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv2)
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
        rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
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
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_beta_spec_pure hd hsz fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl rfl)
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
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_beta_spec_annot hd hsz fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl rfl)
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
          have hsteps := step_ctx_memop hd hsz rfl rfl fmapEmpty
            dst.layout_state dst.core_file dst.core_extern 0 none
            { th₀ with arena := e, env := ev0 :: evs } rfl
          rw [hccall] at hsteps
          refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter,
            rfl, ?_⟩
          exact loop_step_memop fl fmapEmpty acc hth hsteps
            (ars_memop_active fmapEmpty (by
              rw [eqPtrval_loc_irrel _ default pv1 pv2]; exact hmem))
      | memop_op hnvF hp1 hp2 hpd1 hpd2 =>
        obtain ⟨v1, v2, hv1', hv2', hout⟩ := hr.memop_op_inv hnvF
        obtain ⟨h1, h2, h3⟩ : r' = Expr [] (Ememop PtrEq
            [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) ∧
            ρ' = ev0 :: evs ∧ σ' = dst.layout_state := by
          simpa [Prod.mk.injEq] using hout
        subst h1 h2 h3
        rw [htd, hex] at hv1' hv2'
        obtain ⟨s, m, hsteps, hm⟩ := step_ctx_memop_eval_ws hd hsz hnvF
          hpd1 hpd2 fmapEmpty dst.layout_state dst.core_file
          dst.core_extern 0 none
          { th₀ with arena := e, env := ev0 :: evs } rfl
          (by rw [hext]; exact hv1') (by rw [hext]; exact hv2')
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
          (hm dst.core_run_state0)
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
      rw [htd, hex] at hv2 hv3
      obtain ⟨s, m, hsteps, hm⟩ := step_ctx_store_eval_ws hd hsz hnvR
        hp2 hp3 hpd2 hpd3 fmapEmpty dst.layout_state dst.core_file
        dst.core_extern 0 none
        { th₀ with arena := e, env := ev0 :: evs } rfl
        (by rw [hext]; exact hv2) (by rw [hext]; exact hv3)
      refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
        rfl, ?_⟩
      exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
        (hm dst.core_run_state0)
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
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
          rfl, ?_⟩
        exact loop_step_tau fl fmapEmpty acc hth
          (step_ctx_beta_sym_pure hd hsz fmapEmpty dst.layout_state
            dst.core_file dst.core_extern 0 none _ rfl rfl)
  · -- the jump disjunct: the context is discarded, the label read
    -- resolves in the DRIVER'S run state through the tie hQd
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hr.jump_inv (by rfl)
    have hdep : ∀ pe' ∈ pes, peDepth pe' ≤ lemDefaultFuel := by
      cases hfr with
      | run _ hdep => exact hdep
    rw [hlb] at hl
    rw [htd, hex] at hvs
    obtain ⟨h1, h2, h3⟩ : e' = cont ∧
        ρ' = bindArgs params vs (ev0 :: evs) ∧ σ' = dst.layout_state := by
      simpa [Prod.mk.injEq] using hout
    subst h1 h2 h3
    obtain ⟨s, m, hsteps, hm⟩ := step_ctx_run_ws hd hsz hl hdep
      fmapEmpty dst.layout_state dst.core_file dst.core_extern 0 none p
      { th₀ with arena := e, env := ev0 :: evs } rfl hproc
      (by rw [hext]; exact hvs)
    refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter + 1,
      rfl, ?_⟩
    exact loop_step_withrs_eval fl fmapEmpty acc hth hsteps
      (hm dst.core_run_state0
        (by rw [hext, resolveExtern_empty]; exact hQd))

end CerberusHeapLang
