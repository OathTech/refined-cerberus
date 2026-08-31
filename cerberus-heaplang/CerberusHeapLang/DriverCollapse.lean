/-
CerberusHeapLang.DriverCollapse — Extension D obligations D1-D3:
the PRODUCTION driver pipeline collapsed onto the spike's drive loop,
for fragment configurations.

- D1 SCHEDULER COLLAPSE: the production driver's round structure is
  `driver2` (Driver.lean:381-386) → `new_drive_core_threads`
  (Driver.lean:355) → `drive_nonmemory_steps_aux2` (Driver.lean:346-351),
  the fuelled per-thread loop {step_ctx → find_can_advance →
  advance_step}. For a single-threaded state whose thread holds a
  fragment configuration, ONE iteration of that loop is exactly the
  spike drive-loop body: the step_ctx singleton (the per-rule
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
  Step_done2 arm (Driver.lean:377, `prepare_exit`).
  The iteration lemmas (`loop_step_tau`/`loop_step_action`/
  `loop_step_done`) prove this by unfolding the driver's own round
  functions; `prod_loop_done` iterates them: production driving = the
  spike drive, for fragment configurations (single-threaded,
  parent-less, stack-empty — the D14 partition's read set).

- D2 ND COLLAPSE: on the fragment the whole driver computation is a
  branch-free ndM tree — every node the fragment path crosses is a
  single-layer `NDactive`/`NDkilled` state transformer (nd_return/
  nd_get/nd_update/nd_read: Nondeterminism.lean:184-215; the memM ops:
  recon §2.3; `pick` on a SINGLETON list: Nondeterminism.lean:276,
  `NDactive`, no NDnd node), and `nd_bind`/`liftND` compose such
  layers into one layer (`runOne_bind_active`/`runOne_liftMem_active`
  below — each bind spends one layer of its own fresh
  `nd_bind_lemFuel` budget, never accumulating). `runND`
  (CerbND.lean:89-138) on a one-layer active tree is the singleton
  execution (`runND_active`). Branch-freeness per construct is
  engine_complete's singleton step list; these lemmas lift it through
  the ndM structure.

- D3 READOUT: `finalize` (Driver.lean:423) on the PROGRAM-DONE state:
  `prepare_exit` (Driver.lean:372) parks the delivered value as
  `mk_value_e v` in the single surviving thread; `to_pure`
  (Core_aux.lean:570) strips the Epure node; `Driver.hack`
  (Driver.lean:390-395) steps `step_eval_pexpr` (Core_eval.lean:142),
  whose PEval arm returns the pexpr unchanged, and `valueFromPexpr`
  (Core_aux.lean:472) reads the value back — `hack_value`/
  `finalize_done` below. The value delivered by Step_done2 is always
  the BARE value form (the REMOVE-ANNOT tau precedes PROGRAM-DONE —
  Adequacy.lean D20), so the annot value form never reaches `hack`;
  composition with the REMOVE-ANNOT readout happens inside
  `prod_loop_done`'s value protocol, exactly as in `drive`.

FUEL: the driver functions run at their production budgets
(lemDefaultFuel = 10^6). `nd_bind`/`liftND` budgets are spent per
LAYER of one bind and never accumulate across the run;
`drive_nonmemory_steps_aux2`'s budget is spent once per loop
iteration, so statements carry `n + 2 ≤ lemDefaultFuel` (n drive
steps + the done-recording and drain iterations); `driver2`'s budget
is spent once per non-advanceable step (exactly one: Step_done2);
get_ctx budgets are the inherited `esize` side conditions
(Soundness.lean FUEL HONESTY). At insufficient fuel the production
value is the opaque `fuelExhausted` leaf — nothing is provable there,
fail-closed by construction (D19); this is why the production-entry
theorem carries a termination-within-budget hypothesis (fuel
parametricity is out of scope for Extension D — recorded in the
report).
-/
import CerberusHeapLang.Adequacy
import Driver
import CerbND

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-! ## The runOne layer (D2): one-layer application of an ndM tree -/

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
    (hars : runOne (action_request_sequential2 loc 0
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
theorem ars_store_active {loc : CerbLocation.Loc} {mo : memory_order}
    {ty : ctype} {lk : Bool} {pv : CerbMem.PointerValue} {mv : CerbMem.MemValue}
    {k : Nat → CerbMem.Footprint → thread_state} {tid aid : Nat}
    {dst : driver_state} {fp : CerbMem.Footprint} {σ' : Mem}
    (happ : applyMemM (CerbMem.storeM loc ty lk pv mv) dst.layout_state =
      some (fp, σ')) :
    runOne (action_request_sequential2 loc tid aid
        (StoreRequest2 mo ty lk pv mv k)) dst =
      (NDactive (), { dst with
        layout_state := σ',
        trace := ME_store loc none ty lk pv mv :: dst.trace,
        core_state0 := update_thread_state tid (k aid fp) dst.core_state0 }) := by
  unfold action_request_sequential2
  dsimp only
  refine (runOne_bind_active (z := fp) (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (runOne_of_applyMemM happ))).trans ?_
  refine (runOne_bind_active (z := (none : Option String))
    (s' := { dst with layout_state := σ' })
    (runOne_liftMem_active (by rfl))).trans ?_
  rfl

/-- LoadRequest2 discharge, active. -/
theorem ars_load_active {loc : CerbLocation.Loc} {mo : memory_order}
    {ty : ctype} {pv : CerbMem.PointerValue}
    {k : Nat → CerbMem.Footprint → CerbMem.MemValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {fp : CerbMem.Footprint}
    {mval : CerbMem.MemValue} {σ' : Mem}
    (happ : applyMemM (CerbMem.loadM loc ty pv) dst.layout_state =
      some ((fp, mval), σ')) :
    runOne (action_request_sequential2 loc tid aid
        (LoadRequest2 mo ty pv k)) dst =
      (NDactive (), { dst with
        layout_state := σ',
        trace := ME_load loc none ty pv mval :: dst.trace,
        core_state0 := update_thread_state tid (k aid fp mval) dst.core_state0 }) := by
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
theorem ars_create_active {loc : CerbLocation.Loc} {pref : prefix0}
    {align : CerbMem.IntegerValue} {ty : ctype} {reqAddr : Option Int}
    {initOpt : Option CerbMem.MemValue}
    {k : Nat → CerbMem.PointerValue → thread_state}
    {tid aid : Nat} {dst : driver_state} {pv : CerbMem.PointerValue} {σ' : Mem}
    (happ : applyMemM (CerbMem.allocateObject 0 pref align ty reqAddr initOpt)
        dst.layout_state = some (pv, σ')) :
    runOne (action_request_sequential2 loc tid aid
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

/-! ## drive one-step unfolds (the spike drive side of the simulation) -/

theorem drive_step_next {aids : Nat → Nat} {n : Nat} {th th' : thread_state}
    {σ σ' : Mem}
    (h : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
      (dischargeStep (aids 0) spikeRunState σ) = [.next th' σ']) :
    drive aids (n+1) th σ = drive (fun i => aids (i+1)) n th' σ' := by
  rw [drive.eq_def]
  dsimp only
  rw [h]

theorem drive_step_done {aids : Nat → Nat} {n : Nat} {th : thread_state}
    {σ : Mem} {v : value}
    (h : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
      (dischargeStep (aids 0) spikeRunState σ) = [.done v]) :
    drive aids (n+1) th σ = .done v σ := by
  rw [drive.eq_def]
  dsimp only
  rw [h]

theorem drive_step_killed {aids : Nat → Nat} {n : Nat} {th : thread_state}
    {σ : Mem} {r : kill_reason mem_error}
    (h : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
      (dischargeStep (aids 0) spikeRunState σ) = [.killed r]) :
    drive aids (n+1) th σ = .killed r := by
  rw [drive.eq_def]
  dsimp only
  rw [h]

theorem drive_step_error {aids : Nat → Nat} {n : Nat} {th : thread_state}
    {σ : Mem} {s : String}
    (h : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
      (dischargeStep (aids 0) spikeRunState σ) = [.error s]) :
    drive aids (n+1) th σ = .stuck := by
  rw [drive.eq_def]
  dsimp only
  rw [h]

theorem drive_step_off {aids : Nat → Nat} {n : Nat} {th : thread_state}
    {σ : Mem}
    (h : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
      (dischargeStep (aids 0) spikeRunState σ) = [.offFragment]) :
    drive aids (n+1) th σ = .stuck := by
  rw [drive.eq_def]
  dsimp only
  rw [h]

/-! ## THE LOOP SIMULATION (D1 iterated): production driving = the
spike drive, for fragment configurations.

The context is the production one: an arbitrary base thread `th₀`
whose D14 read-set conditions hold (empty call stack — PROGRAM-DONE's
one read; nonempty env — the beta rules' one read), an arbitrary
file/extern in the driver state (unread on the fragment), tid 0, no
parent, tagDefs fmapEmpty. The drive hypothesis is ∀-quantified over
the action-id supply because the production supply starts at the
opaque `initial_core_run_state` seed (Core_run_aux.lean:395,
runEffectful) — the fragment ignores aids (D2/slice A), so the
∀-form is what the exhibits prove anyway. -/
theorem prod_loop_done (th₀ : thread_state)
    (hstack : th₀.stack0 = Stack_empty)
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    (henv : th₀.env = ev0 :: evs)
    (v : value) (σfin : Mem) :
    ∀ (n fl : Nat) (e : CoreExpr) (dst : driver_state)
      (acc : Fmap thread_id (List core_step2)),
      FragP e →
      dst.core_state0.thread_states = [(0, (none, { th₀ with arena := e }))] →
      esize e + n ≤ lemDefaultFuel →
      n + 2 ≤ fl →
      (∀ aids : Nat → Nat,
        drive aids n (spikeThread e) dst.layout_state = .done v σfin) →
      ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
        runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst =
          (NDactive (fmapAddBy defaultCompare 0 [Step_done2 v] acc),
           { dst with
              core_state0 := { dst.core_state0 with thread_states :=
                [(0, (none, { th₀ with arena := ofVal (.pure v) }))] },
              layout_state := σfin,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr }) := by
  intro n
  induction n with
  | zero =>
    intro fl e dst acc _ _ _ _ hdrive
    exact absurd (hdrive fun _ => 0) (fun h => DriveResult.noConfusion h)
  | succ n ih =>
    intro fl e dst acc hf hth hfe hfl hdrive
    have hsz : esize e ≤ lemDefaultFuel := by omega
    cases hv : toVal e with
    | some w =>
      have he := ofVal_of_toVal hv
      subst he
      cases w with
      | pure v' =>
        -- PROGRAM-DONE on both sides.
        have hd0 := hdrive (fun _ => 0)
        rw [drive_step_done (v := v') (by
          rw [drive_scrutinee]
          unfold engineOutcomes
          rw [engineSteps_done]
          rfl)] at hd0
        obtain ⟨rfl, rfl⟩ : v' = v ∧ dst.layout_state = σfin := by
          cases hd0; exact ⟨rfl, rfl⟩
        obtain ⟨f, rfl⟩ : ∃ f, fl = f + 2 := ⟨fl - 2, by omega⟩
        refine ⟨dst.core_run_state0, dst.trace, dst.dr_step_counter, ?_⟩
        rw [loop_step_done f fmapEmpty acc hth
          (step_ctx_done _ fmapEmpty dst.layout_state dst.core_file
            dst.core_extern 0 { th₀ with arena := ofVal (.pure v') } rfl hstack)]
        rw [← hth]
      | annot ds v' =>
        -- the REMOVE-ANNOT tau (D20's value protocol), both sides.
        obtain ⟨f, rfl⟩ : ∃ f, fl = f + 1 := ⟨fl - 1, by omega⟩
        have hdrive' : ∀ aids : Nat → Nat,
            drive aids n (spikeThread (ofVal (.pure v'))) dst.layout_state =
              .done v σfin := by
          intro aids
          have h := hdrive (fun i => Nat.casesOn i 0 aids)
          rw [drive_step_next (th' := spikeThread (ofVal (.pure v')))
            (σ' := dst.layout_state) (by
              rw [drive_scrutinee]
              unfold engineOutcomes
              rw [engineSteps_remove_annot]
              rfl)] at h
          exact h
        rw [loop_step_tau f fmapEmpty acc hth
          (step_ctx_remove_annot ds v' fmapEmpty dst.layout_state dst.core_file
            dst.core_extern 0 none { th₀ with arena := ofVal (.annot ds v') } rfl)]
        have hth' : (update_thread_state 0
            { th₀ with arena := ofVal (.pure v') }
            dst.core_state0).thread_states =
            [(0, (none, { th₀ with arena := ofVal (.pure v') }))] := by
          rw [update_thread_state_single _ _ _ hth]
        obtain ⟨rs', tr, ctr, hrun⟩ := ih f (ofVal (.pure v'))
          ({ { dst with dr_step_counter := dst.dr_step_counter + 1 } with core_state0 := update_thread_state 0 { th₀ with arena := ofVal (.pure v') } dst.core_state0 }) acc
          (fragP_ofVal _) hth' (by simp at hfe ⊢; omega) (by omega) hdrive'
        exact ⟨rs', tr, ctr, hrun⟩
    | none =>
      obtain ⟨ctx, r, hd⟩ := hf.decomp hv
      have hccall := hd.unseq_ccall_false
      obtain ⟨f, rfl⟩ : ∃ f, fl = f + 1 := ⟨fl - 1, by omega⟩
      -- one shared continuation for every Step-matched successor
      have step_case : ∀ (eNext : CoreExpr) (σ' : Mem) (dst' : driver_state),
          Step (e, spikeEnv, dst.layout_state) (eNext, spikeEnv, σ') →
          dst'.core_state0.thread_states =
            [(0, (none, { th₀ with arena := eNext }))] →
          dst'.layout_state = σ' →
          dst'.core_state0.io = dst.core_state0.io →
          dst'.core_file = dst.core_file →
          dst'.core_extern = dst.core_extern →
          dst'.concurrency_state = dst.concurrency_state →
          dst'.fs_state0 = dst.fs_state0 →
          dst'.symbolic_assoc = dst.symbolic_assoc →
          dst'.blocked = dst.blocked →
          (∀ aids : Nat → Nat,
            drive aids n (spikeThread eNext) σ' = .done v σfin) →
          ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
            runOne (drive_nonmemory_steps_aux2_lemFuel f fmapEmpty acc [0]) dst' =
              (NDactive (fmapAddBy defaultCompare 0 [Step_done2 v] acc),
               { dst with
                  core_state0 := { dst.core_state0 with thread_states :=
                    [(0, (none, { th₀ with arena := ofVal (.pure v) }))] },
                  layout_state := σfin,
                  core_run_state0 := rs', trace := tr,
                  dr_step_counter := ctr }) := by
        intro eNext σ' dst' hstep hth' hσ' hio hcf hce hcc hfs hsa hbl hdrive'
        have hfrag' : FragP eNext := hf.step hstep
        have hesz : esize eNext ≤ esize e + 1 := by
          have := hstep.esize_succ; simpa using this
        obtain ⟨rs', tr, ctr, hrun⟩ := ih f eNext dst' acc hfrag' hth'
          (by omega) (by omega) (by rw [hσ']; exact hdrive')
        refine ⟨rs', tr, ctr, ?_⟩
        rw [hrun]
        -- transport the final record from dst' to dst: every carried
        -- component is either overridden or equal by the hypotheses
        rcases dst with ⟨cf, ce, cs, crs, ls, cc, fs, tr0, sa, bl, ctr0⟩
        rcases dst' with ⟨cf', ce', cs', crs', ls', cc', fs', tr0', sa', bl', ctr0'⟩
        rcases cs with ⟨ths, io⟩
        rcases cs' with ⟨ths', io'⟩
        simp only at hio hcf hce hcc hfs hsa hbl
        subst hio hcf hce hcc hfs hsa hbl
        rfl
      -- Step-stuckness refutes the drive hypothesis (via
      -- engine_complete's refusal protocol — the engine's one behavior
      -- at a stuck fragment configuration is a refusal, and a refusal
      -- never yields `.done`).
      have refute : (∀ out, ¬ Step (e, spikeEnv, dst.layout_state) out) → False := by
        intro hstuck
        obtain ⟨o, houts, hmatch⟩ :=
          engine_complete 0 dst.layout_state fmapEmpty [] hf hsz
        cases hmatch with
        | step hs => exact hstuck _ hs
        | removeAnnot h => rw [h, toVal_ofVal] at hv; cases hv
        | done h => rw [h, toVal_ofVal] at hv; cases hv
        | refused href hnostep hnv =>
          have hscr := (drive_scrutinee 0 e dst.layout_state).trans houts
          cases o with
          | next th' σ' => exact href.elim
          | done v'' => exact href.elim
          | killed r =>
            have h := hdrive (fun _ => 0)
            rw [drive_step_killed hscr] at h
            cases h
          | error s =>
            have h := hdrive (fun _ => 0)
            rw [drive_step_error hscr] at h
            cases h
          | offFragment =>
            have h := hdrive (fun _ => 0)
            rw [drive_step_off hscr] at h
            cases h
      cases hd.redex with
      | @store loc ann lk ty pv cv mo hlib =>
        cases hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv with
        | none =>
          exact (refute (fun out hstep => by
            obtain ⟨r', ρr, σr, hr, _⟩ := hd.step_factor hstep
            obtain ⟨mv', _, _, hmv', _, _⟩ := hr.store_inv
            rw [hmv] at hmv'
            cases hmv')).elim
        | some mv =>
          cases happ : applyMemM (CerbMem.storeM loc ty lk pv mv)
              dst.layout_state with
          | none =>
            exact (refute (fun out hstep => by
              obtain ⟨r', ρr, σr, hr, _⟩ := hd.step_factor hstep
              obtain ⟨mv', fp', σ'', hmv', happ', _⟩ := hr.store_inv
              rw [hmv] at hmv'
              obtain rfl : mv = mv' := Option.some.inj hmv'
              rw [happ] at happ'
              cases happ')).elim
          | some p =>
            rcases p with ⟨fp, σ'⟩
            have hstep : Step (e, spikeEnv, dst.layout_state)
                (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                  (Expr [] (Epure (Pexpr [] () (PEval Vunit)))))),
                 spikeEnv, σ') :=
              hd.rebuild (Step.store_canonical hmv happ)
            have hdrive' : ∀ aids : Nat → Nat,
                drive aids n (spikeThread (apply_ctx ctx
                  (Expr [] (Eannot [DA_pos [] fp]
                    (Expr [] (Epure (Pexpr [] () (PEval Vunit)))))))) σ' =
                  .done v σfin := by
              intro aids
              have h := hdrive (fun i => Nat.casesOn i 0 aids)
              rw [drive_step_next (by
                rw [drive_scrutinee]
                unfold engineOutcomes
                rw [engineSteps_store hd hsz hlib hmv]
                simp only [List.map_cons, List.map_nil]
                rw [dischargeStep_store_active happ])] at h
              exact h
            have hsteps := step_ctx_store hd hsz hlib fmapEmpty hmv
              dst.layout_state dst.core_file dst.core_extern 0 none
              { th₀ with arena := e } rfl
            rw [hccall] at hsteps
            rw [loop_step_action f fmapEmpty acc hth hsteps
              (ars_store_active (tid := 0)
                (aid := dst.core_run_state0.aid_supply) happ)]
            refine step_case _ σ' _ hstep ?_ rfl rfl rfl rfl rfl rfl rfl rfl
              hdrive'
            show (update_thread_state 0 _ dst.core_state0).thread_states = _
            rw [update_thread_state_single _ _ _ hth]
      | @load loc ann ty pv mo hlib =>
        cases happ : applyMemM (CerbMem.loadM loc ty pv) dst.layout_state with
        | none =>
          exact (refute (fun out hstep => by
            obtain ⟨r', ρr, σr, hr, _⟩ := hd.step_factor hstep
            obtain ⟨fp', mval', σ'', happ', _⟩ := hr.load_inv
            rw [happ] at happ'
            cases happ')).elim
        | some p =>
          rcases p with ⟨⟨fp, mval⟩, σ'⟩
          have hstep : Step (e, spikeEnv, dst.layout_state)
              (apply_ctx ctx (Expr [] (Eannot [DA_pos [] fp]
                (Expr [] (Epure (Pexpr [] () (PEval
                  (valueFromMemValue mval).2)))))), spikeEnv, σ') :=
            hd.rebuild (Step.load_canonical happ)
          have hdrive' : ∀ aids : Nat → Nat,
              drive aids n (spikeThread (apply_ctx ctx
                (Expr [] (Eannot [DA_pos [] fp]
                  (Expr [] (Epure (Pexpr [] () (PEval
                    (valueFromMemValue mval).2)))))))) σ' =
                .done v σfin := by
            intro aids
            have h := hdrive (fun i => Nat.casesOn i 0 aids)
            rw [drive_step_next (by
              rw [drive_scrutinee]
              unfold engineOutcomes
              rw [engineSteps_load hd hsz hlib]
              simp only [List.map_cons, List.map_nil]
              rw [dischargeStep_load_active happ])] at h
            exact h
          have hsteps := step_ctx_load hd hsz hlib fmapEmpty
            dst.layout_state dst.core_file dst.core_extern 0 none
            { th₀ with arena := e } rfl
          rw [hccall] at hsteps
          rw [loop_step_action f fmapEmpty acc hth hsteps
            (ars_load_active (tid := 0)
              (aid := dst.core_run_state0.aid_supply) happ)]
          refine step_case _ σ' _ hstep ?_ rfl rfl rfl rfl rfl rfl rfl rfl
            hdrive'
          show (update_thread_state 0 _ dst.core_state0).thread_states = _
          rw [update_thread_state_single _ _ _ hth]
      | @create loc ann align ty pref hlib =>
        cases happ : applyMemM (CerbMem.allocateObject 0 pref align ty none none)
            dst.layout_state with
        | none =>
          exact (refute (fun out hstep => by
            obtain ⟨r', ρr, σr, hr, _⟩ := hd.step_factor hstep
            obtain ⟨pv', σ'', happ', _⟩ := hr.create_inv
            rw [happ] at happ'
            cases happ')).elim
        | some p =>
          rcases p with ⟨pv, σ'⟩
          have hstep : Step (e, spikeEnv, dst.layout_state)
              (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval
                (Vobject (OVpointer pv)))))), spikeEnv, σ') :=
            hd.rebuild (Step.create_canonical happ)
          have hdrive' : ∀ aids : Nat → Nat,
              drive aids n (spikeThread (apply_ctx ctx
                (Expr [] (Epure (Pexpr [] () (PEval
                  (Vobject (OVpointer pv)))))))) σ' =
                .done v σfin := by
            intro aids
            have h := hdrive (fun i => Nat.casesOn i 0 aids)
            rw [drive_step_next (by
              rw [drive_scrutinee]
              unfold engineOutcomes
              rw [engineSteps_create hd hsz hlib]
              simp only [List.map_cons, List.map_nil]
              rw [dischargeStep_create_active (reqAddr := get_with_address [])
                happ])] at h
            exact h
          have hsteps := step_ctx_create hd hsz hlib fmapEmpty
            dst.layout_state dst.core_file dst.core_extern 0 none
            { th₀ with arena := e } rfl
          rw [hccall] at hsteps
          rw [loop_step_action f fmapEmpty acc hth hsteps
            (ars_create_active (tid := 0)
              (aid := dst.core_run_state0.aid_supply) happ)]
          refine step_case _ σ' _ hstep ?_ rfl rfl rfl rfl rfl rfl rfl rfl
            hdrive'
          show (update_thread_state 0 _ dst.core_state0).thread_states = _
          rw [update_thread_state_single _ _ _ hth]
      | @beta_pure pa bty v' e2 =>
        have hstep : Step (e, spikeEnv, dst.layout_state) (apply_ctx ctx e2,
            spikeEnv, dst.layout_state) := hd.rebuild Step.sseq_pure
        have hdrive' : ∀ aids : Nat → Nat,
            drive aids n (spikeThread (apply_ctx ctx e2)) dst.layout_state =
              .done v σfin := by
          intro aids
          have h := hdrive (fun i => Nat.casesOn i 0 aids)
          rw [drive_step_next (by
            rw [drive_scrutinee]
            unfold engineOutcomes
            rw [engineSteps_beta_pure hd hsz fmapEmpty []]
            rfl)] at h
          exact h
        rw [loop_step_tau f fmapEmpty acc hth
          (step_ctx_beta_pure hd hsz fmapEmpty dst.layout_state dst.core_file
            dst.core_extern 0 none { th₀ with arena := e } rfl henv)]
        refine step_case _ dst.layout_state _ hstep ?_ rfl rfl rfl rfl rfl rfl
          rfl rfl hdrive'
        show (update_thread_state 0 _ dst.core_state0).thread_states = _
        rw [update_thread_state_single _ _ _ hth]
      | @beta_annot pa bty ds v' e2 =>
        have hstep : Step (e, spikeEnv, dst.layout_state)
            (apply_ctx ctx (Expr [] (Eannot ds e2)), spikeEnv,
              dst.layout_state) :=
          hd.rebuild Step.sseq_annot
        have hdrive' : ∀ aids : Nat → Nat,
            drive aids n (spikeThread (apply_ctx ctx (Expr [] (Eannot ds e2))))
              dst.layout_state = .done v σfin := by
          intro aids
          have h := hdrive (fun i => Nat.casesOn i 0 aids)
          rw [drive_step_next (by
            rw [drive_scrutinee]
            unfold engineOutcomes
            rw [engineSteps_beta_annot hd hsz fmapEmpty []]
            rfl)] at h
          exact h
        rw [loop_step_tau f fmapEmpty acc hth
          (step_ctx_beta_annot hd hsz fmapEmpty dst.layout_state dst.core_file
            dst.core_extern 0 none { th₀ with arena := e } rfl henv)]
        refine step_case _ dst.layout_state _ hstep ?_ rfl rfl rfl rfl rfl rfl
          rfl rfl hdrive'
        show (update_thread_state 0 _ dst.core_state0).thread_states = _
        rw [update_thread_state_single _ _ _ hth]
      | @merge ds1 ds2 b hirr =>
        have hstep : Step (e, spikeEnv, dst.layout_state)
            (apply_ctx ctx (Expr [] (Eannot (ds1 ++ ds2) b)),
              spikeEnv, dst.layout_state) := hd.rebuild Step.annot_merge
        have hdrive' : ∀ aids : Nat → Nat,
            drive aids n
              (spikeThread (apply_ctx ctx (Expr [] (Eannot (ds1 ++ ds2) b))))
              dst.layout_state = .done v σfin := by
          intro aids
          have h := hdrive (fun i => Nat.casesOn i 0 aids)
          rw [drive_step_next (by
            rw [drive_scrutinee]
            unfold engineOutcomes
            rw [engineSteps_merge hd hirr hsz]
            rfl)] at h
          exact h
        rw [loop_step_tau f fmapEmpty acc hth
          (step_ctx_merge hd hirr hsz fmapEmpty dst.layout_state dst.core_file
            dst.core_extern 0 none { th₀ with arena := e } rfl)]
        refine step_case _ dst.layout_state _ hstep ?_ rfl rfl rfl rfl rfl rfl
          rfl rfl hdrive'
        show (update_thread_state 0 _ dst.core_state0).thread_states = _
        rw [update_thread_state_single _ _ _ hth]

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

end CerberusHeapLang
