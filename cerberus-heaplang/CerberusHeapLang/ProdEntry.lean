/-
CerberusHeapLang.ProdEntry — the COLD START and the production-entry
theorem: statements against the shipped pipeline, from the shipped
initial state.

The pipeline under judgment is the SHIPPED one (Main.lean:857-885):

  CerbND.runND (Driver.drive tagDefs false file args)
               (initial_driver_state sup file fs).1

with `initial_driver_state` (Driver.lean:446) the PRODUCTION state
constructor — nothing hand-built enters the quantifiers: memory starts
at `CerbMem.initialMemState` (= the empty MemState), the thread pool
empty (`initial_core_state`, Core_run_aux.lean:393), and the run state
at `initial_core_run_state` (Core_run_aux.lean:406), which seeds
`sym_supply` from the entry's `sup` argument (`initial_driver_state :
Nat → file → fs_state → driver_state × Nat`, the `.1` projection
being the state and `.2` the advanced supply). Every theorem below
quantifies over the supply `sup` — the shipped `Main` seeds one
concrete stream, the theorems hold for every value, because the
fragment never reads `sym_supply`. Every theorem here has axiom set
exactly the classical trio (Audit.lean).

The setup prefix `Driver.drive` runs before `driver2`
(Driver.lean:500-513): spawn thread 0 (`driver_globals` /
`spawn_thread`, Core_run.lean:104 — tid 0 from the run state's
tid_supply), evaluate globals (none in a synthetic one-procedure
file), look up `main` in `funs`, skip argc/argv materialization
(main has no parameters), allocate-and-zero `errno` with the REAL
`allocateObject`/`storeM` on the cold memory, and park main's body as
thread 0's arena. The concrete cold-start facts (`errno_alloc_eq`
etc.) pin that prefix (`drive_after_setup`); `prodMem₀` is the memory
state at fragment start — derived through engine functions only — and
`prodMem₀_launchCoh` is the launch premise `LaunchCoh` at it, for any
plan that fits its cursor.

THE THEOREM (`prod_run_eqJ`): the production pipeline on a synthetic
one-procedure file (`prodFile e`) is EXACTLY ONE Active execution
whose value and final memory satisfy the postcondition, given the
driver-delivery fact `DriverDoneAt` that the total judgment supplies
(`wpt_driver_done_alloc`, ProdLoop.lean) and the registration tie
`LabeledAt`. Scope: single-threaded, fragment-only, total correctness
at a certified step count — plus the in-budget bound `k + 2 ≤
CerbFuel.driverFuel` (the drive cone's budget, 10^8, since the
cerberus-lean fuel arc; the bound is stated against the name the
semantics exports, `CerbFuel.driverFuel`, as the change manifest
directs). Below the bound the shipped driver's value is the kernel-
transparent kill `CerbND.fuelExhaustedKill`; the TOTAL statements here
simply do not speak there. The consumers are `exhibitA_prod`
(ProdExhibit.lean) and the three `*_production` loop theorems
(ProdLoopExhibit.lean).

THE PARTIAL THEOREM (`prod_run_safe_procs`, the fuel-lane restatement
2026-09-03): the production pipeline on the synthetic N-procedure file,
run through the semantics' fuel-parametric mirror `CerbND.drive_lemFuel
fuel` AT EVERY `fuel` — the shipped `drive` is its instance at
`CerbFuel.driverFuel`, `CerbND.drive_wrapper_defeq`, `rfl` — is EXACTLY
ONE execution, and that execution is either the fuel-exhaustion kill
(`nd_status.Killed dst' CerbND.fuelExhaustedKill`) or an Active one whose
value and final memory satisfy the postcondition, given the driver-safety
fact `DriverSafeCtl` the partial adequacy supplies (`engine_adequacy`,
Adequacy.lean) and the whole-file registration tie. No in-budget bound:
a partial statement about every run. MEASURED (the F1 record §3): the
`fuel` parameter bounds the OUTER `driver2` rounds only —
`new_drive_core_threads` (Driver.lean:355) calls the per-thread loop
through its wrapper `drive_nonmemory_steps_aux2 = _lemFuel 10^8` — so
at every `fuel ≥ 1` the statement is the one about the shipped `drive`,
and at `fuel = 0` the setup runs and `driver2_lemFuel 0` kills
(`CerbND.driver2_lemFuel_zero`).

THE REGISTRATION TIE for loops: `fib_labeledAt_production` /
`loop_labeledAt_production` derive `LabeledAt` at the PRODUCTION
initial run state from the shipped `collect_labeled_continuations_NEW`
— the loop exhibits' label maps are exactly what the production entry
computes, nothing hand-built. The production `runND` equations for the
loop RUNS themselves are the `*_production` theorems of
ProdLoopExhibit.lean, through `wpt_driver_done_alloc` → `prod_run_eqJ`.
(The former `counter_loop_certified_registration` — the counter loop over
the package loop `driveU` at that derived tie — was deleted with the loop
in the fuel-lane restatement, 2026-09-03: its content, the counter loop
at the shipped registration, is what the partial lane states at the
production context by construction.)

On `create`: an UNCONDITIONAL `wp_create` from cell ownership alone is
unprovable — `allocateObject` can kill ("out of memory",
CerbMem.lean:1479) from configurations no cell footprint constrains.
The allocation budget supplies the missing authority (K2.5): the
create rules take `allocBudget (allocCost ty align)` (Heap.lean), the
allocation-aware launchers grant a budget from real memory
(`launchResources` under `LaunchCoh` — this module proves the concrete
cold-start instance `prodMem₀_launchCoh`), and every allocating
production exhibit is a whole-program logic proof whose creates cross
the public `wpt_create` (`exhibitA_prod`, `counter_loop_certified_production`,
`list_reverse_certified_production`).
-/
import CerberusHeapLang.DriverCollapse
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.FibExhibit
import CerberusHeapLang.ProdLoop

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List
open scoped Iris.Std.PartialMap

/-! ## The synthetic one-procedure file -/

/-- The startup symbol of the synthetic file. -/
def mainSym : sym := Symbol "" 0 SD_None

/-- Main's declaration: a parameterless Proc whose body is the
    fragment program (Core.lean:1481 — `Proc loc marker ret params
    body`; Driver.drive's Proc arm parks `body` as the arena
    verbatim, Driver.lean:512). -/
def mainDecl (e : CoreExpr) : generic_fun_map_decl Unit core_run_annotation :=
  Proc CerbLocation.unknown none BTy_unit [] e

/-- The synthetic one-procedure Core file wrapping a self-contained
    fragment program: `main` only, no globals, no externs, no tags.
    Only `main`, `funs` and `globs` are read on the production path
    (main lookup, Driver.lean:508-512; globals, Driver.lean:463);
    every other field is inert context. -/
def prodFile (e : CoreExpr) : file core_run_annotation :=
  { main := some mainSym,
    calling_convention0 := default,
    tagDefs := default,
    stdlib := fmapEmpty,
    impl0 := fmapEmpty,
    globs := [],
    funs := fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      (mainDecl e) fmapEmpty,
    extern := fmapEmpty,
    funinfo := fmapEmpty,
    loop_attributes1 := default,
    visible_objects_env0 := default }

theorem prodFile_funs_lookup (e : CoreExpr) :
    fmapLookupBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      (prodFile e).funs = some (mainDecl e) := rfl

/-! ## The cold-start memory: errno allocation on initialMemState

Driver.drive allocates and zeroes `errno` (Driver.lean:512, the
`liftMem` block) before parking main's arena. On the cold state this
is the FIRST allocation: id 0 at the top-of-memory cursor
(0xFFFFFFFFFFF8 = 281474976710648 for a 4-byte int at alignment 4 —
the recon §2.5 address). -/

def errnoAddr : Int := 281474976710648

def errnoPtr : CerbMem.PointerValue := cellPtr 0 errnoAddr

/-- The zero value the driver stores into errno. -/
def zeroMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (Signed Int_) (CerbMem.integerIval 0)

/-- errno's allocation, exactly as allocateObject builds it. -/
def errnoAllocRec : CerbMem.Allocation :=
  { base := errnoAddr, size := 4, ty := some signed_int,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "errno") none,
    prefix_ := PrefOther "errno" }

/-- The engine's own errno allocation on the cold state. -/
def errnoSeeded : Option (CerbMem.PointerValue × Mem) :=
  applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "errno")
    (CerbMem.alignofIval fmapEmpty signed_int) signed_int none none)
    CerbMem.initialMemState

/-- The state after the errno allocation. -/
def σE1 : Mem :=
  match errnoSeeded with
  | some (_, σ) => σ
  | none => {}

theorem errnoSeeded_eq : errnoSeeded = some (errnoPtr, σE1) := rfl

theorem errno_alloc_eq :
    applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "errno")
      (CerbMem.alignofIval fmapEmpty signed_int) signed_int none none)
      CerbMem.initialMemState = some (errnoPtr, σE1) := errnoSeeded_eq

theorem σE1_allocations :
    σE1.allocations = (({} : Mem).allocations.insert 0 errnoAllocRec) := rfl

theorem errno_alloc_get : σE1.allocations.get? 0 = some errnoAllocRec := by
  rw [σE1_allocations]
  simp

theorem errno_bytes_len (a : Int) :
    (CerbMem.readBytesFrom σE1 a 4).length = 4 := by
  unfold CerbMem.readBytesFrom
  simp

/-- errno's ghost-shaped cell in σE1 (only used to drive
    storeM_success — errno is never a fragment cell). -/
abbrev errnoCell : SpikeCell :=
  ⟨errnoAddr, signed_int, CerbMem.readBytesFrom σE1 errnoAddr 4⟩

theorem errnoCellCoh : CellCoh fmapEmpty σE1 0 errnoCell :=
  ⟨rfl, ⟨errnoAllocRec, errno_alloc_get, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype fmapEmpty errnoCell.ty = 4 from rfl]; exact errno_bytes_len errnoAddr,
   by rw [show CerbMem.sizeofCtype fmapEmpty errnoCell.ty = 4 from rfl],
   fun _ _ => rfl⟩

theorem zero_storable {tds : CerbTags.TagDefsMap} : StorableAt tds signed_int zeroMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The memory state at fragment start: errno allocated and zeroed by
    the engine's own operations — the production cold-start memory. -/
def prodMem₀ : Mem :=
  CerbMem.writeBytesTo σE1 errnoAddr (CerbMem.memValueToBytes fmapEmpty [] zeroMval).2

theorem errno_store_eq :
    applyMemM (CerbMem.storeM fmapEmpty (CerbLocation.other "errno init") signed_int
      false errnoPtr zeroMval) σE1 =
      some (.FP .W errnoAddr (CerbMem.sizeofCtype fmapEmpty signed_int), prodMem₀) :=
  storeM_success fmapEmpty σE1 0 errnoCell zeroMval _ errnoCellCoh zero_storable

/-! ## Launch coherence at the production cold start (the CONCRETE
instance; the generic theorem is `LaunchCoh.cohG` in Adequacy.lean,
which encodes neither the errno address nor any demo's future
allocations) -/

theorem prodMem₀_nextAllocId : prodMem₀.nextAllocId = 1 := rfl

theorem prodMem₀_lastAddress : prodMem₀.lastAddress = errnoAddr := rfl

theorem prodMem₀_allocations :
    prodMem₀.allocations =
      (({} : Mem).allocations.insert 0 errnoAllocRec) := rfl

theorem prodMem₀_deadAllocations : prodMem₀.deadAllocations = [] := rfl

theorem prodMem₀_dynamicAddrs : prodMem₀.dynamicAddrs = [] := rfl

/-- THE COLD-START INVARIANT (K0, acceptance goal 3): the production
    initial memory is globally well formed. errno (id 0, below
    `nextAllocId = 1`) is the ONLY allocation, at the cursor
    (`lastAddress = errnoAddr = errnoAllocRec.base`), of size 4;
    nothing is dead; no dynamic address; the cursor is below 2^64. -/
theorem prodMem₀_memWF : MemWF prodMem₀ := by
  have hget : ∀ id : Int, prodMem₀.allocations.get? id =
      if (0 : Int) = id then some errnoAllocRec
      else ({} : Mem).allocations.get? id := by
    intro id
    rw [prodMem₀_allocations]
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
  have hempty : ∀ id : Int, ({} : Mem).allocations.get? id = none := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id al hg
    rw [hget] at hg
    split at hg
    · next h0 =>
      rw [← h0, prodMem₀_nextAllocId]
      decide
    · rw [hempty] at hg
      cases hg
  · intro id hc
    rw [prodMem₀_deadAllocations] at hc
    cases hc
  · intro id al hg
    rw [prodMem₀_deadAllocations]
    rfl
  · intro i j ai aj hne hgi hgj
    rw [hget] at hgi hgj
    split at hgi
    · next hi =>
      split at hgj
      · next hj => exact absurd (hi.symm.trans hj) hne
      · rw [hempty] at hgj
        cases hgj
    · rw [hempty] at hgi
      cases hgi
  · intro id al hg
    rw [hget] at hg
    split at hg
    · obtain rfl := Option.some.inj hg
      rw [prodMem₀_lastAddress]
      exact Int.le_refl _
    · rw [hempty] at hg
      cases hg
  · intro id al hg
    rw [hget] at hg
    split at hg
    · obtain rfl := Option.some.inj hg
      decide
    · rw [hempty] at hg
      cases hg
  · rw [prodMem₀_lastAddress]
    decide
  · rw [prodMem₀_lastAddress]
    decide
  · intro a ha
    rw [prodMem₀_dynamicAddrs] at ha
    cases ha
  · intro a ha
    rw [prodMem₀_dynamicAddrs] at ha
    cases ha

/-- Launch coherence at the production cold start: the invariant
    (`prodMem₀_memWF`) plus any budget within the actual cursor's
    headroom (`errnoAddr − 1`) launches the empty footprint
    allocation-aware (K2.5; formerly a plan fitting the cursor). -/
theorem prodMem₀_launchCoh (B : Nat)
    (hB : B ≤ headroom prodMem₀.lastAddress) :
    LaunchCoh fmapEmpty prodMem₀ (∅ : SpikeHeapF SpikeCell) B :=
  LaunchCoh.empty fmapEmpty prodMem₀ B prodMem₀_memWF hB

/-! ## The thread at fragment start (Driver.lean:512, the parked-main
thread literal) -/

def prodThread (e : CoreExpr) : thread_state :=
  { arena := e, stack0 := Stack_empty, errno := errnoPtr,
    current_loc := CerbLocation.other "Driver.drive",
    exec_loc := ELoc_normal [(mainSym, CerbLocation.other "Driver.drive")],
    env := [fmapEmpty], current_proc_opt := some mainSym }

/-- The globals-evaluation thread driver_globals spawns
    (Driver.lean:457). -/
def globalsThread : thread_state :=
  { arena := Expr [] (Epure (Pexpr [] () (PEval Vunit))),
    stack0 := Stack_empty, errno := CerbMem.nullPtrval signed_int,
    env := [fmapEmpty], current_loc := CerbLocation.unknown,
    exec_loc := ELoc_globals, current_proc_opt := none }

/-- The driver state after driver_globals on the synthetic file:
    thread 0 spawned (tid_supply ticked), nothing else moved. -/
def prodPostGlobals (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState) : driver_state :=
  { (initial_driver_state sup (prodFile e) fs).1 with
      core_state0 := { thread_states := [(0, (none, globalsThread))],
                       io := initial_io_state },
      core_run_state0 :=
        { (initial_core_run_state sup
            (collect_labeled_continuations_NEW (prodFile e))).1 with
          tid_supply := 1 } }

/-- The driver state at driver2 entry: errno allocated and zeroed,
    main's body parked as thread 0's arena. -/
def prodEntryState (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState) : driver_state :=
  { prodPostGlobals sup e fs with
      core_state0 := { thread_states := [(0, (none, prodThread e))],
                       io := initial_io_state },
      layout_state := prodMem₀ }

/-! ## The setup collapse: Driver.drive's prefix from the production
initial state to the driver2 entry, computed through the engine's own
setup functions (spawn_thread, the main lookup, the errno block). -/

theorem drive_after_setup (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstD : driver_state)
    (hdrv2 : runOne (driver2_lemFuel CerbFuel.driverFuel fmapEmpty false)
        (prodEntryState sup e fs) = (NDactive (), dstD)) :
    runOne (_root_.drive fmapEmpty false (prodFile e) args)
        ((initial_driver_state sup (prodFile e) fs).1) =
      (NDactive (finalize fmapEmpty "drive (without concur)" dstD), dstD) := by
  conv => lhs; unfold _root_.drive
  -- driver_globals: spawn thread 0, no globals
  refine (runOne_bind_active (z := (0 : Nat))
    (s' := prodPostGlobals sup e fs) (by rfl)).trans ?_
  -- main lookup on the synthetic file
  refine (runOne_bind_active (z := prodPostGlobals sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (z := mainSym) (by rfl)).trans ?_
  refine (runOne_bind_active
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e))
    (by rfl)).trans ?_
  refine (runOne_bind_active (z := e) (by rfl)).trans ?_
  -- the errno allocation block (real allocateObject/storeM on the
  -- cold memory)
  refine (runOne_bind_active (z := errnoPtr)
    (s' := { prodPostGlobals sup e fs with layout_state := prodMem₀ })
    (runOne_liftMem_active ?_)).trans ?_
  · refine (runOne_bind_active (z := errnoPtr) (s' := σE1)
      (runOne_of_applyMemM errno_alloc_eq)).trans ?_
    refine (runOne_bind_active
      (z := CerbMem.Footprint.FP .W errnoAddr (CerbMem.sizeofCtype fmapEmpty signed_int))
      (s' := prodMem₀) (runOne_of_applyMemM errno_store_eq)).trans ?_
    rfl
  -- park main's arena, run driver2, finalize
  refine (runOne_bind_active (z := ()) (s' := dstD) ?_).trans ?_
  · refine (runOne_bind_active (z := ()) (s' := prodEntryState sup e fs)
      (by rfl)).trans ?_
    exact hdrv2
  · refine (runOne_bind_active (z := dstD) (by rfl)).trans ?_
    rfl

/-! ## THE PRODUCTION RUN EQUATION FOR REGISTERED-LOOP PROGRAMS
(generic production machinery, not example content: the pipeline
theorem composing `drive_after_setup` + a `DriverDoneAt` delivery fact
+ `driver2_done`/`finalize_done`) -/

/-- The production pipeline on a synthetic one-procedure file whose
    program's registered label map (the SHIPPED registration,
    `collect_labeled_continuations_NEW`) ties at `mainSym`, given the
    driver-delivery fact from the cold-start memory: `runND` of the
    SHIPPED driver from the PRODUCTION initial state is EXACTLY ONE
    Active execution, whose result value and final memory satisfy ψ.
    Total-lane composition: `hdd` comes from `wpt_driver_done`, so no
    termination hypothesis remains — only the in-budget bound on the
    certified step count (fuel honesty, D19). -/
theorem prod_run_eqJ (sup : Nat) (e : CoreExpr) {Q : LabelMap}
    (hQe : LabeledAt ((initial_core_run_state sup
      (collect_labeled_continuations_NEW (prodFile e))).1) mainSym Q)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneAt mainSym Q (prodThread e) e [fmapEmpty] prodMem₀ ψ k)
    (hfl : k + 2 ≤ CerbFuel.driverFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args)
          ((initial_driver_state sup (prodFile e) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  obtain ⟨v, σfin, ρfin, rs', tr, ctr, hψ, hloop⟩ :=
    hdd (prodEntryState sup e fs) fmapEmpty CerbFuel.driverFuel rfl rfl rfl hQe hfl
  have hdrv2 := driver2_done 99999999 fmapEmpty (prodEntryState sup e fs) _
    (prodThread e)
    { prodThread e with arena := ofVal (.pure v), env := ρfin }
    v rfl hloop rfl
  have hrun := drive_after_setup sup e fs args _ hdrv2
  refine ⟨_, _, runND_active hrun, ?_, rfl, rfl, rfl⟩
  rw [finalize_done fmapEmpty _ _
    { { prodThread e with arena := ofVal (.pure v), env := ρfin } with
        stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
  exact hψ


/-! ## THE PRODUCTION REGISTRATION TIE (the LabeledAt derivation):
for the authored loop programs, the label map the exhibits' run
states carry is EXACTLY what the SHIPPED registration computes —
`collect_labeled_continuations_NEW` over the synthetic one-procedure
file (Core_aux.lean:853, via `collect_saves`), the map
`initial_core_run_state` installs as `labeled` (Core_run_aux.lean:406).
`LabeledAt` at the PRODUCTION initial run state is therefore DERIVED,
not hypothesized. These statements quantify over the shipped initial
state at every supply `sup` (the `labeled` fiber is
supply-independent, by `rfl`). The production `.done` equations for
the loop RUNS — `fib_certified_production`,
`counter_loop_certified_production`,
`list_reverse_certified_production` (ProdLoopExhibit.lean) — are
proved through `prod_run_eqJ` above with these ties as their
`LabeledAt` premise. -/

open Iris Iris.BI Iris.ProgramLogic

/-- The registration computes the fib exhibit's label map. -/
theorem collect_saves_fib (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) :
    collect_saves (fibProg ra n sbty ibty abty bbty) =
      fibQ ra n ibty abty bbty := rfl

/-- ... lifted through the file-level registration. -/
theorem collect_new_fib (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) :
    collect_labeled_continuations_NEW
        (prodFile (fibProg ra n sbty ibty abty bbty)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (fibQ ra n ibty abty bbty) fmapEmpty := rfl

/-- THE TIE: at the PRODUCTION initial run state of the synthetic
    fib file, the current procedure's `labeled` fiber IS the
    exhibit's label map — `LabeledAt` derived from the shipped
    registration. -/
theorem fib_labeledAt_production (sup : Nat) (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile (fibProg ra n sbty ibty abty bbty)))).1)
      mainSym (fibQ ra n ibty abty bbty) := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile (fibProg ra n sbty ibty abty bbty)))).1).labeled =
    collect_labeled_continuations_NEW
      (prodFile (fibProg ra n sbty ibty abty bbty)) from rfl]
  rw [collect_new_fib]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- The same tie for the S3 counter loop. -/
theorem collect_saves_loop (loc : CerbLocation.Loc)
    (ann ra : core_run_annotation) (mo : memory_order)
    (bty xbty sbty : core_base_type) (c : CerbMem.PointerValue) (n : Int) :
    collect_saves (loopProg loc ann ra mo bty xbty sbty c n) =
      loopQ loc ann ra mo bty xbty c := rfl

theorem loop_labeledAt_production (sup : Nat) (loc : CerbLocation.Loc)
    (ann ra : core_run_annotation) (mo : memory_order)
    (bty xbty sbty : core_base_type) (c : CerbMem.PointerValue) (n : Int) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile (loopProg loc ann ra mo bty xbty sbty c n)))).1)
      mainSym (loopQ loc ann ra mo bty xbty c) := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile (loopProg loc ann ra mo bty xbty sbty c n)))).1).labeled =
    collect_labeled_continuations_NEW
      (prodFile (loopProg loc ann ra mo bty xbty sbty c n)) from rfl]
  rw [show collect_labeled_continuations_NEW
      (prodFile (loopProg loc ann ra mo bty xbty sbty c n)) =
    fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      (loopQ loc ann ra mo bty xbty c) fmapEmpty from rfl]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-! ## THE SYNTHETIC N-PROCEDURE FILE AND ITS PRODUCTION ENTRY (calls arc C4)

`prodFileWith procs e`: `main` (the fragment program `e`, as `prodFile`)
plus the declared procedures `procs` — each `(f, params, body)` a `Proc`
at the unknown location, no marker, the unit return type (inert on the
production path: `call_proc` reads params and body only, Core_run.lean:93;
`funinfo` stays empty, so every RETURN round is a `TSK_Misc` tau). The
procedure map is built by `symAdd` (EnvLaws), so the β-generic lookup law
reads `call_proc`'s lookups off it; `prodFile e` is the no-procedure
instance (`prodFile_eq_with`, `rfl`). The setup collapse
`drive_after_setup_with` and the pipeline theorem `prod_run_eqJ_procs`
are the N-procedure twins of `drive_after_setup`/`prod_run_eqJ`: the one
new obligation is the `main` lookup on a map whose tail is symbolic —
`symAdd_lookup` at the top entry — and the delivery premise is the
live-control `DriverDoneCtl` (ProdLoop.lean) at the production entry
control `prodCtl` (the parked thread literal of `Driver.drive`,
Driver.lean:530: `stack0 := Stack_empty`, `current_proc_opt := some
main_sym`, `exec_loc := ELoc_normal [(main_sym, other "Driver.drive")]`,
`current_loc := other "Driver.drive"`) at the production context
`prodCtx` (the same `current_loc`, the file, the production run state).
The registration tie is the whole-file `LabeledProcs` at the production
initial run state — derived by computation in the exhibit, as
`fib_labeledAt_production` is. -/

/-- The declared procedures as `call_proc`'s map (newest first). -/
def procDecls (procs : List (sym × List (sym × core_base_type) × CoreExpr)) :
    Fmap sym (generic_fun_map_decl Unit core_run_annotation) :=
  procs.foldr (fun pr acc =>
    symAdd pr.1 (Proc CerbLocation.unknown none BTy_unit pr.2.1 pr.2.2) acc) fmapEmpty

theorem procDecls_symMap (procs : List (sym × List (sym × core_base_type) × CoreExpr)) :
    SymMap (procDecls procs) := by
  induction procs with
  | nil => exact symMap_empty
  | cons pr rest ih => exact ih.add _ _

/-- The synthetic file with declared procedures: `prodFile e` with
    `main`'s declaration on top of `procDecls procs`. -/
def prodFileWith (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (e : CoreExpr) : file core_run_annotation :=
  { prodFile e with funs := symAdd mainSym (mainDecl e) (procDecls procs) }

/-- The one-procedure file is the instance at no procedures. -/
theorem prodFile_eq_with (e : CoreExpr) : prodFile e = prodFileWith [] e := rfl

/-- `call_proc`'s lookup of `main` on the N-procedure file (the top
    entry of the map, whatever the tail). -/
theorem prodFileWith_lookup_main (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (e : CoreExpr) :
    lookupProc (prodFileWith procs e) fmapEmpty mainSym = some ([], e) := by
  unfold lookupProc
  rw [show fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) mainSym
      (prodFileWith procs e).stdlib = none from rfl]
  rw [resolveExtern_empty, show (prodFileWith procs e).funs =
      symAdd mainSym (mainDecl e) (procDecls procs) from rfl,
    symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rfl

/-- The production ENTRY CONTROL: the control fields of the thread
    `Driver.drive` parks (Driver.lean:530) — empty call stack, current
    procedure `main`, execution location `[(main, "Driver.drive")]`. -/
def prodCtl : Ctl :=
  ⟨[], some mainSym, ELoc_normal [(mainSym, CerbLocation.other "Driver.drive")]⟩

/-- The parked thread IS the control-threaded thread at the entry control. -/
theorem prodThread_eq_ctlThread (e : CoreExpr) :
    ctlThread (prodThread e) e [fmapEmpty] prodCtl = prodThread e := rfl

/-- The PRODUCTION CONTEXT at a file and a run state: tagDefs/extern
    empty, thread 0, no parent, the cold-start errno pointer, and
    `currentLoc := other "Driver.drive"` — the parked thread's
    `current_loc` (Driver.lean:530), what the PCALL round pushes onto
    `exec_loc` (Core_reduction.lean:484 col 18133, `push_exec_loc psym
    th_st.current_loc th_st.exec_loc`). Reducible, as `procCtx`. -/
@[reducible] def prodCtx (f : file core_run_annotation) (rs : core_run_state) : MachineCtx :=
  { tagDefs := fmapEmpty, file := f, extern := fmapEmpty, tid := 0, parent := none,
    errno := errnoPtr, currentLoc := CerbLocation.other "Driver.drive", runState := rs }

/-- The production initial run state of a synthetic file: what
    `initial_driver_state` installs (`labeled` = the shipped registration
    `collect_labeled_continuations_NEW`, Core_run_aux.lean:406). -/
def prodRS (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (sup : Nat)
    (e : CoreExpr) : core_run_state :=
  (initial_core_run_state sup (collect_labeled_continuations_NEW (prodFileWith procs e))).1

theorem prodRS_labeled (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) :
    (prodRS procs sup e).labeled = collect_labeled_continuations_NEW (prodFileWith procs e) := rfl

/-- The driver state after driver_globals on the N-procedure file. -/
def prodPostGlobalsWith (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState) : driver_state :=
  { (initial_driver_state sup (prodFileWith procs e) fs).1 with
      core_state0 := { thread_states := [(0, (none, globalsThread))],
                       io := initial_io_state },
      core_run_state0 := { prodRS procs sup e with tid_supply := 1 } }

/-- The driver state at driver2 entry on the N-procedure file. -/
def prodEntryStateWith (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState) : driver_state :=
  { prodPostGlobalsWith procs sup e fs with
      core_state0 := { thread_states := [(0, (none, prodThread e))],
                       io := initial_io_state },
      layout_state := prodMem₀ }

/-- The setup collapse on the N-procedure file at EVERY `driver2` fuel,
    ACTIVE arm (`drive_after_setup`'s twin at any fuel): the same prefix,
    the `main` lookup by `symAdd_lookup`. `drive_after_setup_with` below is
    its instance at `fuel := CerbFuel.driverFuel` (`drive = drive_lemFuel
    CerbFuel.driverFuel`, `CerbND.drive_wrapper_defeq`). -/
theorem drive_after_setup_with_lemFuel (fuel : Nat)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstD : driver_state)
    (hdrv2 : runOne (driver2_lemFuel fuel fmapEmpty false)
        (prodEntryStateWith procs sup e fs) = (NDactive (), dstD)) :
    runOne (CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith procs e) args)
        ((initial_driver_state sup (prodFileWith procs e) fs).1) =
      (NDactive (finalize fmapEmpty "drive (without concur)" dstD), dstD) := by
  conv => lhs; unfold CerbND.drive_lemFuel
  refine (runOne_bind_active (z := (0 : Nat))
    (s' := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (z := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (z := mainSym) (by rfl)).trans ?_
  have hlook : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym (prodPostGlobalsWith procs sup e fs).core_file.funs = some (mainDecl e) := by
    show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls procs)) = _
    rw [symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rw [hlook]
  refine (runOne_bind_active
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e)) (by rfl)).trans ?_
  refine (runOne_bind_active (z := e) (by rfl)).trans ?_
  refine (runOne_bind_active (z := errnoPtr)
    (s' := { prodPostGlobalsWith procs sup e fs with layout_state := prodMem₀ })
    (runOne_liftMem_active ?_)).trans ?_
  · refine (runOne_bind_active (z := errnoPtr) (s' := σE1)
      (runOne_of_applyMemM errno_alloc_eq)).trans ?_
    refine (runOne_bind_active
      (z := CerbMem.Footprint.FP .W errnoAddr (CerbMem.sizeofCtype fmapEmpty signed_int))
      (s' := prodMem₀) (runOne_of_applyMemM errno_store_eq)).trans ?_
    rfl
  refine (runOne_bind_active (z := ()) (s' := dstD) ?_).trans ?_
  · refine (runOne_bind_active (z := ()) (s' := prodEntryStateWith procs sup e fs)
      (by rfl)).trans ?_
    exact hdrv2
  · refine (runOne_bind_active (z := dstD) (by rfl)).trans ?_
    rfl

/-- The setup collapse on the N-procedure file at EVERY `driver2` fuel,
    KILLED arm: the same prefix, and `driver2`'s kill propagates through
    the ND bind (`runOne_bind_killed`) — the pipeline's value is the
    kill at `driver2`'s state. -/
theorem drive_after_setup_with_killed (fuel : Nat)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstK : driver_state) (r : kill_reason driver_error)
    (hdrv2 : runOne (driver2_lemFuel fuel fmapEmpty false)
        (prodEntryStateWith procs sup e fs) = (NDkilled r, dstK)) :
    runOne (CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith procs e) args)
        ((initial_driver_state sup (prodFileWith procs e) fs).1) = (NDkilled r, dstK) := by
  conv => lhs; unfold CerbND.drive_lemFuel
  refine (runOne_bind_active (z := (0 : Nat))
    (s' := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (z := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (z := mainSym) (by rfl)).trans ?_
  have hlook : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym (prodPostGlobalsWith procs sup e fs).core_file.funs = some (mainDecl e) := by
    show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls procs)) = _
    rw [symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rw [hlook]
  refine (runOne_bind_active
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e)) (by rfl)).trans ?_
  refine (runOne_bind_active (z := e) (by rfl)).trans ?_
  refine (runOne_bind_active (z := errnoPtr)
    (s' := { prodPostGlobalsWith procs sup e fs with layout_state := prodMem₀ })
    (runOne_liftMem_active ?_)).trans ?_
  · refine (runOne_bind_active (z := errnoPtr) (s' := σE1)
      (runOne_of_applyMemM errno_alloc_eq)).trans ?_
    refine (runOne_bind_active
      (z := CerbMem.Footprint.FP .W errnoAddr (CerbMem.sizeofCtype fmapEmpty signed_int))
      (s' := prodMem₀) (runOne_of_applyMemM errno_store_eq)).trans ?_
    rfl
  refine runOne_bind_killed ?_
  refine (runOne_bind_active (z := ()) (s' := prodEntryStateWith procs sup e fs)
    (by rfl)).trans ?_
  exact hdrv2

/-- The setup collapse on the N-procedure file at the shipped `drive`
    (`drive_after_setup`'s twin; calls arc C4): the instance of
    `drive_after_setup_with_lemFuel` at `CerbFuel.driverFuel` — `drive`
    unfolds to `CerbND.drive_lemFuel CerbFuel.driverFuel`
    (`CerbND.drive_wrapper_defeq`, `rfl`). -/
theorem drive_after_setup_with (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstD : driver_state)
    (hdrv2 : runOne (driver2_lemFuel CerbFuel.driverFuel fmapEmpty false)
        (prodEntryStateWith procs sup e fs) = (NDactive (), dstD)) :
    runOne (_root_.drive fmapEmpty false (prodFileWith procs e) args)
        ((initial_driver_state sup (prodFileWith procs e) fs).1) =
      (NDactive (finalize fmapEmpty "drive (without concur)" dstD), dstD) :=
  drive_after_setup_with_lemFuel CerbFuel.driverFuel procs sup e fs args dstD hdrv2

/-- THE PRODUCTION RUN EQUATION FOR N-PROCEDURE PROGRAMS (calls arc C4;
    `prod_run_eqJ`'s twin): the production pipeline on the synthetic file
    `prodFileWith procs e` is EXACTLY ONE Active execution whose value and
    final memory satisfy ψ, given the whole-file registration tie at the
    production initial run state (`hlab`, derived by computation in the
    exhibit) and the live-control delivery fact from the cold start at
    the entry control `prodCtl` (`hdd`, from `wpt_driver_done_procs`), plus
    the in-budget bound `k + 2 ≤ CerbFuel.driverFuel`. -/
theorem prod_run_eqJ_procs (sup : Nat)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr)
    (hlab : LabeledProcs (prodCtx (prodFileWith procs e) (prodRS procs sup e))
      (prodRS procs sup e).labeled)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneCtl (prodCtx (prodFileWith procs e) (prodRS procs sup e)) (prodThread e) e
      [fmapEmpty] prodCtl prodMem₀ ψ k)
    (hfl : k + 2 ≤ CerbFuel.driverFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileWith procs e) args)
          ((initial_driver_state sup (prodFileWith procs e) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  obtain ⟨v, σfin, ρfin, pfin, ℓfin, rs', tr, ctr, hψ, hloop⟩ :=
    hdd (prodEntryStateWith procs sup e fs) fmapEmpty CerbFuel.driverFuel rfl rfl rfl rfl hlab hfl
  have hdrv2 := driver2_done 99999999 fmapEmpty (prodEntryStateWith procs sup e fs) _
    (prodThread e)
    (ctlThread (prodThread e) (ofVal (.pure v)) ρfin ⟨[], pfin, ℓfin⟩)
    v rfl hloop rfl
  have hrun := drive_after_setup_with procs sup e fs args _ hdrv2
  refine ⟨_, _, runND_active hrun, ?_, rfl, rfl, rfl⟩
  rw [finalize_done fmapEmpty _ _
    { ctlThread (prodThread e) (ofVal (.pure v)) ρfin ⟨[], pfin, ℓfin⟩ with
        stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
  exact hψ

/-! ## THE PARTIAL PIPELINE (the fuel-lane restatement, 2026-09-03): the
setup collapse at every `driver2` fuel, in both arms, and the closed
partial-correctness equation over `CerbND.drive_lemFuel fuel`. -/

/-- THE PRODUCTION PARTIAL-CORRECTNESS EQUATION FOR N-PROCEDURE PROGRAMS
    (the fuel-lane restatement's closed form; `prod_run_eqJ_procs`'s
    partial twin): the production pipeline on the synthetic file
    `prodFileWith procs e`, run through `CerbND.drive_lemFuel fuel` at
    EVERY `fuel` (the shipped `drive` is the instance at
    `CerbFuel.driverFuel`, `CerbND.drive_wrapper_defeq`), is EXACTLY ONE
    execution, and it is either the fuel-exhaustion kill
    `CerbND.fuelExhaustedKill` at the final state or an Active execution
    whose value and final memory satisfy ψ — given the whole-file
    registration tie at the production initial run state (`hlab`, derived
    by computation in the exhibit) and the driver-safety fact from the
    cold start at the entry control `prodCtl` (`hsafe`, from
    `engine_adequacy`). No in-budget bound, no termination claim: the
    exhaustion arm is exactly what the shipped driver does when the
    certified run does not fit `CerbFuel.driverFuel = 10^8` iterations
    (or, at `fuel = 0`, when `driver2` has no round). Every other
    outcome — a kill of any other reason, an ILLTYPED refusal, a second
    execution — is excluded. -/
theorem prod_run_safe_procs (sup : Nat)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr)
    (hlab : LabeledProcs (prodCtx (prodFileWith procs e) (prodRS procs sup e))
      (prodRS procs sup e).labeled)
    (ψ : value → Mem → Prop)
    (hsafe : DriverSafeCtl (prodCtx (prodFileWith procs e) (prodRS procs sup e)) (prodThread e) e
      [fmapEmpty] prodCtl prodMem₀ ψ)
    (fs : CerbFS.FsState) (args : List String) (fuel : Nat) :
    ∃ (st : nd_status driver_result driver_error driver_state) (dst' : driver_state),
      CerbND.runND (CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith procs e) args)
          ((initial_driver_state sup (prodFileWith procs e) fs).1) =
        [(st, ([] : List String), dst')] ∧
      (st = nd_status.Killed dst' CerbND.fuelExhaustedKill ∨
       ∃ dres : driver_result, st = nd_status.Active dres ∧
         ψ dres.dres_core_value dst'.layout_state ∧
         dres.dres_blocked = false ∧
         dres.dres_stdout = "" ∧
         dres.dres_stderr = "") := by
  cases fuel with
  | zero =>
    -- no `driver2` round: the setup runs at its fixed budgets, then the kill
    have hdrv2 : runOne (driver2_lemFuel 0 fmapEmpty false) (prodEntryStateWith procs sup e fs) =
        (NDkilled CerbND.fuelExhaustedKill, prodEntryStateWith procs sup e fs) := by
      rw [CerbND.driver2_lemFuel_zero]
      rfl
    refine ⟨_, _, runND_killed (drive_after_setup_with_killed 0 procs sup e fs args _ _ hdrv2),
      Or.inl rfl⟩
  | succ fl =>
    rcases hsafe (prodEntryStateWith procs sup e fs) fmapEmpty CerbFuel.driverFuel rfl rfl rfl rfl
        hlab (CtlTied.entry hlab (prodFileWith_lookup_main procs e) _) with
      ⟨dstK, hloop⟩ | ⟨v, σfin, ρfin, pfin, ℓfin, rs', tr, ctr, hψ, hloop⟩
    · -- the shipped loop EXHAUSTS its budget: `driver2` kills, the pipeline kills
      have hdrv2 := driver2_killed fl fmapEmpty (prodEntryStateWith procs sup e fs) dstK
        (prodThread e) _ rfl hloop
      refine ⟨_, _, runND_killed (drive_after_setup_with_killed _ procs sup e fs args _ _ hdrv2),
        Or.inl rfl⟩
    · -- the shipped loop DELIVERS: the total pipeline's route
      have hdrv2 := driver2_done fl fmapEmpty (prodEntryStateWith procs sup e fs) _
        (prodThread e)
        (ctlThread (prodThread e) (ofVal (.pure v)) ρfin ⟨[], pfin, ℓfin⟩)
        v rfl hloop rfl
      have hrun := drive_after_setup_with_lemFuel _ procs sup e fs args _ hdrv2
      refine ⟨_, _, runND_active hrun, Or.inr ⟨_, rfl, ?_, rfl, rfl, rfl⟩⟩
      rw [finalize_done fmapEmpty _ _
        { ctlThread (prodThread e) (ofVal (.pure v)) ρfin ⟨[], pfin, ℓfin⟩ with
            stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
      exact hψ

end CerberusHeapLang
