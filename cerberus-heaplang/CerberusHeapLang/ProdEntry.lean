/-
CerberusHeapLang.ProdEntry — the COLD START and the
production-entry theorem: triples restated against the shipped
pipeline, from the shipped initial state.

The pipeline under judgment is the SHIPPED one (Main.lean:857-885):

  CerbND.runND (Driver.drive tagDefs false file args)
               (initial_driver_state file fs)

with `initial_driver_state` (Driver.lean:435) the PRODUCTION state
constructor — nothing hand-built enters the quantifiers: memory starts
at `CerbMem.initialMemState` (= the empty MemState, CerbMem.lean:1193),
the thread pool empty (`initial_core_state`, Core_run_aux.lean:392),
and the run state at `initial_core_run_state` (Core_run_aux.lean:395)
whose `sym_supply` is drawn through the EFFECTFUL seam
`runEffectful (CerberusFresh.freshIntIO ())` — the declared temporal
boundary axiom (see Audit.lean); every theorem below therefore carries
`LemLib.runEffectful` in its cone, and holds REGARDLESS of the drawn
value (the fragment never reads sym_supply — the D14 read-set
partition).

The setup prefix `Driver.drive` runs before `driver2`
(Driver.lean:500-513): spawn thread 0 (`driver_globals` /
`spawn_thread`, Core_run.lean:104 — tid 0 from the run state's
tid_supply), evaluate globals (none in a synthetic one-procedure
file), look up `main` in `funs`, skip argc/argv materialization
(main has no parameters), allocate-and-zero `errno` with the REAL
`allocateObject`/`storeM` on the cold memory, and park main's body as
thread 0's arena. The concrete cold-start facts (`errno_alloc_eq`
etc.) pin that prefix; `prodMem₀` is the memory state at fragment
start — derived through engine functions only.

THE THEOREM (`sem_triple_prod`): the exported semantic-triple face
(Adequacy.lean) restated against this pipeline. Scope honesty:
single-threaded, fragment-only, partial correctness — plus a
termination-within-budget hypothesis, because the production loop's
fuel-exhaustion leaf is the opaque `fuelExhausted` (fail-closed, D19):
at insufficient fuel NOTHING about the production value is provable,
so the run must provably complete for the equation to exist. Fuel
parametricity is a registered residual (README "Registered
divergences").

THE REGISTRATION TIE for loops: `fib_labeledAt_production` /
`loop_labeledAt_production` derive `LabeledAt` at the PRODUCTION
initial run state from the shipped
`collect_labeled_continuations_NEW` — the loop exhibits' label maps
are exactly what the production entry computes, nothing hand-built —
and `counter_loop_certified_registration` re-exports the counter
loop at that derived tie. (Phase 5 [audit F-05]: the theorem is
named for what it is — the REGISTRATION tie at the driveJ lane; the
full production `runND` equations for loop RUNS are the
`*_production` theorems of ProdLoopExhibit.lean, through the
proc-carrying scheduler collapse of DriverCollapse/ProdLoop.)

Note on `create` and the WP layer (D26; 2026-09-01 re-audit R-01):
an UNCONDITIONAL `wp_create` from cell ownership alone is
unprovable — allocateObject can kill ("out of memory",
CerbMem.lean:1479) from configurations no cell footprint
constrains. Phase 2's allocator-cursor resource supplies the
missing authority locally: `wps_create` (Wps.lean) allocates from
cursor ownership, the OOM arm excluded by the pure `freshBase`
guard on owned state. But that rule is LOCAL ONLY — no adequacy
launcher grants `cursorOwn` (R-01; its one client,
`struct_create_store_wps`, assumes the resource and ends at `wps`).
THIS module's cold-start technique is therefore the route the
allocating production exhibits ACTUALLY use: the create prefix runs
on the PRODUCTION-PINNED initial memory as handwritten certified
operational rounds, where allocation success is a theorem (the
`hpre` hypothesis below, discharged concretely by the exhibits) —
a MIXED logical/operational proof shape (R-02), scheduled for
replacement by whole-program logic proofs in alloc arc P1/P2.

Dnn labels are the recorded design findings of
docs/2026-08-30_spike-sliceB-notes.md.
-/
import CerberusHeapLang.DriverCollapse
import CerberusHeapLang.FibExhibit

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
  applyMemM (CerbMem.allocateObject 0 (PrefOther "errno")
    (CerbMem.alignofIval signed_int) signed_int none none)
    CerbMem.initialMemState

/-- The state after the errno allocation. -/
def σE1 : Mem :=
  match errnoSeeded with
  | some (_, σ) => σ
  | none => {}

theorem errnoSeeded_eq : errnoSeeded = some (errnoPtr, σE1) := rfl

theorem errno_alloc_eq :
    applyMemM (CerbMem.allocateObject 0 (PrefOther "errno")
      (CerbMem.alignofIval signed_int) signed_int none none)
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

theorem errnoCellCoh : CellCoh σE1 0 errnoCell :=
  ⟨rfl, ⟨errnoAllocRec, errno_alloc_get, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype errnoCell.ty = 4 from rfl]; exact errno_bytes_len errnoAddr,
   by rw [show CerbMem.sizeofCtype errnoCell.ty = 4 from rfl],
   fun _ _ => rfl⟩

theorem zero_storable : StorableAt signed_int zeroMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The memory state at fragment start: errno allocated and zeroed by
    the engine's own operations — the production cold-start memory. -/
def prodMem₀ : Mem :=
  CerbMem.writeBytesTo σE1 errnoAddr (CerbMem.memValueToBytes [] zeroMval).2

theorem errno_store_eq :
    applyMemM (CerbMem.storeM (CerbLocation.other "errno init") signed_int
      false errnoPtr zeroMval) σE1 =
      some (.FP .W errnoAddr (CerbMem.sizeofCtype signed_int), prodMem₀) :=
  storeM_success σE1 0 errnoCell zeroMval _ errnoCellCoh zero_storable

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
def prodPostGlobals (e : CoreExpr) (fs : CerbFS.FsState) : driver_state :=
  { initial_driver_state (prodFile e) fs with
      core_state0 := { thread_states := [(0, (none, globalsThread))],
                       io := initial_io_state },
      core_run_state0 :=
        { initial_core_run_state
            (collect_labeled_continuations_NEW (prodFile e)) with
          tid_supply := 1 } }

/-- The driver state at driver2 entry: errno allocated and zeroed,
    main's body parked as thread 0's arena. -/
def prodEntryState (e : CoreExpr) (fs : CerbFS.FsState) : driver_state :=
  { prodPostGlobals e fs with
      core_state0 := { thread_states := [(0, (none, prodThread e))],
                       io := initial_io_state },
      layout_state := prodMem₀ }

/-! ## The setup collapse: Driver.drive's prefix from the production
initial state to the driver2 entry, computed through the engine's own
setup functions (spawn_thread, the main lookup, the errno block). -/

theorem drive_after_setup (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstD : driver_state)
    (hdrv2 : runOne (driver2_lemFuel lemDefaultFuel fmapEmpty false)
        (prodEntryState e fs) = (NDactive (), dstD)) :
    runOne (_root_.drive fmapEmpty false (prodFile e) args)
        (initial_driver_state (prodFile e) fs) =
      (NDactive (finalize fmapEmpty "drive (without concur)" dstD), dstD) := by
  conv => lhs; unfold _root_.drive
  -- driver_globals: spawn thread 0, no globals
  refine (runOne_bind_active (z := (0 : Nat))
    (s' := prodPostGlobals e fs) (by rfl)).trans ?_
  -- main lookup on the synthetic file
  refine (runOne_bind_active (z := prodPostGlobals e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (z := mainSym) (by rfl)).trans ?_
  refine (runOne_bind_active
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e))
    (by rfl)).trans ?_
  refine (runOne_bind_active (z := e) (by rfl)).trans ?_
  -- the errno allocation block (real allocateObject/storeM on the
  -- cold memory)
  refine (runOne_bind_active (z := errnoPtr)
    (s' := { prodPostGlobals e fs with layout_state := prodMem₀ })
    (runOne_liftMem_active ?_)).trans ?_
  · refine (runOne_bind_active (z := errnoPtr) (s' := σE1)
      (runOne_of_applyMemM errno_alloc_eq)).trans ?_
    refine (runOne_bind_active
      (z := CerbMem.Footprint.FP .W errnoAddr (CerbMem.sizeofCtype signed_int))
      (s' := prodMem₀) (runOne_of_applyMemM errno_store_eq)).trans ?_
    rfl
  -- park main's arena, run driver2, finalize
  refine (runOne_bind_active (z := ()) (s' := dstD) ?_).trans ?_
  · refine (runOne_bind_active (z := ()) (s' := prodEntryState e fs)
      (by rfl)).trans ?_
    exact hdrv2
  · refine (runOne_bind_active (z := dstD) (by rfl)).trans ?_
    rfl

/-! ## THE PRODUCTION RUN EQUATION -/

/-- The production pipeline on a synthetic one-procedure fragment
    file: `runND` of the SHIPPED driver from the PRODUCTION initial
    state is EXACTLY ONE Active execution, whose result value is the
    drive's delivered value and whose final memory is the drive's
    final memory. Hypotheses: the fragment drive from the cold-start
    memory completes within budget (∀ action-id supplies — the
    production supply starts at an effectful seed). Killed and stuck
    productions are excluded by the equation itself: the run IS the
    singleton Active execution. -/
theorem prod_run_eq (e : CoreExpr) (hfrag : StraightFrag e)
    (v : value) (σfin : Mem) (k : Nat)
    (hterm : ∀ aids : Nat → Nat,
      drive aids k (spikeThread e) prodMem₀ = .done v σfin)
    (hfuel : esize e + k + 2 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args)
          (initial_driver_state (prodFile e) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = v ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" ∧
      dst'.layout_state = σfin := by
  obtain ⟨rs', tr, ctr, hloop⟩ := prod_loop_done (prodThread e) rfl
    (ev0 := fmapEmpty) (evs := []) rfl v σfin k lemDefaultFuel e
    (prodEntryState e fs) fmapEmpty hfrag rfl (by omega) (by omega) hterm
  have hdrv2 := driver2_done 999999 fmapEmpty (prodEntryState e fs) _
    (prodThread e) { prodThread e with arena := ofVal (.pure v) } v rfl
    hloop rfl
  have hrun := drive_after_setup e fs args _ hdrv2
  exact ⟨_, _, runND_active hrun, by
      rw [finalize_done fmapEmpty _ _
        { { prodThread e with arena := ofVal (.pure v) } with
            stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl],
    rfl, rfl, rfl, rfl⟩

/-! ## THE THEOREM: the semantic-triple face at the production entry
(Extension D, D4). The exported face (SemTriple, Adequacy.lean
D16/D17) restated against `runND ∘ Driver.drive ∘
initial_driver_state`: for a synthetic one-procedure file wrapping a
self-contained fragment program (its create prefix runs on the
production cold-start memory and establishes the compute part's
footprint), the production run is the singleton Active execution, its
result value is the delivered value, and the final memory satisfies
the postcondition footprint with the frame R verbatim — the same
splitting quantifier as SemTriple. -/
theorem sem_triple_prod
    (e : CoreExpr) (hfrag : StraightFrag e)
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
        Sat σfin (Iris.Std.PartialMap.union Q R) := by
  have htermFull : ∀ aids : Nat → Nat,
      drive aids (j + k) (spikeThread e) prodMem₀ = .done v σfin := by
    intro aids
    rw [hpre aids k]
    exact hterm _
  obtain ⟨dres, dst', heq, hval, _, _, _, hlay⟩ :=
    prod_run_eq e hfrag v σfin (j + k) htermFull hfuel fs args
  refine ⟨dres, dst', heq, hval, hlay, ?_⟩
  have h := hsem R hdisj σc hsat k (fun _ => 0) hfuelc
  exact h.2.2 v σfin (hterm _)

/-! ## S4 — THE PRODUCTION REGISTRATION TIE (the LabeledAt
derivation): for the authored loop programs, the label map the
exhibits' run states carry is EXACTLY what the SHIPPED registration
computes — `collect_labeled_continuations_NEW` over the synthetic
one-procedure file (Core_aux.lean:853, via `collect_saves`), the
map `initial_core_run_state` installs as `labeled`
(Core_run_aux.lean:395). `LabeledAt` at the PRODUCTION initial run
state is therefore DERIVED, not hypothesized (the S3 exhibit's
recorded gap). These statements quantify over the shipped initial
state, whose `sym_supply` draws the declared temporal boundary seam
— hence this boundary module. HONEST RESIDUAL (recorded, slice
notes): the full production-face `.done` equation for a LOOP run
(the driver2 collapse at a proc-carrying thread with a populated
label map) is not established this slice — the DriverCollapse
scheduler equations are pinned at the phase-1 profile; the drive
lane's `fib_certified_total` carries the step-bound product that
would discharge its in-budget hypothesis. -/

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
theorem fib_labeledAt_production (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) :
    LabeledAt (initial_core_run_state (collect_labeled_continuations_NEW
        (prodFile (fibProg ra n sbty ibty abty bbty))))
      mainSym (fibQ ra n ibty abty bbty) := by
  unfold LabeledAt
  rw [show (initial_core_run_state (collect_labeled_continuations_NEW
      (prodFile (fibProg ra n sbty ibty abty bbty)))).labeled =
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

theorem loop_labeledAt_production (loc : CerbLocation.Loc)
    (ann ra : core_run_annotation) (mo : memory_order)
    (bty xbty sbty : core_base_type) (c : CerbMem.PointerValue) (n : Int) :
    LabeledAt (initial_core_run_state (collect_labeled_continuations_NEW
        (prodFile (loopProg loc ann ra mo bty xbty sbty c n))))
      mainSym (loopQ loc ann ra mo bty xbty c) := by
  unfold LabeledAt
  rw [show (initial_core_run_state (collect_labeled_continuations_NEW
      (prodFile (loopProg loc ann ra mo bty xbty sbty c n)))).labeled =
    collect_labeled_continuations_NEW
      (prodFile (loopProg loc ann ra mo bty xbty sbty c n)) from rfl]
  rw [show collect_labeled_continuations_NEW
      (prodFile (loopProg loc ann ra mo bty xbty sbty c n)) =
    fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      (loopQ loc ann ra mo bty xbty c) fmapEmpty from rfl]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- THE REGISTRATION-TIE LOOP EXPORT (renamed from
    `counter_loop_certified_production` at Phase 5 — audit F-05:
    "production" is reserved for statements whose execution function
    is the shipped runner; this one's lane is driveJ at the
    production run state): the counter-loop certification restated
    with the run state built by the SHIPPED registration ONLY
    (`initial_core_run_state ∘ collect_labeled_continuations_NEW` —
    nothing hand-built in the label plumbing; the drive is the
    certified jump-profile lane). The in-budget hypotheses are the
    sanctioned interim form. The real production equations live in
    ProdLoopExhibit.lean. -/
theorem counter_loop_certified_registration
    (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bty xbty sbty : core_base_type)
    (idx addr : Int) (bs0 : List CerbMem.AbsByte)
    (n : Int) (hn : 0 ≤ n)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem)
    (hcoh : Coh σ₀ ((Iris.Std.PartialMap.singleton idx
      (SpikeCell.mk addr intTy bs0)) : SpikeHeapF SpikeCell))
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 4 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 3 + nsteps ≤ lemDefaultFuel) :
    let prog := loopProg loc ann ra mo bty xbty sbty (cellPtr idx addr) n
    let rs := initial_core_run_state (collect_labeled_continuations_NEW
      (prodFile prog))
    (∀ r, driveJ rs aids nsteps
      (procThread mainSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread mainSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread mainSym prog [fmapEmpty]) σ₀ = .done v σ' →
      v = Vunit ∧ ∃ bs',
        ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
        ∃ i a, cellPtr idx addr = cellPtr i a ∧
          CellCoh σ' i ⟨a, intTy, bs'⟩) := by
  intro prog rs
  refine engine_adequacyJ (GF := SpikeGF)
    (loop_labeledAt_production loc ann ra mo bty xbty sbty
      (cellPtr idx addr) n)
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      exact loopBody_fragJ loc ann ra mo bty _ hlib)
    prog fmapEmpty [] σ₀ _
    (.save (loopBody_fragJ loc ann ra mo bty _ hlib)) hcoh
    (fun v σ' => v = Vunit ∧ ∃ bs',
      ((n = 0 ∧ bs' = bs0) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
      ∃ i a, cellPtr idx addr = cellPtr i a ∧ CellCoh σ' i ⟨a, intTy, bs'⟩)
    ?_ nsteps aids
    (by rw [show esize prog = 4 from rfl]; omega)
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := loopQ_inv loc ann ra mo bty xbty _ hl
      rw [show esize (loopBody loc ann ra mo bty (cellPtr idx addr)) = 3
        from rfl]
      omega)
  intro inst
  refine .trans ?_ (loop_wp_readout loc ann ra mo bty xbty (cellPtr idx addr)
    n bs0 mainSym rs
    (loop_labeledAt_production loc ann ra mo bty xbty sbty
      (cellPtr idx addr) n) hn sbty)
  refine (BigSepM.bigSepM_singleton).1.trans ?_
  iintro Hpt
  iapply (pointsToCell_cellOwn_iff _ _ _ _).mpr
  iexists idx, addr
  isplit
  · ipureintro; rfl
  · iexact Hpt

end CerberusHeapLang
