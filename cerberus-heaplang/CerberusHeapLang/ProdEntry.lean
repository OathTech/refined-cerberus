/-
CerberusHeapLang.ProdEntry — production setup and closed execution equations.

The conclusions use the shipped `CerbND.runND (_root_.drive …)` from
`(initial_driver_state sup file fs).1`. One caller-provided `[LemFuel]`
parameter is retained through ND binds, memory operations, the outer driver,
the per-thread loop, finalization and result enumeration. Each generated
wrapper starts its worker at that ambient budget; it is not a cumulative
counter shared between calls. No fixed default fuel is installed here.

`prod_run_eqJ_file` accepts a complete file with a proved parameterless
main lookup, no globals and empty tag definitions. It retains the actual
library, implementation and external maps, including the external-name map
constructed by startup. The delivery premise must refer to that same file
and map. Actual emitted t1 uses this lane in `EmittedT1Exhibit`.

The earlier constructed-file APIs remain available for regressions. Their
extern/tag/implementation maps are empty; they may contain other procedures
and an arbitrary Core standard-library map. The partial and call lanes
retain those restrictions. A7 remains open for the rest of the corpus.

For ambient fuel at least two, setup spawns thread 0, looks up main,
allocates and zeroes errno through the actual memory engine, and parks
main's body. `ProdMemory` proves the complete resulting memory `prodMem₀`,
its well-formedness and the unallocated-byte freshness used by `LaunchCoh`.
The setup lemmas compose those equations with the shipped driver prefix.

The total equations consume `DriverDoneAtExtern`, its empty-map
specialization `DriverDoneAt`, or `DriverDoneCtl` for that same file and
fuel instance and require `k + 2 ≤ LemFuel.fuel`. They prove
exactly one active outcome with the stated value and memory postcondition,
no blocking, and empty stdout/stderr. Registration, live-control and symbol
supply obligations remain in the delivery premise; this module does not
assert that arbitrary programs ignore the initial supply. A total equation
makes no claim at budgets below its premise.

The partial equations hold at every ambient budget, given a `DriverSafeCtl`
proof whenever that budget is at least two. At zero, `runND` exhausts
before setup and preserves the initial state. At one, setup initializes
errno, then `liftMem` writes back that memory and exhausts before main is
parked. At budgets at least two, the safety premise classifies the actual
per-thread loop at the same ambient budget. In every case there is exactly
one outcome: the designated fuel-exhaustion kill at its actual state, or
an active result satisfying the postcondition and the same output flags.
No termination claim follows from the partial equation.

This closes the production setup composition without requiring a generic
classification of arbitrary fragment-start executions at ambient one.
Authored and emitted clients must separately supply their public logic
proofs and the corresponding safety/delivery premises.
-/
import CerberusHeapLang.DriverCollapse
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.FibExhibit
import CerberusHeapLang.ProdLoop
import CerberusHeapLang.ProdMemory

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

/-- Registration on the single-procedure file reduces to the engine's
    save collector for that procedure body. -/
theorem collect_labeled_prodFile (e : CoreExpr) :
    collect_labeled_continuations_NEW (prodFile e) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (collect_saves e) fmapEmpty := rfl

/-! Save-collector equations used by production registration proofs.
Each equation exposes one constructor so clients can retain sharing
instead of reducing an entire file/collector/union tree at once. -/

theorem collect_saves_aux_pure (n : Nat) (st : collect_saves_state core_run_annotation)
    (a : List annot) (pe : generic_pexpr Unit sym) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Epure pe)) = st := rfl

theorem collect_saves_aux_call (n : Nat) (st : collect_saves_state core_run_annotation)
    (a : List annot) (ra : core_run_annotation) (f : sym)
    (pes : List (generic_pexpr Unit sym)) :
    collect_saves_aux_lemFuel (n + 1) st (callRedex a ra f pes) = st := rfl

theorem collect_saves_aux_if (n : Nat) (st : collect_saves_state core_run_annotation)
    (a : List annot) (g : generic_pexpr Unit sym) (e1 e2 : CoreExpr) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Eif g e1 e2)) =
      collect_saves_aux_lemFuel n (collect_saves_aux_lemFuel n st e1) e2 := rfl

theorem collect_saves_aux_sseq (n : Nat) (st : collect_saves_state core_run_annotation)
    (a : List annot) (pat : pattern) (e1 e2 : CoreExpr) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Esseq pat e1 e2)) =
      union_saves st (union_saves
        { collect_saves_aux_lemFuel n empty_saves e1 with
          tmp_acc := fmapMap (fun p => match p with
            | (syms, e) => (syms, Expr a (Esseq pat e e2)))
            (collect_saves_aux_lemFuel n empty_saves e1).tmp_acc }
        (collect_saves_aux_lemFuel n empty_saves e2)) := rfl

/-! The cold-start memory equations and launch coherence are proved in
`ProdMemory`: actual errno allocation and zeroing, complete metadata and
byte-map state, global memory well-formedness, and unallocated-byte
freshness below the cursor. This module composes them with the driver. -/

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

theorem drive_after_setup [LF : LemFuel] (hfuel : 2 ≤ LemFuel.fuel)
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstD : driver_state)
    (hdrv2 : runOne (driver2_lemFuel LemFuel.fuel fmapEmpty false)
        (prodEntryState sup e fs) = (NDactive (), dstD)) :
    runOne (_root_.drive fmapEmpty false (prodFile e) args)
        ((initial_driver_state sup (prodFile e) fs).1) =
      (NDactive (finalize fmapEmpty "drive (without concur)" dstD), dstD) := by
  rcases LF with ⟨fuel⟩
  change 2 ≤ fuel at hfuel
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  letI : LemFuel := ⟨n + 2⟩
  have hpos : 0 < LemFuel.fuel := by change 0 < n + 2; omega
  have htwo : 2 ≤ LemFuel.fuel := by change 2 ≤ n + 2; omega
  conv => lhs; unfold _root_.drive
  -- driver_globals: spawn thread 0, no globals
  refine (runOne_bind_active (hfuel := hpos) (z := (0 : Nat))
    (s' := prodPostGlobals sup e fs) (by rfl)).trans ?_
  -- main lookup on the synthetic file
  refine (runOne_bind_active (hfuel := hpos) (z := prodPostGlobals sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := mainSym) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos)
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e))
    (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := e) (by rfl)).trans ?_
  -- the errno allocation block (real allocateObject/storeM on the
  -- cold memory)
  refine (runOne_bind_active (hfuel := hpos) (z := errnoPtr)
    (s' := { prodPostGlobals sup e fs with layout_state := prodMem₀ })
    (runOne_liftMem_active (hfuel := htwo) (errno_init_eq hpos))).trans ?_
  -- park main's arena, run driver2, finalize
  refine (runOne_bind_active (hfuel := hpos) (z := ()) (s' := dstD) ?_).trans ?_
  · refine (runOne_bind_active (hfuel := hpos) (z := ()) (s' := prodEntryState sup e fs)
      (by rfl)).trans ?_
    exact hdrv2
  · refine (runOne_bind_active (hfuel := hpos) (z := dstD) (by rfl)).trans ?_
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
theorem prod_run_eqJ [LF : LemFuel] (sup : Nat) (e : CoreExpr) {Q : LabelMap}
    (hQe : LabeledAt ((initial_core_run_state sup
      (collect_labeled_continuations_NEW (prodFile e))).1) mainSym Q)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneAt mainSym Q (prodFile e) (prodThread e) e [fmapEmpty]
      (CerbLocation.other "Driver.drive") ⟨sup, 0⟩ prodMem₀ ψ k)
    (hfl : k + 2 ≤ LemFuel.fuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args)
          ((initial_driver_state sup (prodFile e) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  obtain ⟨v, σfin, ρfin, lcfin, afin, bfin, rs', tr, ctr, hψ, hloop⟩ :=
    hdd (prodEntryState sup e fs) fmapEmpty LemFuel.fuel rfl rfl rfl rfl hQe ⟨rfl, rfl⟩ hfl
  have hdrv2 := driver2_done (hfuel := by omega) (LemFuel.fuel - 1) fmapEmpty (prodEntryState sup e fs) _
    (prodThread e)
    { prodThread e with arena := ofValA (.pure afin bfin v), env := ρfin, current_loc := lcfin }
    v rfl hloop rfl
  rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel by omega] at hdrv2
  have hrun := drive_after_setup (hfuel := by omega) sup e fs args _ hdrv2
  refine ⟨_, _, runND_active (hfuel := by omega) hrun, ?_, rfl, rfl, rfl⟩
  rw [finalize_done (hfuel := by omega) fmapEmpty _ _
    { { prodThread e with arena := ofValA (.pure afin bfin v), env := ρfin, current_loc := lcfin }
        with stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
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
@[reducible] def prodCtl (sup : Nat) : Ctl :=
  ⟨[], some mainSym, ELoc_normal [(mainSym, CerbLocation.other "Driver.drive")],
    CerbLocation.other "Driver.drive", ⟨sup, 0⟩⟩

/-- The parked thread IS the control-threaded thread at the entry control. -/
theorem prodThread_eq_ctlThread (sup : Nat) (e : CoreExpr) :
    ctlThread (prodThread e) e [fmapEmpty] (prodCtl sup) = prodThread e := rfl

/-- The PRODUCTION CONTEXT at a file and a run state: tagDefs/extern
    empty, thread 0, no parent, the cold-start errno pointer, and
    (E1) the current location is LIVE on the control — `prodCtl.curLoc =
    other "Driver.drive"`, the parked thread's `current_loc`
    (Driver.lean:530), what the PCALL round pushes onto `exec_loc`
    (Core_reduction.lean:484 col 18133, `push_exec_loc psym
    th_st.current_loc th_st.exec_loc`). Reducible, as `procCtx`. -/
@[reducible] def prodCtx (f : file core_run_annotation) (rs : core_run_state) : MachineCtx :=
  { tagDefs := fmapEmpty, file := f, extern := fmapEmpty, tid := 0, parent := none,
    errno := errnoPtr, runState := rs }

/-- The production context's label map at a registered procedure
    (`procCtx_labels`'s twin at `prodCtx`): what `Erun` reads. -/
theorem prodCtx_labels {f : file core_run_annotation} {p : sym} {rs : core_run_state}
    {Q : LabelMap}
    (hQ : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p rs.labeled = some Q) :
    (prodCtx f rs).labelsAt (procCtl p).proc = Q := by
  rw [MachineCtx.labelsAt_eq_of_proc (M := prodCtx f rs) (c := procCtl p) rfl,
    MachineCtx.resolveProc_of_extern_empty rfl]
  show (match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
      Lem_Basic_classes.ordCompare s1 s2) p rs.labeled with
    | some Q => Q
    | none => fmapEmpty) = Q
  rw [hQ]

/-- The production context's extern map is empty (`procCtx_extern`'s twin). -/
theorem prodCtx_extern (f : file core_run_annotation) (rs : core_run_state) :
    (prodCtx f rs).extern = fmapEmpty := rfl

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

/-- Setup on the N-procedure file with ambient fuel at least two.
    The active driver result uses the same instance and budget as `drive`. -/
theorem drive_after_setup_with [LF : LemFuel] (hfuel : 2 ≤ LemFuel.fuel)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstD : driver_state)
    (hdrv2 : runOne (driver2_lemFuel LemFuel.fuel fmapEmpty false)
        (prodEntryStateWith procs sup e fs) = (NDactive (), dstD)) :
    runOne (_root_.drive fmapEmpty false (prodFileWith procs e) args)
        ((initial_driver_state sup (prodFileWith procs e) fs).1) =
      (NDactive (finalize fmapEmpty "drive (without concur)" dstD), dstD) := by
  rcases LF with ⟨fuel⟩
  change 2 ≤ fuel at hfuel
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  letI : LemFuel := ⟨n + 2⟩
  have hpos : 0 < LemFuel.fuel := by change 0 < n + 2; omega
  have htwo : 2 ≤ LemFuel.fuel := by change 2 ≤ n + 2; omega
  conv => lhs; unfold _root_.drive
  refine (runOne_bind_active (hfuel := hpos) (z := (0 : Nat))
    (s' := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := mainSym) (by rfl)).trans ?_
  have hlook : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym (prodPostGlobalsWith procs sup e fs).core_file.funs = some (mainDecl e) := by
    show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls procs)) = _
    rw [symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rw [hlook]
  refine (runOne_bind_active (hfuel := hpos)
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e)) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := e) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := errnoPtr)
    (s' := { prodPostGlobalsWith procs sup e fs with layout_state := prodMem₀ })
    (runOne_liftMem_active (hfuel := htwo) (errno_init_eq hpos))).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := ()) (s' := dstD) ?_).trans ?_
  · refine (runOne_bind_active (hfuel := hpos) (z := ()) (s' := prodEntryStateWith procs sup e fs)
      (by rfl)).trans ?_
    exact hdrv2
  · refine (runOne_bind_active (hfuel := hpos) (z := dstD) (by rfl)).trans ?_
    rfl

/-- With ambient fuel one, setup initializes errno and then memory lifting
    exhausts before the driver's main thread is parked. -/
theorem drive_after_setup_with_one [LF : LemFuel] (hone : LemFuel.fuel = 1)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) :
    runOne (_root_.drive fmapEmpty false (prodFileWith procs e) args)
        ((initial_driver_state sup (prodFileWith procs e) fs).1) =
      (NDkilled CerbND.fuelExhaustedKill,
        { prodPostGlobalsWith procs sup e fs with layout_state := prodMem₀ }) := by
  rcases LF with ⟨fuel⟩
  change fuel = 1 at hone
  subst fuel
  letI : LemFuel := ⟨1⟩
  conv => lhs; unfold _root_.drive
  refine (runOne_bind_active (hfuel := by decide) (z := (0 : Nat))
    (s' := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := by decide) (z := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := by decide) (z := mainSym) (by rfl)).trans ?_
  have hlook : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym (prodPostGlobalsWith procs sup e fs).core_file.funs = some (mainDecl e) := by
    show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls procs)) = _
    rw [symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rw [hlook]
  refine (runOne_bind_active (hfuel := by decide)
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e)) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := by decide) (z := e) (by rfl)).trans ?_
  refine runOne_bind_killed (hfuel := by decide) ?_
  rw [runOne_liftMem_one rfl]
  exact congrArg (fun mem : Mem =>
    (NDkilled CerbND.fuelExhaustedKill,
      { prodPostGlobalsWith procs sup e fs with layout_state := mem }))
    (congrArg Prod.snd (errno_init_eq (by decide)))

/-- Setup on the N-procedure file with ambient fuel at least two.
    A kill from the driver propagates with its actual state. -/
theorem drive_after_setup_with_killed [LF : LemFuel] (hfuel : 2 ≤ LemFuel.fuel)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstK : driver_state) (r : kill_reason driver_error)
    (hdrv2 : runOne (driver2_lemFuel LemFuel.fuel fmapEmpty false)
        (prodEntryStateWith procs sup e fs) = (NDkilled r, dstK)) :
    runOne (_root_.drive fmapEmpty false (prodFileWith procs e) args)
        ((initial_driver_state sup (prodFileWith procs e) fs).1) = (NDkilled r, dstK) := by
  rcases LF with ⟨fuel⟩
  change 2 ≤ fuel at hfuel
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  letI : LemFuel := ⟨n + 2⟩
  have hpos : 0 < LemFuel.fuel := by change 0 < n + 2; omega
  have htwo : 2 ≤ LemFuel.fuel := by change 2 ≤ n + 2; omega
  conv => lhs; unfold _root_.drive
  refine (runOne_bind_active (hfuel := hpos) (z := (0 : Nat))
    (s' := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := prodPostGlobalsWith procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := mainSym) (by rfl)).trans ?_
  have hlook : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym (prodPostGlobalsWith procs sup e fs).core_file.funs = some (mainDecl e) := by
    show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls procs)) = _
    rw [symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rw [hlook]
  refine (runOne_bind_active (hfuel := hpos)
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e)) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := e) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := errnoPtr)
    (s' := { prodPostGlobalsWith procs sup e fs with layout_state := prodMem₀ })
    (runOne_liftMem_active (hfuel := htwo) (errno_init_eq hpos))).trans ?_
  refine runOne_bind_killed (hfuel := hpos) ?_
  refine (runOne_bind_active (hfuel := hpos) (z := ()) (s' := prodEntryStateWith procs sup e fs)
    (by rfl)).trans ?_
  exact hdrv2

/-- THE PRODUCTION RUN EQUATION FOR N-PROCEDURE PROGRAMS (calls arc C4;
    `prod_run_eqJ`'s twin): the production pipeline on the synthetic file
    `prodFileWith procs e` is EXACTLY ONE Active execution whose value and
    final memory satisfy ψ, given the whole-file registration tie at the
    production initial run state (`hlab`, derived by computation in the
    exhibit) and the live-control delivery fact from the cold start at
    the entry control `prodCtl` (`hdd`, from `wpt_driver_done_procs`), plus
    the in-budget bound `k + 2 ≤ LemFuel.fuel`. -/
theorem prod_run_eqJ_procs [LF : LemFuel] (sup : Nat)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr)
    (hlab : LabeledProcs (prodCtx (prodFileWith procs e) (prodRS procs sup e))
      (prodRS procs sup e).labeled)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneCtl (prodCtx (prodFileWith procs e) (prodRS procs sup e)) (prodThread e) e
      [fmapEmpty] (prodCtl sup) prodMem₀ ψ k)
    (hfl : k + 2 ≤ LemFuel.fuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileWith procs e) args)
          ((initial_driver_state sup (prodFileWith procs e) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  obtain ⟨v, σfin, ρfin, pfin, ℓfin, lcfin, spfin, afin, bfin, rs', tr, ctr, hψ, hloop⟩ :=
    hdd (prodEntryStateWith procs sup e fs) fmapEmpty LemFuel.fuel rfl rfl rfl rfl hlab ⟨rfl, rfl⟩ hfl
  have hdrv2 := driver2_done (hfuel := by omega) (LemFuel.fuel - 1) fmapEmpty (prodEntryStateWith procs sup e fs) _
    (prodThread e)
    (ctlThread (prodThread e) (ofValA (.pure afin bfin v)) ρfin ⟨[], pfin, ℓfin, lcfin, spfin⟩)
    v rfl hloop rfl
  rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel by omega] at hdrv2
  have hrun := drive_after_setup_with (hfuel := by omega) procs sup e fs args _ hdrv2
  refine ⟨_, _, runND_active (hfuel := by omega) hrun, ?_, rfl, rfl, rfl⟩
  rw [finalize_done (hfuel := by omega) fmapEmpty _ _
    { ctlThread (prodThread e) (ofValA (.pure afin bfin v)) ρfin ⟨[], pfin, ℓfin, lcfin, spfin⟩ with
        stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
  exact hψ

/-! ## Closed partial correctness at every ambient budget -/

/-- Closed partial correctness for the N-procedure file at every ambient
    budget. The safety premise is needed only at budgets at least two;
    at zero and one the actual setup/runner equations give exhaustion.
    Exactly one outcome is returned: the designated fuel-exhaustion kill,
    or an active result satisfying ψ with no blocking or output. -/
theorem prod_run_safe_procs [LF : LemFuel] (sup : Nat)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr)
    (hlab : LabeledProcs (prodCtx (prodFileWith procs e) (prodRS procs sup e))
      (prodRS procs sup e).labeled)
    (ψ : value → Mem → Prop)
    (hsafe : 2 ≤ LemFuel.fuel → DriverSafeCtl (prodCtx (prodFileWith procs e) (prodRS procs sup e)) (prodThread e) e
      [fmapEmpty] (prodCtl sup) prodMem₀ ψ)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (st : nd_status driver_result driver_error driver_state) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileWith procs e) args)
          ((initial_driver_state sup (prodFileWith procs e) fs).1) =
        [(st, ([] : List String), dst')] ∧
      (st = nd_status.Killed dst' CerbND.fuelExhaustedKill ∨
       ∃ dres : driver_result, st = nd_status.Active dres ∧
         ψ dres.dres_core_value dst'.layout_state ∧
         dres.dres_blocked = false ∧
         dres.dres_stdout = "" ∧
         dres.dres_stderr = "") := by
  by_cases hzero : LemFuel.fuel = 0
  · refine ⟨_, (initial_driver_state sup (prodFileWith procs e) fs).1, ?_, Or.inl rfl⟩
    unfold CerbND.runND
    rw [hzero]
    rfl
  by_cases hone : LemFuel.fuel = 1
  · exact ⟨_, _, runND_killed (by omega)
      (drive_after_setup_with_one hone procs sup e fs args), Or.inl rfl⟩
  have hfuel : 2 ≤ LemFuel.fuel := by omega
  rcases hsafe hfuel (prodEntryStateWith procs sup e fs) fmapEmpty LemFuel.fuel rfl rfl rfl rfl
      hlab (CtlTied.entry hlab (prodFileWith_lookup_main procs e) _ _ _) ⟨rfl, rfl⟩ with
    ⟨dstK, hloop⟩ | ⟨v, σfin, ρfin, pfin, ℓfin, lcfin, spfin, afin, bfin, rs', tr, ctr, hψ, hloop⟩
  · have hdrv2 := driver2_killed (by omega) (LemFuel.fuel - 1) fmapEmpty
      (prodEntryStateWith procs sup e fs) dstK (prodThread e) _ rfl hloop
    rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel by omega] at hdrv2
    exact ⟨_, _, runND_killed (by omega)
      (drive_after_setup_with_killed hfuel procs sup e fs args _ _ hdrv2), Or.inl rfl⟩
  · have hdrv2 := driver2_done (by omega) (LemFuel.fuel - 1) fmapEmpty
      (prodEntryStateWith procs sup e fs) _ (prodThread e)
      (ctlThread (prodThread e) (ofValA (.pure afin bfin v)) ρfin ⟨[], pfin, ℓfin, lcfin, spfin⟩)
      v rfl hloop rfl
    rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel by omega] at hdrv2
    have hrun := drive_after_setup_with hfuel procs sup e fs args _ hdrv2
    refine ⟨_, _, runND_active (by omega) hrun, Or.inr ⟨_, rfl, ?_, rfl, rfl, rfl⟩⟩
    rw [finalize_done (by omega) fmapEmpty _ _
      { ctlThread (prodThread e) (ofValA (.pure afin bfin v)) ρfin ⟨[], pfin, ℓfin, lcfin, spfin⟩
          with stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
    exact hψ

/-! ## E3 — THE FILE OBJECT WITH A STANDARD LIBRARY (docs/2026-09-05_e3-notes.md §3)

The emitted dialect calls the Core standard library, and since E3 the
mirror evaluator reads the file's `stdlib` (`callBody`, Step.lean) as the
engine does (`call_function`, core_eval.lem:120–163). `prodFile`/
`prodFileWith` leave `stdlib` EMPTY — under them a `conv_loaded_int` call
is the engine's kill `Illformed_program "calling an unknown function"`
(core_eval.lem:136) and the classifier's `.kill` (`callOut`, EvalClass.lean).
`prodFileLib lib procs e` is `prodFileWith procs e` with `stdlib := lib`;
the E3 statements name it at `lib := stdlibE3` (StdCore.lean), the
hand-transcribed fragment the skeleton speedbump checks against the
pinned std.core. The closed pipeline forms below are the `_procs` forms
at that file, proved by the same setup collapse — the only new premise is
that `main` is not a name of the library (`hmain`; `call_proc`/`lookupProc`
consult `stdlib` FIRST, core_run.lem:34–60). [USER 2026-09-04] E0 question
3: the pipeline's file enters a statement as a hand-transcribed term. -/

/-- The synthetic file with declared procedures AND a standard library. -/
def prodFileLib (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr) :
    file core_run_annotation :=
  { prodFileWith procs e with stdlib := lib }

/-- `prodFileWith` is the instance at the empty library. -/
theorem prodFileWith_eq_lib (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (e : CoreExpr) : prodFileWith procs e = prodFileLib fmapEmpty procs e := rfl

theorem prodFileLib_stdlib (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr) :
    (prodFileLib lib procs e).stdlib = lib := rfl

/-- `call_proc`'s lookup of `main` on the library-carrying file: `main` is
    not a library name (`hmain`), then the top entry of `funs`. -/
theorem prodFileLib_lookup_main (lib : generic_fun_map Unit core_run_annotation)
    (hmain : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym lib = none)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr) :
    lookupProc (prodFileLib lib procs e) fmapEmpty mainSym = some ([], e) := by
  unfold lookupProc
  rw [show (prodFileLib lib procs e).stdlib = lib from rfl, hmain]
  rw [resolveExtern_empty, show (prodFileLib lib procs e).funs =
      symAdd mainSym (mainDecl e) (procDecls procs) from rfl,
    symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rfl

/-- The production initial run state of the library-carrying file. -/
def prodRSLib (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (sup : Nat)
    (e : CoreExpr) : core_run_state :=
  (initial_core_run_state sup (collect_labeled_continuations_NEW (prodFileLib lib procs e))).1

theorem prodRSLib_labeled (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) :
    (prodRSLib lib procs sup e).labeled =
      collect_labeled_continuations_NEW (prodFileLib lib procs e) := rfl

/-- The driver state after driver_globals on the library-carrying file. -/
def prodPostGlobalsLib (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState) : driver_state :=
  { (initial_driver_state sup (prodFileLib lib procs e) fs).1 with
      core_state0 := { thread_states := [(0, (none, globalsThread))],
                       io := initial_io_state },
      core_run_state0 := { prodRSLib lib procs sup e with tid_supply := 1 } }

/-- The driver state at driver2 entry on the library-carrying file. -/
def prodEntryStateLib (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState) : driver_state :=
  { prodPostGlobalsLib lib procs sup e fs with
      core_state0 := { thread_states := [(0, (none, prodThread e))],
                       io := initial_io_state },
      layout_state := prodMem₀ }

/-- The actual initial run state, with the complete file's collected labels. -/
def fileRunState (F : file core_run_annotation) (sup : Nat) : core_run_state :=
  (initial_core_run_state sup (collect_labeled_continuations_NEW F)).1

/-- The state after spawning thread zero when the file has no globals. -/
def filePostGlobals (F : file core_run_annotation) (sup : Nat)
    (fs : CerbFS.FsState) : driver_state :=
  { (initial_driver_state sup F fs).1 with
      core_state0 := { thread_states := [(0, (none, globalsThread))], io := initial_io_state },
      core_run_state0 := { fileRunState F sup with tid_supply := 1 } }

/-- The thread parked by the shipped parameterless-main startup path. -/
def fileEntryThread (p : sym) (e : CoreExpr) : thread_state :=
  { arena := e, stack0 := Stack_empty, errno := errnoPtr,
    current_loc := CerbLocation.other "Driver.drive",
    exec_loc := ELoc_normal [(p, CerbLocation.other "Driver.drive")],
    env := [fmapEmpty], current_proc_opt := some p }

/-- Driver entry retains all actual file fields and its runtime external map. -/
def fileEntryState (F : file core_run_annotation) (p : sym) (e : CoreExpr)
    (sup : Nat) (fs : CerbFS.FsState) : driver_state :=
  { filePostGlobals F sup fs with
      core_state0 := { thread_states := [(0, (none, fileEntryThread p e))], io := initial_io_state },
      layout_state := prodMem₀ }

/-- The shipped startup prefix for any complete file with no globals and
an identified parameterless main. The reader is empty here; the closed
file theorem below ties it to the file's actual tag definitions. -/
theorem drive_after_setup_file [LF : LemFuel] (hfuel : 2 ≤ LemFuel.fuel)
    (F : file core_run_annotation) (hglobs : F.globs = [])
    (p : sym) (hmain : F.main = some p)
    (loc : CerbLocation.Loc) (marker : Option Nat) (bty : core_base_type) (e : CoreExpr)
    (hlookup : fmapLookupBy symCmpL p F.funs = some (Proc loc marker bty [] e))
    (sup : Nat) (fs : CerbFS.FsState) (args : List String) (dstD : driver_state)
    (hdrv2 : runOne (driver2_lemFuel LemFuel.fuel fmapEmpty false)
        (fileEntryState F p e sup fs) = (NDactive (), dstD)) :
    runOne (_root_.drive fmapEmpty false F args) ((initial_driver_state sup F fs).1) =
      (NDactive (finalize fmapEmpty "drive (without concur)" dstD), dstD) := by
  rcases LF with ⟨fuel⟩
  change 2 ≤ fuel at hfuel
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  letI : LemFuel := ⟨n + 2⟩
  have hpos : 0 < LemFuel.fuel := by change 0 < n + 2; omega
  have htwo : 2 ≤ LemFuel.fuel := by change 2 ≤ n + 2; omega
  conv => lhs; unfold _root_.drive
  refine (runOne_bind_active (hfuel := hpos) (z := (0 : Nat))
    (s' := filePostGlobals F sup fs) (by
      unfold driver_globals
      refine (runOne_bind_active (hfuel := hpos) (z := (0 : Nat))
        (s' := filePostGlobals F sup fs) (by rfl)).trans ?_
      refine (runOne_bind_active (hfuel := hpos)
        (z := ([] : List (sym × generic_globs core_run_annotation Unit))) (by
          change (NDactive F.globs, filePostGlobals F sup fs) = (NDactive [], filePostGlobals F sup fs)
          rw [hglobs])).trans ?_
      rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := filePostGlobals F sup fs) (by rfl)).trans ?_
  rw [show (filePostGlobals F sup fs).core_file.main = some p from hmain]
  refine (runOne_bind_active (hfuel := hpos) (z := p) (by rfl)).trans ?_
  change fmapLookupBy (fun (s1 : sym) (s2 : sym) => ordCompare s1 s2)
    p F.funs = some (Proc loc marker bty [] e) at hlookup
  rw [show (filePostGlobals F sup fs).core_file.funs = F.funs from rfl, hlookup]
  refine (runOne_bind_active (hfuel := hpos)
    (z := (loc, ([] : List (sym × core_base_type)), e)) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := e) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := errnoPtr)
    (s' := { filePostGlobals F sup fs with layout_state := prodMem₀ })
    (runOne_liftMem_active (hfuel := htwo) (errno_init_eq hpos))).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := ()) (s' := dstD) ?_).trans ?_
  · refine (runOne_bind_active (hfuel := hpos) (z := ()) (s' := fileEntryState F p e sup fs)
      (by rfl)).trans ?_
    exact hdrv2
  · refine (runOne_bind_active (hfuel := hpos) (z := dstD) (by rfl)).trans ?_
    rfl

/-- Setup on the library-carrying file with ambient fuel at least two.
    The active driver result uses the same instance and budget as `drive`. -/
theorem drive_after_setup_lib [LF : LemFuel] (hfuel : 2 ≤ LemFuel.fuel)
    (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstD : driver_state)
    (hdrv2 : runOne (driver2_lemFuel LemFuel.fuel fmapEmpty false)
        (prodEntryStateLib lib procs sup e fs) = (NDactive (), dstD)) :
    runOne (_root_.drive fmapEmpty false (prodFileLib lib procs e) args)
        ((initial_driver_state sup (prodFileLib lib procs e) fs).1) =
      (NDactive (finalize fmapEmpty "drive (without concur)" dstD), dstD) := by
  apply drive_after_setup_file hfuel (prodFileLib lib procs e) rfl mainSym rfl
    CerbLocation.unknown none BTy_unit e _ sup fs args dstD hdrv2
  show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls procs)) = _
  rw [symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rfl

/-- With ambient fuel one, setup initializes errno and then memory lifting
    exhausts before the driver's main thread is parked. -/
theorem drive_after_setup_lib_one [LF : LemFuel] (hone : LemFuel.fuel = 1)
    (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) :
    runOne (_root_.drive fmapEmpty false (prodFileLib lib procs e) args)
        ((initial_driver_state sup (prodFileLib lib procs e) fs).1) =
      (NDkilled CerbND.fuelExhaustedKill,
        { prodPostGlobalsLib lib procs sup e fs with layout_state := prodMem₀ }) := by
  rcases LF with ⟨fuel⟩
  change fuel = 1 at hone
  subst fuel
  letI : LemFuel := ⟨1⟩
  conv => lhs; unfold _root_.drive
  refine (runOne_bind_active (hfuel := by decide) (z := (0 : Nat))
    (s' := prodPostGlobalsLib lib procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := by decide) (z := prodPostGlobalsLib lib procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := by decide) (z := mainSym) (by rfl)).trans ?_
  have hlook : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym (prodPostGlobalsLib lib procs sup e fs).core_file.funs = some (mainDecl e) := by
    show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls procs)) = _
    rw [symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rw [hlook]
  refine (runOne_bind_active (hfuel := by decide)
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e)) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := by decide) (z := e) (by rfl)).trans ?_
  refine runOne_bind_killed (hfuel := by decide) ?_
  rw [runOne_liftMem_one rfl]
  exact congrArg (fun mem : Mem =>
    (NDkilled CerbND.fuelExhaustedKill,
      { prodPostGlobalsLib lib procs sup e fs with layout_state := mem }))
    (congrArg Prod.snd (errno_init_eq (by decide)))

/-- Setup on the library-carrying file with ambient fuel at least two.
    A kill from the driver propagates with its actual state. -/
theorem drive_after_setup_lib_killed [LF : LemFuel] (hfuel : 2 ≤ LemFuel.fuel)
    (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr))
    (sup : Nat) (e : CoreExpr) (fs : CerbFS.FsState)
    (args : List String) (dstK : driver_state) (r : kill_reason driver_error)
    (hdrv2 : runOne (driver2_lemFuel LemFuel.fuel fmapEmpty false)
        (prodEntryStateLib lib procs sup e fs) = (NDkilled r, dstK)) :
    runOne (_root_.drive fmapEmpty false (prodFileLib lib procs e) args)
        ((initial_driver_state sup (prodFileLib lib procs e) fs).1) = (NDkilled r, dstK) := by
  rcases LF with ⟨fuel⟩
  change 2 ≤ fuel at hfuel
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  letI : LemFuel := ⟨n + 2⟩
  have hpos : 0 < LemFuel.fuel := by change 0 < n + 2; omega
  have htwo : 2 ≤ LemFuel.fuel := by change 2 ≤ n + 2; omega
  conv => lhs; unfold _root_.drive
  refine (runOne_bind_active (hfuel := hpos) (z := (0 : Nat))
    (s' := prodPostGlobalsLib lib procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := prodPostGlobalsLib lib procs sup e fs) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := mainSym) (by rfl)).trans ?_
  have hlook : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym (prodPostGlobalsLib lib procs sup e fs).core_file.funs = some (mainDecl e) := by
    show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls procs)) = _
    rw [symAdd_lookup (procDecls_symMap procs), if_pos (by decide +kernel)]
  rw [hlook]
  refine (runOne_bind_active (hfuel := hpos)
    (z := (CerbLocation.unknown, ([] : List (sym × core_base_type)), e)) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := e) (by rfl)).trans ?_
  refine (runOne_bind_active (hfuel := hpos) (z := errnoPtr)
    (s' := { prodPostGlobalsLib lib procs sup e fs with layout_state := prodMem₀ })
    (runOne_liftMem_active (hfuel := htwo) (errno_init_eq hpos))).trans ?_
  refine runOne_bind_killed (hfuel := hpos) ?_
  refine (runOne_bind_active (hfuel := hpos) (z := ()) (s' := prodEntryStateLib lib procs sup e fs)
    (by rfl)).trans ?_
  exact hdrv2

/-- THE PRODUCTION RUN EQUATION FOR N-PROCEDURE PROGRAMS OVER A LIBRARY-
    CARRYING FILE (`prod_run_eqJ_procs` at `prodFileLib`; E3): the shipped
    pipeline on `prodFileLib lib procs e` is EXACTLY ONE Active execution
    whose value and final memory satisfy ψ, given the registration tie
    `hlab`, the live-control delivery fact `hdd` at the production context
    OF THAT FILE (the mirror evaluator reads its `stdlib`), and the in-budget
    bound. -/
theorem prod_run_eqJ_lib [LF : LemFuel] (sup : Nat) (lib : generic_fun_map Unit core_run_annotation)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr)
    (hlab : LabeledProcs (prodCtx (prodFileLib lib procs e) (prodRSLib lib procs sup e))
      (prodRSLib lib procs sup e).labeled)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneCtl (prodCtx (prodFileLib lib procs e) (prodRSLib lib procs sup e)) (prodThread e) e
      [fmapEmpty] (prodCtl sup) prodMem₀ ψ k)
    (hfl : k + 2 ≤ LemFuel.fuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib lib procs e) args)
          ((initial_driver_state sup (prodFileLib lib procs e) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  obtain ⟨v, σfin, ρfin, pfin, ℓfin, lcfin, spfin, afin, bfin, rs', tr, ctr, hψ, hloop⟩ :=
    hdd (prodEntryStateLib lib procs sup e fs) fmapEmpty LemFuel.fuel rfl rfl rfl rfl hlab ⟨rfl, rfl⟩ hfl
  have hdrv2 := driver2_done (hfuel := by omega) (LemFuel.fuel - 1) fmapEmpty (prodEntryStateLib lib procs sup e fs) _
    (prodThread e)
    (ctlThread (prodThread e) (ofValA (.pure afin bfin v)) ρfin ⟨[], pfin, ℓfin, lcfin, spfin⟩)
    v rfl hloop rfl
  rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel by omega] at hdrv2
  have hrun := drive_after_setup_lib (hfuel := by omega) lib procs sup e fs args _ hdrv2
  refine ⟨_, _, runND_active (hfuel := by omega) hrun, ?_, rfl, rfl, rfl⟩
  rw [finalize_done (hfuel := by omega) fmapEmpty _ _
    { ctlThread (prodThread e) (ofValA (.pure afin bfin v)) ρfin ⟨[], pfin, ℓfin, lcfin, spfin⟩ with
        stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
  exact hψ

/-- Closed total execution of a complete no-globals file with a
parameterless main. The actual file's tag reader, runtime external map and
registered main labels are retained. The delivery premise is supplied by
the public total logic through the shared launcher. -/
theorem prod_run_eqJ_file [LF : LemFuel]
    (F : file core_run_annotation) (htd : F.tagDefs = fmapEmpty) (hglobs : F.globs = [])
    (p : sym) (hmain : F.main = some p)
    (loc : CerbLocation.Loc) (marker : Option Nat) (bty : core_base_type) (e : CoreExpr)
    (hlookup : fmapLookupBy symCmpL p F.funs = some (Proc loc marker bty [] e))
    (sup : Nat) {Q : LabelMap}
    (hQe : LabeledAt (fileRunState F sup) (resolveExtern (create_extern_symmap F) p) Q)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneAtExtern (create_extern_symmap F) p Q F (fileEntryThread p e)
      e [fmapEmpty] (CerbLocation.other "Driver.drive") ⟨sup, 0⟩ prodMem₀ ψ k)
    (hfl : k + 2 ≤ LemFuel.fuel) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive F.tagDefs false F args) ((initial_driver_state sup F fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  rw [htd]
  obtain ⟨v, σfin, ρfin, lcfin, afin, bfin, rs', tr, ctr, hψ, hloop⟩ :=
    hdd (fileEntryState F p e sup fs) fmapEmpty LemFuel.fuel rfl rfl rfl rfl hQe ⟨rfl, rfl⟩ hfl
  have hdrv2 := driver2_done (hfuel := by omega) (LemFuel.fuel - 1) fmapEmpty
    (fileEntryState F p e sup fs) _ (fileEntryThread p e)
    { fileEntryThread p e with arena := ofValA (.pure afin bfin v), env := ρfin, current_loc := lcfin }
    v rfl hloop rfl
  rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel by omega] at hdrv2
  have hrun := drive_after_setup_file (hfuel := by omega) F hglobs p hmain loc marker bty e
    hlookup sup fs args _ hdrv2
  refine ⟨_, _, runND_active (hfuel := by omega) hrun, ?_, rfl, rfl, rfl⟩
  rw [finalize_done (hfuel := by omega) fmapEmpty _ _
    { { fileEntryThread p e with arena := ofValA (.pure afin bfin v), env := ρfin, current_loc := lcfin }
      with stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
  exact hψ

/-- The one-procedure lane over a library-carrying file
    (`prod_run_eqJ` at `prodFileLib lib []`): the delivery fact
    `DriverDoneAt` is tied to THAT file. -/
theorem prod_run_eqJ_lib1 [LF : LemFuel] (sup : Nat) (lib : generic_fun_map Unit core_run_annotation)
    (e : CoreExpr) {Q : LabelMap}
    (hQe : LabeledAt (prodRSLib lib [] sup e) mainSym Q)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneAt mainSym Q (prodFileLib lib [] e) (prodThread e) e [fmapEmpty]
      (CerbLocation.other "Driver.drive") ⟨sup, 0⟩ prodMem₀ ψ k)
    (hfl : k + 2 ≤ LemFuel.fuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib lib [] e) args)
          ((initial_driver_state sup (prodFileLib lib [] e) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  apply prod_run_eqJ_file (prodFileLib lib [] e) rfl rfl mainSym rfl
    CerbLocation.unknown none BTy_unit e _ sup hQe ψ k hdd hfl fs args
  show fmapLookupBy _ mainSym (symAdd mainSym (mainDecl e) (procDecls [])) = _
  rw [symAdd_lookup (procDecls_symMap []), if_pos (by decide +kernel)]
  rfl

/-- Closed partial correctness for a library-carrying file at every
    ambient budget, with the same setup and outcome classification as
    `prod_run_safe_procs`. The library must not shadow main's procedure
    lookup, and safety concerns this file with this library. -/
theorem prod_run_safe_lib [LF : LemFuel] (sup : Nat) (lib : generic_fun_map Unit core_run_annotation)
    (hmain : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      mainSym lib = none)
    (procs : List (sym × List (sym × core_base_type) × CoreExpr)) (e : CoreExpr)
    (hlab : LabeledProcs (prodCtx (prodFileLib lib procs e) (prodRSLib lib procs sup e))
      (prodRSLib lib procs sup e).labeled)
    (ψ : value → Mem → Prop)
    (hsafe : 2 ≤ LemFuel.fuel → DriverSafeCtl (prodCtx (prodFileLib lib procs e) (prodRSLib lib procs sup e)) (prodThread e) e
      [fmapEmpty] (prodCtl sup) prodMem₀ ψ)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (st : nd_status driver_result driver_error driver_state) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib lib procs e) args)
          ((initial_driver_state sup (prodFileLib lib procs e) fs).1) =
        [(st, ([] : List String), dst')] ∧
      (st = nd_status.Killed dst' CerbND.fuelExhaustedKill ∨
       ∃ dres : driver_result, st = nd_status.Active dres ∧
         ψ dres.dres_core_value dst'.layout_state ∧
         dres.dres_blocked = false ∧
         dres.dres_stdout = "" ∧
         dres.dres_stderr = "") := by
  by_cases hzero : LemFuel.fuel = 0
  · refine ⟨_, (initial_driver_state sup (prodFileLib lib procs e) fs).1, ?_, Or.inl rfl⟩
    unfold CerbND.runND
    rw [hzero]
    rfl
  by_cases hone : LemFuel.fuel = 1
  · exact ⟨_, _, runND_killed (by omega)
      (drive_after_setup_lib_one hone lib procs sup e fs args), Or.inl rfl⟩
  have hfuel : 2 ≤ LemFuel.fuel := by omega
  rcases hsafe hfuel (prodEntryStateLib lib procs sup e fs) fmapEmpty LemFuel.fuel rfl rfl rfl rfl
      hlab (CtlTied.entry hlab (prodFileLib_lookup_main lib hmain procs e) _ _ _) ⟨rfl, rfl⟩ with
    ⟨dstK, hloop⟩ | ⟨v, σfin, ρfin, pfin, ℓfin, lcfin, spfin, afin, bfin, rs', tr, ctr, hψ, hloop⟩
  · have hdrv2 := driver2_killed (by omega) (LemFuel.fuel - 1) fmapEmpty
      (prodEntryStateLib lib procs sup e fs) dstK (prodThread e) _ rfl hloop
    rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel by omega] at hdrv2
    exact ⟨_, _, runND_killed (by omega)
      (drive_after_setup_lib_killed hfuel lib procs sup e fs args _ _ hdrv2), Or.inl rfl⟩
  · have hdrv2 := driver2_done (by omega) (LemFuel.fuel - 1) fmapEmpty
      (prodEntryStateLib lib procs sup e fs) _ (prodThread e)
      (ctlThread (prodThread e) (ofValA (.pure afin bfin v)) ρfin ⟨[], pfin, ℓfin, lcfin, spfin⟩)
      v rfl hloop rfl
    rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel by omega] at hdrv2
    have hrun := drive_after_setup_lib hfuel lib procs sup e fs args _ hdrv2
    refine ⟨_, _, runND_active (by omega) hrun, Or.inr ⟨_, rfl, ?_, rfl, rfl, rfl⟩⟩
    rw [finalize_done (by omega) fmapEmpty _ _
      { ctlThread (prodThread e) (ofValA (.pure afin bfin v)) ρfin ⟨[], pfin, ℓfin, lcfin, spfin⟩
          with stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
    exact hψ

end CerberusHeapLang
