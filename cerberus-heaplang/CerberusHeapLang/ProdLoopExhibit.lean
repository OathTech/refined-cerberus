/-
CerberusHeapLang.ProdLoopExhibit — THE PRODUCTION LOOP THEOREMS
(Phase 5; audit F-05 closed): loop programs certified as equations
about the SHIPPED pipeline

  CerbND.runND (Driver.drive tagDefs false file args)
               (initial_driver_state file fs)

from the COLD START — `initial_driver_state` (Driver.lean:435), the
production state constructor, nothing hand-built in the quantifiers.
The execution function in every public statement here is the shipped
runner: no package `drive`/`driveJ` appears in any statement (the
drive-lane theorems remain as lemmas in their exhibit modules).

BOUNDARY MODULE: the statements quantify over the shipped initial
state, whose `initial_core_run_state` draws sym_supply through the
declared temporal boundary axiom `runEffectful` (see Audit.lean —
provenance, mover, planned upstream retirement). Every theorem here
carries exactly trio + runEffectful, pinned in Audit.lean.

THE PIPELINE THEOREM (`prod_run_eqJ`): `drive_after_setup` (the
ProdEntry cold-start prefix: spawn, main lookup, errno block, park) +
`wpt_driver_done`'s DriverDoneAt (ProdLoop — the total judgment
driving the driver's own per-thread loop, jump rounds included) +
`driver2_done`/`finalize_done` (DriverCollapse). The label map the
driver reads is EXACTLY what the shipped registration computes
(`collect_labeled_continuations_NEW` over the synthetic file — the
ProdEntry registration ties), so nothing is hand-built in the label
plumbing either.

PROOF CLASSIFICATION (2026-09-01 re-audit, R-02): the two
heap-allocating exports here are MIXED logical/operational proofs —
`counter_loop_certified_production`'s cold-start create prefix and
`list_reverse_certified_production`'s chain build (two creates +
four field stores) are explicit certified operational rounds
(`Step.sseq_ctx (Step.create …)`/`Step.sseq_pure` +
`driverDone_step` chains), NOT consumers of the create logic rule
(which is local-only, R-01); the total statement judgment drives the
LOOP SUFFIXES only. `fib_certified_production` (no heap) is the
fully logic-driven positive control. Whole-program logic proofs are
alloc arc P2.
-/
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.ProdExhibit
import CerberusHeapLang.ProdLoop
import CerberusHeapLang.ListRevExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List
open Iris Iris.BI Iris.ProgramLogic
open scoped Iris.Std.PartialMap

/-! ## FIB ON THE SHIPPED PIPELINE — the first production loop
theorem (audit acceptance test 6: "at least one loop theorem
concludes directly about the shipped runND (Driver.drive ...)
computation"). -/

/-- FIB, PRODUCTION FORM: running the SHIPPED pipeline cold on the
    synthetic one-procedure file wrapping the authored iterative-fib
    loop program is EXACTLY ONE Active execution delivering
    `fib n` — a back-edge loop through the production scheduler, the
    label map computed by the shipped registration, termination from
    the total statement judgment (no step-count hypothesis; the one
    bound is the engine's own fuel budget, `lemDefaultFuel = 10^6`).
    No package drive/driveJ in the statement: the execution function
    is the shipped runner. -/
theorem fib_certified_production (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) (hn : 0 ≤ n)
    (hfuel : 2 * n.toNat + 6 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (fibProg ra n sbty ibty abty bbty)) args)
          (initial_driver_state
            (prodFile (fibProg ra n sbty ibty abty bbty)) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = ivVal (fibSpec n.toNat) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := fib_labeledAt_production ra n sbty ibty abty bbty
  have h := prod_run_eqJ (fibProg ra n sbty ibty abty bbty) hQprod
    (fun v _ => v = ivVal (fibSpec n.toNat)) (2 * n.toNat + 4)
    (wpt_driver_done (GF := SpikeGF)
      (M₀ := procCtx mainSym (initial_core_run_state
        (collect_labeled_continuations_NEW
          (prodFile (fibProg ra n sbty ibty abty bbty)))))
      rfl rfl (procCtx_labels hQprod) rfl rfl
      (fun l params cont hl => by
        rw [procCtx_labels hQprod] at hl
        obtain ⟨-, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
        exact fibBody_fragJ ra n)
      (fun l params cont hl => by
        rw [procCtx_labels hQprod] at hl
        obtain ⟨-, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
        rw [fibBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (fibLsT n)
      (fibProg ra n sbty ibty abty bbty) fmapEmpty []
      prodMem₀ (∅ : SpikeHeapF SpikeCell)
      (.save (fibBody_fragJ ra n))
      (by rw [fibProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (coh_empty prodMem₀)
      (fun v _ => v = ivVal (fibSpec n.toNat)) (2 * n.toNat + 4)
      (by
        intro inst
        refine .trans (BigSepM.bigSepM_empty).1 ?_
        refine .trans BI.emp_sep.2 (BI.sep_mono ?_ ?_)
        · exact (fib_blockSpecsT ra n ibty abty bbty mainSym _
            hQprod).trans
            (blockSpecsT_mono (fibPost_to_readout n))
        · exact (fib_wpt ra n ibty abty bbty mainSym _
            hQprod hn sbty).trans
            (wpt_mono (fibPost_to_readout n) _ _ _)))
    (by omega) fs args
  obtain ⟨dres, dst', heq, hval, hbl, hout, herr⟩ := h
  exact ⟨dres, dst', heq, hval, hbl, hout, herr⟩

/-! ## THE COUNTER LOOP ON THE SHIPPED PIPELINE — the second
production loop theorem: a HEAP-EFFECTING loop from the cold start.
The program is SELF-CONTAINED (the exhibitA_prod pattern): it creates
its own cell with the engine's real allocator on the cold-start
memory — deterministically `pxPtr` (allocation id 1 at
0xFFFFFFFFFFF4; errno is id 0), the create result discarded and the
loop authored against the concrete production pointer. The create
prefix crosses the driver through two certified rounds
(`driverDone_step` at the mirror's framed-create and LETS-PURE steps,
with ProdExhibit's concrete cold-start facts); the loop rides the
Phase-5 total lane (`loop_wpt`/`loop_blockSpecsT`). -/

/-- The self-contained production counter program. -/
def counterProdProg (ra : core_run_annotation) (mo : memory_order)
    (bty xbty sbty : core_base_type) (n : Int) : CoreExpr :=
  sseqExpr BTy_unit
    (createRedex loc0 empty_annotation (CerbMem.integerIval 4) intTy
      (PrefOther "spike-x"))
    (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n)

/-- The shipped registration computes the counter loop's label map
    (the save sits in tail position under the create prefix). -/
theorem collect_new_counterProd (ra : core_run_annotation)
    (mo : memory_order) (bty xbty sbty : core_base_type) (n : Int) :
    collect_labeled_continuations_NEW
        (prodFile (counterProdProg ra mo bty xbty sbty n)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (loopQ loc0 empty_annotation ra mo bty xbty pxPtr) fmapEmpty := rfl

/-- THE TIE at the production initial run state of the synthetic
    counter file. -/
theorem counterProd_labeledAt (ra : core_run_annotation)
    (mo : memory_order) (bty xbty sbty : core_base_type) (n : Int) :
    LabeledAt (initial_core_run_state (collect_labeled_continuations_NEW
        (prodFile (counterProdProg ra mo bty xbty sbty n))))
      mainSym (loopQ loc0 empty_annotation ra mo bty xbty pxPtr) := by
  unfold LabeledAt
  rw [show (initial_core_run_state (collect_labeled_continuations_NEW
      (prodFile (counterProdProg ra mo bty xbty sbty n)))).labeled =
    collect_labeled_continuations_NEW
      (prodFile (counterProdProg ra mo bty xbty sbty n)) from rfl]
  rw [collect_new_counterProd]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem counterProdProg_pot (ra : core_run_annotation)
    (mo : memory_order) (bty xbty sbty : core_base_type) (n : Int) :
    pot (counterProdProg ra mo bty xbty sbty n) = 6 := rfl

theorem loopProg_pot (ra : core_run_annotation) (mo : memory_order)
    (bty xbty sbty : core_base_type) (n : Int) :
    pot (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n) = 5 := rfl

theorem loopBody_pot_prod (ra : core_run_annotation) (mo : memory_order)
    (bty : core_base_type) :
    pot (loopBody loc0 empty_annotation ra mo bty pxPtr) = 4 := rfl

/-- The production initial run state of the synthetic counter file
    (the context the mirror steps and the tie live at). -/
def counterProdRS (ra : core_run_annotation) (mo : memory_order)
    (bty xbty sbty : core_base_type) (n : Int) : core_run_state :=
  initial_core_run_state (collect_labeled_continuations_NEW
    (prodFile (counterProdProg ra mo bty xbty sbty n)))

/-- THE COUNTER LOOP, PRODUCTION FORM: running the SHIPPED pipeline
    cold on the self-contained counter file is EXACTLY ONE Active
    execution delivering `Vunit`, with the created cell's final bytes
    decided by the loop's data — untouched (the allocator's image)
    for `n = 0`, the stored seven-image for `0 < n` — stated as
    `CellCoh` of the final layout state at the concrete production
    allocation. Cold start, shipped registration, termination from
    the total judgment; no package drive/driveJ in the statement. -/
theorem counter_loop_certified_production (ra : core_run_annotation)
    (mo : memory_order) (bty xbty sbty : core_base_type)
    (n : Int) (hn : 0 ≤ n)
    (hfuel : 5 * n.toNat + 7 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (counterProdProg ra mo bty xbty sbty n)) args)
          (initial_driver_state
            (prodFile (counterProdProg ra mo bty xbty sbty n)) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = Vunit ∧
      (∃ bs', ((n = 0 ∧ bs' = cellXP.bytes) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
        CellCoh dst'.layout_state 1 ⟨pxAddr, intTy, bs'⟩) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := counterProd_labeledAt ra mo bty xbty sbty n
  have hlb : (procCtx mainSym (counterProdRS ra mo bty xbty sbty n)).labels =
      loopQ loc0 empty_annotation ra mo bty xbty pxPtr :=
    procCtx_labels hQprod
  -- the loop part, delivered by the total-driven driver simulation
  have hddLoop : DriverDoneAt mainSym
      (loopQ loc0 empty_annotation ra mo bty xbty pxPtr)
      (prodThread (counterProdProg ra mo bty xbty sbty n))
      (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n)
      [fmapEmpty] σcP
      (fun v σ' => v = Vunit ∧ ∃ bs',
        ((n = 0 ∧ bs' = cellXP.bytes) ∨ (0 < n ∧ bs' = sevenBytes)) ∧
        ∃ i a, pxPtr = cellPtr i a ∧ CellCoh σ' i ⟨a, intTy, bs'⟩)
      (5 * n.toNat + 3) := by
    refine wpt_driver_done (GF := SpikeGF) (M₀ := procCtx mainSym (counterProdRS ra mo bty xbty sbty n))
      rfl rfl hlb rfl rfl
      (fun l params cont hl => by
        rw [hlb] at hl
        obtain ⟨-, rfl⟩ := loopQ_inv loc0 empty_annotation ra mo bty xbty
          pxPtr hl
        exact loopBody_fragJ loc0 empty_annotation ra mo bty pxPtr loc0_lib)
      (fun l params cont hl => by
        rw [hlb] at hl
        obtain ⟨-, rfl⟩ := loopQ_inv loc0 empty_annotation ra mo bty xbty
          pxPtr hl
        rw [loopBody_pot_prod ra mo bty,
          show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (loopLsT pxPtr n cellXP.bytes)
      (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n)
      fmapEmpty [] σcP mAP
      (.save (loopBody_fragJ loc0 empty_annotation ra mo bty pxPtr loc0_lib))
      (by rw [loopProg_pot ra mo bty xbty sbty n,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      coh_mAP _ _ ?_
    intro inst
    refine .trans bigSep_ptx_P ?_
    refine .trans BI.emp_sep.2 (BI.sep_mono ?_ ?_)
    · exact (loop_blockSpecsT loc0 empty_annotation ra mo bty xbty pxPtr n
        cellXP.bytes mainSym (counterProdRS ra mo bty xbty sbty n) hQprod).trans
        (blockSpecsT_mono (loopPost_to_readout pxPtr n cellXP.bytes))
    · exact (loop_wpt loc0 empty_annotation ra mo bty xbty pxPtr n
        cellXP.bytes mainSym (counterProdRS ra mo bty xbty sbty n) hQprod hn sbty).trans
        (wpt_mono (loopPost_to_readout pxPtr n cellXP.bytes) _ _ _)
  -- the create prefix, two certified production rounds
  have hs₂ : Step (procCtx mainSym (counterProdRS ra mo bty xbty sbty n))
      (sseqExpr BTy_unit
        (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pxPtr))))))
        (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n),
        [fmapEmpty], σcP)
      (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n,
        [fmapEmpty], σcP) :=
    Step.sseq_pure
  have hs₁ : Step (procCtx mainSym (counterProdRS ra mo bty xbty sbty n))
      (counterProdProg ra mo bty xbty sbty n, [fmapEmpty], prodMem₀)
      (sseqExpr BTy_unit
        (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pxPtr))))))
        (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n),
        [fmapEmpty], σcP) :=
    Step.sseq_ctx rfl (Step.create rfl rfl create_applies)
  have hf₁ : Frag (sseqExpr BTy_unit
      (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pxPtr))))))
      (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n)) :=
    .sseq (frag_ofVal (.pure (Vobject (OVpointer pxPtr))))
      (.save (loopBody_fragJ loc0 empty_annotation ra mo bty pxPtr loc0_lib))
  have hf₀ : Frag (counterProdProg ra mo bty xbty sbty n) :=
    .sseq (.create loc0_lib)
      (.save (loopBody_fragJ loc0 empty_annotation ra mo bty pxPtr loc0_lib))
  have hdd₁ := driverDone_step (M₀ := procCtx mainSym (counterProdRS ra mo bty xbty sbty n)) rfl rfl hlb rfl
    hf₁ (Nat.le_trans hf₁.esize_le_pot (by
      rw [show pot (sseqExpr BTy_unit
        (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer pxPtr))))))
        (loopProg loc0 empty_annotation ra mo bty xbty sbty pxPtr n)) = 6
        from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
      omega))
    hs₂ hddLoop
  have hdd₀ := driverDone_step (M₀ := procCtx mainSym (counterProdRS ra mo bty xbty sbty n)) rfl rfl hlb rfl
    hf₀ (Nat.le_trans hf₀.esize_le_pot (by
      rw [counterProdProg_pot ra mo bty xbty sbty n,
        show lemDefaultFuel = 999999 + 1 from rfl]
      omega))
    hs₁ hdd₁
  -- the pipeline equation
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ (counterProdProg ra mo bty xbty sbty n) hQprod
      _ ((5 * n.toNat + 3) + 1 + 1) hdd₀
      (by rw [show lemDefaultFuel = 999999 + 1 from rfl] at hfuel ⊢; omega)
      fs args
  obtain ⟨hval, bs', harm, i, a, hpv, hcc⟩ := hψ
  obtain ⟨rfl, rfl⟩ := cellPtr_inj hpv.symm
  exact ⟨dres, dst', heq, hval, ⟨bs', harm, hcc⟩, hbl, hout, herr⟩

/-! ## LIST REVERSAL ON THE SHIPPED PIPELINE — the flagship's
production instance: a SELF-CONTAINED two-node demo. A cold-start
production statement cannot quantify a seeded chain (the initial
memory is pinned to the shipped constructor), so the program BUILDS
its chain with the engine's own operations — two node creates
(deterministically ids 1 and 2 at the production allocator's
addresses), four field stores initializing (value, next) per node —
and then runs the AUTHORED flagship reversal loop `lrProg` against
the built head. The creates cross the driver as certified rounds;
the stores and the loop ride ONE total judgment (the store residue's
LETS-ANNOT annotations are absorbed by the erased-value readout —
`readoutPost_mergeInto_annot`). The conclusion is the flagship's
shape at the demo instance: the delivered value heads a footprint
seeded as the REVERSED chain — same allocation ids, own values —
satisfied by the final production memory. -/

/-- The production node addresses (the engine's own allocator on the
    cold-start memory: errno is id 0; the two 16-byte, 8-aligned node
    allocations land here — pinned by `lr_create*_applies`, `rfl`). -/
def lrA1 : Int := 281474976710632
def lrA2 : Int := 281474976710616

def lrN1 : CerbMem.PointerValue := cellPtr 1 lrA1
def lrN2 : CerbMem.PointerValue := cellPtr 2 lrA2

/-- The demo's node list: ids with their own values. -/
def lrProdNs : List (Int × Int) := [(1, 1), (2, 2)]

/-- Core loaded-long values/mvals for the value fields. -/
def longVal (v : Int) : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval v)))

def longMval (v : Int) : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Long) (CerbMem.integerIval v)

/-! ### The engine's own builds: creates on the cold-start memory -/

def lrSeed1 : Option (CerbMem.PointerValue × Mem) :=
  applyMemM (CerbMem.allocateObject 0 (PrefOther "lr-n1")
    (CerbMem.integerIval 8) nodeTy none none) prodMem₀

def σLr1 : Mem := match lrSeed1 with | some (_, σ) => σ | none => {}

theorem lr_create1_applies :
    applyMemM (CerbMem.allocateObject 0 (PrefOther "lr-n1")
      (CerbMem.integerIval 8) nodeTy none none) prodMem₀ =
      some (lrN1, σLr1) := rfl

def lrSeed2 : Option (CerbMem.PointerValue × Mem) :=
  applyMemM (CerbMem.allocateObject 0 (PrefOther "lr-n2")
    (CerbMem.integerIval 8) nodeTy none none) σLr1

def σLr2 : Mem := match lrSeed2 with | some (_, σ) => σ | none => {}

theorem lr_create2_applies :
    applyMemM (CerbMem.allocateObject 0 (PrefOther "lr-n2")
      (CerbMem.integerIval 8) nodeTy none none) σLr1 =
      some (lrN2, σLr2) := rfl

/-! ### The uninitialized node cells at the post-create state -/

abbrev lrCell1u : SpikeCell :=
  ⟨lrA1, nodeTy, CerbMem.readBytesFrom σLr2 lrA1 16⟩

abbrev lrCell2u : SpikeCell :=
  ⟨lrA2, nodeTy, CerbMem.readBytesFrom σLr2 lrA2 16⟩

open Iris.Std.PartialMap in
def lrM0 : CellMap :=
  insert (insert (∅ : SpikeHeapF SpikeCell) 2 lrCell2u) 1 lrCell1u

def lrAlloc1 : CerbMem.Allocation :=
  { base := lrA1, size := 16, ty := some nodeTy,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "lr-n1") none,
    prefix_ := PrefOther "lr-n1" }

def lrAlloc2 : CerbMem.Allocation :=
  { base := lrA2, size := 16, ty := some nodeTy,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "lr-n2") none,
    prefix_ := PrefOther "lr-n2" }

theorem σLr2_allocations :
    σLr2.allocations =
      (((({} : Mem).allocations.insert 0 errnoAllocRec).insert 1
        lrAlloc1).insert 2 lrAlloc2) := rfl

theorem lr1_alloc_get : σLr2.allocations.get? 1 = some lrAlloc1 := by
  rw [σLr2_allocations]
  rfl

theorem lr2_alloc_get : σLr2.allocations.get? 2 = some lrAlloc2 := by
  rw [σLr2_allocations]
  simp

theorem lr_bytes_len (a : Int) :
    (CerbMem.readBytesFrom σLr2 a 16).length = 16 := by
  unfold CerbMem.readBytesFrom
  simp

theorem cellCohLr1 : CellCoh σLr2 1 lrCell1u :=
  ⟨rfl, ⟨lrAlloc1, lr1_alloc_get, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype lrCell1u.ty = 16 from rfl]
      exact lr_bytes_len lrA1,
   by rw [show CerbMem.sizeofCtype lrCell1u.ty = 16 from rfl],
   fun _ _ => rfl⟩

theorem cellCohLr2 : CellCoh σLr2 2 lrCell2u :=
  ⟨rfl, ⟨lrAlloc2, lr2_alloc_get, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype lrCell2u.ty = 16 from rfl]
      exact lr_bytes_len lrA2,
   by rw [show CerbMem.sizeofCtype lrCell2u.ty = 16 from rfl],
   fun _ _ => rfl⟩

open Iris.Std.PartialMap in
theorem coh_lrM0 : Coh σLr2 lrM0 := by
  refine ⟨?_, ?_⟩
  · intro id c h
    by_cases h1 : id = 1
    · subst h1
      rw [lrM0, Iris.Std.get?_insert_eq rfl] at h
      cases h
      exact cellCohLr1
    · rw [lrM0, Iris.Std.get?_insert_ne (fun h' => h1 h'.symm)] at h
      by_cases h2 : id = 2
      · subst h2
        rw [Iris.Std.get?_insert_eq rfl] at h
        cases h
        exact cellCohLr2
      · rw [Iris.Std.get?_insert_ne (fun h' => h2 h'.symm),
          Iris.Std.LawfulPartialMap.get?_empty] at h
        cases h
  · intro id1 id2 c1 c2 hne h1 h2
    have hget : ∀ (j : Int) (c : SpikeCell),
        Iris.Std.PartialMap.get? lrM0 j = some c →
        (j = 1 ∧ c = lrCell1u) ∨ (j = 2 ∧ c = lrCell2u) := by
      intro j c h
      by_cases hj1 : j = 1
      · subst hj1
        rw [lrM0, Iris.Std.get?_insert_eq rfl] at h
        cases h
        exact .inl ⟨rfl, rfl⟩
      · rw [lrM0, Iris.Std.get?_insert_ne (fun h' => hj1 h'.symm)] at h
        by_cases hj2 : j = 2
        · subst hj2
          rw [Iris.Std.get?_insert_eq rfl] at h
          cases h
          exact .inr ⟨rfl, rfl⟩
        · rw [Iris.Std.get?_insert_ne (fun h' => hj2 h'.symm),
            Iris.Std.LawfulPartialMap.get?_empty] at h
          cases h
    rcases hget id1 c1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hget id2 c2 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · exact Or.inr (show lrCell2u.addr +
        (CerbMem.sizeofCtype lrCell2u.ty : Int) ≤ lrCell1u.addr from by
          rw [show CerbMem.sizeofCtype lrCell2u.ty = 16 from rfl,
            show lrCell2u.addr = lrA2 from rfl,
            show lrCell1u.addr = lrA1 from rfl]
          unfold lrA1 lrA2
          omega)
    · exact Or.inl (show lrCell2u.addr +
        (CerbMem.sizeofCtype lrCell2u.ty : Int) ≤ lrCell1u.addr from by
          rw [show CerbMem.sizeofCtype lrCell2u.ty = 16 from rfl,
            show lrCell2u.addr = lrA2 from rfl,
            show lrCell1u.addr = lrA1 from rfl]
          unfold lrA1 lrA2
          omega)
    · exact absurd rfl hne

/-! ### The program -/

/-- The store suffix + the flagship loop (everything after the two
    creates — the wpt-covered part). -/
def lrProdSuffix (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) : CoreExpr :=
  sseqExpr BTy_unit
    (storeExpr loc0 empty_annotation longTy
      (cellPtr 1 (lrA1 + ((0 : Nat) : Int))) (longVal 1) mo)
    (sseqExpr BTy_unit
      (storeExpr loc0 empty_annotation nodePtrTy
        (cellPtr 1 (lrA1 + ((8 : Nat) : Int))) (ptrVal lrN2) mo)
      (sseqExpr BTy_unit
        (storeExpr loc0 empty_annotation longTy
          (cellPtr 2 (lrA2 + ((0 : Nat) : Int))) (longVal 2) mo)
        (sseqExpr BTy_unit
          (storeExpr loc0 empty_annotation nodePtrTy
            (cellPtr 2 (lrA2 + ((8 : Nat) : Int))) nullVal mo)
          (lrProg loc0 empty_annotation ra mo sbty pbty cbty bbty nbty
            ubty lrN1))))

/-- The self-contained production reversal program. -/
def lrProdProg (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) : CoreExpr :=
  sseqExpr BTy_unit
    (createRedex loc0 empty_annotation (CerbMem.integerIval 8) nodeTy
      (PrefOther "lr-n1"))
    (sseqExpr BTy_unit
      (createRedex loc0 empty_annotation (CerbMem.integerIval 8) nodeTy
        (PrefOther "lr-n2"))
      (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty))

/-! The registration computation, COMPOSITIONALLY (a whole-program
`rfl` hits kernel-whnf term duplication on the six-`Esseq` spine —
the fuel-peeled per-arm equations below rewrite layer by layer with
sharing, each step one cheap `rfl`; the inner loop program's
computation is one bounded-fuel `rfl`). -/

theorem col_aux_action {A : Type} (n : Nat) (st : collect_saves_state A)
    (a : List annot) (p : generic_paction A Unit sym) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Eaction p)) = st := rfl

theorem col_aux_sseq {A : Type} (n : Nat) (st : collect_saves_state A)
    (a : List annot) (pat : pattern) (e1 e2 : generic_expr A Unit sym) :
    collect_saves_aux_lemFuel (n + 1) st (Expr a (Esseq pat e1 e2)) =
      union_saves st (union_saves
        { collect_saves_aux_lemFuel n empty_saves e1 with
            tmp_acc := fmapMap (fun p => match p with
              | (syms, e) => (syms, Expr a (Esseq pat e e2)))
              (collect_saves_aux_lemFuel n empty_saves e1).tmp_acc }
        (collect_saves_aux_lemFuel n empty_saves e2)) := rfl

/-- The flagship loop program's saves, at cushioned variable fuel
    (the save registers its body; nothing else in the cone
    contributes). -/
theorem col_lrProg (m : Nat) (ann ra : core_run_annotation)
    (mo : memory_order) (sbty pbty cbty bbty nbty ubty : core_base_type)
    (pv : CerbMem.PointerValue) :
    collect_saves_aux_lemFuel (m + 9) empty_saves
      (lrProg loc0 ann ra mo sbty pbty cbty bbty nbty ubty pv) =
      { tmp_acc := lrQ loc0 ann ra mo pbty cbty bbty nbty ubty,
        closed_acc := fmapEmpty } := rfl

theorem col_lrProdProg (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) :
    collect_saves (lrProdProg ra mo sbty pbty cbty bbty nbty ubty) =
      lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty := by
  unfold collect_saves collect_saves_aux lrProdProg lrProdSuffix sseqExpr
    createRedex storeExpr
  dsimp only
  rw [show lemDefaultFuel = 999999 + 1 from rfl]
  rw [col_aux_sseq]
  rw [show (999999 : Nat) = 999998 + 1 from rfl]
  rw [col_aux_action, col_aux_sseq]
  rw [show (999998 : Nat) = 999997 + 1 from rfl]
  rw [col_aux_action, col_aux_sseq]
  rw [show (999997 : Nat) = 999996 + 1 from rfl]
  rw [col_aux_action, col_aux_sseq]
  rw [show (999996 : Nat) = 999995 + 1 from rfl]
  rw [col_aux_action, col_aux_sseq]
  rw [show (999995 : Nat) = 999994 + 1 from rfl]
  rw [col_aux_action, col_aux_sseq]
  rw [show (999994 : Nat) = 999993 + 1 from rfl]
  rw [col_aux_action]
  rw [show (999993 : Nat) = 999984 + 9 from rfl]
  rw [col_lrProg]
  rfl

/-- The shipped registration computes the flagship loop's label map
    through the whole build prefix. -/
theorem collect_new_lrProd (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) :
    collect_labeled_continuations_NEW
        (prodFile (lrProdProg ra mo sbty pbty cbty bbty nbty ubty)) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
        (lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty)
        fmapEmpty := by
  rw [show collect_labeled_continuations_NEW
      (prodFile (lrProdProg ra mo sbty pbty cbty bbty nbty ubty)) =
    fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      (collect_saves (lrProdProg ra mo sbty pbty cbty bbty nbty ubty))
      fmapEmpty from rfl]
  rw [col_lrProdProg]

theorem lrProd_labeledAt (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) :
    LabeledAt (initial_core_run_state (collect_labeled_continuations_NEW
        (prodFile (lrProdProg ra mo sbty pbty cbty bbty nbty ubty))))
      mainSym (lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty) := by
  unfold LabeledAt
  rw [show (initial_core_run_state (collect_labeled_continuations_NEW
      (prodFile (lrProdProg ra mo sbty pbty cbty bbty nbty ubty)))).labeled =
    collect_labeled_continuations_NEW
      (prodFile (lrProdProg ra mo sbty pbty cbty bbty nbty ubty)) from rfl]
  rw [collect_new_lrProd]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- The production initial run state of the synthetic reversal file. -/
def lrProdRS (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) : core_run_state :=
  initial_core_run_state (collect_labeled_continuations_NEW
    (prodFile (lrProdProg ra mo sbty pbty cbty bbty nbty ubty)))

/-! ### Cone membership and potentials -/

theorem lrProdSuffix_frag (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) :
    Frag (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty) :=
  .sseq (.store loc0_lib) (.sseq (.store loc0_lib)
    (.sseq (.store loc0_lib) (.sseq (.store loc0_lib)
      (.save (lrBody_fragJ loc0 empty_annotation ra mo bbty nbty ubty
        loc0_lib)))))

theorem lrProdProg_frag (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) :
    Frag (lrProdProg ra mo sbty pbty cbty bbty nbty ubty) :=
  .sseq (.create loc0_lib) (.sseq (.create loc0_lib)
    (lrProdSuffix_frag ra mo sbty pbty cbty bbty nbty ubty))

theorem pot_sseqExpr (bty : core_base_type) (e1 e2 : CoreExpr) :
    pot (sseqExpr bty e1 e2) = 1 + max (pot e1) (pot e2) := rfl

theorem pot_storeExpr (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (ty : ctype) (pv : CerbMem.PointerValue) (cv : value)
    (mo : memory_order) :
    pot (storeExpr loc ann ty pv cv mo) = 2 := rfl

theorem pot_createRedex (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (align : CerbMem.IntegerValue)
    (ty : ctype) (pref : prefix0) :
    pot (createRedex loc ann align ty pref) = 2 := rfl

theorem lrProdSuffix_pot (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) :
    pot (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty) = 11 := by
  unfold lrProdSuffix
  rw [pot_sseqExpr, pot_sseqExpr, pot_sseqExpr, pot_sseqExpr,
    pot_storeExpr, pot_storeExpr, pot_storeExpr, pot_storeExpr,
    lrProg_pot loc0 empty_annotation ra mo pbty cbty bbty nbty ubty
      sbty lrN1]
  rfl

theorem lrProdProg_pot (ra : core_run_annotation) (mo : memory_order)
    (sbty pbty cbty bbty nbty ubty : core_base_type) :
    pot (lrProdProg ra mo sbty pbty cbty bbty nbty ubty) = 13 := by
  unfold lrProdProg
  rw [pot_sseqExpr, pot_sseqExpr, pot_createRedex, pot_createRedex,
    lrProdSuffix_pot ra mo sbty pbty cbty bbty nbty ubty]
  rfl

/-! ### THE EXPORT -/

/-- LIST REVERSAL, PRODUCTION FORM (the flagship's demo instance on
    the shipped pipeline): running `runND ∘ Driver.drive ∘
    initial_driver_state` cold on the self-contained two-node
    build-and-reverse file is EXACTLY ONE Active execution whose
    delivered value heads a footprint `Q` seeded as the REVERSED
    chain — the same two engine-allocated nodes (ids 1, 2 with their
    own values), relinked in reversed order — with the final
    production memory satisfying `Q`. Cold start, shipped
    registration, termination from the total judgment; no package
    drive/driveJ in the statement. -/
theorem list_reverse_certified_production (ra : core_run_annotation)
    (mo : memory_order) (sbty pbty cbty bbty nbty ubty : core_base_type)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (lrProdProg ra mo sbty pbty cbty bbty nbty ubty)) args)
          (initial_driver_state
            (prodFile (lrProdProg ra mo sbty pbty cbty bbty nbty ubty)) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      (∃ (Q : CellMap) (p' : CerbMem.PointerValue),
        dres.dres_core_value = ptrVal p' ∧
        SeedChain Q p' lrProdNs.reverse ∧
        Sat dst'.layout_state Q) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := lrProd_labeledAt ra mo sbty pbty cbty bbty nbty ubty
  have hlb : (procCtx mainSym
      (lrProdRS ra mo sbty pbty cbty bbty nbty ubty)).labels =
      lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty :=
    procCtx_labels hQprod
  -- the store suffix + the loop, delivered by the total-driven
  -- driver simulation from the post-create state
  have hddSuffix : DriverDoneAt mainSym
      (lrQ loc0 empty_annotation ra mo pbty cbty bbty nbty ubty)
      (prodThread (lrProdProg ra mo sbty pbty cbty bbty nbty ubty))
      (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty)
      [fmapEmpty] σLr2
      (fun v σ' => ∃ Q : CellMap,
        (∃ p' : CerbMem.PointerValue, v = ptrVal p' ∧
          SeedChain Q p' lrProdNs.reverse) ∧
        Q ##ₘ (∅ : CellMap) ∧
        Coh σ' (Iris.Std.PartialMap.union Q (∅ : CellMap)))
      (3 + (3 + (3 + (3 + (lrCost lrProdNs.length + 1))))) := by
    refine wpt_driver_done (GF := SpikeGF)
      (M₀ := procCtx mainSym (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
      rfl rfl hlb rfl rfl
      (fun l params cont hl => by
        rw [hlb] at hl
        obtain ⟨-, rfl⟩ := lrQ_inv loc0 empty_annotation ra mo pbty cbty
          bbty nbty ubty hl
        exact lrBody_fragJ loc0 empty_annotation ra mo bbty nbty ubty
          loc0_lib)
      (fun l params cont hl => by
        rw [hlb] at hl
        obtain ⟨-, rfl⟩ := lrQ_inv loc0 empty_annotation ra mo pbty cbty
          bbty nbty ubty hl
        rw [lrBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (lrLsT lrProdNs (lrCellFrame (∅ : CellMap)))
      (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty)
      fmapEmpty [] σLr2
      (Iris.Std.PartialMap.insert
        (Iris.Std.PartialMap.insert (∅ : SpikeHeapF SpikeCell) 2 lrCell2u)
        1 lrCell1u)
      (lrProdSuffix_frag ra mo sbty pbty cbty bbty nbty ubty)
      (by rw [lrProdSuffix_pot ra mo sbty pbty cbty bbty nbty ubty,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      coh_lrM0 _ _ ?_
    intro inst
    refine .trans BI.emp_sep.2 (BI.sep_mono ?_ ?_)
    · exact (lr_blockSpecsT loc0 empty_annotation ra mo pbty cbty bbty
        nbty ubty lrProdNs (lrCellFrame (∅ : CellMap)) mainSym
        (lrProdRS ra mo sbty pbty cbty bbty nbty ubty) hQprod).trans
        (blockSpecsT_mono (lrPost_readout lrProdNs (∅ : CellMap)))
    · -- the store suffix's total judgment, from the two uninit cells
      iintro Hm
      icases (BigSepM.bigSepM_insert
          (Φ := fun (i : Int) (c : SpikeCell) =>
            cellOwn (hlc := .hasLC) (GF := SpikeGF) i (.own 1) c)
          (i := 1) (x := lrCell1u)
          (by rw [Iris.Std.get?_insert_ne (by omega : (2 : Int) ≠ 1),
            Iris.Std.LawfulPartialMap.get?_empty])).1 $$ Hm
        with ⟨H1, Hrest⟩
      ihave H2 : cellOwn (hlc := .hasLC) (GF := SpikeGF) 2 (.own 1)
          lrCell2u $$ [Hrest]
      · icases (BigSepM.bigSepM_insert
            (Φ := fun (i : Int) (c : SpikeCell) =>
              cellOwn (hlc := .hasLC) (GF := SpikeGF) i (.own 1) c)
            (i := 2) (x := lrCell2u)
            (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 2)).1
          $$ Hrest with ⟨H2, -⟩
        iexact H2
      -- store 1: node 1's value field
      rw [show lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty =
        Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
          (storeExpr loc0 empty_annotation longTy
            (cellPtr 1 (lrA1 + ((0 : Nat) : Int))) (longVal 1) mo)
          (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
            (storeExpr loc0 empty_annotation nodePtrTy
              (cellPtr 1 (lrA1 + ((8 : Nat) : Int))) (ptrVal lrN2) mo)
            (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
              (storeExpr loc0 empty_annotation longTy
                (cellPtr 2 (lrA2 + ((0 : Nat) : Int))) (longVal 2) mo)
              (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
                (storeExpr loc0 empty_annotation nodePtrTy
                  (cellPtr 2 (lrA2 + ((8 : Nat) : Int))) nullVal mo)
                (lrProg loc0 empty_annotation ra mo sbty pbty cbty bbty
                  nbty ubty lrN1)))))))) from rfl]
      iapply wpt_seq
      iapply wpt_store_cell_at (mv := longMval 1) loc0 empty_annotation 1
        lrA1 nodeTy 0 longTy
        (longVal 1) mo lrCell1u.bytes [fmapEmpty] (Nat.le_refl 3) rfl
        (by rw [show CerbMem.sizeofCtype longTy = 8 from rfl,
          show CerbMem.sizeofCtype nodeTy = 16 from rfl]; omega)
        rfl (fun _ => rfl) (fun _ => rfl) rfl (fun lum fpm => rfl)
      isplitl [H1]
      · iexact H1
      iintro %fp1 H1
      rw [readoutPost_mergeInto_annot]
      -- store 2: node 1's next field
      iapply wpt_seq
      iapply wpt_store_cell_at loc0 empty_annotation 1 lrA1 nodeTy 8
        nodePtrTy (ptrVal lrN2) mo
        (spliceBytes 0 (CerbMem.memValueToBytes [] (longMval 1)).2
          lrCell1u.bytes)
        [fmapEmpty] (Nat.le_refl 3) (node_ptr_encodes lrN2)
        (by rw [show CerbMem.sizeofCtype nodePtrTy = 8 from rfl,
          show CerbMem.sizeofCtype nodeTy = 16 from rfl]; omega)
        (node_ptr_compat lrN2) (node_ptr_fpm_cell 2 lrA2)
        (fun _ => rfl)
        (by rw [show lrN2 = cellPtr 2 lrA2 from rfl, node_ptr_img_cell]
            exact ptrImg_cell_length 2 lrA2)
        (fun lum fpm => rfl)
      isplitl [H1]
      · iexact H1
      iintro %fp2 H1
      rw [readoutPost_mergeInto_annot]
      -- store 3: node 2's value field
      iapply wpt_seq
      iapply wpt_store_cell_at (mv := longMval 2) loc0 empty_annotation 2
        lrA2 nodeTy 0 longTy
        (longVal 2) mo lrCell2u.bytes [fmapEmpty] (Nat.le_refl 3) rfl
        (by rw [show CerbMem.sizeofCtype longTy = 8 from rfl,
          show CerbMem.sizeofCtype nodeTy = 16 from rfl]; omega)
        rfl (fun _ => rfl) (fun _ => rfl) rfl (fun lum fpm => rfl)
      isplitl [H2]
      · iexact H2
      iintro %fp3 H2
      rw [readoutPost_mergeInto_annot]
      -- store 4: node 2's next field (null)
      iapply wpt_seq
      iapply wpt_store_cell_at loc0 empty_annotation 2 lrA2 nodeTy 8
        nodePtrTy nullVal mo
        (spliceBytes 0 (CerbMem.memValueToBytes [] (longMval 2)).2
          lrCell2u.bytes)
        [fmapEmpty] (Nat.le_refl 3) (node_ptr_encodes nullNode)
        (by rw [show CerbMem.sizeofCtype nodePtrTy = 8 from rfl,
          show CerbMem.sizeofCtype nodeTy = 16 from rfl]; omega)
        (node_ptr_compat nullNode) (fun _ => rfl) (fun _ => rfl)
        (by rw [node_ptr_img_null]; exact ptrImg_null_length)
        (fun lum fpm => rfl)
      isplitl [H2]
      · iexact H2
      iintro %fp4 H2
      rw [readoutPost_mergeInto_annot]
      -- the flagship loop from the built chain
      iapply ((lr_wpt loc0 empty_annotation ra mo pbty cbty bbty nbty ubty
        lrProdNs (lrCellFrame (∅ : CellMap)) mainSym
        (lrProdRS ra mo sbty pbty cbty bbty nbty ubty) hQprod sbty
        lrN1).trans
        (wpt_mono (lrPost_readout lrProdNs (∅ : CellMap)) _ _ _))
      isplitl [H1 H2]
      · -- isList lrN1 [(1,1),(2,2)] from the two built cells
        rw [show lrN1 = cellPtr 1 lrA1 from rfl,
          show lrProdNs = [((1 : Int), (1 : Int)), (2, 2)] from rfl]
        iapply isList_cons_intro 1 lrA1 lrN2
          (spliceBytes 8 (CerbMem.memValueToBytes []
            (CerbMem.pointerMval nodeTy lrN2)).2
            (spliceBytes 0 (CerbMem.memValueToBytes [] (longMval 1)).2
              lrCell1u.bytes))
          1 [(2, 2)] (by unfold lrA1; omega) (by unfold lrA1; omega) rfl
          (fun lum fpm ad => rfl)
          (nodeNextDec_ptrImg_cell 2 lrA2 (by unfold lrA2; omega)
            (by unfold lrA2; omega) _ rfl)
        isplitl [H1]
        · iexact H1
        rw [show lrN2 = cellPtr 2 lrA2 from rfl]
        iapply isList_cons_intro 2 lrA2 nullNode
          (spliceBytes 8 (CerbMem.memValueToBytes []
            (CerbMem.pointerMval nodeTy nullNode)).2
            (spliceBytes 0 (CerbMem.memValueToBytes [] (longMval 2)).2
              lrCell2u.bytes))
          2 [] (by unfold lrA2; omega) (by unfold lrA2; omega) rfl
          (fun lum fpm ad => rfl)
          (nodeNextDec_ptrImg_null _ rfl)
        isplitl [H2]
        · iexact H2
        · exact isList_nil_intro
      · -- the empty frame
        iapply (BigSepM.bigSepM_empty_intro
          (P := (BIBase.emp : IProp SpikeGF))
          (Φ := fun (i : Int) (c : SpikeCell) =>
            cellOwn (hlc := .hasLC) (GF := SpikeGF) i (.own 1) c))
        itrivial
  -- the create prefix, two certified production rounds
  have hs₁ : Step (procCtx mainSym
      (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
      (lrProdProg ra mo sbty pbty cbty bbty nbty ubty,
        [fmapEmpty], prodMem₀)
      (sseqExpr BTy_unit
        (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer lrN1))))))
        (sseqExpr BTy_unit
          (createRedex loc0 empty_annotation (CerbMem.integerIval 8) nodeTy
            (PrefOther "lr-n2"))
          (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty)),
        [fmapEmpty], σLr1) :=
    Step.sseq_ctx rfl (Step.create rfl rfl lr_create1_applies)
  have hs₂ : Step (procCtx mainSym
      (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
      (sseqExpr BTy_unit
        (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer lrN1))))))
        (sseqExpr BTy_unit
          (createRedex loc0 empty_annotation (CerbMem.integerIval 8) nodeTy
            (PrefOther "lr-n2"))
          (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty)),
        [fmapEmpty], σLr1)
      (sseqExpr BTy_unit
        (createRedex loc0 empty_annotation (CerbMem.integerIval 8) nodeTy
          (PrefOther "lr-n2"))
        (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty),
        [fmapEmpty], σLr1) :=
    Step.sseq_pure
  have hs₃ : Step (procCtx mainSym
      (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
      (sseqExpr BTy_unit
        (createRedex loc0 empty_annotation (CerbMem.integerIval 8) nodeTy
          (PrefOther "lr-n2"))
        (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty),
        [fmapEmpty], σLr1)
      (sseqExpr BTy_unit
        (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer lrN2))))))
        (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty),
        [fmapEmpty], σLr2) :=
    Step.sseq_ctx rfl (Step.create rfl rfl lr_create2_applies)
  have hs₄ : Step (procCtx mainSym
      (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
      (sseqExpr BTy_unit
        (Expr [] (Epure (Pexpr [] () (PEval (Vobject (OVpointer lrN2))))))
        (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty),
        [fmapEmpty], σLr2)
      (lrProdSuffix ra mo sbty pbty cbty bbty nbty ubty,
        [fmapEmpty], σLr2) :=
    Step.sseq_pure
  have hdd₄ := driverDone_step
    (M₀ := procCtx mainSym (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
    rfl rfl hlb rfl
    (.sseq (frag_ofVal (.pure (Vobject (OVpointer lrN2))))
      (lrProdSuffix_frag ra mo sbty pbty cbty bbty nbty ubty))
    (Nat.le_trans (Frag.esize_le_pot (.sseq
      (frag_ofVal (.pure (Vobject (OVpointer lrN2))))
      (lrProdSuffix_frag ra mo sbty pbty cbty bbty nbty ubty)))
      (by rw [pot_sseq,
        lrProdSuffix_pot ra mo sbty pbty cbty bbty nbty ubty,
        pot_ofVal_pure,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hs₄ hddSuffix
  have hdd₃ := driverDone_step
    (M₀ := procCtx mainSym (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
    rfl rfl hlb rfl
    (.sseq (.create loc0_lib)
      (lrProdSuffix_frag ra mo sbty pbty cbty bbty nbty ubty))
    (Nat.le_trans (Frag.esize_le_pot (.sseq (.create loc0_lib)
      (lrProdSuffix_frag ra mo sbty pbty cbty bbty nbty ubty)))
      (by rw [pot_sseq, pot_createRedex,
        lrProdSuffix_pot ra mo sbty pbty cbty bbty nbty ubty,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hs₃ hdd₄
  have hdd₂ := driverDone_step
    (M₀ := procCtx mainSym (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
    rfl rfl hlb rfl
    (.sseq (frag_ofVal (.pure (Vobject (OVpointer lrN1))))
      (.sseq (.create loc0_lib)
        (lrProdSuffix_frag ra mo sbty pbty cbty bbty nbty ubty)))
    (Nat.le_trans (Frag.esize_le_pot (.sseq
      (frag_ofVal (.pure (Vobject (OVpointer lrN1))))
      (.sseq (.create loc0_lib)
        (lrProdSuffix_frag ra mo sbty pbty cbty bbty nbty ubty))))
      (by rw [pot_sseq, pot_sseq, pot_createRedex,
        lrProdSuffix_pot ra mo sbty pbty cbty bbty nbty ubty,
        pot_ofVal_pure,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hs₂ hdd₃
  have hdd₁ := driverDone_step
    (M₀ := procCtx mainSym (lrProdRS ra mo sbty pbty cbty bbty nbty ubty))
    rfl rfl hlb rfl
    (lrProdProg_frag ra mo sbty pbty cbty bbty nbty ubty)
    (Nat.le_trans (Frag.esize_le_pot
      (lrProdProg_frag ra mo sbty pbty cbty bbty nbty ubty))
      (by rw [lrProdProg_pot ra mo sbty pbty cbty bbty nbty ubty,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hs₁ hdd₂
  -- the pipeline equation
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ (lrProdProg ra mo sbty pbty cbty bbty nbty ubty) hQprod
      _ ((3 + (3 + (3 + (3 + (lrCost lrProdNs.length + 1))))) + 1 + 1 + 1 + 1)
      hdd₁
      (by rw [show lrCost lrProdNs.length = 32 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      fs args
  obtain ⟨Q, ⟨p', hval, hseed⟩, -, hcoh⟩ := hψ
  exact ⟨dres, dst', heq,
    ⟨Q, p', hval, hseed, Sat.union_left hcoh⟩, hbl, hout, herr⟩

end CerberusHeapLang
