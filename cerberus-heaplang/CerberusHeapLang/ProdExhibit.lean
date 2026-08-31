/-
CerberusHeapLang.ProdExhibit — exhibit A re-exported at the
PRODUCTION ENTRY: the unconditional demonstration that the whole
export chain reaches the shipped pipeline.

The program is fully self-contained — it creates its own cell with the
engine's `create`, then runs the exhibit-A body at the pointer the
production allocator deterministically mints:

  main() = lets _ = create(4, int) in
           lets _ = store(x, 7) in load(x)

where x = the second production allocation (id 1 — errno is id 0 —
at 0xFFFFFFFFFFF4, the cursor after errno). THE THEOREM
(`exhibitA_prod`): `runND` of the SHIPPED driver on the synthetic
one-procedure file wrapping this program, from
`initial_driver_state`, is EXACTLY ONE Active execution; its
driver_result value is `Specified(7)` and the final memory holds 7's
byte image at x — via `sem_triple_prod` with the compute part's
semantic triple (the base logic: wp_store/wp_sseq/wp_load through
`semantic_triple_sound`), the create prefix discharged concretely on
the production cold-start memory, and termination by the 6-step
simulation (the exhibit-A pattern at the production cell).
-/
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.Exhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open scoped Iris.Std.PartialMap

/-! ## The production cell: the program's own create, on prodMem₀ -/

/-- x's address: the cursor after the errno allocation
    (0xFFFFFFFFFFF4). -/
def pxAddr : Int := 281474976710644

/-- x's pointer: allocation id 1 (errno is id 0). -/
def pxPtr : CerbMem.PointerValue := cellPtr 1 pxAddr

/-- The engine's own in-program allocation on the cold-start memory. -/
def createSeeded : Option (CerbMem.PointerValue × Mem) :=
  applyMemM (CerbMem.allocateObject 0 (PrefOther "spike-x")
    (CerbMem.integerIval 4) intTy none none) prodMem₀

/-- The state after the program's create. -/
def σcP : Mem := match createSeeded with | some (_, σ) => σ | none => {}

theorem createSeeded_eq : createSeeded = some (pxPtr, σcP) := rfl

theorem create_applies :
    applyMemM (CerbMem.allocateObject 0 (PrefOther "spike-x")
      (CerbMem.integerIval 4) intTy none none) prodMem₀ =
      some (pxPtr, σcP) := createSeeded_eq

/-- create_applies at the payload's requested address (an opaque
    `get_with_address []` — discarded by allocateObject; bridged by
    the symbolic-argument equation, never by concrete evaluation). -/
theorem create_applies_req :
    applyMemM (CerbMem.allocateObject 0 (PrefOther "spike-x")
      (CerbMem.integerIval 4) intTy (get_with_address []) none) prodMem₀ =
      some (pxPtr, σcP) := by
  rw [allocateObject_arg_irrel 0 0 (PrefOther "spike-x")
    (CerbMem.integerIval 4) intTy (get_with_address []) none none]
  exact create_applies

def pxAllocRec : CerbMem.Allocation :=
  { base := pxAddr, size := 4, ty := some intTy,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "spike-x") none,
    prefix_ := PrefOther "spike-x" }

theorem σcP_allocations :
    σcP.allocations =
      ((({} : Mem).allocations.insert 0 errnoAllocRec).insert 1 pxAllocRec) := rfl

theorem px_alloc_get : σcP.allocations.get? 1 = some pxAllocRec := by
  rw [σcP_allocations]
  simp

theorem px_bytes_len (a : Int) :
    (CerbMem.readBytesFrom σcP a 4).length = 4 := by
  unfold CerbMem.readBytesFrom
  simp

/-- x's (uninitialized) cell in the post-create state. -/
abbrev cellXP : SpikeCell := ⟨pxAddr, intTy, CerbMem.readBytesFrom σcP pxAddr 4⟩

theorem cellCohXP : CellCoh σcP 1 cellXP :=
  ⟨rfl, ⟨pxAllocRec, px_alloc_get, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype cellXP.ty = 4 from rfl]; exact px_bytes_len pxAddr,
   by rw [show CerbMem.sizeofCtype cellXP.ty = 4 from rfl],
   fun _ _ => rfl⟩

/-- x's footprint (the compute part's precondition). -/
abbrev mAP : CellMap := Iris.Std.PartialMap.insert ∅ 1 cellXP

/-- x's cell after the store of 7. -/
abbrev cellXP7 : SpikeCell :=
  ⟨pxAddr, intTy, (CerbMem.memValueToBytes [] sevenMval).2⟩

/-- The postcondition footprint. -/
abbrev mAP7 : CellMap := Iris.Std.PartialMap.insert ∅ 1 cellXP7

theorem coh_mAP : Coh σcP mAP := by
  refine ⟨?_, ?_⟩
  · intro id c h
    by_cases h1 : id = 1
    · subst h1
      rw [mAP, Iris.Std.get?_insert_eq rfl] at h
      cases h
      exact cellCohXP
    · rw [mAP, Iris.Std.get?_insert_ne (fun h' => h1 h'.symm),
        Iris.Std.LawfulPartialMap.get?_empty] at h
      cases h
  · intro id1 id2 c1 c2 hne h1 h2
    by_cases ha : id1 = 1
    · subst ha
      by_cases hb : id2 = 1
      · exact absurd hb.symm hne
      · rw [mAP, Iris.Std.get?_insert_ne (fun h' => hb h'.symm),
          Iris.Std.LawfulPartialMap.get?_empty] at h2
        cases h2
    · rw [mAP, Iris.Std.get?_insert_ne (fun h' => ha h'.symm),
        Iris.Std.LawfulPartialMap.get?_empty] at h1
      cases h1

/-! ## The program -/

/-- The compute part: exhibit A's body at the production cell. -/
abbrev progAProdC : CoreExpr :=
  sseqExpr BTy_unit (storeExpr loc0 empty_annotation intTy pxPtr sevenVal NA)
    (loadExpr loc0 empty_annotation intTy pxPtr NA)

/-- The full self-contained program: create the cell, then compute. -/
abbrev progAProd : CoreExpr :=
  sseqExpr BTy_unit (createRedex loc0 empty_annotation
    (CerbMem.integerIval 4) intTy (PrefOther "spike-x")) progAProdC

theorem fragAProdC : FragP progAProdC :=
  FragP.sseq (.store loc0_lib) (.load loc0_lib)

theorem fragAProd : FragP progAProd :=
  FragP.sseq (.create loc0_lib) fragAProdC

/-! ## The compute part's ProvenTriple (the slice-B derivation,
parametric in the cell — the provenA pattern at (id 1, pxAddr)) -/

theorem loaded_seven_at (i a : Int) :
    loadedVal (cellPtr i a) intTy (CerbMem.memValueToBytes [] sevenMval).2 =
      sevenVal := rfl

theorem htrap_seven_at (a : Int) :
    cellLoadTrap ⟨a, intTy, (CerbMem.memValueToBytes [] sevenMval).2⟩ =
      false := rfl

variable {GF : BundledGFunctors}

theorem bigSep_ptx_P [SpikeGS .hasLC GF] :
    iprop(([∗map] i ↦ c ∈ mAP, pointsTo i (.own 1) c)) ⊢
      pointsToCell (GF := GF) pxPtr (.own 1) intTy cellXP.bytes := by
  refine .trans (BigSepM.bigSepM_insert (i := 1) (x := cellXP)
    (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 1)).1 ?_
  iintro ⟨Hx, -⟩
  iapply (pointsToCell_iff _ _ _ _).mpr
  iexists 1, pxAddr
  isplit
  · ipureintro
    rfl
  · iexact Hx

theorem ptx_to_cells_P [SpikeGS .hasLC GF] :
    iprop(pointsToCell (GF := GF) pxPtr (.own 1) intTy
      (CerbMem.memValueToBytes [] sevenMval).2) ⊢
      iprop([∗map] i ↦ c ∈ mAP7, pointsTo i (.own 1) c) := by
  iintro Hx
  icases (pointsToCell_iff _ _ _ _).mp $$ Hx with ⟨%ix, %ax, %Hpx, Hx⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj Hpx.symm
  iapply (BigSepM.bigSepM_insert
    (Φ := fun (i : Int) (c : SpikeCell) => pointsTo i (.own 1) c)
    (i := 1) (x := cellXP7)
    (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 1)).2
  isplitl [Hx]
  · iexact Hx
  · iapply (BigSepM.bigSepM_empty_intro
      (P := (BIBase.emp : IProp GF))
      (Φ := fun (i : Int) (c : SpikeCell) => pointsTo i (.own 1) c))
    itrivial

/-- The compute part's footprint triple, proved in the derived logic
    (the provenA derivation at the production cell). -/
theorem provenAProd {GF : BundledGFunctors} [SpikeGpreS GF] :
    ProvenTriple GF progAProdC mAP (fun v Q => v = sevenVal ∧ Q = mAP7) := by
  intro instGS
  refine bigSep_ptx_P.trans (.trans ?_ (wp_sseq [] [] BTy_unit _ _ fmapEmpty []))
  iintro Hx
  ihave HW := wp_store (s := Stuckness.NotStuck) (E := ⊤) loc0 empty_annotation
    intTy pxPtr sevenVal NA sevenMval cellXP.bytes spikeEnv seven_encodes
    seven_storable $$ Hx
  iapply spike_wp_wand $$ HW
  iintro %v ⟨%fp, %hv, Hx⟩
  subst hv
  iapply BI.later_intro
  ihave HW2 := wp_load (s := Stuckness.NotStuck) (E := ⊤) loc0 empty_annotation
    intTy pxPtr NA (.own 1) (CerbMem.memValueToBytes [] sevenMval).2 spikeEnv
    (htrap_seven_at (addrOf pxPtr)) $$ Hx
  iapply spike_wp_wand $$ HW2
  iintro %w ⟨%fp2, %hw, Hx⟩
  iexists mAP7
  isplit
  · ipureintro
    subst hw
    refine ⟨?_, rfl⟩
    simp only [mergeInto, CoreRVal.val, CoreRVal.merge_mk, SpikeVal.val_merge]
    exact loaded_seven_at 1 pxAddr
  · ihave HC := ptx_to_cells_P $$ Hx
    iexact HC

/-- The compute part's SEMANTIC triple (the exported face). -/
theorem semAProd {GF : BundledGFunctors} [SpikeGpreS GF] :
    SemTriple progAProdC mAP (fun v Q => v = sevenVal ∧ Q = mAP7) :=
  semantic_triple_sound (GF := GF) fragAProdC provenAProd

/-! ## The create prefix (2 drive steps, concrete) -/

theorem prodA_pre (aids : Nat → Nat) (n : Nat) :
    drive aids (2 + n) (spikeThread progAProd) prodMem₀ =
      drive (fun i => aids (i + 2)) n (spikeThread progAProdC) σcP := by
  rw [show 2 + n = (n + 1) + 1 from by omega]
  rw [drive_step_next (th' := spikeThread (Expr [] (Esseq
      (Pattern [] (CaseBase (none, BTy_unit)))
      (ofVal (.pure (Vobject (OVpointer pxPtr)))) progAProdC))) (σ' := σcP) (by
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_create
      (Decomp.toJ (Decomp.sseq (pa := []) (bty := BTy_unit) (e2 := progAProdC)
        (Decomp.root (Redex.create (ann := empty_annotation)
          (align := CerbMem.integerIval 4) (ty := intTy)
          (pref := PrefOther "spike-x") loc0_lib))))
      (by decide) loc0_lib spikeEnv prodMem₀
    rw [show engineSteps progAProd spikeEnv prodMem₀ = _ from hE]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_create_active create_applies_req]
    rfl)]
  rw [drive_step_next (th' := spikeThread progAProdC) (σ' := σcP) (by
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_beta_pure (pa := []) (bty := BTy_unit)
      (v := Vobject (OVpointer pxPtr)) (e2 := progAProdC)
      (Decomp.toJ (Decomp.root Redex.beta_pure)) (by decide) fmapEmpty [] σcP
    rw [show engineSteps (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
      (ofVal (.pure (Vobject (OVpointer pxPtr)))) progAProdC)) spikeEnv σcP =
        _ from hE]
    rfl)]

/-! ## Termination of the compute part (the exhibit-A 6-step
simulation at the production cell) -/

def σ1P : Mem :=
  CerbMem.writeBytesTo σcP pxAddr (CerbMem.memValueToBytes [] sevenMval).2

def fpSP : CerbMem.Footprint := .FP .W pxAddr 4
def fpLP : CerbMem.Footprint := .FP .R pxAddr 4

theorem store_applies_P :
    applyMemM (CerbMem.storeM loc0 intTy false pxPtr sevenMval) σcP =
      some (fpSP, σ1P) :=
  storeM_success σcP 1 cellXP sevenMval loc0 cellCohXP seven_storable

theorem coh_after_store_P :
    Coh σ1P (Iris.Std.PartialMap.insert mAP 1 cellXP7) :=
  Coh.store σcP mAP 1 cellXP sevenMval coh_mAP (Iris.Std.get?_insert_eq rfl)
    seven_storable

theorem load_applies_P :
    applyMemM (CerbMem.loadM loc0 intTy pxPtr) σ1P =
      some ((fpLP, decodeCell cellXP7), σ1P) :=
  loadM_success σ1P 1 cellXP7 loc0
    (coh_after_store_P.cells 1 _ (Iris.Std.get?_insert_eq rfl))
    (htrap_seven_at pxAddr)

/-- The intermediate arenas of the compute drive. -/
def eP1 : CoreExpr :=
  Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [] (Eannot [DA_pos [] fpSP]
      (Expr [] (Epure (Pexpr [] () (PEval Vunit))))))
    (loadExpr loc0 empty_annotation intTy pxPtr NA))

def eP2 : CoreExpr :=
  Expr [] (Eannot [DA_pos [] fpSP] (loadExpr loc0 empty_annotation intTy pxPtr NA))

def eP3 : CoreExpr :=
  Expr [] (Eannot [DA_pos [] fpSP] (Expr [] (Eannot [DA_pos [] fpLP]
    (Expr [] (Epure (Pexpr [] () (PEval sevenVal)))))))

theorem prodA_terminates (aids : Nat → Nat) :
    drive aids 6 (spikeThread progAProdC) σcP = .done sevenVal σ1P := by
  rw [drive_next (th' := spikeThread eP1) (σ' := σ1P) ?s1]
  case s1 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_store
      (Decomp.toJ (Decomp.sseq (pa := []) (bty := BTy_unit)
        (e2 := loadExpr loc0 empty_annotation intTy pxPtr NA)
        (Decomp.root (Redex.store (loc := loc0) (ann := empty_annotation)
          (lk := false) (ty := intTy) (pv := pxPtr) (cv := sevenVal)
          (mo := NA) loc0_lib))))
      (by decide) loc0_lib seven_encodes spikeEnv σcP
    rw [show engineSteps progAProdC spikeEnv σcP = _ from hE]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_store_active store_applies_P]
    rfl
  rw [drive_next (th' := spikeThread eP2) (σ' := σ1P) ?s2]
  case s2 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_beta_annot (pa := []) (bty := BTy_unit)
      (ds := [DA_pos [] fpSP]) (v := Vunit)
      (e2 := loadExpr loc0 empty_annotation intTy pxPtr NA)
      (Decomp.toJ (Decomp.root Redex.beta_annot)) (by decide) fmapEmpty [] σ1P
    rw [show engineSteps eP1 spikeEnv σ1P = _ from hE]
    rfl
  rw [drive_next (th' := spikeThread eP3) (σ' := σ1P) ?s3]
  case s3 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_load
      (Decomp.toJ (Decomp.annot (ds := [DA_pos [] fpSP]) rfl rfl (fun n => rfl)
        (Decomp.root (Redex.load (loc := loc0) (ann := empty_annotation)
          (ty := intTy) (pv := pxPtr) (mo := NA) loc0_lib))))
      (by decide) loc0_lib spikeEnv σ1P
    rw [show engineSteps eP2 spikeEnv σ1P = _ from hE]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_load_active load_applies_P]
    rfl
  rw [drive_next
    (th' := spikeThread (ofVal (.annot [DA_pos [] fpSP, DA_pos [] fpLP] sevenVal)))
    (σ' := σ1P) ?s4]
  case s4 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_merge (ds1 := [DA_pos [] fpSP])
      (ds2 := [DA_pos [] fpLP])
      (Decomp.toJ (Decomp.root (Redex.merge
        (b := Expr [] (Epure (Pexpr [] () (PEval sevenVal)))) rfl)))
      rfl (by decide) spikeEnv σ1P
    rw [show engineSteps eP3 spikeEnv σ1P = _ from hE]
    rfl
  rw [drive_next (th' := spikeThread (ofVal (.pure sevenVal))) (σ' := σ1P) ?s5]
  case s5 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    rw [engineSteps_remove_annot]
    rfl
  rw [drive_done ?s6]
  case s6 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    rw [engineSteps_done]
    rfl

/-! ## THE EXHIBIT AT THE PRODUCTION ENTRY -/

/-- EXHIBIT A, PRODUCTION-ENTRY FORM: the shipped pipeline on the
    synthetic one-procedure file wrapping the self-contained program
    is EXACTLY ONE Active execution; its result value is
    `Specified(7)` and the final memory holds 7's byte image at the
    program's own cell. -/
theorem exhibitA_prod (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile progAProd) args)
          (initial_driver_state (prodFile progAProd) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = sevenVal ∧
      CerbMem.readBytesFrom dst'.layout_state pxAddr 4 =
        (CerbMem.memValueToBytes [] sevenMval).2 := by
  obtain ⟨dres, dst', heq, hval, hlay, Q, hpost, _, hsat⟩ :=
    sem_triple_prod progAProd fragAProd progAProdC mAP
      (fun v Q => v = sevenVal ∧ Q = mAP7) (semAProd (GF := SpikeGF)) ∅
      (Iris.Std.LawfulPartialMap.disjoint_empty_right mAP) σcP 2 prodA_pre
      (by rw [show Iris.Std.PartialMap.union mAP ∅ = mAP from
            Iris.Std.LawfulPartialMap.union_empty_right]
          exact coh_mAP)
      sevenVal σ1P 6 prodA_terminates
      (by rw [show esize progAProd = 3 from rfl]; unfold lemDefaultFuel; omega)
      (by rw [show esize progAProdC = 2 from rfl]; unfold lemDefaultFuel; omega)
      fs args
  obtain ⟨-, rfl⟩ := hpost
  refine ⟨dres, dst', heq, hval, ?_⟩
  have hsat' : Sat σ1P mAP7 :=
    Sat.mono hsat (by
      rw [show Iris.Std.PartialMap.union mAP7 ∅ = mAP7 from
        Iris.Std.LawfulPartialMap.union_empty_right])
  have hcx := (hsat'.cells 1 _ (Iris.Std.get?_insert_eq rfl)).bytes
  rw [show CerbMem.sizeofCtype intTy = 4 from rfl] at hcx
  rw [hlay]
  exact hcx

end CerberusHeapLang
