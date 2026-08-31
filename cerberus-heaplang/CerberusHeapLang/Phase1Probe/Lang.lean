/-
CerberusHeapLang.Phase1Probe.Lang — PHASE-1 PROBE MODULE (S1a):
the iris-lean `Language` instance over the UNIFIED relation, and
the store small axiom re-proved against it.

`primStep` IS the authoritative relation (arc plan Phase 1 item 4):
the language expression is the runtime tuple (Core expression ×
live env stack × MACHINE CONTEXT) — the old tuple's label-map slot
generalized to the full context; `primStep` runs `StepU` at the
tuple's own context and pins the successor's context to it (the
engine never writes any context component on the sequential path —
the per-rule step_ctx lemmas return `{th with arena, env}` record
updates and the run state verbatim).

`wp_storeU` is the store small axiom over this language: the SAME
statement shape as `wp_store` (Rules.lean) with the tuple's label
map generalized to the context and the operand-encoding premise
stated at `M.tagDefs` — the one place the old rule hard-coded a
frozen constant inside a LOGIC RULE's statement. The proof is the
old proof with the unified inversions substituted — evidence for
the S1b migration's per-rule cost estimate.
-/
import CerberusHeapLang.Phase1Probe.Match
import CerberusHeapLang.Rules

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

/-! ## The runtime tuple over the machine context -/

/-- The unified runtime expression tuple: Core expression + live
    environment stack + the machine context (every immutable the
    fragment reads — Phase1Probe/Machine.lean; the old `CoreRt`
    carried only the label-map projection of it). -/
structure CoreRtU where
  e : CoreExpr
  ρ : EnvStack
  M : MachineCtx

/-- Values carry the final env and the (unchanged) context. -/
structure CoreRValU where
  w : SpikeVal
  ρ : EnvStack
  M : MachineCtx

/-- The delivered engine value (annotations and env erased). -/
def CoreRValU.val (v : CoreRValU) : value := v.w.val

def toValRtU (r : CoreRtU) : Option CoreRValU :=
  (toVal r.e).map fun w => ⟨w, r.ρ, r.M⟩

def ofValRtU (v : CoreRValU) : CoreRtU := ⟨ofVal v.w, v.ρ, v.M⟩

@[simp] theorem toValRtU_mk (e : CoreExpr) (ρ : EnvStack) (M : MachineCtx) :
    toValRtU ⟨e, ρ, M⟩ = (toVal e).map fun w => ⟨w, ρ, M⟩ := rfl

@[simp] theorem ofValRtU_mk (w : SpikeVal) (ρ : EnvStack) (M : MachineCtx) :
    ofValRtU ⟨w, ρ, M⟩ = ⟨ofVal w, ρ, M⟩ := rfl

@[simp] theorem toValRtU_ofValRtU (v : CoreRValU) :
    toValRtU (ofValRtU v) = some v := by
  obtain ⟨w, ρ, M⟩ := v
  rw [ofValRtU_mk, toValRtU_mk, toVal_ofVal]
  rfl

/-! ## The Language instance -/

instance : Language CoreRtU Mem Empty CoreRValU where
  primStep := fun p _obs q =>
    StepU p.1.M (p.1.e, p.1.ρ, p.2) (q.1.e, q.1.ρ, q.2.1) ∧
      q.1.M = p.1.M ∧ q.2.2 = []
  toVal := toValRtU
  ofVal := ofValRtU
  coe_of_toVal_eq_some {r v} h := by
    obtain ⟨e, ρ, M⟩ := r
    rw [toValRtU_mk] at h
    cases he : toVal e with
    | none => rw [he] at h; cases h
    | some w =>
      rw [he] at h
      cases h
      show ofValRtU ⟨w, ρ, M⟩ = ⟨e, ρ, M⟩
      rw [ofValRtU_mk, ofVal_of_toVal he]
  toVal_coe v := by
    obtain ⟨w, ρ, M⟩ := v
    rw [ofValRtU_mk, toValRtU_mk, toVal_ofVal]
    rfl
  val_stuck {r σ obs r' σ' eₜ} h := by
    obtain ⟨e, ρ, M⟩ := r
    show toValRtU ⟨e, ρ, M⟩ = none
    rw [toValRtU_mk, StepU.toVal_none h.1]
    rfl

@[simp] theorem primStepU_eq (r : CoreRtU) (σ : Mem) (obs : List Empty)
    (r' : CoreRtU) (σ' : Mem) (efs : List CoreRtU) :
    (PrimStep.primStep (r, σ) obs (r', σ', efs) : Prop) ↔
      (StepU r.M (r.e, r.ρ, σ) (r'.e, r'.ρ, σ') ∧ r'.M = r.M ∧ efs = []) :=
  Iff.rfl

theorem language_toVal_eqU (r : CoreRtU) :
    ToVal.toVal (Val := CoreRValU) r = toValRtU r := rfl

/-! ## The Iris ghost-state instance over the unified language
(the state interpretation and ghost state are SHARED with the old
language — `StateInterp Mem Empty GF` and `SpikeGS` never mention
the expression type; only the IrisGS bundle is per-language). -/

instance instIrisGSU {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF] :
    IrisGS_gen hlc CoreRtU GF where
  invGS := SpikeGS.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    letI := @SpikeGS.invGS hlc GF _
    iintro $

/-- wp_wand at the unified language. -/
theorem wp_wandU {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    {s : Stuckness} {E : CoPset}
    {e : CoreRtU} {Φ Ψ : CoreRValU → IProp GF} :
    WP e @ s; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }} :=
  wp_wand

/-! ## The store small axiom over the unified relation -/

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- wp_store over the unified language (statement = `wp_store` with
    the label-map slot generalized to the machine context and the
    encoding premise at `M.tagDefs`; proof = the old proof with
    `StepU.store_canonical`/`StepU.store_inv` substituted). -/
theorem wp_storeU [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt ty mv) :
    pointsToCell (GF := GF) pv (.own 1) ty bs ⊢
      WP (⟨storeExpr loc ann ty pv cv mo, ρ, M⟩ : CoreRtU) @ s; E
        {{ w, ∃ fp, ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, ρ, M⟩ : CoreRValU)⌝ ∗
            pointsToCell pv (.own 1) ty (CerbMem.memValueToBytes [] mv).2 }} := by
  iintro Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_iff σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨%m, %Hcoh, Hh⟩
  icases (pointsToCell_iff pv (.own 1) ty bs).mp $$ Hpt with ⟨%i, %addr, %Hpv, Hpt⟩
  subst Hpv
  ihave %Hget : ⌜Iris.Std.PartialMap.get? m i = some (SpikeCell.mk addr ty bs)⌝
      $$ [Hh Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hh $Hpt]
    itrivial
  have hcell : CellCoh σ₁ i ⟨addr, ty, bs⟩ := Hcoh.cells i _ Hget
  have hrun := storeM_success σ₁ i ⟨addr, ty, bs⟩ mv loc hcell hst
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨StepU.store_canonical hmv hrun, rfl, rfl⟩⟩
    · trivial
  iintro !> %e₂ %σ₂ %eₜ %Hstep -
  obtain ⟨hstep, hM, rfl⟩ := Hstep
  obtain ⟨mv', fp', σ'', hmv', hmem', hout⟩ := hstep.store_inv
  obtain rfl : mv = mv' := Option.some.inj (hmv.symm.trans hmv')
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : fp' = CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty) ∧
      σ'' = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes [] mv).2 := by
    have h := Option.some.inj hmem'.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
  simp only at hM
  obtain rfl : M = e₂M := hM.symm
  obtain ⟨he, hρ, hσ⟩ : e₂e = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty))]
        (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧ e₂ρ = ρ ∧
      σ₂ = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes [] mv).2 := by
    simpa [Prod.mk.injEq] using hout
  subst he hσ
  obtain rfl : ρ = e₂ρ := hρ.symm
  imod (genHeap_update
      (v₂ := SpikeCell.mk addr ty (CerbMem.memValueToBytes [] mv).2))
    $$ [$Hh $Hpt] with ⟨Hh, Hpt⟩
  imodintro
  isplitl [Hh]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists (Iris.Std.PartialMap.insert m i
      (SpikeCell.mk addr ty (CerbMem.memValueToBytes [] mv).2))
    isplitr [Hh]
    · ipureintro
      exact Coh.store σ₁ m i ⟨addr, ty, bs⟩ mv Hcoh Hget hst
    · iexact Hh
  isplitl [Hpt]
  · iexists (⟨SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty))] Vunit,
      ρ, M⟩ : CoreRValU)
    isplit
    · ipureintro; rfl
    iexists (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty))
    isplit
    · ipureintro; rfl
    iapply (pointsToCell_iff _ _ _ _).mpr
    iexists i, addr
    isplit
    · ipureintro; rfl
    · iexact Hpt
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

end CerberusHeapLang
