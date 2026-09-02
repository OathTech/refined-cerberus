/-
CerberusHeapLang.Rules — the base stratum: the store/load small
axioms at iris-lean's raw WP, and the readout combinator.

The contents:
- SMALL AXIOMS `wp_store` / `wp_load` — UB-EXCLUDING: the
  preconditions rule out every NDkilled (undefined-behavior/error)
  arm of the engine's storeM/loadM: the points-to supplies
  pointer-shape, liveness, bounds, writability, non-atomicity;
  `StorableAt` supplies the type-compat fact (the non-UB `Other`
  arm!); `cellLoadTrap = false` excludes the _Bool
  trap-representation arm. Both are generic in the machine context
  `M` and the environment stack `ρ`: a local action step never
  consults the label context (the jump disjuncts of the inversions
  are refuted by node shape) and returns the env VERBATIM.
- THE READOUT COMBINATOR `stateInterp_readout` — the ONE open/close
  of the state interpretation the projection (Adequacy.lean) uses to
  turn an Iris postcondition into a pure fact about the final memory.
- `spike_wp_wand`: iris-lean's `wp_wand` at this language.
- The value dichotomy of an annot-wrapped term (`toVal_annot_cases`,
  `toVal_annot_none`), consumed by the statement strata's annotation
  rules (Wps.lean, Wpt.lean).

WHAT IS DELIBERATELY NOT HERE. Frame and consequence at the raw WP
are iris-lean's own `wp_frame_r` / `wp_mono`. There is NO raw-WP
sequencing rule and NO raw-WP annotation-commuting rule: at a
populated label map both are FALSE for the base WP — a jump discards
the `Esseq`/`Eannot` context, so the premise's continuation and the
conclusion's land on the same registered body owing DIFFERENT
postconditions. Sequencing, annotation commutation, frame across
back edges and consequence are therefore stated at the label-context
judgments `wps` (Wps.lean) and `wpt` (Wpt.lean), whose jump clause is
post-independent; that is why those judgments exist. The spike-era
raw-WP lane pinned to the empty label map (`triple`, `triple_seq`
with its `EnvStable` side condition, `wp_sseq`, `wp_annot`) was
retired at QA-2 (docs/2026-09-02_qa2-notes.md); its exhibits live at
the statement stratum (Examples/Layout.lean).

SOUNDNESS STATUS: every theorem here is proved against `Step`
(Step.lean), the hand-written mirror; Step is certified against the
engine's step_ctx/driver composite (Soundness.lean), and the
bundled `SpikeGS` ghost state is constructed inside the adequacy
proof (Adequacy.lean), so what is proved here acquires engine-level
meaning through the projection / semantic triples.

Design records: docs/2026-08-30_spike-minilog-plan.md and the dated
slice notes in docs/.
-/
import CerberusHeapLang.Lang

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

/-! ## The fragment's action expressions (canonical shapes, recon §1.3) -/

/-- `store(ty, pv, cv)` — positive, strong, non-locking store. -/
def storeExpr (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Store0 false (Pexpr [] () (PEval (Vctype ty)))
      (Pexpr [] () (PEval (Vobject (OVpointer pv))))
      (Pexpr [] () (PEval cv)) mo))))

/-- `load(ty, pv)` — positive strong load. -/
def loadExpr (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Load0 (Pexpr [] () (PEval (Vctype ty)))
      (Pexpr [] () (PEval (Vobject (OVpointer pv)))) mo))))

/-- `lets _ = e1 in e2` — wildcard strong sequencing. -/
def sseqExpr (bty : core_base_type) (e1 e2 : CoreExpr) : CoreExpr :=
  Expr [] (Esseq (Pattern [] (CaseBase (none, bty))) e1 e2)

/-- The address of a fragment pointer (loadM/storeM dispatch on it). -/
def addrOf : CerbMem.PointerValue → Int
  | .PV _ (.PVconcrete _ a) => a
  | _ => 0

@[simp] theorem addrOf_cellPtr (i a : Int) : addrOf (cellPtr i a) = a := rfl

/-- The value a load of cell contents `(ty, bs)` through pointer `pv`
    returns: the engine's own decode (Heap.decodeCell) at the
    pointer's address. -/
def loadedVal (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue) (ty : ctype)
    (bs : List CerbMem.AbsByte) : value :=
  (valueFromMemValue (decodeCell tds ⟨addrOf pv, ty, bs⟩)).2

variable {hlc : HasLC} {GF : BundledGFunctors}

theorem stateInterp_iff [SpikeGS hlc GF] (σ : Mem) (ns : Nat) (κs : List Empty)
    (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt ⊣⊢
      iprop(∃ mm mb mk, ⌜CohG σ mm mb mk⌝ ∗
        metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk) := .rfl

/-- THE READOUT COMBINATOR (foundations Phase 4 — the phase-2
    residual's registered tidy): the ONE open/close of the state
    interpretation the exhibit readout lemmas consume. An exhibit
    supplies its footprint assertion `Φ` and a coupling-conditional
    extraction (typically one or more `cellOwn_cellCoh` /
    `cellsOwn_extract` applications — READ-ONLY: the interp
    components are consumed into a pure fact, never updated); the
    combinator packages the `stateInterp_iff` destructuring and the
    final mask discard once, here. Exhibit modules no longer touch
    `stateInterp_iff` or the fupd plumbing directly. -/
theorem stateInterp_readout [SpikeGS hlc GF] {Φ : IProp GF} {ψ : Mem → Prop}
    (h : ∀ (σ : Mem) (mm : SpikeHeapF MetaCell)
        (mb : SpikeHeapF CerbMem.AbsByte) (mk : SpikeHeapF AllocCursor),
        CohG σ mm mb mk →
        iprop(Φ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ σ⌝ : IProp GF)) :
    Φ ⊢ iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
      stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ σ'⌝) := by
  iintro HΦ %σ' %ns %κs %nt Hσ
  icases (stateInterp_iff σ' ns κs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  ihave %hψ : ⌜ψ σ'⌝ $$ [HΦ Hmi Hbi]
  · iapply h σ' mm mb mk HG
    isplitl [HΦ]
    · iexact HΦ
    isplitl [Hmi]
    · iexact Hmi
    · iexact Hbi
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact hψ

theorem pointsToCell_iff [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap)
    (pv : CerbMem.PointerValue) (dq : DFrac) (ty : ctype) (bs : List CerbMem.AbsByte) :
    pointsToCell (GF := GF) tds pv dq ty bs ⊣⊢
      iprop(∃ (i : Int) (a : Int),
        ⌜pv = cellPtr i a⌝ ∗ metaOwn i dq ⟨a, ty, CerbMem.sizeofCtype tds ty⟩ ∗
        bytesOwn a dq bs ∗
        ⌜bs.length = CerbMem.sizeofCtype tds ty ∧ decIndep tds a ty bs⌝) := .rfl

/-! ## The small axioms -/

/-- wp_store (small axiom, UB-excluding).

    {x ↦ (ty, bs)} store(ty, x, cv) {w. ∃ fp, ⌜w = ({DA_pos [] fp}unit, ρ)⌝ ∗
                                          x ↦ (ty, bytes-of cv)}

    Engine path (recon §5.4 seam (a)): the WP obligation discharges
    into ONE application of the real `CerbMem.storeM`
    (storeM_success, Heap.lean). Preconditions vs the NDkilled arms
    (CerbMem.lean:1662-1696): `hst.compat` kills the ill-typed-store
    `Other` arm; the ↦'s `cellPtr` shape kills
    null/function/no-prov/device; Coh's liveness+bounds+writability+
    non-atomicity (carried by stateInterp) kill the rest. The
    footprint annotation is existentially hidden (R-i); no aid enters
    the terms at all (DA_pos carries only the exclusion list and the
    footprint). Env: arbitrary and returned VERBATIM (the request
    path never reads it). -/
theorem wp_store [SpikeGS hlc GF] {s : Stuckness} {E : CoPset} {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ⊢
      WP (⟨storeExpr loc ann ty pv cv mo, ρ, M⟩ : CoreRt) @ s; E
        {{ w, ∃ fp, ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, ρ, M⟩ : CoreRVal)⌝ ∗
            pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 }} := by
  iintro Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_iff σ₁ ns (obs ++ obs') nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  icases (pointsToCell_iff M.tagDefs pv (.own 1) ty bs).mp $$ Hpt
    with ⟨%i, %addr, %Hpv, Hm, Hb, %Hpure⟩
  subst Hpv
  obtain ⟨hlen, hdec⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm i = some (⟨addr, ty, CerbMem.sizeofCtype M.tagDefs ty⟩ : MetaCell)⌝
      $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  ihave %Hcover : ⌜∀ (j : Nat), j < bs.length →
      Iris.Std.PartialMap.get? mb (addr + (j : Int)) = bs[j]?⌝ $$ [Hbi Hb]
  · iapply bytesOwn_get mb addr (.own 1) bs $$ [$Hbi $Hb]
  ihave %Hread : ⌜CerbMem.readBytesFrom σ₁ addr bs.length = bs⌝ $$ [Hbi Hb]
  · iapply bytesOwn_read HG addr (.own 1) bs $$ [$Hbi $Hb]
  have hcell : CellCoh M.tagDefs σ₁ i ⟨addr, ty, bs⟩ :=
    CellCoh.ofParts M.tagDefs (HG.metas i _ Hgetm) hlen (hlen ▸ Hread) hdec
  have hrun := storeM_success M.tagDefs σ₁ i ⟨addr, ty, bs⟩ mv loc hcell hst
  have hlen' : (CerbMem.memValueToBytes M.tagDefs [] mv).2.length = bs.length := by
    rw [hst.len [], hlen]
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.store_canonical hmv hrun, rfl, rfl⟩⟩
    · trivial
  iintro !> %e₂ %σ₂ %eₜ %Hstep -
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨mv', fp', σ'', hmv', hmem', hout⟩ := hstep.store_inv
  obtain rfl : mv = mv' := Option.some.inj (hmv.symm.trans hmv')
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : fp' = CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype M.tagDefs ty) ∧
      σ'' = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes M.tagDefs [] mv).2 := by
    have h := Option.some.inj hmem'.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
  simp only at hlbl
  obtain rfl : M = e₂M := hlbl.symm
  obtain ⟨he, hρ, hσ⟩ : e₂e = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype M.tagDefs ty))]
        (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧ e₂ρ = ρ ∧
      σ₂ = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes M.tagDefs [] mv).2 := by
    simpa [Prod.mk.injEq] using hout
  subst he hσ
  obtain rfl : ρ = e₂ρ := hρ.symm
  imod (bytesOwn_update mb addr bs (CerbMem.memValueToBytes M.tagDefs [] mv).2 hlen')
    $$ [$Hbi $Hb] with ⟨Hbi, Hb⟩
  imodintro
  isplitl [Hmi Hbi Hki]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists mm, (insertRange mb addr (CerbMem.memValueToBytes M.tagDefs [] mv).2), mk
    isplitr [Hmi Hbi Hki]
    · ipureintro
      exact HG.storeRange addr (CerbMem.memValueToBytes M.tagDefs [] mv).2
        (fun j hj => ⟨bs[j]'(by omega), by
          rw [Hcover j (by omega)]
          exact List.getElem?_eq_getElem _⟩)
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  isplitl [Hm Hb]
  · iexists (⟨SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype M.tagDefs ty))] Vunit,
      ρ, M⟩ : CoreRVal)
    isplit
    · ipureintro; rfl
    iexists (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype M.tagDefs ty))
    isplit
    · ipureintro; rfl
    iapply (pointsToCell_iff M.tagDefs _ _ _ _).mpr
    iexists i, addr
    isplit
    · ipureintro; rfl
    isplitl [Hm]
    · iexact Hm
    isplitl [Hb]
    · iexact Hb
    · ipureintro
      refine ⟨hst.len [], ?_⟩
      intro lum fpm
      exact hst.stored_dec lum fpm addr
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

/-- wp_load (small axiom, UB-excluding, any fraction dq).

    {x ↦{q} (ty, bs)} load(ty, x) {w. ∃ fp, ⌜w = ({DA_pos [] fp} v, ρ)⌝ ∗
                                        x ↦{q} (ty, bs)}
    where v = the engine's own decode of the cell
    (`loadedVal` = valueFromMemValue ∘ reconstructValue at the
    Coh-pinned side tables). The `htrap` premise excludes the _Bool
    trap-representation kill arm (CerbMem.lean:1598-1604) — the one
    loadM failure the points-to alone cannot rule out (R4). -/
theorem wp_load [SpikeGS hlc GF] {s : Stuckness} {E : CoPset} {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    pointsToCell M.tagDefs (GF := GF) pv dq ty bs ⊢
      WP (⟨loadExpr loc ann ty pv mo, ρ, M⟩ : CoreRt) @ s; E
        {{ w, ∃ fp, ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] (loadedVal M.tagDefs pv ty bs),
            ρ, M⟩ : CoreRVal)⌝ ∗
            pointsToCell M.tagDefs pv dq ty bs }} := by
  iintro Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_iff σ₁ ns (obs ++ obs') nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  icases (pointsToCell_iff M.tagDefs pv dq ty bs).mp $$ Hpt
    with ⟨%i, %addr, %Hpv, Hm, Hb, %Hpure⟩
  subst Hpv
  obtain ⟨hlen, hdec⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm i = some (⟨addr, ty, CerbMem.sizeofCtype M.tagDefs ty⟩ : MetaCell)⌝
      $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  ihave %Hread : ⌜CerbMem.readBytesFrom σ₁ addr bs.length = bs⌝ $$ [Hbi Hb]
  · iapply bytesOwn_read HG addr dq bs $$ [$Hbi $Hb]
  have hcell : CellCoh M.tagDefs σ₁ i ⟨addr, ty, bs⟩ :=
    CellCoh.ofParts M.tagDefs (HG.metas i _ Hgetm) hlen (hlen ▸ Hread) hdec
  have hrun := loadM_success M.tagDefs σ₁ i ⟨addr, ty, bs⟩ loc hcell htrap
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.load_canonical hrun, rfl, rfl⟩⟩
    · trivial
  iintro !> %e₂ %σ₂ %eₜ %Hstep -
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨fp', mval', σ'', hmem', hout⟩ := hstep.load_inv
  rw [hrun] at hmem'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ :
      (fp' = CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty) ∧
        mval' = decodeCell M.tagDefs ⟨addr, ty, bs⟩) ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem'.symm
    exact ⟨⟨congrArg (fun p => p.1.1) h, congrArg (fun p => p.1.2) h⟩,
      (congrArg Prod.snd h).symm⟩
  obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
  simp only at hlbl
  obtain rfl : M = e₂M := hlbl.symm
  obtain ⟨he, hρ, hσ⟩ : e₂e = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty))]
        (Expr [] (Epure (Pexpr [] () (PEval
          (valueFromMemValue (decodeCell M.tagDefs ⟨addr, ty, bs⟩)).2))))) ∧
      e₂ρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst he
  obtain rfl : ρ = e₂ρ := hρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imodintro
  isplitl [Hmi Hbi Hki]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists mm, mb, mk
    isplitr [Hmi Hbi Hki]
    · ipureintro
      exact HG
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  isplitl [Hm Hb]
  · iexists (⟨SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty))]
      (loadedVal M.tagDefs (cellPtr i addr) ty bs), ρ, M⟩ : CoreRVal)
    isplit
    · ipureintro; rfl
    iexists (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty))
    isplit
    · ipureintro; rfl
    iapply (pointsToCell_iff M.tagDefs _ _ _ _).mpr
    iexists i, addr
    isplit
    · ipureintro; rfl
    isplitl [Hm]
    · iexact Hm
    isplitl [Hb]
    · iexact Hb
    · ipureintro
      exact ⟨hlen, hdec⟩
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

/-! ## The value dichotomy of an annot-wrapped term

The run-time `Eannot` wrapper is NOT an iris-lean evaluation context
(`Context.primStep_fill` fails when the wrapped body is annot-rooted:
the engine merges at the root instead of descending, get_ctx's arm
order, Core_reduction.lean:375). The statement strata commute their
judgments with the wrapper (`wps_annot`, `wpt_annot`, and the
reindexing lemmas); the two facts below are the value-side input
those proofs share. -/

/-- Value dichotomy for an annot-wrapped term: it is a value iff the
    node annots are empty and the body is a canonical bare value —
    and then its value is ds-indexed accordingly. -/
theorem toVal_annot_cases (a : List annot) (c : CoreExpr)
    (ds : List dyn_annotation) :
    (a = [] ∧ ∃ v, c = ofVal (.pure v) ∧
      toVal (Expr a (Eannot ds c)) = some (.annot ds v)) ∨
    toVal (Expr a (Eannot ds c)) = none := by
  cases h : toVal (Expr a (Eannot ds c)) with
  | none => exact .inr rfl
  | some w =>
    left
    have he := ofVal_of_toVal h
    cases w with
    | pure v => exact absurd he (by simp [ofVal])
    | annot ds' v =>
      obtain ⟨ha, hds, hc⟩ :
          ([] : List annot) = a ∧ ds' = ds ∧
            Expr ([] : List annot) (Epure (Pexpr [] () (PEval v))) = c := by
        simpa [ofVal] using he
      subst ha hds hc
      exact ⟨rfl, v, rfl, h⟩

theorem toVal_annot_none {a : List annot} {ds : List dyn_annotation}
    {e : CoreExpr} (h : toVal e = none) :
    toVal (Expr a (Eannot ds e)) = none := by
  rcases toVal_annot_cases a e ds with ⟨_, v, rfl, _⟩ | h'
  · rw [toVal_ofVal] at h; cases h
  · exact h'

/-- wp_wand, re-exported at the spike's language (Iris's `wp_wand`). -/
theorem spike_wp_wand [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    {e : CoreRt} {Φ Ψ : CoreRVal → IProp GF} :
    WP e @ s; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }} :=
  wp_wand

end CerberusHeapLang
