/-
RefinedCerberus.Spike.Rules — spike artifact 3: the logic.

The acceptance package (docs/2026-08-30_spike-minilog-plan.md):
- SMALL AXIOMS `wp_store` / `wp_load` — UB-EXCLUDING (R4): the
  preconditions rule out every NDkilled arm of storeM/loadM (recon
  §2.6): the points-to supplies pointer-shape, liveness, bounds,
  writability, non-atomicity; `StorableAt` supplies the type-compat
  fact (the non-UB `Other` arm!); `cellLoadTrap = false` excludes the
  _Bool trap-representation arm.
- SEQ/BIND: Iris `wp_bind` through the genuine `Language.Context`
  instance for the Esseq frame (Lang.lean), the two beta lifts, and
  the annotation-commuting lemmas `wp_annot_reindex`/`wp_annot`
  (the R-i residue's cost, paid once), assembled into `wp_sseq` and
  the triple-level `triple_seq`.
- FRAME from Iris (`wp_frame_l/r`), stated at triple level.
- CONSEQUENCE + `wp_wand` (from Iris, stated at triple level).
- THE EXHIBIT: {x ↦ - ∗ y ↦ a} store(x,7) {x ↦ 7 ∗ y ↦ a}, derived by
  FRAME on the store small axiom.
- The anti-frame sanity check: a comment-fenced negative test at the
  end of this file (a failing example cannot be committed compiling;
  the stuck goal is recorded verbatim there and in the slice notes).

SOUNDNESS STATUS: every theorem here is proved against `Step`
(Step.lean), the hand-written mirror. Slice B closed both slice-A
gaps: Step is certified against the engine's step_ctx/driver
composite (Soundness.lean), and the bundled `SpikeGS` ghost state is
constructed inside the adequacy proof (Adequacy.lean,
spike_step_adequacy), so triples proved here acquire engine-level
meaning through SemTriple / semantic_triple_sound.
-/
import RefinedCerberus.Spike.Lang

set_option autoImplicit false

namespace RefinedCerberus.Spike

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
def loadedVal (pv : CerbMem.PointerValue) (ty : ctype)
    (bs : List CerbMem.AbsByte) : value :=
  (valueFromMemValue (decodeCell ⟨addrOf pv, ty, bs⟩)).2

variable {hlc : HasLC} {GF : BundledGFunctors}

theorem stateInterp_iff [SpikeGS hlc GF] (σ : Mem) (ns : Nat) (κs : List Empty)
    (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt ⊣⊢
      iprop(∃ m, ⌜Coh σ m⌝ ∗ genHeapInterp m) := .rfl

theorem pointsToCell_iff [SpikeGS hlc GF] (pv : CerbMem.PointerValue)
    (dq : DFrac) (ty : ctype) (bs : List CerbMem.AbsByte) :
    pointsToCell (GF := GF) pv dq ty bs ⊣⊢
      iprop(∃ (i : Int) (a : Int),
        ⌜pv = cellPtr i a⌝ ∗ pointsTo i dq (SpikeCell.mk a ty bs)) := .rfl

/-! ## The small axioms -/

/-- wp_store (small axiom, UB-excluding).

    {x ↦ (ty, bs)} store(ty, x, cv) {w. ∃ fp, ⌜w = {DA_pos [] fp}unit⌝ ∗
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
    footprint). -/
theorem wp_store [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte)
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt ty mv) :
    pointsToCell (GF := GF) pv (.own 1) ty bs ⊢
      WP (storeExpr loc ann ty pv cv mo) @ s; E
        {{ w, ∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] Vunit⌝ ∗
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
    · exact ⟨[], _, _, [], ⟨Step.store hmv hrun, rfl⟩⟩
    · trivial
  iintro !> %e₂ %σ₂ %eₜ %Hstep -
  obtain ⟨hstep, rfl⟩ := Hstep
  obtain ⟨mv', fp', σ'', hmv', hmem', hout⟩ := hstep.store_inv
  obtain rfl : mv = mv' := Option.some.inj (hmv.symm.trans hmv')
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : fp' = CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty) ∧
      σ'' = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes [] mv).2 := by
    have h := Option.some.inj hmem'.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  cases hout
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
  · iexists (SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty))] Vunit)
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

/-- wp_load (small axiom, UB-excluding, any fraction dq).

    {x ↦{q} (ty, bs)} load(ty, x) {w. ∃ fp, ⌜w = {DA_pos [] fp} v⌝ ∗
                                        x ↦{q} (ty, bs)}
    where v = the engine's own decode of the cell
    (`loadedVal` = valueFromMemValue ∘ reconstructValue at the
    Coh-pinned side tables). The `htrap` premise excludes the _Bool
    trap-representation kill arm (CerbMem.lean:1598-1604) — the one
    loadM failure the points-to alone cannot rule out (R4). -/
theorem wp_load [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte)
    (htrap : cellLoadTrap ⟨addrOf pv, ty, bs⟩ = false) :
    pointsToCell (GF := GF) pv dq ty bs ⊢
      WP (loadExpr loc ann ty pv mo) @ s; E
        {{ w, ∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] (loadedVal pv ty bs)⌝ ∗
            pointsToCell pv dq ty bs }} := by
  iintro Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_iff σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨%m, %Hcoh, Hh⟩
  icases (pointsToCell_iff pv dq ty bs).mp $$ Hpt with ⟨%i, %addr, %Hpv, Hpt⟩
  subst Hpv
  ihave %Hget : ⌜Iris.Std.PartialMap.get? m i = some (SpikeCell.mk addr ty bs)⌝
      $$ [Hh Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hh $Hpt]
    itrivial
  have hcell : CellCoh σ₁ i ⟨addr, ty, bs⟩ := Hcoh.cells i _ Hget
  have hrun := loadM_success σ₁ i ⟨addr, ty, bs⟩ loc hcell htrap
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [], ⟨Step.load hrun, rfl⟩⟩
    · trivial
  iintro !> %e₂ %σ₂ %eₜ %Hstep -
  obtain ⟨hstep, rfl⟩ := Hstep
  obtain ⟨fp', mval', σ'', hmem', hout⟩ := hstep.load_inv
  rw [hrun] at hmem'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ :
      (fp' = CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype ty) ∧
        mval' = decodeCell ⟨addr, ty, bs⟩) ∧ σ'' = σ₁ := by
    have h := Option.some.inj hmem'.symm
    exact ⟨⟨congrArg (fun p => p.1.1) h, congrArg (fun p => p.1.2) h⟩,
      congrArg Prod.snd h⟩
  cases hout
  imodintro
  isplitl [Hh]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists m
    isplitr [Hh]
    · ipureintro
      exact Hcoh
    · iexact Hh
  isplitl [Hpt]
  · iexists (SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype ty))]
      (loadedVal (cellPtr i addr) ty bs))
    isplit
    · ipureintro; rfl
    iexists (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype ty))
    isplit
    · ipureintro; rfl
    iapply (pointsToCell_iff _ _ _ _).mpr
    iexists i, addr
    isplit
    · ipureintro; rfl
    · iexact Hpt
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

/-! ## The annotation layer (R-i's cost, paid once)

The run-time `Eannot` wrapper is NOT an iris-lean evaluation context:
`Context.primStep_fill` fails when the wrapped body is annot-rooted,
because the engine then merges at the root instead of descending
(get_ctx's arm order, Core_reduction.lean:375). WP commutes with the
wrapper anyway, in two steps:
- `wp_annot_reindex`: two wraps of the SAME body differing only in
  the dyn-annotation payload step in lockstep forever (annotations
  never influence fragment stepping — they are race bookkeeping), so
  their WPs are interderivable whenever the postconditions agree
  modulo `SpikeVal.merge`. Proved by Löb induction.
- `wp_annot`: the actual commuting rule, by Löb induction; the
  merge case discharges through the reindexing lemma (that is the
  step the naive bind-style proof cannot take — recorded in the
  slice notes as the R-i finding). -/

/-- `wp_value'` at the fragment's value injection. -/
theorem wp_ofVal [SpikeGS hlc GF] {s : Stuckness} {E : CoPset} (v : SpikeVal)
    {Φ : SpikeVal → IProp GF} :
    Φ v ⊢ WP (ofVal v) @ s; E {{ Φ }} := wp_value'

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

/-- Annotation reindexing (the lockstep argument): the two wraps make
    exactly corresponding steps — context steps of the shared body, or
    simultaneous merges — so WPs transfer along a `merge`-compatible
    postcondition translation. -/
theorem wp_annot_reindex [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (a : List annot) (dsA dsB : List dyn_annotation) (c : CoreExpr)
    {Φ₁ Φ₂ : SpikeVal → IProp GF}
    (hΦ : ∀ v, Φ₁ (SpikeVal.merge dsA v) = Φ₂ (SpikeVal.merge dsB v)) :
    WP (Expr a (Eannot dsA c)) @ s; E {{ Φ₁ }} ⊢
      WP (Expr a (Eannot dsB c)) @ s; E {{ Φ₂ }} := by
  iloeb as IH generalizing %a %dsA %dsB %c %hΦ
  rcases toVal_annot_cases a c dsA with ⟨rfl, v, rfl, hA⟩ | hA
  · -- value on both sides
    have hB : toVal (Expr ([] : List annot) (Eannot dsB (ofVal (.pure v)))) =
        some (.annot dsB v) := rfl
    rw [wp_unfold.to_eq, wp_unfold.to_eq]
    simp only [language_toVal_eq, wp.pre, hA, hB]
    iintro H
    imod H with H
    imodintro
    have h' : Φ₁ (SpikeVal.annot dsA v) = Φ₂ (SpikeVal.annot dsB v) :=
      hΦ (.pure v)
    rw [← h']
    iexact H
  · -- non-value on both sides
    have hB : toVal (Expr a (Eannot dsB c)) = none := by
      rcases toVal_annot_cases a c dsB with ⟨rfl, v, rfl, _⟩ | hB
      · rw [show toVal (Expr ([] : List annot) (Eannot dsA (ofVal (.pure v)))) =
            some (.annot dsA v) from rfl] at hA
        cases hA
      · exact hB
    rw [wp_unfold.to_eq, wp_unfold.to_eq]
    simp only [language_toVal_eq, wp.pre, hA, hB]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    icases H $$ Hσ with >⟨%hred, H⟩
    imodintro
    isplit
    · ipureintro
      cases s with
      | MaybeStuck => trivial
      | NotStuck =>
        obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
        rcases hstep.1.annot_inv with ⟨hg, c', σ'', hs, _⟩ | ⟨a2, ds2, c'', rfl, _⟩
        · exact ⟨[], _, _, [], ⟨Step.annot_ctx hg hs, rfl⟩⟩
        · exact ⟨[], _, _, [], ⟨Step.annot_merge, rfl⟩⟩
    · iintro %e₂ %σ₂ %eₜ %HstepB Hcred
      obtain ⟨hstepB, rfl⟩ := HstepB
      dsimp only [Nat.repeat]
      rcases hstepB.annot_inv with ⟨hg, c', σ'', hs, hout⟩ | ⟨a2, ds2, c'', rfl, hout⟩
      · cases hout
        imod H $$ %(Expr a (Eannot dsA c')) %_ %([])
          %⟨Step.annot_ctx hg hs, rfl⟩ Hcred with H
        iintro !> !>
        imod H
        iintro !>
        iapply step_fupdN_wand $$ H
        iintro >⟨HSI, Hwp, Hefs⟩
        imodintro
        iframe HSI
        isplitl [Hwp]
        · iapply IH $$ %a %dsA %dsB %c' %hΦ Hwp
        · iexact Hefs
      · cases hout
        imod H $$ %(Expr (a ++ a2) (Eannot (dsA ++ ds2) c'')) %_ %([])
          %⟨Step.annot_merge, rfl⟩ Hcred with H
        iintro !> !>
        imod H
        iintro !>
        iapply step_fupdN_wand $$ H
        iintro >⟨HSI, Hwp, Hefs⟩
        imodintro
        iframe HSI
        isplitl [Hwp]
        · iapply IH $$ %(a ++ a2) %(dsA ++ ds2) %(dsB ++ ds2) %c''
            %(fun v => by
              rw [← SpikeVal.merge_merge, ← SpikeVal.merge_merge]
              exact hΦ (SpikeVal.merge ds2 v)) Hwp
        · iexact Hefs

/-- WP commutes with the run-time dyn-annotation wrapper: to verify
    `{A}e`, verify `e` with the postcondition translated along
    `SpikeVal.merge`. This is what makes the LETS-ANNOT continuation
    (`lets _ = {A}v in E2 --> {A}E2`) usable compositionally. Proved
    by Löb; the annot-rooted body case takes the ANNOTS merge step and
    exits through `wp_annot_reindex`. -/
theorem wp_annot [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (ds : List dyn_annotation) (e : CoreExpr) {Φ : SpikeVal → IProp GF} :
    WP e @ s; E {{ v, Φ (SpikeVal.merge ds v) }} ⊢
      WP (Expr ([] : List annot) (Eannot ds e)) @ s; E {{ Φ }} := by
  iloeb as IH generalizing %ds %e
  cases hv : toVal e with
  | some w =>
    have he := ofVal_of_toVal hv
    subst he
    cases w with
    | pure v =>
      -- the wrap is itself a value: .annot ds v
      rw [wp_unfold.to_eq, wp_unfold.to_eq]
      simp only [language_toVal_eq, wp.pre, toVal_ofVal,
        show toVal (Expr ([] : List annot) (Eannot ds (ofVal (.pure v)))) =
          some (.annot ds v) from rfl]
      iintro H
      imod H with H
      imodintro
      rw [show (SpikeVal.annot ds v) = SpikeVal.merge ds (SpikeVal.pure v) from rfl]
      iexact H
    | annot ds2 v =>
      -- double annot: one deterministic tau (ANNOTS merge) to a value
      iintro H
      iapply wp_lift_pure_det_step_no_fork E
        (e₂ := ofVal (SpikeVal.annot (ds ++ ds2) v))
        ?safe ?det
      case safe =>
        intro σ
        cases s
        · exact ⟨[], _, _, [], ⟨Step.annot_merge, rfl⟩⟩
        · rfl
      case det =>
        intro obs σ₁ e₂' σ₂ eₜ h
        exact annot_merge_det h
      ihave H := wp_value_fupd'.mp $$ H
      imod H with H
      iapply step_fupd_intro Std.LawfulSet.subset_refl
      inext
      iintro -
      iapply wp_ofVal
      rw [show (SpikeVal.annot (ds ++ ds2) v) =
        SpikeVal.merge ds (SpikeVal.annot ds2 v) from rfl]
      iexact H
  | none =>
    by_cases hr : annotRooted e = true
    · -- annot-rooted body: the wrap merges; exit through reindexing
      obtain ⟨a2, ds2, c, rfl⟩ : ∃ a2 ds2 c, e = Expr a2 (Eannot ds2 c) := by
        unfold annotRooted at hr
        split at hr
        · rename_i a2 ds2 c
          exact ⟨a2, ds2, c, rfl⟩
        · cases hr
      iintro H
      iapply wp_lift_pure_det_step_no_fork E
        (e₂ := Expr ([] ++ a2) (Eannot (ds ++ ds2) c))
        ?safe2 ?det2
      case safe2 =>
        intro σ
        cases s
        · exact ⟨[], _, _, [], ⟨Step.annot_merge, rfl⟩⟩
        · rfl
      case det2 =>
        intro obs σ₁ e₂' σ₂ eₜ h
        exact annot_merge_det h
      iapply step_fupd_intro Std.LawfulSet.subset_refl
      inext
      iintro -
      simp only [List.nil_append]
      iapply (wp_annot_reindex (Φ₁ := fun w => iprop(Φ (SpikeVal.merge ds w)))
        a2 ds2 (ds ++ ds2) c
        (fun v => congrArg Φ (SpikeVal.merge_merge ds ds2 v))) $$ H
    · -- plain body: reduction in the Cannot frame, Löb
      have hr' : annotRooted e = false := by simpa using hr
      have hwrap : toVal (Expr ([] : List annot) (Eannot ds e)) = none :=
        toVal_annot_none hv
      rw [wp_unfold.to_eq, wp_unfold.to_eq]
      simp only [language_toVal_eq, wp.pre, hv, hwrap]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      icases H $$ Hσ with >⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        cases s with
        | MaybeStuck => trivial
        | NotStuck =>
          obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
          exact ⟨[], _, _, [], ⟨Step.annot_ctx hr' hstep.1, rfl⟩⟩
      · iintro %e₂ %σ₂ %eₜ %HstepW Hcred
        obtain ⟨hstepW, rfl⟩ := HstepW
        dsimp only [Nat.repeat]
        rcases hstepW.annot_inv with ⟨hg, e'', σ'', hs, hout⟩ |
            ⟨a2, ds2, c, heq, hout⟩
        · cases hout
          imod H $$ %e'' %_ %([]) %⟨hs, rfl⟩ Hcred with H
          iintro !> !>
          imod H
          iintro !>
          iapply step_fupdN_wand $$ H
          iintro >⟨HSI, Hwp, Hefs⟩
          imodintro
          iframe HSI
          isplitl [Hwp]
          · iapply IH $$ %ds %e'' Hwp
          · iexact Hefs
        · exact absurd heq (by
            intro heq
            rw [heq] at hr'
            simp [annotRooted] at hr')

/-! ## Sequencing (R6: Iris bind over real Esseq) -/

/-- How a bound value's annotations flow into the continuation's
    value: `lets _ = v in e2` leaves e2's value alone; `lets _ = {A}v
    in e2` prefixes A (LETS-ANNOT + the eventual ANNOTS merge). -/
def mergeInto : SpikeVal → SpikeVal → SpikeVal
  | .pure _, w => w
  | .annot ds _, w => SpikeVal.merge ds w

/-- The value-level sequencing rule for real Esseq (wildcard pattern),
    assembled from Iris `wp_bind` (via the Csseq `Language.Context`
    instance — the R6 "bind layer dissolves" test), the two beta
    lifts (LETS-PURE / LETS-ANNOT as deterministic pure steps), and
    `wp_annot` for the LETS-ANNOT continuation. -/
theorem wp_sseq [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    {Φ : SpikeVal → IProp GF} :
    WP e1 @ s; E {{ v, ▷ WP e2 @ s; E {{ w, Φ (mergeInto v w) }} }} ⊢
      WP (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2)) @ s; E
        {{ Φ }} := by
  refine .trans ?_
    (wp_bind (fun e => Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e e2)))
  apply wp_mono
  intro v
  cases v with
  | pure v =>
    refine .trans ?_ (wp_lift_pure_det_step_no_fork E (e₂ := e2) ?safeP ?detP)
    case safeP =>
      intro σ
      cases s
      · exact ⟨[], _, _, [], ⟨Step.sseq_pure, rfl⟩⟩
      · rfl
    case detP =>
      intro obs σ₁ e₂' σ₂ eₜ h
      exact sseq_pure_det h
    iintro HP
    iapply step_fupd_intro Std.LawfulSet.subset_refl
    inext
    iintro -
    iapply (wp_mono (fun w => .rfl) :
      WP e2 @ s; E {{ w, Φ (mergeInto (SpikeVal.pure v) w) }} ⊢
        WP e2 @ s; E {{ Φ }}) $$ HP
  | annot ds v =>
    refine .trans ?_ (wp_lift_pure_det_step_no_fork E
      (e₂ := Expr ([] : List annot) (Eannot ds e2)) ?safeA ?detA)
    case safeA =>
      intro σ
      cases s
      · exact ⟨[], _, _, [], ⟨Step.sseq_annot, rfl⟩⟩
      · rfl
    case detA =>
      intro obs σ₁ e₂' σ₂ eₜ h
      exact sseq_annot_det h
    iintro HP
    iapply step_fupd_intro Std.LawfulSet.subset_refl
    inext
    iintro -
    ihave HP := (wp_mono (fun w => .rfl) :
      WP e2 @ s; E {{ w, Φ (mergeInto (SpikeVal.annot ds v) w) }} ⊢
        WP e2 @ s; E {{ w, Φ (SpikeVal.merge ds w) }}) $$ HP
    iapply wp_annot ds e2 $$ HP

/-! ## Triples

The triple is the standard Iris-WP definition: `P` entails the
weakest precondition at NotStuck (UB-exclusion IS the NotStuck
obligation, R4) with the full mask ⊤. -/

def triple [SpikeGS hlc GF] (P : IProp GF) (e : CoreExpr)
    (Ψ : SpikeVal → IProp GF) : Prop :=
  P ⊢ WP e @ Stuckness.NotStuck; ⊤ {{ Ψ }}

/-- FRAME (the acceptance item, stated at triple level; the WP-level
    rule is Iris's `wp_frame_r`/`wp_frame_l`). -/
theorem triple_frame [SpikeGS hlc GF] {P R : IProp GF} {e : CoreExpr}
    {Ψ : SpikeVal → IProp GF} (h : triple P e Ψ) :
    triple iprop(P ∗ R) e (fun v => iprop(Ψ v ∗ R)) :=
  (BI.sep_mono h .rfl).trans (wp_frame_r.trans (wp_mono fun _ => BI.sep_comm.1))

/-- CONSEQUENCE (from BI entailment). -/
theorem triple_conseq [SpikeGS hlc GF] {P' P : IProp GF} {e : CoreExpr}
    {Ψ Ψ' : SpikeVal → IProp GF} (hP : P' ⊢ P) (hΨ : ∀ v, Ψ v ⊢ Ψ' v)
    (h : triple P e Ψ) : triple P' e Ψ' :=
  hP.trans (h.trans (wp_mono hΨ))

/-- wp_wand, re-exported at the spike's language (Iris's `wp_wand`). -/
theorem spike_wp_wand [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    {e : CoreExpr} {Φ Ψ : SpikeVal → IProp GF} :
    WP e @ s; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }} :=
  wp_wand

/-- SEQ: {P} e1 {Q} and {Q} e2 {R} give {P} e1;e2 {R} (assertion
    postconditions — the wildcard-binding form the fragment needs;
    the value-binding generalization is `wp_sseq`). -/
theorem triple_seq [SpikeGS hlc GF] {P Q R : IProp GF}
    {bty : core_base_type} {e1 e2 : CoreExpr}
    (h1 : triple P e1 (fun _ => Q)) (h2 : triple Q e2 (fun _ => R)) :
    triple P (sseqExpr bty e1 e2) (fun _ => R) := by
  refine h1.trans (.trans ?_ (wp_sseq [] [] bty e1 e2))
  exact wp_mono fun v => h2.trans BI.later_intro

/-! ## The exhibit -/

/-- signed int (the recon's probe type). -/
def intTy : ctype := Ctype [] (.Basic (.Integer (.Signed .Int_)))

/-- The Core value `Specified(7) : loaded integer`. -/
def sevenVal : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval 7)))

/-- Its memory value. -/
def sevenMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 7)

/-- Its byte image (the engine's own serialization). -/
def sevenBytes : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes [] sevenMval).2

theorem seven_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) sevenVal =
      some sevenMval := rfl

theorem seven_storable : StorableAt intTy sevenMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- THE EXHIBIT ([USER 2026-08-30], the go order):

      {x ↦ - ∗ y ↦ a} store(x, 7) {x ↦ 7 ∗ y ↦ a}

    derived COMPOSITIONALLY: FRAME on the store small axiom, then
    CONSEQUENCE to forget the return value. `y`'s cell is entirely
    arbitrary (any type, any bytes) and untouched. -/
theorem exhibit [SpikeGS hlc GF] (x y : CerbMem.PointerValue)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) :
    triple (GF := GF)
      iprop(pointsToCell x (.own 1) intTy bs ∗ pointsToCell y (.own 1) ty' bs')
      (storeExpr loc ann intTy x sevenVal mo)
      (fun _ => iprop(pointsToCell x (.own 1) intTy sevenBytes ∗
        pointsToCell y (.own 1) ty' bs')) := by
  -- 1. the small axiom, instantiated at 7/int
  have hax : triple (GF := GF) (pointsToCell x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun w => iprop(∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] Vunit⌝ ∗
        pointsToCell x (.own 1) intTy sevenBytes)) :=
    wp_store loc ann intTy x sevenVal mo sevenMval bs seven_encodes
      seven_storable
  -- 2. FRAME with y's cell
  have hfr := triple_frame (R := pointsToCell y (.own 1) ty' bs') hax
  -- 3. CONSEQUENCE: drop the return-value information
  refine triple_conseq .rfl ?_ hfr
  intro v
  iintro ⟨⟨%fp, %hw, Hx⟩, Hy⟩
  iframe

/-! ## The anti-frame sanity check (negative test — locality is real)

A failing example cannot be committed compiling, so the test is
recorded as its verbatim transcript (re-runnable; also in the slice
notes). Claiming y's cell in the postcondition WITHOUT owning it in
the precondition leaves the derivation stuck on exactly the missing
cell, with an EMPTY spatial context after the x-cell is consumed:

```
example {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (x y : CerbMem.PointerValue) (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) :
    triple (GF := GF) (pointsToCell x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun _ => iprop(pointsToCell x (.own 1) intTy sevenBytes ∗
        pointsToCell y (.own 1) ty' bs')) := by
  have hax : triple (GF := GF) (pointsToCell x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun w => iprop(∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] Vunit⌝ ∗
        pointsToCell x (.own 1) intTy sevenBytes)) :=
    wp_store loc ann intTy x sevenVal mo sevenMval bs seven_encodes
      seven_storable
  refine triple_conseq .rfl ?_ hax
  intro v
  iintro ⟨%fp, %hw, Hx⟩
  iframe
```

Transcript (verbatim, `lake env lean` on the above, 2026-08-30):

```
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
inst✝ : SpikeGS hlc GF
x y : CerbMem.PointerValue
loc : CerbLocation.Loc
ann : core_run_annotation
mo : memory_order
bs bs' : List CerbMem.AbsByte
ty' : ctype
hax :
  triple (x ↦c intTy ; bs) (storeExpr loc ann intTy x sevenVal mo) fun w =>
    iprop(∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] Vunit⌝ ∗ x ↦c intTy ; sevenBytes)
v : SpikeVal
fp : CerbMem.Footprint
hw : v = SpikeVal.annot [DA_pos [] fp] Vunit
⊢
  ⊢ y ↦c ty' ; bs'
```
-/

end RefinedCerberus.Spike
