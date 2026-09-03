/-
CerberusHeapLang.Rules — the base stratum: the atomic step
specifications, the store/load small axioms at iris-lean's raw WP,
and the readout combinator.

The contents:
- THE ATOMIC STEP SPECIFICATIONS (`AtomicStep`; `store_atomic`,
  `load_atomic`, `loadAt_atomic`, `storeAt_atomic`, `create_atomic`,
  `kill_atomic`)
  — every memory small axiom proved ONCE, against `Step`, in the
  mask-generic one-step-to-value shape all three judgments lift
  (`wp_of_atomic` here; `wps_of_atomic`, `wpt_of_atomic` in Wps.lean
  and Wpt.lean). Each runs the real engine function inside the proof
  (`storeM_success`, `loadM_success`, `storeM_at`, `loadM_at`,
  `allocateObject_success`, Heap.lean).
- THE SMALL AXIOMS `wp_store` / `wp_load` (corollaries) — UB-EXCLUDING:
  the preconditions rule out every NDkilled (undefined-behaviour or
  error) arm of the engine's storeM/loadM: the points-to supplies
  pointer shape, liveness, bounds, writability, non-atomicity;
  `StorableAt` supplies the type-compatibility fact (the non-UB
  `MerrOther` arm); `cellLoadTrap = false` excludes the `_Bool`
  trap-representation arm. Both are generic in the machine context
  `M` and the environment stack `ρ`: a local action step never
  consults the label context (the jump disjuncts of the inversions
  are refuted by node shape) and returns the env VERBATIM.
- THE READOUT COMBINATOR `stateInterp_readout` — the ONE open/close of
  the state interpretation the projection (Adequacy.lean) uses to turn
  an Iris postcondition into a pure fact about the final memory.
- `deliveryCost` (the value protocol's step cost: 1 for a bare value,
  2 for an annotated one), `spike_wp_wand` (iris-lean's `wp_wand` at
  this language), and the value dichotomy of an annotation-wrapped
  term (`toVal_annot_cases`, `toVal_annot_none`), consumed by the
  judgments' annotation rules.

WHAT IS DELIBERATELY NOT HERE. Frame and consequence at the raw WP are
iris-lean's own `wp_frame_r` / `wp_mono`. There is NO raw-WP
sequencing rule and NO raw-WP annotation-commuting rule: at a
populated label map both are FALSE for the base WP — a jump discards
the `Esseq`/`Eannot` context, so the premise's continuation and the
conclusion's land on the same registered body owing DIFFERENT
postconditions. Sequencing, annotation commutation, frame across back
edges and consequence are therefore stated at the label-context
judgments `wps` (Wps.lean) and `wpt` (Wpt.lean), whose jump clause is
post-independent; that is why those judgments exist.

SOUNDNESS STATUS: every theorem here is proved against `Step`
(Step.lean), the hand-written mirror; `Step` is certified against the
engine's step_ctx/driver composite (Soundness.lean), and the bundled
`SpikeGS` ghost state is constructed inside the adequacy proof
(Adequacy.lean), so what is proved here acquires engine-level meaning
through the projection theorems.
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
        metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk ∗ budgetInterp mk) := .rfl

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
        ⌜pv = cellPtr i a⌝ ∗ metaOwn i dq (objCell tds a ty true false) ∗
        bytesOwn a dq bs ∗
        ⌜bs.length = CerbMem.sizeofCtype tds ty ∧ decIndep tds a ty bs⌝) := .rfl

/-! ## The delivery cost of a value (the drive lane's value protocol:
PROGRAM-DONE costs one drive step; an annot value pays the
REMOVE-ANNOT tau first — Soundness.lean, the value protocol). Stated
here, below every stratum, because the atomic step specification
carries it. -/

def deliveryCost : SpikeVal → Nat
  | .pure _ => 1
  | .annot _ _ => 2

@[simp] theorem deliveryCost_pure (v : value) :
    deliveryCost (.pure v) = 1 := rfl

@[simp] theorem deliveryCost_annot (ds : List dyn_annotation) (v : value) :
    deliveryCost (.annot ds v) = 2 := rfl

theorem deliveryCost_pos (w : SpikeVal) : 1 ≤ deliveryCost w := by
  cases w <;> simp [deliveryCost]

/-! ## THE ATOMIC STEP SPECIFICATION — one proof per small axiom
(2026-09-02 professor review 1, required fix 8)

A memory action of the fragment is ATOMIC: one `Step` from the redex
to a VALUE, forking nothing. `AtomicStep M e ρ c P Q` says exactly
that, in the shape every stratum's step clause consumes: under `P`
and the state interpretation, at any mask pair `E₂ ⊆ E₁`, the
configuration is reducible, and every step of it re-establishes the
interpretation at a value `w` (delivery cost ≤ `c`) with `Q w`. Each
small axiom is proved ONCE, as an `AtomicStep`, by the engine
unfolding (`storeM_success`/`loadM_success`/`storeM_at`/`loadM_at`/
`allocateObject_success` against `Step`); the three strata's rules
are corollaries through three lifting lemmas — `wp_of_atomic` (here,
iris-lean's `wp_lift_atomic_step`), `wps_of_atomic` (Wps.lean) and
`wpt_of_atomic` (Wpt.lean, budget `c + 1`).

WHY THIS SHAPE AND NOT "`WP` entails `wps`" (the review's suggested
lemma). A raw-WP hypothesis cannot be lifted to `wps`/`wpt`:
iris-lean's `wp.pre` places its `▷` AFTER the step's `|={∅}=>`
(`£ 1 ={∅}▷=∗^[1] …`), while `wps.pre`'s step clause — the
`wp_lift_step` premise shape — places `▷` BEFORE the `∀` over steps;
`|={∅}=> ▷ P ⊢ ▷ |={∅}=> P` is not a law of the logic, and the one
later credit the clause supplies is spent feeding the raw WP. The
mask-generic atomic specification is the common ancestor all three
can be derived from; it is also exactly what the twelve former
direct proofs established before their final `wp`/`wps`/`wpt`
packaging lines. -/

/-- The atomic step specification of `e` at `ρ`: precondition `P`,
    postcondition `Q` on the delivered value, delivery cost bound
    `c`; mask-generic (`E₂ ⊆ E₁`), observations trivial (`Empty`),
    no forks. -/
def AtomicStep [SpikeGS hlc GF] (M : MachineCtx) (e : CoreExpr) (ρ : EnvStack)
    (c : Nat) (P : IProp GF) (Q : SpikeVal → IProp GF) : Prop :=
  ∀ (E₁ E₂ : CoPset), E₂ ⊆ E₁ →
  ∀ (σ₁ : Mem) (ns : Nat) (obs : List Empty) (nt : Nat),
    iprop(P ∗ stateInterp σ₁ ns obs nt) ⊢
      iprop(|={E₁,E₂}=> (⌜PrimStep.Reducible ((⟨e, ρ, M⟩ : CoreRt), σ₁)⌝ ∗
        ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
          ⌜((⟨e, ρ, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝ -∗
          |={E₂,E₁}=> (stateInterp σ₂ (ns + 1) obs nt ∗
            ∃ w : SpikeVal, ⌜r = (⟨ofVal w, ρ, M⟩ : CoreRt) ∧ eₜ = [] ∧
              deliveryCost w ≤ c⌝ ∗ Q w)))

/-- LIFTING TO THE RAW WP (any stuckness, any mask): an atomic step
    specification yields iris-lean's WP of the redex, the
    postcondition applied to the delivered value at the verbatim env
    and context. -/
theorem wp_of_atomic [SpikeGS hlc GF] {s : Stuckness} {E : CoPset} {M : MachineCtx}
    {e : CoreExpr} {ρ : EnvStack} {c : Nat} {P : IProp GF} {Q : SpikeVal → IProp GF}
    (h : AtomicStep M e ρ c P Q) (hnv : toVal e = none)
    (Φ : CoreRVal → IProp GF) :
    iprop(P ∗ (∀ w : SpikeVal, Q w -∗ Φ (⟨w, ρ, M⟩ : CoreRVal))) ⊢
      WP (⟨e, ρ, M⟩ : CoreRt) @ s; E {{ Φ }} := by
  have htoval : ToVal.toVal (Val := CoreRVal) (⟨e, ρ, M⟩ : CoreRt) = none := by
    rw [language_toVal_eq, toValRt_mk, hnv]
    rfl
  iintro ⟨HP, HΦ⟩
  iapply wp_lift_atomic_step htoval
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  cases obs with
  | cons o _ => exact o.elim
  | nil =>
  simp only [List.nil_append]
  imod (h E E Std.LawfulSet.subset_refl σ₁ ns obs' nt) $$ [$HP $Hσ]
    with ⟨%hred, Hcont⟩
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact hred
    · trivial
  iintro !> %e₂ %σ₂ %eₜ %Hstep -
  imod Hcont $$ %e₂ %σ₂ %eₜ %Hstep with ⟨Hσ', %w, %hw, HQ⟩
  obtain ⟨rfl, rfl, -⟩ := hw
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  isplitl [Hσ']
  · iexact Hσ'
  isplitl [HΦ HQ]
  · iexists (⟨w, ρ, M⟩ : CoreRVal)
    isplit
    · ipureintro
      rw [language_toVal_eq, toValRt_mk, toVal_ofVal]
      rfl
    · iapply HΦ $$ HQ
  · itrivial

/-! ## The small axioms, proved once -/

/-- STORE (whole cell, full ownership, UB-excluding) as an atomic
    step: ONE application of the real `CerbMem.storeM`
    (`storeM_success`, Heap.lean). Preconditions vs the NDkilled arms
    (CerbMem.lean:1662-1696): `hst.compat` kills the ill-typed-store
    `Other` arm; the ↦'s `cellPtr` shape kills
    null/function/no-prov/device; Coh's liveness+bounds+writability+
    non-atomicity (carried by stateInterp) kill the rest. The
    delivered value is the annotated unit `{DA_pos [] fp} unit`
    (engine-forced; no aid enters the terms). -/
theorem store_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    AtomicStep M (storeExpr loc ann ty pv cv mo) ρ 2
      (pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs)
      (fun w => iprop(∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] Vunit⌝ ∗
        pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  iintro ⟨Hpt, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  icases (pointsToCell_iff M.tagDefs pv (.own 1) ty bs).mp $$ Hpt
    with ⟨%i, %addr, %Hpv, Hm, Hb, %Hpure⟩
  subst Hpv
  obtain ⟨hlen, hdec⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm i = some (objCell M.tagDefs addr ty true false)⌝
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
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.store_canonical hmv hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨mv', fp', σ'', hmv', hmem', hout⟩ := hstep.store_inv
  obtain rfl : mv = mv' := Option.some.inj (hmv.symm.trans hmv')
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : fp' = CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype M.tagDefs ty) ∧
      σ'' = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes M.tagDefs [] mv).2 := by
    have h := Option.some.inj hmem'.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype M.tagDefs ty))]
        (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧ rρ = ρ ∧
      σ₂ = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes M.tagDefs [] mv).2 := by
    simpa [Prod.mk.injEq] using hout
  subst hre hσ
  obtain rfl : ρ = rρ := hrρ.symm
  imod Hclose with -
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
  · iexists (SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype M.tagDefs ty))] Vunit)
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 2⟩
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

/-- LOAD (whole cell, any fraction, UB-excluding) as an atomic step:
    ONE application of the real `CerbMem.loadM` (`loadM_success`);
    the delivered value is the annotated engine decode
    `{DA_pos [] fp} (loadedVal …)`. `htrap` excludes the `_Bool`
    trap-representation kill arm (CerbMem.lean:1598-1604) — the one
    loadM failure the points-to alone cannot rule out. -/
theorem load_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    AtomicStep M (loadExpr loc ann ty pv mo) ρ 2
      (pointsToCell M.tagDefs (GF := GF) pv dq ty bs)
      (fun w => iprop(∃ fp,
        ⌜w = SpikeVal.annot [DA_pos [] fp] (loadedVal M.tagDefs pv ty bs)⌝ ∗
        pointsToCell M.tagDefs pv dq ty bs)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  iintro ⟨Hpt, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  icases (pointsToCell_iff M.tagDefs pv dq ty bs).mp $$ Hpt
    with ⟨%i, %addr, %Hpv, Hm, Hb, %Hpure⟩
  subst Hpv
  obtain ⟨hlen, hdec⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm i = some (objCell M.tagDefs addr ty true false)⌝
      $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  ihave %Hread : ⌜CerbMem.readBytesFrom σ₁ addr bs.length = bs⌝ $$ [Hbi Hb]
  · iapply bytesOwn_read HG addr dq bs $$ [$Hbi $Hb]
  have hcell : CellCoh M.tagDefs σ₁ i ⟨addr, ty, bs⟩ :=
    CellCoh.ofParts M.tagDefs (HG.metas i _ Hgetm) hlen (hlen ▸ Hread) hdec
  have hrun := loadM_success M.tagDefs σ₁ i ⟨addr, ty, bs⟩ loc hcell htrap
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.load_canonical hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨fp', mval', σ'', hmem', hout⟩ := hstep.load_inv
  rw [hrun] at hmem'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ :
      (fp' = CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty) ∧
        mval' = decodeCell M.tagDefs ⟨addr, ty, bs⟩) ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem'.symm
    exact ⟨⟨congrArg (fun p => p.1.1) h, congrArg (fun p => p.1.2) h⟩,
      (congrArg Prod.snd h).symm⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty))]
        (Expr [] (Epure (Pexpr [] () (PEval
          (valueFromMemValue (decodeCell M.tagDefs ⟨addr, ty, bs⟩)).2))))) ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
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
  · iexists (SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty))]
      (loadedVal M.tagDefs (cellPtr i addr) ty bs))
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 2⟩
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

/-- LOAD FROM A READ-ONLY CELL (whole cell, any fraction, UB-excluding)
    as an atomic step (K1): the same engine path as `load_atomic` —
    `loadM` never consults writability (CerbMem.lean:1621-1664) — so a
    `readonlyCell` supports the load spec verbatim; the engine seam is
    the live-cell load `loadM_live` at the read-only metadata literal.
    There is NO store counterpart: `storeM` at a read-only allocation
    is killed with `MerrWriteOnReadOnly kind` (`storeM_readonly_kills`,
    Heap.lean; :1724-1725), and `Step` has no step at a killed arm. -/
theorem load_atomic_readonly [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    AtomicStep M (loadExpr loc ann ty pv mo) ρ 2
      (readonlyCell M.tagDefs (GF := GF) pv dq ty bs)
      (fun w => iprop(∃ fp,
        ⌜w = SpikeVal.annot [DA_pos [] fp] (loadedVal M.tagDefs pv ty bs)⌝ ∗
        readonlyCell M.tagDefs pv dq ty bs)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  iintro ⟨Hpt, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  icases (readonlyCell_iff M.tagDefs pv dq ty bs).mp $$ Hpt
    with ⟨%i, %addr, %Hpv, Hm, Hb, %Hpure⟩
  subst Hpv
  obtain ⟨hlen, hdec⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm i = some (objCell M.tagDefs addr ty true true)⌝
      $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  ihave %Hread : ⌜CerbMem.readBytesFrom σ₁ addr bs.length = bs⌝ $$ [Hbi Hb]
  · iapply bytesOwn_read HG addr dq bs $$ [$Hbi $Hb]
  have hrun := loadM_live M.tagDefs σ₁ i (objCell M.tagDefs addr ty true true) 0 ty bs
    (decodeCell M.tagDefs ⟨addr, ty, bs⟩) loc (HG.metas i _ Hgetm) rfl
    (by simp [objCell])
    (by rw [hlen] at Hread; simpa [objCell] using Hread)
    (by simpa [objCell] using hdec σ₁.lastUsedUnionMembers σ₁.funptrmap)
    htrap
  simp only [objCell, Int.natCast_zero, Int.add_zero] at hrun
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.load_canonical hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨fp', mval', σ'', hmem', hout⟩ := hstep.load_inv
  rw [hrun] at hmem'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ :
      (fp' = CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty) ∧
        mval' = decodeCell M.tagDefs ⟨addr, ty, bs⟩) ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem'.symm
    exact ⟨⟨congrArg (fun p => p.1.1) h, congrArg (fun p => p.1.2) h⟩,
      (congrArg Prod.snd h).symm⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty))]
        (Expr [] (Epure (Pexpr [] () (PEval
          (valueFromMemValue (decodeCell M.tagDefs ⟨addr, ty, bs⟩)).2))))) ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
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
  · iexists (SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty))]
      (loadedVal M.tagDefs (cellPtr i addr) ty bs))
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 2⟩
    iexists (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype M.tagDefs ty))
    isplit
    · ipureintro; rfl
    iapply (readonlyCell_iff M.tagDefs _ _ _ _).mpr
    iexists i, addr
    isplit
    · ipureintro; rfl
    isplitl [Hm]
    · iexact Hm
    isplitl [Hb]
    · iexact Hb
    · ipureintro
      exact ⟨hlen, hdec⟩

/-- GENERIC TYPED SUBRANGE LOAD as an atomic step (any fractions,
    UB-excluding): loading a typed view delivers the fixed decode of
    its byte image; the view rides through untouched. `hdec` is the
    view's table-independent decode at the interior address; `htrap`
    excludes the _Bool trap arm at the accessed type. Engine seam:
    `loadM_at`. -/
theorem loadAt_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (mo : memory_order) (dqm dqb : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    AtomicStep M (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo) ρ 2
      (pointsToView M.tagDefs (GF := GF) id a aty off dqm dqb vty bs)
      (fun w => iprop(∃ fp,
        ⌜w = SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)⌝ ∗
        pointsToView M.tagDefs id a aty off dqm dqb vty bs)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  iintro ⟨Hv, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  icases (pointsToView_iff M.tagDefs id a aty off dqm dqb vty bs).mp $$ Hv
    with ⟨Hm, %Hpure, Hb⟩
  obtain ⟨hbound, hlenbs⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm id = some (objCell M.tagDefs a aty true false)⌝
      $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  ihave %Hread : ⌜CerbMem.readBytesFrom σ₁ (a + (off : Int)) bs.length = bs⌝
      $$ [Hbi Hb]
  · iapply bytesOwn_read HG (a + (off : Int)) dqb bs $$ [$Hbi $Hb]
  have hrun := loadM_at M.tagDefs σ₁ id a aty off vty bs mv loc
    (HG.metas id _ Hgetm) hbound (hlenbs ▸ Hread)
    (hdec σ₁.lastUsedUnionMembers σ₁.funptrmap) htrap
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.load_canonical hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨fp', mval', σ'', hmem', hout⟩ := hstep.load_inv
  rw [hrun] at hmem'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ :
      (fp' = CerbMem.Footprint.FP .R (a + (off : Int))
        (CerbMem.sizeofCtype M.tagDefs vty) ∧ mv = mval') ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem'.symm
    exact ⟨⟨congrArg (fun p => p.1.1) h,
      (congrArg (fun p => p.1.2) h).symm⟩,
      (congrArg Prod.snd h).symm⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .R (a + (off : Int))
          (CerbMem.sizeofCtype M.tagDefs vty))]
        (Expr [] (Epure (Pexpr [] () (PEval (valueFromMemValue mv).2))))) ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
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
  · iexists (SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .R (a + (off : Int))
        (CerbMem.sizeofCtype M.tagDefs vty))] ((valueFromMemValue mv).2))
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 2⟩
    iexists (CerbMem.Footprint.FP .R (a + (off : Int)) (CerbMem.sizeofCtype M.tagDefs vty))
    isplit
    · ipureintro; rfl
    iapply (pointsToView_iff M.tagDefs _ _ _ _ _ _ _ _).mpr
    isplitl [Hm]
    · iexact Hm
    isplit
    · ipureintro
      exact ⟨hbound, hlenbs⟩
    · iexact Hb

/-- GENERIC FULL-OWNERSHIP TYPED SUBRANGE STORE as an atomic step.
    Engine seam: `storeM_at`; `StorableView` supplies the
    type-compatibility and serialization facts. -/
theorem storeAt_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order) (dqm : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hst : StorableView M.tagDefs vty mv) :
    AtomicStep M (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo) ρ 2
      (pointsToView M.tagDefs (GF := GF) id a aty off dqm (.own 1) vty bs)
      (fun w => iprop(∃ fp, ⌜w = SpikeVal.annot [DA_pos [] fp] Vunit⌝ ∗
        pointsToView M.tagDefs id a aty off dqm (.own 1) vty
          (CerbMem.memValueToBytes M.tagDefs [] mv).2)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  iintro ⟨Hv, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  icases (pointsToView_iff M.tagDefs id a aty off dqm (.own 1) vty bs).mp $$ Hv
    with ⟨Hm, %Hpure, Hb⟩
  obtain ⟨hbound, hlenbs⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm id = some (objCell M.tagDefs a aty true false)⌝
      $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  ihave %Hcover : ⌜∀ (j : Nat), j < bs.length →
      Iris.Std.PartialMap.get? mb ((a + (off : Int)) + (j : Int)) = bs[j]?⌝
      $$ [Hbi Hb]
  · iapply bytesOwn_get mb (a + (off : Int)) (.own 1) bs $$ [$Hbi $Hb]
  have hrun := storeM_at M.tagDefs σ₁ id a aty off vty mv loc
    (HG.metas id _ Hgetm) hbound hst.compat hst.fpm hst.bytes_fpm
  have hlen' : (CerbMem.memValueToBytes M.tagDefs [] mv).2.length = bs.length := by
    rw [hst.len, hlenbs]
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.store_canonical hmv hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨mv', fp', σ'', hmv', hmem', hout⟩ := hstep.store_inv
  obtain rfl : mv = mv' := Option.some.inj (hmv.symm.trans hmv')
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : fp' = CerbMem.Footprint.FP .W (a + (off : Int))
      (CerbMem.sizeofCtype M.tagDefs vty) ∧
      σ'' = CerbMem.writeBytesTo σ₁ (a + (off : Int))
        (CerbMem.memValueToBytes M.tagDefs [] mv).2 := by
    have h := Option.some.inj hmem'.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .W (a + (off : Int))
          (CerbMem.sizeofCtype M.tagDefs vty))]
        (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧ rρ = ρ ∧
      σ₂ = CerbMem.writeBytesTo σ₁ (a + (off : Int))
        (CerbMem.memValueToBytes M.tagDefs [] mv).2 := by
    simpa [Prod.mk.injEq] using hout
  subst hre hσ
  obtain rfl : ρ = rρ := hrρ.symm
  imod Hclose with -
  imod (bytesOwn_update mb (a + (off : Int)) bs
    (CerbMem.memValueToBytes M.tagDefs [] mv).2 hlen') $$ [$Hbi $Hb] with ⟨Hbi, Hb⟩
  imodintro
  isplitl [Hmi Hbi Hki]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists mm, (insertRange mb (a + (off : Int)) (CerbMem.memValueToBytes M.tagDefs [] mv).2), mk
    isplitr [Hmi Hbi Hki]
    · ipureintro
      exact HG.storeRange (a + (off : Int)) (CerbMem.memValueToBytes M.tagDefs [] mv).2
        (fun j hj => ⟨bs[j]'(by omega), by
          rw [Hcover j (by omega)]
          exact List.getElem?_eq_getElem _⟩)
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  · iexists (SpikeVal.annot
      [DA_pos [] (CerbMem.Footprint.FP .W (a + (off : Int))
        (CerbMem.sizeofCtype M.tagDefs vty))] Vunit)
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 2⟩
    iexists (CerbMem.Footprint.FP .W (a + (off : Int)) (CerbMem.sizeofCtype M.tagDefs vty))
    isplit
    · ipureintro; rfl
    iapply (pointsToView_iff M.tagDefs _ _ _ _ _ _ _ _).mpr
    isplitl [Hm]
    · iexact Hm
    isplit
    · ipureintro
      exact ⟨hbound, hst.len⟩
    · iexact Hb

/-- `create(align, ty)` — positive strong create, canonical value
    operands (what `Step.create` fires on). -/
def createExpr (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (align : CerbMem.IntegerValue) (ty : ctype) (pref : prefix0) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Create (Pexpr [] () (PEval (Vobject (OVinteger align))))
            (Pexpr [] () (PEval (Vctype ty))) pref))))

open Iris.Std.PartialMap in
/-- CREATE FROM THE BUDGET, as an atomic step (kill/free arc K2.5 — the
    heap-implementation form the public rules `wps_create`/`wpt_create`
    lift): `allocBudget (allocCost ty alignN)` buys ONE application of
    the real `allocateObject` (`allocateObject_success`), which delivers
    an EXISTENTIAL fresh pointer (the engine's cursor picks it; no
    client sees the cursor since K2.5) with the whole-allocation
    points-to at unspecified bytes and its machine-address bounds
    `0 < addrOf p < 2^64` (`MemWF.la_wf` through `CohG.wf`). The budget
    is CONSUMED (nothing comes back). The out-of-memory arm is excluded
    by THE COUPLING INEQUALITY: the budget authority is at most the
    cursor's headroom (`budgetInterp`), a fragment is at most the
    authority (`budgetAuth_bound`), and a cost within the headroom is a
    nonzero fresh base (`freshBase_ne_zero_of_cost`); the authority
    shrinks by the cost while the headroom shrinks by at most the cost
    (`headroom_freshBase`), so the inequality is re-established. The
    delivered value is the BARE pointer (cost 1). `hsz`/`hatom` pin a
    real non-atomic object type; `hinert` is the unspecified image's
    decode-inertness at every address (rfl for scalar and integer-array
    types). -/
theorem create_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (ty : ctype)
    (pref : prefix0) (ρ : EnvStack)
    (hsz : 0 < CerbMem.sizeofCtype M.tagDefs ty) (hatom : atomicTy ty = false)
    (hinert : ∀ a : Int, decIndep M.tagDefs a ty
      (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte)) :
    AtomicStep M (createExpr loc ann (.IV aprov alignN) ty pref) ρ 1
      (allocBudget (GF := GF) (allocCost M.tagDefs ty alignN))
      (fun w => iprop(∃ p : CerbMem.PointerValue,
        ⌜w = SpikeVal.pure (Vobject (OVpointer p))⌝ ∗
        pointsToCell M.tagDefs p (.own 1) ty
          (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte) ∗
        ⌜0 < addrOf p ∧ addrOf p < 2 ^ 64⌝)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  iintro ⟨Hb, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki, HB⟩
  icases (budgetInterp_iff mk).mp $$ HB with ⟨%B, HBa, HBc⟩
  -- the fragment is bounded by the authority
  ihave %hle : ⌜allocCost M.tagDefs ty alignN ≤ B⌝ $$ [HBa Hb]
  · iapply budgetAuth_bound B (allocCost M.tagDefs ty alignN)
    isplitl [HBa]
    · iexact HBa
    · iexact Hb
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hpos := allocCost_pos M.tagDefs ty alignN hsz
  icases HBc with (%hB0 | ⟨%c, %hc, Hc⟩)
  · -- a positive cost at the empty authority is impossible
    exact ((by omega) : False).elim
  obtain ⟨Hgetc, hBle⟩ := hc
  obtain ⟨cla, cnid⟩ := c
  obtain ⟨hla, hnid⟩ := HG.cursor _ Hgetc
  simp only at hla hnid hBle
  subst hla
  subst hnid
  have hcurne : get? mk 0 ≠ none := by
    rw [Hgetc]
    simp
  have hla64 : σ₁.lastAddress ≤ 2 ^ 64 := (HG.wf hcurne).la_wf
  have hcost : allocCost M.tagDefs ty alignN ≤ headroom σ₁.lastAddress :=
    Nat.le_trans (Nat.le_add_right _ _) hBle
  have hnz : freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty) ≠ 0 :=
    freshBase_ne_zero_of_cost _ _ _ hsz hcost
  have hcons := headroom_freshBase σ₁.lastAddress alignN _ hsz hcost
  have hrun := allocateObject_success M.tagDefs σ₁ pref aprov alignN ty hsz hnz
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.create_canonical hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', σ'', hmem', hout⟩ := hstep.create_inv
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : cellPtr σ₁.nextAllocId
      (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty)) = pv' ∧
      CerbMem.writeBytesTo
        { σ₁ with
            nextAllocId := σ₁.nextAllocId + 1,
            lastAddress := freshBase σ₁.lastAddress alignN
              (CerbMem.sizeofCtype M.tagDefs ty),
            allocations := σ₁.allocations.insert σ₁.nextAllocId
              { base := freshBase σ₁.lastAddress alignN
                  (CerbMem.sizeofCtype M.tagDefs ty),
                size := (CerbMem.sizeofCtype M.tagDefs ty : Int),
                ty := some ty,
                isReadonly := .IsWritable,
                prefix_ := pref } }
        (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
        (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte) = σ'' := by
    have h := Option.some.inj hmem'
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Epure (Pexpr [] () (PEval
        (Vobject (OVpointer (cellPtr σ₁.nextAllocId
          (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty)))))))) ∧
      rρ = ρ ∧ σ₂ = _ := by
    simpa [Prod.mk.injEq] using hout
  subst hre hσ
  obtain rfl : ρ = rρ := hrρ.symm
  imod Hclose with -
  -- ghost: advance the cursor, mint the metadata, mint the bytes, spend
  -- the budget
  imod (cursorHeap_update
    (AllocCursor.mk (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
      (σ₁.nextAllocId + 1))) $$ [$Hki $Hc] with ⟨Hki, Hc⟩
  have hfreshm : Iris.Std.PartialMap.get? mm σ₁.nextAllocId = none := by
    cases hg : Iris.Std.PartialMap.get? mm σ₁.nextAllocId with
    | none => rfl
    | some mc =>
      have := HG.cur_meta_lt hcurne _ _ hg
      omega
  imod (metaHeap_alloc
    (objCell M.tagDefs (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
      ty true false)
    hfreshm) $$ [$Hmi] with ⟨Hmi, Hmnew⟩
  have hfreshb : (rangeMap
      (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
      (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte)) ##ₘ mb := by
    rw [Iris.Std.PartialMap.disjoint_iff]
    intro key
    cases hg : Iris.Std.PartialMap.get? mb key with
    | none => exact .inr rfl
    | some b =>
      left
      rw [rangeMap_get?]
      rw [if_neg ?_]
      have hkey := HG.cur_byte_lo hcurne _ _ hg
      have hbase_le : freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty) +
          (CerbMem.sizeofCtype M.tagDefs ty : Int) ≤ σ₁.lastAddress :=
        freshBase_add_le M.tagDefs σ₁.lastAddress alignN ty hsz hnz
      intro hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [List.length_replicate] at h2
      exact absurd (Int.lt_of_lt_of_le h2 (Int.le_trans hbase_le hkey))
        (Int.lt_irrefl key)
  imod (byteHeap_alloc_big (rangeMap
      (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
      (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte)) hfreshb)
    $$ [$Hbi] with ⟨Hbi, Hbnew⟩
  imod (budgetAuth_consume (allocCost M.tagDefs ty alignN) m) $$ [$HBa $Hb] with HBa
  imodintro
  isplitl [Hmi Hbi Hki HBa Hc]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists (Iris.Std.PartialMap.insert mm σ₁.nextAllocId
        (objCell M.tagDefs (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
          ty true false)),
      (Iris.Std.PartialMap.union (rangeMap
        (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
        (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte)) mb),
      (Iris.Std.PartialMap.insert mk 0
        ⟨freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty),
          σ₁.nextAllocId + 1⟩)
    isplitr [Hmi Hbi Hki HBa Hc]
    · ipureintro
      exact HG.create M.tagDefs pref alignN ty hsz hatom Hgetc hnz
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    isplitl [Hki]
    · iexact Hki
    · -- the coupling inequality at the advanced cursor: the authority
      -- lost the cost, the headroom lost at most the cost
      iapply budgetInterp_intro _
        ⟨freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty),
          σ₁.nextAllocId + 1⟩ m (Iris.Std.get?_insert_eq rfl)
        (by
          show m ≤ headroom (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
          have hc : allocCost M.tagDefs ty alignN =
            CerbMem.sizeofCtype M.tagDefs ty + alignN.toNat.max 1 - 1 := rfl
          omega)
      isplitl [HBa]
      · iexact HBa
      · iexact Hc
  · iexists (SpikeVal.pure (Vobject (OVpointer (cellPtr σ₁.nextAllocId
        (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))))))
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 1⟩
    ihave HBy : bytesOwn (freshBase σ₁.lastAddress alignN
        (CerbMem.sizeofCtype M.tagDefs ty)) (.own 1)
        (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte) $$ [Hbnew]
    · iapply bigSepM_rangeMap $$ Hbnew
    iexists (cellPtr σ₁.nextAllocId
      (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty)))
    isplit
    · ipureintro; rfl
    isplitl [Hmnew HBy]
    · iapply (pointsToCell_iff M.tagDefs _ _ _ _).mpr
      iexists σ₁.nextAllocId,
        (freshBase σ₁.lastAddress alignN (CerbMem.sizeofCtype M.tagDefs ty))
      isplit
      · ipureintro; rfl
      isplitl [Hmnew]
      · iexact Hmnew
      isplitl [HBy]
      · iexact HBy
      · ipureintro
        exact ⟨by simp, hinert _⟩
    · ipureintro
      exact ⟨freshBase_pos M.tagDefs σ₁.lastAddress alignN ty hnz,
        freshBase_lt_two64 M.tagDefs σ₁.lastAddress alignN ty hsz hnz hla64⟩

/-- `kill(kind, pv)` — positive strong kill, canonical evaluated pointer
    operand (what `Step.kill` fires on; `killRedex`'s spelling). -/
def killExpr (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (kind : kill_kind) (pv : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Kill kind (Pexpr [] () (PEval (Vobject (OVpointer pv))))))))

/-- THE DISPOSE RULE (kill/free arc K2) — the classical `{p ↦ -}
    dispose(p) {emp}` as an atomic step: the STATIC kill (`hstatic :
    is_dynamic kind = false`; `kill(static ty, p)`, C's automatic
    storage) of a whole created object consumes the cell at FULL
    ownership — the liveness token `metaOwn id (.own 1) (objCell … true
    false)` inside `pointsToCell` — and delivers the BARE unit (cost 1)
    with, at most, the persistent DEAD cell `deadObj` (a client may drop
    it; `wps_kill_emp`/`wpt_kill_emp`). ONE application of the real
    `CerbMem.killM` (`killM_success`): the points-to's `cellPtr` shape
    and `MetaCoh` (via the state interpretation) pass every kill arm
    (null/function/other-provenance UB179a, dead UB179b, out-of-bound
    `Other`); nothing about bytes, type or size is checked by the
    engine. Ghost: `metaHeap_update` flips `alive := false`
    (RefinedC's `alloc_alive_kill`), then `metaOwn_persist` discards the
    dead cell; the byte fragments are DROPPED — sound because `killM`
    leaves the bytemap alone (`CohG.bytes` is about `σ.bytemap`) and
    addresses are never reused (`CohG.kill`). The `Static0 ty` payload
    is discarded by the engine, so the kill type is unrelated to the
    cell's type by design (design note §1(a)). -/
theorem kill_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hstatic : is_dynamic kind = false) :
    AtomicStep M (killExpr loc ann kind pv) ρ 1
      (pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs)
      (fun w => iprop(⌜w = SpikeVal.pure Vunit⌝ ∗
        ∃ (id a : Int), ⌜pv = cellPtr id a⌝ ∗ deadObj M.tagDefs id a ty)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  iintro ⟨Hpt, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  -- the byte fragments and the pure layout facts are dropped: the
  -- engine's kill reads none of them
  icases (pointsToCell_iff M.tagDefs pv (.own 1) ty bs).mp $$ Hpt
    with ⟨%i, %addr, %Hpv, Hm, -, -⟩
  subst Hpv
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm i = some (objCell M.tagDefs addr ty true false)⌝
      $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  have hrun : applyMemM (CerbMem.killM loc (is_dynamic kind) (cellPtr i addr)) σ₁ =
      some ((), { σ₁ with deadAllocations := i :: σ₁.deadAllocations,
                          allocations := σ₁.allocations.erase i }) := by
    rw [hstatic]
    exact killM_success σ₁ i (objCell M.tagDefs addr ty true false) loc
      (HG.metas i _ Hgetm) rfl
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.kill_canonical hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨σ'', hmem', hout⟩ := hstep.kill_inv
  rw [hrun] at hmem'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hmem')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hσ⟩ := hout
  subst hre hσ
  obtain rfl : ρ = rρ := hrρ.symm
  imod Hclose with -
  -- ghost: flip the cell to dead, then discard it
  imod (metaHeap_update (objCell M.tagDefs addr ty false false)) $$ [$Hmi $Hm]
    with ⟨Hmi, Hm⟩
  imod (metaOwn_persist i (.own 1) _) $$ Hm with Hm
  imodintro
  isplitl [Hmi Hbi Hki]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists (Iris.Std.PartialMap.insert mm i (objCell M.tagDefs addr ty false false)), mb, mk
    isplitr [Hmi Hbi Hki]
    · ipureintro
      exact HG.kill i _ Hgetm rfl
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  · iexists (SpikeVal.pure Vunit)
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 1⟩
    isplit
    · ipureintro; rfl
    iexists i, addr
    isplit
    · ipureintro; rfl
    · unfold deadObj
      iexact Hm

/-- `alloc(align, size)` — positive strong dynamic allocation, canonical
    evaluated integer operands (what `Step.alloc` fires on; `allocRedex`'s
    spelling). -/
def allocExpr (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (align size : CerbMem.IntegerValue) (pref : prefix0) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc ann
    (Alloc0 (Pexpr [] () (PEval (Vobject (OVinteger align))))
            (Pexpr [] () (PEval (Vobject (OVinteger size)))) pref))))

open Iris.Std.PartialMap in
/-- THE ALLOCATION RULE (kill/free arc K3) — the classical `{emp} cons
    {p ↦ -}` in its budgeted form, as an atomic step: `allocBudget
    (regionCost alignN sizeN)` buys ONE application of the real
    `allocateRegion` (`allocateRegion_success`), which delivers an
    EXISTENTIAL fresh region pointer `cellPtr id a` (the engine's cursor
    picks it) with the whole REGION at full ownership — `regionOwn id a
    sizeN.toNat (.own 1)` at unspecified bytes: untyped, writable, DYNAMIC
    (the cell records `dynamic := true`, coupled to the base's push onto
    `dynamicAddrs`, CerbMem.lean:1548) — and its machine-address bounds
    `0 < a ∧ a + size ≤ 2^64` (`MemWF.la_wf` through `CohG.wf`). The budget
    is CONSUMED. The out-of-memory arm is excluded by THE COUPLING
    INEQUALITY exactly as for `create`, now at EVERY size: the authority is
    at most the cursor's headroom (`budgetInterp`), the fragment is at most
    the authority (`budgetAuth_bound`), the cursor is positive
    (`MemWF.la_pos`, K3), so a cost within the headroom is a nonzero fresh
    base (`freshBase_ne_zero_of_cost'`) and the headroom shrinks by at most
    the cost (`headroom_freshBase'`). `hcost : 0 < regionCost alignN sizeN`
    is what makes the budget FORCE a cursor cell (a zero-cost fragment,
    `allocBudget 0`, is the unit and witnesses nothing): it holds at every
    positive size (`regionCost_pos`) and at size 0 whenever the alignment
    is ≥ 2; the one shape outside the rule is `alloc(al, 0)` at `al ≤ 1`
    — an engine-classified round (`complete_alloc`), never a hidden
    assumption. Ghost: the cursor advances, the metadata cell is minted at
    the fresh id, the (possibly empty) byte range is minted, the budget is
    spent (`CohG.alloc` re-establishes the coupling). The delivered value
    is the BARE pointer (cost 1). No type premise, no `hinert`: regions are
    layout-free. -/
theorem alloc_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov sprov : CerbMem.Provenance) (alignN sizeN : Int)
    (pref : prefix0) (ρ : EnvStack)
    (hcost : 0 < regionCost alignN sizeN) :
    AtomicStep M (allocExpr loc ann (.IV aprov alignN) (.IV sprov sizeN) pref) ρ 1
      (allocBudget (GF := GF) (regionCost alignN sizeN))
      (fun w => iprop(∃ (id a : Int),
        ⌜w = SpikeVal.pure (Vobject (OVpointer (cellPtr id a)))⌝ ∗
        regionOwn id a sizeN.toNat (.own 1) (List.replicate sizeN.toNat undefByte) ∗
        ⌜0 < a ∧ a + (sizeN.toNat : Int) ≤ 2 ^ 64⌝)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  iintro ⟨Hb, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki, HB⟩
  icases (budgetInterp_iff mk).mp $$ HB with ⟨%B, HBa, HBc⟩
  -- the fragment is bounded by the authority
  ihave %hle : ⌜regionCost alignN sizeN ≤ B⌝ $$ [HBa Hb]
  · iapply budgetAuth_bound B (regionCost alignN sizeN)
    isplitl [HBa]
    · iexact HBa
    · iexact Hb
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
  icases HBc with (%hB0 | ⟨%c, %hc, Hc⟩)
  · -- a positive cost at the empty authority is impossible
    exact ((by omega) : False).elim
  obtain ⟨Hgetc, hBle⟩ := hc
  obtain ⟨cla, cnid⟩ := c
  obtain ⟨hla, hnid⟩ := HG.cursor _ Hgetc
  simp only at hla hnid hBle
  subst hla
  subst hnid
  have hcurne : get? mk 0 ≠ none := by
    rw [Hgetc]
    simp
  have hla64 : σ₁.lastAddress ≤ 2 ^ 64 := (HG.wf hcurne).la_wf
  have hlapos : 0 < σ₁.lastAddress := (HG.wf hcurne).la_pos
  have hcostle : sizeN.toNat + alignN.toNat.max 1 - 1 ≤ headroom σ₁.lastAddress :=
    Nat.le_trans (Nat.le_add_right _ _) hBle
  have hnz : freshBase σ₁.lastAddress alignN sizeN.toNat ≠ 0 :=
    freshBase_ne_zero_of_cost' _ _ _ hlapos hcostle
  have hcons := headroom_freshBase' σ₁.lastAddress alignN _ hlapos hcostle
  have hbase_le := freshBase_add_le_nat σ₁.lastAddress alignN sizeN.toNat hnz
  have hbase_pos := freshBase_pos_nat σ₁.lastAddress alignN sizeN.toNat hnz
  have hrun := allocateRegion_success σ₁ pref aprov sprov alignN sizeN hnz
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.alloc_canonical hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', σ'', hmem', hout⟩ := hstep.alloc_inv
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : cellPtr σ₁.nextAllocId
      (freshBase σ₁.lastAddress alignN sizeN.toNat) = pv' ∧
      CerbMem.writeBytesTo
        { σ₁ with
            nextAllocId := σ₁.nextAllocId + 1,
            lastAddress := freshBase σ₁.lastAddress alignN sizeN.toNat,
            allocations := σ₁.allocations.insert σ₁.nextAllocId
              { base := freshBase σ₁.lastAddress alignN sizeN.toNat,
                size := (sizeN.toNat : Int),
                prefix_ := pref },
            dynamicAddrs := freshBase σ₁.lastAddress alignN sizeN.toNat :: σ₁.dynamicAddrs }
        (freshBase σ₁.lastAddress alignN sizeN.toNat)
        (List.replicate sizeN.toNat undefByte) = σ'' := by
    have h := Option.some.inj hmem'
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hσ⟩ := hout
  subst hre hσ
  obtain rfl : ρ = rρ := hrρ.symm
  imod Hclose with -
  -- ghost: advance the cursor, mint the region cell, mint the bytes,
  -- spend the budget
  imod (cursorHeap_update
    (AllocCursor.mk (freshBase σ₁.lastAddress alignN sizeN.toNat)
      (σ₁.nextAllocId + 1))) $$ [$Hki $Hc] with ⟨Hki, Hc⟩
  have hfreshm : Iris.Std.PartialMap.get? mm σ₁.nextAllocId = none := by
    cases hg : Iris.Std.PartialMap.get? mm σ₁.nextAllocId with
    | none => rfl
    | some mc =>
      have := HG.cur_meta_lt hcurne _ _ hg
      omega
  imod (metaHeap_alloc
    (regionCell (freshBase σ₁.lastAddress alignN sizeN.toNat) sizeN.toNat true)
    hfreshm) $$ [$Hmi] with ⟨Hmi, Hmnew⟩
  have hfreshb : (rangeMap
      (freshBase σ₁.lastAddress alignN sizeN.toNat)
      (List.replicate sizeN.toNat undefByte)) ##ₘ mb := by
    rw [Iris.Std.PartialMap.disjoint_iff]
    intro key
    cases hg : Iris.Std.PartialMap.get? mb key with
    | none => exact .inr rfl
    | some b =>
      left
      rw [rangeMap_get?]
      rw [if_neg ?_]
      have hkey := HG.cur_byte_lo hcurne _ _ hg
      intro hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [List.length_replicate] at h2
      exact absurd (Int.lt_of_lt_of_le h2 (Int.le_trans hbase_le hkey))
        (Int.lt_irrefl key)
  imod (byteHeap_alloc_big (rangeMap
      (freshBase σ₁.lastAddress alignN sizeN.toNat)
      (List.replicate sizeN.toNat undefByte)) hfreshb)
    $$ [$Hbi] with ⟨Hbi, Hbnew⟩
  imod (budgetAuth_consume (regionCost alignN sizeN) m) $$ [$HBa $Hb] with HBa
  imodintro
  isplitl [Hmi Hbi Hki HBa Hc]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists (Iris.Std.PartialMap.insert mm σ₁.nextAllocId
        (regionCell (freshBase σ₁.lastAddress alignN sizeN.toNat) sizeN.toNat true)),
      (Iris.Std.PartialMap.union (rangeMap
        (freshBase σ₁.lastAddress alignN sizeN.toNat)
        (List.replicate sizeN.toNat undefByte)) mb),
      (Iris.Std.PartialMap.insert mk 0
        ⟨freshBase σ₁.lastAddress alignN sizeN.toNat, σ₁.nextAllocId + 1⟩)
    isplitr [Hmi Hbi Hki HBa Hc]
    · ipureintro
      exact HG.alloc pref alignN sizeN Hgetc hnz
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    isplitl [Hki]
    · iexact Hki
    · -- the coupling inequality at the advanced cursor
      iapply budgetInterp_intro _
        ⟨freshBase σ₁.lastAddress alignN sizeN.toNat, σ₁.nextAllocId + 1⟩ m
        (Iris.Std.get?_insert_eq rfl)
        (by
          show m ≤ headroom (freshBase σ₁.lastAddress alignN sizeN.toNat)
          have hc : regionCost alignN sizeN = sizeN.toNat + alignN.toNat.max 1 - 1 := rfl
          omega)
      isplitl [HBa]
      · iexact HBa
      · iexact Hc
  · ihave HBy : bytesOwn (freshBase σ₁.lastAddress alignN sizeN.toNat) (.own 1)
        (List.replicate sizeN.toNat undefByte) $$ [Hbnew]
    · iapply bigSepM_rangeMap $$ Hbnew
    iexists (SpikeVal.pure (Vobject (OVpointer (cellPtr σ₁.nextAllocId
        (freshBase σ₁.lastAddress alignN sizeN.toNat)))))
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 1⟩
    iexists σ₁.nextAllocId, (freshBase σ₁.lastAddress alignN sizeN.toNat)
    isplit
    · ipureintro; rfl
    isplitl [Hmnew HBy]
    · unfold regionOwn
      isplitl [Hmnew]
      · iexact Hmnew
      isplitl [HBy]
      · iexact HBy
      · ipureintro
        simp
    · ipureintro
      exact ⟨hbase_pos, Int.le_trans hbase_le hla64⟩

/-- THE FREE RULE (kill/free arc K3) — the classical `{p ↦ region}
    dispose(p) {emp}` for DYNAMIC storage, as an atomic step: the dynamic
    kill (`hdyn : is_dynamic kind = true`; `free(p)`, `Kill Dynamic0`) at
    the base of a whole live REGION consumes the region at FULL ownership —
    `regionOwn id a n (.own 1) bs`, whose liveness token is `metaOwn id
    (.own 1) (regionCell a n true)` — and delivers the BARE unit (cost 1)
    with, at most, the persistent DEAD region `deadRegion id a n` (a client
    may drop it: `wps_free_emp`/`wpt_free_emp`). ONE application of the
    real `CerbMem.killM` at `isDynamic = true` (`killM_success_dynamic`):
    the `cellPtr` shape and `MetaCoh` pass the null/function/other-
    provenance (UB179a), dead (UB179b) and out-of-bound (`Other`) arms as
    for the static kill, and the DYNAMIC check `!st.dynamicAddrs.contains
    alloc.base` (CerbMem.lean:1573 — UB179a when it fails) passes because
    the cell's `dynamic = true` is coupled to `a ∈ dynamicAddrs`
    (`MetaCoh.dynamic`, `regionOwn_facts`), crossed to the engine's Bool by
    `mem_contains_int`. "This allocation is dynamic" is read off the
    METADATA CELL the `alloc` rule minted, never off `dynamicAddrs` (K0
    audit N-1: the list is never cleaned, so it is not evidence). Ghost as
    `kill_atomic`: `metaHeap_update` flips `alive := false`, `metaOwn_persist`
    discards; the byte fragments are DROPPED (`killM` leaves the bytemap
    alone, addresses are never reused — `CohG.kill`). -/
theorem free_atomic [SpikeGS hlc GF] {M : MachineCtx}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (id a : Int) (n : Nat) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hdyn : is_dynamic kind = true) :
    AtomicStep M (killExpr loc ann kind (cellPtr id a)) ρ 1
      (regionOwn (GF := GF) id a n (.own 1) bs)
      (fun w => iprop(⌜w = SpikeVal.pure Vunit⌝ ∗ deadRegion id a n)) := by
  intro E₁ E₂ hE σ₁ ns obs nt
  unfold regionOwn
  iintro ⟨⟨Hm, -, -⟩, Hσ⟩
  icases (stateInterp_iff σ₁ ns obs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm id = some (regionCell a n true)⌝
      $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  have hrun : applyMemM (CerbMem.killM loc (is_dynamic kind) (cellPtr id a)) σ₁ =
      some ((), { σ₁ with deadAllocations := id :: σ₁.deadAllocations,
                          allocations := σ₁.allocations.erase id }) := by
    rw [hdyn]
    exact killM_success_dynamic σ₁ id (regionCell a n true) loc
      (HG.metas id _ Hgetm) rfl rfl
  iapply fupd_mask_intro hE
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.kill_canonical hrun, rfl, rfl⟩⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨σ'', hmem', hout⟩ := hstep.kill_inv
  rw [hrun] at hmem'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hmem')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hσ⟩ := hout
  subst hre hσ
  obtain rfl : ρ = rρ := hrρ.symm
  imod Hclose with -
  -- ghost: flip the region cell to dead, then discard it
  imod (metaHeap_update (regionCell a n false)) $$ [$Hmi $Hm] with ⟨Hmi, Hm⟩
  imod (metaOwn_persist id (.own 1) _) $$ Hm with Hm
  imodintro
  isplitl [Hmi Hbi Hki]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists (Iris.Std.PartialMap.insert mm id (regionCell a n false)), mb, mk
    isplitr [Hmi Hbi Hki]
    · ipureintro
      exact HG.kill id _ Hgetm rfl
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  · iexists (SpikeVal.pure Vunit)
    isplit
    · ipureintro
      exact ⟨rfl, rfl, Nat.le_refl 1⟩
    isplit
    · ipureintro; rfl
    · unfold deadRegion
      iexact Hm

/-! ## The raw-WP faces of the small axioms (corollaries) -/

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
  iapply wp_of_atomic (store_atomic loc ann ty pv cv mo mv bs ρ hmv hst) rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%fp, %hw, Hpt'⟩
    subst hw
    iexists fp
    isplit
    · ipureintro; rfl
    · iexact Hpt'

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
  iapply wp_of_atomic (load_atomic loc ann ty pv mo dq bs ρ htrap) rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%fp, %hw, Hpt'⟩
    subst hw
    iexists fp
    isplit
    · ipureintro; rfl
    · iexact Hpt'

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
