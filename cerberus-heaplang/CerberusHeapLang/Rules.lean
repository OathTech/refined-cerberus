/-
CerberusHeapLang.Rules — the base logic: the store/load small
axioms, sequencing, frame, consequence, and the first derived
exhibit.

The contents:
- SMALL AXIOMS `wp_store` / `wp_load` — UB-EXCLUDING: the
  preconditions rule out every NDkilled (undefined-behavior/error)
  arm of the engine's storeM/loadM: the points-to supplies
  pointer-shape, liveness, bounds, writability, non-atomicity;
  `StorableAt` supplies the type-compat fact (the non-UB `Other`
  arm!); `cellLoadTrap = false` excludes the _Bool
  trap-representation arm.
- SEQ/BIND: `wp_sseq` — proved DIRECTLY by Löb induction over the
  factor structure of the Esseq frame (`Step.sseq_inv`), NOT
  through a `Language.Context`/wp_bind route: the direct proof
  (i) uses the fact that the betas fire only at cons-shaped env
  stacks (invisible to the pointwise `wp_mono` step of the bind
  route), and (ii) accommodates the jump disjunct as one more case
  (a Context instance for Esseq is falsified by jumps — Lang.lean).
  The annotation-commuting lemmas `wp_annot_reindex`/`wp_annot`
  handle the run-time annotation residue; `triple_seq` glues at the
  triple level.
- FRAME from Iris (`wp_frame_l/r`), stated at triple level.
- CONSEQUENCE + `wp_wand` (from Iris, stated at triple level).
- THE EXHIBIT: {x ↦ - ∗ y ↦ a} store(x,7) {x ↦ 7 ∗ y ↦ a}, derived
  by FRAME on the store small axiom.
- The anti-frame sanity check: a comment-fenced negative test at the
  end of this file (a failing example cannot be committed compiling;
  the stuck goal is recorded verbatim there).

ENV DISCIPLINE: the WP is over the runtime tuple `CoreRt`;
postconditions speak `CoreRVal` (value + final env). The action
small axioms return the env VERBATIM in their postconditions (the
request path never touches it); the triple layer is stated at the
frozen entry env `spikeEnv` (what the production driver parks for a
parameterless `main` — ProdEntry.prodThread).

LABEL DISCIPLINE (the tuple carries the per-procedure label map):
- LABEL-GENERAL (quantified `Q`): the small axioms `wp_store`/
  `wp_load` — local action steps never consult the label context;
  the jump disjuncts of their inversions are refuted by node shape.
- PINNED AT `spikeLbl` (the frozen EMPTY label map — the `spikeEnv`
  precedent): `wp_annot_reindex`/`wp_annot`/`wp_sseq` and the triple
  layer. The annotation-commuting lemmas are FALSE at a populated
  label map for the BASE WP (a jump discards the `Eannot` wrapper,
  so the two wraps land on the same continuation owing different
  posts — the lockstep argument breaks exactly at the jump); their
  label-general forms live at the wps stratum (Wps.lean), where the
  jump CLAUSE is post-independent and the transfer is formula
  identity. `wp_sseq` at a populated map has the analogous
  postcondition clash and is likewise a wps-stratum statement
  (`wps_seq`).
- There is deliberately NO env-invariance lemma at WP level — false
  once Esave/Erun rebind the env; the FragP-scoped
  `wp_env_invariant_frag` survives for the straight-line fragment,
  and `triple_seq` carries the `FragP e1` hypothesis it needs.

SOUNDNESS STATUS: every theorem here is proved against `Step`
(Step.lean), the hand-written mirror; Step is certified against the
engine's step_ctx/driver composite (Soundness.lean), and the
bundled `SpikeGS` ghost state is constructed inside the adequacy
proof (Adequacy.lean), so triples proved here acquire engine-level
meaning through SemTriple / semantic_triple_sound.

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
  modulo `CoreRVal.merge`. Proved by Löb induction.
- `wp_annot`: the actual commuting rule, by Löb induction; the
  merge case discharges through the reindexing lemma (that is the
  step the naive bind-style proof cannot take — recorded in the
  slice notes as the R-i finding). -/

/-- `wp_value'` at the fragment's value injection. -/
theorem wp_ofVal [SpikeGS hlc GF] {s : Stuckness} {E : CoPset} (v : CoreRVal)
    {Φ : CoreRVal → IProp GF} :
    Φ v ⊢ WP (ofValRt v) @ s; E {{ Φ }} := wp_value'

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

/-- Tuple-level value dichotomy corollaries (per-constructor simp
    discipline — the probe's match-reduction rule). -/
theorem toValRt_of_toVal {e : CoreExpr} {ρ : EnvStack} {M : MachineCtx}
    {w : SpikeVal} (h : toVal e = some w) :
    toValRt ⟨e, ρ, M⟩ = some ⟨w, ρ, M⟩ := by
  rw [toValRt_mk, h]; rfl

theorem toValRt_of_toVal_none {e : CoreExpr} {ρ : EnvStack} {M : MachineCtx}
    (h : toVal e = none) : toValRt ⟨e, ρ, M⟩ = none := by
  rw [toValRt_mk, h]; rfl

/-- Annotation reindexing (the lockstep argument): the two wraps make
    exactly corresponding steps — context steps of the shared body, or
    simultaneous merges — so WPs transfer along a `merge`-compatible
    postcondition translation. -/
theorem wp_annot_reindex [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (a : List annot) (dsA dsB : List dyn_annotation) (c : CoreExpr)
    (ρ : EnvStack) {Φ₁ Φ₂ : CoreRVal → IProp GF}
    (hΦ : ∀ v, Φ₁ (CoreRVal.merge dsA v) = Φ₂ (CoreRVal.merge dsB v)) :
    WP (⟨Expr a (Eannot dsA c), ρ, spikeCtx⟩ : CoreRt) @ s; E {{ Φ₁ }} ⊢
      WP (⟨Expr a (Eannot dsB c), ρ, spikeCtx⟩ : CoreRt) @ s; E {{ Φ₂ }} := by
  iloeb as IH generalizing %a %dsA %dsB %c %ρ %hΦ
  rcases toVal_annot_cases a c dsA with ⟨rfl, v, rfl, hA⟩ | hA
  · -- value on both sides
    have hB : toVal (Expr ([] : List annot) (Eannot dsB (ofVal (.pure v)))) =
        some (.annot dsB v) := rfl
    rw [wp_unfold.to_eq, wp_unfold.to_eq]
    simp only [language_toVal_eq, wp.pre, toValRt_of_toVal hA,
      toValRt_of_toVal hB]
    iintro H
    imod H with H
    imodintro
    have h' : Φ₁ (⟨SpikeVal.annot dsA v, ρ, spikeCtx⟩ : CoreRVal) =
        Φ₂ (⟨SpikeVal.annot dsB v, ρ, spikeCtx⟩ : CoreRVal) :=
      hΦ ⟨.pure v, ρ, spikeCtx⟩
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
    simp only [language_toVal_eq, wp.pre, toValRt_of_toVal_none hA,
      toValRt_of_toVal_none hB]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    icases H $$ Hσ with >⟨%hred, H⟩
    imodintro
    isplit
    · ipureintro
      cases s with
      | MaybeStuck => trivial
      | NotStuck =>
        obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
        rcases hstep.1.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs, _⟩ |
            ⟨a2, ds2, c'', rfl, _⟩ |
            ⟨l, pes, params, cont, vs, _, _, _, _, _, hl, _, _⟩
        · exact ⟨[], ⟨Expr a (Eannot dsB c'), ρ', spikeCtx⟩, _, [],
            ⟨Step.annot_ctx hnj hg hs, rfl, rfl⟩⟩
        · exact ⟨[], ⟨Expr (a ++ a2) (Eannot (dsB ++ ds2) c''), ρ, spikeCtx⟩,
            _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
        · rw [spikeCtx_labels, lookupLabel_empty] at hl; cases hl
    · iintro %e₂ %σ₂ %eₜ %HstepB Hcred
      obtain ⟨hstepB, hlbl, rfl⟩ := HstepB
      dsimp only [Nat.repeat]
      rcases hstepB.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs, hout⟩ |
          ⟨a2, ds2, c'', rfl, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, _, _, _, hl, _, _⟩
      · obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
        simp only at hlbl
        subst hlbl
        obtain ⟨he, hρ, hσ⟩ : e₂e = Expr a (Eannot dsB c') ∧ e₂ρ = ρ' ∧
            σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst he hρ hσ
        imod H $$ %(⟨Expr a (Eannot dsA c'), e₂ρ, spikeCtx⟩ : CoreRt) %_ %([])
          %⟨Step.annot_ctx hnj hg hs, rfl, rfl⟩ Hcred with H
        iintro !> !>
        imod H
        iintro !>
        iapply step_fupdN_wand $$ H
        iintro >⟨HSI, Hwp, Hefs⟩
        imodintro
        iframe HSI
        isplitl [Hwp]
        · iapply IH $$ %a %dsA %dsB %c' %e₂ρ %hΦ Hwp
        · iexact Hefs
      · obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
        simp only at hlbl
        subst hlbl
        obtain ⟨he, hρ, hσ⟩ : e₂e = Expr (a ++ a2) (Eannot (dsB ++ ds2) c'') ∧
            e₂ρ = ρ ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq] using hout
        subst he
        obtain rfl : ρ = e₂ρ := hρ.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod H $$ %(⟨Expr (a ++ a2) (Eannot (dsA ++ ds2) c''), ρ,
            spikeCtx⟩ : CoreRt) %_
          %([]) %⟨Step.annot_merge, rfl, rfl⟩ Hcred with H
        iintro !> !>
        imod H
        iintro !>
        iapply step_fupdN_wand $$ H
        iintro >⟨HSI, Hwp, Hefs⟩
        imodintro
        iframe HSI
        isplitl [Hwp]
        · iapply IH $$ %(a ++ a2) %(dsA ++ ds2) %(dsB ++ ds2) %c'' %ρ
            %(fun v => by
              rw [← CoreRVal.merge_merge, ← CoreRVal.merge_merge]
              exact hΦ (CoreRVal.merge ds2 v)) Hwp
        · iexact Hefs
      · rw [spikeCtx_labels, lookupLabel_empty] at hl; cases hl

/-- WP commutes with the run-time dyn-annotation wrapper: to verify
    `{A}e`, verify `e` with the postcondition translated along
    `CoreRVal.merge`. This is what makes the LETS-ANNOT continuation
    (`lets _ = {A}v in E2 --> {A}E2`) usable compositionally. Proved
    by Löb; the annot-rooted body case takes the ANNOTS merge step and
    exits through `wp_annot_reindex`. -/
theorem wp_annot [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (ds : List dyn_annotation) (e : CoreExpr) (ρ : EnvStack)
    {Φ : CoreRVal → IProp GF} :
    WP (⟨e, ρ, spikeCtx⟩ : CoreRt) @ s; E {{ v, Φ (CoreRVal.merge ds v) }} ⊢
      WP (⟨Expr ([] : List annot) (Eannot ds e), ρ, spikeCtx⟩ : CoreRt) @ s; E
        {{ Φ }} := by
  iloeb as IH generalizing %ds %e %ρ
  cases hv : toVal e with
  | some w =>
    have he := ofVal_of_toVal hv
    subst he
    cases w with
    | pure v =>
      -- the wrap is itself a value: (.annot ds v, ρ)
      rw [wp_unfold.to_eq, wp_unfold.to_eq]
      simp only [language_toVal_eq, wp.pre, toValRt_of_toVal (toVal_ofVal _),
        toValRt_of_toVal
          (show toVal (Expr ([] : List annot) (Eannot ds (ofVal (.pure v)))) =
            some (.annot ds v) from rfl)]
      iintro H
      imod H with H
      imodintro
      rw [show (⟨SpikeVal.annot ds v, ρ, spikeCtx⟩ : CoreRVal) =
        CoreRVal.merge ds ⟨SpikeVal.pure v, ρ, spikeCtx⟩ from rfl]
      iexact H
    | annot ds2 v =>
      -- double annot: one deterministic tau (ANNOTS merge) to a value
      rw [show (⟨ofVal (SpikeVal.annot ds2 v), ρ, spikeCtx⟩ : CoreRt) =
        ofValRt ⟨SpikeVal.annot ds2 v, ρ, spikeCtx⟩ from rfl]
      iintro H
      iapply wp_lift_pure_det_step_no_fork E
        (e₂ := (⟨ofVal (SpikeVal.annot (ds ++ ds2) v), ρ, spikeCtx⟩ : CoreRt))
        ?safe ?det
      case safe =>
        intro σ
        cases s
        · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
        · rfl
      case det =>
        intro obs σ₁ e₂' σ₂ eₜ h
        exact annot_merge_det h
      ihave H := wp_value_fupd'.mp $$ H
      imod H with H
      iapply step_fupd_intro Std.LawfulSet.subset_refl
      inext
      iintro -
      rw [show (⟨ofVal (SpikeVal.annot (ds ++ ds2) v), ρ, spikeCtx⟩ : CoreRt) =
        ofValRt ⟨SpikeVal.annot (ds ++ ds2) v, ρ, spikeCtx⟩ from rfl]
      iapply wp_ofVal
      rw [show (⟨SpikeVal.annot (ds ++ ds2) v, ρ, spikeCtx⟩ : CoreRVal) =
        CoreRVal.merge ds ⟨SpikeVal.annot ds2 v, ρ, spikeCtx⟩ from rfl]
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
        (e₂ := (⟨Expr ([] ++ a2) (Eannot (ds ++ ds2) c), ρ, spikeCtx⟩ : CoreRt))
        ?safe2 ?det2
      case safe2 =>
        intro σ
        cases s
        · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
        · rfl
      case det2 =>
        intro obs σ₁ e₂' σ₂ eₜ h
        exact annot_merge_det h
      iapply step_fupd_intro Std.LawfulSet.subset_refl
      inext
      iintro -
      simp only [List.nil_append]
      iapply (wp_annot_reindex (Φ₁ := fun w => iprop(Φ (CoreRVal.merge ds w)))
        a2 ds2 (ds ++ ds2) c ρ
        (fun v => congrArg Φ (CoreRVal.merge_merge ds ds2 v))) $$ H
    · -- plain body: reduction in the Cannot frame, Löb
      have hr' : annotRooted e = false := by simpa using hr
      have hwrap : toVal (Expr ([] : List annot) (Eannot ds e)) = none :=
        toVal_annot_none hv
      rw [wp_unfold.to_eq, wp_unfold.to_eq]
      simp only [language_toVal_eq, wp.pre, toValRt_of_toVal_none hv,
        toValRt_of_toVal_none hwrap]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      icases H $$ Hσ with >⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        cases s with
        | MaybeStuck => trivial
        | NotStuck =>
          obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
          exact ⟨[], ⟨Expr ([] : List annot) (Eannot ds e'.e), e'.ρ, spikeCtx⟩,
            _, [],
            ⟨Step.annot_ctx (Step.jumpRedex?_none_of_spikeCtx hstep.1) hr'
              hstep.1, rfl, rfl⟩⟩
      · iintro %e₂ %σ₂ %eₜ %HstepW Hcred
        obtain ⟨hstepW, hlbl, rfl⟩ := HstepW
        dsimp only [Nat.repeat]
        rcases hstepW.annot_inv with ⟨hg, hnj, e'', ρ', σ'', hs, hout⟩ |
            ⟨a2, ds2, c, heq, hout⟩ |
            ⟨l, pes, params, cont, vs, _, _, _, _, _, hl, _, _⟩
        · obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
          simp only at hlbl
          subst hlbl
          obtain ⟨he, hρ, hσ⟩ : e₂e = Expr ([] : List annot) (Eannot ds e'') ∧
              e₂ρ = ρ' ∧ σ₂ = σ'' := by
            simpa [Prod.mk.injEq] using hout
          subst he hρ hσ
          imod H $$ %(⟨e'', e₂ρ, spikeCtx⟩ : CoreRt) %_ %([])
            %⟨hs, rfl, rfl⟩ Hcred with H
          iintro !> !>
          imod H
          iintro !>
          iapply step_fupdN_wand $$ H
          iintro >⟨HSI, Hwp, Hefs⟩
          imodintro
          iframe HSI
          isplitl [Hwp]
          · iapply IH $$ %ds %e'' %e₂ρ Hwp
          · iexact Hefs
        · exact absurd heq (by
            intro heq
            rw [heq] at hr'
            simp [annotRooted] at hr')
        · rw [spikeCtx_labels, lookupLabel_empty] at hl; cases hl

/-! ## Sequencing (the jump-ready factor route — header note) -/

/-- How a bound value's annotations flow into the continuation's
    value: `lets _ = v in e2` leaves e2's value alone; `lets _ = {A}v
    in e2` prefixes A (LETS-ANNOT + the eventual ANNOTS merge). The
    env is the continuation value's (annotation flow never touches
    it). -/
def mergeInto : CoreRVal → CoreRVal → CoreRVal
  | ⟨.pure _, _, _⟩, w => w
  | ⟨.annot ds _, _, _⟩, w => CoreRVal.merge ds w

/-- The value-level sequencing rule for real Esseq (wildcard pattern).

    PROOF ROUTE (phase-1 restratification): direct Löb induction over
    the factor structure of the Esseq frame (`Step.sseq_inv`) — the
    base-WP face of the probe's jump-aware sequencing argument
    (probe report §3, minus the jump case, which S3 adds as one more
    disjunct). Not via `wp_bind`: the bind route's pointwise
    `wp_mono` step cannot see that e1's delivered values carry a
    cons-shaped env (phase-1 env invariance), which the beta step
    requires. The env stack is quantified in cons shape — the beta
    fires only there (the empty-env panic channel is absence of a
    step, Step.lean header note 1). -/
theorem wp_sseq [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    {Φ : CoreRVal → IProp GF} :
    WP (⟨e1, ev0 :: evs, spikeCtx⟩ : CoreRt) @ s; E
      {{ v, ▷ WP (⟨e2, v.ρ, spikeCtx⟩ : CoreRt) @ s; E
        {{ w, Φ (mergeInto v w) }} }} ⊢
      WP (⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2),
          ev0 :: evs, spikeCtx⟩ : CoreRt) @ s; E {{ Φ }} := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases hv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal hv
    subst he
    cases w with
    | pure v =>
      -- one deterministic beta step (LETS-PURE) into e2
      rw [show (⟨ofVal (SpikeVal.pure v), ev0 :: evs, spikeCtx⟩ : CoreRt) =
        ofValRt ⟨SpikeVal.pure v, ev0 :: evs, spikeCtx⟩ from rfl]
      iintro H
      iapply wp_lift_pure_det_step_no_fork E
        (e₂ := (⟨e2, ev0 :: evs, spikeCtx⟩ : CoreRt)) ?safeP ?detP
      case safeP =>
        intro σ
        cases s
        · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_pure, rfl, rfl⟩⟩
        · rfl
      case detP =>
        intro obs σ₁ e₂' σ₂ eₜ h
        exact sseq_pure_det h
      ihave H := wp_value_fupd'.mp $$ H
      imod H with H
      iapply step_fupd_intro Std.LawfulSet.subset_refl
      inext
      iintro -
      iapply (wp_mono (fun w => .rfl) :
        WP (⟨e2, ev0 :: evs, spikeCtx⟩ : CoreRt) @ s; E
          {{ w, Φ (mergeInto ⟨SpikeVal.pure v, ev0 :: evs, spikeCtx⟩ w) }} ⊢
          WP (⟨e2, ev0 :: evs, spikeCtx⟩ : CoreRt) @ s; E {{ Φ }}) $$ H
    | annot ds v =>
      -- one deterministic beta step (LETS-ANNOT) into {ds}e2, then
      -- the annotation-commuting rule
      rw [show (⟨ofVal (SpikeVal.annot ds v), ev0 :: evs, spikeCtx⟩ : CoreRt) =
        ofValRt ⟨SpikeVal.annot ds v, ev0 :: evs, spikeCtx⟩ from rfl]
      iintro H
      iapply wp_lift_pure_det_step_no_fork E
        (e₂ := (⟨Expr ([] : List annot) (Eannot ds e2), ev0 :: evs,
          spikeCtx⟩ : CoreRt))
        ?safeA ?detA
      case safeA =>
        intro σ
        cases s
        · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_annot, rfl, rfl⟩⟩
        · rfl
      case detA =>
        intro obs σ₁ e₂' σ₂ eₜ h
        exact sseq_annot_det h
      ihave H := wp_value_fupd'.mp $$ H
      imod H with H
      iapply step_fupd_intro Std.LawfulSet.subset_refl
      inext
      iintro -
      ihave H := (wp_mono (fun w => .rfl) :
        WP (⟨e2, ev0 :: evs, spikeCtx⟩ : CoreRt) @ s; E
          {{ w, Φ (mergeInto ⟨SpikeVal.annot ds v, ev0 :: evs, spikeCtx⟩ w) }} ⊢
          WP (⟨e2, ev0 :: evs, spikeCtx⟩ : CoreRt) @ s; E
            {{ w, Φ (CoreRVal.merge ds w) }}) $$ H
      iapply wp_annot ds e2 (ev0 :: evs) $$ H
  | none =>
    -- e1 steps: factor (`sseq_inv`, betas excluded by hv, the jump
    -- disjunct by the frozen empty label map) + lift
    -- (`Step.sseq_ctx`) + Löb; env cons-shape rides the Löb.
    have hwrap : toVal (Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
        e1 e2)) = none := rfl
    rw [wp_unfold.to_eq, wp_unfold.to_eq]
    simp only [language_toVal_eq, wp.pre, toValRt_of_toVal_none hv,
      toValRt_of_toVal_none hwrap]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    icases H $$ Hσ with >⟨%hred, H⟩
    imodintro
    isplit
    · ipureintro
      cases s with
      | MaybeStuck => trivial
      | NotStuck =>
        obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
        exact ⟨[], ⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
            e'.e e2), e'.ρ, spikeCtx⟩, _, [],
          ⟨Step.sseq_ctx (Step.jumpRedex?_none_of_spikeCtx hstep.1)
            hstep.1, rfl, rfl⟩⟩
    · iintro %e₂ %σ₂ %eₜ %HstepW Hcred
      obtain ⟨hstepW, hlbl, rfl⟩ := HstepW
      dsimp only [Nat.repeat]
      rcases hstepW.sseq_inv with ⟨e1', ρ', σ'', hnj, hs, hout⟩ |
          ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, _, _, hl, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩
      · -- S3: env invariance is gone; the step keeps the stack
        -- CONS-SHAPED (`Step.env_cons`) and the Löb IH re-enters at
        -- the new head frame.
        obtain ⟨ev0', rfl⟩ := Step.env_cons hs
        obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
        simp only at hlbl
        subst hlbl
        obtain ⟨he, hρ, hσ⟩ : e₂e = Expr a (Esseq (Pattern pa
              (CaseBase (none, bty))) e1' e2) ∧ e₂ρ = ev0' :: evs ∧
            σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst he hρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, spikeCtx⟩ : CoreRt) %_ %([])
          %⟨hs, rfl, rfl⟩ Hcred with H
        iintro !> !>
        imod H
        iintro !>
        iapply step_fupdN_wand $$ H
        iintro >⟨HSI, Hwp, Hefs⟩
        imodintro
        iframe HSI
        isplitl [Hwp]
        · iapply IH $$ %e1' %ev0' %evs Hwp
        · iexact Hefs
      · rw [he1, toVal_ofVal] at hv; cases hv
      · rw [he1, toVal_ofVal] at hv; cases hv
      · rw [spikeCtx_labels, lookupLabel_empty] at hl; cases hl
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim

/-! ## Triples

The triple is the standard Iris-WP definition: `P` entails the
weakest precondition at NotStuck (UB-exclusion IS the NotStuck
obligation, R4) with the full mask ⊤ — stated at the frozen entry
env `spikeEnv` (env-general triples arrive with binding patterns,
phase 2). -/

def triple [SpikeGS hlc GF] (P : IProp GF) (e : CoreExpr)
    (Ψ : CoreRVal → IProp GF) : Prop :=
  P ⊢ WP (⟨e, spikeEnv, spikeCtx⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ Ψ }}

/-- FRAME (the acceptance item, stated at triple level; the WP-level
    rule is Iris's `wp_frame_r`/`wp_frame_l`). -/
theorem triple_frame [SpikeGS hlc GF] {P R : IProp GF} {e : CoreExpr}
    {Ψ : CoreRVal → IProp GF} (h : triple P e Ψ) :
    triple iprop(P ∗ R) e (fun v => iprop(Ψ v ∗ R)) :=
  (BI.sep_mono h .rfl).trans (wp_frame_r.trans (wp_mono fun _ => BI.sep_comm.1))

/-- CONSEQUENCE (from BI entailment). -/
theorem triple_conseq [SpikeGS hlc GF] {P' P : IProp GF} {e : CoreExpr}
    {Ψ Ψ' : CoreRVal → IProp GF} (hP : P' ⊢ P) (hΨ : ∀ v, Ψ v ⊢ Ψ' v)
    (h : triple P e Ψ) : triple P' e Ψ' :=
  hP.trans (h.trans (wp_mono hΨ))

/-- wp_wand, re-exported at the spike's language (Iris's `wp_wand`). -/
theorem spike_wp_wand [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    {e : CoreRt} {Φ Ψ : CoreRVal → IProp GF} :
    WP e @ s; E {{ Φ }} ⊢ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }} :=
  wp_wand

/-- The env-write-free sub-grammar: the phase-1 expression shapes
    (pure leaves, actions, WILDCARD strong sequencing, the Eannot
    residue), with operand/location side conditions dropped — no
    rule that fires on these shapes writes the environment
    (`EnvStable.step_env`), and none of the env-writing constructs
    (Esave/Erun binding, Ecase substitution targets) occur in it.
    This is the S3 scope of the retired unconditional env invariance
    at the Rules stratum (`FragP` bundles action-canonicity and
    non-library-location facts irrelevant to the env, and the frozen
    exhibits quantify locations — so the weaker cone is the honest
    hypothesis). -/
inductive EnvStable : CoreExpr → Prop where
  | pure (a : List annot) (pe : generic_pexpr Unit sym) :
      EnvStable (Expr a (Epure pe))
  | action (a : List annot)
      (p : generic_paction core_run_annotation Unit sym) :
      EnvStable (Expr a (Eaction p))
  | sseq {a pa : List annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      EnvStable e1 → EnvStable e2 →
      EnvStable (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
  | annot {a : List annot} {ds : List dyn_annotation} {b : CoreExpr} :
      EnvStable b → EnvStable (Expr a (Eannot ds b))

theorem EnvStable.jumpRedex?_none {e : CoreExpr} (hf : EnvStable e) :
    jumpRedex? e = none := by
  induction hf with
  | pure a pe => rfl
  | action a p => rfl
  | sseq hf1 hf2 ih1 ih2 => rw [jumpRedex?_sseq]; exact ih1
  | annot hfb ihb =>
    rw [jumpRedex?_annot]
    split
    · rfl
    · exact ihb

/-- Closure + env invariance on the env-write-free cone. -/
theorem EnvStable.step_env {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : EnvStable e) (hs : Step M (e, ρ, σ) (e', ρ', σ')) :
    EnvStable e' ∧ ρ' = ρ := by
  induction hf generalizing e' ρ' σ' with
  | pure a pe =>
    cases hs with
    | run hj hl hvs => simp at hj
    | pure_eval hnv hv => exact ⟨.pure _ _, rfl⟩
  | action a p =>
    cases hs with
    | store h1 h2 h3 hmv hmem => exact ⟨.annot (.pure _ _), rfl⟩
    | load h1 h2 hmem => exact ⟨.annot (.pure _ _), rfl⟩
    | create h1 h2 hmem => exact ⟨.pure _ _, rfl⟩
    | run hj hl hvs => simp at hj
    | load_eval hnv2 hv2 => exact ⟨.action _ _, rfl⟩
    | store_eval hnv2 hnv3 hv2 hv3 => exact ⟨.action _ _, rfl⟩
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, _, _, hout⟩ | ⟨_, _, ds', v, _, _, _, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, _⟩
    · obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2
      obtain ⟨hf1', hρ⟩ := ih1 hstep
      exact ⟨.sseq hf1' hf2, hρ⟩
    · obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨hf2, h2⟩
    · obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨.annot hf2, h2⟩
    · rw [hf1.jumpRedex?_none] at hj
      cases hj
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, _, hj, _, _, _, _⟩
    · obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1 h2
      obtain ⟨hfb', hρ⟩ := ihb hstep
      exact ⟨.annot hfb', hρ⟩
    · subst hb
      obtain ⟨h1, h2, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      cases hfb with
      | annot hfc => exact ⟨.annot hfc, h2⟩
    · rw [hfb.jumpRedex?_none] at hj
      cases hj

/-- ENV INVARIANCE, INTERNALIZED — S3 SURVIVOR FORM. The
    unconditional `wp_env_invariant` is RETIRED as pre-declared
    (phase-1 notes §2 item 6): `Esave`/`Erun` rebind the env, so "no
    rule writes the env" is false of the extended relation. On the
    env-write-free cone it survives verbatim: a WP launched at env
    `ρ` on an `EnvStable` subject may strengthen its postcondition
    with `⌜final env = ρ⌝` (`EnvStable.step_env` transported through
    the Löb induction). Needed where a postcondition FORGETS the
    delivered value (e.g. `triple_seq`'s assertion form) but the
    sequencing premise still owes the continuation's env. -/
theorem wp_env_invariant_stable [SpikeGS hlc GF] {s : Stuckness} {E : CoPset}
    (e : CoreExpr) (ρ : EnvStack) (hf : EnvStable e)
    {Φ : CoreRVal → IProp GF} :
    WP (⟨e, ρ, spikeCtx⟩ : CoreRt) @ s; E {{ Φ }} ⊢
      WP (⟨e, ρ, spikeCtx⟩ : CoreRt) @ s; E {{ v, ⌜v.ρ = ρ⌝ ∗ Φ v }} := by
  iloeb as IH generalizing %e %ρ %hf
  cases hv : toVal e with
  | some w =>
    rw [wp_unfold.to_eq, wp_unfold.to_eq]
    simp only [language_toVal_eq, wp.pre, toValRt_of_toVal hv]
    iintro H
    imod H with H
    imodintro
    isplit
    · ipureintro; trivial
    · iexact H
  | none =>
    rw [wp_unfold.to_eq, wp_unfold.to_eq]
    simp only [language_toVal_eq, wp.pre, toValRt_of_toVal_none hv]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨$, H⟩
    imodintro
    iintro %e₂ %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    dsimp only [Nat.repeat]
    obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
    simp only at hlbl
    subst hlbl
    obtain ⟨hf', hρ⟩ := EnvStable.step_env hf hs
    have hρ' : ρ = e₂ρ := hρ.symm
    subst hρ'
    imod H $$ %(⟨e₂e, ρ, spikeCtx⟩ : CoreRt) %σ₂ %([] : List CoreRt)
      %⟨hs, rfl, rfl⟩ Hcred with H
    iintro !> !>
    imod H
    iintro !>
    iapply step_fupdN_wand $$ H
    iintro >⟨HSI, Hwp, Hefs⟩
    imodintro
    iframe HSI
    isplitl [Hwp]
    · iapply IH $$ %e₂e %ρ %hf' Hwp
    · iexact Hefs

/-- SEQ: {P} e1 {Q} and {Q} e2 {R} give {P} e1;e2 {R} (assertion
    postconditions — the wildcard-binding form the fragment needs;
    the value-binding generalization is `wp_sseq`). The delivered
    env of e1 is pinned to `spikeEnv` by `wp_env_invariant_stable`
    before the pointwise continuation is supplied.
    S3 FINDING (forced by the pre-declared `wp_env_invariant`
    retirement): gains the `EnvStable e1` hypothesis — for an
    arbitrary jump-capable e1 the delivered env is not the entry
    env, and h2's triple (pinned at `spikeEnv`) says nothing about
    the continuation at the delivered env. Every existing user
    passes an env-write-free subject. -/
theorem triple_seq [SpikeGS hlc GF] {P Q R : IProp GF}
    {bty : core_base_type} {e1 e2 : CoreExpr} (hf : EnvStable e1)
    (h1 : triple P e1 (fun _ => Q)) (h2 : triple Q e2 (fun _ => R)) :
    triple P (sseqExpr bty e1 e2) (fun _ => R) := by
  refine h1.trans ((wp_env_invariant_stable e1 spikeEnv hf).trans
    (.trans ?_ (wp_sseq [] [] bty e1 e2 fmapEmpty [])))
  apply wp_mono
  intro v
  iintro ⟨%hρ, HQ⟩
  rw [hρ]
  ihave HW := h2.trans BI.later_intro $$ HQ
  iexact HW

/-! ## The exhibit -/

/-- signed int (the recon's probe type). -/
def intTy : ctype := Ctype [] (.Basic (.Integer (.Signed .Int_)))

-- Phase 2 (F-04): the int-specific interior load engine seam
-- (`loadM_interior_int`) is RETIRED — the generic typed-subrange seam
-- `loadM_at` (Heap.lean) covers every accessed type and offset.

/-- The Core value `Specified(7) : loaded integer`. -/
def sevenVal : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval 7)))

/-- Its memory value. -/
def sevenMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 7)

/-- Its byte image (the engine's own serialization). -/
def sevenBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] sevenMval).2

theorem seven_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) sevenVal =
      some sevenMval := rfl

theorem seven_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy sevenMval :=
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
      iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy bs ∗ pointsToCell spikeCtx.tagDefs y (.own 1) ty' bs')
      (storeExpr loc ann intTy x sevenVal mo)
      (fun _ => iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (sevenBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) ty' bs')) := by
  -- 1. the small axiom, instantiated at 7/int
  have hax : triple (GF := GF) (pointsToCell spikeCtx.tagDefs x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun w => iprop(∃ fp,
        ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, spikeEnv, spikeCtx⟩ : CoreRVal)⌝ ∗
        pointsToCell spikeCtx.tagDefs x (.own 1) intTy (sevenBytes spikeCtx.tagDefs))) :=
    wp_store loc ann intTy x sevenVal mo sevenMval bs spikeEnv seven_encodes
      (seven_storable _)
  -- 2. FRAME with y's cell
  have hfr := triple_frame (R := pointsToCell spikeCtx.tagDefs y (.own 1) ty' bs') hax
  -- 3. CONSEQUENCE: drop the return-value information
  refine triple_conseq .rfl ?_ hfr
  intro v
  iintro ⟨⟨%fp, %hw, Hx⟩, Hy⟩
  iframe

/-! ## The anti-frame sanity check (negative test — locality is real)

A failing example cannot be committed compiling, so the test is
recorded as its verbatim transcript (re-runnable; also in the slice
notes; env-plumbed 2026-08-31 at the S1 migration — the stuck goal is
unchanged in substance: exactly the missing y-cell). Claiming y's
cell in the postcondition WITHOUT owning it in the precondition
leaves the derivation stuck on exactly the missing cell, with an
EMPTY spatial context after the x-cell is consumed:

```
example {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (x y : CerbMem.PointerValue) (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) :
    triple (GF := GF) (pointsToCell x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun _ => iprop(pointsToCell x (.own 1) intTy (sevenBytes spikeCtx.tagDefs) ∗
        pointsToCell y (.own 1) ty' bs')) := by
  have hax : triple (GF := GF) (pointsToCell x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun w => iprop(∃ fp,
        ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, spikeEnv, spikeCtx⟩ : CoreRVal)⌝ ∗
        pointsToCell x (.own 1) intTy (sevenBytes spikeCtx.tagDefs))) :=
    wp_store loc ann intTy x sevenVal mo sevenMval bs spikeEnv seven_encodes
      (seven_storable _)
  refine triple_conseq .rfl ?_ hax
  intro v
  iintro ⟨%fp, %hw, Hx⟩
  iframe
```

Transcript (verbatim, `lake env lean` on the above, 2026-08-30, tuple
form re-run 2026-08-31 — the final stuck goal both times):

```
error: unsolved goals
⊢
  ⊢ y ↦c ty' ; bs'
```
-/

/-! ## EXHIBIT C ([USER 2026-08-30]): disjoint sequential stores

`lets _ = store(x,5) in store(y,6)` on two distinct cells gives
NON-CONFLICTING updates:

    {x ↦ - ∗ y ↦ -} store(x,5); store(y,6) {x ↦ 5 ∗ y ↦ 6}

The PROOF DISCIPLINE is the exhibit: each leg is the store small
axiom FRAMED with the other cell (triple_frame + consequence), and
the two legs are glued by SEQ (triple_seq, itself wp_sseq over the
real Esseq). Nothing below unfolds Step/storeM/state_interp — the
derivation is exactly the compositional surface. -/

/-- The Core value `Specified(5)`, its memory value, its byte image. -/
def fiveVal : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval 5)))

def fiveMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 5)

def fiveBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] fiveMval).2

theorem five_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) fiveVal =
      some fiveMval := rfl

theorem five_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy fiveMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The Core value `Specified(6)`, its memory value, its byte image. -/
def sixVal : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval 6)))

def sixMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 6)

def sixBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] sixMval).2

theorem six_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) sixVal =
      some sixMval := rfl

theorem six_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy sixMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- EXHIBIT C at the Iris triple level. Derivation (the point):
    1. wp_store on x, FRAMED with y's cell (+ consequence to drop
       the return-value annotation);
    2. wp_store on y, FRAMED with x's now-updated cell (+ the same);
    3. glued by triple_seq (= wp_sseq over the fragment's Esseq).
    x and y are arbitrary distinct-cell pointers — distinctness is
    never stated: the ∗ in the precondition carries it. -/
theorem exhibitC_triple [SpikeGS hlc GF] (x y : CerbMem.PointerValue)
    (loc loc' : CerbLocation.Loc) (ann ann' : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type)
    (bsx bsy : List CerbMem.AbsByte) :
    triple (GF := GF)
      iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy bsx ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)
      (sseqExpr bty (storeExpr loc ann intTy x fiveVal mo)
        (storeExpr loc' ann' intTy y sixVal mo'))
      (fun _ => iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy (sixBytes spikeCtx.tagDefs))) := by
  -- leg 1: the store small axiom on x, FRAMED with y's cell
  have hx : triple (GF := GF) (pointsToCell spikeCtx.tagDefs x (.own 1) intTy bsx)
      (storeExpr loc ann intTy x fiveVal mo)
      (fun w => iprop(∃ fp,
        ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, spikeEnv, spikeCtx⟩ : CoreRVal)⌝ ∗
        pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs))) :=
    wp_store loc ann intTy x fiveVal mo fiveMval bsx spikeEnv five_encodes
      (five_storable _)
  have h1 : triple (GF := GF)
      iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy bsx ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)
      (storeExpr loc ann intTy x fiveVal mo)
      (fun _ => iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)) := by
    refine triple_conseq .rfl ?_
      (triple_frame (R := pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy) hx)
    intro v
    iintro ⟨⟨%fp, %hw, Hx⟩, Hy⟩
    iframe
  -- leg 2: the store small axiom on y, FRAMED with x's updated cell
  have hy : triple (GF := GF) (pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)
      (storeExpr loc' ann' intTy y sixVal mo')
      (fun w => iprop(∃ fp,
        ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, spikeEnv, spikeCtx⟩ : CoreRVal)⌝ ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy (sixBytes spikeCtx.tagDefs))) :=
    wp_store loc' ann' intTy y sixVal mo' sixMval bsy spikeEnv six_encodes
      (six_storable _)
  have h2 : triple (GF := GF)
      iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)
      (storeExpr loc' ann' intTy y sixVal mo')
      (fun _ => iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy (sixBytes spikeCtx.tagDefs))) := by
    refine triple_conseq BI.sep_comm.1 ?_
      (triple_frame (R := pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs)) hy)
    intro v
    iintro ⟨⟨%fp, %hw, Hy⟩, Hx⟩
    iframe
  -- glue: SEQ
  exact triple_seq (.action _ _) h1 h2

end CerberusHeapLang
