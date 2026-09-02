/-
CerberusHeapLang.ProdExhibit — exhibit A re-exported at the
PRODUCTION ENTRY: the unconditional demonstration that the whole
export chain reaches the shipped pipeline.

The program is fully self-contained — it creates its own cell with
the engine's `create`, BINDS the fresh pointer (alloc arc P2: the
created pointer flows through the program's own `lets p = ...`
binder — the real-Core malloc shape; the P2 pointer-flow design
record is in docs/2026-09-01_p2-notes.md), stores the constant 7
through the bound pointer and loads it back:

  main() = lets p = create(4, int) in
           lets _ = store(int, p, 7) in load(int, p)

(QA-1/H-1: the store's operands are a SYMBOL pointer and a LITERAL
value — the mixed shape the engine's ACTION_EVAL arm takes; the
pre-QA-1 form bound the constant first, `lets v = 7 in store(int, p,
v)`, because the mirrored arm then required two non-value operands.)

THE THEOREM (`exhibitA_prod`): `runND` of the SHIPPED driver on the
synthetic one-procedure file wrapping this program, from
`initial_driver_state`, is EXACTLY ONE Active execution; its
driver_result value is `Specified(7)` and the final memory holds 7's
byte image at the program's own fresh cell (existential allocation
id/address — the logic binds the pointer, the engine picks it).

PROOF CLASSIFICATION (alloc arc P2, charter step 3 — the R-02
conversion): ONE whole-program LOGICAL total theorem
(`progAProd_wpt`: create through the PUBLIC `wpt_create` from
`allocCap [⟨4, intTy⟩]`, store/load through the generic heap rules,
at derived budget 10) + the GENERIC adequacy/driver collapse
(`wpt_driver_done_alloc` → `prod_run_eqJ`). The former operational
create prefix (`prodA_pre`) and six-round termination trace
(`prodA_terminates`) are DELETED — no `Step.*`, `engineSteps_*`,
`driveJ_step`, `driverDone_step` in any proof of this module.

The former concrete cold-start scaffolding (`pxAddr`/`pxPtr`/`σcP`/
`cellXP`/`mAP`/`bigSep_ptx_P`/`create_applies`) is DELETED (alloc
arc P2 step 6): its last consumers were the loop exports' handwritten
operational prefixes, replaced by whole-program logic proofs in
ProdLoopExhibit.
-/
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.Exhibit
import CerberusHeapLang.AllocExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open scoped Iris.Std.PartialMap

variable {GF : BundledGFunctors}

/-! ## The program (alloc arc P2 shape: the created pointer is
BOUND; QA-1/H-1: the constant is stored directly) -/

/-- The bound fresh-pointer symbol. -/
def pASym : sym := Symbol "" 511 SD_None

/-- The full self-contained program:
    `lets p = create(4, int) in lets _ = store(int, p, 7) in load(int, p)`. -/
def progAProd : CoreExpr :=
  Expr [] (Esseq (symPat [] pASym BTy_unit)
    (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy
      (PrefOther "spike-x"))
    (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
      (storeOpRedex loc0 empty_annotation intTy
        (Pexpr [] () (PEsym pASym)) (Pexpr [] () (PEval sevenVal)) NA)
      (loadOpRedex loc0 empty_annotation intTy
        (Pexpr [] () (PEsym pASym)) NA))))

/-- Cone membership. -/
theorem progAProd_frag : Frag progAProd :=
  .sseq_sym (.create loc0_lib)
    (.sseq
      (.store_op loc0_lib rfl (.sym [] pASym) (.val [] sevenVal)
        (by rw [show peDepth (Pexpr ([] : List annot) ()
            (PEsym pASym)) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)
        (peDepth_val_le _ _))
      (.load_op loc0_lib rfl (.sym [] pASym)
        (by rw [show peDepth (Pexpr ([] : List annot) ()
            (PEsym pASym)) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)))

/-! ## The mixed operand shapes of `store` (QA-1/H-1)

The engine's ACTION_EVAL arm for `store` fires whenever the operand
triple is NOT all values; before QA-1 the mirror and the rules covered
only the two-non-value sub-case. The two mixed shapes, at the mirror
and at the rules (instances of `Step.store_eval` / `wps_store_eval` /
`wpt_store_eval`, the "not all values" premise by `rfl`): -/

/-- `store(ty, x, v)` — SYMBOL pointer, LITERAL value — steps. -/
theorem store_sym_lit_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {x : sym} {cv : value}
    {mo : memory_order} {ρ : EnvStack} {σ : Mem} {pv : CerbMem.PointerValue}
    (hx : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym x)) =
      some (Vobject (OVpointer pv))) :
    Step M (storeOpRedex loc ann ty (Pexpr [] () (PEsym x))
        (Pexpr [] () (PEval cv)) mo, ρ, σ)
      (storeExpr loc ann ty pv cv mo, ρ, σ) :=
  Step.store_eval rfl hx rfl

/-- `store(ty, p, y)` — LITERAL pointer, SYMBOL value — steps. -/
theorem store_lit_sym_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {y : sym} {mo : memory_order} {ρ : EnvStack} {σ : Mem} {cv : value}
    (hy : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym y)) = some cv) :
    Step M (storeOpRedex loc ann ty (Pexpr [] () (PEval (Vobject (OVpointer pv))))
        (Pexpr [] () (PEsym y)) mo, ρ, σ)
      (storeExpr loc ann ty pv cv mo, ρ, σ) :=
  Step.store_eval rfl rfl hy

/-- The rule at the symbol-pointer/literal-value shape (both strata). -/
theorem wps_store_sym_lit [SpikeGS .hasLC GF] {M : MachineCtx} {Ls : LabelSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (x : sym) (cv : value) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue}
    (hx : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym x)) =
      some (Vobject (OVpointer pv))) :
    wps M Ls Ψ (storeExpr loc ann ty pv cv mo) ρ ⊢
      wps M Ls Ψ (storeOpRedex loc ann ty (Pexpr [] () (PEsym x))
        (Pexpr [] () (PEval cv)) mo) ρ :=
  wps_store_eval loc ann ty _ _ mo ρ rfl hx rfl

theorem wpt_store_lit_sym [SpikeGS .hasLC GF] {M : MachineCtx} {Ls : LabelSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (y : sym) (mo : memory_order) (ρ : EnvStack)
    {cv : value} {k : Nat}
    (hy : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym y)) = some cv) :
    wpt M Ls k Ψ (storeExpr loc ann ty pv cv mo) ρ ⊢
      wpt M Ls (k + 1) Ψ (storeOpRedex loc ann ty
        (Pexpr [] () (PEval (Vobject (OVpointer pv)))) (Pexpr [] () (PEsym y)) mo) ρ :=
  wpt_store_eval loc ann ty _ _ mo ρ rfl rfl hy

/-! ## The frame after the bind, and its lookup -/

/-- The head frame after `p` is bound. -/
abbrev prodAFrame (p : CerbMem.PointerValue) (f : Fmap sym value) :
    Fmap sym value :=
  envAdd pASym (Vobject (OVpointer p)) f

theorem prodAFrame_lookup_p {f : Fmap sym value} (hf : SymFrame f)
    (p : CerbMem.PointerValue) :
    fmapLookupBy symCmpK pASym (prodAFrame p f) =
      some (Vobject (OVpointer p)) := by
  unfold prodAFrame
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

/-! ## THE ONE LOGICAL TOTAL THEOREM (charter P2 step 3): the
complete create/store/load in `wpt`, from the abstract capacity
alone — replaces the deleted `prodA_pre` (operational create prefix)
and `prodA_terminates` (six-round termination trace). -/

/-- The engine-facing postcondition: the delivered value is
    `Specified(7)` and the final memory holds 7's image at the
    program's own fresh cell (existential id/address). -/
def ψA (tds : CerbTags.TagDefsMap) : value → Mem → Prop := fun v σ' =>
  v = sevenVal ∧ ∃ i a : Int, CellCoh tds σ' i ⟨a, intTy, sevenBytes tds⟩

/-- THE WHOLE PROGRAM AT THE TOTAL JUDGMENT, budget 10 (derived:
    create 2 + store-operand eval 1 + store 3 + load-operand eval 1 +
    load 3): from `allocCap [⟨4, intTy⟩]` ALONE — the create through
    the PUBLIC `wpt_create`, the store/load through the generic heap
    rules at the PROGRAM-BOUND pointer. -/
theorem progAProd_wpt [SpikeGS .hasLC GF]
    {M : MachineCtx} {Ls : LabelSpecT GF}
    (hex : M.extern = fmapEmpty)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hf : SymFrame ev0) :
    iprop(allocCap M.tagDefs (GF := GF) [⟨4, intTy⟩]) ⊢
      wpt M Ls 10 (readoutPost (ψA M.tagDefs)) progAProd (ev0 :: evs) := by
  iintro Hcap
  rw [show progAProd =
    Expr [] (Esseq (symPat [] pASym BTy_unit)
      (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy
        (PrefOther "spike-x"))
      (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
        (storeOpRedex loc0 empty_annotation intTy
          (Pexpr [] () (PEsym pASym)) (Pexpr [] () (PEval sevenVal)) NA)
        (loadOpRedex loc0 empty_annotation intTy
          (Pexpr [] () (PEsym pASym)) NA)))) from rfl,
    show (10 : Nat) = 2 + 8 from rfl]
  iapply wpt_seq_sym
  iapply wpt_create loc0 empty_annotation .Prov_none ⟨4, intTy⟩ []
    (PrefOther "spike-x") (ev0 :: evs) (Nat.le_refl 2) intTy_nonatomic
    (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p ⟨Hpt, -, -⟩
  iexists (Vobject (OVpointer p))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pASym BTy_unit, show (8 : Nat) = 4 + 4 from rfl]
  iapply wpt_seq
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval loc0 empty_annotation intTy _ _ NA _ rfl
    (pv := p) (cv := sevenVal)
    (by rw [hex, evalPexpr_sym_empty]
        exact lookup_env_head (prodAFrame_lookup_p hf p) evs)
    rfl
  iapply wpt_store loc0 empty_annotation intTy p sevenVal NA sevenMval
    (intUndefBytes M.tagDefs) _ (Nat.le_refl 3) seven_encodes (seven_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  iapply wpt_mono
    (fun u ρ' => readoutPost_annot_absorb (ψA M.tagDefs) [DA_pos [] fp] Vunit u ρ') _ _
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  iapply wpt_load_eval loc0 empty_annotation intTy _ NA _ rfl (pv := p)
    (by rw [hex, evalPexpr_sym_empty]
        exact lookup_env_head (prodAFrame_lookup_p hf p) evs)
  rw [hpv, show (cellPtr id a) = cellPtr id (a + ((0 : Nat) : Int))
    from congrArg (cellPtr id) (by omega)]
  iapply wpt_load_cell_at loc0 empty_annotation id a intTy 0 intTy NA
    (.own 1) (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2 _
    (mv := sevenMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => seven_reconstruct lum fpm _) seven_loadTrap
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp2 Hcell
  iintro %σ' %ns %κs %nt Hσ
  icases (stateInterp_iff σ' ns κs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  ihave %Hcc : ⌜CellCoh M.tagDefs σ' id ⟨a, intTy,
      (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2⟩ ∧
      Iris.Std.PartialMap.get? mm id = some (metaOf M.tagDefs
        (⟨a, intTy, (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2⟩ :
          SpikeCell))⌝ $$ [Hmi Hbi Hcell]
  · iapply cellOwn_cellCoh M.tagDefs HG id (.own 1)
      ⟨a, intTy, (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2⟩
      $$ [$Hmi $Hbi $Hcell]
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact ⟨seven_fromMemValue, id, a, Hcc.1⟩

/-! ## THE EXHIBIT AT THE PRODUCTION ENTRY (the generic route:
wpt_driver_done_alloc → prod_run_eqJ — no example-specific engine
arrows) -/

/-- The label-free program registers the empty label map at
    `mainSym` (the shipped registration on the synthetic file). -/
theorem progAProd_labeledAt (sup : Nat) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile progAProd))).1)
      mainSym fmapEmpty := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile progAProd))).1).labeled =
    collect_labeled_continuations_NEW (prodFile progAProd) from rfl]
  rw [show collect_labeled_continuations_NEW (prodFile progAProd) =
    fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      fmapEmpty fmapEmpty from rfl]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- EXHIBIT A, PRODUCTION-ENTRY FORM: the shipped pipeline on the
    synthetic one-procedure file wrapping the self-contained program
    is EXACTLY ONE Active execution; its result value is
    `Specified(7)` and the final memory holds 7's byte image at the
    program's own fresh cell (existential allocation id/address).
    Whole chain: `progAProd_wpt` (PUBLIC `wpt_create` + generic heap
    rules) → `wpt_driver_done_alloc` (allocation-aware launch from
    the cold-start memory with the one-request plan) →
    `prod_run_eqJ` (generic driver collapse). -/
theorem exhibitA_prod (sup : Nat) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile progAProd) args)
          ((initial_driver_state sup (prodFile progAProd) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = sevenVal ∧
      (∃ i a : Int, CellCoh fmapEmpty dst'.layout_state i ⟨a, intTy, (sevenBytes fmapEmpty)⟩) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQe := progAProd_labeledAt sup
  have hnolabel : ∀ (l : sym) (params : List (sym × core_base_type))
      (cont : CoreExpr),
      lookupLabel (procCtx mainSym ((initial_core_run_state sup
        (collect_labeled_continuations_NEW (prodFile progAProd))).1)).labels l =
        some (params, cont) → False := by
    intro l params cont hl
    rw [procCtx_labels hQe, lookupLabel_empty] at hl
    cases hl
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ sup progAProd hQe (ψA fmapEmpty) 10
      (wpt_driver_done_alloc (GF := SpikeGF)
        (M₀ := procCtx mainSym ((initial_core_run_state sup
          (collect_labeled_continuations_NEW (prodFile progAProd))).1))
        rfl rfl (procCtx_labels hQe) rfl rfl
        (fun l params cont hl => (hnolabel l params cont hl).elim)
        (fun l params cont hl => (hnolabel l params cont hl).elim)
        (fun _ _ _ _ => iprop(False))
        progAProd fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
        [⟨4, intTy⟩] progAProd_frag
        (by rw [show pot progAProd = 4 from rfl,
            show lemDefaultFuel = 999999 + 1 from rfl]
            omega)
        (prodMem₀_launchCoh [⟨4, intTy⟩] prod_one_int_plan_fits)
        (ψA fmapEmpty) 10
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply blockSpecsT_intro fun l params cont _ _ _ _ hl =>
              (hnolabel l params cont hl).elim
          · iapply progAProd_wpt (procCtx_extern _ _) fmapEmpty []
              symFrame_empty $$ Hcap))
      (by rw [show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      fs args
  exact ⟨dres, dst', heq, hψ.1, hψ.2, hbl, hout, herr⟩

end CerberusHeapLang
