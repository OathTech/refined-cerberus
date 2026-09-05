/-
CerberusHeapLang.EmittedAExhibit — EXHIBIT A IN THE EMITTED-CORE SHAPE
(dialect arc E1; the acceptance exhibit of the slice, briefed from
docs/2026-09-04_emitted-core-dialect-design.md §C.1).

The authored exhibits write Core the way a person writes it: bare nodes
(`Expr []`), literal alignments (`create(4, int)`), no `bound`. The
elaborator writes Core differently (docs/corpus-e0/t1.annot.core): every
statement and expression node carries annotations (`Aloc`/`Astmt`/
`Aexpr`; `Astd` "§6.5#2" on the `bound`s), every full expression is
wrapped in `bound(...)`, and the alignment of a `create` is the type
constant `Ivalignof(ty)`. E1 admits exactly these three features; this
module re-expresses exhibit A (`progAProd`, ProdExhibit.lean) as an E1
SYNTHETIC in the dialect's features — annotations on every node
(action nodes INCLUDED), `bound` around the two actions, `Ivalignof` —
with the placements CHOSEN to exercise the location update at every
round, not the elaborator's own: the corpus (docs/corpus-e0/*.annot.core)
leaves `create`/`store`/`load`/`kill` action nodes without `Expr`
annotations (their `loc` is in the `Action loc` field; the one exception
is t5's object-lifetime store, `Astd` + `Aloc`) and never emits
`bound(store …)`/`bound(load …)` (a `bound` wraps a full expression whose
body is a `pure`/`let weak …`; a declaration's store is unbound; an
assignment's store is `neg(store …)`, E5's protocol) — the E1 range audit,
docs/2026-09-05_audit-e1-range.md §7/R-1. The elaborator's own placements
are t1Main's (Examples/CorpusE0.lean). The loaded-value protocol
(`Specified`, `conv_loaded_int`), `unseq`, the negative-action protocol
and `Eccall` are E2–E6. The program is certified through the PUBLIC rules
at both strata and through the production lane (`exhibitA_prod_e1`, the
shipped pipeline on the synthetic file).

What the re-expression exercises that the authored twin does not:
  * the live LOCATION: every node's `Aloc` is a non-library location, so
    the mirror's general-arm location update fires at every round
    (`Ctl.upd`; Core_reduction.lean:484 `get_loc`), and the production
    control starts at the parked thread's `other "Driver.drive"`;
  * `bound` around the store and around the load (`Frag.bound`,
    `wps_bound`/`wpt_bound`): REMOVE-BOUND drops the load's dynamic
    annotation, so the program's value is BARE `Specified(7)` — the
    authored twin delivers `{DA_pos …} Specified(7)`;
  * `create(Ivalignof(int), int)` (`Frag.create_op`, `wps_create_eval`/
    `wpt_create_eval`): the alignment is the evaluator's own
    `CerbMem.alignofIval M.tagDefs intTy` (= 4), not an authored literal.

A CLIENT of the logic: it reasons through the public rules only (no
`Step.*`, no engine arrows) — the same discipline as ProdExhibit.lean;
the production theorem is reached through the generic
`wpt_driver_done_alloc → prod_run_eqJ` route.
-/
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.Exhibit
import CerberusHeapLang.AllocExhibit
import CerberusHeapLang.ProdExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open scoped Iris.Std.PartialMap

variable {GF : BundledGFunctors}

/-! ## The program in the emitted shape -/

/-- The pseudo-source the annotations point into (a NON-library path, so
    `isLibraryLocation` is false and the location update fires). -/
def eaFile : String := "exhibitA.c"

def eaPos (l c : Nat) : CerbLocation.Pos := ⟨eaFile, l, c⟩

/-- A source region, as the elaborator's `Aloc` carries it. -/
def eaLoc (l1 c1 l2 c2 : Nat) : CerbLocation.Loc :=
  .region (eaPos l1 c1) (eaPos l2 c2) .noCursor

/-- `Ivalignof('signed int')` — the type constant the elaborator emits as
    the alignment operand of every `create`. -/
def alignofIntPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Civalignof [Pexpr [] () (PEval (Vctype intTy))])

/-- The ctype operand `'signed int'`. -/
def intTyPe : generic_pexpr Unit sym := Pexpr [] () (PEval (Vctype intTy))

/-- Exhibit A in the emitted shape:
    ```
    {-# <exhibitA.c:1:17, exhibitA.c:1:61> #-} let strong p: pointer =
      create(Ivalignof('signed int'), 'signed int') in
    {-# §6.5#2 #-}
    bound(store('signed int', p, Specified(7))) ;
    {-# §6.5#2 #-}
    bound(load('signed int', p))
    ```
    (annotation lists in the elaborator's VOCABULARY — `Aloc` + `Astmt` on
    the statement node, `Aloc` + `Aexpr` on the expression nodes, `Astd` on
    the `bound`s — at placements chosen for the exercise, action nodes
    included (the elaborator leaves action nodes unannotated and never
    wraps a bare action in `bound`: header, R-1); positions are the
    exhibit's own pseudo-source). -/
def progAE1 : CoreExpr :=
  Expr [Aloc (eaLoc 1 17 1 61), Astmt] (Esseq (symPat [] pASym BTy_unit)
    (createOpRedex [Aloc (eaLoc 1 26 1 61), Aexpr] (eaLoc 1 26 1 61) empty_annotation
      alignofIntPe intTyPe (PrefOther "spike-x"))
    (Expr [Aloc (eaLoc 2 2 2 28), Astmt] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
      (Expr [Astd "§6.5#2"] (Ebound
        (storeOpRedex [Aloc (eaLoc 2 2 2 16), Aexpr] (eaLoc 2 2 2 16) empty_annotation intTy
          (Pexpr [] () (PEsym pASym)) (Pexpr [] () (PEval sevenVal)) NA)))
      (Expr [Astd "§6.5#2"] (Ebound
        (loadOpRedex [Aloc (eaLoc 2 18 2 27), Aexpr] (eaLoc 2 18 2 27) empty_annotation intTy
          (Pexpr [] () (PEsym pASym)) NA))))))

/-- Cone membership: the plain-symbol binder at a `create_op` head, then
    the wildcard binder over two `bound` frames. -/
theorem progAE1_frag : Frag progAE1 :=
  .sseq_sym
    (.create_op rfl (.ctorTy [] Civalignof rfl [] intTy) (.val [] (Vctype intTy))
      (by rw [show peDepth alignofIntPe = 2 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (peDepth_val_le _ _))
    (.sseq
      (.bound (.store_op rfl (.sym [] pASym) (.val [] sevenVal)
        (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym pASym)) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)
        (peDepth_val_le _ _)))
      (.bound (.load_op rfl (.sym [] pASym)
        (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym pASym)) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega))))

/-- The alignment operand evaluates to the evaluator's own alignment
    constant (`evalPexpr_tyctor`, `evalTyCtor_alignof`), which for `int`
    is the literal alignment 4 the authored twin wrote. -/
theorem alignofIntPe_eval {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym) {file : generic_file Unit core_run_annotation} (ρ : EnvStack) :
    evalPexpr tds ext file ρ alignofIntPe =
      some (Vobject (OVinteger (CerbMem.alignofIval tds intTy))) := by
  simp only [alignofIntPe, evalPexpr_tyctor, evalTyCtor_alignof, isTyCtor]

theorem alignofIval_intTy {tds : CerbTags.TagDefsMap} :
    CerbMem.alignofIval tds intTy = .IV .Prov_none 4 := rfl

/-! ## THE PARTIAL JUDGMENT: the value is BARE `Specified(7)` (the `bound`
dropped the load's dynamic annotation) and the cell holds 7 -/

theorem progAE1_wps [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4)) ⊢
      wps M p Ls Θ (fun w _ => iprop(⌜w = SpikeVal.pure sevenVal⌝ ∗
          (∃ (id a : Int), cellOwn M.tagDefs (GF := GF) id (.own 1)
            ⟨a, intTy, (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2⟩)))
        progAE1 (ev0 :: evs) := by
  iintro Hcap
  unfold progAE1
  iapply wps_seq_sym
  iapply wps_create_eval _ _ empty_annotation alignofIntPe intTyPe (PrefOther "spike-x")
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wps_create _ _ empty_annotation .Prov_none 4 intTy (PrefOther "spike-x") (ev0 :: evs)
    intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p ⟨Hpt, -⟩
  iexists (Vobject (OVpointer p))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pASym BTy_unit]
  iapply wps_seq
  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wps_store_eval _ _ empty_annotation intTy _ _ NA _ rfl
    (pv := p) (cv := sevenVal)
    (by rw [evalPexpr_sym_of_resolve _ _ _ (hex _)]
        exact lookup_env_head (prodAFrame_lookup_p hf p) evs)
    (evalPexpr_val _ _ _ _ _)
  iapply wps_store _ _ empty_annotation intTy p sevenVal NA sevenMval
    (intUndefBytes M.tagDefs) _ seven_encodes (seven_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto]
  iapply wps_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  iapply wps_load_eval _ _ empty_annotation intTy _ NA _ rfl (pv := p)
    (by rw [evalPexpr_sym_of_resolve _ _ _ (hex _)]
        exact lookup_env_head (prodAFrame_lookup_p hf p) evs)
  rw [hpv, show (cellPtr id a) = cellPtr id (a + ((0 : Nat) : Int))
    from congrArg (cellPtr id) (by omega)]
  iapply wps_load_cell_at _ _ empty_annotation id a intTy 0 intTy NA
    (.own 1) (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2 _
    (mv := sevenMval) (by omega)
    (fun lum fpm => seven_reconstruct lum fpm _) seven_loadTrap
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp2 Hcell
  simp only [SpikeVal.val]
  isplit
  · ipureintro
    rw [seven_fromMemValue]
  iexists id, a
  iexact Hcell

/-! ## THE TOTAL JUDGMENT, budget 13 (derived: create-operand eval 1 +
create 2 + bound 1 + store-operand eval 1 + store 3 + bound 1 +
load-operand eval 1 + load 3) -/

theorem progAE1_wpt [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4)) ⊢
      wpt M p Ls Θ 13 (readoutPost (ψA M.tagDefs)) progAE1 (ev0 :: evs) := by
  iintro Hcap
  unfold progAE1
  rw [show (13 : Nat) = 3 + 10 from rfl]
  iapply wpt_seq_sym
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation alignofIntPe intTyPe (PrefOther "spike-x")
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create _ _ empty_annotation .Prov_none 4 intTy
    (PrefOther "spike-x") (ev0 :: evs) (Nat.le_refl 2) intTy_size_pos intTy_nonatomic
    (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p ⟨Hpt, -⟩
  iexists (Vobject (OVpointer p))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym pASym BTy_unit, show (10 : Nat) = 5 + 5 from rfl]
  iapply wpt_seq
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ empty_annotation intTy _ _ NA _ rfl
    (pv := p) (cv := sevenVal)
    (by rw [evalPexpr_sym_of_resolve _ _ _ (hex _)]
        exact lookup_env_head (prodAFrame_lookup_p hf p) evs)
    (evalPexpr_val _ _ _ _ _)
  iapply wpt_store _ _ empty_annotation intTy p sevenVal NA sevenMval
    (intUndefBytes M.tagDefs) _ (Nat.le_refl 3) seven_encodes (seven_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto]
  -- the earlier numeral rewrites already shaped this budget as `3 + 1 + 1`
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  iapply wpt_load_eval _ _ empty_annotation intTy _ NA _ rfl (pv := p)
    (by rw [evalPexpr_sym_of_resolve _ _ _ (hex _)]
        exact lookup_env_head (prodAFrame_lookup_p hf p) evs)
  rw [hpv, show (cellPtr id a) = cellPtr id (a + ((0 : Nat) : Int))
    from congrArg (cellPtr id) (by omega)]
  iapply wpt_load_cell_at _ _ empty_annotation id a intTy 0 intTy NA
    (.own 1) (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2 _
    (mv := sevenMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => seven_reconstruct lum fpm _) seven_loadTrap
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp2 Hcell
  simp only [SpikeVal.val]
  iintro %σ' %ns %κs %nt Hσ
  ihave H := cellOwn_readout M.tagDefs id (.own 1) _ $$ Hcell
  imod H $$ %σ' %ns %κs %nt Hσ with %hcc
  ipureintro
  exact ⟨seven_fromMemValue, id, a, hcc⟩

/-! ## THE PRODUCTION ENTRY (the generic route, as exhibit A's) -/

/-- The label-free program registers the empty label map at `mainSym`. -/
theorem progAE1_labeledAt (sup : Nat) :
    LabeledAt ((initial_core_run_state sup (collect_labeled_continuations_NEW
        (prodFile progAE1))).1)
      mainSym fmapEmpty := by
  unfold LabeledAt
  rw [show ((initial_core_run_state sup (collect_labeled_continuations_NEW
      (prodFile progAE1))).1).labeled =
    collect_labeled_continuations_NEW (prodFile progAE1) from rfl]
  rw [show collect_labeled_continuations_NEW (prodFile progAE1) =
    fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym
      fmapEmpty fmapEmpty from rfl]
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- EXHIBIT A IN THE EMITTED SHAPE, PRODUCTION-ENTRY FORM: the shipped
    pipeline on the synthetic one-procedure file wrapping `progAE1` is
    EXACTLY ONE Active execution; its result value is `Specified(7)` and
    the final memory holds 7's byte image at the program's own fresh cell.
    The statement is exhibit A's (`exhibitA_prod`) verbatim but for the
    program; the chain is `progAE1_wpt` → `wpt_driver_done_alloc` →
    `prod_run_eqJ`. -/
theorem exhibitA_prod_e1 (sup : Nat) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile progAE1) args)
          ((initial_driver_state sup (prodFile progAE1) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = sevenVal ∧
      (∃ i a : Int, CellCoh fmapEmpty dst'.layout_state i ⟨a, intTy, (sevenBytes fmapEmpty)⟩) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQe := progAE1_labeledAt sup
  have hnolabel : ∀ (l : sym) (params : List (sym × core_base_type))
      (cont : CoreExpr),
      lookupLabel ((prodCtx (prodFile progAE1) ((initial_core_run_state sup
        (collect_labeled_continuations_NEW (prodFile progAE1))).1)).labelsAt (procCtl mainSym).proc) l =
        some (params, cont) → False := by
    intro l params cont hl
    rw [prodCtx_labels hQe, lookupLabel_empty] at hl
    cases hl
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ sup progAE1 hQe (ψA fmapEmpty) 13
      (wpt_driver_done_alloc (GF := SpikeGF) (ctl := prodCtl sup)
        (M₀ := prodCtx (prodFile progAE1) ((initial_core_run_state sup
          (collect_labeled_continuations_NEW (prodFile progAE1))).1))
        rfl rfl (prodCtx_labels hQe) rfl rfl rfl rfl
        (fun l params cont hl => (hnolabel l params cont hl).elim)
        (fun l params cont hl => (hnolabel l params cont hl).elim)
        (fun _ _ _ _ => iprop(False))
        progAE1 fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
        (allocCost fmapEmpty intTy 4) progAE1_frag
        (by exact Nat.le_of_ble_eq_true rfl)
        (prodMem₀_launchCoh _ prod_one_int_budget_fits)
        (ψA fmapEmpty) 13
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply blockSpecsT_intro fun l params cont _ _ _ _ hl =>
              (hnolabel l params cont hl).elim
          · iapply progAE1_wpt (resolveExtern_id_of_empty (prodCtx_extern _ _)) fmapEmpty []
              symFrame_empty $$ Hcap))
      (by rw [show CerbFuel.driverFuel = 99999999 + 1 from rfl]; omega)
      fs args
  exact ⟨dres, dst', heq, hψ.1, hψ.2, hbl, hout, herr⟩

end CerberusHeapLang
