/- Public-rule derivation and complete-file production certificate for t5. -/
import CerberusHeapLang.Examples.EmittedT5
import CerberusHeapLang.EmittedIntSupport
import CerberusHeapLang.ProdEntry

set_option autoImplicit false
namespace CerberusHeapLang.CorpusA7.T5
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (psym specInt act wc seqE letS letW bnd)
open EmittedStdCore (HasIntLibrary sintTyAnn)
open EmittedIntSupport (int_size_pos int_nonatomic int_decIndep int_storable int_encodes)
variable {GF : BundledGFunctors}

theorem convLoaded_eval [LemFuel] {M : MachineCtx} (h : HasIntLibrary M.file)
    {ρ : EnvStack} {an ta : List annot} {s : sym} {n : Int}
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym s) = some (lint n))
    (hlo : -2147483648 ≤ n) (hhi : n ≤ 2147483647) :
    evalPexpr M.tagDefs M.extern M.file ρ (convLoaded an (sintTyAnn ta) s) = some (lint n) :=
  EmittedStdCore.eval_convLoadedInt_spec an h (evalPexpr_val _ _ _ _ _) hv hlo hhi

theorem tuple_eval [LemFuel] {M : MachineCtx} {ρ : EnvStack} (n m : Nat) (v w : value)
    (hn : evalPexpr M.tagDefs M.extern M.file ρ (psym (tmp n)) = some v)
    (hm : evalPexpr M.tagDefs M.extern M.file ρ (psym (tmp m)) = some w) :
    evalPexpr M.tagDefs M.extern M.file ρ (tuple n m) = some (Vtuple [v, w]) := by
  rw [tuple, evalPexpr_ctor2, hn, hm]
  rfl

theorem gtBranch_eval [LemFuel] {M : MachineCtx} (h : HasIntLibrary M.file) (ρ : EnvStack) :
    evalPexpr M.tagDefs M.extern M.file ρ (gtBranch (ointPe 3) (ointPe 2)) = some (lint 1) := by
  unfold gtBranch convInt tyPe ointPe
  rw [evalPexpr_if, if_pos (show (isPePure (specInt 1) && isPePure (specInt 0)) = true from rfl),
    evalPexpr_op, EmittedStdCore.eval_convInt_call _ h (evalPexpr_val _ _ _ _ _)
      (evalPexpr_val _ _ _ _ _) (by decide) (by decide),
    EmittedStdCore.eval_convInt_call _ h (evalPexpr_val _ _ _ _ _)
      (evalPexpr_val _ _ _ _ _) (by decide) (by decide)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalBinop OpGt (oint 3) (oint 2) = some Vtrue from rfl]
  exact specInt_eval _ 1

theorem condBranch_eval [LemFuel] {M : MachineCtx} (h : HasIntLibrary M.file) (ρ : EnvStack) :
    evalPexpr M.tagDefs M.extern M.file ρ (condBranch (ointPe 1) (ointPe 0)) = some (lint 0) := by
  unfold condBranch convInt tyPe ointPe
  rw [evalPexpr_if, if_pos (show (isPePure (specInt 1) && isPePure (specInt 0)) = true from rfl),
    evalPexpr_op, EmittedStdCore.eval_convInt_call _ h (evalPexpr_val _ _ _ _ _)
      (evalPexpr_val _ _ _ _ _) (by decide) (by decide),
    EmittedStdCore.eval_convInt_call _ h (evalPexpr_val _ _ _ _ _)
      (evalPexpr_val _ _ _ _ _) (by decide) (by decide)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalBinop OpEq (oint 1) (oint 0) = some Vfalse from rfl]
  exact specInt_eval _ 0

abbrev frAssign (n m : Nat) (v : Int) (pr : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (tmp n) (Vobject (OVpointer pr)) (envAdd (tmp m) (lint v) f)

theorem gt_select :
    select_case subst_sym_expr (Vtuple [lint 3, lint 2]) gtPats =
      some (Expr [Astd "§6.5.8#6"] (Epure (gtBranch (ointPe 3) (ointPe 2)))) := rfl

theorem cond_select :
    select_case subst_sym_pexpr (Vtuple [lint 1, lint 0]) condPats =
      some (condBranch (ointPe 1) (ointPe 0)) := rfl

def selectedBoolBranch : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEnot
    (Pexpr [] () (PEop OpEq (ointPe 0) (ointPe 1)))))
    (Pexpr [] () (PEval Vtrue)) (Pexpr [] () (PEval Vfalse)))

theorem bool_select : select_case subst_sym_expr (lint 0) boolPats =
    some (pure selectedBoolBranch) := rfl

theorem boolBranch_eval [LemFuel] {M : MachineCtx} (ρ : EnvStack) :
    evalPexpr M.tagDefs M.extern M.file ρ selectedBoolBranch = some Vtrue := by
  rw [selectedBoolBranch, evalPexpr_if,
    if_pos (show (isPePure (Pexpr [] () (PEval Vtrue)) &&
      isPePure (Pexpr [] () (PEval Vfalse))) = true from rfl),
    evalPexpr_not, evalPexpr_op, ointPe, ointPe, evalPexpr_val, evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalBinop OpEq (oint 0) (oint 1) = some Vfalse from rfl]
  simp only [Option.bind_some]
  rw [evalPexpr_val]

theorem condPe_eval [LemFuel] {M : MachineCtx} (hstd : HasIntLibrary M.file) {ρ : EnvStack}
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (tuple 29 30) =
      some (Vtuple [lint 1, lint 0])) :
    evalPexpr M.tagDefs M.extern M.file ρ
      (Pexpr [] () (PEcase (tuple 29 30) condPats)) = some (lint 0) := by
  rw [evalPexpr_case, if_pos (show isPePureAlts condPats = true from rfl), hv]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [cond_select]
  simp only [Option.bind_some]
  rw [if_pos (show peDepth (reannot0 (condBranch (ointPe 1) (ointPe 0))) ≤ peDepthAlts condPats
    from Nat.le_of_ble_eq_true rfl), evalPexpr_reannot0]
  exact condBranch_eval hstd ρ

/-- A whole integer load with the emitted temporary binder, using the
    public whole-cell rule and preserving the caller's postcondition. -/
theorem wpt_t5Load [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (ty : ctype) (x : sym) (n c1 c2 : Nat) (f : Fmap sym value) (rest : EnvStack)
    (hf : SymFrame f) (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv ty bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) ty bs -∗
        Ψ (.annot [DA_pos [] fp] v) (envAdd (tmp n) (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (load ty x n c1 c2) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  rw [show load ty x n c1 c2 = EmittedIntSupport.boundLoad
    [Aloc (loc c1 c2), Aexpr, intValueAnnot] [] [Aloc (loc c1 c2), Aexpr] [] [] []
    ptrBty (loc c1 c2) empty_annotation ty x (tmp n) NA from rfl]
  iapply EmittedIntSupport.wpt_boundLoad hex
    [Aloc (loc c1 c2), Aexpr, intValueAnnot] [] [Aloc (loc c1 c2), Aexpr] [] [] []
    ptrBty (loc c1 c2) empty_annotation ty x (tmp n) NA
    f rest hf pv (.own 1) bs v hl hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro Hpt
  iapply HΨ $$ Hpt


abbrev frGt (px : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (tmp 35) (lint 3) (envAdd (tmp 36) (lint 2)
    (envAdd (tmp 34) (Vobject (OVpointer px)) f))

/-- The emitted comparison reads x=3 and returns Specified(1), retaining
    the load footprint until the surrounding full-expression bound. -/
theorem wpt_t5Gt [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK xSym f = some (Vobject (OVpointer px))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) xTy (emittedIntBytes M.tagDefs 3) ∗
      (∀ fp, pointsToCell M.tagDefs px (.own 1) xTy (emittedIntBytes M.tagDefs 3) -∗
        Ψ (.annot [DA_pos [] fp] (lint 1)) (frGt px f :: rest))) ⊢
      wpt M p Ls Θ 16 Ψ gt (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold gt
  rw [show tuplePattern 35 36 =
    tuplePat [] [([], some (tmp 35), intBty), ([], some (tmp 36), intBty)] from rfl]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ 11 5
  unfold intLiteral intPe
  iapply wpt_mono_k (show 6 + 3 ≤ 11 by decide) _ _
  iapply EmittedIntSupport.wpt_unseq_value_right _ _ [] _ (lint 2) _ 6
  iapply wpt_t5Load hex xTy xSym 34 40 41 f rest hf px (emittedIntBytes M.tagDefs 3)
    (lint 3) hx rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint 3, lint 2], [DA_pos [] fp]
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_annot
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl (cval := Vtuple [lint 3, lint 2])
    (tuple_eval 35 36 _ _
      (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_pos (by decide)]))
      (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_neg (by decide),
        envAdd_lookup (hf.add _ _), if_pos (by decide)])))
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl gt_select
  iapply wpt_pure (gtBranch (ointPe 3) (ointPe 2)) _ (Nat.le_refl 2) rfl
    (gtBranch_eval hstd _)
  simp only [SpikeVal.merge]
  iapply HΨ $$ Hpt

abbrev frCond (px : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (tmp 29) (lint 1) (envAdd (tmp 30) (lint 0) (frGt px f))

theorem wpt_t5Cond [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK xSym f = some (Vobject (OVpointer px))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) xTy (emittedIntBytes M.tagDefs 3) ∗
      (pointsToCell M.tagDefs px (.own 1) xTy (emittedIntBytes M.tagDefs 3) -∗
        Ψ (.pure (lint 0)) (frCond px f :: rest))) ⊢
      wpt M p Ls Θ 25 Ψ cond (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold cond bnd
  rw [show (25 : Nat) = 24 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  rw [show tuplePattern 29 30 =
    tuplePat [] [([], some (tmp 29), intBty), ([], some (tmp 30), intBty)] from rfl]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ 21 3
  unfold intLiteral intPe
  iapply wpt_mono_k (show 16 + 3 ≤ 21 by decide) _ _
  iapply EmittedIntSupport.wpt_unseq_value_right _ _ [] _ (lint 0) _ 16
  iapply wpt_t5Gt hstd hex f rest hf px hx
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint 1, lint 0], [DA_pos [] fp]
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_annot
  have hfg : SymFrame (frGt px f) := ((hf.add _ _).add _ _).add _ _
  unfold pure
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl
    (condPe_eval hstd (tuple_eval 29 30 _ _
      (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by rw [envAdd_lookup (hfg.add _ _), if_pos (by decide)]))
      (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by rw [envAdd_lookup (hfg.add _ _), if_neg (by decide),
        envAdd_lookup hfg, if_pos (by decide)]))))
  simp only [SpikeVal.merge]
  iapply HΨ $$ Hpt

theorem wpt_t5AssignBlock [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (start n m : Nat) (v : Int) (hnm : m ≠ n)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hr : fmapLookupBy symCmpK rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) pr (.own 1) rTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pr (.own 1) rTy (emittedIntBytes M.tagDefs v) -∗
        Ψ (.pure Vunit) (envAdd s (lint v) (frAssign n m v pr f) :: rest))) ⊢
      wpt M p Ls Θ 25 Ψ (assignBlock start n m v) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold assignBlock wc
  iapply wpt_seq _ _ _ _ _ _ _ 24 1
  iapply wpt_seq _ _ _ _ _ _ _ 23 1
  unfold bnd
  rw [show (Pattern [] (CaseCtor Ctuple
    [Pattern [] (CaseBase (some (tmp n), ptrBty)), Pattern [] (CaseBase (some (tmp m), intBty))]) : pattern) =
    tuplePat [] [([], some (tmp n), ptrBty), ([], some (tmp m), intBty)] from rfl]
  iapply wpt_bound_wseq_tuple _ _ _ _ _ _ _ _ 7 16 rfl
  unfold intLiteral intPe
  iapply wpt_mono_k (show 2 + 3 ≤ 7 by decide) _ _
  iapply EmittedIntSupport.wpt_unseq_value_right _ _ [] _ (lint v) _ 2
  iapply wpt_pure (psym rSym) _ (Nat.le_refl 2) rfl (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] hr)
  simp only [SpikeVal.mergeInto, SpikeVal.val]
  iexists [Vobject (OVpointer pr), lint v], []
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  rw [show (Expr [] (Eannot [] (Expr [] (Ewseq (Pattern [] (CaseBase (none, BTy_unit)))
      (Expr [Astd "§6.5.16.1#2, store"] (Eaction (Paction polarity.Neg0
        (Action (locP start (start + 5) (start + 2)) empty_annotation
          (Store0 false (tyPe rTy) (assignmentPtr n) (assignmentConv m) NA)))))
      (pure (assignmentConv m))))) : CoreExpr) =
    negAssignBody [] [] [Astd "§6.5.16.1#2, store"] [] [] [] BTy_unit
      (locP start (start + 5) (start + 2)) empty_annotation rTy
      (assignmentPtr n) (assignmentConv m) (assignmentConv m) NA from rfl]
  have hlp : evalPexpr M.tagDefs M.extern M.file (frAssign n m v pr f :: rest)
      (assignmentPtr n) = some (Vobject (OVpointer pr)) :=
    EmittedIntSupport.symbol_eval hex ((hf.add _ _).add _ _) rest [Astd "§6.5.16#3, sentence 1"]
      (by rw [envAdd_lookup (hf.add _ _), if_pos (symOrd_self _)])
  have hlv : evalPexpr M.tagDefs M.extern M.file (frAssign n m v pr f :: rest)
      (assignmentConv m) = some (lint v) :=
    convLoaded_eval hstd (EmittedIntSupport.symbol_eval hex ((hf.add _ _).add _ _) rest []
      (by rw [envAdd_lookup (hf.add _ _), if_neg (show symOrd (tmp m) (tmp n) ≠ .eq from symOrd_ne_eq_of_num_ne hnm),
        envAdd_lookup hf, if_pos (symOrd_self _)])) hv1 hv2
  rw [show rTy = sintTyAnn [Aloc (loc 29 32)] from rfl]
  iapply EmittedIntSupport.wpt_intAssign hex [Astd "§6.5#2"] [] []
    [Astd "§6.5.16.1#2, store"] [] [] [] BTy_unit
    (locP start (start + 5) (start + 2)) empty_annotation [Aloc (loc 29 32)]
    (assignmentPtr n) (assignmentConv m) (assignmentConv m) NA
    (frAssign n m v pr f) rest ((hf.add _ _).add _ _) pr bs v (lint v)
    hv1 hv2 rfl hlp hlv rfl hlv
  isplitl [Hpt]
  · iexact Hpt
  iintro %s %hs Hpt
  unfold unitExpr pure
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply HΨ $$ %s %hs Hpt


theorem wpt_t5Bool [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} (ρ : EnvStack)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym (tmp 27)) = some (lint 0)) :
    Ψ (.pure Vtrue) ρ ⊢ wpt M p Ls Θ 4 Ψ boolExpr ρ := by
  iintro H
  unfold boolExpr
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl hv
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl bool_select
  unfold pure
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (boolBranch_eval _)
  iexact H

def returnQ : LabelMap :=
  fmapAddBy symCmpL retSym ([((tmp 46), intBty)], Expr [] (Epure (psym (tmp 46)))) fmapEmpty

theorem mainBody_saves : collect_saves mainBody = returnQ := rfl

theorem returnQ_lookup :
    lookupLabel returnQ retSym = some ([((tmp 46), intBty)], Expr [] (Epure (psym (tmp 46)))) := by
  unfold lookupLabel returnQ
  rw [fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

theorem returnQ_inv {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel returnQ l = some (params, cont)) :
    params = [((tmp 46), intBty)] ∧ cont = Expr [] (Epure (psym (tmp 46))) := by
  unfold lookupLabel returnQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem returnQ_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs [((tmp 46), intBty)] [v] (f :: rest) = envAdd (tmp 46) v f :: rest := by
  show update_env (mk_sym_pat (tmp 46) intBty) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem fr46_lookup {f : Fmap sym value} (hf : SymFrame f) (v : value) :
    fmapLookupBy symCmpK (tmp 46) (envAdd (tmp 46) v f) = some v := by
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

def returnSpec (GF : BundledGFunctors) [SpikeGS .hasLC GF] : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜symOrd l retSym = .eq ∧ m = 2 ∧ vs = [lint 1] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝)

/-- The post: the delivered value is `Specified(1)`. -/
def resultPost : value → Mem → Prop := fun v _ => v = lint 1

theorem returnSpec_readout [LemFuel] [SpikeGS .hasLC GF] :
    ∀ w ρ', iprop(⌜w = SpikeVal.pure (lint 1)⌝) ⊢ readoutPost (GF := GF) resultPost w ρ' := by
  intro w ρ'
  iintro %hw
  iintro %σ' %ns %κs %nt -
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  subst hw
  rfl

theorem returnSpec_valid [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = returnQ) :
    ⊢ blockSpecsT (GF := GF) M p (returnSpec GF) emptyProcSpecT (readoutPost resultPost) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [hQ] at hl
  obtain ⟨rfl, rfl⟩ := returnQ_inv hl
  dsimp only [returnSpec]
  iintro %hpure
  obtain ⟨-, rfl, rfl, f, rest, hρ, hf⟩ := hpure
  cases hρ
  rw [returnQ_bindArgs]
  iapply wpt_pure (psym (tmp 46)) _ (Nat.le_refl 2) rfl
    (EmittedIntSupport.symbol_eval hex (by emitted_frame) _ [] (fr46_lookup hf (lint 1)))
  iapply returnSpec_readout
  ipureintro
  rfl


-- The shared frame tactics apply public frame laws. Concrete symbol
-- comparisons are decided by the kernel; fresh symbols need explicit facts.
theorem kill_eq (atLoc : CerbLocation.Loc) (ty : ctype) (x : sym) :
    kill atLoc ty x = killOpRedex [] atLoc empty_annotation (Static0 ty) (psym x) := rfl

theorem wpt_t5Return [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = returnQ)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) xTy (emittedIntBytes M.tagDefs 3) ∗
      pointsToCell M.tagDefs pr (.own 1) rTy (emittedIntBytes M.tagDefs 1)) ⊢
      wpt M p (returnSpec GF) emptyProcSpecT 16 Ψ returnStmt (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  simp only [returnStmt, letS, seqE, wc, bnd, kill_eq]
  rw [show (Pattern [] (CaseBase (some (tmp 45), intBty)) : pattern) =
    symPat [] (tmp 45) intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 9
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_t5Load hex rTy rSym 44 81 82 f rest hf pr (emittedIntBytes M.tagDefs 1) (lint 1) hr rfl rfl
  isplitl [Hr]
  · iexact Hr
  iintro %fp Hr
  simp only [SpikeVal.val]
  iexists (lint 1)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 3 6
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ _ _ (psym xSym) _ rfl (pv := px) (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by emitted_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 xTy) px xTy (emittedIntBytes M.tagDefs 3) _ (Nat.le_refl 2) rfl
  isplitl [Hx]
  · iexact Hx
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 3
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ _ _ (psym rSym) _ rfl (pv := pr) (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by emitted_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 rTy) pr rTy (emittedIntBytes M.tagDefs 1) _ (Nat.le_refl 2) rfl
  isplitl [Hr]
  · iexact Hr
  simp only [SpikeVal.mergeInto]
  iapply wpt_run [] empty_annotation retSym [convLoaded [] retTy (tmp 45)] _ _ 2
    (by rw [hQ]; exact returnQ_lookup)
    (by
      have hv : evalPexpr M.tagDefs M.extern M.file
          (envAdd (tmp 45) (lint 1) (envAdd (tmp 44) (Vobject (OVpointer pr)) f) :: rest)
          (convLoaded [] retTy (tmp 45)) = some (lint 1) :=
        convLoaded_eval hstd (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest []
          (by emitted_lookup)) (by decide) (by decide)
      rw [evalPexprs_cons, hv, evalPexprs_nil]
      rfl) (Nat.le_refl 3)
  dsimp only [returnSpec]
  ipureintro
  exact ⟨by decide +kernel, rfl, rfl, _, _, rfl, by emitted_frame⟩

abbrev frIf (px pr : CerbMem.PointerValue) (f : Fmap sym value) :=
  frAssign 40 41 1 pr (envAdd (tmp 26) Vtrue (envAdd (tmp 27) (lint 0) (frCond px f)))

theorem wpt_t5If [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hx : fmapLookupBy symCmpK xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) xTy (emittedIntBytes M.tagDefs 3) ∗
      pointsToCell M.tagDefs pr (.own 1) rTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs px (.own 1) xTy (emittedIntBytes M.tagDefs 3) -∗
        pointsToCell M.tagDefs pr (.own 1) rTy (emittedIntBytes M.tagDefs 1) -∗
        Ψ (.pure Vunit) (envAdd s (lint 1) (frIf px pr f) :: rest))) ⊢
      wpt M p Ls Θ 55 Ψ ifStmt (f :: rest) := by
  iintro ⟨Hx, Hr, HΨ⟩
  unfold ifStmt letS
  rw [show (Pattern [] (CaseBase (some (tmp 27), intBty)) : pattern) =
    symPat [] (tmp 27) intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 25 30
  iapply wpt_t5Cond hstd hex f rest hf px hx
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iexists (lint 0)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (tmp 26), BTy_boolean)) : pattern) =
    symPat [] (tmp 26) BTy_boolean from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 4 26
  iapply wpt_t5Bool _ (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by emitted_lookup))
  iexists Vtrue
  isplit
  · ipureintro; rfl
  rw [update_env_sym, show (26 : Nat) = 25 + 1 from rfl]
  iapply wpt_if_true _ (psym (tmp 26)) _ _ _ (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by emitted_lookup))
  iapply wpt_t5AssignBlock hstd hex 49 40 41 1 (by decide) (by decide) (by decide)
    _ rest (by emitted_frame) pr bs (by emitted_lookup)
  isplitl [Hr]
  · iexact Hr
  iintro %s %hs Hr
  iapply HΨ $$ %s %hs Hx Hr

theorem store_eq (a : List annot) (atLoc : CerbLocation.Loc) (ty : ctype)
    (pe2 pe3 : generic_pexpr Unit sym) :
    (Expr a (Eaction (Paction polarity.Pos (Action atLoc empty_annotation
      (Store0 false (tyPe ty) pe2 pe3 NA)))) : CoreExpr) =
      storeOpRedex a atLoc empty_annotation ty pe2 pe3 NA := rfl

theorem createX_eq : createX = createOpRedex [] (locR 16 85 22 23) empty_annotation
    (Pexpr [] () (PEctor Civalignof [tyPe xTy])) (tyPe xTy)
    (PrefSource (loc 22 23) [mainSym, xSym]) := rfl
theorem createR_eq : createR = createOpRedex [] (locR 16 85 33 34) empty_annotation
    (Pexpr [] () (PEctor Civalignof [tyPe rTy])) (tyPe rTy)
    (PrefSource (loc 33 34) [mainSym, rSym]) := rfl

def unspecifiedMval : CerbMem.MemValue := CerbMem.unspecifiedMval rTy
theorem unspecified_encodes [LemFuel] (tds : CerbTags.TagDefsMap) :
    memValueFromValue tds (Ctype [] (unatomic_ rTy)) (Vloaded (LVunspecified rTy)) =
      some unspecifiedMval := rfl
theorem unspecified_storable (tds : CerbTags.TagDefsMap) : StorableAt tds rTy unspecifiedMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- Sufficient total budget: 17 initialization, 55 condition/assignment, 16 return.
Value-literal pairs use explicit budget weakening; no minimality is claimed.
The local supply premise protects the two source cell bindings after the
negative assignment generates a temporary. -/
theorem mainBody_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : HasIntLibrary M.file)
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = returnQ) (hsup : 22 < M.runState.sym_supply)
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs xTy 4 + allocCost M.tagDefs rTy 4)) ⊢
      wpt M p (returnSpec GF) emptyProcSpecT 88 (readoutPost resultPost) mainBody (f :: rest) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapX, HcapR⟩
  rw [mainBody_shape]
  unfold seqE wc
  iapply wpt_seq _ _ _ _ _ _ _ 88 0
  simp only [block, initializeX, initializeR, letS, seqE, wc, bnd, createX_eq, createR_eq, act, store_eq]
  rw [show (Pattern [] (CaseBase (some xSym, ptrBty)) : pattern) = symPat [] xSym ptrBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 85
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [tyPe xTy])) (tyPe xTy)
    (PrefSource (loc 22 23) [mainSym, xSym]) _
    (align := CerbMem.alignofIval M.tagDefs xTy) (ty := xTy) rfl
    (by rw [evalPexpr_ctor1]; unfold tyPe; rw [evalPexpr_val]; rfl) (evalPexpr_val _ _ _ _ _)
  rw [show CerbMem.alignofIval M.tagDefs xTy = .IV .Prov_none 4 from rfl]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 xTy
    (PrefSource (loc 22 23) [mainSym, xSym]) _ (Nat.le_refl 2)
    (int_size_pos [Aloc (loc 18 21)]) (int_nonatomic [Aloc (loc 18 21)])
    (fun a => int_decIndep [Aloc (loc 18 21)] a _)
  isplitl [HcapX]
  · iexact HcapX
  iintro %px ⟨Hx, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some rSym, ptrBty)) : pattern) = symPat [] rSym ptrBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 82
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [tyPe rTy])) (tyPe rTy)
    (PrefSource (loc 33 34) [mainSym, rSym]) _
    (align := CerbMem.alignofIval M.tagDefs rTy) (ty := rTy) rfl
    (by rw [evalPexpr_ctor1]; unfold tyPe; rw [evalPexpr_val]; rfl) (evalPexpr_val _ _ _ _ _)
  rw [show CerbMem.alignofIval M.tagDefs rTy = .IV .Prov_none 4 from rfl]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 rTy
    (PrefSource (loc 33 34) [mainSym, rSym]) _ (Nat.le_refl 2)
    (int_size_pos [Aloc (loc 29 32)]) (int_nonatomic [Aloc (loc 29 32)])
    (fun a => int_decIndep [Aloc (loc 29 32)] a _)
  isplitl [HcapR]
  · iexact HcapR
  iintro %pr ⟨Hr, -⟩
  iexists (Vobject (OVpointer pr))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 7 75
  rw [show (Pattern [] (CaseBase (some (tmp 25), intBty)) : pattern) = symPat [] (tmp 25) intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 4
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  rw [show intLiteral [Aloc (loc 26 27), Aexpr, intValueAnnot] 3 =
    ofValA (.pure [Aloc (loc 26 27), Aexpr, intValueAnnot] [] (lint 3)) from rfl]
  iapply wpt_ofValA (.pure [Aloc (loc 26 27), Aexpr, intValueAnnot] [] (lint 3)) _ (by decide)
  simp only [SpikeVal.val]
  iexists (lint 3)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ xTy (psym xSym) (convLoaded [] xTy (tmp 25)) NA _
    rfl (pv := px) (cv := lint 3)
    (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by emitted_lookup))
    (convLoaded_eval hstd (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest []
      (by emitted_lookup)) (by decide) (by decide))
  iapply wpt_store _ _ _ xTy px (lint 3) NA (emittedIntMval 3) _ _ (Nat.le_refl 3)
    (int_encodes _ [Aloc (loc 18 21)] 3) (int_storable _ [Aloc (loc 18 21)] 3 (by decide) (by decide))
  isplitl [Hx]
  · iexact Hx
  iintro %fpX Hx
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 4 71
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ rTy (psym rSym) (Pexpr [] () (PEval (Vloaded (LVunspecified rTy)))) NA _ rfl
    (pv := pr) (cv := Vloaded (LVunspecified rTy))
    (EmittedIntSupport.symbol_eval hex (by emitted_frame) rest [] (by emitted_lookup))
    (evalPexpr_val _ _ _ _ _)
  iapply wpt_store _ _ _ rTy pr (Vloaded (LVunspecified rTy)) NA unspecifiedMval _ _
    (Nat.le_refl 3) (unspecified_encodes _) (unspecified_storable _)
  isplitl [Hr]
  · iexact Hr
  iintro %fpR Hr
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 55 16
  iapply wpt_t5If hstd hex _ rest (by emitted_frame) px pr _ (by emitted_lookup) (by emitted_lookup)
  isplitl [Hx]
  · iexact Hx
  isplitl [Hr]
  · iexact Hr
  iintro %s %hs Hx Hr
  obtain ⟨k, rfl, hk⟩ := hs
  have hxs : symOrd xSym (fresh_given_int k) ≠ .eq :=
    symOrd_ne_eq_of_num_ne (show 21 ≠ k by omega)
  have hrs : symOrd rSym (fresh_given_int k) ≠ .eq :=
    symOrd_ne_eq_of_num_ne (show 22 ≠ k by omega)
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 16 0
  iapply wpt_t5Return hstd hex hQ _ rest (by emitted_frame) px pr
    (by rw [envAdd_lookup (by emitted_frame), if_neg hxs]; emitted_lookup)
    (by rw [envAdd_lookup (by emitted_frame), if_neg hrs]; emitted_lookup)
  isplitl [Hx]
  · iexact Hx
  iexact Hr
def entryRunState (cmp : EmittedFile.Comparators) (sup : Nat) : core_run_state :=
  (initial_core_run_state sup (collect_labeled_continuations_NEW (restoredFile cmp))).1

theorem entryRunState_main (cmp : EmittedFile.Comparators) (sup : Nat)
    (h : labelUnionCheck cmp = true) :
    fmapLookupBy symCmpL mainSym (entryRunState cmp sup).labeled = some returnQ := by
  change fmapLookupBy symCmpL mainSym
    (collect_labeled_continuations_NEW (restoredFile cmp)) = some returnQ
  rw [main_labels_of_check cmp h, mainBody_saves]

def entryCtx (cmp : EmittedFile.Comparators) (sup : Nat) : MachineCtx :=
  { tagDefs := (restoredFile cmp).tagDefs, file := restoredFile cmp,
    extern := runtimeExtern, tid := 0, parent := none, errno := errnoPtr,
    runState := entryRunState cmp sup }

def entryCtl (sup : Nat) : Ctl :=
  ⟨[], some mainSym, ELoc_normal [(mainSym, CerbLocation.other "Driver.drive")],
    CerbLocation.other "Driver.drive", ⟨sup, 0⟩⟩

def entryThread : thread_state :=
  { arena := mainBody, stack0 := Stack_empty, errno := errnoPtr,
    current_loc := CerbLocation.other "Driver.drive",
    exec_loc := ELoc_normal [(mainSym, CerbLocation.other "Driver.drive")],
    env := [fmapEmpty], current_proc_opt := some mainSym }

theorem entryCtx_labels (cmp : EmittedFile.Comparators) (sup : Nat)
    (hQ : fmapLookupBy symCmpL mainSym (entryRunState cmp sup).labeled = some returnQ) :
    (entryCtx cmp sup).labelsAt (entryCtl sup).proc = returnQ := by
  change (match fmapLookupBy symCmpL (resolveExtern runtimeExtern mainSym)
      (entryRunState cmp sup).labeled with
    | some Q => Q
    | none => fmapEmpty) = returnQ
  rw [runtimeExtern_main, hQ]

theorem entry_budget_fits :
    allocCost fmapEmpty xTy 4 + allocCost fmapEmpty rTy 4 ≤
      headroom prodMem₀.lastAddress := by
  exact prod_two_int_budget_fits

/-- The actual main's per-thread driver delivery. The checked library paths
and collector union establish the file premises, including registration;
the environment map is the one produced by actual startup. -/
theorem mainBody_driver_done [LemFuel] (hfuel : 40 ≤ LemFuel.fuel)
    (cmp : EmittedFile.Comparators) (sup : Nat) (hsup : 22 < sup)
    (hstd : EmittedStdCore.intLibraryCheck cmp.stdlib = true)
    (hlabels : labelUnionCheck cmp = true) :
    DriverDoneAtExtern runtimeExtern mainSym returnQ (restoredFile cmp) entryThread
      mainBody [fmapEmpty] (CerbLocation.other "Driver.drive") ⟨sup, 0⟩
      prodMem₀ resultPost 88 := by
  have hlbl := entryCtx_labels cmp sup (entryRunState_main cmp sup hlabels)
  exact wpt_driver_done_alloc_extern (hfuel := by omega) (GF := SpikeGF)
    (M₀ := entryCtx cmp sup) (ctl := entryCtl sup) (th₀ := entryThread)
    (p := mainSym) (Q := returnQ) rfl hlbl rfl rfl rfl rfl (Nat.le_refl _)
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := returnQ_inv hl
      exact .pure_op rfl (.sym [] (tmp 46)))
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := returnQ_inv hl
      change 1 ≤ LemFuel.fuel
      omega)
    (returnSpec SpikeGF) mainBody fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
    (allocCost fmapEmpty xTy 4 + allocCost fmapEmpty rTy 4) mainBody_frag (Nat.le_trans mainBody_evalDepth hfuel)
    (prodMem₀_launchCoh _ entry_budget_fits) resultPost 88
    (by
      intro inst
      rw [show (entryCtl sup).proc = some mainSym from rfl]
      iintro ⟨-, Hcap⟩
      isplitr [Hcap]
      · iapply returnSpec_valid (M := entryCtx cmp sup) (p := some mainSym) runtimeExtern_compare hlbl
      · have hw := mainBody_wpt (GF := SpikeGF) (M := entryCtx cmp sup)
          (p := some mainSym) (hfuel := by omega)
          (hasIntLibrary_restore cmp hstd) runtimeExtern_compare hlbl
          (by change 22 < sup; exact hsup) fmapEmpty [] symFrame_empty
        rw [show (entryCtx cmp sup).tagDefs = fmapEmpty from rfl] at hw
        iapply hw $$ Hcap)

/-- Complete-file execution at the actual frontend supply. The checked
file/library premises feed the public body proof and derived registration;
startup, errno initialization, driver delivery and finalization are composed
over the shipped semantics. -/
theorem certified_production [LemFuel] (hfuel : 90 ≤ LemFuel.fuel)
    (cmp : EmittedFile.Comparators)
    (hstd : EmittedStdCore.intLibraryCheck cmp.stdlib = true)
    (hmain : mainLookupCheck cmp.funs = true)
    (hlabels : labelUnionCheck cmp = true)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive (restoredFile cmp).tagDefs false (restoredFile cmp) args)
          ((initial_driver_state frontendSupply (restoredFile cmp) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 1 ∧
      dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  refine prod_run_eqJ_file (restoredFile cmp) (restoredFile_tagDefs cmp)
    (restoredFile_globs cmp) mainSym (restoredFile_main cmp)
    (locR 1 85 5 9) (some 20) intBty mainBody (restoredFile_mainLookup cmp hmain)
    frontendSupply (Q := returnQ) ?_ resultPost 88 ?_ (by omega) fs args
  · rw [restoredFile_extern, runtimeExtern_main]
    exact entryRunState_main cmp frontendSupply hlabels
  · rw [restoredFile_extern]
    exact mainBody_driver_done (hfuel := by omega) cmp frontendSupply (by decide) hstd hlabels

/-- Transfer the production equation to the original file and supply when
the retained data and the original comparator checks agree. The executable
frontend comparison tests this connection; it does not discharge these Lean
equality premises or prove correctness of the IO frontend. -/
theorem certified_production_of_capture_eq [LemFuel] (hfuel : 90 ≤ LemFuel.fuel)
    (fallback : EmittedFile.Comparators) (F : file core_run_annotation) (sup : Nat)
    (hdata : EmittedFile.captureData F = data) (hsup : sup = frontendSupply)
    (hstd : EmittedStdCore.intLibraryCheck (EmittedFile.captureComparators fallback F).stdlib = true)
    (hmain : mainLookupCheck (EmittedFile.captureComparators fallback F).funs = true)
    (hlabels : labelUnionCheck (EmittedFile.captureComparators fallback F) = true)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive F.tagDefs false F args) ((initial_driver_state sup F fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 1 ∧
      dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  subst sup
  rw [← EmittedFile.restore_eq_of_data_eq fallback F data hdata]
  exact certified_production hfuel (EmittedFile.captureComparators fallback F) hstd hmain hlabels fs args

end CerberusHeapLang.CorpusA7.T5
