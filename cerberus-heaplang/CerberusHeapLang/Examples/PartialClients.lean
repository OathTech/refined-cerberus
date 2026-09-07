/-
Partial-correctness clients for the seven D5 manifest rows. The complete
CorpusE0.t5Main is verified through the public partial rules, including
its negative-action assignment and its case evaluation. A second client
loads a cell, binds the annotated result, and returns the same value with
its exact read footprint and ownership intact. Helpers are private proof
composition; no logic internals or total-to-partial conversion are used.
-/
import CerberusHeapLang.API
import CerberusHeapLang.Examples.EmittedInt

set_option autoImplicit false
namespace CerberusHeapLang.PartialClients
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (t5a t5rSym t5Load t5Gt t5Cond t5Bool t5GtPats t5CondPats t5BoolPats
  t5Tuple t5TuplePat t5Pure t5Reg t5RegP t5ConvInt t5Unspec
  ptrTy intCty psym specInt convLoadedInt act wc seqE letS letW bnd createInt)

variable {GF : BundledGFunctors}

private theorem alignofIntPe_eval [LemFuel] {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym)
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack) :
    evalPexpr tds ext file ρ (Pexpr [] () (PEctor Civalignof [intCty])) =
      some (Vobject (OVinteger (CerbMem.alignofIval tds intTy))) := by
  simp only [intCty, evalPexpr_tyctor, evalTyCtor_alignof, isTyCtor]

private theorem alignofIval_intTy [LemFuel] {tds : CerbTags.TagDefsMap} :
    CerbMem.alignofIval tds intTy = .IV .Prov_none 4 := rfl

private theorem intTy_size_pos {tds : CerbTags.TagDefsMap} :
    0 < CerbMem.sizeofCtype tds intTy := by
  change 0 < (4 : Nat)
  decide

private theorem intTy_nonatomic : atomicTy intTy = false := rfl

private theorem intTy_decIndep {tds : CerbTags.TagDefsMap} (a : Int)
    (bs : List CerbMem.AbsByte) : decIndep tds a intTy bs := fun _ _ => rfl

private def unspecMval : CerbMem.MemValue := CerbMem.unspecifiedMval intTy

private theorem unspec_encodes [LemFuel] {tds : CerbTags.TagDefsMap} :
    memValueFromValue tds (Ctype [] (unatomic_ intTy)) (Vloaded (LVunspecified intTy)) =
      some unspecMval := rfl

private theorem unspec_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy unspecMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

private theorem unspecIntPe_eval [LemFuel] {tds : CerbTags.TagDefsMap} (ext : Fmap sym sym)
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack) :
    evalPexpr tds ext file ρ t5Unspec = some (Vloaded (LVunspecified intTy)) := by
  simp only [t5Unspec, intCty, evalPexpr_tyctor, evalTyCtor_unspecified, isTyCtor]

private theorem wps_unseq_pure_right [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (a ap : List annot) (e : CoreExpr) (pe : generic_pexpr Unit sym)
    (ρ : EnvStack) (v : value)
    (hcc : ccallFree e = true) (hnv : valueFromPexpr pe = none)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ pe = some v) :
    wps M p Ls Θ (fun w ρ' => Ψ (w.mergeInto (.annot [] (Vtuple [w.val, v]))) ρ') e ρ ⊢
      wps M p Ls Θ Ψ (Expr a (Eunseq [e, Expr ap (Epure pe)])) ρ := by
  iintro H
  rw [show ([e, Expr ap (Epure pe)] : List CoreExpr) = [e] ++ Expr ap (Epure pe) :: [] from rfl]
  iapply wps_unseq_focus a [e] (Expr ap (Epure pe)) [] ρ
    rfl (by simpa only [List.append_nil, ccallFreeList, Bool.and_true] using hcc)
  iapply wps_pure pe ρ hnv hv
  iintro %wa %hwa
  cases wa with
  | annot _ _ _ _ _ => cases hwa
  | pure aa ab av =>
  have hav : av = v := SpikeVal.pure.inj hwa
  subst av
  rw [show ([e] ++ ofValA (.pure aa ab v) :: [] : List CoreExpr) =
    [] ++ e :: [ofValA (.pure aa ab v)] from rfl]
  iapply wps_unseq_focus a [] e [ofValA (.pure aa ab v)] ρ
    (by rw [valsOnly_cons, isValE_ofValA, valsOnly_nil])
    (by simp only [List.nil_append, ccallFreeList, ccallFree_ofValA])
  iapply wps_wand e ρ $$ H
  iintro %w %ρ' HΨ %wb %hwb
  cases wb with
  | pure ba bb bv =>
    cases hwb
    rw [show ([] ++ ofValA (.pure ba bb bv) :: [ofValA (.pure aa ab v)] : List CoreExpr) =
      [SpikeValA.pure ba bb bv, .pure aa ab v].map ofValA from rfl]
    iapply wps_unseq_vals a _ ρ' (fps := []) (cvals := [bv, v]) rfl
    simp only [SpikeValA.erase_pure, SpikeVal.mergeInto, SpikeVal.val]
    iexact HΨ
  | annot ba bb bc ds bv =>
    cases hwb
    rw [show ([] ++ ofValA (.annot ba bb bc ds bv) :: [ofValA (.pure aa ab v)] : List CoreExpr) =
      [SpikeValA.annot ba bb bc ds bv, .pure aa ab v].map ofValA from rfl]
    iapply wps_unseq_vals a _ ρ' (fps := ds) (cvals := [bv, v])
      (by simp only [collectUnseq, do_race_nil_right, Bool.false_eq_true, ↓reduceIte,
        combine_dyn_annotations, List.append_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append])
    simp only [SpikeValA.erase_annot, SpikeVal.val, SpikeVal.mergeInto, SpikeVal.merge, List.append_nil]
    iexact HΨ

private theorem wps_emittedIntStore [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (loc : CerbLocation.Loc) (n m : sym) (ds : List dyn_annotation) (v : Int)
    (hnm : symOrd m n ≠ .eq) (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) intTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pv (.own 1) intTy (emittedIntBytes M.tagDefs v) -∗
        Ψ (.pure (lint v)) (envAdd s (lint v)
          (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f)) :: rest))) ⊢
      wps M p Ls Θ Ψ
        (Expr [Astd "§6.5#2"] (Ebound
          (negAssignBody [] [] [Astd "§6.5.16.1#2, store"] [] [] ds BTy_unit
            loc empty_annotation intTy (psym n) (CorpusE0.convLoadedInt m) (CorpusE0.convLoadedInt m) NA)))
        (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f) :: rest) := by
  have hlp := t1sym_eval hex rest (by
    rw [envAdd_lookup (hf.add m (lint v)), if_pos (symOrd_self n)] :
      fmapLookupBy symCmpK n (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f)) =
        some (Vobject (OVpointer pv)))
  have hlv := t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by
    rw [envAdd_lookup (hf.add m (lint v)), if_neg hnm, envAdd_lookup hf, if_pos (symOrd_self m)] :
      fmapLookupBy symCmpK m (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f)) = some (lint v))) hv1 hv2
  exact wps_neg_bound [Astd "§6.5#2"] [] [] [Astd "§6.5.16.1#2, store"] [] [] ds BTy_unit
    loc empty_annotation intTy (psym n) (CorpusE0.convLoadedInt m) (CorpusE0.convLoadedInt m) NA
    (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f)) rest ((hf.add _ _).add _ _)
    (emittedIntMval v) bs hex rfl hlp hlv rfl hlv
    (emittedInt_encodes _ v) (emittedInt_storable _ v hv1 hv2)



private theorem t5Gt_select :
    select_case subst_sym_expr (Vtuple [lint 3, lint 2]) t5GtPats =
      some (Expr [Astd "§6.5.8#6"] (Epure (t5CmpBranch OpGt 3 2))) := rfl

private theorem t5Cond_select :
    select_case subst_sym_pexpr (Vtuple [lint 1, lint 0]) t5CondPats =
      some (t5CmpBranch OpEq 1 0) := rfl

private def t5BoolBranch : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEnot
    (Pexpr [] () (PEop OpEq (ointPe 0) (ointPe 1)))))
    (Pexpr [] () (PEval Vtrue)) (Pexpr [] () (PEval Vfalse)))

private theorem t5Bool_select : select_case subst_sym_expr (lint 0) t5BoolPats =
    some (t5Pure t5BoolBranch) := rfl

private theorem t5BoolBranch_eval [LemFuel] {M : MachineCtx} (ρ : EnvStack) :
    evalPexpr M.tagDefs M.extern M.file ρ t5BoolBranch = some Vtrue := by
  rw [t5BoolBranch, evalPexpr_if,
    if_pos (show (isPePure (Pexpr [] () (PEval Vtrue)) &&
      isPePure (Pexpr [] () (PEval Vfalse))) = true from rfl),
    evalPexpr_not, evalPexpr_op, ointPe, ointPe, evalPexpr_val, evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalBinop OpEq (oint 0) (oint 1) = some Vfalse from rfl]
  simp only [Option.bind_some]
  rw [evalPexpr_val]

private theorem t5CondPe_eval [LemFuel] {M : MachineCtx} (hstd : StdE3 M.file) {ρ : EnvStack}
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (t5Tuple 512 513) =
      some (Vtuple [lint 1, lint 0])) :
    evalPexpr M.tagDefs M.extern M.file ρ
      (Pexpr [] () (PEcase (t5Tuple 512 513) t5CondPats)) = some (lint 0) := by
  rw [evalPexpr_case, if_pos (show isPePureAlts t5CondPats = true from rfl), hv]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [t5Cond_select]
  change evalPexpr M.tagDefs M.extern M.file ρ (t5CmpBranch OpEq 1 0) = some (lint 0)
  exact t5CmpBranch_eval hstd ρ OpEq 1 0 false (by decide) (by decide) (by decide) (by decide) rfl

/-- A whole integer load with the emitted temporary binder, using the
    public whole-cell rule and preserving the caller's postcondition. -/
private theorem wps_t5Load [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (x : sym) (tmp c1 c2 : Nat) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : SymFrame f) (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv intTy bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) intTy bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) intTy bs -∗
        Ψ (.annot [DA_pos [] fp] v) (envAdd (t5a tmp) (Vobject (OVpointer pv)) f :: rest))) ⊢
      wps M p Ls Θ Ψ (t5Load x tmp c1 c2) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold t5Load CorpusE0.emittedIntLoad letW
  rw [show (Pattern [] (CaseBase (some (t5a tmp), ptrTy)) : pattern) =
    symPat [] (t5a tmp) ptrTy from rfl]
  iapply wps_wseq_sym _ _ _ _ _ _ _ _
  iapply wps_pure (psym x) _ rfl (t1sym_eval hex rest hl)
  iexists (Vobject (OVpointer pv))
  isplit
  · ipureintro; rfl
  rw [update_env_sym, act_load_eq]
  iapply wps_load_eval _ _ _ _ _ _ _ rfl (pv := pv)
    (t1sym_eval hex rest (by rw [envAdd_lookup hf, if_pos (symOrd_self _)]))
  iapply wps_load_footprint _ _ _ _ pv _ (.own 1) bs _ htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro Hpt
  rw [hload]
  iapply HΨ $$ Hpt



private abbrev t5frGt (px : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (t5a 518) (lint 3) (envAdd (t5a 519) (lint 2)
    (envAdd (t5a 517) (Vobject (OVpointer px)) f))

/-- The emitted comparison reads x=3 and returns Specified(1), retaining
    the load footprint until the surrounding full-expression bound. -/
private theorem wps_t5Gt [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK CorpusE0.xSym f = some (Vobject (OVpointer px))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (emittedIntBytes M.tagDefs 3) ∗
      (∀ fp, pointsToCell M.tagDefs px (.own 1) intTy (emittedIntBytes M.tagDefs 3) -∗
        Ψ (.annot [DA_pos [] fp] (lint 1)) (t5frGt px f :: rest))) ⊢
      wps M p Ls Θ Ψ t5Gt (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold t5Gt
  rw [show t5TuplePat 518 519 =
    tuplePat [] [([], some (t5a 518), CorpusE0.lint), ([], some (t5a 519), CorpusE0.lint)] from rfl]
  iapply wps_wseq_tuple_annot _ _ _ _ _ _ _
  iapply wps_unseq_pure_right _ _ _ (specInt 2) _ (lint 2) rfl rfl (specInt_eval _ 2)
  iapply wps_t5Load hex CorpusE0.xSym 517 39 40 f rest hf px (emittedIntBytes M.tagDefs 3)
    (lint 3) hx rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint 3, lint 2], [DA_pos [] fp]
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  iapply wps_annot
  iapply wps_case_eval _ _ _ _ rfl (cval := Vtuple [lint 3, lint 2])
    (t5Tuple_eval 518 519 _ _
      (t1sym_eval hex rest (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_pos (by decide)]))
      (t1sym_eval hex rest (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_neg (by decide),
        envAdd_lookup (hf.add _ _), if_pos (by decide)])))
  iapply wps_case_value _ _ _ _ rfl t5Gt_select
  iapply wps_pure (t5CmpBranch OpGt 3 2) _ rfl
    (t5CmpBranch_eval hstd _ OpGt 3 2 true (by decide) (by decide) (by decide) (by decide) rfl)
  simp only [SpikeVal.merge, ↓reduceIte]
  iapply HΨ $$ Hpt

private abbrev t5frCond (px : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (t5a 512) (lint 1) (envAdd (t5a 513) (lint 0) (t5frGt px f))

private theorem wps_t5Cond [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK CorpusE0.xSym f = some (Vobject (OVpointer px))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (emittedIntBytes M.tagDefs 3) ∗
      (pointsToCell M.tagDefs px (.own 1) intTy (emittedIntBytes M.tagDefs 3) -∗
        Ψ (.pure (lint 0)) (t5frCond px f :: rest))) ⊢
      wps M p Ls Θ Ψ t5Cond (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold t5Cond bnd
  iapply wps_bound _ _ _ rfl
  rw [show t5TuplePat 512 513 =
    tuplePat [] [([], some (t5a 512), CorpusE0.lint), ([], some (t5a 513), CorpusE0.lint)] from rfl]
  iapply wps_wseq_tuple_annot _ _ _ _ _ _ _
  iapply wps_unseq_pure_right _ _ _ (specInt 0) _ (lint 0) rfl rfl (specInt_eval _ 0)
  iapply wps_t5Gt hstd hex f rest hf px hx
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint 1, lint 0], [DA_pos [] fp]
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  iapply wps_annot
  have hfg : SymFrame (t5frGt px f) := ((hf.add _ _).add _ _).add _ _
  unfold t5Pure
  iapply wps_pure _ _ rfl
    (t5CondPe_eval hstd (t5Tuple_eval 512 513 _ _
      (t1sym_eval hex rest (by rw [envAdd_lookup (hfg.add _ _), if_pos (by decide)]))
      (t1sym_eval hex rest (by rw [envAdd_lookup (hfg.add _ _), if_neg (by decide),
        envAdd_lookup hfg, if_pos (by decide)]))))
  simp only [SpikeVal.merge]
  iapply HΨ $$ Hpt

private theorem wps_t5AssignBlock [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (start n m : Nat) (v : Int) (hnm : m ≠ n)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hr : fmapLookupBy symCmpK t5rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) pr (.own 1) intTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs v) -∗
        Ψ (.pure Vunit) (envAdd s (lint v) (t5frAssign n m v pr f) :: rest))) ⊢
      wps M p Ls Θ Ψ (CorpusE0.t5AssignBlock start n m v) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold CorpusE0.t5AssignBlock wc
  iapply wps_seq _ _ _ _ _ _ _
  iapply wps_seq _ _ _ _ _ _ _
  unfold bnd
  rw [show (Pattern [] (CaseCtor Ctuple
    [Pattern [] (CaseBase (some (t5a n), ptrTy)), Pattern [] (CaseBase (some (t5a m), CorpusE0.lint))]) : pattern) =
    tuplePat [] [([], some (t5a n), ptrTy), ([], some (t5a m), CorpusE0.lint)] from rfl]
  iapply wps_bound_wseq_tuple _ _ _ _ _ _ _ _ rfl
  iapply wps_unseq_pure_right _ _ _ (specInt v) _ (lint v) rfl rfl (specInt_eval _ v)
  iapply wps_pure (psym t5rSym) _ rfl (t1sym_eval hex rest hr)
  simp only [SpikeVal.mergeInto, SpikeVal.val]
  iexists [Vobject (OVpointer pr), lint v], []
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  rw [show (Expr [] (Eannot [] (Expr [] (Ewseq (Pattern [] (CaseBase (none, BTy_unit)))
      (Expr [Astd "§6.5.16.1#2, store"] (Eaction (Paction polarity.Neg0
        (Action (t5RegP start (start + 5) (start + 2)) empty_annotation
          (Store0 false intCty (psym (t5a n)) (convLoadedInt (t5a m)) NA)))))
      (t5Pure (convLoadedInt (t5a m)))))) : CoreExpr) =
    negAssignBody [] [] [Astd "§6.5.16.1#2, store"] [] [] [] BTy_unit
      (t5RegP start (start + 5) (start + 2)) empty_annotation intTy
      (psym (t5a n)) (convLoadedInt (t5a m)) (convLoadedInt (t5a m)) NA from rfl]
  iapply wps_emittedIntStore hstd hex (t5RegP start (start + 5) (start + 2)) (t5a n) (t5a m) [] v
    (show symOrd (t5a m) (t5a n) ≠ .eq from symOrd_ne_eq_of_num_ne hnm)
    hv1 hv2 f rest hf pr bs
  isplitl [Hpt]
  · iexact Hpt
  iintro %s %hs Hpt
  unfold CorpusE0.t5Unit t5Pure
  rw [← ofValA_pure [] [] Vunit]
  iapply wps_ofValA (.pure [] [] Vunit) _
  simp only [SpikeValA.erase_pure]
  iapply wps_ofValA (.pure [] [] Vunit) _
  simp only [SpikeValA.erase_pure]
  iapply HΨ $$ %s %hs Hpt


private theorem wps_t5Bool [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} (ρ : EnvStack)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym (t5a 510)) = some (lint 0)) :
    Ψ (.pure Vtrue) ρ ⊢ wps M p Ls Θ Ψ t5Bool ρ := by
  iintro H
  unfold t5Bool
  iapply wps_case_eval _ _ _ _ rfl hv
  iapply wps_case_value _ _ _ _ rfl t5Bool_select
  unfold t5Pure
  iapply wps_pure _ _ rfl (t5BoolBranch_eval _)
  iexact H

def t5RetQ : LabelMap :=
  fmapAddBy symCmpL CorpusE0.retSym ([((t5a 529), CorpusE0.lint)], Expr [] (Epure (psym (t5a 529)))) fmapEmpty

private theorem t5RetQ_lookup :
    lookupLabel t5RetQ CorpusE0.retSym = some ([((t5a 529), CorpusE0.lint)], Expr [] (Epure (psym (t5a 529)))) := by
  unfold lookupLabel t5RetQ
  rw [fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

private theorem t5RetQ_inv {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t5RetQ l = some (params, cont)) :
    params = [((t5a 529), CorpusE0.lint)] ∧ cont = Expr [] (Epure (psym (t5a 529))) := by
  unfold lookupLabel t5RetQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

private theorem t5RetQ_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs [((t5a 529), CorpusE0.lint)] [v] (f :: rest) = envAdd (t5a 529) v f :: rest := by
  show update_env (mk_sym_pat (t5a 529) CorpusE0.lint) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

private theorem t5fr529_lookup {f : Fmap sym value} (hf : SymFrame f) (v : value) :
    fmapLookupBy symCmpK (t5a 529) (envAdd (t5a 529) v f) = some v := by
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

def t5Ls (GF : BundledGFunctors) [SpikeGS .hasLC GF] : LabelSpec GF := fun l vs ρ =>
  iprop(⌜symOrd l CorpusE0.retSym = .eq ∧ vs = [lint 1] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝)

/-- The post: the delivered value is `Specified(1)`. -/
def ψT5 : value → Mem → Prop := fun v _ => v = lint 1

private theorem t5Ls_readout [LemFuel] [SpikeGS .hasLC GF] :
    ∀ w ρ', iprop(⌜w = SpikeVal.pure (lint 1)⌝) ⊢ readoutPost (GF := GF) ψT5 w ρ' := by
  intro w ρ'
  iintro %hw
  iintro %σ' %ns %κs %nt -
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  subst hw
  rfl

theorem t5_blockSpecs [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t5RetQ) :
    ⊢ blockSpecs (GF := GF) M p (t5Ls GF) emptyProcSpec (readoutPost ψT5) := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  rw [hQ] at hl
  obtain ⟨rfl, rfl⟩ := t5RetQ_inv hl
  dsimp only [t5Ls]
  iintro %hpure
  obtain ⟨-, rfl, f, rest, hρ, hf⟩ := hpure
  cases hρ
  rw [t5RetQ_bindArgs]
  iapply wps_pure (psym (t5a 529)) _ rfl
    (t1sym_eval hex _ (t5fr529_lookup hf (lint 1)))
  iapply t5Ls_readout
  ipureintro
  rfl


-- These local tactics only apply the public frame laws. Concrete symbol
-- comparisons are decided by the kernel; fresh symbols need explicit facts.
local macro "t5_frame" : tactic => `(tactic| repeat first | assumption | apply SymFrame.add)
local macro "t5_lookup" : tactic => `(tactic|
  (repeat first
    | rw [envAdd_lookup (by t5_frame), if_pos (by decide +kernel)]
    | rw [envAdd_lookup (by t5_frame), if_neg (by decide +kernel)]) <;> assumption)

private theorem t5Kill_eq (x : sym) : CorpusE0.t5Kill x =
    killOpRedex [] (t5Reg 0 84) empty_annotation (Static0 intTy) (psym x) := rfl

private theorem wps_t5Return [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t5RetQ)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK CorpusE0.xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK t5rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (emittedIntBytes M.tagDefs 3) ∗
      pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs 1)) ⊢
      wps M p (t5Ls GF) emptyProcSpec Ψ CorpusE0.t5Return (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  simp only [CorpusE0.t5Return, letS, seqE, wc, bnd, t5Kill_eq]
  rw [show (Pattern [] (CaseBase (some (t5a 528), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 528) CorpusE0.lint from rfl]
  iapply wps_seq_sym _ _ _ _ _ _ _ _
  iapply wps_bound _ _ _ rfl
  iapply wps_t5Load hex t5rSym 527 80 81 f rest hf pr (emittedIntBytes M.tagDefs 1) (lint 1) hr rfl rfl
  isplitl [Hr]
  · iexact Hr
  iintro %fp Hr
  simp only [SpikeVal.val]
  iexists (lint 1)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wps_seq _ _ _ _ _ _ _
  iapply wps_kill_eval _ _ _ _ _ _ rfl (pv := px) (t1sym_eval hex rest (by t5_lookup))
  iapply wps_kill_emp _ _ _ (Static0 intTy) px intTy (emittedIntBytes M.tagDefs 3) _ rfl
  isplitl [Hx]
  · iexact Hx
  simp only [SpikeVal.mergeInto]
  iapply wps_seq _ _ _ _ _ _ _
  iapply wps_kill_eval _ _ _ _ _ _ rfl (pv := pr) (t1sym_eval hex rest (by t5_lookup))
  iapply wps_kill_emp _ _ _ (Static0 intTy) pr intTy (emittedIntBytes M.tagDefs 1) _ rfl
  isplitl [Hr]
  · iexact Hr
  simp only [SpikeVal.mergeInto]
  iapply wps_seq _ _ _ _ _ _ _
  iapply wps_run [] empty_annotation CorpusE0.retSym [convLoadedInt (t5a 528)] _ _
    (by rw [hQ]; exact t5RetQ_lookup)
    (by rw [evalPexprs_cons, t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by t5_lookup))
      (by decide) (by decide), evalPexprs_nil]; rfl)
  dsimp only [t5Ls]
  ipureintro
  exact ⟨by decide +kernel, rfl, _, _, rfl, by t5_frame⟩

private abbrev t5frIf (px pr : CerbMem.PointerValue) (f : Fmap sym value) :=
  t5frAssign 523 524 1 pr (envAdd (t5a 509) Vtrue (envAdd (t5a 510) (lint 0) (t5frCond px f)))

private theorem wps_t5If [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hx : fmapLookupBy symCmpK CorpusE0.xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK t5rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (emittedIntBytes M.tagDefs 3) ∗
      pointsToCell M.tagDefs pr (.own 1) intTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs px (.own 1) intTy (emittedIntBytes M.tagDefs 3) -∗
        pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs 1) -∗
        Ψ (.pure Vunit) (envAdd s (lint 1) (t5frIf px pr f) :: rest))) ⊢
      wps M p Ls Θ Ψ CorpusE0.t5IfStmt (f :: rest) := by
  iintro ⟨Hx, Hr, HΨ⟩
  unfold CorpusE0.t5IfStmt letS
  rw [show (Pattern [] (CaseBase (some (t5a 510), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 510) CorpusE0.lint from rfl]
  iapply wps_seq_sym _ _ _ _ _ _ _ _
  iapply wps_t5Cond hstd hex f rest hf px hx
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iexists (lint 0)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (t5a 509), BTy_boolean)) : pattern) =
    symPat [] (t5a 509) BTy_boolean from rfl]
  iapply wps_seq_sym _ _ _ _ _ _ _ _
  iapply wps_t5Bool _ (t1sym_eval hex rest (by t5_lookup))
  iexists Vtrue
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wps_if_true _ _ _ _ _ (t1sym_eval hex rest (by t5_lookup))
  iapply wps_t5AssignBlock hstd hex 48 523 524 1 (by decide) (by decide) (by decide)
    _ rest (by t5_frame) pr bs (by t5_lookup)
  isplitl [Hr]
  · iexact Hr
  iintro %s %hs Hr
  iapply HΨ $$ %s %hs Hx Hr

private theorem t5Store_eq (a : List annot) (loc : CerbLocation.Loc) (pe2 pe3 : generic_pexpr Unit sym) :
    (Expr a (Eaction (Paction polarity.Pos (Action loc empty_annotation
      (Store0 false intCty pe2 pe3 NA)))) : CoreExpr) =
      storeOpRedex a loc empty_annotation intTy pe2 pe3 NA := rfl

/-- Partial correctness of the complete emitted t5 program. The freshness
    premise protects the two source bindings used after the assignment;
    it carries no numeric supply or execution bound. `hfuel` is the public
    allocation rule's own premise at the L2 pin (`wps_create`: positive
    memory-bind fuel), not a bound introduced by this proof. -/
theorem t5_wps [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = t5RetQ)
    (hfresh : ∀ k, M.runState.sym_supply ≤ k →
      symOrd CorpusE0.xSym (fresh_given_int k) ≠ .eq ∧
      symOrd t5rSym (fresh_given_int k) ≠ .eq)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4)) ⊢
      wps M p (t5Ls GF) emptyProcSpec (readoutPost ψT5) CorpusE0.t5Main (f :: rest) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapX, HcapR⟩
  simp only [CorpusE0.t5Main, letS, seqE, wc, bnd, createInt_eq, act_store_eq, t5Store_eq]
  rw [show (Pattern [] (CaseBase (some CorpusE0.xSym, ptrTy)) : pattern) =
    symPat [] CorpusE0.xSym ptrTy from rfl]
  iapply wps_seq_sym _ _ _ _ _ _ _ _
  iapply wps_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty
    (PrefSource (t5Reg 15 84) [CorpusE0.xSym]) _
    (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wps_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t5Reg 15 84) [CorpusE0.xSym])
    _ intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapX]
  · iexact HcapX
  iintro %px ⟨Hx, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some t5rSym, ptrTy)) : pattern) = symPat [] t5rSym ptrTy from rfl]
  iapply wps_seq_sym _ _ _ _ _ _ _ _
  iapply wps_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty
    (PrefSource (t5Reg 15 84) [t5rSym]) _
    (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wps_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t5Reg 15 84) [t5rSym])
    _ intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapR]
  · iexact HcapR
  iintro %pr ⟨Hr, -⟩
  iexists (Vobject (OVpointer pr))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (t5a 508), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 508) CorpusE0.lint from rfl]
  iapply wps_seq_sym _ _ _ _ _ _ _ _
  iapply wps_bound _ _ _ rfl
  iapply wps_pure (specInt 3) _ rfl (specInt_eval _ 3)
  simp only [SpikeVal.val]
  iexists (lint 3)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wps_seq _ _ _ _ _ _ _
  iapply wps_store_eval _ _ _ intTy (psym CorpusE0.xSym) (convLoadedInt (t5a 508)) NA _
    rfl (pv := px) (cv := lint 3) (t1sym_eval hex rest (by t5_lookup))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by t5_lookup)) (by decide) (by decide))
  iapply wps_store _ _ _ intTy px (lint 3) NA (emittedIntMval 3) _ _
    (emittedInt_encodes _ 3) (emittedInt_storable _ 3 (by decide) (by decide))
  isplitl [Hx]
  · iexact Hx
  iintro %fpX Hx
  simp only [SpikeVal.mergeInto]
  iapply wps_seq _ _ _ _ _ _ _
  iapply wps_store_eval _ _ _ intTy (psym t5rSym) t5Unspec NA _ rfl
    (pv := pr) (cv := Vloaded (LVunspecified intTy)) (t1sym_eval hex rest (by t5_lookup))
    (unspecIntPe_eval _ _)
  iapply wps_store _ _ _ intTy pr (Vloaded (LVunspecified intTy)) NA unspecMval _ _
    unspec_encodes (unspec_storable _)
  isplitl [Hr]
  · iexact Hr
  iintro %fpR Hr
  simp only [SpikeVal.mergeInto]
  iapply wps_seq _ _ _ _ _ _ _
  iapply wps_t5If hstd hex _ rest (by t5_frame) px pr _ (by t5_lookup) (by t5_lookup)
  isplitl [Hx]
  · iexact Hx
  isplitl [Hr]
  · iexact Hr
  iintro %s %hs Hx Hr
  obtain ⟨k, rfl, hk⟩ := hs
  obtain ⟨hxs, hrs⟩ := hfresh k hk
  simp only [SpikeVal.mergeInto]
  iapply wps_t5Return hstd hex hQ _ rest (by t5_frame) px pr
    (by rw [envAdd_lookup (by t5_frame), if_neg hxs]; t5_lookup)
    (by rw [envAdd_lookup (by t5_frame), if_neg hrs]; t5_lookup)
  isplitl [Hx]
  · iexact Hx
  iexact Hr


/-- Read an integer cell, strongly bind the annotated result, then return
    the bound value. The load's read footprint remains on the result. -/
def loadBind (loc : CerbLocation.Loc) (ann : core_run_annotation) (x : sym)
    (pv : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Esseq (symPat [] x CorpusE0.lint) (loadExpr [] loc ann intTy pv NA)
    (Expr [] (Epure (psym x))))

theorem loadBind_wps [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (x : sym)
    (pv : CerbMem.PointerValue) (dq : DFrac) (bs : List CerbMem.AbsByte)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, intTy, bs⟩ = false) :
    pointsToCell M.tagDefs (GF := GF) pv dq intTy bs ⊢
      wps M p Ls Θ
        (fun w ρ => iprop(⌜w = .annot [DA_pos [] (loadFootprint M.tagDefs pv intTy)]
            (loadedVal M.tagDefs pv intTy bs) ∧
          ρ = envAdd x (loadedVal M.tagDefs pv intTy bs) f :: rest⌝ ∗
          pointsToCell M.tagDefs pv dq intTy bs))
        (loadBind loc ann x pv) (f :: rest) := by
  iintro Hpt
  unfold loadBind
  iapply wps_seq_sym_annot _ _ _ _ _ _ _ _
  iapply wps_load_footprint _ _ _ _ _ _ dq bs _ htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro Hpt
  iexists (loadedVal M.tagDefs pv intTy bs), [DA_pos [] (loadFootprint M.tagDefs pv intTy)]
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wps_annot
  iapply wps_pure (psym x) _ rfl
    (t1sym_eval hex rest (by rw [envAdd_lookup hf, if_pos (symOrd_self x)]))
  simp only [SpikeVal.merge]
  isplit
  · ipureintro; simp
  · iexact Hpt

end CerberusHeapLang.PartialClients
