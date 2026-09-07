/-
The emitted t5_ifelse main: a total-correctness proof through public rules.

The transcription is CorpusE0.t5Main. Its constructor skeleton is checked
against docs/corpus-e0/t5_ifelse.annot.core; the checker leaves symbol and
literal identity to transcription review; full-file identity remains A7.
t5_wpt derives a budget of 88 and exposes the initial fresh-symbol floor. t5_certified_production proves
that at ambient fuel at least ninety the shipped driver returns Specified(1)
on prodFileLib stdlibE3 [] t5Main. This file contains the transcribed main and three checked std.core
functions; it is not the complete frontend file and full std.core library.

The condition, assignment and return have separate public-rule derivations.
Every syntactic branch has a Frag witness in Examples/CorpusE5.lean.
-/
import CerberusHeapLang.Examples.EmittedInt
import CerberusHeapLang.Examples.CorpusE5
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.EmittedAExhibit
import CerberusHeapLang.EmittedBExhibit
import CerberusHeapLang.EmittedCExhibit

set_option autoImplicit false
namespace CerberusHeapLang
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (t5a t5rSym t5Load t5Gt t5Cond t5Bool t5GtPats t5CondPats t5BoolPats
  t5Tuple t5TuplePat t5Pure t5Reg t5RegP t5ConvInt t5Unspec
  ptrTy intCty psym specInt convLoadedInt act wc seqE letS letW bnd createInt)

variable {GF : BundledGFunctors}

-- `t5CmpBranch`/`t5CmpBranch_eval`, `t5Tuple_eval` and `t5frAssign` — shared
-- with CorpusT4Exhibit — live in Examples/EmittedInt.lean since the L1
-- landing (2026-09-07): a client must not import a client.

theorem t5Gt_select :
    select_case subst_sym_expr (Vtuple [lint 3, lint 2]) t5GtPats =
      some (Expr [Astd "§6.5.8#6"] (Epure (t5CmpBranch OpGt 3 2))) := rfl

theorem t5Cond_select :
    select_case subst_sym_pexpr (Vtuple [lint 1, lint 0]) t5CondPats =
      some (t5CmpBranch OpEq 1 0) := rfl

def t5BoolBranch : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEnot
    (Pexpr [] () (PEop OpEq (ointPe 0) (ointPe 1)))))
    (Pexpr [] () (PEval Vtrue)) (Pexpr [] () (PEval Vfalse)))

theorem t5Bool_select : select_case subst_sym_expr (lint 0) t5BoolPats =
    some (t5Pure t5BoolBranch) := rfl

theorem t5BoolBranch_eval [LemFuel] {M : MachineCtx} (ρ : EnvStack) :
    evalPexpr M.tagDefs M.extern M.file ρ t5BoolBranch = some Vtrue := by
  rw [t5BoolBranch, evalPexpr_if,
    if_pos (show (isPePure (Pexpr [] () (PEval Vtrue)) &&
      isPePure (Pexpr [] () (PEval Vfalse))) = true from rfl),
    evalPexpr_not, evalPexpr_op, ointPe, ointPe, evalPexpr_val, evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalBinop OpEq (oint 0) (oint 1) = some Vfalse from rfl]
  simp only [Option.bind_some]
  rw [evalPexpr_val]

theorem t5CondPe_eval [LemFuel] {M : MachineCtx} (hstd : StdE3 M.file) {ρ : EnvStack}
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
theorem wpt_t5Load [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
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
      wpt M p Ls Θ 6 Ψ (t5Load x tmp c1 c2) (f :: rest) :=
  wpt_emittedIntLoad hex (t5Reg c1 c2) x (t5a tmp) f rest hf pv bs v hl hload htrap


abbrev t5frGt (px : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (t5a 518) (lint 3) (envAdd (t5a 519) (lint 2)
    (envAdd (t5a 517) (Vobject (OVpointer px)) f))

/-- The emitted comparison reads x=3 and returns Specified(1), retaining
    the load footprint until the surrounding full-expression bound. -/
theorem wpt_t5Gt [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK CorpusE0.xSym f = some (Vobject (OVpointer px))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (threeBytes M.tagDefs) ∗
      (∀ fp, pointsToCell M.tagDefs px (.own 1) intTy (threeBytes M.tagDefs) -∗
        Ψ (.annot [DA_pos [] fp] (lint 1)) (t5frGt px f :: rest))) ⊢
      wpt M p Ls Θ 16 Ψ t5Gt (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold t5Gt
  rw [show t5TuplePat 518 519 =
    tuplePat [] [([], some (t5a 518), CorpusE0.lint), ([], some (t5a 519), CorpusE0.lint)] from rfl]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ 11 5
  iapply wpt_unseq_pure_right _ _ _ (specInt 2) _ 6 (lint 2) rfl rfl (specInt_eval _ 2)
  iapply wpt_t5Load hex CorpusE0.xSym 517 39 40 f rest hf px (threeBytes M.tagDefs)
    (lint 3) hx rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint 3, lint 2], [DA_pos [] fp]
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2]
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_annot
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl (cval := Vtuple [lint 3, lint 2])
    (t5Tuple_eval 518 519 _ _
      (t1sym_eval hex rest (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_pos (by decide)]))
      (t1sym_eval hex rest (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_neg (by decide),
        envAdd_lookup (hf.add _ _), if_pos (by decide)])))
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl t5Gt_select
  iapply wpt_pure (t5CmpBranch OpGt 3 2) _ (Nat.le_refl 2) rfl
    (t5CmpBranch_eval hstd _ OpGt 3 2 true (by decide) (by decide) (by decide) (by decide) rfl)
  simp only [SpikeVal.merge, ↓reduceIte]
  iapply HΨ $$ Hpt

abbrev t5frCond (px : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (t5a 512) (lint 1) (envAdd (t5a 513) (lint 0) (t5frGt px f))

theorem wpt_t5Cond [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK CorpusE0.xSym f = some (Vobject (OVpointer px))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (threeBytes M.tagDefs) ∗
      (pointsToCell M.tagDefs px (.own 1) intTy (threeBytes M.tagDefs) -∗
        Ψ (.pure (lint 0)) (t5frCond px f :: rest))) ⊢
      wpt M p Ls Θ 25 Ψ t5Cond (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold t5Cond bnd
  rw [show (25 : Nat) = 24 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  rw [show t5TuplePat 512 513 =
    tuplePat [] [([], some (t5a 512), CorpusE0.lint), ([], some (t5a 513), CorpusE0.lint)] from rfl]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ 21 3
  iapply wpt_unseq_pure_right _ _ _ (specInt 0) _ 16 (lint 0) rfl rfl (specInt_eval _ 0)
  iapply wpt_t5Gt hstd hex f rest hf px hx
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint 1, lint 0], [DA_pos [] fp]
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2]
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_annot
  have hfg : SymFrame (t5frGt px f) := ((hf.add _ _).add _ _).add _ _
  unfold t5Pure
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl
    (t5CondPe_eval hstd (t5Tuple_eval 512 513 _ _
      (t1sym_eval hex rest (by rw [envAdd_lookup (hfg.add _ _), if_pos (by decide)]))
      (t1sym_eval hex rest (by rw [envAdd_lookup (hfg.add _ _), if_neg (by decide),
        envAdd_lookup hfg, if_pos (by decide)]))))
  simp only [SpikeVal.merge]
  iapply HΨ $$ Hpt

theorem wpt_t5AssignBlock [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
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
      wpt M p Ls Θ 25 Ψ (CorpusE0.t5AssignBlock start n m v) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold CorpusE0.t5AssignBlock wc
  iapply wpt_seq _ _ _ _ _ _ _ 24 1
  iapply wpt_seq _ _ _ _ _ _ _ 23 1
  unfold bnd
  rw [show (Pattern [] (CaseCtor Ctuple
    [Pattern [] (CaseBase (some (t5a n), ptrTy)), Pattern [] (CaseBase (some (t5a m), CorpusE0.lint))]) : pattern) =
    tuplePat [] [([], some (t5a n), ptrTy), ([], some (t5a m), CorpusE0.lint)] from rfl]
  iapply wpt_bound_wseq_tuple _ _ _ _ _ _ _ _ 7 16 rfl
  iapply wpt_unseq_pure_right _ _ _ (specInt v) _ 2 (lint v) rfl rfl (specInt_eval _ v)
  iapply wpt_pure (psym t5rSym) _ (Nat.le_refl 2) rfl (t1sym_eval hex rest hr)
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
  iapply wpt_emittedIntStore hstd hex (t5RegP start (start + 5) (start + 2)) (t5a n) (t5a m) [] v
    (show symOrd (t5a m) (t5a n) ≠ .eq from symOrd_ne_eq_of_num_ne hnm)
    hv1 hv2 f rest hf pr bs
  isplitl [Hpt]
  · iexact Hpt
  iintro %s %hs Hpt
  unfold CorpusE0.t5Unit t5Pure
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply HΨ $$ %s %hs Hpt


theorem wpt_t5Bool [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} (ρ : EnvStack)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym (t5a 510)) = some (lint 0)) :
    Ψ (.pure Vtrue) ρ ⊢ wpt M p Ls Θ 4 Ψ t5Bool ρ := by
  iintro H
  unfold t5Bool
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl hv
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl t5Bool_select
  unfold t5Pure
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (t5BoolBranch_eval _)
  iexact H

def t5RetQ : LabelMap :=
  fmapAddBy symCmpL CorpusE0.retSym ([((t5a 529), CorpusE0.lint)], Expr [] (Epure (psym (t5a 529)))) fmapEmpty

theorem t5RetQ_lookup :
    lookupLabel t5RetQ CorpusE0.retSym = some ([((t5a 529), CorpusE0.lint)], Expr [] (Epure (psym (t5a 529)))) := by
  unfold lookupLabel t5RetQ
  rw [fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

theorem t5RetQ_inv {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t5RetQ l = some (params, cont)) :
    params = [((t5a 529), CorpusE0.lint)] ∧ cont = Expr [] (Epure (psym (t5a 529))) := by
  unfold lookupLabel t5RetQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem t5RetQ_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs [((t5a 529), CorpusE0.lint)] [v] (f :: rest) = envAdd (t5a 529) v f :: rest := by
  show update_env (mk_sym_pat (t5a 529) CorpusE0.lint) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem t5fr529_lookup {f : Fmap sym value} (hf : SymFrame f) (v : value) :
    fmapLookupBy symCmpK (t5a 529) (envAdd (t5a 529) v f) = some v := by
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

def t5LsT (GF : BundledGFunctors) [SpikeGS .hasLC GF] : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜symOrd l CorpusE0.retSym = .eq ∧ m = 2 ∧ vs = [lint 1] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝)

/-- The post: the delivered value is `Specified(1)`. -/
def ψT5 : value → Mem → Prop := fun v _ => v = lint 1

theorem t5LsT_readout [LemFuel] [SpikeGS .hasLC GF] :
    ∀ w ρ', iprop(⌜w = SpikeVal.pure (lint 1)⌝) ⊢ readoutPost (GF := GF) ψT5 w ρ' := by
  intro w ρ'
  iintro %hw
  iintro %σ' %ns %κs %nt -
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  subst hw
  rfl

theorem t5_blockSpecsT [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t5RetQ) :
    ⊢ blockSpecsT (GF := GF) M p (t5LsT GF) emptyProcSpecT (readoutPost ψT5) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [hQ] at hl
  obtain ⟨rfl, rfl⟩ := t5RetQ_inv hl
  dsimp only [t5LsT]
  iintro %hpure
  obtain ⟨-, rfl, rfl, f, rest, hρ, hf⟩ := hpure
  cases hρ
  rw [t5RetQ_bindArgs]
  iapply wpt_pure (psym (t5a 529)) _ (Nat.le_refl 2) rfl
    (t1sym_eval hex _ (t5fr529_lookup hf (lint 1)))
  iapply t5LsT_readout
  ipureintro
  rfl


-- These local tactics only apply the public frame laws. Concrete symbol
-- comparisons are decided by the kernel; fresh symbols need explicit facts.
theorem t5Kill_eq (x : sym) : CorpusE0.t5Kill x =
    killOpRedex [] (t5Reg 0 84) empty_annotation (Static0 intTy) (psym x) := rfl

theorem wpt_t5Return [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t5RetQ)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK CorpusE0.xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK t5rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (threeBytes M.tagDefs) ∗
      pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs 1)) ⊢
      wpt M p (t5LsT GF) emptyProcSpecT 16 Ψ CorpusE0.t5Return (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  simp only [CorpusE0.t5Return, letS, seqE, wc, bnd, t5Kill_eq]
  rw [show (Pattern [] (CaseBase (some (t5a 528), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 528) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 9
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_t5Load hex t5rSym 527 80 81 f rest hf pr (emittedIntBytes M.tagDefs 1) (lint 1) hr rfl rfl
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
  iapply wpt_kill_eval _ _ _ _ _ _ rfl (pv := px) (t1sym_eval hex rest (by emitted_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 intTy) px intTy (threeBytes M.tagDefs) _ (Nat.le_refl 2) rfl
  isplitl [Hx]
  · iexact Hx
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 3
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ _ _ _ _ rfl (pv := pr) (t1sym_eval hex rest (by emitted_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 intTy) pr intTy (emittedIntBytes M.tagDefs 1) _ (Nat.le_refl 2) rfl
  isplitl [Hr]
  · iexact Hr
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 0
  iapply wpt_run [] empty_annotation CorpusE0.retSym [convLoadedInt (t5a 528)] _ _ 2
    (by rw [hQ]; exact t5RetQ_lookup)
    (by rw [evalPexprs_cons, t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by emitted_lookup))
      (by decide) (by decide), evalPexprs_nil]; rfl) (Nat.le_refl 3)
  dsimp only [t5LsT]
  ipureintro
  exact ⟨by decide +kernel, rfl, rfl, _, _, rfl, by emitted_frame⟩

abbrev t5frIf (px pr : CerbMem.PointerValue) (f : Fmap sym value) :=
  t5frAssign 523 524 1 pr (envAdd (t5a 509) Vtrue (envAdd (t5a 510) (lint 0) (t5frCond px f)))

theorem wpt_t5If [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hx : fmapLookupBy symCmpK CorpusE0.xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK t5rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (threeBytes M.tagDefs) ∗
      pointsToCell M.tagDefs pr (.own 1) intTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs px (.own 1) intTy (threeBytes M.tagDefs) -∗
        pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs 1) -∗
        Ψ (.pure Vunit) (envAdd s (lint 1) (t5frIf px pr f) :: rest))) ⊢
      wpt M p Ls Θ 55 Ψ CorpusE0.t5IfStmt (f :: rest) := by
  iintro ⟨Hx, Hr, HΨ⟩
  unfold CorpusE0.t5IfStmt letS
  rw [show (Pattern [] (CaseBase (some (t5a 510), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 510) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 25 30
  iapply wpt_t5Cond hstd hex f rest hf px hx
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iexists (lint 0)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (t5a 509), BTy_boolean)) : pattern) =
    symPat [] (t5a 509) BTy_boolean from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 4 26
  iapply wpt_t5Bool _ (t1sym_eval hex rest (by emitted_lookup))
  iexists Vtrue
  isplit
  · ipureintro; rfl
  rw [update_env_sym, show (26 : Nat) = 25 + 1 from rfl]
  iapply wpt_if_true _ _ _ _ _ (t1sym_eval hex rest (by emitted_lookup))
  iapply wpt_t5AssignBlock hstd hex 48 523 524 1 (by decide) (by decide) (by decide)
    _ rest (by emitted_frame) pr bs (by emitted_lookup)
  isplitl [Hr]
  · iexact Hr
  iintro %s %hs Hr
  iapply HΨ $$ %s %hs Hx Hr

theorem t5Store_eq (a : List annot) (loc : CerbLocation.Loc) (pe2 pe3 : generic_pexpr Unit sym) :
    (Expr a (Eaction (Paction polarity.Pos (Action loc empty_annotation
      (Store0 false intCty pe2 pe3 NA)))) : CoreExpr) =
      storeOpRedex a loc empty_annotation intTy pe2 pe3 NA := rfl

/-- The complete emitted conditional program. The fresh-symbol floor is
    explicit; its purpose is to protect source bindings after assignment.
    The total budget is 17 (initialization) + 55 (conditional) + 16 (return). -/
theorem t5_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = t5RetQ)
    (hsup : 600 ≤ M.runState.sym_supply)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4)) ⊢
      wpt M p (t5LsT GF) emptyProcSpecT 88 (readoutPost ψT5) CorpusE0.t5Main (f :: rest) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapX, HcapR⟩
  simp only [CorpusE0.t5Main, letS, seqE, wc, bnd, createInt_eq, act_store_eq, t5Store_eq]
  rw [show (Pattern [] (CaseBase (some CorpusE0.xSym, ptrTy)) : pattern) =
    symPat [] CorpusE0.xSym ptrTy from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 85
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty
    (PrefSource (t5Reg 15 84) [CorpusE0.xSym]) _
    (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t5Reg 15 84) [CorpusE0.xSym])
    _ (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapX]
  · iexact HcapX
  iintro %px ⟨Hx, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some t5rSym, ptrTy)) : pattern) = symPat [] t5rSym ptrTy from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 82
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty
    (PrefSource (t5Reg 15 84) [t5rSym]) _
    (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t5Reg 15 84) [t5rSym])
    _ (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapR]
  · iexact HcapR
  iintro %pr ⟨Hr, -⟩
  iexists (Vobject (OVpointer pr))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (t5a 508), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 508) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 79
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_pure (specInt 3) _ (Nat.le_refl 2) rfl (specInt_eval _ 3)
  simp only [SpikeVal.val]
  iexists (lint 3)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 4 75
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ intTy (psym CorpusE0.xSym) (convLoadedInt (t5a 508)) NA _
    rfl (pv := px) (cv := lint 3) (t1sym_eval hex rest (by emitted_lookup))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by emitted_lookup)) (by decide) (by decide))
  iapply wpt_store _ _ _ intTy px (lint 3) NA threeMval _ _ (Nat.le_refl 3)
    three_encodes (three_storable _)
  isplitl [Hx]
  · iexact Hx
  iintro %fpX Hx
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 4 71
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ intTy (psym t5rSym) t5Unspec NA _ rfl
    (pv := pr) (cv := Vloaded (LVunspecified intTy)) (t1sym_eval hex rest (by emitted_lookup))
    (unspecIntPe_eval _ _)
  iapply wpt_store _ _ _ intTy pr (Vloaded (LVunspecified intTy)) NA unspecMval _ _
    (Nat.le_refl 3) unspec_encodes (unspec_storable _)
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
  have hxs : symOrd CorpusE0.xSym (fresh_given_int k) ≠ .eq :=
    symOrd_ne_eq_of_num_ne (show 505 ≠ k by omega)
  have hrs : symOrd t5rSym (fresh_given_int k) ≠ .eq :=
    symOrd_ne_eq_of_num_ne (show 506 ≠ k by omega)
  simp only [SpikeVal.mergeInto]
  iapply wpt_t5Return hstd hex hQ _ rest (by emitted_frame) px pr
    (by rw [envAdd_lookup (by emitted_frame), if_neg hxs]; emitted_lookup)
    (by rw [envAdd_lookup (by emitted_frame), if_neg hrs]; emitted_lookup)
  isplitl [Hx]
  · iexact Hx
  iexact Hr

theorem collect_new_t5Main :
    collect_labeled_continuations_NEW (prodFileLib stdlibE3 [] CorpusE0.t5Main) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym t5RetQ fmapEmpty := rfl

theorem t5Main_labeledAt (sup : Nat) :
    LabeledAt (prodRSLib stdlibE3 [] sup CorpusE0.t5Main) mainSym t5RetQ := by
  labeled_main rw [prodRSLib_labeled, collect_new_t5Main]

/-- The shipped driver on the one-procedure file wrapping the transcribed
    t5 main and the checked three-function std.core fragment returns
    Specified(1). The premise `600 ≤ sup` is a SUFFICIENT floor (above every
    source symbol number, so the fresh symbol the assignment protocol draws
    cannot collide with a source binding — the fact t5_wpt exposes), not a
    necessary one: the compiled composite delivers the same result at
    `sup = 0` (measured, docs/2026-09-07_l1-landing-notes.md) — and not
    vacuous: at `sup = 505` (x's symbol number) the composite is KILLED, an
    `Undef0` kill after LemLib's `can_advance: Step_error2 ==> Kill` panic
    (measured; the E5 full-range audit's D-2, re-run at the fixes). The same
    caller fuel instance must provide at least ninety units (cost 88 plus two
    driver iterations). This wrapper certificate leaves the full-file/library
    connection A7 open. -/
theorem t5_certified_production [LemFuel] (hfuel : 90 ≤ LemFuel.fuel)
    (sup : Nat) (hsup : 600 ≤ sup) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 [] CorpusE0.t5Main) args)
          ((initial_driver_state sup (prodFileLib stdlibE3 [] CorpusE0.t5Main) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 1 ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQe := t5Main_labeledAt sup
  have hlbl := prodCtx_labels (f := prodFileLib stdlibE3 [] CorpusE0.t5Main) hQe
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ_lib1 sup stdlibE3 CorpusE0.t5Main hQe ψT5 88
      (wpt_driver_done_alloc (hfuel := by omega) (GF := SpikeGF) (ctl := prodCtl sup)
        (M₀ := prodCtx (prodFileLib stdlibE3 [] CorpusE0.t5Main) (prodRSLib stdlibE3 [] sup CorpusE0.t5Main))
        rfl rfl hlbl rfl rfl rfl rfl (Nat.le_refl _)
        (fun l params cont hl => by
          rw [hlbl] at hl
          obtain ⟨-, rfl⟩ := t5RetQ_inv hl
          exact .pure_op rfl (.sym [] (t5a 529)))
        (fun l params cont hl => by
          rw [hlbl] at hl
          obtain ⟨-, rfl⟩ := t5RetQ_inv hl
          exact (Nat.le_trans (show evalDepth _ ≤ 1 from Nat.le_of_ble_eq_true rfl) (by omega)))
        (t5LsT SpikeGF)
        CorpusE0.t5Main fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
        (allocCost fmapEmpty intTy 4 + allocCost fmapEmpty intTy 4) CorpusE0.t5Main_frag (Nat.le_trans (show evalDepth _ ≤ 40 from Nat.le_of_ble_eq_true rfl) (by omega))
        (prodMem₀_launchCoh _ prod_two_int_budget_fits)
        ψT5 88
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply t5_blockSpecsT (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl
          · iapply t5_wpt (hfuel := by omega) (M := prodCtx (prodFileLib stdlibE3 [] CorpusE0.t5Main) (prodRSLib stdlibE3 [] sup CorpusE0.t5Main))
              rfl (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl hsup fmapEmpty []
              symFrame_empty $$ Hcap))
      hfuel
      fs args
  exact ⟨dres, dst', heq, hψ, hbl, hout, herr⟩

end CerberusHeapLang
