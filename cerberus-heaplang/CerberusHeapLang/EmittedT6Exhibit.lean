/- Public total proof and genuine-driver certificate for the complete captured t6 file. -/
import CerberusHeapLang.Examples.EmittedT6
import CerberusHeapLang.EmittedIntSupport
import CerberusHeapLang.ProdEntry

set_option autoImplicit false
namespace CerberusHeapLang.CorpusA7.T6
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (psym seqE letS letW bnd act specInt wc)
open EmittedStdCore (sintTyAnn HasIntLibrary)
open EmittedIntSupport
variable {GF : BundledGFunctors}

private theorem psym_eval [LemFuel] {M : MachineCtx}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    {x : sym} {f : Fmap sym value} {v : value} (hf : SymFrame f)
    (rest : EnvStack) (hl : fmapLookupBy symCmpK x f = some v) :
    evalPexpr M.tagDefs M.extern M.file (f :: rest) (psym x) = some v :=
  symbol_eval hex hf rest [] hl

private theorem convLoaded_eval [LemFuel] {M : MachineCtx} {ρ : EnvStack}
    (h : HasIntLibrary M.file) {ta : List annot} {s : sym} {n : Int}
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym s) = some (lint n))
    (hlo : -2147483648 ≤ n) (hhi : n ≤ 2147483647) :
    evalPexpr M.tagDefs M.extern M.file ρ (convLoaded (sintTyAnn ta) s) = some (lint n) :=
  EmittedStdCore.eval_convLoadedInt_spec [] h (evalPexpr_val _ _ _ _ _) hv hlo hhi

def caseContext (body : CoreExpr) : CoreExpr :=
  seqE (seqE (Expr [Aloc (loc 40 124), Astmt]
    (Esseq wc (seqE body unitE) afterSwitch)) (seqE returnStmt cleanup)) returnSave

def case1Cont : CoreExpr := caseContext
  (Expr [Aloc (loc 51 124), Astmt] (Esseq wc (assignStmt 61 42 43 10)
    (seqE (run [Aloc (loc 69 75), Astmt] breakSym) case2Tail)))
def case2Cont : CoreExpr := caseContext
  (seqE (assignStmt 84 44 45 20)
    (seqE (run [Aloc (loc 92 98), Astmt] breakSym) defaultTail))
def defaultCont : CoreExpr := caseContext
  (seqE (assignStmt 108 46 47 30)
    (seqE (run [Aloc (loc 116 122), Astmt] breakSym) unitE))
def breakCont : CoreExpr :=
  seqE (seqE (seqE (Expr [Aloc (loc 40 124), Astmt]
    (Epure (Pexpr [] () (PEval Vunit)))) unitE) (seqE returnStmt cleanup)) returnSave

def ptrParams : List (sym × core_base_type) := [(xSym, ptrBty), (rSym, ptrBty)]
def retParams : List (sym × core_base_type) := [(tmp 50, intBty)]
def retCont : CoreExpr := pureE (psym (tmp 50))
def Q : LabelMap := collect_saves mainBody

/-- Exact save map, including all five continuations and retained suffixes.
As with complete-file main registration, the ordinary kernel checks the
reflexivity term synchronously; no native evaluation supplies this equality. -/
theorem Q_eq : Q =
    fmapAddBy symCmpL case1Sym (ptrParams, case1Cont)
      (fmapAddBy symCmpL breakSym (ptrParams, breakCont)
      (fmapAddBy symCmpL defaultSym (ptrParams, defaultCont)
      (fmapAddBy symCmpL retSym (retParams, retCont)
      (fmapAddBy symCmpL case2Sym (ptrParams, case2Cont) fmapEmpty)))) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let some (_, _, rhs) := target.eq? | throwError "expected an equality"
    let proof ← Lean.Meta.mkEqRefl rhs
    let lemmaName ← Lean.withOptions (Lean.Elab.async.set · false) do
      Lean.Meta.mkAuxLemma [] target proof
    goal.assign (Lean.mkConst lemmaName)
    Lean.Elab.Tactic.replaceMainGoal []

theorem Q_case1 : lookupLabel Q case1Sym = some (ptrParams, case1Cont) := by rw [Q_eq]; rfl
theorem Q_case2 : lookupLabel Q case2Sym = some (ptrParams, case2Cont) := by rw [Q_eq]; rfl
theorem Q_default : lookupLabel Q defaultSym = some (ptrParams, defaultCont) := by rw [Q_eq]; rfl
theorem Q_break : lookupLabel Q breakSym = some (ptrParams, breakCont) := by rw [Q_eq]; rfl
theorem Q_ret : lookupLabel Q retSym = some (retParams, retCont) := by rw [Q_eq]; rfl

theorem Q_lookup (l : sym) : lookupLabel Q l =
    if symOrd l case1Sym = .eq then some (ptrParams, case1Cont)
    else if symOrd l breakSym = .eq then some (ptrParams, breakCont)
    else if symOrd l defaultSym = .eq then some (ptrParams, defaultCont)
    else if symOrd l retSym = .eq then some (retParams, retCont)
    else if symOrd l case2Sym = .eq then some (ptrParams, case2Cont)
    else none := by
  rw [Q_eq]
  unfold lookupLabel
  rw [labelAdd_lookup ((((symMap_empty.addLabel _ _).addLabel _ _).addLabel _ _).addLabel _ _),
    labelAdd_lookup (((symMap_empty.addLabel _ _).addLabel _ _).addLabel _ _),
    labelAdd_lookup ((symMap_empty.addLabel _ _).addLabel _ _),
    labelAdd_lookup (symMap_empty.addLabel _ _), labelAdd_lookup symMap_empty]
  rfl

theorem Q_cont {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel Q l = some (params, cont)) :
    cont ∈ [case1Cont, case2Cont, defaultCont, breakCont, retCont] := by
  rw [Q_lookup] at h
  split at h
  · cases h; simp
  split at h
  · cases h; simp
  split at h
  · cases h; simp
  split at h
  · cases h; simp
  split at h
  · cases h; simp
  · cases h

theorem caseContext_frag (body : CoreExpr) (hb : Frag body) : Frag (caseContext body) :=
  .sseq (.sseq (.sseq (.sseq hb (.val_pure _)) afterSwitch_frag)
    (.sseq returnStmt_frag cleanup_frag)) returnSave_frag

theorem Q_frag {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel Q l = some (params, cont)) : Frag cont := by
  have hc := Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact caseContext_frag _ (.sseq (assignStmt_frag _ _ _ _)
      (.sseq (run_frag _ _) case2Tail_frag))
  · exact caseContext_frag _ (.sseq (assignStmt_frag _ _ _ _)
      (.sseq (run_frag _ _) defaultTail_frag))
  · exact caseContext_frag _ (.sseq (assignStmt_frag _ _ _ _)
      (.sseq (run_frag _ _) (.val_pure _)))
  · exact .sseq (.sseq (.sseq (.val_pure _) (.val_pure _))
      (.sseq returnStmt_frag cleanup_frag)) returnSave_frag
  · exact .pure_op rfl (.sym _ _)

theorem Q_depth [LemFuel] (hfuel : 40 ≤ LemFuel.fuel)
    {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel Q l = some (params, cont)) : evalDepth cont ≤ LemFuel.fuel := by
  have hc := Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    exact Nat.le_trans (by decide +kernel : evalDepth _ ≤ 40) hfuel

theorem wpt_load [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (x : sym) (ty : ctype) (n lo hi : Nat)
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv ty bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (pointsToCell M.tagDefs pv (.own 1) ty bs -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pv ty)] v)
          (envAdd (tmp n) (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (load x ty n lo hi) (f :: rest) :=
  wpt_boundLoad hex [Aloc (loc lo hi), Aexpr, intValueAnnot] []
    [Aloc (loc lo hi), Aexpr] [] [] [] ptrBty (loc lo hi) empty_annotation ty x (tmp n) NA
    f rest hf pv (.own 1) bs v hl hload htrap

abbrev assignFrame (n m : Nat) (v : Int) (pr : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (tmp n) (Vobject (OVpointer pr)) (envAdd (tmp m) (lint v) f)

theorem wpt_assignStmt [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (start n m : Nat) (v : Int) (hnm : m ≠ n)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f)
    (pr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hr : fmapLookupBy symCmpK rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) pr (.own 1) rTy bs ∗
      (∀ s : sym, ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pr (.own 1) rTy (emittedIntBytes M.tagDefs v) -∗
        Ψ (.pure Vunit) (envAdd s (lint v) (assignFrame n m v pr f) :: rest))) ⊢
      wpt M p Ls Θ 24 Ψ (assignStmt start n m v) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold assignStmt wc
  iapply wpt_seq _ _ _ _ _ _ _ 23 1
  unfold bnd
  rw [show (Pattern [] (CaseCtor Ctuple
    [Pattern [] (CaseBase (some (tmp n), ptrBty)), Pattern [] (CaseBase (some (tmp m), intBty))]) : pattern) =
    tuplePat [] [([], some (tmp n), ptrBty), ([], some (tmp m), intBty)] from rfl]
  iapply wpt_bound_wseq_tuple _ _ _ _ _ _ _ _ 7 16 rfl
  unfold intLiteral
  iapply wpt_mono_k (show (2 + 3 : Nat) ≤ 7 by decide)
  iapply wpt_unseq_value_right _ _ _ _ (lint v) _ 2
  iapply wpt_pure (psym rSym) _ (Nat.le_refl 2) rfl (psym_eval hex hf rest hr)
  simp only [SpikeVal.mergeInto, SpikeVal.val]
  iexists [Vobject (OVpointer pr), lint v], []
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  have hframe : SymFrame (assignFrame n m v pr f) := (hf.add _ _).add _ _
  have hlp : fmapLookupBy symCmpK (tmp n) (assignFrame n m v pr f) = some (Vobject (OVpointer pr)) := by
    rw [envAdd_lookup (hf.add _ _), if_pos (symOrd_self _)]
  have hlv : fmapLookupBy symCmpK (tmp m) (assignFrame n m v pr f) = some (lint v) := by
    rw [envAdd_lookup (hf.add _ _), if_neg (show symOrd (tmp m) (tmp n) ≠ .eq from symOrd_ne_eq_of_num_ne hnm),
      envAdd_lookup hf, if_pos (symOrd_self _)]
  have hp : evalPexpr M.tagDefs M.extern M.file (assignFrame n m v pr f :: rest)
      (ptrAssign (tmp n)) = some (Vobject (OVpointer pr)) :=
    symbol_eval (M := M) hex hframe rest [Astd "§6.5.16#3, sentence 1"] hlp
  have hv : evalPexpr M.tagDefs M.extern M.file (assignFrame n m v pr f :: rest)
      (convAssign (tmp m)) = some (lint v) :=
    EmittedStdCore.eval_convLoadedInt_spec [Astd "§6.5.16.1#2, conversion"] hstd
      (ta := [Aloc (loc 29 32)]) (evalPexpr_val _ _ _ _ _)
      (psym_eval (M := M) hex hframe rest hlv) hv1 hv2
  rw [show (Expr [] (Eannot [] (Expr [] (Ewseq (Pattern [] (CaseBase (none, BTy_unit)))
      (Expr [Astd "§6.5.16.1#2, store"] (Eaction (Paction polarity.Neg0
        (Action (locP start (start + 6) (start + 2)) empty_annotation
          (Store0 false (tyPe rTy) (ptrAssign (tmp n)) (convAssign (tmp m)) NA)))))
      (pureE (convAssign (tmp m)))))) : CoreExpr) =
    negAssignBody [] [] [Astd "§6.5.16.1#2, store"] [] [] [] BTy_unit
      (locP start (start + 6) (start + 2)) empty_annotation rTy
      (ptrAssign (tmp n)) (convAssign (tmp m)) (convAssign (tmp m)) NA from rfl]
  rw [show rTy = sintTyAnn [Aloc (loc 29 32)] from rfl]
  iapply wpt_intAssign hex [Astd "§6.5#2"] [] [] [Astd "§6.5.16.1#2, store"] [] [] [] BTy_unit
    (locP start (start + 6) (start + 2)) empty_annotation [Aloc (loc 29 32)]
    (ptrAssign (tmp n)) (convAssign (tmp m)) (convAssign (tmp m)) NA
    (assignFrame n m v pr f) rest hframe pr bs v (lint v) hv1 hv2 rfl hp hv rfl hv
  isplitl [Hpt]
  · iexact Hpt
  iintro %s %hs Hpt
  unfold unitE pureE
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply HΨ $$ %s %hs Hpt

/-- The label arguments carry the two owned cells; the jump itself binds
    x/r, so the source frame only needs its ordinary well-formedness. -/
def cells (GF : BundledGFunctors) [SpikeGS .hasLC GF]
    (tds : CerbTags.TagDefsMap) (n : Int) (vs : List value) (ρ : EnvStack) : IProp GF :=
  iprop(∃ (px pr : CerbMem.PointerValue) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [Vobject (OVpointer px), Vobject (OVpointer pr)] ∧ ρ = f :: rest ∧ SymFrame f⌝ ∗
    pointsToCell tds px (.own 1) xTy (emittedIntBytes tds 2) ∗
    pointsToCell tds pr (.own 1) rTy (emittedIntBytes tds n))

def labelSpec (GF : BundledGFunctors) [SpikeGS .hasLC GF]
    (tds : CerbTags.TagDefsMap) : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜l = retSym ∧ m = 2 ∧ vs = [lint 20] ∧
      ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝ ∨
    (⌜l = breakSym ∧ m = 18⌝ ∗ cells GF tds 20 vs ρ) ∨
    (⌜l = case2Sym ∧ m = 43⌝ ∗ cells GF tds 0 vs ρ))

def resultPost : value → Mem → Prop := fun v _ => v = lint 20

theorem retParams_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs retParams [v] (f :: rest) = envAdd (tmp 50) v f :: rest := by
  show update_env (mk_sym_pat (tmp 50) intBty) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem ptrParams_bindArgs (px pr : CerbMem.PointerValue)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs ptrParams [Vobject (OVpointer px), Vobject (OVpointer pr)] (f :: rest) =
      envAdd rSym (Vobject (OVpointer pr)) (envAdd xSym (Vobject (OVpointer px)) f) :: rest := by
  change update_env (mk_sym_pat rSym ptrBty) (Vobject (OVpointer pr))
    (update_env (mk_sym_pat xSym ptrBty) (Vobject (OVpointer px)) (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons, update_env_aux_sym]

theorem kill_eq (atLoc : CerbLocation.Loc) (ty : ctype) (x : sym) : kill atLoc ty x =
    killOpRedex [] atLoc empty_annotation (Static0 ty) (psym x) := rfl

theorem wpt_returnStmt [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) xTy (emittedIntBytes M.tagDefs 2) ∗
      pointsToCell M.tagDefs pr (.own 1) rTy (emittedIntBytes M.tagDefs 20)) ⊢
      wpt M p (labelSpec GF M.tagDefs) emptyProcSpecT 16 Ψ returnStmt (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  simp only [returnStmt, letS, seqE, wc, bnd, kill_eq]
  rw [show (Pattern [] (CaseBase (some (tmp 49), intBty)) : pattern) =
    symPat [] (tmp 49) intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 9
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_load hex rSym rTy 48 132 133 f rest hf pr (emittedIntBytes M.tagDefs 20) (lint 20) hr rfl rfl
  isplitl [Hr]
  · iexact Hr
  iintro Hr
  simp only [SpikeVal.val]
  iexists (lint 20)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 3 6
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval [] (loc 125 134) empty_annotation (Static0 xTy) (psym xSym) _ rfl (pv := px) (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 xTy) px xTy (emittedIntBytes M.tagDefs 2) _ (Nat.le_refl 2) rfl
  isplitl [Hx]
  · iexact Hx
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 3
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval [] (loc 125 134) empty_annotation (Static0 rTy) (psym rSym) _ rfl (pv := pr) (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 rTy) pr rTy (emittedIntBytes M.tagDefs 20) _ (Nat.le_refl 2) rfl
  isplitl [Hr]
  · iexact Hr
  simp only [SpikeVal.mergeInto]
  iapply wpt_run [] empty_annotation retSym [convLoaded retTy (tmp 49)] _ _ 2
    (by rw [hQ]; exact Q_ret)
    (by
      have hv : evalPexpr M.tagDefs M.extern M.file
          (envAdd (tmp 49) (lint 20) (envAdd (tmp 48) (Vobject (OVpointer pr)) f) :: rest)
          (convLoaded retTy (tmp 49)) = some (lint 20) :=
        convLoaded_eval hstd (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
          (by decide) (by decide)
      rw [evalPexprs_cons, hv, evalPexprs_nil]; rfl) (Nat.le_refl 3)
  dsimp only [labelSpec]
  ileft
  ipureintro
  exact ⟨rfl, rfl, rfl, _, _, rfl, by emitted_frame⟩

theorem wpt_break [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) xTy (emittedIntBytes M.tagDefs 2) ∗
      pointsToCell M.tagDefs pr (.own 1) rTy (emittedIntBytes M.tagDefs 20)) ⊢
      wpt M p (labelSpec GF M.tagDefs) emptyProcSpecT 18 Ψ breakCont (f :: rest) := by
  iintro H
  unfold breakCont seqE wc
  iapply wpt_seq _ _ _ _ _ _ _ 18 0
  iapply wpt_seq _ _ _ _ _ _ _ 2 16
  iapply wpt_seq _ _ _ _ _ _ _ 1 1
  rw [← ofValA_pure [Aloc (loc 40 124), Astmt] [] Vunit]
  iapply wpt_ofValA (.pure [Aloc (loc 40 124), Astmt] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  unfold unitE pureE
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply wpt_seq _ _ _ _ _ _ _ 16 0
  iapply wpt_returnStmt hstd hex hQ f rest hf px pr hx hr $$ H

theorem wpt_case2 [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q) (hsup : 51 ≤ M.runState.sym_supply)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) xTy (emittedIntBytes M.tagDefs 2) ∗
      pointsToCell M.tagDefs pr (.own 1) rTy (emittedIntBytes M.tagDefs 0)) ⊢
      wpt M p (labelSpec GF M.tagDefs) emptyProcSpecT 43 Ψ case2Cont (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  unfold case2Cont caseContext seqE wc
  iapply wpt_seq _ _ _ _ _ _ _ 43 0
  iapply wpt_seq _ _ _ _ _ _ _ 43 0
  iapply wpt_seq _ _ _ _ _ _ _ 43 0
  iapply wpt_seq _ _ _ _ _ _ _ 43 0
  iapply wpt_seq _ _ _ _ _ _ _ 24 19
  iapply wpt_assignStmt hstd hex 84 44 45 20 (by decide) (by decide) (by decide)
    f rest hf pr _ hr
  isplitl [Hr]
  · iexact Hr
  iintro %s %hs Hr
  obtain ⟨k, rfl, hk⟩ := hs
  have hxs : symOrd xSym (fresh_given_int k) ≠ .eq :=
    symOrd_ne_eq_of_num_ne (show 21 ≠ k by omega)
  have hrs : symOrd rSym (fresh_given_int k) ≠ .eq :=
    symOrd_ne_eq_of_num_ne (show 22 ≠ k by omega)
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 19 0
  unfold run
  iapply wpt_run [Aloc (loc 92 98), Astmt] empty_annotation breakSym
    [psym xSym, psym rSym] _ rest 18
    (by rw [hQ]; exact Q_break)
    (by rw [evalPexprs_cons, psym_eval hex (by emitted_frame) rest (by
        rw [envAdd_lookup (by emitted_frame), if_neg hxs]; emitted_lookup),
      evalPexprs_cons, psym_eval hex (by emitted_frame) rest (by
        rw [envAdd_lookup (by emitted_frame), if_neg hrs]; emitted_lookup), evalPexprs_nil]; rfl)
    (Nat.le_refl 19)
  dsimp only [labelSpec]
  iright
  ileft
  isplit
  · ipureintro; exact ⟨rfl, rfl⟩
  dsimp only [cells]
  iexists px, pr, _, rest
  isplit
  · ipureintro; exact ⟨rfl, rfl, by emitted_frame⟩
  isplitl [Hx]
  · iexact Hx
  iexact Hr

theorem blockSpecs_valid [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q) (hsup : 51 ≤ M.runState.sym_supply) :
    ⊢ blockSpecsT (GF := GF) M p (labelSpec GF M.tagDefs) emptyProcSpecT (readoutPost resultPost) := by
  refine blockSpecsT_intro fun l params cont vs f rest m hl => ?_
  dsimp only [labelSpec]
  iintro HL
  icases HL with (Hr | Hother)
  · icases Hr with %hpure
    obtain ⟨rfl, rfl, rfl, f', rest', hρ, hf⟩ := hpure
    obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
    rw [hQ, Q_ret] at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    rw [retParams_bindArgs]
    unfold retCont pureE
    iapply wpt_pure (psym (tmp 50)) _ (Nat.le_refl 2) rfl
      (psym_eval hex (by emitted_frame) _ (by emitted_lookup))
    iintro %σ' %ns %κs %nt -
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    rfl
  · icases Hother with (Hb | Hc)
    · icases Hb with ⟨%hpure, Hcells⟩
      obtain ⟨rfl, rfl⟩ := hpure
      rw [hQ, Q_break] at hl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
      dsimp only [cells]
      icases Hcells with ⟨%px, %pr, %f', %rest', %hargs, Hx, Hr⟩
      obtain ⟨rfl, hρ, hf⟩ := hargs
      obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
      rw [ptrParams_bindArgs]
      iapply wpt_break hstd hex hQ
        (envAdd rSym (Vobject (OVpointer pr)) (envAdd xSym (Vobject (OVpointer px)) f)) rest (by emitted_frame) px pr (by emitted_lookup) (by emitted_lookup)
      isplitl [Hx]
      · iexact Hx
      iexact Hr
    · icases Hc with ⟨%hpure, Hcells⟩
      obtain ⟨rfl, rfl⟩ := hpure
      rw [hQ, Q_case2] at hl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
      dsimp only [cells]
      icases Hcells with ⟨%px, %pr, %f', %rest', %hargs, Hx, Hr⟩
      obtain ⟨rfl, hρ, hf⟩ := hargs
      obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
      rw [ptrParams_bindArgs]
      iapply wpt_case2 hstd hex hQ hsup
        (envAdd rSym (Vobject (OVpointer pr)) (envAdd xSym (Vobject (OVpointer px)) f)) rest (by emitted_frame) px pr (by emitted_lookup) (by emitted_lookup)
      isplitl [Hx]
      · iexact Hx
      iexact Hr

theorem wpt_switch [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) xTy (emittedIntBytes M.tagDefs 2) ∗
      pointsToCell M.tagDefs pr (.own 1) rTy (emittedIntBytes M.tagDefs 0)) ⊢
      wpt M p (labelSpec GF M.tagDefs) emptyProcSpecT 58 Ψ switch (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  unfold switch letS bnd
  rw [show (Pattern [] (CaseBase (some (tmp 36), intBty)) : pattern) =
    symPat [] (tmp 36) intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 51
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_load hex xSym xTy 35 48 49 f rest hf px (emittedIntBytes M.tagDefs 2) (lint 2) hx rfl rfl
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  simp only [SpikeVal.val]
  iexists (lint 2)
  isplit
  · ipureintro; rfl
  rw [update_env_sym, show (51 : Nat) = 50 + 1 from rfl]
  iapply wpt_case_eval [] (psym (tmp 36)) switchPats _ rfl (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
  rw [show (50 : Nat) = 49 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl (switch_select (lint 2))
  unfold specifiedBranch letS
  rw [show (Pattern [] (CaseBase (some (tmp 38), BTy_object OTy_integer)) : pattern) =
    symPat [] (tmp 38) (BTy_object OTy_integer) from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 2 47
  unfold pureE
  have hconv : evalPexpr M.tagDefs M.extern M.file
      (envAdd (tmp 36) (lint 2) (envAdd (tmp 35) (Vobject (OVpointer px)) f) :: rest)
      (Pexpr [Astd "§6.8.4.2#5, sentence 1"] ()
        (PEcall (Sym EmittedStdCore.convInt.1) [tyPe switchTy, Pexpr [] () (PEval (Vobject (OVinteger (CerbMem.integerIval 2))))])) =
      some (oint 2) :=
    EmittedStdCore.eval_convInt_call [Astd "§6.8.4.2#5, sentence 1"] hstd
      (ta := [Aloc (loc 48 49)]) (evalPexpr_val _ _ _ _ _)
      (evalPexpr_val _ _ _ _ _) (by decide) (by decide)
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl hconv
  iexists (oint 2)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  unfold dispatch seqE wc
  iapply wpt_seq _ _ _ _ _ _ _ 2 45
  rw [show (2 : Nat) = 1 + 1 from rfl]
  iapply wpt_if_false _ _ _ _ _ (by
    rw [evalPexpr_op, psym_eval hex (by emitted_frame) rest (by emitted_lookup), evalPexpr_val]; rfl)
  unfold unitE pureE
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 45 0
  rw [show (45 : Nat) = 44 + 1 from rfl]
  iapply wpt_if_true _ _ _ _ _ (by
    rw [evalPexpr_op, psym_eval hex (by emitted_frame) rest (by emitted_lookup), evalPexpr_val]; rfl)
  unfold run
  iapply wpt_run [] empty_annotation case2Sym [psym xSym, psym rSym] _ rest 43
    (by rw [hQ]; exact Q_case2)
    (by rw [evalPexprs_cons, psym_eval hex (by emitted_frame) rest (by emitted_lookup),
      evalPexprs_cons, psym_eval hex (by emitted_frame) rest (by emitted_lookup), evalPexprs_nil]; rfl)
    (Nat.le_refl 44)
  dsimp only [labelSpec]
  iright
  iright
  isplit
  · ipureintro; exact ⟨rfl, rfl⟩
  dsimp only [cells]
  iexists px, pr, _, rest
  isplit
  · ipureintro; exact ⟨rfl, rfl, by emitted_frame⟩
  isplitl [Hx]
  · iexact Hx
  iexact Hr


theorem createX_eq : createX = createOpRedex [] (locR 16 136 22 23) empty_annotation
    (Pexpr [] () (PEctor Civalignof [tyPe xTy])) (tyPe xTy)
    (PrefSource (loc 22 23) [mainSym, xSym]) := rfl
theorem createR_eq : createR = createOpRedex [] (locR 16 136 33 34) empty_annotation
    (Pexpr [] () (PEctor Civalignof [tyPe rTy])) (tyPe rTy)
    (PrefSource (loc 33 34) [mainSym, rSym]) := rfl
theorem store_eq (atLoc : CerbLocation.Loc) (ty : ctype) (p v : generic_pexpr Unit sym) :
    act atLoc (Store0 false (tyPe ty) p v NA) = storeOpRedex [] atLoc empty_annotation ty p v NA := rfl

/-- 20 units for allocation/initialization, 58 for dispatch and its label path. -/
theorem mainBody_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : HasIntLibrary M.file)
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ) (hQ : M.labelsAt p = Q)
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs xTy 4 + allocCost M.tagDefs rTy 4)) ⊢
      wpt M p (labelSpec GF M.tagDefs) emptyProcSpecT 78 (readoutPost resultPost) mainBody (f :: rest) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapX, HcapR⟩
  rw [mainBody_shape]
  simp only [block, letS, seqE, wc, createX_eq, createR_eq]
  iapply wpt_seq _ _ _ _ _ _ _ 78 0
  rw [show (Pattern [] (CaseBase (some xSym, ptrBty)) : pattern) = symPat [] xSym ptrBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 75
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [tyPe xTy])) (tyPe xTy)
    (PrefSource (loc 22 23) [mainSym, xSym]) _
    (align := CerbMem.alignofIval M.tagDefs xTy) (ty := xTy) rfl
    (by unfold tyPe; rw [evalPexpr_ctor1, evalPexpr_val]; rfl) (evalPexpr_val _ _ _ _ _)
  rw [show CerbMem.alignofIval M.tagDefs xTy = .IV .Prov_none 4 from rfl]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 xTy
    (PrefSource (loc 22 23) [mainSym, xSym]) _ (Nat.le_refl 2)
    (int_size_pos _) (int_nonatomic _) (fun a => int_decIndep _ a _)
  isplitl [HcapX]
  · iexact HcapX
  iintro %px ⟨Hx, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some rSym, ptrBty)) : pattern) = symPat [] rSym ptrBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 72
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [tyPe rTy])) (tyPe rTy)
    (PrefSource (loc 33 34) [mainSym, rSym]) _
    (align := CerbMem.alignofIval M.tagDefs rTy) (ty := rTy) rfl
    (by unfold tyPe; rw [evalPexpr_ctor1, evalPexpr_val]; rfl) (evalPexpr_val _ _ _ _ _)
  rw [show CerbMem.alignofIval M.tagDefs rTy = .IV .Prov_none 4 from rfl]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 rTy
    (PrefSource (loc 33 34) [mainSym, rSym]) _ (Nat.le_refl 2)
    (int_size_pos _) (int_nonatomic _) (fun a => int_decIndep _ a _)
  isplitl [HcapR]
  · iexact HcapR
  iintro %pr ⟨Hr, -⟩
  iexists (Vobject (OVpointer pr))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 7 65
  simp only [initializeX, letS, bnd, store_eq]
  rw [show (Pattern [] (CaseBase (some (tmp 33), intBty)) : pattern) = symPat [] (tmp 33) intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 4
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  rw [show intLiteral [Aloc (loc 26 27), Aexpr, intValueAnnot] 2 =
    ofValA (.pure [Aloc (loc 26 27), Aexpr, intValueAnnot] [] (lint 2)) from rfl]
  iapply wpt_ofValA (.pure [Aloc (loc 26 27), Aexpr, intValueAnnot] [] (lint 2)) _ (by decide)
  simp only [SpikeVal.val]
  iexists (lint 2)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ xTy (psym xSym) (convLoaded xTy (tmp 33)) NA _
    rfl (pv := px) (cv := lint 2) (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
    (convLoaded_eval hstd
      (psym_eval hex (by emitted_frame) rest (by emitted_lookup)) (by decide) (by decide))
  iapply wpt_store _ _ _ xTy px (lint 2) NA (emittedIntMval 2) _ _ (Nat.le_refl 3)
    (int_encodes _ _ _) (int_storable _ _ _ (by decide) (by decide))
  isplitl [Hx]
  · iexact Hx
  iintro %fpX Hx
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 7 58
  simp only [initializeR, letS, bnd, store_eq]
  rw [show (Pattern [] (CaseBase (some (tmp 34), intBty)) : pattern) = symPat [] (tmp 34) intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 4
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  rw [show intLiteral [Aloc (loc 37 38), Aexpr, intValueAnnot] 0 =
    ofValA (.pure [Aloc (loc 37 38), Aexpr, intValueAnnot] [] (lint 0)) from rfl]
  iapply wpt_ofValA (.pure [Aloc (loc 37 38), Aexpr, intValueAnnot] [] (lint 0)) _ (by decide)
  simp only [SpikeVal.val]
  iexists (lint 0)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ rTy (psym rSym) (convLoaded rTy (tmp 34)) NA _
    rfl (pv := pr) (cv := lint 0) (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
    (convLoaded_eval hstd
      (psym_eval hex (by emitted_frame) rest (by emitted_lookup)) (by decide) (by decide))
  iapply wpt_store _ _ _ rTy pr (lint 0) NA (emittedIntMval 0) _ _ (Nat.le_refl 3)
    (int_encodes _ _ _) (int_storable _ _ _ (by decide) (by decide))
  isplitl [Hr]
  · iexact Hr
  iintro %fpR Hr
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 58 0
  unfold switchBlock wc
  iapply wpt_seq _ _ _ _ _ _ _ 58 0
  iapply wpt_switch hstd hex hQ
    (envAdd (tmp 34) (lint 0) (envAdd (tmp 33) (lint 2)
      (envAdd rSym (Vobject (OVpointer pr)) (envAdd xSym (Vobject (OVpointer px)) f))))
    rest (by emitted_frame) px pr (by emitted_lookup) (by emitted_lookup)
  isplitl [Hx]
  · iexact Hx
  iexact Hr

def entryRunState (cmp : EmittedFile.Comparators) (sup : Nat) : core_run_state :=
  (initial_core_run_state sup (collect_labeled_continuations_NEW (restoredFile cmp))).1

theorem entryRunState_main (cmp : EmittedFile.Comparators) (sup : Nat)
    (h : labelUnionCheck cmp = true) :
    fmapLookupBy symCmpL mainSym (entryRunState cmp sup).labeled = some Q := by
  change fmapLookupBy symCmpL mainSym
    (collect_labeled_continuations_NEW (restoredFile cmp)) = some Q
  exact main_labels_of_check cmp h

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
    (hQ : fmapLookupBy symCmpL mainSym (entryRunState cmp sup).labeled = some Q) :
    (entryCtx cmp sup).labelsAt (entryCtl sup).proc = Q := by
  change (match fmapLookupBy symCmpL (resolveExtern runtimeExtern mainSym)
      (entryRunState cmp sup).labeled with
    | some Q => Q
    | none => fmapEmpty) = Q
  rw [runtimeExtern_main, hQ]

theorem entry_budget_fits :
    allocCost fmapEmpty xTy 4 + allocCost fmapEmpty rTy 4 ≤
      headroom prodMem₀.lastAddress := by
  exact prod_two_int_budget_fits

/-- The actual main's per-thread driver delivery. The checked library paths
and collector union establish the file premises, including registration;
the environment map is the one produced by actual startup. -/
theorem mainBody_driver_done [LemFuel] (hfuel : 40 ≤ LemFuel.fuel)
    (cmp : EmittedFile.Comparators) (sup : Nat) (hsup : 51 ≤ sup)
    (hstd : EmittedStdCore.intLibraryCheck cmp.stdlib = true)
    (hlabels : labelUnionCheck cmp = true) :
    DriverDoneAtExtern runtimeExtern mainSym Q (restoredFile cmp) entryThread
      mainBody [fmapEmpty] (CerbLocation.other "Driver.drive") ⟨sup, 0⟩
      prodMem₀ resultPost 78 := by
  have hlbl := entryCtx_labels cmp sup (entryRunState_main cmp sup hlabels)
  exact wpt_driver_done_alloc_extern (hfuel := by omega) (GF := SpikeGF)
    (M₀ := entryCtx cmp sup) (ctl := entryCtl sup) (th₀ := entryThread)
    (p := mainSym) (Q := Q) rfl hlbl rfl rfl rfl rfl (Nat.le_refl _)
    (fun l params cont hl => Q_frag (by rw [← hlbl]; exact hl))
    (fun l params cont hl => Q_depth hfuel (by rw [← hlbl]; exact hl))
    (labelSpec SpikeGF fmapEmpty) mainBody fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
    (allocCost fmapEmpty xTy 4 + allocCost fmapEmpty rTy 4) mainBody_frag (Nat.le_trans mainBody_evalDepth hfuel)
    (prodMem₀_launchCoh _ entry_budget_fits) resultPost 78
    (by
      intro inst
      rw [show (entryCtl sup).proc = some mainSym from rfl]
      iintro ⟨-, Hcap⟩
      isplitr [Hcap]
      · have hb := blockSpecs_valid (GF := SpikeGF) (M := entryCtx cmp sup) (p := some mainSym)
          (hasIntLibrary_restore cmp hstd) runtimeExtern_compare hlbl hsup
        rw [show (entryCtx cmp sup).tagDefs = fmapEmpty from rfl] at hb
        iapply hb
      · have hw := mainBody_wpt (GF := SpikeGF) (M := entryCtx cmp sup)
          (p := some mainSym) (hfuel := by omega)
          (hasIntLibrary_restore cmp hstd) runtimeExtern_compare hlbl
          fmapEmpty [] symFrame_empty
        rw [show (entryCtx cmp sup).tagDefs = fmapEmpty from rfl] at hw
        iapply hw $$ Hcap)

/-- Complete-file execution at the actual frontend supply. The checked
file/library premises feed the public body proof and derived registration;
startup, errno initialization, driver delivery and finalization are composed
over the shipped semantics. -/
theorem certified_production [LemFuel] (hfuel : 80 ≤ LemFuel.fuel)
    (cmp : EmittedFile.Comparators)
    (hstd : EmittedStdCore.intLibraryCheck cmp.stdlib = true)
    (hmain : mainLookupCheck cmp.funs = true)
    (hlabels : labelUnionCheck cmp = true)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive (restoredFile cmp).tagDefs false (restoredFile cmp) args)
          ((initial_driver_state frontendSupply (restoredFile cmp) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 20 ∧
      dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  refine prod_run_eqJ_file (restoredFile cmp) (restoredFile_tagDefs cmp)
    (restoredFile_globs cmp) mainSym (restoredFile_main cmp)
    (locR 1 136 5 9) (some 20) intBty mainBody (restoredFile_mainLookup cmp hmain)
    frontendSupply (Q := Q) ?_ resultPost 78 ?_ (by omega) fs args
  · rw [restoredFile_extern, runtimeExtern_main]
    exact entryRunState_main cmp frontendSupply hlabels
  · rw [restoredFile_extern]
    exact mainBody_driver_done (hfuel := by omega) cmp frontendSupply (by decide) hstd hlabels

/-- Transfer the production equation to the original file and supply when
the retained data and the original comparator checks agree. The executable
frontend comparison tests this connection; it does not discharge these Lean
equality premises or prove correctness of the IO frontend. -/
theorem certified_production_of_capture_eq [LemFuel] (hfuel : 80 ≤ LemFuel.fuel)
    (fallback : EmittedFile.Comparators) (F : file core_run_annotation) (sup : Nat)
    (hdata : EmittedFile.captureData F = data) (hsup : sup = frontendSupply)
    (hstd : EmittedStdCore.intLibraryCheck (EmittedFile.captureComparators fallback F).stdlib = true)
    (hmain : mainLookupCheck (EmittedFile.captureComparators fallback F).funs = true)
    (hlabels : labelUnionCheck (EmittedFile.captureComparators fallback F) = true)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive F.tagDefs false F args) ((initial_driver_state sup F fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 20 ∧
      dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  subst sup
  rw [← EmittedFile.restore_eq_of_data_eq fallback F data hdata]
  exact certified_production hfuel (EmittedFile.captureComparators fallback F) hstd hmain hlabels fs args


end CerberusHeapLang.CorpusA7.T6
