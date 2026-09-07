/-
The emitted t6_switch main, using public total-correctness rules.
The full term's membership is in Examples/CorpusE5. t6_wpt has budget 78;
t6_certified_production concludes exactly one Active Specified(20),
unblocked with empty stdout/stderr, when the initial symbol supply is at
least 600. The current file/library boundary is the same one as t1 and t5
(KOI A7): the transcribed main and a checked three-function std.core
fragment with an empty implementation map, not the full frontend file.

The five registered continuations are checked against collect_saves.
The label specifications admit the reachable case-2, break and return
entries; whole-term and label-body membership also cover the other cases.
-/
import CerberusHeapLang.Examples.EmittedInt
import CerberusHeapLang.Examples.CorpusE5
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.EmittedAExhibit

set_option autoImplicit false
namespace CerberusHeapLang
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (t6a t6Load t6Reg t6RegP t6xSym t6rSym t6RetSym t6BreakSym
  t6Case1Sym t6Case2Sym t6DefaultSym t6Run t6Save t6AssignStmt t6Cases
  t6Dispatch t6SpecifiedBranch t6AfterSwitch t6Return t6Main
  t5Pure t5Unit ptrTy intCty psym specInt convLoadedInt act wc seqE letS letW bnd createInt)

variable {GF : BundledGFunctors}

theorem wpt_t6Load [SpikeGS .hasLC GF]
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
        Ψ (.annot [DA_pos [] fp] v) (envAdd (t6a tmp) (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (t6Load x tmp c1 c2) (f :: rest) :=
  wpt_emittedIntLoad hex (t6Reg c1 c2) x (t6a tmp) f rest hf pv bs v hl hload htrap


/-! The collector retains the surrounding sequence suffix at each save. -/

def t6DefaultTail : CoreExpr :=
  seqE (t6Save [Aloc (t6Reg 98 114), Astmt] t6DefaultSym (t6AssignStmt 107 527 528 30))
    (seqE (t6Run [Aloc (t6Reg 115 121), Astmt] t6BreakSym) t5Unit)

def t6Case2Tail : CoreExpr :=
  seqE (t6Save [Aloc (t6Reg 75 90), Astmt] t6Case2Sym (t6AssignStmt 83 525 526 20))
    (seqE (t6Run [Aloc (t6Reg 91 97), Astmt] t6BreakSym) t6DefaultTail)

def t6CaseContext (body : CoreExpr) : CoreExpr :=
  Expr [Aloc (t6Reg 39 123), Astmt] (Esseq wc
    (Expr [Aloc (t6Reg 50 123), Astmt] (Esseq wc body t5Unit)) t6AfterSwitch)

def t6Case1Cont : CoreExpr :=
  t6CaseContext (seqE (t6AssignStmt 60 523 524 10)
    (seqE (t6Run [Aloc (t6Reg 68 74), Astmt] t6BreakSym) t6Case2Tail))

def t6Case2Cont : CoreExpr :=
  t6CaseContext (seqE (t6AssignStmt 83 525 526 20)
    (seqE (t6Run [Aloc (t6Reg 91 97), Astmt] t6BreakSym) t6DefaultTail))

def t6DefaultCont : CoreExpr :=
  t6CaseContext (seqE (t6AssignStmt 107 527 528 30)
    (seqE (t6Run [Aloc (t6Reg 115 121), Astmt] t6BreakSym) t5Unit))

def t6BreakCont : CoreExpr :=
  seqE (Expr [Aloc (t6Reg 39 123), Astmt] (Epure (Pexpr [] () (PEval Vunit))))
    (seqE t5Unit t6Return)

def t6PtrParams : List (sym × core_base_type) := [(t6xSym, ptrTy), (t6rSym, ptrTy)]
def t6RetParams : List (sym × core_base_type) := [(t6a 531, CorpusE0.lint)]
def t6RetCont : CoreExpr := t5Pure (psym (t6a 531))

/-- The actual engine collector is the authority for this label map. -/
def t6Q : LabelMap := collect_saves t6Main

theorem t6Q_case1 : lookupLabel t6Q t6Case1Sym = some (t6PtrParams, t6Case1Cont) := rfl
theorem t6Q_case2 : lookupLabel t6Q t6Case2Sym = some (t6PtrParams, t6Case2Cont) := rfl
theorem t6Q_default : lookupLabel t6Q t6DefaultSym = some (t6PtrParams, t6DefaultCont) := rfl
theorem t6Q_break : lookupLabel t6Q t6BreakSym = some (t6PtrParams, t6BreakCont) := rfl
theorem t6Q_ret : lookupLabel t6Q t6RetSym = some (t6RetParams, t6RetCont) := rfl

abbrev t6frAssign (n m : Nat) (v : Int) (pr : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (t6a n) (Vobject (OVpointer pr)) (envAdd (t6a m) (lint v) f)

theorem wpt_t6AssignStmt [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (start n m : Nat) (v : Int) (hnm : m ≠ n)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hr : fmapLookupBy symCmpK t6rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) pr (.own 1) intTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs v) -∗
        Ψ (.pure Vunit) (envAdd s (lint v) (t6frAssign n m v pr f) :: rest))) ⊢
      wpt M p Ls Θ 24 Ψ (t6AssignStmt start n m v) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold t6AssignStmt wc
  iapply wpt_seq _ _ _ _ _ _ _ 23 1
  unfold bnd
  rw [show (Pattern [] (CaseCtor Ctuple
    [Pattern [] (CaseBase (some (t6a n), ptrTy)), Pattern [] (CaseBase (some (t6a m), CorpusE0.lint))]) : pattern) =
    tuplePat [] [([], some (t6a n), ptrTy), ([], some (t6a m), CorpusE0.lint)] from rfl]
  iapply wpt_bound_wseq_tuple _ _ _ _ _ _ _ _ 7 16 rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_unseq_pure_right _ _ _ (specInt v) _ 2 (lint v) rfl rfl (specInt_eval _ v)
  iapply wpt_pure (psym t6rSym) _ (Nat.le_refl 2) rfl (t1sym_eval hex rest hr)
  simp only [SpikeVal.mergeInto, SpikeVal.val]
  iexists [Vobject (OVpointer pr), lint v], []
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  rw [show (Expr [] (Eannot [] (Expr [] (Ewseq (Pattern [] (CaseBase (none, BTy_unit)))
      (Expr [Astd "§6.5.16.1#2, store"] (Eaction (Paction polarity.Neg0
        (Action (t6RegP start (start + 6) (start + 2)) empty_annotation
          (Store0 false intCty (psym (t6a n)) (convLoadedInt (t6a m)) NA)))))
      (t5Pure (convLoadedInt (t6a m)))))) : CoreExpr) =
    negAssignBody [] [] [Astd "§6.5.16.1#2, store"] [] [] [] BTy_unit
      (t6RegP start (start + 6) (start + 2)) empty_annotation intTy
      (psym (t6a n)) (convLoadedInt (t6a m)) (convLoadedInt (t6a m)) NA from rfl]
  iapply wpt_emittedIntStore hstd hex (t6RegP start (start + 6) (start + 2)) (t6a n) (t6a m) [] v
    (show symOrd (t6a m) (t6a n) ≠ .eq from symOrd_ne_eq_of_num_ne hnm)
    hv1 hv2 f rest hf pr bs
  isplitl [Hpt]
  · iexact Hpt
  iintro %s %hs Hpt
  unfold CorpusE0.t5Unit t5Pure
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply HΨ $$ %s %hs Hpt

theorem t6Q_eq : t6Q =
    fmapAddBy symCmpL t6Case1Sym (t6PtrParams, t6Case1Cont)
    (fmapAddBy symCmpL t6Case2Sym (t6PtrParams, t6Case2Cont)
    (fmapAddBy symCmpL t6DefaultSym (t6PtrParams, t6DefaultCont)
    (fmapAddBy symCmpL t6BreakSym (t6PtrParams, t6BreakCont)
    (fmapAddBy symCmpL t6RetSym (t6RetParams, t6RetCont) fmapEmpty)))) := rfl

theorem t6Q_lookup (l : sym) : lookupLabel t6Q l =
    if symOrd l t6Case1Sym = .eq then some (t6PtrParams, t6Case1Cont)
    else if symOrd l t6Case2Sym = .eq then some (t6PtrParams, t6Case2Cont)
    else if symOrd l t6DefaultSym = .eq then some (t6PtrParams, t6DefaultCont)
    else if symOrd l t6BreakSym = .eq then some (t6PtrParams, t6BreakCont)
    else if symOrd l t6RetSym = .eq then some (t6RetParams, t6RetCont)
    else none := by
  rw [t6Q_eq]
  unfold lookupLabel
  rw [labelAdd_lookup ((((symMap_empty.addLabel _ _).addLabel _ _).addLabel _ _).addLabel _ _),
    labelAdd_lookup (((symMap_empty.addLabel _ _).addLabel _ _).addLabel _ _),
    labelAdd_lookup ((symMap_empty.addLabel _ _).addLabel _ _),
    labelAdd_lookup (symMap_empty.addLabel _ _), labelAdd_lookup symMap_empty]
  rfl

theorem t6Q_cont {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t6Q l = some (params, cont)) :
    cont ∈ [t6Case1Cont, t6Case2Cont, t6DefaultCont, t6BreakCont, t6RetCont] := by
  rw [t6Q_lookup] at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · split at h
        · cases h; simp
        · split at h
          · cases h; simp
          · cases h

/-- The label arguments carry the two owned cells; the jump itself binds
    x/r, so the source frame only needs its ordinary well-formedness. -/
def t6Cells (GF : BundledGFunctors) [SpikeGS .hasLC GF]
    (tds : CerbTags.TagDefsMap) (n : Int) (vs : List value) (ρ : EnvStack) : IProp GF :=
  iprop(∃ (px pr : CerbMem.PointerValue) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [Vobject (OVpointer px), Vobject (OVpointer pr)] ∧ ρ = f :: rest ∧ SymFrame f⌝ ∗
    pointsToCell tds px (.own 1) intTy (emittedIntBytes tds 2) ∗
    pointsToCell tds pr (.own 1) intTy (emittedIntBytes tds n))

def t6LsT (GF : BundledGFunctors) [SpikeGS .hasLC GF]
    (tds : CerbTags.TagDefsMap) : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜l = t6RetSym ∧ m = 2 ∧ vs = [lint 20] ∧
      ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝ ∨
    (⌜l = t6BreakSym ∧ m = 18⌝ ∗ t6Cells GF tds 20 vs ρ) ∨
    (⌜l = t6Case2Sym ∧ m = 43⌝ ∗ t6Cells GF tds 0 vs ρ))

def ψT6 : value → Mem → Prop := fun v _ => v = lint 20

theorem t6RetParams_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs t6RetParams [v] (f :: rest) = envAdd (t6a 531) v f :: rest := by
  show update_env (mk_sym_pat (t6a 531) CorpusE0.lint) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem t6PtrParams_bindArgs (px pr : CerbMem.PointerValue)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs t6PtrParams [Vobject (OVpointer px), Vobject (OVpointer pr)] (f :: rest) =
      envAdd t6rSym (Vobject (OVpointer pr)) (envAdd t6xSym (Vobject (OVpointer px)) f) :: rest := by
  change update_env (mk_sym_pat t6rSym ptrTy) (Vobject (OVpointer pr))
    (update_env (mk_sym_pat t6xSym ptrTy) (Vobject (OVpointer px)) (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons, update_env_aux_sym]

local macro "t6_frame" : tactic => `(tactic| repeat first | assumption | apply SymFrame.add)
local macro "t6_lookup" : tactic => `(tactic|
  (repeat first
    | rw [envAdd_lookup (by t6_frame), if_pos (by decide +kernel)]
    | rw [envAdd_lookup (by t6_frame), if_neg (by decide +kernel)]) <;> assumption)

theorem t6Kill_eq (x : sym) : CorpusE0.t6Kill x =
    killOpRedex [] (t6Reg 0 135) empty_annotation (Static0 intTy) (psym x) := rfl

theorem wpt_t6Return [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t6Q)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK t6xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK t6rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (emittedIntBytes M.tagDefs 2) ∗
      pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs 20)) ⊢
      wpt M p (t6LsT GF M.tagDefs) emptyProcSpecT 16 Ψ t6Return (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  simp only [t6Return, letS, seqE, wc, bnd, t6Kill_eq]
  rw [show (Pattern [] (CaseBase (some (t6a 530), CorpusE0.lint)) : pattern) =
    symPat [] (t6a 530) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 9
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_t6Load hex t6rSym 529 131 132 f rest hf pr (emittedIntBytes M.tagDefs 20) (lint 20) hr rfl rfl
  isplitl [Hr]
  · iexact Hr
  iintro %fp Hr
  simp only [SpikeVal.val]
  iexists (lint 20)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 3 6
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ _ _ _ _ rfl (pv := px) (t1sym_eval hex rest (by t6_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 intTy) px intTy (emittedIntBytes M.tagDefs 2) _ (Nat.le_refl 2) rfl
  isplitl [Hx]
  · iexact Hx
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 3
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ _ _ _ _ rfl (pv := pr) (t1sym_eval hex rest (by t6_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 intTy) pr intTy (emittedIntBytes M.tagDefs 20) _ (Nat.le_refl 2) rfl
  isplitl [Hr]
  · iexact Hr
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 0
  iapply wpt_run [] empty_annotation t6RetSym [convLoadedInt (t6a 530)] _ _ 2
    (by rw [hQ]; exact t6Q_ret)
    (by rw [evalPexprs_cons, t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by t6_lookup))
      (by decide) (by decide), evalPexprs_nil]; rfl) (Nat.le_refl 3)
  dsimp only [t6LsT]
  ileft
  ipureintro
  exact ⟨rfl, rfl, rfl, _, _, rfl, by t6_frame⟩

theorem wpt_t6Break [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t6Q)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK t6xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK t6rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (emittedIntBytes M.tagDefs 2) ∗
      pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs 20)) ⊢
      wpt M p (t6LsT GF M.tagDefs) emptyProcSpecT 18 Ψ t6BreakCont (f :: rest) := by
  iintro H
  unfold t6BreakCont seqE wc
  iapply wpt_seq _ _ _ _ _ _ _ 1 17
  rw [← ofValA_pure [Aloc (t6Reg 39 123), Astmt] [] Vunit]
  iapply wpt_ofValA (.pure [Aloc (t6Reg 39 123), Astmt] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 1 16
  unfold t5Unit t5Pure
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  iapply wpt_t6Return hstd hex hQ f rest hf px pr hx hr $$ H

theorem wpt_t6Case2 [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t6Q) (hsup : 600 ≤ M.runState.sym_supply)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK t6xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK t6rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (emittedIntBytes M.tagDefs 2) ∗
      pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs 0)) ⊢
      wpt M p (t6LsT GF M.tagDefs) emptyProcSpecT 43 Ψ t6Case2Cont (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  unfold t6Case2Cont t6CaseContext seqE wc
  iapply wpt_seq _ _ _ _ _ _ _ 43 0
  iapply wpt_seq _ _ _ _ _ _ _ 43 0
  iapply wpt_seq _ _ _ _ _ _ _ 24 19
  iapply wpt_t6AssignStmt hstd hex 83 525 526 20 (by decide) (by decide) (by decide)
    f rest hf pr _ hr
  isplitl [Hr]
  · iexact Hr
  iintro %s %hs Hr
  obtain ⟨k, rfl, hk⟩ := hs
  have hxs : symOrd t6xSym (fresh_given_int k) ≠ .eq :=
    symOrd_ne_eq_of_num_ne (show 509 ≠ k by omega)
  have hrs : symOrd t6rSym (fresh_given_int k) ≠ .eq :=
    symOrd_ne_eq_of_num_ne (show 510 ≠ k by omega)
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 19 0
  unfold t6Run
  iapply wpt_run [Aloc (t6Reg 91 97), Astmt] empty_annotation t6BreakSym
    [psym t6xSym, psym t6rSym] _ rest 18
    (by rw [hQ]; exact t6Q_break)
    (by rw [evalPexprs_cons, t1sym_eval hex rest (by
        rw [envAdd_lookup (by t6_frame), if_neg hxs]; t6_lookup),
      evalPexprs_cons, t1sym_eval hex rest (by
        rw [envAdd_lookup (by t6_frame), if_neg hrs]; t6_lookup), evalPexprs_nil]; rfl)
    (Nat.le_refl 19)
  dsimp only [t6LsT]
  iright
  ileft
  isplit
  · ipureintro; exact ⟨rfl, rfl⟩
  dsimp only [t6Cells]
  iexists px, pr, _, rest
  isplit
  · ipureintro; exact ⟨rfl, rfl, by t6_frame⟩
  isplitl [Hx]
  · iexact Hx
  iexact Hr

theorem t6_blockSpecsT [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t6Q) (hsup : 600 ≤ M.runState.sym_supply) :
    ⊢ blockSpecsT (GF := GF) M p (t6LsT GF M.tagDefs) emptyProcSpecT (readoutPost ψT6) := by
  refine blockSpecsT_intro fun l params cont vs f rest m hl => ?_
  dsimp only [t6LsT]
  iintro HL
  icases HL with (Hr | Hother)
  · icases Hr with %hpure
    obtain ⟨rfl, rfl, rfl, f', rest', hρ, hf⟩ := hpure
    obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
    rw [hQ, t6Q_ret] at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    rw [t6RetParams_bindArgs]
    unfold t6RetCont t5Pure
    iapply wpt_pure (psym (t6a 531)) _ (Nat.le_refl 2) rfl
      (t1sym_eval hex _ (by t6_lookup))
    iintro %σ' %ns %κs %nt -
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    rfl
  · icases Hother with (Hb | Hc)
    · icases Hb with ⟨%hpure, Hcells⟩
      obtain ⟨rfl, rfl⟩ := hpure
      rw [hQ, t6Q_break] at hl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
      dsimp only [t6Cells]
      icases Hcells with ⟨%px, %pr, %f', %rest', %hargs, Hx, Hr⟩
      obtain ⟨rfl, hρ, hf⟩ := hargs
      obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
      rw [t6PtrParams_bindArgs]
      iapply wpt_t6Break hstd hex hQ
        (envAdd t6rSym (Vobject (OVpointer pr)) (envAdd t6xSym (Vobject (OVpointer px)) f)) rest (by t6_frame) px pr (by t6_lookup) (by t6_lookup)
      isplitl [Hx]
      · iexact Hx
      iexact Hr
    · icases Hc with ⟨%hpure, Hcells⟩
      obtain ⟨rfl, rfl⟩ := hpure
      rw [hQ, t6Q_case2] at hl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
      dsimp only [t6Cells]
      icases Hcells with ⟨%px, %pr, %f', %rest', %hargs, Hx, Hr⟩
      obtain ⟨rfl, hρ, hf⟩ := hargs
      obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
      rw [t6PtrParams_bindArgs]
      iapply wpt_t6Case2 hstd hex hQ hsup
        (envAdd t6rSym (Vobject (OVpointer pr)) (envAdd t6xSym (Vobject (OVpointer px)) f)) rest (by t6_frame) px pr (by t6_lookup) (by t6_lookup)
      isplitl [Hx]
      · iexact Hx
      iexact Hr

theorem wpt_t6Switch [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t6Q)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (px pr : CerbMem.PointerValue)
    (hx : fmapLookupBy symCmpK t6xSym f = some (Vobject (OVpointer px)))
    (hr : fmapLookupBy symCmpK t6rSym f = some (Vobject (OVpointer pr))) :
    iprop(pointsToCell M.tagDefs (GF := GF) px (.own 1) intTy (emittedIntBytes M.tagDefs 2) ∗
      pointsToCell M.tagDefs pr (.own 1) intTy (emittedIntBytes M.tagDefs 0)) ⊢
      wpt M p (t6LsT GF M.tagDefs) emptyProcSpecT 58 Ψ CorpusE0.t6Switch (f :: rest) := by
  iintro ⟨Hx, Hr⟩
  unfold CorpusE0.t6Switch letS bnd
  rw [show (Pattern [] (CaseBase (some (t6a 517), CorpusE0.lint)) : pattern) =
    symPat [] (t6a 517) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 51
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_t6Load hex t6xSym 516 47 48 f rest hf px (emittedIntBytes M.tagDefs 2) (lint 2) hx rfl rfl
  isplitl [Hx]
  · iexact Hx
  iintro %fp Hx
  simp only [SpikeVal.val]
  iexists (lint 2)
  isplit
  · ipureintro; rfl
  rw [update_env_sym, show (51 : Nat) = 50 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl (t1sym_eval hex rest (by t6_lookup))
  rw [show (50 : Nat) = 49 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl (CorpusE0.t6Switch_select (lint 2))
  unfold t6SpecifiedBranch letS
  rw [show (Pattern [] (CaseBase (some (t6a 519), BTy_object OTy_integer)) : pattern) =
    symPat [] (t6a 519) (BTy_object OTy_integer) from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 2 47
  unfold t5Pure
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl
    (evalPexpr_convInt_call_int [] hstd (by rw [intCty, evalPexpr_val]; rfl)
      (by rw [evalPexpr_val]; rfl) (show -2147483648 ≤ (2 : Int) by decide)
      (show (2 : Int) ≤ 2147483647 by decide))
  iexists (oint 2)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  unfold t6Dispatch seqE wc
  iapply wpt_seq _ _ _ _ _ _ _ 2 45
  rw [show (2 : Nat) = 1 + 1 from rfl]
  iapply wpt_if_false _ _ _ _ _ (by
    rw [evalPexpr_op, t1sym_eval hex rest (by t6_lookup), evalPexpr_val]; rfl)
  unfold t5Unit t5Pure
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 45 0
  rw [show (45 : Nat) = 44 + 1 from rfl]
  iapply wpt_if_true _ _ _ _ _ (by
    rw [evalPexpr_op, t1sym_eval hex rest (by t6_lookup), evalPexpr_val]; rfl)
  unfold t6Run
  iapply wpt_run [] empty_annotation t6Case2Sym [psym t6xSym, psym t6rSym] _ rest 43
    (by rw [hQ]; exact t6Q_case2)
    (by rw [evalPexprs_cons, t1sym_eval hex rest (by t6_lookup),
      evalPexprs_cons, t1sym_eval hex rest (by t6_lookup), evalPexprs_nil]; rfl)
    (Nat.le_refl 44)
  dsimp only [t6LsT]
  iright
  iright
  isplit
  · ipureintro; exact ⟨rfl, rfl⟩
  dsimp only [t6Cells]
  iexists px, pr, _, rest
  isplit
  · ipureintro; exact ⟨rfl, rfl, by t6_frame⟩
  isplitl [Hx]
  · iexact Hx
  iexact Hr

/-- Total proof of the emitted main: 20 units for initialization and 58 for the switch and its label path. -/
theorem t6_wpt [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = t6Q)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4)) ⊢
      wpt M p (t6LsT GF M.tagDefs) emptyProcSpecT 78 (readoutPost ψT6) t6Main (f :: rest) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapX, HcapR⟩
  simp only [t6Main, letS, seqE, wc, bnd, createInt_eq, act_store_eq]
  rw [show (Pattern [] (CaseBase (some t6xSym, ptrTy)) : pattern) =
    symPat [] t6xSym ptrTy from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 75
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty
    (PrefSource (t6Reg 15 135) [t6xSym]) _
    (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t6Reg 15 135) [t6xSym])
    _ (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapX]
  · iexact HcapX
  iintro %px ⟨Hx, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some t6rSym, ptrTy)) : pattern) = symPat [] t6rSym ptrTy from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 72
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty
    (PrefSource (t6Reg 15 135) [t6rSym]) _
    (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t6Reg 15 135) [t6rSym])
    _ (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapR]
  · iexact HcapR
  iintro %pr ⟨Hr, -⟩
  iexists (Vobject (OVpointer pr))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (t6a 514), CorpusE0.lint)) : pattern) =
    symPat [] (t6a 514) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 69
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_pure (specInt 2) _ (Nat.le_refl 2) rfl (specInt_eval _ 2)
  simp only [SpikeVal.val]
  iexists (lint 2)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 4 65
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ intTy (psym t6xSym) (convLoadedInt (t6a 514)) NA _
    rfl (pv := px) (cv := lint 2) (t1sym_eval hex rest (by t6_lookup))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by t6_lookup)) (by decide) (by decide))
  iapply wpt_store _ _ _ intTy px (lint 2) NA (emittedIntMval 2) _ _ (Nat.le_refl 3)
    (emittedInt_encodes _ 2) (emittedInt_storable _ 2)
  isplitl [Hx]
  · iexact Hx
  iintro %fpX Hx
  simp only [SpikeVal.mergeInto]
  rw [show (Pattern [] (CaseBase (some (t6a 515), CorpusE0.lint)) : pattern) =
    symPat [] (t6a 515) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 62
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_pure (specInt 0) _ (Nat.le_refl 2) rfl (specInt_eval _ 0)
  iexists (lint 0)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 4 58
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ intTy (psym t6rSym) (convLoadedInt (t6a 515)) NA _
    rfl (pv := pr) (cv := lint 0) (t1sym_eval hex rest (by t6_lookup))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by t6_lookup)) (by decide) (by decide))
  iapply wpt_store _ _ _ intTy pr (lint 0) NA (emittedIntMval 0) _ _ (Nat.le_refl 3)
    (emittedInt_encodes _ 0) (emittedInt_storable _ 0)
  isplitl [Hr]
  · iexact Hr
  iintro %fpR Hr
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 58 0
  iapply wpt_t6Switch hstd hex hQ
    (envAdd (t6a 515) (lint 0) (envAdd (t6a 514) (lint 2)
      (envAdd t6rSym (Vobject (OVpointer pr)) (envAdd t6xSym (Vobject (OVpointer px)) f))))
    rest (by t6_frame) px pr (by t6_lookup) (by t6_lookup)
  isplitl [Hx]
  · iexact Hx
  iexact Hr

theorem t6DefaultTail_frag : Frag t6DefaultTail :=
  .sseq (CorpusE0.t6Save_frag _ _ _ (CorpusE0.t6AssignStmt_frag _ _ _ _))
    (.sseq (CorpusE0.t6Run_frag _ _) (.val_pure _))

theorem t6Case2Tail_frag : Frag t6Case2Tail :=
  .sseq (CorpusE0.t6Save_frag _ _ _ (CorpusE0.t6AssignStmt_frag _ _ _ _))
    (.sseq (CorpusE0.t6Run_frag _ _) t6DefaultTail_frag)

theorem t6CaseContext_frag (body : CoreExpr) (hb : Frag body) : Frag (t6CaseContext body) :=
  .sseq (.sseq hb (.val_pure _))
    (.sseq (CorpusE0.t6Save_frag _ _ _ (.val_pure _))
      (.sseq (.val_pure _) CorpusE0.t6Return_frag))

theorem t6Q_frag {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t6Q l = some (params, cont)) : Frag cont := by
  have hc := t6Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact t6CaseContext_frag _ (.sseq (CorpusE0.t6AssignStmt_frag _ _ _ _)
      (.sseq (CorpusE0.t6Run_frag _ _) t6Case2Tail_frag))
  · exact t6CaseContext_frag _ (.sseq (CorpusE0.t6AssignStmt_frag _ _ _ _)
      (.sseq (CorpusE0.t6Run_frag _ _) t6DefaultTail_frag))
  · exact t6CaseContext_frag _ (.sseq (CorpusE0.t6AssignStmt_frag _ _ _ _)
      (.sseq (CorpusE0.t6Run_frag _ _) (.val_pure _)))
  · exact .sseq (.val_pure _) (.sseq (.val_pure _) CorpusE0.t6Return_frag)
  · exact Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _)

theorem t6Q_pot {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t6Q l = some (params, cont)) : pot cont ≤ lemDefaultFuel := by
  have hc := t6Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl

theorem collect_new_t6Main :
    collect_labeled_continuations_NEW (prodFileLib stdlibE3 [] t6Main) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym t6Q fmapEmpty := rfl

theorem t6Main_labeledAt (sup : Nat) :
    LabeledAt (prodRSLib stdlibE3 [] sup t6Main) mainSym t6Q := by
  unfold LabeledAt
  rw [prodRSLib_labeled, collect_new_t6Main, fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

theorem t6Main_pot : pot t6Main ≤ lemDefaultFuel := Nat.le_of_ble_eq_true rfl

/-- The shipped driver returns Specified(20) on the transcribed switch
    and the current checked three-function std.core fragment. The premise
    `600 ≤ sup` is a SUFFICIENT floor (it keeps the fresh symbol the negative
    assignment draws away from every source binding), not a necessary one:
    the compiled composite delivers the same result at `sup = 0` (measured,
    docs/2026-09-07_l1-landing-notes.md). -/
theorem t6_certified_production (sup : Nat) (hsup : 600 ≤ sup)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 [] t6Main) args)
          ((initial_driver_state sup (prodFileLib stdlibE3 [] t6Main) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 20 ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQe := t6Main_labeledAt sup
  have hlbl := prodCtx_labels (f := prodFileLib stdlibE3 [] t6Main) hQe
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ_lib1 sup stdlibE3 t6Main hQe ψT6 78
      (wpt_driver_done_alloc (GF := SpikeGF) (ctl := prodCtl sup)
        (M₀ := prodCtx (prodFileLib stdlibE3 [] t6Main) (prodRSLib stdlibE3 [] sup t6Main))
        rfl rfl hlbl rfl rfl rfl rfl (Nat.le_refl _)
        (fun l params cont hl => t6Q_frag (by rw [← hlbl]; exact hl))
        (fun l params cont hl => t6Q_pot (by rw [← hlbl]; exact hl))
        (t6LsT SpikeGF fmapEmpty)
        t6Main fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
        (allocCost fmapEmpty intTy 4 + allocCost fmapEmpty intTy 4) CorpusE0.t6Main_frag
        t6Main_pot
        (prodMem₀_launchCoh _ prod_two_int_budget_fits)
        ψT6 78
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply t6_blockSpecsT
              (M := prodCtx (prodFileLib stdlibE3 [] t6Main) (prodRSLib stdlibE3 [] sup t6Main))
              rfl (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl hsup
          · iapply t6_wpt (M := prodCtx (prodFileLib stdlibE3 [] t6Main) (prodRSLib stdlibE3 [] sup t6Main))
              rfl (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl fmapEmpty []
              symFrame_empty $$ Hcap))
      (by rw [show CerbFuel.driverFuel = 99999999 + 1 from rfl]; omega)
      fs args
  exact ⟨dres, dst', heq, hψ, hbl, hout, herr⟩

end CerberusHeapLang
