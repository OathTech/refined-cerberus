/- Public total proof and genuine-driver certificate for the complete captured t4 file. -/
import CerberusHeapLang.Examples.EmittedT4
import CerberusHeapLang.EmittedIntSupport
import CerberusHeapLang.ProdEntry

set_option autoImplicit false
namespace CerberusHeapLang.CorpusA7.T4
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (psym seqE letS letW bnd act specInt wc)
open EmittedStdCore (sintTyAnn HasIntLibrary)
open EmittedIntSupport
variable {GF : BundledGFunctors}

def loopContext (body : CoreExpr) : CoreExpr :=
  seqE (seqE (Expr [Aloc (loc 40 88), Astmt] (Esseq wc body afterWhile))
    (seqE returnStmt cleanup)) returnSave

def whileCont : CoreExpr := loopContext loopTest
def continueCont : CoreExpr := loopContext
  (seqE (seqE (Expr [Aloc (loc 40 88), Astmt] (Epure (Pexpr [] () (PEval Vunit)))) unitE)
    (Expr [] (Erun empty_annotation whileSym [psym iSym, psym sSym])))
def breakCont : CoreExpr :=
  seqE (seqE (seqE (Expr [Aloc (loc 40 88), Astmt] (Epure (Pexpr [] () (PEval Vunit)))) unitE)
    (seqE returnStmt cleanup)) returnSave
def retCont : CoreExpr := pureE (psym (tmp 91))
def ptrParams : List (sym × core_base_type) := [(iSym, ptrBty), (sSym, ptrBty)]
def retParams : List (sym × core_base_type) := [(tmp 91, intBty)]
def Q : LabelMap := collect_saves mainBody

theorem Q_eq : Q =
    fmapAddBy symCmpL continueSym (ptrParams, continueCont)
    (fmapAddBy symCmpL whileSym (ptrParams, whileCont)
    (fmapAddBy symCmpL retSym (retParams, retCont)
    (fmapAddBy symCmpL breakSym (ptrParams, breakCont) fmapEmpty))) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let some (_, _, rhs) := target.eq? | throwError "expected an equality"
    let proof ← Lean.Meta.mkEqRefl rhs
    let lemmaName ← Lean.withOptions (Lean.Elab.async.set · false) do
      Lean.Meta.mkAuxLemma [] target proof
    goal.assign (Lean.mkConst lemmaName)
    Lean.Elab.Tactic.replaceMainGoal []

theorem Q_while : lookupLabel Q whileSym = some (ptrParams, whileCont) := by rw [Q_eq]; rfl
theorem Q_continue : lookupLabel Q continueSym = some (ptrParams, continueCont) := by rw [Q_eq]; rfl
theorem Q_break : lookupLabel Q breakSym = some (ptrParams, breakCont) := by rw [Q_eq]; rfl
theorem Q_ret : lookupLabel Q retSym = some (retParams, retCont) := by rw [Q_eq]; rfl

theorem Q_lookup (l : sym) : lookupLabel Q l =
    if symOrd l continueSym = .eq then some (ptrParams, continueCont)
    else if symOrd l whileSym = .eq then some (ptrParams, whileCont)
    else if symOrd l retSym = .eq then some (retParams, retCont)
    else if symOrd l breakSym = .eq then some (ptrParams, breakCont)
    else none := by
  rw [Q_eq]
  unfold lookupLabel
  rw [labelAdd_lookup (((symMap_empty.addLabel _ _).addLabel _ _).addLabel _ _),
    labelAdd_lookup ((symMap_empty.addLabel _ _).addLabel _ _),
    labelAdd_lookup (symMap_empty.addLabel _ _), labelAdd_lookup symMap_empty]
  rfl

theorem Q_cont {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel Q l = some (params, cont)) :
    cont ∈ [continueCont, whileCont, breakCont, retCont] := by
  rw [Q_lookup] at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · split at h
        · cases h; simp
        · cases h

theorem loopContext_frag (body : CoreExpr) (hb : Frag body) : Frag (loopContext body) :=
  .sseq (.sseq (.sseq hb afterWhile_frag) (.sseq returnStmt_frag cleanup_frag)) returnSave_frag

theorem Q_frag {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel Q l = some (params, cont)) : Frag cont := by
  have hc := Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · refine loopContext_frag _ (.sseq (.sseq (.val_pure _) (.val_pure _)) (.run ?_))
    intro pe hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact .sym _ _
  · exact loopContext_frag _ (.sseq_sym cond_frag (.sseq_sym boolE_frag
      (.if_ (.sym _ _) body_frag (.val_pure _))))
  · exact .sseq (.sseq (.sseq (.val_pure _) (.val_pure _))
      (.sseq returnStmt_frag cleanup_frag)) returnSave_frag
  · exact Frag.of_pePure _ (.sym _ _)

theorem Q_depth [LemFuel] (hfuel : 40 ≤ LemFuel.fuel)
    {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel Q l = some (params, cont)) : evalDepth cont ≤ LemFuel.fuel := by
  have hc := Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    exact Nat.le_trans (by decide +kernel : evalDepth _ ≤ 40) hfuel


theorem wpt_load_exact [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (ty : ctype) (x : sym) (n lo hi : Nat)
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv ty bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (pointsToCell M.tagDefs pv (.own 1) ty bs -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pv ty)] v)
          (envAdd (tmp n) (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (load ty x n lo hi) (f :: rest) :=
  wpt_boundLoad hex (exprAnn (loc lo hi)) [] [Aloc (loc lo hi), Aexpr] [] [] []
    ptrBty (loc lo hi) empty_annotation ty x (tmp n) NA
    f rest hf pv (.own 1) bs v hl hload htrap

theorem wpt_load [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (ty : ctype) (x : sym) (n lo hi : Nat)
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv ty bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) ty bs -∗
        Ψ (.annot [DA_pos [] fp] v) (envAdd (tmp n) (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (load ty x n lo hi) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_load_exact hex ty x n lo hi f rest hf pv bs v hl hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro Hpt
  iapply HΨ $$ %_ Hpt

def bit (b : Bool) : Int := if b then 1 else 0

theorem tmp_ne {m n : Nat} (h : m ≠ n) : symOrd (tmp m) (tmp n) ≠ .eq :=
  symOrd_ne_eq_of_num_ne h

theorem intTuple_eval [LemFuel] {M : MachineCtx} (n m : Nat) (ρ : EnvStack) (v w : value)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym (tmp n)) = some v)
    (hw : evalPexpr M.tagDefs M.extern M.file ρ (psym (tmp m)) = some w) :
    evalPexpr M.tagDefs M.extern M.file ρ (intTuple n m) = some (Vtuple [v,w]) := by
  unfold intTuple
  rw [evalPexpr_ctor2, hv, hw]
  rfl

def cmpBranch (ac : List annot) (op : binop) (v k : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEop op
    (Pexpr ac () (PEcall (Sym EmittedStdCore.convInt.1) [tyPe (sintTyAnn []), ointPe v]))
    (Pexpr ac () (PEcall (Sym EmittedStdCore.convInt.1) [tyPe (sintTyAnn []), ointPe k]))))
    (specInt 1) (specInt 0))

theorem cmpBranch_eval [LemFuel] {M : MachineCtx} (hstd : HasIntLibrary M.file)
    (ρ : EnvStack) (ac : List annot) (op : binop) (v k : Int) (b : Bool)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (hk1 : -2147483648 ≤ k) (hk2 : k ≤ 2147483647)
    (hop : evalBinop op (oint v) (oint k) = some (boolValue b)) :
    evalPexpr M.tagDefs M.extern M.file ρ (cmpBranch ac op v k) = some (lint (bit b)) := by
  unfold cmpBranch
  rw [evalPexpr_if, if_pos (show (isPePure (specInt 1) && isPePure (specInt 0)) = true from rfl),
    evalPexpr_op,
    EmittedStdCore.eval_convInt_call ac hstd (by unfold tyPe; rw [evalPexpr_val])
      (by unfold ointPe; rw [evalPexpr_val]) hv1 hv2,
    EmittedStdCore.eval_convInt_call ac hstd (by unfold tyPe; rw [evalPexpr_val])
      (by unfold ointPe; rw [evalPexpr_val]) hk1 hk2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hop]
  cases b <;> simp only [boolValue, Option.bind_some, bit, Bool.false_eq_true, ↓reduceIte]
  · exact specInt_eval ρ 0
  · exact specInt_eval ρ 1

abbrev frLt (t n m : Nat) (pv : CerbMem.PointerValue) (v k : Int) (f : Fmap sym value) :=
  envAdd (tmp n) (lint v) (envAdd (tmp m) (lint k) (envAdd (tmp t) (Vobject (OVpointer pv)) f))


/-- A loaded signed-int comparison retains its actual read footprint. -/
theorem wpt_lt [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (ty : ctype) (x : sym) (t n m a b start : Nat) (v k : Int) (hnm : m ≠ n)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (hk1 : -2147483648 ≤ k) (hk2 : k ≤ 2147483647)
    (hsel : select_case subst_sym_expr (Vtuple [lint v, lint k])
      (ltPats (locP start (start + 5) (start + 2)) a b) =
      some (Expr [Astd "§6.5.8#6"] (Epure (cmpBranch [Astd "§6.5.8#3"] OpLt v k))))
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hx : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv ty bs = lint v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) ty bs -∗
        Ψ (.annot [DA_pos [] fp] (lint (bit (decide (v < k)))))
          (frLt t n m pv v k f :: rest))) ⊢
      wpt M p Ls Θ 16 Ψ (lt ty x t n m a b start k) (f :: rest) := by
  unfold frLt bit
  iintro ⟨Hpt, HΨ⟩
  unfold lt
  rw [show intTuplePat n m = tuplePat [] [([], some (tmp n), intBty),
    ([], some (tmp m), intBty)] from rfl]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ 11 5
  iapply wpt_mono_k (show 6 + 3 ≤ 11 by decide)
  unfold literal
  iapply wpt_unseq_value_right
  iapply wpt_load hex ty x t start (start + 1) f rest hf pv bs (lint v) hx hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint v, lint k], [DA_pos [] fp]
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_annot
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl (cval := Vtuple [lint v, lint k])
    (intTuple_eval n m _ _ _
      (symbol_eval hex (by emitted_frame) rest []
        (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_pos (symOrd_self _)]))
      (symbol_eval hex (by emitted_frame) rest []
        (by rw [envAdd_lookup (((hf.add _ _).add _ _)),
          if_neg (tmp_ne hnm), envAdd_lookup (hf.add _ _), if_pos (symOrd_self _)])))
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl hsel
  iapply wpt_pure (cmpBranch [Astd "§6.5.8#3"] OpLt v k) _ (Nat.le_refl 2) rfl
    (cmpBranch_eval hstd _ _ OpLt v k (decide (v < k)) hv1 hv2 hk1 hk2 rfl)
  simp only [SpikeVal.merge, bit]
  iapply HΨ $$ %fp Hpt


def truthBranch (negate b : Bool) : generic_pexpr Unit sym :=
  let eq0 := PEop OpEq
    (Pexpr [Astd "§6.5.9#4, sentence 1"] () (PEcall (Sym EmittedStdCore.convInt.1)
      [tyPe (sintTyAnn []), ointPe (bit b)]))
    (Pexpr [Astd "§6.5.9#4, sentence 1"] () (PEcall (Sym EmittedStdCore.convInt.1)
      [tyPe (sintTyAnn []), ointPe 0]))
  let test := Pexpr [Astd "§6.5.9#4, sentence 3"] ()
    (if negate then PEnot (Pexpr [] () eq0) else eq0)
  Pexpr [Astd "§6.5.9#3"] () (PEif test (specInt 1) (specInt 0))

theorem truthBranch_eval [LemFuel] {M : MachineCtx} (hstd : HasIntLibrary M.file)
    (ρ : EnvStack) (negate b : Bool) :
    evalPexpr M.tagDefs M.extern M.file ρ (truthBranch negate b) =
      some (lint (bit (if negate then b else !b))) := by
  cases negate with
  | false =>
    unfold truthBranch
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [evalPexpr_if, if_pos (show (isPePure (specInt 1) && isPePure (specInt 0)) = true from rfl),
      evalPexpr_op,
      EmittedStdCore.eval_convInt_call _ hstd (by unfold tyPe; rw [evalPexpr_val])
        (by unfold ointPe; rw [evalPexpr_val]) (by cases b <;> decide) (by cases b <;> decide),
      EmittedStdCore.eval_convInt_call _ hstd (by unfold tyPe; rw [evalPexpr_val])
        (by unfold ointPe; rw [evalPexpr_val]) (by decide) (by decide)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases b
    · change evalPexpr M.tagDefs M.extern M.file ρ (specInt 1) = _
      exact specInt_eval ρ 1
    · change evalPexpr M.tagDefs M.extern M.file ρ (specInt 0) = _
      exact specInt_eval ρ 0
  | true =>
    unfold truthBranch
    simp only [↓reduceIte]
    rw [evalPexpr_if, if_pos (show (isPePure (specInt 1) && isPePure (specInt 0)) = true from rfl),
      evalPexpr_not, evalPexpr_op,
      EmittedStdCore.eval_convInt_call _ hstd (by unfold tyPe; rw [evalPexpr_val])
        (by unfold ointPe; rw [evalPexpr_val]) (by cases b <;> decide) (by cases b <;> decide),
      EmittedStdCore.eval_convInt_call _ hstd (by unfold tyPe; rw [evalPexpr_val])
        (by unfold ointPe; rw [evalPexpr_val]) (by decide) (by decide)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases b
    · change evalPexpr M.tagDefs M.extern M.file ρ (specInt 0) = _
      exact specInt_eval ρ 0
    · change evalPexpr M.tagDefs M.extern M.file ρ (specInt 1) = _
      exact specInt_eval ρ 1

/-- One actual truth conversion, preserving source annotations and the
entire dynamic footprint produced by its operand. -/
theorem wpt_truth [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (l : CerbLocation.Loc) (n m a b : Nat) (negate bit' : Bool) (hnm : m ≠ n)
    (e : CoreExpr)
    (hsel : select_case subst_sym_pexpr (Vtuple [lint (bit bit'), lint 0]) (truthPats l a b negate) =
      some (truthBranch negate bit'))
    (f : Fmap sym value) (rest : EnvStack) (k : Nat) :
    wpt M p Ls Θ k (fun w ρ' => iprop(∃ (f' : Fmap sym value) (rest' : EnvStack)
        (ds : List dyn_annotation),
      ⌜w = .annot ds (lint (bit bit')) ∧ ρ' = f' :: rest' ∧ SymFrame f'⌝ ∗
      Ψ (.annot ds (lint (bit (if negate then bit' else !bit'))))
        (envAdd (tmp n) (lint (bit bit')) (envAdd (tmp m) (lint 0) f') :: rest'))) e (f :: rest) ⊢
    wpt M p Ls Θ (k + 8) Ψ (truth l n m a b negate e) (f :: rest) := by
  iintro H
  unfold truth
  rw [show intTuplePat n m = tuplePat [] [([], some (tmp n), intBty),
    ([], some (tmp m), intBty)] from rfl]
  rw [show k + 8 = (k + 5) + 3 by omega]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ (k + 5) 3
  iapply wpt_mono_k (show k + 3 ≤ k + 5 by omega)
  unfold literal
  iapply wpt_unseq_value_right
  iapply wpt_mono ?_ k e (f :: rest) $$ H
  intro w ρ'
  iintro ⟨%f', %rest', %ds, %hw, HΨ⟩
  obtain ⟨rfl, rfl, hf'⟩ := hw
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint (bit bit'), lint 0], ds
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_annot
  unfold pureE
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl ?_
  · rw [evalPexpr_case, if_pos (show isPePureAlts (truthPats l a b negate) = true by cases negate <;> rfl),
      intTuple_eval n m _ _ _
        (symbol_eval hex (by emitted_frame) rest' [] (by rw [envAdd_lookup (hf'.add _ _), if_pos (symOrd_self _)]))
        (symbol_eval hex (by emitted_frame) rest' [] (by rw [envAdd_lookup (hf'.add _ _), if_neg (tmp_ne hnm),
          envAdd_lookup hf', if_pos (symOrd_self _)]))]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [hsel]
    rw [Option.bind_some, if_pos (by cases negate <;> exact Nat.le_of_ble_eq_true rfl)]
    rw [evalPexpr_reannot0]
    change evalPexpr M.tagDefs M.extern M.file _ (truthBranch negate bit') = _
    exact truthBranch_eval hstd _ negate bit'
  simp only [SpikeVal.merge]
  iexact HΨ

abbrev frTruth (n m : Nat) (b : Bool) (f : Fmap sym value) :=
  envAdd (tmp n) (lint (bit b)) (envAdd (tmp m) (lint 0) f)
abbrev frLeft (pi : CerbMem.PointerValue) (v : Int) (f : Fmap sym value) :=
  frTruth 41 42 (!(decide (v < 5))) (frTruth 46 47 (decide (v < 5)) (frLt 51 52 53 pi v 5 f))
abbrev frRight (ps : CerbMem.PointerValue) (v : Int) (f : Fmap sym value) :=
  frTruth 60 61 (decide (v < 7)) (frLt 65 66 67 ps v 7 f)

end CerberusHeapLang.CorpusA7.T4
