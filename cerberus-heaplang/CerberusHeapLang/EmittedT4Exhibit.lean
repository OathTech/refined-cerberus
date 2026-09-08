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

theorem psym_eval [LemFuel] {M : MachineCtx}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    {x : sym} {f : Fmap sym value} {v : value} (hf : SymFrame f)
    (rest : EnvStack) (hl : fmapLookupBy symCmpK x f = some v) :
    evalPexpr M.tagDefs M.extern M.file (f :: rest) (psym x) = some v :=
  symbol_eval hex hf rest [] hl

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
      (psym_eval hex (by emitted_frame) rest
        (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_pos (symOrd_self _)]))
      (psym_eval hex (by emitted_frame) rest
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
        (psym_eval hex (by emitted_frame) rest' (by rw [envAdd_lookup (hf'.add _ _), if_pos (symOrd_self _)]))
        (psym_eval hex (by emitted_frame) rest' (by rw [envAdd_lookup (hf'.add _ _), if_neg (tmp_ne hnm),
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


theorem convLoaded_eval [LemFuel] {M : MachineCtx} {ρ : EnvStack}
    (hstd : HasIntLibrary M.file) {a ta : List annot} {s : sym} {n : Int}
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym s) = some (lint n))
    (hlo : -2147483648 ≤ n) (hhi : n ≤ 2147483647) :
    evalPexpr M.tagDefs M.extern M.file ρ (convLoaded a (sintTyAnn ta) s) = some (lint n) :=
  EmittedStdCore.eval_convLoadedInt_spec a hstd
    (by unfold tyPe; rw [evalPexpr_val]) hv hlo hhi

theorem wpt_left [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (v : Int) (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pi : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hi : fmapLookupBy symCmpK iSym f = some (Vobject (OVpointer pi)))
    (hload : loadedVal M.tagDefs pi iTy bs = lint v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pi, iTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy bs ∗
      (∀ fp, pointsToCell M.tagDefs pi (.own 1) iTy bs -∗
        Ψ (.annot [DA_pos [] fp] (lint (bit (decide (v < 5))))) (frLeft pi v f :: rest))) ⊢
      wpt M p Ls Θ 32 Ψ left (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold left
  iapply wpt_truth hstd hex _ 41 42 43 44 false (!(decide (v < 5)))
    (by decide) _ (by cases h : decide (v < 5) <;> rfl) f rest 24
  iapply wpt_truth hstd hex _ 46 47 48 49 false (decide (v < 5))
    (by decide) _ (by cases h : decide (v < 5) <;> rfl) f rest 16
  iapply wpt_lt hstd hex iTy iSym 51 52 53 54 55 47 v 5 (by decide)
    hv1 hv2 (by decide) (by decide) rfl f rest hf pi bs hi hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  iexists frLt 51 52 53 pi v 5 f, rest, [DA_pos [] fp]
  isplit
  · ipureintro; exact ⟨rfl, rfl, by emitted_frame⟩
  iexists frTruth 46 47 (decide (v < 5)) (frLt 51 52 53 pi v 5 f), rest, [DA_pos [] fp]
  isplit
  · ipureintro; exact ⟨rfl, rfl, by emitted_frame⟩
  simp only [Bool.not_not, Bool.false_eq_true, ↓reduceIte, frLeft, frTruth]
  iapply HΨ $$ %fp Hpt

theorem wpt_right [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (v : Int) (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (ps : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hs : fmapLookupBy symCmpK sSym f = some (Vobject (OVpointer ps)))
    (hload : loadedVal M.tagDefs ps sTy bs = lint v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf ps, sTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) ps (.own 1) sTy bs ∗
      (∀ fp, pointsToCell M.tagDefs ps (.own 1) sTy bs -∗
        Ψ (.annot [DA_pos [] fp] (lint (bit (decide (v < 7))))) (frRight ps v f :: rest))) ⊢
      wpt M p Ls Θ 24 Ψ right (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold right
  iapply wpt_truth hstd hex _ 60 61 62 63 true (decide (v < 7))
    (by decide) _ (by cases h : decide (v < 7) <;> rfl) f rest 16
  iapply wpt_lt hstd hex sTy sSym 65 66 67 68 69 56 v 7 (by decide)
    hv1 hv2 (by decide) (by decide) rfl f rest hf ps bs hs hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  iexists frLt 65 66 67 ps v 7 f, rest, [DA_pos [] fp]
  isplit
  · ipureintro; exact ⟨rfl, rfl, by emitted_frame⟩
  simp only [↓reduceIte, frRight, frTruth]
  iapply HΨ $$ %fp Hpt

/-- Only the source pointers survive as logical interface to the next
    statement; emitted temporary bindings may accumulate in the frame. -/
def SourceFrame (pi ps : CerbMem.PointerValue) (f : Fmap sym value) : Prop :=
  SymFrame f ∧ fmapLookupBy symCmpK iSym f = some (Vobject (OVpointer pi)) ∧
    fmapLookupBy symCmpK sSym f = some (Vobject (OVpointer ps))

theorem SourceFrame.add {pi ps : CerbMem.PointerValue} {f : Fmap sym value}
    (n : Nat) (v : value) (hn : 23 ≤ n) (h : SourceFrame pi ps f) :
    SourceFrame pi ps (envAdd (tmp n) v f) := by
  have hi : symOrd iSym (tmp n) ≠ .eq := symOrd_ne_eq_of_num_ne (by omega)
  have hs : symOrd sSym (tmp n) ≠ .eq := symOrd_ne_eq_of_num_ne (by omega)
  exact ⟨h.1.add _ _, by rw [envAdd_lookup h.1, if_neg hi]; exact h.2.1,
    by rw [envAdd_lookup h.1, if_neg hs]; exact h.2.2⟩

local macro "t4_source" : tactic => `(tactic|
  repeat first | assumption | apply SourceFrame.add _ _ (by decide +kernel))


theorem wpt_andE [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (i s : Int) (hi1 : -2147483648 ≤ i) (hi2 : i ≤ 2147483647)
    (hs1 : -2147483648 ≤ s) (hs2 : s ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : SourceFrame pi ps f)
    (hli : loadedVal M.tagDefs pi iTy bi = lint i)
    (hti : cellLoadTrap M.tagDefs ⟨addrOf pi, iTy, bi⟩ = false)
    (hls : loadedVal M.tagDefs ps sTy bs = lint s)
    (hts : cellLoadTrap M.tagDefs ⟨addrOf ps, sTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) sTy bs ∗
      (∀ (f' : Fmap sym value) (ds : List dyn_annotation), ⌜SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) iTy bi -∗ pointsToCell M.tagDefs ps (.own 1) sTy bs -∗
        Ψ (.annot ds (lint (bit (decide (i < 5) && decide (s < 7))))) (f' :: rest))) ⊢
      wpt M p Ls Θ 63 Ψ andE (f :: rest) := by
  have hframe : SymFrame f := hf.1
  iintro ⟨Hi, Hs, HΨ⟩
  unfold andE letS
  rw [show (Pattern [] (CaseBase (some (tmp 57), intBty)) : pattern) =
    symPat [] (tmp 57) intBty from rfl]
  iapply wpt_seq_sym_annot _ _ _ _ _ _ _ _ 32 31
  iapply wpt_left hstd hex i hi1 hi2 f rest hf.1 pi bi hf.2.1 hli hti
  isplitl [Hi]
  · iexact Hi
  iintro %fpi Hi
  iexists lint (bit (decide (i < 5))), [DA_pos [] fpi]
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (31 : Nat) = 30 + 1 from rfl]
  iapply wpt_annot
  rw [show (30 : Nat) = 29 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl
    (psym_eval hex (by emitted_frame) rest (by rw [envAdd_lookup (by emitted_frame), if_pos (symOrd_self _)]))
  rw [show (29 : Nat) = 28 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl (by rw [and_select]; rfl)
  unfold andSpecified
  have hfa : SourceFrame pi ps
      (envAdd (tmp 57) (lint (bit (decide (i < 5)))) (frLeft pi i f)) := by t4_source
  by_cases hi5 : i < 5
  · have hb : decide (i < 5) = true := decide_eq_true hi5
    simp only [hb, Bool.true_and] at *
    rw [show (28 : Nat) = 27 + 1 from rfl]
    iapply wpt_if_false _ _ _ _ _ (by rw [evalPexpr_op, evalPexpr_val, evalPexpr_val]; rfl)
    unfold letS
    rw [show (Pattern [] (CaseBase (some (tmp 71), intBty)) : pattern) =
      symPat [] (tmp 71) intBty from rfl]
    iapply wpt_seq_sym_annot _ _ _ _ _ _ _ _ 24 3
    iapply wpt_right hstd hex s hs1 hs2
      (envAdd (tmp 57) (lint (bit true)) (frLeft pi i f)) rest hfa.1 ps bs hfa.2.2 hls hts
    isplitl [Hs]
    · iexact Hs
    iintro %fps Hs
    iexists lint (bit (decide (s < 7))), [DA_pos [] fps]
    isplit
    · ipureintro; rfl
    rw [update_env_sym, show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_annot
    unfold pureE
    iapply wpt_pure _ _ (Nat.le_refl 2) rfl
      (convLoaded_eval hstd (psym_eval hex (by emitted_frame) rest (by rw [envAdd_lookup (by emitted_frame), if_pos (symOrd_self _)]))
        (by cases decide (s < 7) <;> decide) (by cases decide (s < 7) <;> decide))
    simp only [SpikeVal.merge]
    iapply HΨ $$ %_ %_ %(by t4_source) Hi Hs
  · have hb : decide (i < 5) = false := decide_eq_false hi5
    simp only [hb, Bool.false_and] at *
    rw [show (28 : Nat) = 27 + 1 from rfl]
    iapply wpt_if_true _ _ _ _ _ (by rw [evalPexpr_op, evalPexpr_val, evalPexpr_val]; rfl)
    iapply wpt_mono_k (show 4 ≤ 27 by decide)
    unfold letS
    rw [show (Pattern [] (CaseBase (some (tmp 59), intBty)) : pattern) =
      symPat [] (tmp 59) intBty from rfl]
    iapply wpt_seq_sym _ _ _ _ _ _ _ _ 2 2
    unfold literal
    rw [← ofValA_pure (exprAnn .unknown) [] (lint 0)]
    iapply wpt_ofValA (.pure (exprAnn .unknown) [] (lint 0)) _ (by decide)
    simp only [SpikeValA.erase_pure]
    iexists lint 0
    isplit
    · ipureintro; rfl
    rw [update_env_sym]
    unfold pureE
    iapply wpt_pure _ _ (Nat.le_refl 2) rfl
      (convLoaded_eval hstd (psym_eval hex (by emitted_frame) rest (by rw [envAdd_lookup (by emitted_frame), if_pos (symOrd_self _)]))
        (by decide) (by decide))
    simp only [SpikeVal.merge, bit, Bool.false_eq_true, ↓reduceIte]
    iapply HΨ $$ %_ %_ %(by t4_source) Hi Hs

/-- The full controlling expression ends its annotation scope at bound.
    Its result is the emitted equality-to-zero test of the conjunction. -/
theorem wpt_cond [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (i s : Int) (hi1 : -2147483648 ≤ i) (hi2 : i ≤ 2147483647)
    (hs1 : -2147483648 ≤ s) (hs2 : s ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : SourceFrame pi ps f)
    (hli : loadedVal M.tagDefs pi iTy bi = lint i)
    (hti : cellLoadTrap M.tagDefs ⟨addrOf pi, iTy, bi⟩ = false)
    (hls : loadedVal M.tagDefs ps sTy bs = lint s)
    (hts : cellLoadTrap M.tagDefs ⟨addrOf ps, sTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) sTy bs ∗
      (∀ (f' : Fmap sym value), ⌜SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) iTy bi -∗ pointsToCell M.tagDefs ps (.own 1) sTy bs -∗
        Ψ (.pure (lint (bit (!(decide (i < 5) && decide (s < 7)))))) (f' :: rest))) ⊢
      wpt M p Ls Θ 72 Ψ cond (f :: rest) := by
  iintro ⟨Hi, Hs, HΨ⟩
  unfold cond CorpusE0.bnd
  rw [show (72 : Nat) = 71 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_truth hstd hex _ 36 37 38 39 false (decide (i < 5) && decide (s < 7))
    (by decide) _ (by cases decide (i < 5) && decide (s < 7) <;> rfl) f rest 63
  iapply wpt_andE hstd hex i s hi1 hi2 hs1 hs2 f rest pi ps bi bs hf hli hti hls hts
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f' %ds %hf' Hi Hs
  iexists f', rest, ds
  isplit
  · ipureintro; exact ⟨rfl, rfl, hf'.1⟩
  simp only [SpikeVal.val, Bool.false_eq_true, ↓reduceIte]
  iapply HΨ $$ %_ %(by t4_source) Hi Hs

def boolBranch (b : Bool) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEnot
    (Pexpr [] () (PEop OpEq (ointPe (bit (!b))) (ointPe 1)))))
    (Pexpr [] () (PEval Vtrue)) (Pexpr [] () (PEval Vfalse)))

theorem boolE_select (b : Bool) :
    select_case subst_sym_expr (lint (bit (!b))) boolPats =
      some (pureE (boolBranch b)) := by cases b <;> rfl

theorem boolBranch_eval [LemFuel] {M : MachineCtx} (ρ : EnvStack) (b : Bool) :
    evalPexpr M.tagDefs M.extern M.file ρ (boolBranch b) = some (boolValue b) := by
  rw [boolBranch, evalPexpr_if,
    if_pos (show (isPePure (Pexpr [] () (PEval Vtrue)) &&
      isPePure (Pexpr [] () (PEval Vfalse))) = true from rfl),
    evalPexpr_not, evalPexpr_op, ointPe, ointPe, evalPexpr_val, evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases b with
  | false =>
    rw [show evalBinop OpEq (oint (bit (!false))) (oint 1) = some Vtrue from rfl]
    simp only [Option.bind_some]
    rw [evalPexpr_val]
    rfl
  | true =>
    rw [show evalBinop OpEq (oint (bit (!true))) (oint 1) = some Vfalse from rfl]
    simp only [Option.bind_some]
    rw [evalPexpr_val]
    rfl

theorem wpt_boolE [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} (ρ : EnvStack) (b : Bool)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym (tmp 34)) = some (lint (bit (!b)))) :
    Ψ (.pure (boolValue b)) ρ ⊢ wpt M p Ls Θ 4 Ψ boolE ρ := by
  iintro H
  unfold boolE
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl hv
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl (boolE_select b)
  unfold pureE
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (boolBranch_eval _ b)
  iexact H



abbrev frAdd (n m : Nat) (v1 v2 : Int) (f : Fmap sym value) :=
  envAdd (tmp n) (lint v1) (envAdd (tmp m) (lint v2) f)

theorem addBranch_eval [LemFuel] {M : MachineCtx} (ρ : EnvStack) (v1 v2 : Int)
    (h1 : -2147483648 ≤ v1) (h1' : v1 ≤ 2147483647)
    (h2 : -2147483648 ≤ v2) (h2' : v2 ≤ 2147483647)
    (hs : -2147483648 ≤ v1 + v2) (hs' : v1 + v2 ≤ 2147483647) :
    evalPexpr M.tagDefs M.extern M.file ρ (addBranch (ointPe v1) (ointPe v2)) =
      some (lint (v1 + v2)) := by
  unfold addBranch
  rw [evalPexpr_ctor1,
    evalPexpr_catch_add_int [Astd "§6.5.6#5"]
      (evalPexpr_conv_int_int [Astd "§6.5.6#4"] (by rw [ointPe, evalPexpr_val]) h1 h1')
      (evalPexpr_conv_int_int [Astd "§6.5.6#4"] (by rw [ointPe, evalPexpr_val]) h2 h2') hs hs']
  rfl

/-- The actual addition tail evaluates annotated arithmetic after binding
its loaded operands. Both operands and the sum satisfy the ABI ranges. -/
theorem wpt_addE [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (l : CerbLocation.Loc) (n m a b : Nat) (v1 v2 : Int) (hnm : m ≠ n)
    (h1 : -2147483648 ≤ v1) (h1' : v1 ≤ 2147483647)
    (h2 : -2147483648 ≤ v2) (h2' : v2 ≤ 2147483647)
    (hs : -2147483648 ≤ v1 + v2) (hs' : v1 + v2 ≤ 2147483647)
    (hsel : select_case subst_sym_pexpr (Vtuple [lint v1, lint v2]) (addPats l a b) =
      some (addBranch (ointPe v1) (ointPe v2)))
    (e1 e2 : CoreExpr) (f : Fmap sym value) (rest : EnvStack) (k : Nat) :
    wpt M p Ls Θ k (fun w ρ' => iprop(∃ (f' : Fmap sym value) (ds : List dyn_annotation),
      ⌜w = .annot ds (Vtuple [lint v1, lint v2]) ∧ ρ' = f' :: rest ∧ SymFrame f'⌝ ∗
      Ψ (.annot ds (lint (v1 + v2))) (frAdd n m v1 v2 f' :: rest)))
      (Expr [] (Eunseq [e1, e2])) (f :: rest) ⊢
    wpt M p Ls Θ (k + 3) Ψ (addE l n m a b e1 e2) (f :: rest) := by
  iintro H
  unfold addE
  rw [show intTuplePat n m = tuplePat [] [([], some (tmp n), intBty),
    ([], some (tmp m), intBty)] from rfl]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ k 3
  iapply wpt_mono ?_ k _ (f :: rest) $$ H
  intro w ρ'
  iintro ⟨%f', %ds, %hw, HΨ⟩
  obtain ⟨rfl, rfl, hf'⟩ := hw
  iexists [lint v1, lint v2], ds
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  iapply wpt_annot (k := 2)
  unfold pureE
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl ?_
  · rw [evalPexpr_case, if_pos (show isPePureAlts (addPats l a b) = true from rfl),
      intTuple_eval n m _ _ _
        (psym_eval hex (by emitted_frame) rest
          (by rw [envAdd_lookup (hf'.add _ _), if_pos (symOrd_self _)]))
        (psym_eval hex (by emitted_frame) rest
          (by rw [envAdd_lookup (hf'.add _ _), if_neg (tmp_ne hnm),
            envAdd_lookup hf', if_pos (symOrd_self _)]))]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [hsel]
    simp only [Option.bind_some]
    rw [if_pos (show peDepth (reannot0 (addBranch (ointPe v1) (ointPe v2))) ≤
      peDepthAlts (addPats l a b) from Nat.le_refl _), evalPexpr_reannot0]
    exact addBranch_eval _ v1 v2 h1 h1' h2 h2' hs hs'
  simp only [SpikeVal.merge]
  iexact HΨ

abbrev frAddSI (pi ps : CerbMem.PointerValue) (i s : Int) (f : Fmap sym value) :=
  frAdd 73 74 s i
    (envAdd (tmp 78) (Vobject (OVpointer ps)) (envAdd (tmp 79) (Vobject (OVpointer pi)) f))

/-- The actual two-load RHS `s + i`. The driver reads `i` first and
    retains both read footprints; no sequencing replacement is used. -/
theorem wpt_addSI [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (i s : Int) (hi : -2147483648 ≤ i) (hi' : i ≤ 2147483647)
    (hs : -2147483648 ≤ s) (hs' : s ≤ 2147483647)
    (hsum : -2147483648 ≤ s + i) (hsum' : s + i ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : SourceFrame pi ps f)
    (hloadI : loadedVal M.tagDefs pi iTy bi = lint i)
    (htrapI : cellLoadTrap M.tagDefs ⟨addrOf pi, iTy, bi⟩ = false)
    (hloadS : loadedVal M.tagDefs ps sTy bs = lint s)
    (htrapS : cellLoadTrap M.tagDefs ⟨addrOf ps, sTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) sTy bs ∗
      (pointsToCell M.tagDefs pi (.own 1) iTy bi -∗
        pointsToCell M.tagDefs ps (.own 1) sTy bs -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pi iTy),
          DA_pos [] (loadFootprint M.tagDefs ps sTy)] (lint (s + i)))
          (frAddSI pi ps i s f :: rest))) ⊢
      wpt M p Ls Θ 18 Ψ addSI (f :: rest) := by
  have hframe := hf.1
  iintro ⟨Hi, Hs, HΨ⟩
  unfold addSI
  iapply wpt_addE hex _ _ _ _ _ s i (by decide +kernel) hs hs' hi hi' hsum hsum' rfl _ _ f rest 15
  rw [show ([load sTy sSym 78 69 70, load iTy iSym 79 73 74] : List CoreExpr) =
    [load sTy sSym 78 69 70] ++ load iTy iSym 79 73 74 :: [] from rfl]
  iapply wpt_unseq_focus [] [_] _ [] (f :: rest) rfl rfl 6 9
  iapply wpt_load_exact hex iTy iSym 79 73 74 f rest hframe pi bi
    (lint i) hf.2.1 hloadI htrapI
  isplitl [Hi]
  · iexact Hi
  iintro Hi %wa %hwa
  obtain ⟨a1, a2, b1, rfl⟩ : ∃ a1 a2 b1,
      wa = .annot a1 a2 b1 [DA_pos [] (loadFootprint M.tagDefs pi iTy)] (lint i) := by
    cases wa with
    | pure _ _ _ => cases hwa
    | annot _ _ _ _ _ => cases hwa; exact ⟨_, _, _, rfl⟩
  rw [show ([load sTy sSym 78 69 70] ++ ofValA (.annot a1 a2 b1
      [DA_pos [] (loadFootprint M.tagDefs pi iTy)] (lint i)) :: [] : List CoreExpr) =
    [] ++ load sTy sSym 78 69 70 :: [ofValA (.annot a1 a2 b1
      [DA_pos [] (loadFootprint M.tagDefs pi iTy)] (lint i))] from rfl]
  iapply wpt_unseq_focus [] [] _ [_] _
    (by rw [valsOnly_cons, isValE_ofValA, valsOnly_nil])
    (by simp only [List.nil_append, ccallFreeList, ccallFree_ofValA]) 6 3
  iapply wpt_load_exact hex sTy sSym 78 69 70
    (envAdd (tmp 79) (Vobject (OVpointer pi)) f) rest (hframe.add _ _) ps bs (lint s)
    (SourceFrame.add 79 _ (by decide +kernel) hf).2.2 hloadS htrapS
  isplitl [Hs]
  · iexact Hs
  iintro Hs %wb %hwb
  obtain ⟨c1, c2, d1, rfl⟩ : ∃ c1 c2 d1,
      wb = .annot c1 c2 d1 [DA_pos [] (loadFootprint M.tagDefs ps sTy)] (lint s) := by
    cases wb with
    | pure _ _ _ => cases hwb
    | annot _ _ _ _ _ => cases hwb; exact ⟨_, _, _, rfl⟩
  rw [show ([] ++ ofValA (.annot c1 c2 d1 [DA_pos [] (loadFootprint M.tagDefs ps sTy)] (lint s)) ::
      [ofValA (.annot a1 a2 b1 [DA_pos [] (loadFootprint M.tagDefs pi iTy)] (lint i))] : List CoreExpr) =
    [SpikeValA.annot c1 c2 d1 [DA_pos [] (loadFootprint M.tagDefs ps sTy)] (lint s),
      .annot a1 a2 b1 [DA_pos [] (loadFootprint M.tagDefs pi iTy)] (lint i)].map ofValA from rfl]
  iapply wpt_unseq_vals [] _ _ (Nat.le_refl 3)
    (fps := [DA_pos [] (loadFootprint M.tagDefs pi iTy), DA_pos [] (loadFootprint M.tagDefs ps sTy)])
    (cvals := [lint s, lint i])
    (by simp only [collectUnseq, do_race_nil_right, do_race_loadFootprint,
      combine_dyn_annotations, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append])
  iexists (envAdd (tmp 78) (Vobject (OVpointer ps)) (envAdd (tmp 79) (Vobject (OVpointer pi)) f)), _
  isplit
  · ipureintro; exact ⟨rfl, rfl, by emitted_frame⟩
  iapply HΨ $$ Hi Hs

abbrev frAddI1 (pi : CerbMem.PointerValue) (i : Int) (f : Fmap sym value) :=
  frAdd 82 83 i 1 (envAdd (tmp 87) (Vobject (OVpointer pi)) f)

/-- The emitted `i + 1`, with one read and a pure right operand. -/
theorem wpt_addI1 [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (i : Int) (hi : -2147483648 ≤ i) (hi' : i + 1 ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pi : CerbMem.PointerValue) (bi : List CerbMem.AbsByte)
    (hl : fmapLookupBy symCmpK iSym f = some (Vobject (OVpointer pi)))
    (hload : loadedVal M.tagDefs pi iTy bi = lint i)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pi, iTy, bi⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy bi ∗
      (pointsToCell M.tagDefs pi (.own 1) iTy bi -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pi iTy)] (lint (i + 1)))
          (frAddI1 pi i f :: rest))) ⊢
      wpt M p Ls Θ 14 Ψ addI1 (f :: rest) := by
  iintro ⟨Hi, HΨ⟩
  unfold addI1
  iapply wpt_addE hex _ _ _ _ _ i 1 (by decide +kernel) hi (by omega)
    (by decide +kernel) (by decide +kernel) (by omega) hi' rfl _ _ f rest 11
  iapply wpt_mono_k (show 6 + 3 ≤ 11 by decide)
  unfold literal
  iapply wpt_unseq_value_right
  iapply wpt_load_exact hex iTy iSym 87 80 81 f rest hf pi bi
    (lint i) hl hload htrap
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists (envAdd (tmp 87) (Vobject (OVpointer pi)) f), _
  isplit
  · ipureintro; exact ⟨rfl, rfl, hf.add _ _⟩
  iapply HΨ $$ Hi



abbrev assignFrame (n m : Nat) (v : Int) (pv : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (tmp n) (Vobject (OVpointer pv)) (envAdd (tmp m) (lint v) f)
abbrev ptrAssign (s : sym) : generic_pexpr Unit sym :=
  Pexpr [Astd "§6.5.16#3, sentence 1"] () (PEsym s)
abbrev convAssign (ta : List annot) (s : sym) : generic_pexpr Unit sym :=
  convLoaded [Astd "§6.5.16.1#2, conversion"] (sintTyAnn ta) s
/-- Fresh symbols generated above the source-variable numbers preserve
    the two source-pointer bindings, regardless of their descriptions. -/
theorem SourceFrame.fresh {pi ps : CerbMem.PointerValue} {f : Fmap sym value}
    (k : Nat) (v : value) (hk : 22 < k) (h : SourceFrame pi ps f) :
    SourceFrame pi ps (envAdd (fresh_given_int k) v f) := by
  have hi : symOrd iSym (fresh_given_int k) ≠ .eq := symOrd_ne_eq_of_num_ne (by omega)
  have hs : symOrd sSym (fresh_given_int k) ≠ .eq := symOrd_ne_eq_of_num_ne (by omega)
  exact ⟨h.1.add _ _, by rw [envAdd_lookup h.1, if_neg hi]; exact h.2.1,
    by rw [envAdd_lookup h.1, if_neg hs]; exact h.2.2⟩

/-- An emitted integer assignment with an annotated, effectful RHS.
    Evaluate its pointer operand in the RHS's resulting frame, bind the
    tuple, perform the negative store, and discard the statement value. -/
theorem wpt_assign [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (ta : List annot) (x : sym) (start n m : Nat) (v : Int) (hnm : m ≠ n)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (rhs : CoreExpr) (hnf : negFree rhs = true)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (k : Nat)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte) :
    wpt M p Ls Θ k (fun w ρ' => iprop(∃ (f' : Fmap sym value) (ds : List dyn_annotation),
      ⌜w = .annot ds (lint v) ∧ ρ' = f' :: rest ∧ SymFrame f' ∧
        fmapLookupBy symCmpK x f' = some (Vobject (OVpointer pv))⌝ ∗
      pointsToCell M.tagDefs pv (.own 1) (sintTyAnn ta) bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pv (.own 1) (sintTyAnn ta) (emittedIntBytes M.tagDefs v) -∗
        Ψ (.pure Vunit) (envAdd s (lint v) (assignFrame n m v pv f') :: rest)))) rhs (f :: rest) ⊢
      wpt M p Ls Θ (k + 22) Ψ (assign (sintTyAnn ta) x start n m rhs) (f :: rest) := by
  iintro H
  unfold assign
  rw [show k + 22 = (k + 21) + 1 by omega]
  iapply wpt_seq _ _ _ _ _ _ _ (k + 21) 1
  unfold CorpusE0.bnd
  rw [show (Pattern [] (CaseCtor Ctuple
    [Pattern [] (CaseBase (some (tmp n), ptrBty)), Pattern [] (CaseBase (some (tmp m), intBty))]) : pattern) =
    tuplePat [] [([], some (tmp n), ptrBty), ([], some (tmp m), intBty)] from rfl,
    show k + 21 = (k + 5) + 16 by omega]
  iapply wpt_bound_wseq_tuple _ _ _ _ _ _ _ _ (k + 5) 16
    (by simpa only [negFree, negFreeList, Bool.true_and, Bool.and_true] using hnf)
  iapply wpt_unseq_pure_left _ _ (psym x) rhs (f :: rest) k rfl
  iapply wpt_mono ?_ k rhs (f :: rest) $$ H
  intro w ρ'
  iintro ⟨%f', %ds, %hw, Hpt, HΨ⟩
  obtain ⟨rfl, rfl, hf', hl⟩ := hw
  iexists (Vobject (OVpointer pv))
  isplit
  · ipureintro; exact psym_eval hex (by emitted_frame) rest hl
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [Vobject (OVpointer pv), lint v], ds
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  have hframe : SymFrame (assignFrame n m v pv f') := (hf'.add _ _).add _ _
  have hlp : fmapLookupBy symCmpK (tmp n) (assignFrame n m v pv f') = some (Vobject (OVpointer pv)) := by
    rw [envAdd_lookup (hf'.add _ _), if_pos (symOrd_self _)]
  have hlv : fmapLookupBy symCmpK (tmp m) (assignFrame n m v pv f') = some (lint v) := by
    rw [envAdd_lookup (hf'.add _ _), if_neg (tmp_ne hnm), envAdd_lookup hf', if_pos (symOrd_self _)]
  have hp : evalPexpr M.tagDefs M.extern M.file (assignFrame n m v pv f' :: rest)
      (ptrAssign (tmp n)) = some (Vobject (OVpointer pv)) :=
    symbol_eval (M := M) hex hframe rest [Astd "§6.5.16#3, sentence 1"] hlp
  have hv : evalPexpr M.tagDefs M.extern M.file (assignFrame n m v pv f' :: rest)
      (convAssign ta (tmp m)) = some (lint v) :=
    convLoaded_eval hstd (psym_eval (M := M) hex hframe rest hlv) hv1 hv2
  rw [show (Expr [] (Eannot ds (Expr [] (Ewseq wc
      (Expr [Astd "§6.5.16.1#2, store"] (Eaction (Paction polarity.Neg0
        (Action (locP start (start + 9) (start + 2)) empty_annotation
          (Store0 false (tyPe (sintTyAnn ta)) (ptrAssign (tmp n)) (convAssign ta (tmp m)) NA)))))
      (pureE (convAssign ta (tmp m)))))) : CoreExpr) =
    negAssignBody [] [] [Astd "§6.5.16.1#2, store"] [] [] ds BTy_unit
      (locP start (start + 9) (start + 2)) empty_annotation (sintTyAnn ta)
      (ptrAssign (tmp n)) (convAssign ta (tmp m)) (convAssign ta (tmp m)) NA from rfl]
  iapply wpt_intAssign hex [Astd "§6.5#2"] [] [] [Astd "§6.5.16.1#2, store"] [] [] ds BTy_unit
    (locP start (start + 9) (start + 2)) empty_annotation ta
    (ptrAssign (tmp n)) (convAssign ta (tmp m)) (convAssign ta (tmp m)) NA
    (assignFrame n m v pv f') rest hframe pv bs v (lint v) hv1 hv2 rfl hp hv rfl hv
  isplitl [Hpt]
  · iexact Hpt
  iintro %s %hs Hpt
  unfold unitE pureE
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply HΨ $$ %s %hs Hpt


/-- The emitted `s = s + i`, preserving i's cell and both source pointers. -/
theorem wpt_assignS [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hsup : 22 < M.runState.sym_supply)
    (i s : Int) (hi : -2147483648 ≤ i) (hi' : i ≤ 2147483647)
    (hs : -2147483648 ≤ s) (hs' : s ≤ 2147483647)
    (hsum : -2147483648 ≤ s + i) (hsum' : s + i ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : SourceFrame pi ps f)
    (hloadI : loadedVal M.tagDefs pi iTy bi = lint i)
    (htrapI : cellLoadTrap M.tagDefs ⟨addrOf pi, iTy, bi⟩ = false)
    (hloadS : loadedVal M.tagDefs ps sTy bs = lint s)
    (htrapS : cellLoadTrap M.tagDefs ⟨addrOf ps, sTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) sTy bs ∗
      (∀ f', ⌜SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) iTy bi -∗
        pointsToCell M.tagDefs ps (.own 1) sTy (emittedIntBytes M.tagDefs (s + i)) -∗
        Ψ (.pure Vunit) (f' :: rest))) ⊢
      wpt M p Ls Θ 40 Ψ (assign sTy sSym 65 72 80 addSI) (f :: rest) := by
  iintro ⟨Hi, Hs, HΨ⟩
  iapply wpt_assign hstd hex [Aloc (loc 29 32)] sSym 65 72 80 (s + i) (by decide +kernel) hsum hsum'
    addSI rfl f rest 18 ps bs
  iapply wpt_addSI hex i s hi hi' hs hs' hsum hsum' f rest pi ps bi bs hf hloadI htrapI hloadS htrapS
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro Hi Hs
  have hfa : SourceFrame pi ps (frAddSI pi ps i s f) := by
    unfold frAddSI frAdd
    t4_source
  iexists (frAddSI pi ps i s f), _
  isplit
  · ipureintro; exact ⟨rfl, rfl, hfa.1, hfa.2.2⟩
  isplitl [Hs]
  · iexact Hs
  iintro %z %hz Hs
  obtain ⟨k, rfl, hk⟩ := hz
  have hfinal : SourceFrame pi ps (envAdd (fresh_given_int k) (lint (s + i))
      (assignFrame 72 80 (s + i) ps (frAddSI pi ps i s f))) := by
    apply SourceFrame.fresh k _ (by omega)
    unfold assignFrame
    t4_source
  iapply HΨ $$ %_ %hfinal Hi Hs

/-- The emitted `i = i + 1`, preserving s's cell and both source pointers. -/
theorem wpt_assignI [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hsup : 22 < M.runState.sym_supply)
    (i : Int) (hi : -2147483648 ≤ i) (hi' : i + 1 ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : SourceFrame pi ps f)
    (hloadI : loadedVal M.tagDefs pi iTy bi = lint i)
    (htrapI : cellLoadTrap M.tagDefs ⟨addrOf pi, iTy, bi⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) sTy bs ∗
      (∀ f', ⌜SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) iTy (emittedIntBytes M.tagDefs (i + 1)) -∗
        pointsToCell M.tagDefs ps (.own 1) sTy bs -∗
        Ψ (.pure Vunit) (f' :: rest))) ⊢
      wpt M p Ls Θ 36 Ψ (assign iTy iSym 76 81 88 addI1) (f :: rest) := by
  iintro ⟨Hi, Hs, HΨ⟩
  iapply wpt_assign hstd hex [Aloc (loc 18 21)] iSym 76 81 88 (i + 1) (by decide +kernel) (by omega) hi'
    addI1 rfl f rest 14 pi bi
  iapply wpt_addI1 hex i hi hi' f rest hf.1 pi bi hf.2.1 hloadI htrapI
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  have hfa : SourceFrame pi ps (frAddI1 pi i f) := by
    unfold frAddI1 frAdd
    t4_source
  iexists (frAddI1 pi i f), _
  isplit
  · ipureintro; exact ⟨rfl, rfl, hfa.1, hfa.2.1⟩
  isplitl [Hi]
  · iexact Hi
  iintro %z %hz Hi
  obtain ⟨k, rfl, hk⟩ := hz
  have hfinal : SourceFrame pi ps (envAdd (fresh_given_int k) (lint (i + 1))
      (assignFrame 81 88 (i + 1) pi (frAddI1 pi i f))) := by
    apply SourceFrame.fresh k _ (by omega)
    unfold assignFrame
    t4_source
  iapply HΨ $$ %_ %hfinal Hi Hs

/-- Both pointer parameters are rebound by each loop save and run. -/
abbrev frPtrs (pi ps : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd sSym (Vobject (OVpointer ps)) (envAdd iSym (Vobject (OVpointer pi)) f)

theorem SourceFrame.params (pi ps : CerbMem.PointerValue) (f : Fmap sym value) (hf : SymFrame f) :
    SourceFrame pi ps (frPtrs pi ps f) := by
  refine ⟨(hf.add _ _).add _ _, ?_, ?_⟩
  · rw [envAdd_lookup (hf.add _ _), if_neg (by decide +kernel), envAdd_lookup hf,
      if_pos (symOrd_self _)]
  · rw [envAdd_lookup (hf.add _ _), if_pos (symOrd_self _)]

theorem ptrParams_bindArgs (pi ps : CerbMem.PointerValue)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs ptrParams [Vobject (OVpointer pi), Vobject (OVpointer ps)] (f :: rest) =
      frPtrs pi ps f :: rest := by
  change update_env (mk_sym_pat sSym ptrBty) (Vobject (OVpointer ps))
    (update_env (mk_sym_pat iSym ptrBty) (Vobject (OVpointer pi)) (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons, update_env_aux_sym]

theorem ptrInits_bindSaveParams (pi ps : CerbMem.PointerValue)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams ptrInits [Vobject (OVpointer pi), Vobject (OVpointer ps)] (f :: rest) =
      frPtrs pi ps f :: rest := by
  change update_env (mk_sym_pat sSym ptrBty) (Vobject (OVpointer ps))
    (update_env (mk_sym_pat iSym ptrBty) (Vobject (OVpointer pi)) (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons, update_env_aux_sym]

theorem t4PtrArgs_eval [LemFuel] {M : MachineCtx} (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (pi ps : CerbMem.PointerValue) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : SourceFrame pi ps f) :
    evalPexprs M.tagDefs M.extern M.file (f :: rest) [psym iSym, psym sSym] =
      some [Vobject (OVpointer pi), Vobject (OVpointer ps)] := by
  rw [evalPexprs_cons, psym_eval hex hf.1 rest hf.2.1,
    evalPexprs_cons, psym_eval hex hf.1 rest hf.2.2, evalPexprs_nil]
  rfl

/-- Entry at any of t4's pointer-parameter saves, retaining the actual
    rebinding and the two-step initializer cost. -/
theorem wpt_saveEntry [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (la : label_annot) (l : sym) (body : CoreExpr) (k : Nat)
    (pi ps : CerbMem.PointerValue) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : SourceFrame pi ps f) :
    wpt M p Ls Θ k Ψ body (frPtrs pi ps f :: rest) ⊢
      wpt M p Ls Θ (k + 2) Ψ (save la l body) (f :: rest) := by
  unfold save
  rw [show (2 : Nat) = saveEntryCost ptrInits from rfl]
  iintro H
  iapply wpt_save _ _ _ _ f rest (t4PtrArgs_eval hex pi ps f rest hf)
  rw [ptrInits_bindSaveParams]
  iexact H

/-- One whole emitted loop body, including both assignments, the continue
    save and the jump to the registered while continuation. The caller
    supplies its next label precondition at budget m; the body costs 82+m. -/
theorem wpt_body [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q) (hsup : 22 < M.runState.sym_supply)
    (i s : Int) (hi : -2147483648 ≤ i) (hi' : i + 1 ≤ 2147483647)
    (hs : -2147483648 ≤ s) (hs' : s ≤ 2147483647)
    (hsum : -2147483648 ≤ s + i) (hsum' : s + i ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : SourceFrame pi ps f)
    (hloadI : loadedVal M.tagDefs pi iTy bi = lint i)
    (htrapI : cellLoadTrap M.tagDefs ⟨addrOf pi, iTy, bi⟩ = false)
    (hloadS : loadedVal M.tagDefs ps sTy bs = lint s)
    (htrapS : cellLoadTrap M.tagDefs ⟨addrOf ps, sTy, bs⟩ = false) (m : Nat) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) sTy bs ∗
      (∀ f', ⌜SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) iTy (emittedIntBytes M.tagDefs (i + 1)) -∗
        pointsToCell M.tagDefs ps (.own 1) sTy (emittedIntBytes M.tagDefs (s + i)) -∗
        Ls whileSym m [Vobject (OVpointer pi), Vobject (OVpointer ps)] (f' :: rest))) ⊢
      wpt M p Ls Θ (82 + m) Ψ body (f :: rest) := by
  iintro ⟨Hi, Hs, Hnext⟩
  unfold body seqE wc
  rw [show 82 + m = 81 + (1 + m) by omega]
  iapply wpt_seq _ _ _ _ _ _ _ 81 (1 + m)
  iapply wpt_seq _ _ _ _ _ _ _ 77 4
  iapply wpt_seq _ _ _ _ _ _ _ 40 37
  iapply wpt_assignS hstd hex hsup i s hi (by omega) hs hs' hsum hsum'
    f rest pi ps bi bs hf hloadI htrapI hloadS htrapS
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f1 %hf1 Hi Hs
  iapply wpt_seq _ _ _ _ _ _ _ 36 1
  iapply wpt_assignI hstd hex hsup i hi hi' f1 rest pi ps bi _ hf1 hloadI htrapI
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f2 %hf2 Hi Hs
  unfold unitE pureE
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 1
  iapply wpt_saveEntry hex (.LAloop_continue 24) continueSym _ 1 pi ps f2 rest hf2
  rw [← ofValA_pure [Aloc (loc 40 88), Astmt] [] Vunit]
  iapply wpt_ofValA (.pure [Aloc (loc 40 88), Astmt] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  have hfinal := SourceFrame.params pi ps f2 hf2.1
  iapply wpt_run [] empty_annotation whileSym [psym iSym, psym sSym]
    (frPtrs pi ps f2) rest m (by rw [hQ]; exact Q_while)
    (t4PtrArgs_eval hex pi ps _ rest hfinal) (Nat.le_refl (1 + m))
  iapply Hnext $$ %_ %hfinal Hi Hs


/-- The loop's mathematical sum, with the same recurrence as its body. -/
def sum : Nat → Nat
  | 0 => 0
  | n + 1 => sum n + n

theorem sum_succ (n : Nat) : (sum (n + 1) : Int) = (sum n : Int) + (n : Int) :=
  Int.natCast_add _ _

theorem index_cases {n : Nat} (hn : n ≤ 5) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega

theorem sum_le {n : Nat} (hn : n ≤ 5) : sum n ≤ 10 := by
  rcases index_cases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- The actual C conjunction agrees with n<5 on the invariant. -/
theorem guard {n : Nat} (hn : n ≤ 5) :
    (decide ((n : Int) < 5) && decide ((sum n : Int) < 7)) = decide (n < 5) := by
  rcases index_cases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Byte readouts for the six invariant states. Only finite scalar byte
    encodings are reduced here, never the program's execution. -/
theorem index_loaded (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    {n : Nat} (hn : n ≤ 5) :
    loadedVal tds pv iTy (emittedIntBytes tds n) = lint n := by
  rcases index_cases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem sum_loaded (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    {n : Nat} (hn : n ≤ 5) :
    loadedVal tds pv sTy (emittedIntBytes tds (sum n)) = lint (sum n) := by
  rcases index_cases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- 159 per back edge; 98 for the final condition, saves, cleanup and return. -/
def loopBudget (n : Nat) : Nat := 159 * (5 - n) + 98

theorem loopBudget_succ {n : Nat} (hn : n < 5) :
    loopBudget n = 159 + loopBudget (n + 1) := by unfold loopBudget; omega

/-- The loop arguments carry the owned cells and ordinary frame validity.
    The registered continuation rebinds both source pointers on entry. -/
def cells (GF : BundledGFunctors) [SpikeGS .hasLC GF]
    (tds : CerbTags.TagDefsMap) (n : Nat) (vs : List value) (ρ : EnvStack) : IProp GF :=
  iprop(∃ (pi ps : CerbMem.PointerValue) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [Vobject (OVpointer pi), Vobject (OVpointer ps)] ∧ ρ = f :: rest ∧ SymFrame f ∧ n ≤ 5⌝ ∗
    pointsToCell tds pi (.own 1) iTy (emittedIntBytes tds n) ∗
    pointsToCell tds ps (.own 1) sTy (emittedIntBytes tds (sum n)))

def LsT (GF : BundledGFunctors) [SpikeGS .hasLC GF]
    (tds : CerbTags.TagDefsMap) : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜l = retSym ∧ m = 2 ∧ vs = [lint 10] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝ ∨
    ∃ n, ⌜l = whileSym ∧ m = loopBudget n⌝ ∗ cells GF tds n vs ρ)

def resultPost : value → Mem → Prop := fun v _ => v = lint 10

theorem retParams_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs retParams [v] (f :: rest) = envAdd (tmp 91) v f :: rest := by
  show update_env (mk_sym_pat (tmp 91) intBty) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem kill_eq (l : CerbLocation.Loc) (ty : ctype) (s : sym) :
    kill l ty s = killOpRedex [] l empty_annotation (Static0 ty) (psym s) := rfl


/-- Read the final sum, dispose of both cells and jump to the real return
    continuation. The emitted dead cleanup remains after that jump. -/
theorem wpt_returnStmt [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy (emittedIntBytes M.tagDefs 5) ∗
      pointsToCell M.tagDefs ps (.own 1) sTy (emittedIntBytes M.tagDefs 10)) ⊢
      wpt M p (LsT GF M.tagDefs) emptyProcSpecT 16 Ψ returnStmt (f :: rest) := by
  have hframe := hf.1
  have hi := hf.2.1
  have hs := hf.2.2
  iintro ⟨Hi, Hs⟩
  simp only [returnStmt, letS, seqE, wc, CorpusE0.bnd, kill_eq]
  rw [show (Pattern [] (CaseBase (some (tmp 90), intBty)) : pattern) =
    symPat [] (tmp 90) intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 9
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  iapply wpt_load hex sTy sSym 89 96 97 f rest hframe ps (emittedIntBytes M.tagDefs 10) (lint 10) hs rfl rfl
  isplitl [Hs]
  · iexact Hs
  iintro %fp Hs
  simp only [SpikeVal.val]
  iexists (lint 10)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 3 6
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ _ _ _ _ rfl (pv := pi) (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 iTy) pi iTy (emittedIntBytes M.tagDefs 5) _ (Nat.le_refl 2) rfl
  isplitl [Hi]
  · iexact Hi
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 3
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ _ _ _ _ rfl (pv := ps) (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 sTy) ps sTy (emittedIntBytes M.tagDefs 10) _ (Nat.le_refl 2) rfl
  isplitl [Hs]
  · iexact Hs
  simp only [SpikeVal.mergeInto]
  iapply wpt_run [] empty_annotation retSym [convLoaded [] retTy (tmp 90)] _ _ 2
    (by rw [hQ]; exact Q_ret)
    (by rw [evalPexprs_cons, convLoaded_eval hstd (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
      (by decide) (by decide), evalPexprs_nil]; rfl) (Nat.le_refl 3)
  dsimp only [LsT]
  ileft
  ipureintro
  exact ⟨rfl, rfl, rfl, _, _, rfl, by emitted_frame⟩

/-- The loop test selects the actual body or final unit on the invariant,
    with 77 units before the selected branch. -/
theorem wpt_loopTest [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (n : Nat) (hn : n ≤ 5) (k : Nat)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy (emittedIntBytes M.tagDefs n) ∗
      pointsToCell M.tagDefs ps (.own 1) sTy (emittedIntBytes M.tagDefs (sum n)) ∗
      (∀ f', ⌜SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) iTy (emittedIntBytes M.tagDefs n) -∗
        pointsToCell M.tagDefs ps (.own 1) sTy (emittedIntBytes M.tagDefs (sum n)) -∗
        wpt M p Ls Θ k Ψ (if n < 5 then body else unitE) (f' :: rest))) ⊢
      wpt M p Ls Θ (77 + k) Ψ loopTest (f :: rest) := by
  have hsum := sum_le hn
  iintro ⟨Hi, Hs, Hnext⟩
  unfold loopTest letS
  rw [show (Pattern [] (CaseBase (some (tmp 34), intBty)) : pattern) =
    symPat [] (tmp 34) intBty from rfl, show 77 + k = 72 + (5 + k) by omega]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 72 (5 + k)
  iapply wpt_cond hstd hex n (sum n) (by omega) (by omega) (by omega) (by omega)
    f rest pi ps _ _ hf (index_loaded _ _ hn) rfl (sum_loaded _ _ hn) rfl
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f1 %hf1 Hi Hs
  have hframe1 := hf1.1
  rw [guard hn]
  iexists (lint (bit (!decide (n < 5))))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (tmp 33), BTy_boolean)) : pattern) =
    symPat [] (tmp 33) BTy_boolean from rfl, show 5 + k = 4 + (k + 1) by omega]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 4 (k + 1)
  iapply wpt_boolE _ (decide (n < 5)) (psym_eval hex (by emitted_frame) rest (by
    rw [envAdd_lookup hf1.1, if_pos (symOrd_self _)]))
  iexists (boolValue (decide (n < 5)))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_if _ _ _ _ _ (decide (n < 5))
  isplit
  · ipureintro
    exact psym_eval hex (by emitted_frame) rest (by rw [envAdd_lookup (hf1.1.add _ _), if_pos (symOrd_self _)])
  rw [show (bif decide (n < 5) then body else unitE) =
    (if n < 5 then body else unitE) by by_cases h : n < 5 <;> simp [h]]
  have hfinal : SourceFrame pi ps (envAdd (tmp 33) (boolValue (decide (n < 5)))
      (envAdd (tmp 34) (lint (bit (!decide (n < 5)))) f1)) := by t4_source
  iapply Hnext $$ %_ %hfinal Hi Hs

/-- A continuing iteration establishes the next while-label invariant,
    using the strictly smaller budget for n+1. -/
theorem wpt_loopStep [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q) (hsup : 22 < M.runState.sym_supply)
    (n : Nat) (hlt : n < 5)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy (emittedIntBytes M.tagDefs n) ∗
      pointsToCell M.tagDefs ps (.own 1) sTy (emittedIntBytes M.tagDefs (sum n))) ⊢
      wpt M p (LsT GF M.tagDefs) emptyProcSpecT (loopBudget n) Ψ loopTest (f :: rest) := by
  have hn : n ≤ 5 := by omega
  have hsum := sum_le hn
  iintro ⟨Hi, Hs⟩
  rw [loopBudget_succ hlt, show 159 + loopBudget (n + 1) = 77 + (82 + loopBudget (n + 1)) by omega]
  iapply wpt_loopTest hstd hex n hn (82 + loopBudget (n + 1)) f rest pi ps hf
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f1 %hf1 Hi Hs
  rw [if_pos hlt]
  iapply wpt_body hstd hex hQ hsup n (sum n) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) f1 rest pi ps _ _ hf1 (index_loaded _ _ hn) rfl
    (sum_loaded _ _ hn) rfl (loopBudget (n + 1))
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f2 %hf2 Hi Hs
  dsimp only [LsT]
  iright
  iexists (n + 1)
  isplit
  · ipureintro; exact ⟨rfl, rfl⟩
  dsimp only [cells]
  iexists pi, ps, f2, rest
  isplit
  · ipureintro; exact ⟨rfl, rfl, hf2.1, by omega⟩
  rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by omega, sum_succ]
  isplitl [Hi]
  · iexact Hi
  iexact Hs


/-- The registered while continuation satisfies the invariant budget.
    A true test advances n and spends 159; the n=5 path costs 98. -/
theorem wpt_whileCont [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q) (hsup : 22 < M.runState.sym_supply)
    (n : Nat) (hn : n ≤ 5)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy (emittedIntBytes M.tagDefs n) ∗
      pointsToCell M.tagDefs ps (.own 1) sTy (emittedIntBytes M.tagDefs (sum n))) ⊢
      wpt M p (LsT GF M.tagDefs) emptyProcSpecT (loopBudget n) Ψ whileCont (f :: rest) := by
  iintro ⟨Hi, Hs⟩
  by_cases hlt : n < 5
  · unfold whileCont loopContext seqE wc
    rw [show loopBudget n = loopBudget n + 0 from rfl]
    iapply wpt_seq _ _ _ _ _ _ _ (loopBudget n) 0
    iapply wpt_seq _ _ _ _ _ _ _ (loopBudget n) 0
    iapply wpt_seq _ _ _ _ _ _ _ (loopBudget n) 0
    iapply wpt_loopStep hstd hex hQ hsup n hlt f rest pi ps hf
    isplitl [Hi]
    · iexact Hi
    iexact Hs
  · have hn5 : n = 5 := by omega
    subst n
    rw [show loopBudget 5 = 98 from rfl]
    unfold whileCont loopContext seqE wc
    iapply wpt_seq _ _ _ _ _ _ _ 98 0
    iapply wpt_seq _ _ _ _ _ _ _ 82 16
    iapply wpt_seq _ _ _ _ _ _ _ 78 4
    iapply wpt_loopTest hstd hex 5 (by decide +kernel) 1 f rest pi ps hf
    isplitl [Hi]
    · iexact Hi
    isplitl [Hs]
    · iexact Hs
    iintro %f1 %hf1 Hi Hs
    rw [if_neg (by decide +kernel), show (sum 5 : Int) = 10 from rfl]
    unfold unitE pureE
    rw [← ofValA_pure [] [] Vunit]
    iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
    simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
    unfold afterWhile seqE wc
    iapply wpt_seq _ _ _ _ _ _ _ 3 1
    iapply wpt_saveEntry hex (.LAloop_break 24) breakSym _ 1 pi ps f1 rest hf1
    rw [← ofValA_pure [Aloc (loc 40 88), Astmt] [] Vunit]
    iapply wpt_ofValA (.pure [Aloc (loc 40 88), Astmt] [] Vunit) _ (Nat.le_refl 1)
    simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
    unfold unitE pureE
    rw [← ofValA_pure [] [] Vunit]
    iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
    simp only [SpikeValA.erase_pure]
    iapply wpt_seq _ _ _ _ _ _ _ 16 0
    iapply wpt_returnStmt hstd hex hQ (frPtrs pi ps f1) rest pi ps (SourceFrame.params pi ps f1 hf1.1)
    isplitl [Hi]
    · iexact Hi
    iexact Hs

/-- The two reachable jump entries are while and return. The other
    registered continuations remain in the whole-term fragment proof;
    their saves execute on the normal path, but no run targets them. -/
theorem blockSpecsT_main [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q) (hsup : 22 < M.runState.sym_supply) :
    ⊢ blockSpecsT (GF := GF) M p (LsT GF M.tagDefs) emptyProcSpecT (readoutPost resultPost) := by
  refine blockSpecsT_intro fun l params cont vs f rest m hl => ?_
  dsimp only [LsT]
  iintro HL
  icases HL with (Hr | Hw)
  · icases Hr with %hpure
    obtain ⟨rfl, rfl, rfl, f', rest', hρ, hf⟩ := hpure
    obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
    rw [hQ, Q_ret] at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    rw [retParams_bindArgs]
    unfold retCont pureE
    iapply wpt_pure (psym (tmp 91)) _ (Nat.le_refl 2) rfl (psym_eval hex (by emitted_frame) rest (by emitted_lookup))
    iintro %σ' %ns %κs %nt -
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    rfl
  · icases Hw with ⟨%n, %hpure, Hcells⟩
    obtain ⟨rfl, rfl⟩ := hpure
    rw [hQ, Q_while] at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    dsimp only [cells]
    icases Hcells with ⟨%pi, %ps, %f', %rest', %hargs, Hi, Hs⟩
    obtain ⟨rfl, hρ, hf, hn⟩ := hargs
    obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
    rw [ptrParams_bindArgs]
    iapply wpt_whileCont hstd hex hQ hsup n hn (frPtrs pi ps f) rest pi ps
      (SourceFrame.params pi ps f hf)
    isplitl [Hi]
    · iexact Hi
    iexact Hs

/-- Entry executes the emitted while save before its first continuing
    iteration; the registered continuation handles subsequent iterations. -/
theorem wpt_whileEntry [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : HasIntLibrary M.file) (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = Q) (hsup : 22 < M.runState.sym_supply)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) iTy (emittedIntBytes M.tagDefs 0) ∗
      pointsToCell M.tagDefs ps (.own 1) sTy (emittedIntBytes M.tagDefs 0)) ⊢
      wpt M p (LsT GF M.tagDefs) emptyProcSpecT 895 Ψ (loopContext whileE) (f :: rest) := by
  iintro ⟨Hi, Hs⟩
  unfold loopContext seqE wc whileE
  iapply wpt_seq _ _ _ _ _ _ _ 895 0
  iapply wpt_seq _ _ _ _ _ _ _ 895 0
  iapply wpt_seq _ _ _ _ _ _ _ 895 0
  iapply wpt_saveEntry hex (.LAloop 24) whileSym _ 893 pi ps f rest hf
  rw [← show loopBudget 0 = 893 from rfl]
  iapply wpt_loopStep hstd hex hQ hsup 0 (by decide +kernel) (frPtrs pi ps f) rest pi ps
    (SourceFrame.params pi ps f hf.1)
  isplitl [Hi]
  · iexact Hi
  rw [show (sum 0 : Int) = 0 from rfl]
  iexact Hs


end CerberusHeapLang.CorpusA7.T4
