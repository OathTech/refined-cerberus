/-
The emitted t4_while execution proof, in progress. The controlling
expression and both addition RHSs have public total proofs, including
short-circuit evaluation, nested truth conversions and the two-load race
check. Four continuations are checked against the engine collector, with
fragment and potential obligations. The assignments, total loop derivation
and production result remain to be completed.
-/
import CerberusHeapLang.CorpusT5Exhibit

set_option autoImplicit false
namespace CerberusHeapLang
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (t4Load t4Reg t4iSym t4sSym t4RetSym t4ContinueSym t4BreakSym t4WhileSym
  t4LoopTest t4While t4AfterWhile t4Return t4Main t5a t5Unit t5Pure
  ptrTy psym seqE letS wc specInt t4Lt t4LtPats t4Truth t4TruthPats t5Tuple t5TuplePat)

variable {GF : BundledGFunctors}

theorem wpt_t4Load [SpikeGS .hasLC GF]
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
      wpt M p Ls Θ 6 Ψ (t4Load x tmp c1 c2) (f :: rest) :=
  wpt_emittedIntLoad hex (t4Reg c1 c2) x (t5a tmp) f rest hf pv bs v hl hload htrap

/-- The integer representation used by the emitted C truth conversions. -/
def t4Bit (b : Bool) : Int := if b then 1 else 0

theorem t4a_ne {m n : Nat} (h : m ≠ n) : symOrd (t5a m) (t5a n) ≠ .eq :=
  symOrd_ne_eq_of_num_ne h

theorem t4Lt_eval (v k : Int) : evalBinop OpLt (oint v) (oint k) =
    some (boolValue (decide (v < k))) := rfl

abbrev t4frLt (tmp n m : Nat) (pv : CerbMem.PointerValue) (v k : Int) (f : Fmap sym value) :=
  envAdd (t5a n) (lint v) (envAdd (t5a m) (lint k) (envAdd (t5a tmp) (Vobject (OVpointer pv)) f))

/-- A loaded integer comparison, with the load footprint retained for
    its surrounding full expression. The selection premise checks the
    emitted pattern's two binders independently of the integer values. -/
theorem wpt_t4Lt [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (x : sym) (tmp n m a b start : Nat) (v k : Int) (hnm : m ≠ n)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (hk1 : -2147483648 ≤ k) (hk2 : k ≤ 2147483647)
    (hsel : select_case subst_sym_expr (Vtuple [lint v, lint k]) (t4LtPats a b) =
      some (Expr [Astd "§6.5.8#6"] (Epure (t5CmpBranch OpLt v k))))
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hx : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv intTy bs = lint v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) intTy bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) intTy bs -∗
        Ψ (.annot [DA_pos [] fp] (lint (t4Bit (decide (v < k)))))
          (t4frLt tmp n m pv v k f :: rest))) ⊢
      wpt M p Ls Θ 16 Ψ (t4Lt x tmp n m a b start k) (f :: rest) := by
  unfold t4frLt t4Bit
  iintro ⟨Hpt, HΨ⟩
  unfold t4Lt
  rw [show t5TuplePat n m = tuplePat [] [([], some (t5a n), CorpusE0.lint),
    ([], some (t5a m), CorpusE0.lint)] from rfl]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ 11 5
  iapply wpt_unseq_pure_right _ _ _ (specInt k) _ 6 (lint k) rfl rfl (specInt_eval _ k)
  iapply wpt_t4Load hex x tmp start (start + 1) f rest hf pv bs (lint v) hx hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint v, lint k], [DA_pos [] fp]
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2]
  rw [show (5 : Nat) = 4 + 1 from rfl]
  iapply wpt_annot
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl (cval := Vtuple [lint v, lint k])
    (t5Tuple_eval n m _ _
      (t1sym_eval hex rest (by rw [envAdd_lookup (((hf.add _ _).add _ _)), if_pos (symOrd_self _)]))
      (t1sym_eval hex rest (by rw [envAdd_lookup (((hf.add _ _).add _ _)),
        if_neg (t4a_ne hnm), envAdd_lookup (hf.add _ _), if_pos (symOrd_self _)])))
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl hsel
  iapply wpt_pure (t5CmpBranch OpLt v k) _ (Nat.le_refl 2) rfl
    (t5CmpBranch_eval hstd _ OpLt v k (decide (v < k)) hv1 hv2 hk1 hk2 (t4Lt_eval v k))
  simp only [SpikeVal.merge]
  iapply HΨ $$ %fp Hpt

def t4TruthBranch (negate b : Bool) : generic_pexpr Unit sym :=
  let eq0 := Pexpr [] () (PEop OpEq
    (Pexpr [] () (PEcall (Sym convIntSym) [CorpusE0.intCty, ointPe (t4Bit b)]))
    (Pexpr [] () (PEcall (Sym convIntSym) [CorpusE0.intCty, ointPe 0])))
  Pexpr [] () (PEif (if negate then Pexpr [] () (PEnot eq0) else eq0) (specInt 1) (specInt 0))

theorem t4TruthBranch_eval {M : MachineCtx} (hstd : StdE3 M.file) (ρ : EnvStack)
    (negate b : Bool) :
    evalPexpr M.tagDefs M.extern M.file ρ (t4TruthBranch negate b) =
      some (lint (t4Bit (if negate then b else !b))) := by
  cases negate with
  | false =>
    change evalPexpr M.tagDefs M.extern M.file ρ (t5CmpBranch OpEq (t4Bit b) 0) = _
    exact t5CmpBranch_eval hstd ρ OpEq (t4Bit b) 0 (!b)
      (by cases b <;> decide) (by cases b <;> decide) (by decide) (by decide) (by cases b <;> rfl)
  | true =>
    unfold t4TruthBranch
    simp only [↓reduceIte]
    rw [evalPexpr_if, if_pos (show (isPePure (specInt 1) && isPePure (specInt 0)) = true from rfl),
      evalPexpr_not, evalPexpr_op,
      evalPexpr_convInt_call_int [] hstd (by rw [CorpusE0.intCty, evalPexpr_val]; rfl)
        (by rw [ointPe, evalPexpr_val]) (by cases b <;> decide) (by cases b <;> decide),
      evalPexpr_convInt_call_int [] hstd (by rw [CorpusE0.intCty, evalPexpr_val]; rfl)
        (by rw [ointPe, evalPexpr_val]) (by decide) (by decide)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases b <;> change _ = some (lint _)
    · rw [show evalBinop OpEq (oint (t4Bit false)) (oint 0) = some Vtrue from rfl]
      simp only [Option.bind_some]
      exact specInt_eval ρ 0
    · rw [show evalBinop OpEq (oint (t4Bit true)) (oint 0) = some Vfalse from rfl]
      simp only [Option.bind_some]
      exact specInt_eval ρ 1

/-- One nested truth conversion. The head may change the environment;
    its post supplies the resulting frame and footprint to the caller. -/
theorem wpt_t4Truth [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (loc : CerbLocation.Loc) (n m a b : Nat) (negate bit : Bool) (hnm : m ≠ n)
    (e : CoreExpr) (hc : ccallFree e = true)
    (hsel : select_case subst_sym_pexpr (Vtuple [lint (t4Bit bit), lint 0]) (t4TruthPats a b negate) =
      some (t4TruthBranch negate bit))
    (f : Fmap sym value) (rest : List (Fmap sym value)) (k : Nat) :
    wpt M p Ls Θ k (fun w ρ' => iprop(∃ (f' : Fmap sym value) (rest' : List (Fmap sym value))
        (ds : List dyn_annotation),
      ⌜w = .annot ds (lint (t4Bit bit)) ∧ ρ' = f' :: rest' ∧ SymFrame f'⌝ ∗
      Ψ (.annot ds (lint (t4Bit (if negate then bit else !bit))))
        (envAdd (t5a n) (lint (t4Bit bit)) (envAdd (t5a m) (lint 0) f') :: rest'))) e (f :: rest) ⊢
    wpt M p Ls Θ (k + 8) Ψ (t4Truth loc n m a b negate e) (f :: rest) := by
  iintro H
  unfold t4Truth
  rw [show t5TuplePat n m = tuplePat [] [([], some (t5a n), CorpusE0.lint),
    ([], some (t5a m), CorpusE0.lint)] from rfl]
  rw [show k + 8 = (2 + (k + 3)) + 3 by omega]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ (2 + (k + 3)) 3
  iapply wpt_unseq_pure_right _ _ _ (specInt 0) _ k (lint 0) hc rfl (specInt_eval _ 0)
  iapply wpt_mono ?_ k e (f :: rest) $$ H
  intro w ρ'
  iintro ⟨%f', %rest', %ds, %hw, HΨ⟩
  obtain ⟨rfl, rfl, hf'⟩ := hw
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [lint (t4Bit bit), lint 0], ds
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2]
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_annot
  unfold t5Pure
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl ?_
  · rw [evalPexpr_case, if_pos (show isPePureAlts (t4TruthPats a b negate) = true by cases negate <;> rfl),
      t5Tuple_eval n m _ _
        (t1sym_eval hex rest' (by rw [envAdd_lookup (hf'.add _ _), if_pos (symOrd_self _)]))
        (t1sym_eval hex rest' (by rw [envAdd_lookup (hf'.add _ _), if_neg (t4a_ne hnm),
          envAdd_lookup hf', if_pos (symOrd_self _)]))]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [hsel]
    rw [Option.bind_some, if_pos (by cases negate <;> exact Nat.le_of_ble_eq_true rfl)]
    change evalPexpr M.tagDefs M.extern M.file _ (t4TruthBranch negate bit) = _
    exact t4TruthBranch_eval hstd _ negate bit
  simp only [SpikeVal.merge]
  iexact HΨ

abbrev t4frTruth (n m : Nat) (bit : Bool) (f : Fmap sym value) :=
  envAdd (t5a n) (lint (t4Bit bit)) (envAdd (t5a m) (lint 0) f)

abbrev t4frLeft (pi : CerbMem.PointerValue) (v : Int) (f : Fmap sym value) :=
  t4frTruth 524 525 (!(decide (v < 5)))
    (t4frTruth 529 530 (decide (v < 5)) (t4frLt 534 535 536 pi v 5 f))

abbrev t4frRight (ps : CerbMem.PointerValue) (v : Int) (f : Fmap sym value) :=
  t4frTruth 543 544 (decide (v < 7)) (t4frLt 548 549 550 ps v 7 f)

local macro "t4_frame" : tactic => `(tactic| repeat first | assumption | apply SymFrame.add)
local macro "t4_lookup" : tactic => `(tactic|
  (repeat first
    | rw [envAdd_lookup (by t4_frame), if_pos (by decide +kernel)]
    | rw [envAdd_lookup (by t4_frame), if_neg (by decide +kernel)]) <;> assumption)

theorem wpt_t4Left [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (v : Int) (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pi : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hi : fmapLookupBy symCmpK t4iSym f = some (Vobject (OVpointer pi)))
    (hload : loadedVal M.tagDefs pi intTy bs = lint v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pi, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy bs ∗
      (∀ fp, pointsToCell M.tagDefs pi (.own 1) intTy bs -∗
        Ψ (.annot [DA_pos [] fp] (lint (t4Bit (decide (v < 5))))) (t4frLeft pi v f :: rest))) ⊢
      wpt M p Ls Θ 32 Ψ CorpusE0.t4Left (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold CorpusE0.t4Left
  iapply wpt_t4Truth hstd hex _ 524 525 526 527 false (!(decide (v < 5)))
    (by decide) _ rfl (by cases h : decide (v < 5) <;> rfl) f rest 24
  iapply wpt_t4Truth hstd hex _ 529 530 531 532 false (decide (v < 5))
    (by decide) _ rfl (by cases h : decide (v < 5) <;> rfl) f rest 16
  iapply wpt_t4Lt hstd hex t4iSym 534 535 536 537 538 46 v 5 (by decide)
    hv1 hv2 (by decide) (by decide) rfl f rest hf pi bs hi hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  iexists t4frLt 534 535 536 pi v 5 f, rest, [DA_pos [] fp]
  isplit
  · ipureintro; exact ⟨rfl, rfl, by t4_frame⟩
  iexists t4frTruth 529 530 (decide (v < 5)) (t4frLt 534 535 536 pi v 5 f), rest, [DA_pos [] fp]
  isplit
  · ipureintro; exact ⟨rfl, rfl, by t4_frame⟩
  simp only [Bool.not_not, Bool.false_eq_true, ↓reduceIte, t4frLeft, t4frTruth]
  iapply HΨ $$ %fp Hpt

theorem wpt_t4Right [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (v : Int) (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (ps : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (hs : fmapLookupBy symCmpK t4sSym f = some (Vobject (OVpointer ps)))
    (hload : loadedVal M.tagDefs ps intTy bs = lint v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf ps, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) ps (.own 1) intTy bs ∗
      (∀ fp, pointsToCell M.tagDefs ps (.own 1) intTy bs -∗
        Ψ (.annot [DA_pos [] fp] (lint (t4Bit (decide (v < 7))))) (t4frRight ps v f :: rest))) ⊢
      wpt M p Ls Θ 24 Ψ CorpusE0.t4Right (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold CorpusE0.t4Right
  iapply wpt_t4Truth hstd hex _ 543 544 545 546 true (decide (v < 7))
    (by decide) _ rfl (by cases h : decide (v < 7) <;> rfl) f rest 16
  iapply wpt_t4Lt hstd hex t4sSym 548 549 550 551 552 55 v 7 (by decide)
    hv1 hv2 (by decide) (by decide) rfl f rest hf ps bs hs hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  iexists t4frLt 548 549 550 ps v 7 f, rest, [DA_pos [] fp]
  isplit
  · ipureintro; exact ⟨rfl, rfl, by t4_frame⟩
  simp only [↓reduceIte, t4frRight, t4frTruth]
  iapply HΨ $$ %fp Hpt

/-- Only the source pointers survive as logical interface to the next
    statement; emitted temporary bindings may accumulate in the frame. -/
def t4SourceFrame (pi ps : CerbMem.PointerValue) (f : Fmap sym value) : Prop :=
  SymFrame f ∧ fmapLookupBy symCmpK t4iSym f = some (Vobject (OVpointer pi)) ∧
    fmapLookupBy symCmpK t4sSym f = some (Vobject (OVpointer ps))

theorem t4SourceFrame.add {pi ps : CerbMem.PointerValue} {f : Fmap sym value}
    (n : Nat) (v : value) (hn : 513 ≤ n) (h : t4SourceFrame pi ps f) :
    t4SourceFrame pi ps (envAdd (t5a n) v f) := by
  have hi : symOrd t4iSym (t5a n) ≠ .eq := symOrd_ne_eq_of_num_ne (by omega)
  have hs : symOrd t4sSym (t5a n) ≠ .eq := symOrd_ne_eq_of_num_ne (by omega)
  exact ⟨h.1.add _ _, by rw [envAdd_lookup h.1, if_neg hi]; exact h.2.1,
    by rw [envAdd_lookup h.1, if_neg hs]; exact h.2.2⟩

local macro "t4_source" : tactic => `(tactic|
  repeat first | assumption | apply t4SourceFrame.add _ _ (by decide +kernel))

theorem wpt_t4And [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (i s : Int) (hi1 : -2147483648 ≤ i) (hi2 : i ≤ 2147483647)
    (hs1 : -2147483648 ≤ s) (hs2 : s ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : t4SourceFrame pi ps f)
    (hli : loadedVal M.tagDefs pi intTy bi = lint i)
    (hti : cellLoadTrap M.tagDefs ⟨addrOf pi, intTy, bi⟩ = false)
    (hls : loadedVal M.tagDefs ps intTy bs = lint s)
    (hts : cellLoadTrap M.tagDefs ⟨addrOf ps, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) intTy bs ∗
      (∀ (f' : Fmap sym value) (ds : List dyn_annotation), ⌜t4SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) intTy bi -∗ pointsToCell M.tagDefs ps (.own 1) intTy bs -∗
        Ψ (.annot ds (lint (t4Bit (decide (i < 5) && decide (s < 7))))) (f' :: rest))) ⊢
      wpt M p Ls Θ 63 Ψ CorpusE0.t4And (f :: rest) := by
  have hframe : SymFrame f := hf.1
  iintro ⟨Hi, Hs, HΨ⟩
  unfold CorpusE0.t4And letS
  rw [show (Pattern [] (CaseBase (some (t5a 540), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 540) CorpusE0.lint from rfl]
  iapply wpt_seq_sym_annot _ _ _ _ _ _ _ _ 32 31
  iapply wpt_t4Left hstd hex i hi1 hi2 f rest hf.1 pi bi hf.2.1 hli hti
  isplitl [Hi]
  · iexact Hi
  iintro %fpi Hi
  iexists lint (t4Bit (decide (i < 5))), [DA_pos [] fpi]
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (31 : Nat) = 30 + 1 from rfl]
  iapply wpt_annot
  rw [show (30 : Nat) = 29 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl
    (t1sym_eval hex rest (by rw [envAdd_lookup (by t4_frame), if_pos (symOrd_self _)]))
  rw [show (29 : Nat) = 28 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl (by rw [CorpusE0.t4And_select]; rfl)
  unfold CorpusE0.t4AndSpecified
  have hfa : t4SourceFrame pi ps
      (envAdd (t5a 540) (lint (t4Bit (decide (i < 5)))) (t4frLeft pi i f)) := by t4_source
  by_cases hi5 : i < 5
  · have hb : decide (i < 5) = true := decide_eq_true hi5
    simp only [hb, Bool.true_and] at *
    rw [show (28 : Nat) = 27 + 1 from rfl]
    iapply wpt_if_false _ _ _ _ _ (by rw [evalPexpr_op, evalPexpr_val, evalPexpr_val]; rfl)
    unfold letS
    rw [show (Pattern [] (CaseBase (some (t5a 554), CorpusE0.lint)) : pattern) =
      symPat [] (t5a 554) CorpusE0.lint from rfl]
    iapply wpt_seq_sym_annot _ _ _ _ _ _ _ _ 24 3
    iapply wpt_t4Right hstd hex s hs1 hs2
      (envAdd (t5a 540) (lint (t4Bit true)) (t4frLeft pi i f)) rest hfa.1 ps bs hfa.2.2 hls hts
    isplitl [Hs]
    · iexact Hs
    iintro %fps Hs
    iexists lint (t4Bit (decide (s < 7))), [DA_pos [] fps]
    isplit
    · ipureintro; rfl
    rw [update_env_sym, show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_annot
    unfold t5Pure
    iapply wpt_pure _ _ (Nat.le_refl 2) rfl
      (t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by rw [envAdd_lookup (by t4_frame), if_pos (symOrd_self _)]))
        (by cases decide (s < 7) <;> decide) (by cases decide (s < 7) <;> decide))
    simp only [SpikeVal.merge]
    iapply HΨ $$ %_ %_ %(by t4_source) Hi Hs
  · have hb : decide (i < 5) = false := decide_eq_false hi5
    simp only [hb, Bool.false_and] at *
    rw [show (28 : Nat) = 27 + 1 from rfl]
    iapply wpt_if_true _ _ _ _ _ (by rw [evalPexpr_op, evalPexpr_val, evalPexpr_val]; rfl)
    iapply wpt_mono_k (show 4 ≤ 27 by decide)
    unfold letS
    rw [show (Pattern [] (CaseBase (some (t5a 542), CorpusE0.lint)) : pattern) =
      symPat [] (t5a 542) CorpusE0.lint from rfl]
    iapply wpt_seq_sym _ _ _ _ _ _ _ _ 2 2
    iapply wpt_pure (specInt 0) _ (Nat.le_refl 2) rfl (specInt_eval _ 0)
    iexists lint 0
    isplit
    · ipureintro; rfl
    rw [update_env_sym]
    unfold t5Pure
    iapply wpt_pure _ _ (Nat.le_refl 2) rfl
      (t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by rw [envAdd_lookup (by t4_frame), if_pos (symOrd_self _)]))
        (by decide) (by decide))
    simp only [SpikeVal.merge, t4Bit, Bool.false_eq_true, ↓reduceIte]
    iapply HΨ $$ %_ %_ %(by t4_source) Hi Hs

/-- The full controlling expression ends its annotation scope at bound.
    Its result is the emitted equality-to-zero test of the conjunction. -/
theorem wpt_t4Cond [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (i s : Int) (hi1 : -2147483648 ≤ i) (hi2 : i ≤ 2147483647)
    (hs1 : -2147483648 ≤ s) (hs2 : s ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : t4SourceFrame pi ps f)
    (hli : loadedVal M.tagDefs pi intTy bi = lint i)
    (hti : cellLoadTrap M.tagDefs ⟨addrOf pi, intTy, bi⟩ = false)
    (hls : loadedVal M.tagDefs ps intTy bs = lint s)
    (hts : cellLoadTrap M.tagDefs ⟨addrOf ps, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) intTy bs ∗
      (∀ (f' : Fmap sym value), ⌜t4SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) intTy bi -∗ pointsToCell M.tagDefs ps (.own 1) intTy bs -∗
        Ψ (.pure (lint (t4Bit (!(decide (i < 5) && decide (s < 7)))))) (f' :: rest))) ⊢
      wpt M p Ls Θ 72 Ψ CorpusE0.t4Cond (f :: rest) := by
  iintro ⟨Hi, Hs, HΨ⟩
  unfold CorpusE0.t4Cond CorpusE0.bnd
  rw [show (72 : Nat) = 71 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_t4Truth hstd hex _ 519 520 521 522 false (decide (i < 5) && decide (s < 7))
    (by decide) _ rfl (by cases decide (i < 5) && decide (s < 7) <;> rfl) f rest 63
  iapply wpt_t4And hstd hex i s hi1 hi2 hs1 hs2 f rest pi ps bi bs hf hli hti hls hts
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

def t4BoolBranch (b : Bool) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEnot
    (Pexpr [] () (PEop OpEq (ointPe (t4Bit (!b))) (ointPe 1)))))
    (Pexpr [] () (PEval Vtrue)) (Pexpr [] () (PEval Vfalse)))

theorem t4Bool_select (b : Bool) :
    select_case subst_sym_expr (lint (t4Bit (!b))) CorpusE0.t4BoolPats =
      some (t5Pure (t4BoolBranch b)) := by cases b <;> rfl

theorem t4BoolBranch_eval {M : MachineCtx} (ρ : EnvStack) (b : Bool) :
    evalPexpr M.tagDefs M.extern M.file ρ (t4BoolBranch b) = some (boolValue b) := by
  rw [t4BoolBranch, evalPexpr_if,
    if_pos (show (isPePure (Pexpr [] () (PEval Vtrue)) &&
      isPePure (Pexpr [] () (PEval Vfalse))) = true from rfl),
    evalPexpr_not, evalPexpr_op, ointPe, ointPe, evalPexpr_val, evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases b with
  | false =>
    rw [show evalBinop OpEq (oint (t4Bit (!false))) (oint 1) = some Vtrue from rfl]
    simp only [Option.bind_some]
    rw [evalPexpr_val]
    rfl
  | true =>
    rw [show evalBinop OpEq (oint (t4Bit (!true))) (oint 1) = some Vfalse from rfl]
    simp only [Option.bind_some]
    rw [evalPexpr_val]
    rfl

theorem wpt_t4Bool [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} (ρ : EnvStack) (b : Bool)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ (psym (t5a 517)) = some (lint (t4Bit (!b)))) :
    Ψ (.pure (boolValue b)) ρ ⊢ wpt M p Ls Θ 4 Ψ CorpusE0.t4Bool ρ := by
  iintro H
  unfold CorpusE0.t4Bool
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_case_eval _ _ _ _ rfl hv
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_case_value _ _ _ _ rfl (t4Bool_select b)
  unfold t5Pure
  iapply wpt_pure _ _ (Nat.le_refl 2) rfl (t4BoolBranch_eval _ b)
  iexact H

/-- The suffix outside the while save belongs to each label in its body. -/
def t4LoopContext (body : CoreExpr) : CoreExpr :=
  seqE (Expr [Aloc (t4Reg 39 87), Astmt] (Esseq wc body t4AfterWhile)) t4Return

def t4WhileCont : CoreExpr := t4LoopContext t4LoopTest
def t4ContinueCont : CoreExpr := t4LoopContext
  (seqE (seqE (Expr [Aloc (t4Reg 39 87), Astmt] (Epure (Pexpr [] () (PEval Vunit)))) t5Unit)
    (Expr [] (Erun empty_annotation t4WhileSym [psym t4iSym, psym t4sSym])))
def t4BreakCont : CoreExpr :=
  seqE (seqE (Expr [Aloc (t4Reg 39 87), Astmt] (Epure (Pexpr [] () (PEval Vunit)))) t5Unit) t4Return
def t4RetCont : CoreExpr := t5Pure (psym (t5a 574))
def t4PtrParams : List (sym × core_base_type) := [(t4iSym, ptrTy), (t4sSym, ptrTy)]
def t4RetParams : List (sym × core_base_type) := [(t5a 574, CorpusE0.lint)]

def t4Q : LabelMap := collect_saves t4Main

theorem t4Q_while : lookupLabel t4Q t4WhileSym = some (t4PtrParams, t4WhileCont) := rfl
theorem t4Q_continue : lookupLabel t4Q t4ContinueSym = some (t4PtrParams, t4ContinueCont) := rfl
theorem t4Q_break : lookupLabel t4Q t4BreakSym = some (t4PtrParams, t4BreakCont) := rfl
theorem t4Q_ret : lookupLabel t4Q t4RetSym = some (t4RetParams, t4RetCont) := rfl

theorem t4Q_eq : t4Q =
    fmapAddBy symCmpL t4BreakSym (t4PtrParams, t4BreakCont)
    (fmapAddBy symCmpL t4ContinueSym (t4PtrParams, t4ContinueCont)
    (fmapAddBy symCmpL t4WhileSym (t4PtrParams, t4WhileCont)
    (fmapAddBy symCmpL t4RetSym (t4RetParams, t4RetCont) fmapEmpty))) := rfl

theorem t4Q_lookup (l : sym) : lookupLabel t4Q l =
    if symOrd l t4BreakSym = .eq then some (t4PtrParams, t4BreakCont)
    else if symOrd l t4ContinueSym = .eq then some (t4PtrParams, t4ContinueCont)
    else if symOrd l t4WhileSym = .eq then some (t4PtrParams, t4WhileCont)
    else if symOrd l t4RetSym = .eq then some (t4RetParams, t4RetCont)
    else none := by
  rw [t4Q_eq]
  unfold lookupLabel
  rw [labelAdd_lookup (((symMap_empty.addLabel _ _).addLabel _ _).addLabel _ _),
    labelAdd_lookup ((symMap_empty.addLabel _ _).addLabel _ _),
    labelAdd_lookup (symMap_empty.addLabel _ _), labelAdd_lookup symMap_empty]
  rfl

theorem t4Q_cont {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t4Q l = some (params, cont)) :
    cont ∈ [t4ContinueCont, t4WhileCont, t4BreakCont, t4RetCont] := by
  rw [t4Q_lookup] at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · split at h
        · cases h; simp
        · cases h

theorem t4LoopContext_frag (body : CoreExpr) (hb : Frag body) : Frag (t4LoopContext body) :=
  .sseq (.sseq hb (.sseq (CorpusE0.t4Save_frag _ _ (.val_pure _)) (.val_pure _))) CorpusE0.t4Return_frag

theorem t4Q_frag {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t4Q l = some (params, cont)) : Frag cont := by
  have hc := t4Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · refine t4LoopContext_frag _ (.sseq (.sseq (.val_pure _) (.val_pure _)) (.run ?_ ?_))
    · intro pe hpe
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      rcases hpe with rfl | rfl <;> exact .sym _ _
    · intro pe hpe
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      rcases hpe with rfl | rfl <;> exact peDepth_sym_le _ _
  · exact t4LoopContext_frag _ (.sseq_sym CorpusE0.t4Cond_frag (.sseq_sym CorpusE0.t4Bool_frag
      (.if_ (.sym _ _) (peDepth_sym_le _ _) CorpusE0.t4Body_frag (.val_pure _))))
  · exact .sseq (.sseq (.val_pure _) (.val_pure _)) CorpusE0.t4Return_frag
  · exact Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _)

theorem t4Q_pot {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t4Q l = some (params, cont)) : pot cont ≤ lemDefaultFuel := by
  have hc := t4Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl

theorem collect_new_t4Main :
    collect_labeled_continuations_NEW (prodFileLib stdlibE3 [] t4Main) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym t4Q fmapEmpty := rfl

theorem t4Main_labeledAt (sup : Nat) :
    LabeledAt (prodRSLib stdlibE3 [] sup t4Main) mainSym t4Q := by
  unfold LabeledAt
  rw [prodRSLib_labeled, collect_new_t4Main, fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

theorem t4Main_pot : pot t4Main ≤ lemDefaultFuel := Nat.le_of_ble_eq_true rfl

abbrev t4frAdd (n m : Nat) (v1 v2 : Int) (f : Fmap sym value) :=
  envAdd (t5a n) (lint v1) (envAdd (t5a m) (lint v2) f)

/-- The emitted addition tail, independently of how its operands produce
    their tuple. Both operands and the sum must fit signed `int`. -/
theorem wpt_t4Add [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (loc : CerbLocation.Loc) (n m a b : Nat) (v1 v2 : Int) (hnm : m ≠ n)
    (h1 : -2147483648 ≤ v1) (h1' : v1 ≤ 2147483647)
    (h2 : -2147483648 ≤ v2) (h2' : v2 ≤ 2147483647)
    (hs : -2147483648 ≤ v1 + v2) (hs' : v1 + v2 ≤ 2147483647)
    (hsel : select_case subst_sym_pexpr (Vtuple [lint v1, lint v2])
      (cAddPats (t5a a) (t5a b) loc) = some (cAddBranch v1 v2))
    (e1 e2 : CoreExpr) (f : Fmap sym value) (rest : List (Fmap sym value)) (k : Nat) :
    wpt M p Ls Θ k (fun w ρ' => iprop(∃ (f' : Fmap sym value) (ds : List dyn_annotation),
      ⌜w = .annot ds (Vtuple [lint v1, lint v2]) ∧ ρ' = f' :: rest ∧ SymFrame f'⌝ ∗
      Ψ (.annot ds (lint (v1 + v2))) (t4frAdd n m v1 v2 f' :: rest)))
      (Expr [] (Eunseq [e1, e2])) (f :: rest) ⊢
    wpt M p Ls Θ (k + 3) Ψ (CorpusE0.t4Add loc n m a b e1 e2) (f :: rest) := by
  iintro H
  unfold CorpusE0.t4Add
  rw [show t5TuplePat n m = tuplePat [] [([], some (t5a n), CorpusE0.lint),
    ([], some (t5a m), CorpusE0.lint)] from rfl]
  iapply wpt_wseq_tuple_annot _ _ _ _ _ _ _ k 3
  iapply wpt_mono ?_ k _ (f :: rest) $$ H
  intro w ρ'
  iintro ⟨%f', %ds, %hw, HΨ⟩
  obtain ⟨rfl, rfl, hf'⟩ := hw
  iexists [lint v1, lint v2], ds
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2]
  iapply wpt_annot (k := 2)
  rw [show t5Pure (Pexpr [] () (PEcase (t5Tuple n m) (CorpusE0.t4AddPats loc a b))) =
    Expr [] (Epure (cAddPe (t5a n) (t5a m) (t5a a) (t5a b) loc)) from rfl]
  iapply wpt_c_add (t5a n) (t5a m) (t5a a) (t5a b) loc _ (Nat.le_refl 2)
    (t1sym_eval hex rest (by rw [envAdd_lookup (hf'.add _ _), if_pos (symOrd_self _)]))
    (t1sym_eval hex rest (by rw [envAdd_lookup (hf'.add _ _), if_neg (t4a_ne hnm),
      envAdd_lookup hf', if_pos (symOrd_self _)])) hsel h1 h1' h2 h2' hs hs'
  simp only [SpikeVal.merge]
  iexact HΨ

abbrev t4frAddSI (pi ps : CerbMem.PointerValue) (i s : Int) (f : Fmap sym value) :=
  t4frAdd 556 557 s i
    (envAdd (t5a 561) (Vobject (OVpointer ps)) (envAdd (t5a 562) (Vobject (OVpointer pi)) f))

/-- The actual two-load RHS `s + i`. The driver reads `i` first and
    retains both read footprints; no sequencing replacement is used. -/
theorem wpt_t4AddSI [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (i s : Int) (hi : -2147483648 ≤ i) (hi' : i ≤ 2147483647)
    (hs : -2147483648 ≤ s) (hs' : s ≤ 2147483647)
    (hsum : -2147483648 ≤ s + i) (hsum' : s + i ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : t4SourceFrame pi ps f)
    (hloadI : loadedVal M.tagDefs pi intTy bi = lint i)
    (htrapI : cellLoadTrap M.tagDefs ⟨addrOf pi, intTy, bi⟩ = false)
    (hloadS : loadedVal M.tagDefs ps intTy bs = lint s)
    (htrapS : cellLoadTrap M.tagDefs ⟨addrOf ps, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) intTy bs ∗
      (pointsToCell M.tagDefs pi (.own 1) intTy bi -∗
        pointsToCell M.tagDefs ps (.own 1) intTy bs -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pi intTy),
          DA_pos [] (loadFootprint M.tagDefs ps intTy)] (lint (s + i)))
          (t4frAddSI pi ps i s f :: rest))) ⊢
      wpt M p Ls Θ 18 Ψ CorpusE0.t4AddSI (f :: rest) := by
  have hframe := hf.1
  iintro ⟨Hi, Hs, HΨ⟩
  unfold CorpusE0.t4AddSI
  iapply wpt_t4Add hex _ _ _ _ _ s i (by decide +kernel) hs hs' hi hi' hsum hsum' rfl _ _ f rest 15
  rw [show ([t4Load t4sSym 561 68 69, t4Load t4iSym 562 72 73] : List CoreExpr) =
    [t4Load t4sSym 561 68 69] ++ t4Load t4iSym 562 72 73 :: [] from rfl]
  iapply wpt_unseq_focus [] [_] _ [] (f :: rest) rfl rfl 6 9
  rw [show t4Load t4iSym 562 72 73 =
    CorpusE0.emittedIntLoad (t4Reg 72 73) t4iSym (t5a 562) from rfl]
  iapply wpt_emittedIntLoad_footprint hex (t4Reg 72 73) t4iSym (t5a 562) f rest hframe pi bi
    (lint i) hf.2.1 hloadI htrapI
  isplitl [Hi]
  · iexact Hi
  iintro Hi %wa %hwa
  obtain ⟨a1, a2, b1, rfl⟩ : ∃ a1 a2 b1,
      wa = .annot a1 a2 b1 [DA_pos [] (loadFootprint M.tagDefs pi intTy)] (lint i) := by
    cases wa with
    | pure _ _ _ => cases hwa
    | annot _ _ _ _ _ => cases hwa; exact ⟨_, _, _, rfl⟩
  rw [show ([t4Load t4sSym 561 68 69] ++ ofValA (.annot a1 a2 b1
      [DA_pos [] (loadFootprint M.tagDefs pi intTy)] (lint i)) :: [] : List CoreExpr) =
    [] ++ t4Load t4sSym 561 68 69 :: [ofValA (.annot a1 a2 b1
      [DA_pos [] (loadFootprint M.tagDefs pi intTy)] (lint i))] from rfl]
  iapply wpt_unseq_focus [] [] _ [_] _
    (by rw [valsOnly_cons, isValE_ofValA, valsOnly_nil])
    (by simp only [List.nil_append, ccallFreeList, ccallFree_ofValA]) 6 3
  unfold t4Load
  iapply wpt_emittedIntLoad_footprint hex (t4Reg 68 69) t4sSym (t5a 561)
    (envAdd (t5a 562) (Vobject (OVpointer pi)) f) rest (hframe.add _ _) ps bs (lint s)
    (t4SourceFrame.add 562 _ (by decide +kernel) hf).2.2 hloadS htrapS
  isplitl [Hs]
  · iexact Hs
  iintro Hs %wb %hwb
  obtain ⟨c1, c2, d1, rfl⟩ : ∃ c1 c2 d1,
      wb = .annot c1 c2 d1 [DA_pos [] (loadFootprint M.tagDefs ps intTy)] (lint s) := by
    cases wb with
    | pure _ _ _ => cases hwb
    | annot _ _ _ _ _ => cases hwb; exact ⟨_, _, _, rfl⟩
  rw [show ([] ++ ofValA (.annot c1 c2 d1 [DA_pos [] (loadFootprint M.tagDefs ps intTy)] (lint s)) ::
      [ofValA (.annot a1 a2 b1 [DA_pos [] (loadFootprint M.tagDefs pi intTy)] (lint i))] : List CoreExpr) =
    [SpikeValA.annot c1 c2 d1 [DA_pos [] (loadFootprint M.tagDefs ps intTy)] (lint s),
      .annot a1 a2 b1 [DA_pos [] (loadFootprint M.tagDefs pi intTy)] (lint i)].map ofValA from rfl]
  iapply wpt_unseq_vals [] _ _ (Nat.le_refl 3)
    (fps := [DA_pos [] (loadFootprint M.tagDefs pi intTy), DA_pos [] (loadFootprint M.tagDefs ps intTy)])
    (cvals := [lint s, lint i])
    (by simp only [collectUnseq, do_race_nil_right, do_race_loadFootprint,
      combine_dyn_annotations, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append])
  iexists (envAdd (t5a 561) (Vobject (OVpointer ps)) (envAdd (t5a 562) (Vobject (OVpointer pi)) f)), _
  isplit
  · ipureintro; exact ⟨rfl, rfl, by t4_frame⟩
  iapply HΨ $$ Hi Hs

abbrev t4frAddI1 (pi : CerbMem.PointerValue) (i : Int) (f : Fmap sym value) :=
  t4frAdd 565 566 i 1 (envAdd (t5a 570) (Vobject (OVpointer pi)) f)

/-- The emitted `i + 1`, with one read and a pure right operand. -/
theorem wpt_t4AddI1 [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (i : Int) (hi : -2147483648 ≤ i) (hi' : i + 1 ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pi : CerbMem.PointerValue) (bi : List CerbMem.AbsByte)
    (hl : fmapLookupBy symCmpK t4iSym f = some (Vobject (OVpointer pi)))
    (hload : loadedVal M.tagDefs pi intTy bi = lint i)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pi, intTy, bi⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy bi ∗
      (pointsToCell M.tagDefs pi (.own 1) intTy bi -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pi intTy)] (lint (i + 1)))
          (t4frAddI1 pi i f :: rest))) ⊢
      wpt M p Ls Θ 14 Ψ CorpusE0.t4AddI1 (f :: rest) := by
  iintro ⟨Hi, HΨ⟩
  unfold CorpusE0.t4AddI1
  iapply wpt_t4Add hex _ _ _ _ _ i 1 (by decide +kernel) hi (by omega)
    (by decide +kernel) (by decide +kernel) (by omega) hi' rfl _ _ f rest 11
  iapply wpt_unseq_pure_right _ _ _ (specInt 1) _ 6 (lint 1) rfl rfl (specInt_eval _ 1)
  unfold t4Load
  iapply wpt_emittedIntLoad_footprint hex (t4Reg 79 80) t4iSym (t5a 570) f rest hf pi bi
    (lint i) hl hload htrap
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists (envAdd (t5a 570) (Vobject (OVpointer pi)) f), _
  isplit
  · ipureintro; exact ⟨rfl, rfl, hf.add _ _⟩
  iapply HΨ $$ Hi

end CerberusHeapLang
