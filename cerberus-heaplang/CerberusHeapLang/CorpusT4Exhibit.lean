/-
The emitted t4_while public total proof and shipped-driver result. The
invariant owns i = n and s = sum(0..n-1), with n <= 5 and a decreasing
label budget. The proof retains short-circuit evaluation, both assignments,
all four registered continuations and the emitted cleanup. The whole main
has budget 915 and returns Specified(10). The production theorem requires
initial symbol supply at least 600 and uses the checked three-function
std.core fragment; the full emitted-file connection remains KOI A7.
-/
import CerberusHeapLang.Examples.EmittedInt
import CerberusHeapLang.Examples.CorpusE5
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.EmittedAExhibit
import CerberusHeapLang.EmittedBExhibit

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

/-- Fresh symbols generated above the source-variable numbers preserve
    the two source-pointer bindings, regardless of their descriptions. -/
theorem t4SourceFrame.fresh {pi ps : CerbMem.PointerValue} {f : Fmap sym value}
    (k : Nat) (v : value) (hk : 510 ≤ k) (h : t4SourceFrame pi ps f) :
    t4SourceFrame pi ps (envAdd (fresh_given_int k) v f) := by
  have hi : symOrd t4iSym (fresh_given_int k) ≠ .eq := symOrd_ne_eq_of_num_ne (by omega)
  have hs : symOrd t4sSym (fresh_given_int k) ≠ .eq := symOrd_ne_eq_of_num_ne (by omega)
  exact ⟨h.1.add _ _, by rw [envAdd_lookup h.1, if_neg hi]; exact h.2.1,
    by rw [envAdd_lookup h.1, if_neg hs]; exact h.2.2⟩

/-- An emitted integer assignment with an annotated, effectful RHS.
    Evaluate its pointer operand in the RHS's resulting frame, bind the
    tuple, perform the negative store, and discard the statement value. -/
theorem wpt_t4Assign [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (x : sym) (start n m : Nat) (v : Int) (hnm : m ≠ n)
    (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (rhs : CoreExpr) (hnf : negFree rhs = true) (hpot : pot rhs + 6 ≤ lemDefaultFuel)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (k : Nat)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte) :
    wpt M p Ls Θ k (fun w ρ' => iprop(∃ (f' : Fmap sym value) (ds : List dyn_annotation),
      ⌜w = .annot ds (lint v) ∧ ρ' = f' :: rest ∧ SymFrame f' ∧
        fmapLookupBy symCmpK x f' = some (Vobject (OVpointer pv))⌝ ∗
      pointsToCell M.tagDefs pv (.own 1) intTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pv (.own 1) intTy (emittedIntBytes M.tagDefs v) -∗
        Ψ (.pure Vunit) (envAdd s (lint v) (t5frAssign n m v pv f') :: rest)))) rhs (f :: rest) ⊢
      wpt M p Ls Θ (k + 22) Ψ (CorpusE0.t4Assign x start n m rhs) (f :: rest) := by
  iintro H
  unfold CorpusE0.t4Assign
  rw [show k + 22 = (k + 21) + 1 by omega]
  iapply wpt_seq _ _ _ _ _ _ _ (k + 21) 1
  unfold CorpusE0.bnd
  rw [show (Pattern [] (CaseCtor Ctuple
    [Pattern [] (CaseBase (some (t5a n), ptrTy)), Pattern [] (CaseBase (some (t5a m), CorpusE0.lint))]) : pattern) =
    tuplePat [] [([], some (t5a n), ptrTy), ([], some (t5a m), CorpusE0.lint)] from rfl,
    show k + 21 = (k + 5) + 16 by omega]
  iapply wpt_bound_wseq_tuple _ _ _ _ _ _ _ _ (k + 5) 16
    (by simpa only [negFree, negFreeList, Bool.true_and, Bool.and_true] using hnf)
    (by change 2 + (1 + 2 + (1 + pot rhs + 0)) ≤ lemDefaultFuel; omega)
  iapply wpt_unseq_pure_left _ _ (psym x) rhs (f :: rest) k rfl
  iapply wpt_mono ?_ k rhs (f :: rest) $$ H
  intro w ρ'
  iintro ⟨%f', %ds, %hw, Hpt, HΨ⟩
  obtain ⟨rfl, rfl, hf', hl⟩ := hw
  iexists (Vobject (OVpointer pv))
  isplit
  · ipureintro; exact t1sym_eval hex rest hl
  simp only [SpikeVal.mergeInto, SpikeVal.merge, SpikeVal.val, List.append_nil]
  iexists [Vobject (OVpointer pv), lint v], ds
  isplit
  · ipureintro; rfl
  rw [update_env_tuple2_mixed]
  rw [show (Expr [] (Eannot ds (Expr [] (Ewseq wc
      (Expr [Astd "§6.5.16.1#2, store"] (Eaction (Paction polarity.Neg0
        (Action (CorpusE0.t4RegP start (start + 9) (start + 2)) empty_annotation
          (Store0 false CorpusE0.intCty (psym (t5a n)) (CorpusE0.convLoadedInt (t5a m)) NA)))))
      (t5Pure (CorpusE0.convLoadedInt (t5a m)))))) : CoreExpr) =
    negAssignBody [] [] [Astd "§6.5.16.1#2, store"] [] [] ds BTy_unit
      (CorpusE0.t4RegP start (start + 9) (start + 2)) empty_annotation intTy
      (psym (t5a n)) (CorpusE0.convLoadedInt (t5a m)) (CorpusE0.convLoadedInt (t5a m)) NA from rfl]
  iapply wpt_emittedIntStore hstd hex (CorpusE0.t4RegP start (start + 9) (start + 2))
    (t5a n) (t5a m) ds v (t4a_ne hnm) hv1 hv2 f' rest hf' pv bs
  isplitl [Hpt]
  · iexact Hpt
  iintro %s %hs Hpt
  unfold t5Unit t5Pure
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  iapply HΨ $$ %s %hs Hpt

/-- The emitted `s = s + i`, preserving i's cell and both source pointers. -/
theorem wpt_t4AssignS [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hsup : 600 ≤ M.runState.sym_supply)
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
      (∀ f', ⌜t4SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) intTy bi -∗
        pointsToCell M.tagDefs ps (.own 1) intTy (emittedIntBytes M.tagDefs (s + i)) -∗
        Ψ (.pure Vunit) (f' :: rest))) ⊢
      wpt M p Ls Θ 40 Ψ (CorpusE0.t4Assign t4sSym 64 555 563 CorpusE0.t4AddSI) (f :: rest) := by
  iintro ⟨Hi, Hs, HΨ⟩
  iapply wpt_t4Assign hstd hex t4sSym 64 555 563 (s + i) (by decide +kernel) hsum hsum'
    CorpusE0.t4AddSI rfl (Nat.le_of_ble_eq_true rfl) f rest 18 ps bs
  iapply wpt_t4AddSI hex i s hi hi' hs hs' hsum hsum' f rest pi ps bi bs hf hloadI htrapI hloadS htrapS
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro Hi Hs
  have hfa : t4SourceFrame pi ps (t4frAddSI pi ps i s f) := by
    unfold t4frAddSI t4frAdd
    t4_source
  iexists (t4frAddSI pi ps i s f), _
  isplit
  · ipureintro; exact ⟨rfl, rfl, hfa.1, hfa.2.2⟩
  isplitl [Hs]
  · iexact Hs
  iintro %z %hz Hs
  obtain ⟨k, rfl, hk⟩ := hz
  have hfinal : t4SourceFrame pi ps (envAdd (fresh_given_int k) (lint (s + i))
      (t5frAssign 555 563 (s + i) ps (t4frAddSI pi ps i s f))) := by
    apply t4SourceFrame.fresh k _ (by omega)
    unfold t5frAssign
    t4_source
  iapply HΨ $$ %_ %hfinal Hi Hs

/-- The emitted `i = i + 1`, preserving s's cell and both source pointers. -/
theorem wpt_t4AssignI [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hsup : 600 ≤ M.runState.sym_supply)
    (i : Int) (hi : -2147483648 ≤ i) (hi' : i + 1 ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : t4SourceFrame pi ps f)
    (hloadI : loadedVal M.tagDefs pi intTy bi = lint i)
    (htrapI : cellLoadTrap M.tagDefs ⟨addrOf pi, intTy, bi⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) intTy bs ∗
      (∀ f', ⌜t4SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) intTy (emittedIntBytes M.tagDefs (i + 1)) -∗
        pointsToCell M.tagDefs ps (.own 1) intTy bs -∗
        Ψ (.pure Vunit) (f' :: rest))) ⊢
      wpt M p Ls Θ 36 Ψ (CorpusE0.t4Assign t4iSym 75 564 571 CorpusE0.t4AddI1) (f :: rest) := by
  iintro ⟨Hi, Hs, HΨ⟩
  iapply wpt_t4Assign hstd hex t4iSym 75 564 571 (i + 1) (by decide +kernel) (by omega) hi'
    CorpusE0.t4AddI1 rfl (Nat.le_of_ble_eq_true rfl) f rest 14 pi bi
  iapply wpt_t4AddI1 hex i hi hi' f rest hf.1 pi bi hf.2.1 hloadI htrapI
  isplitl [Hi]
  · iexact Hi
  iintro Hi
  have hfa : t4SourceFrame pi ps (t4frAddI1 pi i f) := by
    unfold t4frAddI1 t4frAdd
    t4_source
  iexists (t4frAddI1 pi i f), _
  isplit
  · ipureintro; exact ⟨rfl, rfl, hfa.1, hfa.2.1⟩
  isplitl [Hi]
  · iexact Hi
  iintro %z %hz Hi
  obtain ⟨k, rfl, hk⟩ := hz
  have hfinal : t4SourceFrame pi ps (envAdd (fresh_given_int k) (lint (i + 1))
      (t5frAssign 564 571 (i + 1) pi (t4frAddI1 pi i f))) := by
    apply t4SourceFrame.fresh k _ (by omega)
    unfold t5frAssign
    t4_source
  iapply HΨ $$ %_ %hfinal Hi Hs

/-- Both pointer parameters are rebound by each loop save and run. -/
abbrev t4frPtrs (pi ps : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd t4sSym (Vobject (OVpointer ps)) (envAdd t4iSym (Vobject (OVpointer pi)) f)

theorem t4SourceFrame.params (pi ps : CerbMem.PointerValue) (f : Fmap sym value) (hf : SymFrame f) :
    t4SourceFrame pi ps (t4frPtrs pi ps f) := by
  refine ⟨(hf.add _ _).add _ _, ?_, ?_⟩
  · rw [envAdd_lookup (hf.add _ _), if_neg (by decide +kernel), envAdd_lookup hf,
      if_pos (symOrd_self _)]
  · rw [envAdd_lookup (hf.add _ _), if_pos (symOrd_self _)]

theorem t4PtrParams_bindArgs (pi ps : CerbMem.PointerValue)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs t4PtrParams [Vobject (OVpointer pi), Vobject (OVpointer ps)] (f :: rest) =
      t4frPtrs pi ps f :: rest := by
  change update_env (mk_sym_pat t4sSym ptrTy) (Vobject (OVpointer ps))
    (update_env (mk_sym_pat t4iSym ptrTy) (Vobject (OVpointer pi)) (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons, update_env_aux_sym]

theorem t4PtrInits_bindSaveParams (pi ps : CerbMem.PointerValue)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams CorpusE0.t4PtrInits [Vobject (OVpointer pi), Vobject (OVpointer ps)] (f :: rest) =
      t4frPtrs pi ps f :: rest := by
  change update_env (mk_sym_pat t4sSym ptrTy) (Vobject (OVpointer ps))
    (update_env (mk_sym_pat t4iSym ptrTy) (Vobject (OVpointer pi)) (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons, update_env_aux_sym]

theorem t4PtrArgs_eval {M : MachineCtx} (hex : ∀ x, resolveExtern M.extern x = x)
    (pi ps : CerbMem.PointerValue) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : t4SourceFrame pi ps f) :
    evalPexprs M.tagDefs M.extern M.file (f :: rest) [psym t4iSym, psym t4sSym] =
      some [Vobject (OVpointer pi), Vobject (OVpointer ps)] := by
  rw [evalPexprs_cons, t1sym_eval hex rest hf.2.1,
    evalPexprs_cons, t1sym_eval hex rest hf.2.2, evalPexprs_nil]
  rfl

/-- Entry at any of t4's pointer-parameter saves, retaining the actual
    rebinding and the two-step initializer cost. -/
theorem wpt_t4Save [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (l : sym) (body : CoreExpr) (k : Nat)
    (pi ps : CerbMem.PointerValue) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : t4SourceFrame pi ps f) :
    wpt M p Ls Θ k Ψ body (t4frPtrs pi ps f :: rest) ⊢
      wpt M p Ls Θ (k + 2) Ψ (CorpusE0.t4Save l body) (f :: rest) := by
  unfold CorpusE0.t4Save
  rw [show (2 : Nat) = saveEntryCost CorpusE0.t4PtrInits from rfl]
  iintro H
  iapply wpt_save _ _ _ _ f rest (t4PtrArgs_eval hex pi ps f rest hf)
  rw [t4PtrInits_bindSaveParams]
  iexact H

/-- One whole emitted loop body, including both assignments, the continue
    save and the jump to the registered while continuation. The caller
    supplies its next label precondition at budget m; the body costs 82+m. -/
theorem wpt_t4Body [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t4Q) (hsup : 600 ≤ M.runState.sym_supply)
    (i s : Int) (hi : -2147483648 ≤ i) (hi' : i + 1 ≤ 2147483647)
    (hs : -2147483648 ≤ s) (hs' : s ≤ 2147483647)
    (hsum : -2147483648 ≤ s + i) (hsum' : s + i ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (bi bs : List CerbMem.AbsByte)
    (hf : t4SourceFrame pi ps f)
    (hloadI : loadedVal M.tagDefs pi intTy bi = lint i)
    (htrapI : cellLoadTrap M.tagDefs ⟨addrOf pi, intTy, bi⟩ = false)
    (hloadS : loadedVal M.tagDefs ps intTy bs = lint s)
    (htrapS : cellLoadTrap M.tagDefs ⟨addrOf ps, intTy, bs⟩ = false) (m : Nat) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy bi ∗
      pointsToCell M.tagDefs ps (.own 1) intTy bs ∗
      (∀ f', ⌜t4SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) intTy (emittedIntBytes M.tagDefs (i + 1)) -∗
        pointsToCell M.tagDefs ps (.own 1) intTy (emittedIntBytes M.tagDefs (s + i)) -∗
        Ls t4WhileSym m [Vobject (OVpointer pi), Vobject (OVpointer ps)] (f' :: rest))) ⊢
      wpt M p Ls Θ (82 + m) Ψ CorpusE0.t4Body (f :: rest) := by
  iintro ⟨Hi, Hs, Hnext⟩
  unfold CorpusE0.t4Body seqE wc
  rw [show 82 + m = 81 + (1 + m) by omega]
  iapply wpt_seq _ _ _ _ _ _ _ 81 (1 + m)
  iapply wpt_seq _ _ _ _ _ _ _ 77 4
  iapply wpt_seq _ _ _ _ _ _ _ 40 37
  iapply wpt_t4AssignS hstd hex hsup i s hi (by omega) hs hs' hsum hsum'
    f rest pi ps bi bs hf hloadI htrapI hloadS htrapS
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f1 %hf1 Hi Hs
  iapply wpt_seq _ _ _ _ _ _ _ 36 1
  iapply wpt_t4AssignI hstd hex hsup i hi hi' f1 rest pi ps bi _ hf1 hloadI htrapI
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f2 %hf2 Hi Hs
  unfold t5Unit t5Pure
  rw [← ofValA_pure [] [] Vunit]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 1
  iapply wpt_t4Save hex t4ContinueSym _ 1 pi ps f2 rest hf2
  rw [← ofValA_pure [Aloc (t4Reg 39 87), Astmt] [] Vunit]
  iapply wpt_ofValA (.pure [Aloc (t4Reg 39 87), Astmt] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
  iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
  simp only [SpikeValA.erase_pure]
  have hfinal := t4SourceFrame.params pi ps f2 hf2.1
  iapply wpt_run [] empty_annotation t4WhileSym [psym t4iSym, psym t4sSym]
    (t4frPtrs pi ps f2) rest m (by rw [hQ]; exact t4Q_while)
    (t4PtrArgs_eval hex pi ps _ rest hfinal) (Nat.le_refl (1 + m))
  iapply Hnext $$ %_ %hfinal Hi Hs

/-- The loop's mathematical sum, with the same recurrence as its body. -/
def t4Sum : Nat → Nat
  | 0 => 0
  | n + 1 => t4Sum n + n

theorem t4Sum_succ (n : Nat) : (t4Sum (n + 1) : Int) = (t4Sum n : Int) + (n : Int) :=
  Int.natCast_add _ _

theorem t4Index_cases {n : Nat} (hn : n ≤ 5) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega

theorem t4Sum_le {n : Nat} (hn : n ≤ 5) : t4Sum n ≤ 10 := by
  rcases t4Index_cases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- The actual C conjunction agrees with n<5 on the invariant. -/
theorem t4Guard {n : Nat} (hn : n ≤ 5) :
    (decide ((n : Int) < 5) && decide ((t4Sum n : Int) < 7)) = decide (n < 5) := by
  rcases t4Index_cases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Byte readouts for the six invariant states. Only finite scalar byte
    encodings are reduced here, never the program's execution. -/
theorem t4Index_loaded (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    {n : Nat} (hn : n ≤ 5) :
    loadedVal tds pv intTy (emittedIntBytes tds n) = lint n := by
  rcases t4Index_cases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem t4Sum_loaded (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    {n : Nat} (hn : n ≤ 5) :
    loadedVal tds pv intTy (emittedIntBytes tds (t4Sum n)) = lint (t4Sum n) := by
  rcases t4Index_cases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- 159 per back edge; 98 for the final condition, saves, cleanup and return. -/
def t4Budget (n : Nat) : Nat := 159 * (5 - n) + 98

theorem t4Budget_succ {n : Nat} (hn : n < 5) :
    t4Budget n = 159 + t4Budget (n + 1) := by unfold t4Budget; omega

/-- The loop arguments carry the owned cells and ordinary frame validity.
    The registered continuation rebinds both source pointers on entry. -/
def t4Cells (GF : BundledGFunctors) [SpikeGS .hasLC GF]
    (tds : CerbTags.TagDefsMap) (n : Nat) (vs : List value) (ρ : EnvStack) : IProp GF :=
  iprop(∃ (pi ps : CerbMem.PointerValue) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [Vobject (OVpointer pi), Vobject (OVpointer ps)] ∧ ρ = f :: rest ∧ SymFrame f ∧ n ≤ 5⌝ ∗
    pointsToCell tds pi (.own 1) intTy (emittedIntBytes tds n) ∗
    pointsToCell tds ps (.own 1) intTy (emittedIntBytes tds (t4Sum n)))

def t4LsT (GF : BundledGFunctors) [SpikeGS .hasLC GF]
    (tds : CerbTags.TagDefsMap) : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜l = t4RetSym ∧ m = 2 ∧ vs = [lint 10] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝ ∨
    ∃ n, ⌜l = t4WhileSym ∧ m = t4Budget n⌝ ∗ t4Cells GF tds n vs ρ)

def ψT4 : value → Mem → Prop := fun v _ => v = lint 10

theorem t4RetParams_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs t4RetParams [v] (f :: rest) = envAdd (t5a 574) v f :: rest := by
  show update_env (mk_sym_pat (t5a 574) CorpusE0.lint) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem t4Kill_eq (x : sym) : CorpusE0.t4Kill x =
    killOpRedex [] (t4Reg 0 99) empty_annotation (Static0 intTy) (psym x) := rfl

/-- Read the final sum, dispose of both cells and jump to the real return
    continuation. The emitted dead cleanup remains after that jump. -/
theorem wpt_t4Return [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t4Q)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : t4SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy (emittedIntBytes M.tagDefs 5) ∗
      pointsToCell M.tagDefs ps (.own 1) intTy (emittedIntBytes M.tagDefs 10)) ⊢
      wpt M p (t4LsT GF M.tagDefs) emptyProcSpecT 16 Ψ t4Return (f :: rest) := by
  have hframe := hf.1
  have hi := hf.2.1
  have hs := hf.2.2
  iintro ⟨Hi, Hs⟩
  simp only [t4Return, letS, seqE, wc, CorpusE0.bnd, t4Kill_eq]
  rw [show (Pattern [] (CaseBase (some (t5a 573), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 573) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 9
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_t4Load hex t4sSym 572 95 96 f rest hframe ps (emittedIntBytes M.tagDefs 10) (lint 10) hs rfl rfl
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
  iapply wpt_kill_eval _ _ _ _ _ _ rfl (pv := pi) (t1sym_eval hex rest (by t4_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 intTy) pi intTy (emittedIntBytes M.tagDefs 5) _ (Nat.le_refl 2) rfl
  isplitl [Hi]
  · iexact Hi
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 3
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ _ _ _ _ rfl (pv := ps) (t1sym_eval hex rest (by t4_lookup))
  iapply wpt_kill_emp _ _ _ (Static0 intTy) ps intTy (emittedIntBytes M.tagDefs 10) _ (Nat.le_refl 2) rfl
  isplitl [Hs]
  · iexact Hs
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 3 0
  iapply wpt_run [] empty_annotation t4RetSym [CorpusE0.convLoadedInt (t5a 573)] _ _ 2
    (by rw [hQ]; exact t4Q_ret)
    (by rw [evalPexprs_cons, t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by t4_lookup))
      (by decide) (by decide), evalPexprs_nil]; rfl) (Nat.le_refl 3)
  dsimp only [t4LsT]
  ileft
  ipureintro
  exact ⟨rfl, rfl, rfl, _, _, rfl, by t4_frame⟩

/-- The loop test selects the actual body or final unit on the invariant,
    with 77 units before the selected branch. -/
theorem wpt_t4LoopTest [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (n : Nat) (hn : n ≤ 5) (k : Nat)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : t4SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy (emittedIntBytes M.tagDefs n) ∗
      pointsToCell M.tagDefs ps (.own 1) intTy (emittedIntBytes M.tagDefs (t4Sum n)) ∗
      (∀ f', ⌜t4SourceFrame pi ps f'⌝ -∗
        pointsToCell M.tagDefs pi (.own 1) intTy (emittedIntBytes M.tagDefs n) -∗
        pointsToCell M.tagDefs ps (.own 1) intTy (emittedIntBytes M.tagDefs (t4Sum n)) -∗
        wpt M p Ls Θ k Ψ (if n < 5 then CorpusE0.t4Body else t5Unit) (f' :: rest))) ⊢
      wpt M p Ls Θ (77 + k) Ψ t4LoopTest (f :: rest) := by
  have hsum := t4Sum_le hn
  iintro ⟨Hi, Hs, Hnext⟩
  unfold t4LoopTest letS
  rw [show (Pattern [] (CaseBase (some (t5a 517), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 517) CorpusE0.lint from rfl, show 77 + k = 72 + (5 + k) by omega]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 72 (5 + k)
  iapply wpt_t4Cond hstd hex n (t4Sum n) (by omega) (by omega) (by omega) (by omega)
    f rest pi ps _ _ hf (t4Index_loaded _ _ hn) rfl (t4Sum_loaded _ _ hn) rfl
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f1 %hf1 Hi Hs
  rw [t4Guard hn]
  iexists (lint (t4Bit (!decide (n < 5))))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (t5a 516), BTy_boolean)) : pattern) =
    symPat [] (t5a 516) BTy_boolean from rfl, show 5 + k = 4 + (k + 1) by omega]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 4 (k + 1)
  iapply wpt_t4Bool _ (decide (n < 5)) (t1sym_eval hex rest (by
    rw [envAdd_lookup hf1.1, if_pos (symOrd_self _)]))
  iexists (boolValue (decide (n < 5)))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_if _ _ _ _ _ (decide (n < 5))
  isplit
  · ipureintro
    exact t1sym_eval hex rest (by rw [envAdd_lookup (hf1.1.add _ _), if_pos (symOrd_self _)])
  rw [show (bif decide (n < 5) then CorpusE0.t4Body else t5Unit) =
    (if n < 5 then CorpusE0.t4Body else t5Unit) by by_cases h : n < 5 <;> simp [h]]
  have hfinal : t4SourceFrame pi ps (envAdd (t5a 516) (boolValue (decide (n < 5)))
      (envAdd (t5a 517) (lint (t4Bit (!decide (n < 5)))) f1)) := by t4_source
  iapply Hnext $$ %_ %hfinal Hi Hs

/-- A continuing iteration establishes the next while-label invariant,
    using the strictly smaller budget for n+1. -/
theorem wpt_t4LoopStep [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t4Q) (hsup : 600 ≤ M.runState.sym_supply)
    (n : Nat) (hlt : n < 5)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : t4SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy (emittedIntBytes M.tagDefs n) ∗
      pointsToCell M.tagDefs ps (.own 1) intTy (emittedIntBytes M.tagDefs (t4Sum n))) ⊢
      wpt M p (t4LsT GF M.tagDefs) emptyProcSpecT (t4Budget n) Ψ t4LoopTest (f :: rest) := by
  have hn : n ≤ 5 := by omega
  have hsum := t4Sum_le hn
  iintro ⟨Hi, Hs⟩
  rw [t4Budget_succ hlt, show 159 + t4Budget (n + 1) = 77 + (82 + t4Budget (n + 1)) by omega]
  iapply wpt_t4LoopTest hstd hex n hn (82 + t4Budget (n + 1)) f rest pi ps hf
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f1 %hf1 Hi Hs
  rw [if_pos hlt]
  iapply wpt_t4Body hstd hex hQ hsup n (t4Sum n) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) f1 rest pi ps _ _ hf1 (t4Index_loaded _ _ hn) rfl
    (t4Sum_loaded _ _ hn) rfl (t4Budget (n + 1))
  isplitl [Hi]
  · iexact Hi
  isplitl [Hs]
  · iexact Hs
  iintro %f2 %hf2 Hi Hs
  dsimp only [t4LsT]
  iright
  iexists (n + 1)
  isplit
  · ipureintro; exact ⟨rfl, rfl⟩
  dsimp only [t4Cells]
  iexists pi, ps, f2, rest
  isplit
  · ipureintro; exact ⟨rfl, rfl, hf2.1, by omega⟩
  rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 by omega, t4Sum_succ]
  isplitl [Hi]
  · iexact Hi
  iexact Hs

/-- The registered while continuation satisfies the invariant budget.
    A true test advances n and spends 159; the n=5 path costs 98. -/
theorem wpt_t4WhileCont [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t4Q) (hsup : 600 ≤ M.runState.sym_supply)
    (n : Nat) (hn : n ≤ 5)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : t4SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy (emittedIntBytes M.tagDefs n) ∗
      pointsToCell M.tagDefs ps (.own 1) intTy (emittedIntBytes M.tagDefs (t4Sum n))) ⊢
      wpt M p (t4LsT GF M.tagDefs) emptyProcSpecT (t4Budget n) Ψ t4WhileCont (f :: rest) := by
  iintro ⟨Hi, Hs⟩
  by_cases hlt : n < 5
  · unfold t4WhileCont t4LoopContext seqE wc
    rw [show t4Budget n = t4Budget n + 0 from rfl]
    iapply wpt_seq _ _ _ _ _ _ _ (t4Budget n) 0
    iapply wpt_seq _ _ _ _ _ _ _ (t4Budget n) 0
    iapply wpt_t4LoopStep hstd hex hQ hsup n hlt f rest pi ps hf
    isplitl [Hi]
    · iexact Hi
    iexact Hs
  · have hn5 : n = 5 := by omega
    subst n
    rw [show t4Budget 5 = 98 from rfl]
    unfold t4WhileCont t4LoopContext seqE wc
    iapply wpt_seq _ _ _ _ _ _ _ 82 16
    iapply wpt_seq _ _ _ _ _ _ _ 78 4
    iapply wpt_t4LoopTest hstd hex 5 (by decide +kernel) 1 f rest pi ps hf
    isplitl [Hi]
    · iexact Hi
    isplitl [Hs]
    · iexact Hs
    iintro %f1 %hf1 Hi Hs
    rw [if_neg (by decide +kernel), show (t4Sum 5 : Int) = 10 from rfl]
    unfold t5Unit t5Pure
    rw [← ofValA_pure [] [] Vunit]
    iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
    simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
    unfold t4AfterWhile seqE wc
    iapply wpt_seq _ _ _ _ _ _ _ 3 1
    iapply wpt_t4Save hex t4BreakSym _ 1 pi ps f1 rest hf1
    rw [← ofValA_pure [Aloc (t4Reg 39 87), Astmt] [] Vunit]
    iapply wpt_ofValA (.pure [Aloc (t4Reg 39 87), Astmt] [] Vunit) _ (Nat.le_refl 1)
    simp only [SpikeValA.erase_pure, SpikeVal.mergeInto]
    unfold t5Unit t5Pure
    rw [← ofValA_pure [] [] Vunit]
    iapply wpt_ofValA (.pure [] [] Vunit) _ (Nat.le_refl 1)
    simp only [SpikeValA.erase_pure]
    iapply wpt_t4Return hstd hex hQ (t4frPtrs pi ps f1) rest pi ps (t4SourceFrame.params pi ps f1 hf1.1)
    isplitl [Hi]
    · iexact Hi
    iexact Hs

/-- The two reachable jump entries are while and return. The other
    registered continuations remain in the whole-term fragment proof;
    their saves execute on the normal path, but no run targets them. -/
theorem t4_blockSpecsT [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t4Q) (hsup : 600 ≤ M.runState.sym_supply) :
    ⊢ blockSpecsT (GF := GF) M p (t4LsT GF M.tagDefs) emptyProcSpecT (readoutPost ψT4) := by
  refine blockSpecsT_intro fun l params cont vs f rest m hl => ?_
  dsimp only [t4LsT]
  iintro HL
  icases HL with (Hr | Hw)
  · icases Hr with %hpure
    obtain ⟨rfl, rfl, rfl, f', rest', hρ, hf⟩ := hpure
    obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
    rw [hQ, t4Q_ret] at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    rw [t4RetParams_bindArgs]
    unfold t4RetCont t5Pure
    iapply wpt_pure (psym (t5a 574)) _ (Nat.le_refl 2) rfl (t1sym_eval hex rest (by t4_lookup))
    iintro %σ' %ns %κs %nt -
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    rfl
  · icases Hw with ⟨%n, %hpure, Hcells⟩
    obtain ⟨rfl, rfl⟩ := hpure
    rw [hQ, t4Q_while] at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    dsimp only [t4Cells]
    icases Hcells with ⟨%pi, %ps, %f', %rest', %hargs, Hi, Hs⟩
    obtain ⟨rfl, hρ, hf, hn⟩ := hargs
    obtain ⟨rfl, rfl⟩ := List.cons.inj hρ
    rw [t4PtrParams_bindArgs]
    iapply wpt_t4WhileCont hstd hex hQ hsup n hn (t4frPtrs pi ps f) rest pi ps
      (t4SourceFrame.params pi ps f hf)
    isplitl [Hi]
    · iexact Hi
    iexact Hs

/-- Entry executes the emitted while save before its first continuing
    iteration; the registered continuation handles subsequent iterations. -/
theorem wpt_t4WhileEntry [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t4Q) (hsup : 600 ≤ M.runState.sym_supply)
    (f : Fmap sym value) (rest : List (Fmap sym value))
    (pi ps : CerbMem.PointerValue) (hf : t4SourceFrame pi ps f) :
    iprop(pointsToCell M.tagDefs (GF := GF) pi (.own 1) intTy (emittedIntBytes M.tagDefs 0) ∗
      pointsToCell M.tagDefs ps (.own 1) intTy (emittedIntBytes M.tagDefs 0)) ⊢
      wpt M p (t4LsT GF M.tagDefs) emptyProcSpecT 895 Ψ (t4LoopContext t4While) (f :: rest) := by
  iintro ⟨Hi, Hs⟩
  unfold t4LoopContext seqE wc t4While
  iapply wpt_seq _ _ _ _ _ _ _ 895 0
  iapply wpt_seq _ _ _ _ _ _ _ 895 0
  iapply wpt_t4Save hex t4WhileSym _ 893 pi ps f rest hf
  rw [← show t4Budget 0 = 893 from rfl]
  iapply wpt_t4LoopStep hstd hex hQ hsup 0 (by decide +kernel) (t4frPtrs pi ps f) rest pi ps
    (t4SourceFrame.params pi ps f hf.1)
  isplitl [Hi]
  · iexact Hi
  rw [show (t4Sum 0 : Int) = 0 from rfl]
  iexact Hs

/-- The emitted main: 20 units for two allocations and initialization,
    then 895 for the while entry and its label path. -/
theorem t4_wpt [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = t4Q) (hsup : 600 ≤ M.runState.sym_supply)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4)) ⊢
      wpt M p (t4LsT GF M.tagDefs) emptyProcSpecT 915 (readoutPost ψT4) t4Main (f :: rest) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapI, HcapS⟩
  simp only [t4Main, letS, seqE, wc, CorpusE0.bnd, createInt_eq, act_store_eq]
  rw [show (Pattern [] (CaseBase (some t4iSym, ptrTy)) : pattern) =
    symPat [] t4iSym ptrTy from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 912
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [CorpusE0.intCty])) CorpusE0.intCty
    (PrefSource (t4Reg 15 99) [t4iSym]) _
    (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t4Reg 15 99) [t4iSym])
    _ (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapI]
  · iexact HcapI
  iintro %pi ⟨Hi, -⟩
  iexists (Vobject (OVpointer pi))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some t4sSym, ptrTy)) : pattern) = symPat [] t4sSym ptrTy from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 909
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [CorpusE0.intCty])) CorpusE0.intCty
    (PrefSource (t4Reg 15 99) [t4sSym]) _
    (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t4Reg 15 99) [t4sSym])
    _ (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapS]
  · iexact HcapS
  iintro %ps ⟨Hs, -⟩
  iexists (Vobject (OVpointer ps))
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  rw [show (Pattern [] (CaseBase (some (t5a 513), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 513) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 906
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_pure (specInt 0) _ (Nat.le_refl 2) rfl (specInt_eval _ 0)
  simp only [SpikeVal.val]
  iexists (lint 0)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 4 902
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ intTy (psym t4iSym) (CorpusE0.convLoadedInt (t5a 513)) NA _
    rfl (pv := pi) (cv := lint 0) (t1sym_eval hex rest (by t4_lookup))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by t4_lookup)) (by decide) (by decide))
  iapply wpt_store _ _ _ intTy pi (lint 0) NA (emittedIntMval 0) _ _ (Nat.le_refl 3)
    (emittedInt_encodes _ 0) (emittedInt_storable _ 0)
  isplitl [Hi]
  · iexact Hi
  iintro %fpI Hi
  simp only [SpikeVal.mergeInto]
  rw [show (Pattern [] (CaseBase (some (t5a 514), CorpusE0.lint)) : pattern) =
    symPat [] (t5a 514) CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 899
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)
  iapply wpt_pure (specInt 0) _ (Nat.le_refl 2) rfl (specInt_eval _ 0)
  iexists (lint 0)
  isplit
  · ipureintro; rfl
  rw [update_env_sym]
  iapply wpt_seq _ _ _ _ _ _ _ 4 895
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ _ intTy (psym t4sSym) (CorpusE0.convLoadedInt (t5a 514)) NA _
    rfl (pv := ps) (cv := lint 0) (t1sym_eval hex rest (by t4_lookup))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by t4_lookup)) (by decide) (by decide))
  iapply wpt_store _ _ _ intTy ps (lint 0) NA (emittedIntMval 0) _ _ (Nat.le_refl 3)
    (emittedInt_encodes _ 0) (emittedInt_storable _ 0)
  isplitl [Hs]
  · iexact Hs
  iintro %fpS Hs
  simp only [SpikeVal.mergeInto]
  rw [show (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [Aloc (t4Reg 39 87), Astmt] (Esseq (Pattern [] (CaseBase (none, BTy_unit))) t4While t4AfterWhile))
    t4Return) : CoreExpr) = t4LoopContext t4While from rfl]
  have hsrc : t4SourceFrame pi ps
      (envAdd (t5a 514) (lint 0) (envAdd (t5a 513) (lint 0)
        (envAdd t4sSym (Vobject (OVpointer ps)) (envAdd t4iSym (Vobject (OVpointer pi)) f)))) := by
    apply t4SourceFrame.add _ _ (by decide +kernel)
    apply t4SourceFrame.add _ _ (by decide +kernel)
    exact t4SourceFrame.params pi ps f hf
  iapply wpt_t4WhileEntry hstd hex hQ hsup _ rest pi ps hsrc
  isplitl [Hi]
  · iexact Hi
  iexact Hs

/-- The shipped driver returns Specified(10) on the transcribed while loop
    and the current checked three-function std.core fragment. The premise
    `600 ≤ sup` is a SUFFICIENT floor (it keeps the fresh symbols the negative
    assignments draw away from every source binding), not a necessary one:
    the compiled composite delivers the same result at `sup = 0` (measured,
    docs/2026-09-07_l1-landing-notes.md). -/
theorem t4_certified_production (sup : Nat) (hsup : 600 ≤ sup)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 [] t4Main) args)
          ((initial_driver_state sup (prodFileLib stdlibE3 [] t4Main) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 10 ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQe := t4Main_labeledAt sup
  have hlbl := prodCtx_labels (f := prodFileLib stdlibE3 [] t4Main) hQe
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ_lib1 sup stdlibE3 t4Main hQe ψT4 915
      (wpt_driver_done_alloc (GF := SpikeGF) (ctl := prodCtl sup)
        (M₀ := prodCtx (prodFileLib stdlibE3 [] t4Main) (prodRSLib stdlibE3 [] sup t4Main))
        rfl rfl hlbl rfl rfl rfl rfl (Nat.le_refl _)
        (fun l params cont hl => t4Q_frag (by rw [← hlbl]; exact hl))
        (fun l params cont hl => t4Q_pot (by rw [← hlbl]; exact hl))
        (t4LsT SpikeGF fmapEmpty)
        t4Main fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
        (allocCost fmapEmpty intTy 4 + allocCost fmapEmpty intTy 4) CorpusE0.t4Main_frag
        t4Main_pot
        (prodMem₀_launchCoh _ prod_two_int_budget_fits)
        ψT4 915
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply t4_blockSpecsT
              (M := prodCtx (prodFileLib stdlibE3 [] t4Main) (prodRSLib stdlibE3 [] sup t4Main))
              rfl (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl hsup
          · iapply t4_wpt (M := prodCtx (prodFileLib stdlibE3 [] t4Main) (prodRSLib stdlibE3 [] sup t4Main))
              rfl (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl hsup fmapEmpty []
              symFrame_empty $$ Hcap))
      (by rw [show CerbFuel.driverFuel = 99999999 + 1 from rfl]; omega)
      fs args
  exact ⟨dres, dst', heq, hψ, hbl, hout, herr⟩
end CerberusHeapLang
