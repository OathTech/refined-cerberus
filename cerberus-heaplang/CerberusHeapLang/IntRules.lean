/-
CerberusHeapLang.IntRules — THE DEMO'S FIRST C INTEGER RULES (dialect arc E3;
docs/2026-09-05_e3-notes.md).

The emitted dialect computes a C `int` expression `x + y` as
```
pure(case (a, b) of
  | (Specified(a': integer), Specified(b': integer)) =>
      Specified(catch_exceptional_condition_add('signed int',
        __conv_int__('signed int', a'), __conv_int__('signed int', b')))
  | _: (loaded integer, loaded integer) => undef(<<UB036_exceptional_condition>>)
  end)
```
(docs/corpus-e0/t1.core:17–23) and every C conversion as
`conv_loaded_int('signed int', e)` (std.core:61–67 → `conv_int` →
`is_representable_integer`). The engine's semantics of the two AST
constructors are its OWN functions `mk_conv_int` and
`mk_call_catch_exceptional_condition` (core_eval.lem:61–113) over the
memory model's integer values; the std.core calls unfold through the file
(StdCore.lean). This module states them as rules in the Reynolds/O'Hearn
shape — PURE premises, no memory: the operands' values and the RANGE
conditions of the pinned implementation's `int`
(`CerbMem.minIval`/`maxIval (Signed Int_)`, evaluated by the model to
`-2147483648`/`2147483647`: `int_min_eq`/`int_max_eq`, kernel-checked) —
at three strata:

* the ENGINE FUNCTIONS: `mk_conv_int_int_in_range` (a representable
  `int` converts to itself), `mk_call_catch_add_in_range` (an in-range sum
  is delivered), `mk_call_catch_add_overflow` (out of range: `none`, the
  engine's `undef [UB036_exceptional_condition]`);
* the MIRROR EVALUATOR: `evalPexpr_conv_int_int`, `evalPexpr_catch_add_int`,
  `evalPexpr_isRepr_int`, `evalPexpr_convInt_call_int`,
  `evalPexpr_convLoadedInt_spec`/`_unspec`, and the emitted `+`
  `evalPexpr_cAdd`; the OUT-OF-RANGE face `evalClass_cAdd_overflow`: the
  classifier's `.undef loc [UB036_exceptional_condition]` — through
  `complete_pure_op` (Round.lean) the shipped round is the KILL
  `Undef0 loc [UB036_exceptional_condition]`, never a default value;
* the JUDGMENTS: `wps_c_add`/`wpt_c_add` (the `+` node under `pure`) and
  `wps_conv_loaded_int`/`wpt_conv_loaded_int` (a conversion under `pure`);
  a conversion in an ACTION operand (`store(ty, x, conv_loaded_int(…))`) or
  a `run` argument composes through the generic ACTION_EVAL rules with the
  evaluator lemma as the operand premise (the E3 exhibit does both).

The client's proof obligation is the range condition: the UB036 kill is
EXCLUDED by hypothesis, never absorbed — "out-of-range ⇒ the UB kill is
excluded by the client's proof obligation" (the E3 brief). Where the
engine converts a NON-representable signed value, `mk_conv_int` wraps
(`mk_wrapI`) — not stated here (NO-RULE; the divergence note
../docs/2026-09-05_note-cerberus-lean-conv-int-divergence.md). -/
import CerberusHeapLang.Wpt
import CerberusHeapLang.EvalClass
import CerberusHeapLang.StdCore

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List
open Iris Iris.BI Iris.ProgramLogic

/-! ## The pinned implementation's `int` -/

/-- `signed int` (Examples/Layout.lean's `intTy`, restated here so the core
    module does not import an exhibit-support module). -/
def sintTy : ctype := Ctype [] (.Basic (.Integer (.Signed .Int_)))
def sintTyPe : generic_pexpr Unit sym := Pexpr [] () (PEval (Vctype sintTy))

/-- The loaded integer `Specified(n)` and the object integer `n`. -/
def lint (n : Int) : value := Vloaded (LVspecified (OVinteger (CerbMem.integerIval n)))
def oint (n : Int) : value := Vobject (OVinteger (CerbMem.integerIval n))
def ointPe (n : Int) : generic_pexpr Unit sym := Pexpr [] () (PEval (oint n))

/-- The memory model's `int` bounds (`CerbMem.minIval`/`maxIval` at the gcc
    impl: `sizeof_ity (Signed Int_) = some 4`), evaluated. -/
theorem int_min_eq : eval_integer_value (CerbMem.minIval (.Signed .Int_)) = some (-2147483648) := rfl
theorem int_max_eq : eval_integer_value (CerbMem.maxIval (.Signed .Int_)) = some 2147483647 := rfl

theorem eval_integer_value_ival (n : Int) : eval_integer_value (CerbMem.integerIval n) = some n := rfl

/-! ## The engine functions on `int` -/

/-- `mk_conv_int` at a REPRESENTABLE `int` is the identity
    (core_eval.lem:61–81: not `_Bool`, `min ≤ n ≤ max`). -/
theorem mk_conv_int_int_in_range (n : Int) (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    mk_conv_int (.Signed .Int_) (CerbMem.integerIval n) = CerbMem.integerIval n := by
  unfold mk_conv_int
  rw [eval_integer_value_ival, int_min_eq, int_max_eq]
  rw [show integerTypeEqual (.Signed .Int_) Bool0 = false from rfl]
  simp only [Bool.false_eq_true, if_false, intLteb, decide_eq_true h1, decide_eq_true h2,
    Bool.and_self, if_true]

/-- `mk_iop IOpAdd` at two provenance-free integers is their sum
    (`opIval IntAdd`, CerbMem.lean:1334–1339; `combineProv Prov_none Prov_none`). -/
theorem mk_iop_add_ival (a b : Int) :
    mk_iop IOpAdd (CerbMem.integerIval a) (CerbMem.integerIval b) = CerbMem.integerIval (a + b) := rfl
theorem mk_iop_sub_ival (a b : Int) :
    mk_iop IOpSub (CerbMem.integerIval a) (CerbMem.integerIval b) = CerbMem.integerIval (a - b) := rfl
theorem mk_iop_mul_ival (a b : Int) :
    mk_iop IOpMul (CerbMem.integerIval a) (CerbMem.integerIval b) = CerbMem.integerIval (a * b) := rfl

/-- `catch_exceptional_condition_add` at an IN-RANGE sum delivers it
    (core_eval.lem:99–111). -/
theorem mk_call_catch_add_in_range (a b : Int)
    (h1 : -2147483648 ≤ a + b) (h2 : a + b ≤ 2147483647) :
    mk_call_catch_exceptional_condition (.Signed .Int_) IOpAdd
      (CerbMem.integerIval a) (CerbMem.integerIval b) = some (CerbMem.integerIval (a + b)) := by
  unfold mk_call_catch_exceptional_condition
  dsimp only
  rw [mk_iop_add_ival, int_min_eq, int_max_eq, eval_integer_value_ival]
  simp only [intLteb, decide_eq_true h1, decide_eq_true h2, Bool.and_self, if_true]

/-- … and OUT OF RANGE it is `none`: the engine's `undef loc
    [UB036_exceptional_condition]` (core_eval.lem:847–848). -/
theorem mk_call_catch_add_overflow (a b : Int)
    (h : a + b < -2147483648 ∨ 2147483647 < a + b) :
    mk_call_catch_exceptional_condition (.Signed .Int_) IOpAdd
      (CerbMem.integerIval a) (CerbMem.integerIval b) = none := by
  unfold mk_call_catch_exceptional_condition
  dsimp only
  rw [mk_iop_add_ival, int_min_eq, int_max_eq, eval_integer_value_ival]
  rcases h with h | h
  · simp only [intLteb, decide_eq_false (by omega : ¬ (-2147483648 ≤ a + b)), Bool.false_and,
      Bool.false_eq_true, if_false]
  · simp only [intLteb, decide_eq_false (by omega : ¬ (a + b ≤ 2147483647)), Bool.and_false,
      Bool.false_eq_true, if_false]

/-! ## The mirror evaluator at the constructors -/

theorem evalConvInt_int (n : Int) (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalConvInt (.Signed .Int_) (oint n) = some (oint n) := by
  unfold evalConvInt oint; dsimp only; rw [mk_conv_int_int_in_range n h1 h2]

theorem evalCatch_add_int (a b : Int) (h1 : -2147483648 ≤ a + b) (h2 : a + b ≤ 2147483647) :
    evalCatch (.Signed .Int_) IOpAdd (oint a) (oint b) = some (oint (a + b)) := by
  unfold evalCatch oint; dsimp only; rw [mk_call_catch_add_in_range a b h1 h2]; rfl

theorem evalCatch_add_overflow (a b : Int) (h : a + b < -2147483648 ∨ 2147483647 < a + b) :
    evalCatch (.Signed .Int_) IOpAdd (oint a) (oint b) = none := by
  unfold evalCatch oint; dsimp only; rw [mk_call_catch_add_overflow a b h]; rfl

/-! ## The std.core bodies INSTANTIATED (what `callBody` delivers at `int`
arguments: the transcribed bodies with the parameters substituted —
`foldl2 subst_sym_pexpr`, computed by `rfl`) -/

/-- `Ivmin('signed int') <= n /\ n <= Ivmax('signed int')`. -/
def isReprInst (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEop OpAnd
    (Pexpr [] () (PEop OpLe (Pexpr [] () (PEctor Civmin [sintTyPe])) (ointPe n)))
    (Pexpr [] () (PEop OpLe (ointPe n) (Pexpr [] () (PEctor Civmax [sintTyPe])))))

def convIntThen (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEop OpEq (ointPe n) (stdInt 0))) (stdInt 0) (stdInt 1))
def convIntElse2 (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEis_unsigned sintTyPe))
    (Pexpr [] () (PEcall (Sym wrapISym) [sintTyPe, ointPe n]))
    (Pexpr [] () (PEcall (Impl Integer__conv_nonrepresentable_signed_integer) [sintTyPe, ointPe n])))
def convIntElse (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEcall (Sym isReprSym) [ointPe n, sintTyPe])) (ointPe n)
    (convIntElse2 n))
/-- `conv_int`'s body at `('signed int', n)`. -/
def convIntInst (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEop OpEq sintTyPe stdBoolTyPe)) (convIntThen n) (convIntElse n))

/-- `conv_loaded_int`'s alternatives at a ctype operand `tyPe`. -/
def cliAlts (tyPe : generic_pexpr Unit sym) : List (pattern × generic_pexpr Unit sym) :=
  [(Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some cliNSym, BTy_object OTy_integer))]),
    Pexpr [] () (PEctor Cspecified [Pexpr [] () (PEcall (Sym convIntSym) [tyPe, stdSym cliNSym])])),
   (Pattern [] (CaseCtor Cunspecified [Pattern [] (CaseBase (none, BTy_ctype))]),
    Pexpr [] () (PEctor Cunspecified [tyPe]))]
/-- `conv_loaded_int`'s body at `(ty, v)`. -/
def convLoadedIntInst (ty : ctype) (v : value) : generic_pexpr Unit sym :=
  Pexpr [] () (PEcase (Pexpr [] () (PEval v)) (cliAlts (Pexpr [] () (PEval (Vctype ty)))))

theorem callBody_isRepr {file : generic_file Unit core_run_annotation} (hstd : StdE3 file) (n : Int) :
    callBody file (Sym isReprSym) [oint n, Vctype sintTy] = some (isReprInst n) := by
  unfold callBody; rw [lookupFun_isRepr hstd]; rfl

theorem callBody_convInt {file : generic_file Unit core_run_annotation} (hstd : StdE3 file) (n : Int) :
    callBody file (Sym convIntSym) [Vctype sintTy, oint n] = some (convIntInst n) := by
  unfold callBody; rw [lookupFun_convInt hstd]; rfl

theorem callBody_convLoadedInt {file : generic_file Unit core_run_annotation} (hstd : StdE3 file)
    (ty : ctype) (v : value) :
    callBody file (Sym convLoadedIntSym) [Vctype ty, v] = some (convLoadedIntInst ty v) := by
  unfold callBody; rw [lookupFun_convLoadedInt hstd]; rfl

theorem peStrip_isReprInst (n : Int) : peStrip (isReprInst n) = isReprInst n := rfl
theorem peStrip_convIntInst (n : Int) : peStrip (convIntInst n) = convIntInst n := rfl
theorem peStrip_convLoadedIntInst (ty : ctype) (v : value) :
    peStrip (convLoadedIntInst ty v) = convLoadedIntInst ty v := rfl
theorem peDepth_isReprInst (n : Int) : peDepth (isReprInst n) = 4 := rfl
theorem peDepth_convIntInst (n : Int) : peDepth (convIntInst n) = 17 := rfl
theorem peDepth_convLoadedIntInst (ty : ctype) (v : value) :
    peDepth (convLoadedIntInst ty v) = 23 := rfl
theorem isPePure_convIntBranches (n : Int) :
    (isPePure (convIntThen n) && isPePure (convIntElse n)) = true := rfl
theorem isPePure_cliAlts (ty : ctype) :
    isPePureAlts (cliAlts (Pexpr [] () (PEval (Vctype ty)))) = true := rfl

section Evaluator
variable {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
  {file : generic_file Unit core_run_annotation} {ρ : EnvStack}

/-- `__conv_int__('signed int', e)` at a representable operand: the operand. -/
theorem evalPexpr_conv_int_int [LemFuel] (a : List annot) {pe : generic_pexpr Unit sym} {n : Int}
    (hv : evalPexpr tds ext file ρ pe = some (oint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext file ρ (Pexpr a () (PEconv_int (.Signed .Int_) pe)) = some (oint n) := by
  rw [evalPexpr_conv_int, hv]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact evalConvInt_int n h1 h2

/-- `catch_exceptional_condition_add('signed int', e1, e2)` at an in-range
    sum: the sum. -/
theorem evalPexpr_catch_add_int [LemFuel] (a : List annot) {pe1 pe2 : generic_pexpr Unit sym} {n1 n2 : Int}
    (hv1 : evalPexpr tds ext file ρ pe1 = some (oint n1))
    (hv2 : evalPexpr tds ext file ρ pe2 = some (oint n2))
    (h1 : -2147483648 ≤ n1 + n2) (h2 : n1 + n2 ≤ 2147483647) :
    evalPexpr tds ext file ρ
      (Pexpr a () (PEcatch_exceptional_condition (.Signed .Int_) IOpAdd pe1 pe2)) =
      some (oint (n1 + n2)) := by
  rw [evalPexpr_catch, hv1, hv2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact evalCatch_add_int n1 n2 h1 h2

/-- The engine's `if b then Vtrue else Vfalse` at a decided range test. -/
theorem boolValue_decide_true {P : Prop} [Decidable P] (h : P) : boolValue (decide P) = Vtrue := by
  rw [decide_eq_true h]; rfl

/-- `Ivmin('signed int')`/`Ivmax('signed int')` (`evalTyCtor` at the pinned
    impl's `int`). -/
theorem evalCtor_ivmin_int [LemFuel] :
    evalCtor tds Civmin [Vctype sintTy] =
      some (Vobject (OVinteger (CerbMem.minIval (.Signed .Int_)))) := rfl
theorem evalCtor_ivmax_int [LemFuel] :
    evalCtor tds Civmax [Vctype sintTy] =
      some (Vobject (OVinteger (CerbMem.maxIval (.Signed .Int_)))) := rfl

/-- The instantiated `is_representable_integer` body at a representable `n`. -/
theorem evalPexpr_isReprInst [LemFuel] (n : Int) (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext file ρ (isReprInst n) = some Vtrue := by
  unfold isReprInst
  rw [evalPexpr_op, evalPexpr_op, evalPexpr_op, evalPexpr_ctor1, evalPexpr_ctor1, ointPe, sintTyPe,
    evalPexpr_val, evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [evalCtor_ivmin_int, evalCtor_ivmax_int]
  simp only [Option.bind_some]
  rw [show evalBinop OpLe (Vobject (OVinteger (CerbMem.minIval (.Signed .Int_)))) (oint n) =
      some (boolValue (decide (-2147483648 ≤ n))) from rfl,
    show evalBinop OpLe (oint n) (Vobject (OVinteger (CerbMem.maxIval (.Signed .Int_)))) =
      some (boolValue (decide (n ≤ 2147483647))) from rfl,
    boolValue_decide_true h1, boolValue_decide_true h2]
  rfl

/-- `is_representable_integer(n, 'signed int')` at a representable `n` is
    `True` (std.core:5–6 through `callBody`). -/
theorem evalPexpr_isRepr_int [LemFuel] (a : List annot) (hstd : StdE3 file)
    {pe1 pe2 : generic_pexpr Unit sym} {n : Int}
    (hv1 : evalPexpr tds ext file ρ pe1 = some (oint n))
    (hv2 : evalPexpr tds ext file ρ pe2 = some (Vctype sintTy))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext file ρ (Pexpr a () (PEcall (Sym isReprSym) [pe1, pe2])) = some Vtrue := by
  rw [evalPexpr_call, evalPexprList_cons, hv1, evalPexprList_cons, hv2, evalPexprList_nil]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callBody_isRepr hstd n]
  simp only [Option.bind_some]
  rw [peStrip_isReprInst, if_pos (by rw [peDepth_isReprInst, stdBudget_isRepr]; exact Nat.le_refl _)]
  exact evalPexpr_isReprInst n h1 h2

/-- The instantiated `conv_int` body at a representable `n`. -/
theorem evalPexpr_convIntInst [LemFuel] (hstd : StdE3 file) (n : Int)
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext file ρ (convIntInst n) = some (oint n) := by
  unfold convIntInst
  rw [evalPexpr_if, if_pos (isPePure_convIntBranches n), evalPexpr_op, sintTyPe, stdBoolTyPe,
    evalPexpr_val, evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalBinop OpEq (Vctype sintTy) (Vctype stdBoolTy) = some Vfalse from rfl]
  simp only [Option.bind_some]
  unfold convIntElse
  rw [evalPexpr_if, if_pos (show (isPePure (ointPe n) && isPePure (convIntElse2 n)) = true from rfl),
    evalPexpr_isRepr_int [] hstd (pe1 := ointPe n) (pe2 := sintTyPe)
      (by rw [ointPe, evalPexpr_val]) (by rw [sintTyPe, evalPexpr_val]) h1 h2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [ointPe, evalPexpr_val]

/-- `conv_int('signed int', n)` at a representable `n` is `n` (std.core:25–55:
    the `_Bool` test fails, `is_representable_integer` holds). -/
theorem evalPexpr_convInt_call_int [LemFuel] (a : List annot) (hstd : StdE3 file)
    {pe1 pe2 : generic_pexpr Unit sym} {n : Int}
    (hv1 : evalPexpr tds ext file ρ pe1 = some (Vctype sintTy))
    (hv2 : evalPexpr tds ext file ρ pe2 = some (oint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext file ρ (Pexpr a () (PEcall (Sym convIntSym) [pe1, pe2])) = some (oint n) := by
  rw [evalPexpr_call, evalPexprList_cons, hv1, evalPexprList_cons, hv2, evalPexprList_nil]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callBody_convInt hstd n]
  simp only [Option.bind_some]
  rw [peStrip_convIntInst, if_pos (by rw [peDepth_convIntInst, stdBudget_convInt]; exact Nat.le_refl _)]
  exact evalPexpr_convIntInst hstd n h1 h2

/-- `conv_loaded_int('signed int', Specified(n))` at a representable `n`
    is `Specified(n)` (std.core:61–67: the `Specified` alternative,
    `conv_int`). The operand is any covered expression evaluating to the
    loaded integer (t1's is a bound symbol). -/
theorem evalPexpr_convLoadedInt_spec [LemFuel] (a : List annot) (hstd : StdE3 file)
    {pe1 pe2 : generic_pexpr Unit sym} {n : Int}
    (hv1 : evalPexpr tds ext file ρ pe1 = some (Vctype sintTy))
    (hv2 : evalPexpr tds ext file ρ pe2 = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext file ρ (Pexpr a () (PEcall (Sym convLoadedIntSym) [pe1, pe2])) =
      some (lint n) := by
  rw [evalPexpr_call, evalPexprList_cons, hv1, evalPexprList_cons, hv2, evalPexprList_nil]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callBody_convLoadedInt hstd sintTy (lint n)]
  simp only [Option.bind_some]
  rw [peStrip_convLoadedIntInst, if_pos (by rw [peDepth_convLoadedIntInst, stdBudget_convLoadedInt]; exact Nat.le_refl _)]
  unfold convLoadedIntInst
  rw [evalPexpr_case, if_pos (isPePure_cliAlts sintTy), evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show select_case subst_sym_pexpr (lint n) (cliAlts (Pexpr [] () (PEval (Vctype sintTy)))) =
      some (Pexpr [] () (PEctor Cspecified
        [Pexpr [] () (PEcall (Sym convIntSym) [Pexpr [] () (PEval (Vctype sintTy)), ointPe n])]))
      from rfl]
  simp only [Option.bind_some]
  rw [if_pos (show peDepth (reannot0 (Pexpr [] () (PEctor Cspecified
      [Pexpr [] () (PEcall (Sym convIntSym) [Pexpr [] () (PEval (Vctype sintTy)), ointPe n])]))) ≤
      peDepthAlts (cliAlts (Pexpr [] () (PEval (Vctype sintTy)))) from Nat.le_of_eq rfl),
    evalPexpr_reannot0]
  rw [evalPexpr_ctor1, evalPexpr_convInt_call_int [] hstd
    (pe1 := Pexpr [] () (PEval (Vctype sintTy))) (pe2 := ointPe n)
    (evalPexpr_val _ _ _ _ _) (by rw [ointPe, evalPexpr_val]) h1 h2]
  rfl

/-- `conv_loaded_int(ty, Unspecified(ty'))` is `Unspecified(ty)` (std.core:
    65–66: the `Unspecified` alternative, no conversion) — at ANY ctype
    operand `ty` and any unspecified operand. -/
theorem evalPexpr_convLoadedInt_unspec [LemFuel] (a : List annot) (hstd : StdE3 file)
    {pe1 pe2 : generic_pexpr Unit sym} {ty ty' : ctype}
    (hv1 : evalPexpr tds ext file ρ pe1 = some (Vctype ty))
    (hv2 : evalPexpr tds ext file ρ pe2 = some (Vloaded (LVunspecified ty'))) :
    evalPexpr tds ext file ρ (Pexpr a () (PEcall (Sym convLoadedIntSym) [pe1, pe2])) =
      some (Vloaded (LVunspecified ty)) := by
  rw [evalPexpr_call, evalPexprList_cons, hv1, evalPexprList_cons, hv2, evalPexprList_nil]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callBody_convLoadedInt hstd ty (Vloaded (LVunspecified ty'))]
  simp only [Option.bind_some]
  rw [peStrip_convLoadedIntInst, if_pos (by rw [peDepth_convLoadedIntInst, stdBudget_convLoadedInt]; exact Nat.le_refl _)]
  unfold convLoadedIntInst
  rw [evalPexpr_case, if_pos (isPePure_cliAlts ty), evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show select_case subst_sym_pexpr (Vloaded (LVunspecified ty'))
      (cliAlts (Pexpr [] () (PEval (Vctype ty)))) =
      some (Pexpr [] () (PEctor Cunspecified [Pexpr [] () (PEval (Vctype ty))])) from rfl]
  simp only [Option.bind_some]
  rw [if_pos (by
    show peDepth (Pexpr [] () (PEctor Cunspecified [Pexpr [] () (PEval (Vctype ty))])) ≤ _
    rw [show peDepth (Pexpr [] () (PEctor Cunspecified [Pexpr [] () (PEval (Vctype ty))])) = 2
      from rfl]
    exact Nat.le_trans (by decide : 2 ≤ 2) (Nat.le_max_right _ _))]
  rw [evalPexpr_reannot0, evalPexpr_tyctor _ _ _ _ _ _ _ rfl]
  rfl

end Evaluator

/-! ## The emitted `x + y` (t1.core:17–23) -/

/-- The `case` alternatives of the emitted `+`: the `(Specified(a'),
    Specified(b'))` row computing `catch_exceptional_condition_add` of the
    two `__conv_int__`s, and the wildcard `undef(<<UB036>>)` arm. -/
def cAddPats (a' b' : sym) (loc : CerbLocation.Loc) : List (pattern × generic_pexpr Unit sym) :=
  [(Pattern [] (CaseCtor Ctuple
      [Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some a', BTy_object OTy_integer))]),
       Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some b', BTy_object OTy_integer))])]),
    Pexpr [] () (PEctor Cspecified [Pexpr [] () (PEcatch_exceptional_condition (.Signed .Int_) IOpAdd
      (Pexpr [] () (PEconv_int (.Signed .Int_) (stdSym a')))
      (Pexpr [] () (PEconv_int (.Signed .Int_) (stdSym b'))))])),
   (Pattern [] (CaseBase (none, BTy_tuple [BTy_loaded OTy_integer, BTy_loaded OTy_integer])),
    Pexpr [] () (PEundef loc UB036_exceptional_condition))]

/-- The emitted `+` at the loaded operands `a`, `b`. -/
def cAddPe (a b a' b' : sym) (loc : CerbLocation.Loc) : generic_pexpr Unit sym :=
  Pexpr [] () (PEcase (Pexpr [] () (PEctor Ctuple [stdSym a, stdSym b])) (cAddPats a' b' loc))

/-- The selected row with the two integers substituted (what `select_case
    subst_sym_pexpr` delivers at `(Specified(n1), Specified(n2))`; the
    client states this equation — `rfl` at concrete symbols — as
    `Frag.case_value` states its selected branch). -/
def cAddBranch (n1 n2 : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Cspecified [Pexpr [] () (PEcatch_exceptional_condition (.Signed .Int_) IOpAdd
    (Pexpr [] () (PEconv_int (.Signed .Int_) (ointPe n1)))
    (Pexpr [] () (PEconv_int (.Signed .Int_) (ointPe n2))))])

theorem isPePureAlts_cAddPats (a' b' : sym) (loc : CerbLocation.Loc) :
    isPePureAlts (cAddPats a' b' loc) = true := rfl
theorem peDepth_cAddPe (a b a' b' : sym) (loc : CerbLocation.Loc) : peDepth (cAddPe a b a' b' loc) = 8 := rfl
theorem peDepth_cAddBranch (n1 n2 : Int) : peDepth (cAddBranch n1 n2) = 4 := rfl
theorem peDepthAlts_cAddPats (a' b' : sym) (loc : CerbLocation.Loc) : peDepthAlts (cAddPats a' b' loc) = 4 := rfl

section CAdd
variable {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
  {file : generic_file Unit core_run_annotation} {ρ : EnvStack}

/-- The selected branch at an in-range sum: `Specified(n1 + n2)`. -/
theorem evalPexpr_cAddBranch [LemFuel] (n1 n2 : Int)
    (h1 : -2147483648 ≤ n1) (h1' : n1 ≤ 2147483647)
    (h2 : -2147483648 ≤ n2) (h2' : n2 ≤ 2147483647)
    (hs : -2147483648 ≤ n1 + n2) (hs' : n1 + n2 ≤ 2147483647) :
    evalPexpr tds ext file ρ (cAddBranch n1 n2) = some (lint (n1 + n2)) := by
  unfold cAddBranch
  rw [evalPexpr_ctor1, evalPexpr_catch_add_int [] (evalPexpr_conv_int_int [] (by rw [ointPe, evalPexpr_val]) h1 h1')
    (evalPexpr_conv_int_int [] (by rw [ointPe, evalPexpr_val]) h2 h2') hs hs']
  rfl

/-- THE EMITTED `+` (mirror evaluator): at operands bound to representable
    `int`s whose sum is representable, `Specified(n1 + n2)`. -/
theorem evalPexpr_cAdd [LemFuel] {a b a' b' : sym} {loc : CerbLocation.Loc} {n1 n2 : Int}
    (hv1 : evalPexpr tds ext file ρ (stdSym a) = some (lint n1))
    (hv2 : evalPexpr tds ext file ρ (stdSym b) = some (lint n2))
    (hsel : select_case subst_sym_pexpr (Vtuple [lint n1, lint n2]) (cAddPats a' b' loc) =
      some (cAddBranch n1 n2))
    (h1 : -2147483648 ≤ n1) (h1' : n1 ≤ 2147483647)
    (h2 : -2147483648 ≤ n2) (h2' : n2 ≤ 2147483647)
    (hs : -2147483648 ≤ n1 + n2) (hs' : n1 + n2 ≤ 2147483647) :
    evalPexpr tds ext file ρ (cAddPe a b a' b' loc) = some (lint (n1 + n2)) := by
  unfold cAddPe
  rw [evalPexpr_case, if_pos (isPePureAlts_cAddPats a' b' loc), evalPexpr_ctor2, hv1, hv2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalCtor tds Ctuple [lint n1, lint n2] = some (Vtuple [lint n1, lint n2]) from rfl]
  simp only [Option.bind_some]
  rw [hsel]
  simp only [Option.bind_some]
  rw [if_pos (show peDepth (reannot0 (cAddBranch n1 n2)) ≤ peDepthAlts (cAddPats a' b' loc) from
    by rw [peDepth_reannot0, peDepth_cAddBranch, peDepthAlts_cAddPats]; exact Nat.le_refl _),
    evalPexpr_reannot0]
  exact evalPexpr_cAddBranch n1 n2 h1 h1' h2 h2' hs hs'

/-! ### The OUT-OF-RANGE face: the classifier's UB036 undef -/

/-- The first pass on the emitted `+`: the scrutinee tuple evaluates and
    the `Specified` row is selected, UNEVALUATED. -/
theorem stepPexprRaw_cAdd [LemFuel] {a b a' b' : sym} {loc : CerbLocation.Loc} {n1 n2 : Int}
    (hv1 : evalPexpr tds ext file ρ (stdSym a) = some (lint n1))
    (hv2 : evalPexpr tds ext file ρ (stdSym b) = some (lint n2))
    (hsel : select_case subst_sym_pexpr (Vtuple [lint n1, lint n2]) (cAddPats a' b' loc) =
      some (cAddBranch n1 n2)) :
    stepPexprRaw tds ext file ρ (cAddPe a b a' b' loc) = some (reannot0 (cAddBranch n1 n2)) := by
  simp only [stdSym, evalPexpr_sym] at hv1 hv2
  unfold cAddPe stdSym
  rw [stepPexprRaw, stepPexprRaw, stepPexprsRaw_cons, stepPexprsRaw_cons, stepPexprsRaw_nil,
    stepPexprRaw, stepPexprRaw, hv1, hv2]
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, valueFromPexprs_cons,
    valueFromPexprs_nil, valueFromPexpr_valPe]
  rw [show evalCtor tds Ctuple [lint n1, lint n2] = some (Vtuple [lint n1, lint n2]) from rfl]
  simp only [Option.map_some, Option.bind_some, valueFromPexpr_valPe]
  rw [hsel]
  rfl

/-- The second pass, at an OVERFLOWING sum: the two conversions reach
    their values and the range check fails — the mirror's `none`. -/
theorem stepPexprRaw_cAddBranch_overflow [LemFuel] (n1 n2 : Int)
    (h1 : -2147483648 ≤ n1) (h1' : n1 ≤ 2147483647)
    (h2 : -2147483648 ≤ n2) (h2' : n2 ≤ 2147483647)
    (hov : n1 + n2 < -2147483648 ∨ 2147483647 < n1 + n2) :
    stepPexprRaw tds ext file ρ (cAddBranch n1 n2) = none := by
  unfold cAddBranch
  rw [stepPexprRaw, stepPexprsRaw_cons, stepPexprsRaw_nil, stepPexprRaw, stepPexprRaw, stepPexprRaw,
    ointPe, ointPe, stepPexprRaw, stepPexprRaw]
  simp only [Option.bind_eq_bind, Option.bind_some, valueFromPexpr_valPe]
  rw [evalConvInt_int n1 h1 h1', evalConvInt_int n2 h2 h2']
  simp only [Option.map_some, Option.bind_some, valueFromPexpr_valPe]
  rw [evalCatch_add_overflow n1 n2 hov]
  rfl

/-- … and the classifier names the reason: the engine's
    `undef loc [UB036_exceptional_condition]` at the thread's current
    location (core_eval.lem:847–848; `catchOut`). -/
theorem stepFail_cAddBranch_overflow [LemFuel] (loc : CerbLocation.Loc) (n1 n2 : Int)
    (h1 : -2147483648 ≤ n1) (h1' : n1 ≤ 2147483647)
    (h2 : -2147483648 ≤ n2) (h2' : n2 ≤ 2147483647)
    (hov : n1 + n2 < -2147483648 ∨ 2147483647 < n1 + n2) :
    stepFail tds loc ext file ρ (cAddBranch n1 n2) =
      StepFail.undef loc [UB036_exceptional_condition] := by
  unfold cAddBranch
  rw [stepFail_ctor, stepFailList_cons]
  have hcatch : stepPexprRaw tds ext file ρ
      (Pexpr [] () (PEcatch_exceptional_condition (.Signed .Int_) IOpAdd
        (Pexpr [] () (PEconv_int (.Signed .Int_) (ointPe n1)))
        (Pexpr [] () (PEconv_int (.Signed .Int_) (ointPe n2))))) = none := by
    rw [stepPexprRaw, stepPexprRaw, stepPexprRaw, ointPe, ointPe, stepPexprRaw, stepPexprRaw]
    simp only [Option.bind_eq_bind, Option.bind_some, valueFromPexpr_valPe]
    rw [evalConvInt_int n1 h1 h1', evalConvInt_int n2 h2 h2']
    simp only [Option.map_some, Option.bind_some, valueFromPexpr_valPe]
    rw [evalCatch_add_overflow n1 n2 hov]
    rfl
  rw [hcatch]
  dsimp only
  rw [stepFail_catch, stepPexprRaw, ointPe, stepPexprRaw]
  simp only [Option.bind_eq_bind, Option.bind_some, valueFromPexpr_valPe]
  rw [evalConvInt_int n1 h1 h1']
  simp only [Option.map_some]
  rw [stepPexprRaw, ointPe, stepPexprRaw]
  simp only [Option.bind_eq_bind, Option.bind_some, valueFromPexpr_valPe]
  rw [evalConvInt_int n2 h2 h2']
  simp only [Option.map_some, valueFromPexpr_valPe]
  unfold catchOut
  rw [evalCatch_add_overflow n1 n2 hov]
  dsimp only [oint]
  rw [stepPexprsRaw_nil]

/-- THE EMITTED `+` AT AN OVERFLOWING SUM (classifier): the outcome is the
    UB036 undef — through `complete_pure_op` (Round.lean) the shipped round
    is the kill `Undef0 loc [UB036_exceptional_condition]`; the mirror has
    no step (`evalPexpr_cAdd_overflow`). -/
theorem evalPexpr_cAdd_overflow [LemFuel] {a b a' b' : sym} {loc : CerbLocation.Loc} {n1 n2 : Int}
    (hv1 : evalPexpr tds ext file ρ (stdSym a) = some (lint n1))
    (hv2 : evalPexpr tds ext file ρ (stdSym b) = some (lint n2))
    (hsel : select_case subst_sym_pexpr (Vtuple [lint n1, lint n2]) (cAddPats a' b' loc) =
      some (cAddBranch n1 n2))
    (h1 : -2147483648 ≤ n1) (h1' : n1 ≤ 2147483647)
    (h2 : -2147483648 ≤ n2) (h2' : n2 ≤ 2147483647)
    (hov : n1 + n2 < -2147483648 ∨ 2147483647 < n1 + n2) :
    evalPexpr tds ext file ρ (cAddPe a b a' b' loc) = none := by
  unfold cAddPe
  rw [evalPexpr_case, if_pos (isPePureAlts_cAddPats a' b' loc), evalPexpr_ctor2, hv1, hv2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalCtor tds Ctuple [lint n1, lint n2] = some (Vtuple [lint n1, lint n2]) from rfl]
  simp only [Option.bind_some]
  rw [hsel]
  simp only [Option.bind_some]
  rw [if_pos (show peDepth (reannot0 (cAddBranch n1 n2)) ≤ peDepthAlts (cAddPats a' b' loc) from
    by rw [peDepth_reannot0, peDepth_cAddBranch, peDepthAlts_cAddPats]; exact Nat.le_refl _),
    evalPexpr_reannot0]
  unfold cAddBranch
  rw [evalPexpr_ctor1, evalPexpr_catch, evalPexpr_conv_int_int [] (by rw [ointPe, evalPexpr_val]) h1 h1',
    evalPexpr_conv_int_int [] (by rw [ointPe, evalPexpr_val]) h2 h2']
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [evalCatch_add_overflow n1 n2 hov]
  rfl

theorem evalClass_cAdd_overflow [LemFuel] (loc : CerbLocation.Loc) {a b a' b' : sym}
    {uloc : CerbLocation.Loc} {n1 n2 : Int}
    (hv1 : evalPexpr tds ext file ρ (stdSym a) = some (lint n1))
    (hv2 : evalPexpr tds ext file ρ (stdSym b) = some (lint n2))
    (hsel : select_case subst_sym_pexpr (Vtuple [lint n1, lint n2]) (cAddPats a' b' uloc) =
      some (cAddBranch n1 n2))
    (h1 : -2147483648 ≤ n1) (h1' : n1 ≤ 2147483647)
    (h2 : -2147483648 ≤ n2) (h2' : n2 ≤ 2147483647)
    (hov : n1 + n2 < -2147483648 ∨ 2147483647 < n1 + n2) :
    evalClass tds loc ext file ρ (cAddPe a b a' b' uloc) =
      EvalOut.undef loc [UB036_exceptional_condition] := by
  unfold evalClass
  rw [evalPexpr_cAdd_overflow hv1 hv2 hsel h1 h1' h2 h2' hov]
  dsimp only
  rw [peDepth_cAddPe]
  -- pass 1: the row is selected
  rw [classIter, show peStrip (cAddPe a b a' b' uloc) = cAddPe a b a' b' uloc from rfl]
  unfold stepClass
  rw [stepPexprRaw_cAdd hv1 hv2 hsel]
  dsimp only
  rw [show valueFromPexpr (reannot0 (cAddBranch n1 n2)) = none from rfl]
  dsimp only
  rw [if_pos (show (isPePure (reannot0 (cAddBranch n1 n2)) &&
      decide (peDepth (reannot0 (cAddBranch n1 n2)) < peDepth (cAddPe a b a' b' uloc))) = true from
      by rw [peDepth_cAddPe]; rfl)]
  -- pass 2: the conversions reach their values, the range check fails
  rw [classIter, show peStrip (reannot0 (cAddBranch n1 n2)) = cAddBranch n1 n2 from rfl]
  unfold stepClass
  rw [stepPexprRaw_cAddBranch_overflow n1 n2 h1 h1' h2 h2' hov]
  dsimp only
  rw [stepFail_cAddBranch_overflow loc n1 n2 h1 h1' h2 h2' hov]
  rfl

end CAdd

/-! ## The rules at both strata -/

section Rules
variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {p : Option sym}

/-- THE C `+` ON `int`, partial stratum (Reynolds/O'Hearn shape: pure
    premises — the two operands are bound to representable `int`s whose
    sum is representable — and the postcondition at `Specified(n1 + n2)`;
    the UB036 kill is EXCLUDED by the range obligation). -/
theorem wps_c_add [LemFuel] {Ls : LabelSpec GF} {Θ : ProcSpec GF} {Ψ : SpikeVal → EnvStack → IProp GF}
    (a b a' b' : sym) (loc : CerbLocation.Loc) (ρ : EnvStack) {n1 n2 : Int}
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ (stdSym a) = some (lint n1))
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ (stdSym b) = some (lint n2))
    (hsel : select_case subst_sym_pexpr (Vtuple [lint n1, lint n2]) (cAddPats a' b' loc) =
      some (cAddBranch n1 n2))
    (h1 : -2147483648 ≤ n1) (h1' : n1 ≤ 2147483647)
    (h2 : -2147483648 ≤ n2) (h2' : n2 ≤ 2147483647)
    (hs : -2147483648 ≤ n1 + n2) (hs' : n1 + n2 ≤ 2147483647) :
    Ψ (.pure (lint (n1 + n2))) ρ ⊢
      wps M p Ls Θ Ψ (Expr ([] : List annot) (Epure (cAddPe a b a' b' loc))) ρ :=
  wps_pure _ _ rfl (evalPexpr_cAdd hv1 hv2 hsel h1 h1' h2 h2' hs hs')

/-- THE C `+` ON `int`, total stratum (one evaluation tau then the
    delivery, `2 ≤ k`). -/
theorem wpt_c_add [LemFuel] {Ls : LabelSpecT GF} {Θ : ProcSpecT GF} {Ψ : SpikeVal → EnvStack → IProp GF}
    (a b a' b' : sym) (loc : CerbLocation.Loc) (ρ : EnvStack) {n1 n2 : Int} {k : Nat}
    (hk : 2 ≤ k)
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ (stdSym a) = some (lint n1))
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ (stdSym b) = some (lint n2))
    (hsel : select_case subst_sym_pexpr (Vtuple [lint n1, lint n2]) (cAddPats a' b' loc) =
      some (cAddBranch n1 n2))
    (h1 : -2147483648 ≤ n1) (h1' : n1 ≤ 2147483647)
    (h2 : -2147483648 ≤ n2) (h2' : n2 ≤ 2147483647)
    (hs : -2147483648 ≤ n1 + n2) (hs' : n1 + n2 ≤ 2147483647) :
    Ψ (.pure (lint (n1 + n2))) ρ ⊢
      wpt M p Ls Θ k Ψ (Expr ([] : List annot) (Epure (cAddPe a b a' b' loc))) ρ :=
  wpt_pure _ _ hk rfl (evalPexpr_cAdd hv1 hv2 hsel h1 h1' h2 h2' hs hs')

/-- THE C CONVERSION `conv_loaded_int('signed int', e)` at a representable
    loaded `int`, partial stratum: the value is unchanged. -/
theorem wps_conv_loaded_int [LemFuel] {Ls : LabelSpec GF} {Θ : ProcSpec GF} {Ψ : SpikeVal → EnvStack → IProp GF}
    (pe1 pe2 : generic_pexpr Unit sym) (ρ : EnvStack) {n : Int}
    (hstd : StdE3 M.file)
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vctype sintTy))
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    Ψ (.pure (lint n)) ρ ⊢
      wps M p Ls Θ Ψ (Expr ([] : List annot) (Epure (Pexpr [] () (PEcall (Sym convLoadedIntSym) [pe1, pe2])))) ρ :=
  wps_pure _ _ rfl (evalPexpr_convLoadedInt_spec [] hstd hv1 hv2 h1 h2)

/-- … total stratum. -/
theorem wpt_conv_loaded_int [LemFuel] {Ls : LabelSpecT GF} {Θ : ProcSpecT GF} {Ψ : SpikeVal → EnvStack → IProp GF}
    (pe1 pe2 : generic_pexpr Unit sym) (ρ : EnvStack) {n : Int} {k : Nat} (hk : 2 ≤ k)
    (hstd : StdE3 M.file)
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vctype sintTy))
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    Ψ (.pure (lint n)) ρ ⊢
      wpt M p Ls Θ k Ψ (Expr ([] : List annot) (Epure (Pexpr [] () (PEcall (Sym convLoadedIntSym) [pe1, pe2])))) ρ :=
  wpt_pure _ _ hk rfl (evalPexpr_convLoadedInt_spec [] hstd hv1 hv2 h1 h2)

end Rules

end CerberusHeapLang
