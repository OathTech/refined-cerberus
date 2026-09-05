/-
CerberusHeapLang.EvalClass — THE ENGINE'S PURE-EVALUATOR OUTCOME ON THE
COVERED OPERAND GRAMMAR, CLASSIFIED.

The mirror evaluator `evalPexpr` (Step.lean) is partial and fail-closed:
on the covered grammar `PePure` it answers `some v` exactly where the
engine's evaluator tower (`step_eval_pexpr` → `eval_pexpr_aux2` →
`full_eval_pexpr`, Core_eval.lean:135-158 / Core_reduction.lean:84-100)
returns `v` (the SUCCESS bridge, Soundness.lean). This module names what
the engine does where the mirror answers `none`:

- `EvalOut.kill err` — the engine RAISES `err : core_run_cause`
  (`exception_undef_fail`): an unbound symbol that names no procedure
  (`Unresolved_symbol loc x`, Core_eval.lean:145 PEsym arm), a binop at
  operands of mismatched kinds (`Illformed_program "[loc] ill-typed PEop
  ==> …"`, step_eval_peop's `_, some _, some _` arm, Core_eval.lean:135),
  an array shift at a non-(pointer, integer) pair (`Illformed_program
  "PEarray_shift: type error ==> …"`), `not` / `if` at a non-boolean
  operand (E2). The shipped driver turns the exception into the kill
  `Other (DErr_core_run err)` (`liftCore_run`, Driver.lean:245) — a
  `ShippedRefusal.killed` (Round.lean).
- `EvalOut.undef loc ubs` (E2) — the engine's `undef(UB)` outcome
  (`PEundef`, Core_eval.lean:145: `except_return (undef loc' [ub])`, the
  location resolved against the thread's current location for library
  locations), propagated through the evaluator's binds; the shipped
  driver turns it into the kill `Undef0 loc ubs` (`liftCore_run`). The
  mirror's `undef(UB…)` arm is this FAIL-CLOSED KILL, never a default.
- `EvalOut.uncovered` — the engine SUCCEEDS with a value the mirror does
  not compute, or the outcome is not characterized here: a symbol unbound
  in the environment but naming a `Proc` of the file (the engine returns
  the null function pointer); the eight mirrored binops at two floating
  operands (`opFval`, the float comparisons); `OpEq` at two ctypes
  (`ctypeEqual`); the six non-mirrored binops (`Div`/`Rem_t`/`Rem_f`/
  `Exp` — integer successes; `And`/`Or` — the boolean arms), which
  `PePure` excludes syntactically; a `case` whose value matches no
  pattern (the engine's `failwithI` PANIC, opaque); a constructor
  dispatch failure; `UB088_reached_end_of_function` (its location is the
  call-location parameter); a constructor operand list whose first
  failing operand is an undef followed by another failure (the engine's
  `except_sequence` collects undefs and raises the first exception —
  Exception-first — so the outcome is not decided by the first failure).
  `.uncovered` carries NO engine claim: a compound operand with an
  accepted-but-unmirrored leaf is `.uncovered` whatever the engine then
  does with that leaf's value.

E2 STRUCTURE. The engine evaluates in PASSES (`eval_pexpr_aux2`
iterates {pull, `step_eval_pexpr`, value test} until a value — `case`
returns the selected branch unevaluated, so a kill in a branch surfaces
in a LATER pass). The classifier mirrors that: `stepClass` is the one
pass — `stepPexprRaw`'s result where the pass succeeds (`.next r`), and
`stepFail`'s classification of WHY it did not otherwise; `classIter`
iterates it as the engine does (strip, pass, value test, recurse) with
the mirror evaluator's own depth guard; `evalClass` is the mirror
evaluator's value where it has one and `classIter`'s verdict otherwise.

`evalClass` is a CLASSIFICATION VOCABULARY like `PePure`: it is not a
mirror rule, and it appears in no `Step`. Its `.val` face is the mirror
evaluator (`evalClass_val_iff`); its `.kill`/`.undef` faces are certified
against the engine level by level (`step_eval_bridge_kill`/`_undef`,
`aux2_bridge_fail`, `full_eval_bridge_fail`, `eval1_bridge_fail`) in the
same shape as the success bridge; its `.uncovered` face carries no engine
claim. The two failing faces share one currency, `EvalFail` — the
computation the engine's state-threaded monad delivers (`EvalFail.run`):
a RAISE (state irrelevant) or an UNDEF (state untouched).

OPERAND LISTS. Two list shapes, because the engine's two folds disagree
at an undef followed by a raise: `stExceptUndef_mapM` (Ememop/Esave/Eproc
operands) COLLECTS undefs at the exceptM layer and raises the first
exception in list order (`except_sequence`/`sequence0`) — `evalClassList`;
`stExceptUndef_foldM` (Erun arguments) propagates the first failure —
`evalClassFold`.
-/
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-- The engine's outcome on one operand (module header). -/
inductive EvalOut : Type where
  | val (v : value)
  | kill (err : core_run_cause)
  | undef (loc : CerbLocation.Loc) (ubs : List undefined_behaviour)
  | uncovered

/-- The engine's outcome on ONE PASS (`step_eval_pexpr`): the pass's
    result term (a value or the rebuilt/selected term), a raise, an
    undef, or not characterized. -/
inductive StepOut : Type where
  | next (r : generic_pexpr Unit sym)
  | kill (err : core_run_cause)
  | undef (loc : CerbLocation.Loc) (ubs : List undefined_behaviour)
  | uncovered

/-- A FAILING outcome — the currency the two failing faces share. -/
inductive EvalFail : Type where
  | kill (err : core_run_cause)
  | undef (loc : CerbLocation.Loc) (ubs : List undefined_behaviour)

/-- The failing outcome in the pure exception-undef monad
    (`exceptM (t0 α) core_run_cause`, the evaluator's own). -/
def EvalFail.pure (α : Type) : EvalFail → exceptM (t0 α) core_run_cause
  | .kill err => Exception err
  | .undef l u => Result (Undef l u)

/-- The failing outcome in the state-threaded monad (`stExceptUndef`,
    the driver-facing layer): a raise ignores the state, an undef leaves
    it untouched. -/
def EvalFail.run (α σ : Type) : EvalFail → σ → exceptM (t0 α × σ) core_run_cause
  | .kill err => fun _ => Exception err
  | .undef l u => fun st => Result (Undef l u, st)

def StepOut.fail? : StepOut → Option EvalFail
  | .kill err => some (.kill err)
  | .undef l u => some (.undef l u)
  | _ => none

/-- A FAILED pass classified (no result term): a raise, an undef, or not
    characterized. -/
inductive StepFail : Type where
  | kill (err : core_run_cause)
  | undef (loc : CerbLocation.Loc) (ubs : List undefined_behaviour)
  | uncovered

def StepFail.fail? : StepFail → Option EvalFail
  | .kill err => some (.kill err)
  | .undef l u => some (.undef l u)
  | .uncovered => none

def StepFail.lift : StepFail → StepOut
  | .kill err => .kill err
  | .undef l u => .undef l u
  | .uncovered => .uncovered

theorem StepFail.lift_fail? (o : StepFail) : o.lift.fail? = o.fail? := by
  cases o <;> rfl

def EvalOut.fail? : EvalOut → Option EvalFail
  | .kill err => some (.kill err)
  | .undef l u => some (.undef l u)
  | _ => none

/-! ### The failing outcome through the engine's monads -/

theorem exception_undef_bind_fail {α β : Type} (fl : EvalFail)
    (f : α → exceptM (t0 β) core_run_cause) :
    exception_undef_bind (fl.pure α) f = fl.pure β := by
  cases fl <;> rfl

theorem exception_undef_fmap_fail {α β : Type} (g : α → β) (fl : EvalFail) :
    exception_undef_fmap g (fl.pure α) = fl.pure β := by
  cases fl <;> rfl

theorem runEU_fail {α σ : Type} (fl : EvalFail) :
    runEU (s := σ) (fl.pure α) = fl.run α σ := by
  cases fl <;> (funext st; rfl)

theorem stExceptUndef_bind_fail_apply {α β σ : Type} {fl : EvalFail}
    {m : σ → exceptM (t0 α × σ) core_run_cause}
    (k : α → σ → exceptM (t0 β × σ) core_run_cause) {st : σ}
    (hm : m st = fl.run α σ st) :
    stExceptUndef_bind m k st = fl.run β σ st := by
  rw [stExceptUndef_bind_apply, hm]
  cases fl <;> rfl

/-! ### The classified messages -/

/-- step_eval_peop's ill-typed-operands exception (Core_eval.lean:135,
    the `_, some _, some _` arm), at the operands as the pass received
    them (post-pull: `peStrip`ped). -/
def illtypedPEop (loc : CerbLocation.Loc) (op : binop)
    (pe1 pe2 : generic_pexpr Unit sym) : core_run_cause :=
  Illformed_program (String.append "["
    (String.append (CerbLocation.stringFromLocation loc)
      (String.append "] ill-typed PEop ==> "
        (CerbPP.stringFromCore_pexpr (mk_op_pe op pe1 pe2)))))

/-- step_eval_pexpr's array-shift type error (Core_eval.lean:145, the
    `some _, some _` arm of the `PEarray_shift` case), at the evaluated
    operands. -/
def illtypedArrayShift (v1 : value) (ty : ctype) (v2 : value) : core_run_cause :=
  Illformed_program (String.append "PEarray_shift: type error ==> "
    (CerbPP.stringFromCore_pexpr ((Pexpr [] () (PEarray_shift
      (Pexpr [] () (PEval v1)) ty (Pexpr [] () (PEval v2)))) : generic_pexpr Unit sym)))

/-- E2: `PEnot` at a non-boolean value (Core_eval.lean:145, the `PEval _`
    arm of the `PEnot` case). -/
def illtypedPEnot : core_run_cause :=
  Illformed_program "PEnot: operand should be a boolean"

/-- E2: `PEif` at a non-boolean guard value (Core_eval.lean:145, the
    `some cval` arm of the `PEif` case). -/
def illtypedPEif (cval : value) : core_run_cause :=
  Illformed_program (String.append "PEif: first operand should be a boolean ==> "
    (CerbPP.stringFromCore_value cval))

/-- `/\` at a non-boolean operand (core_eval.lem:498–499). -/
def illtypedAnd (loc : CerbLocation.Loc) (v1 v2 : value) : core_run_cause :=
  Illformed_program (String.append "["
    (String.append (CerbLocation.stringFromLocation loc)
      (String.append "] the two operands of /\\ should be booleans ==> "
        (String.append (CerbPP.stringFromCore_value v1)
          (String.append " <-> " (CerbPP.stringFromCore_value v2))))))

/-- `\/` at a non-boolean operand (core_eval.lem:512–513). -/
def illtypedOr (loc : CerbLocation.Loc) : core_run_cause :=
  Illformed_program (String.append "["
    (String.append (CerbLocation.stringFromLocation loc)
      "] the two operands of \\/ should be booleans"))

/-- The binop dispatch's FAILURES classified (step_eval_peop's value
    match, Core_eval.lean:135; consulted only where the mirror's
    `evalBinop` answers `none`): two integers — the engine's success
    outside the mirror (a non-mirrored op, or a symbolic comparison's
    `PEconstrained`); two floats — an engine success outside the mirror;
    two ctypes — a success at `OpEq`; `And`/`Or` — not characterized
    (outside `PePure`); everything else — the ill-typed-`PEop`
    exception. -/
def binopOut (loc : CerbLocation.Loc) (op : binop) (pe1 pe2 : generic_pexpr Unit sym)
    (v1 v2 : value) : StepFail :=
  match op, v1, v2 with
  | _, Vobject (OVinteger _), Vobject (OVinteger _) => StepFail.uncovered
  | _, Vobject (OVfloating _), Vobject (OVfloating _) => StepFail.uncovered
  | .OpEq, Vctype _, Vctype _ => StepFail.uncovered
  -- E3: the connectives — booleans are the mirror's successes; anything
  -- else is the engine's kill (core_eval.lem:454–514)
  | .OpAnd, Vtrue, Vtrue => StepFail.uncovered
  | .OpAnd, Vtrue, Vfalse => StepFail.uncovered
  | .OpAnd, Vfalse, Vtrue => StepFail.uncovered
  | .OpAnd, Vfalse, Vfalse => StepFail.uncovered
  | .OpAnd, v1, v2 => StepFail.kill (illtypedAnd loc v1 v2)
  | .OpOr, Vtrue, Vtrue => StepFail.uncovered
  | .OpOr, Vtrue, Vfalse => StepFail.uncovered
  | .OpOr, Vfalse, Vtrue => StepFail.uncovered
  | .OpOr, Vfalse, Vfalse => StepFail.uncovered
  | .OpOr, _, _ => StepFail.kill (illtypedOr loc)
  | op, _, _ => StepFail.kill (illtypedPEop loc op pe1 pe2)

/-- The array-shift dispatch's FAILURE: anything but (pointer, integer)
    is the type error. -/
def shiftOut (tds : CerbTags.TagDefsMap) (ty : ctype) (v1 v2 : value) : StepFail :=
  match evalArrayShift tds ty v1 v2 with
  | some _ => StepFail.uncovered
  | none => StepFail.kill (illtypedArrayShift v1 ty v2)

/-- E2: the `PEundef` arm's location resolution (Core_eval.lean:145):
    `UB088_reached_end_of_function` reads the call-location parameter
    (not characterized); every other UB is located at the undef's own
    location unless that is a library location, in which case at the
    thread's current location. -/
def undefOut (loc undef_loc : CerbLocation.Loc) (ub : undefined_behaviour) : StepFail :=
  match ub with
  | .UB088_reached_end_of_function => StepFail.uncovered
  | ub => StepFail.undef (if CerbLocation.isLibraryLocation undef_loc then loc else undef_loc) [ub]

/-! ### E3: the impl arithmetic constructors, `is_unsigned`, the boolean
connectives and the standard-library call — their failing faces -/

/-- `PEconv_int` at a non-integer value (core_eval.lem:823–824). -/
def illtypedConvInt : core_run_cause :=
  Illformed_program "PEconv_int: operand should be an object integer"

/-- `PEwrapI` at non-integer values (core_eval.lem:834–835). -/
def illtypedWrapI : core_run_cause :=
  Illformed_program "PEwrapI: operands should be an object integers"

/-- `PEcatch_exceptional_condition` at non-integer values (core_eval.lem:850–851). -/
def illtypedCatch : core_run_cause :=
  Illformed_program "PEcatch_exceptional_condition: operands should be an object integers"

/-- `PEis_unsigned` at a non-ctype value (core_eval.lem:1083–1084). -/
def illtypedIsUnsigned : core_run_cause :=
  Illformed_program "PEis_unsigned: the operand should be a ctype"

/-- `call_function`'s unknown-callee kills (core_eval.lem:136, :144–145). -/
def unknownFunction : core_run_cause := Illformed_program "calling an unknown function"
def unknownImpl (c : implementation_constant) : core_run_cause :=
  Illformed_program (String.append "calling an unknown impl-function: "
    (string_of_implementation_constant c))

/-- The `__conv_int__` dispatch's FAILURE: anything but an object integer
    is the type error. -/
def convIntOut (ity : integerType) (v : value) : StepFail :=
  match evalConvInt ity v with
  | some _ => StepFail.uncovered
  | none => StepFail.kill illtypedConvInt

/-- The `wrapI_<op>` dispatch's failure. -/
def wrapIOut (ity : integerType) (op : iop) (v1 v2 : value) : StepFail :=
  match evalWrapI ity op v1 v2 with
  | some _ => StepFail.uncovered
  | none => StepFail.kill illtypedWrapI

/-- The `catch_exceptional_condition_<op>` dispatch's failures: at two object
    integers the mirror's `none` IS the engine's out-of-range
    `undef loc [UB036_exceptional_condition]` (core_eval.lem:847–848, at the
    thread's current location `loc`); at any other value pair the type
    error. -/
def catchOut (loc : CerbLocation.Loc) (ity : integerType) (op : iop) (v1 v2 : value) : StepFail :=
  match evalCatch ity op v1 v2 with
  | some _ => StepFail.uncovered
  | none =>
    match v1, v2 with
    | Vobject (OVinteger _), Vobject (OVinteger _) =>
        StepFail.undef loc [UB036_exceptional_condition]
    | _, _ => StepFail.kill illtypedCatch

/-- The `is_unsigned` dispatch's failure. -/
def isUnsignedOut (v : value) : StepFail :=
  match evalIsUnsigned v with
  | some _ => StepFail.uncovered
  | none => StepFail.kill illtypedIsUnsigned

/-- The CALL's failure where the mirror finds no body (`callBody = none`,
    Step.lean): an unknown callee is `call_function`'s `Illformed_program`
    kill (core_eval.lem:136; :143–145 for an `Impl` name — also at a `Def`
    constant); a callee found with the wrong arity, or a declaration that
    is not a `Fun`/`IFun`, is the engine's `failwithI` PANIC (:149–162),
    not characterized. -/
def callOut (file : generic_file Unit core_run_annotation) : generic_name sym → StepFail
  | Sym f =>
    match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
        f file.stdlib with
    | some _ => StepFail.uncovered
    | none =>
      match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
          f file.funs with
      | some _ => StepFail.uncovered
      | none => StepFail.kill unknownFunction
  | Impl c =>
    match fmapLookupBy implementation_constant_compare c file.impl0 with
    | some (IFun _ _ _) => StepFail.uncovered
    | _ => StepFail.kill (unknownImpl c)

/-! ### The one pass, classified -/

/-! `stepFail`: WHY one pass (`step_eval_pexpr`) does not deliver a
result term on a covered operand (consulted only where `stepPexprRaw`
answers `none`): the first failing child in the engine's evaluation
order, then the node's own dispatch. Arms the pass cannot reach (a
value, a child pass that succeeded where the parent's did not, …) are
`.uncovered` — fail-closed, no claim. `stepFailList`: the constructor
operand list (`exception_undef_mapM`) — the first operand whose pass
fails decides when it RAISES (the fold stops) or when it is an UNDEF and
every later operand's pass succeeds (the collected undef is the list's);
otherwise not characterized. -/
mutual
def stepFail (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    generic_pexpr Unit sym → StepFail
  | Pexpr _ _ (PEsym x) =>
      match lookup_env (resolveExtern ext x) ρ with
      | some _ => StepFail.uncovered
      | none =>
        match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
            (resolveExtern ext x) file.funs with
        | some (Proc _ _ _ _ _) => StepFail.uncovered
        | _ => StepFail.kill (Unresolved_symbol loc (resolveExtern ext x))
  | Pexpr _ _ (PEundef uloc ub) => undefOut loc uloc ub
  | Pexpr _ _ (PEop op pe1 pe2) =>
      match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match stepPexprRaw tds ext file ρ pe2 with
        | none => stepFail tds loc ext file ρ pe2
        | some r2 =>
          match valueFromPexpr r1, valueFromPexpr r2 with
          | some v1, some v2 => binopOut loc op pe1 pe2 v1 v2
          | _, _ => StepFail.uncovered
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) =>
      match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match stepPexprRaw tds ext file ρ pe2 with
        | none => stepFail tds loc ext file ρ pe2
        | some r2 =>
          match valueFromPexpr r1, valueFromPexpr r2 with
          | some v1, some v2 => shiftOut tds ty v1 v2
          | _, _ => StepFail.uncovered
  | Pexpr _ _ (PEctor _ pes) => stepFailList tds loc ext file ρ pes
  | Pexpr _ _ (PEcase pe _) =>
      match stepPexprRaw tds ext file ρ pe with
      | none => stepFail tds loc ext file ρ pe
      | some _ => StepFail.uncovered
  | Pexpr _ _ (PEnot pe) =>
      match stepPexprRaw tds ext file ρ pe with
      | none => stepFail tds loc ext file ρ pe
      | some r =>
        match valueFromPexpr r with
        | some Vtrue => StepFail.uncovered
        | some Vfalse => StepFail.uncovered
        | some _ => StepFail.kill illtypedPEnot
        | none => StepFail.uncovered
  | Pexpr _ _ (PEif pe1 pe2 pe3) =>
      match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match valueFromPexpr r1 with
        | some Vtrue =>
          match stepPexprRaw tds ext file ρ pe2 with
          | none => stepFail tds loc ext file ρ pe2
          | some _ => StepFail.uncovered
        | some Vfalse =>
          match stepPexprRaw tds ext file ρ pe3 with
          | none => stepFail tds loc ext file ρ pe3
          | some _ => StepFail.uncovered
        | some cval => StepFail.kill (illtypedPEif cval)
        | none => StepFail.uncovered
  -- E3
  | Pexpr _ _ (PEconv_int ity pe) =>
      match stepPexprRaw tds ext file ρ pe with
      | none => stepFail tds loc ext file ρ pe
      | some r =>
        match valueFromPexpr r with
        | some v => convIntOut ity v
        | none => StepFail.uncovered
  | Pexpr _ _ (PEwrapI ity op pe1 pe2) =>
      match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match stepPexprRaw tds ext file ρ pe2 with
        | none => stepFail tds loc ext file ρ pe2
        | some r2 =>
          match valueFromPexpr r1, valueFromPexpr r2 with
          | some v1, some v2 => wrapIOut ity op v1 v2
          | _, _ => StepFail.uncovered
  | Pexpr _ _ (PEcatch_exceptional_condition ity op pe1 pe2) =>
      match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match stepPexprRaw tds ext file ρ pe2 with
        | none => stepFail tds loc ext file ρ pe2
        | some r2 =>
          match valueFromPexpr r1, valueFromPexpr r2 with
          | some v1, some v2 => catchOut loc ity op v1 v2
          | _, _ => StepFail.uncovered
  | Pexpr _ _ (PEis_unsigned pe) =>
      match stepPexprRaw tds ext file ρ pe with
      | none => stepFail tds loc ext file ρ pe
      | some r =>
        match valueFromPexpr r with
        | some v => isUnsignedOut v
        | none => StepFail.uncovered
  | Pexpr _ _ (PEcall nm pes) =>
      match stepPexprsRaw tds ext file ρ pes with
      | none => stepFailList tds loc ext file ρ pes
      | some rs =>
        match valueFromPexprs rs with
        | none => StepFail.uncovered
        | some vs =>
          match callBody file nm vs with
          | some _ => StepFail.uncovered
          | none => callOut file nm
  | _ => StepFail.uncovered
def stepFailList (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → StepFail
  | [] => StepFail.uncovered
  | pe :: pes =>
      match stepPexprRaw tds ext file ρ pe with
      | some _ => stepFailList tds loc ext file ρ pes
      | none =>
        match stepFail tds loc ext file ρ pe with
        | .kill e => StepFail.kill e
        | .undef l u =>
          match stepPexprsRaw tds ext file ρ pes with
          | some _ => StepFail.undef l u
          | none => StepFail.uncovered
        | _ => StepFail.uncovered
end

/-- ONE PASS classified: the mirror's pass where it succeeds, the failure
    classification otherwise. -/
def stepClass (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) : StepOut :=
  match stepPexprRaw tds ext file ρ pe with
  | some r => StepOut.next r
  | none => (stepFail tds loc ext file ρ pe).lift

/-- The engine's iteration (`eval_pexpr_aux2`, Core_eval.lean:152) on the
    classifier: strip (the engine's `pull_constrained` on the covered
    grammar), one pass, the value test, recurse on the result — under the
    mirror evaluator's guards (covered grammar, strictly decreasing
    depth; a result outside them is not characterized). A pass that
    reaches a value is not characterized here either: `evalClass`
    consults `classIter` only where the mirror evaluator answers `none`,
    and then no pass reaches a value that the mirror missed except past
    the `case` depth guard (`evalPexpr_case`). -/
def classIter (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    Nat → generic_pexpr Unit sym → EvalOut
  | 0, _ => EvalOut.uncovered
  | n + 1, pe =>
    match stepClass tds loc ext file ρ (peStrip pe) with
    | .kill err => EvalOut.kill err
    | .undef l u => EvalOut.undef l u
    | .uncovered => EvalOut.uncovered
    | .next r =>
      match valueFromPexpr r with
      | some _ => EvalOut.uncovered
      | none =>
        if isPePure r && decide (peDepth r < peDepth pe) then
          classIter tds loc ext file ρ n r
        else EvalOut.uncovered

/-- THE CLASSIFIER (module header). Parameters: the tag environment, the
    thread's current location (the engine's `loc1`), the extern map, the
    file (its `funs` decide the procedure-pointer arm) and the
    environment stack. -/
def evalClass (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) : EvalOut :=
  match evalPexpr tds ext file ρ pe with
  | some v => EvalOut.val v
  | none => classIter tds loc ext file ρ (peDepth pe) pe

/-! ## The `.val` face is the mirror evaluator -/

theorem classIter_ne_val (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc)
    (ext : Fmap sym sym) (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    ∀ (n : Nat) (pe : generic_pexpr Unit sym) (v : value),
      classIter tds loc ext file ρ n pe ≠ EvalOut.val v := by
  intro n
  induction n with
  | zero => intro pe v h; cases h
  | succ n ih =>
    intro pe v h
    unfold classIter at h
    revert h
    cases stepClass tds loc ext file ρ (peStrip pe) with
    | next r =>
      dsimp only
      cases valueFromPexpr r with
      | some _ => intro h; cases h
      | none =>
        dsimp only
        split
        · exact ih r v
        · intro h; cases h
    | kill err => intro h; cases h
    | undef l u => intro h; cases h
    | uncovered => intro h; cases h

/-- `evalClass` answers `.val v` exactly where the mirror evaluator
    answers `some v` (at every location and file). -/
theorem evalClass_val_iff (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc)
    (ext : Fmap sym sym) (file : generic_file Unit core_run_annotation) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) (v : value) :
    evalClass tds loc ext file ρ pe = .val v ↔ evalPexpr tds ext file ρ pe = some v := by
  unfold evalClass
  cases h : evalPexpr tds ext file ρ pe with
  | some w =>
    constructor
    · intro h'; cases h'; rfl
    · intro h'; cases h'; rfl
  | none =>
    constructor
    · intro h'; exact absurd h' (classIter_ne_val _ _ _ _ _ _ _ _)
    · intro h'; cases h'

/-- Where the mirror answers `none`, the classifier answers a kill, an
    undef, or the residual. -/
theorem evalClass_of_none {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} (loc : CerbLocation.Loc)
    (file : generic_file Unit core_run_annotation)
    (h : evalPexpr tds ext file ρ pe = none) :
    (∃ fl, (evalClass tds loc ext file ρ pe).fail? = some fl) ∨
    evalClass tds loc ext file ρ pe = .uncovered := by
  cases hc : evalClass tds loc ext file ρ pe with
  | val v => rw [(evalClass_val_iff tds loc ext file ρ pe v).mp hc] at h; cases h
  | kill err => exact .inl ⟨_, rfl⟩
  | undef l u => exact .inl ⟨_, rfl⟩
  | uncovered => exact .inr rfl

theorem evalPexpr_none_of_fail {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation} {fl : EvalFail}
    (h : (evalClass tds loc ext file ρ pe).fail? = some fl) :
    evalPexpr tds ext file ρ pe = none := by
  cases hv : evalPexpr tds ext file ρ pe with
  | none => rfl
  | some v => rw [← evalClass_val_iff tds loc ext file ρ pe v] at hv; rw [hv] at h; cases h

theorem evalPexpr_none_of_kill {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation} {err : core_run_cause}
    (h : evalClass tds loc ext file ρ pe = .kill err) :
    evalPexpr tds ext file ρ pe = none :=
  evalPexpr_none_of_fail (fl := .kill err) (by rw [h]; rfl)

theorem evalPexpr_none_of_uncovered {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {ρ : EnvStack} {pe : generic_pexpr Unit sym} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    (h : evalClass tds loc ext file ρ pe = .uncovered) :
    evalPexpr tds ext file ρ pe = none := by
  cases hv : evalPexpr tds ext file ρ pe with
  | none => rfl
  | some v => rw [← evalClass_val_iff tds loc ext file ρ pe v, h] at hv; cases hv

/-! ## Equations of the failure classifier -/

section StepFailEqns
variable (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
  (file : generic_file Unit core_run_annotation) (ρ : EnvStack)

theorem stepFail_val (a : List _root_.annot) (v : value) :
    stepFail tds loc ext file ρ (Pexpr a () (PEval v)) = StepFail.uncovered := by
  rw [stepFail.eq_def]

theorem stepFail_sym (a : List _root_.annot) (x : sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEsym x)) =
      (match lookup_env (resolveExtern ext x) ρ with
      | some _ => StepFail.uncovered
      | none =>
        match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
            (resolveExtern ext x) file.funs with
        | some (Proc _ _ _ _ _) => StepFail.uncovered
        | _ => StepFail.kill (Unresolved_symbol loc (resolveExtern ext x))) := by
  rw [stepFail]

theorem stepFail_undef (a : List _root_.annot) (uloc : CerbLocation.Loc)
    (ub : undefined_behaviour) :
    stepFail tds loc ext file ρ (Pexpr a () (PEundef uloc ub)) = undefOut loc uloc ub := by
  rw [stepFail]

theorem stepFail_op (a : List _root_.annot) (op : binop) (pe1 pe2 : generic_pexpr Unit sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEop op pe1 pe2)) =
      (match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match stepPexprRaw tds ext file ρ pe2 with
        | none => stepFail tds loc ext file ρ pe2
        | some r2 =>
          match valueFromPexpr r1, valueFromPexpr r2 with
          | some v1, some v2 => binopOut loc op pe1 pe2 v1 v2
          | _, _ => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_array_shift (a : List _root_.annot) (pe1 : generic_pexpr Unit sym)
    (ty : ctype) (pe2 : generic_pexpr Unit sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEarray_shift pe1 ty pe2)) =
      (match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match stepPexprRaw tds ext file ρ pe2 with
        | none => stepFail tds loc ext file ρ pe2
        | some r2 =>
          match valueFromPexpr r1, valueFromPexpr r2 with
          | some v1, some v2 => shiftOut tds ty v1 v2
          | _, _ => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_ctor (a : List _root_.annot) (c : ctor) (pes : List (generic_pexpr Unit sym)) :
    stepFail tds loc ext file ρ (Pexpr a () (PEctor c pes)) =
      stepFailList tds loc ext file ρ pes := by
  rw [stepFail]

theorem stepFail_case (a : List _root_.annot) (pe : generic_pexpr Unit sym)
    (pats : List (pattern × generic_pexpr Unit sym)) :
    stepFail tds loc ext file ρ (Pexpr a () (PEcase pe pats)) =
      (match stepPexprRaw tds ext file ρ pe with
      | none => stepFail tds loc ext file ρ pe
      | some _ => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_not (a : List _root_.annot) (pe : generic_pexpr Unit sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEnot pe)) =
      (match stepPexprRaw tds ext file ρ pe with
      | none => stepFail tds loc ext file ρ pe
      | some r =>
        match valueFromPexpr r with
        | some Vtrue => StepFail.uncovered
        | some Vfalse => StepFail.uncovered
        | some _ => StepFail.kill illtypedPEnot
        | none => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_if (a : List _root_.annot) (pe1 pe2 pe3 : generic_pexpr Unit sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEif pe1 pe2 pe3)) =
      (match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match valueFromPexpr r1 with
        | some Vtrue =>
          match stepPexprRaw tds ext file ρ pe2 with
          | none => stepFail tds loc ext file ρ pe2
          | some _ => StepFail.uncovered
        | some Vfalse =>
          match stepPexprRaw tds ext file ρ pe3 with
          | none => stepFail tds loc ext file ρ pe3
          | some _ => StepFail.uncovered
        | some cval => StepFail.kill (illtypedPEif cval)
        | none => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_conv_int (a : List _root_.annot) (ity : integerType) (pe : generic_pexpr Unit sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEconv_int ity pe)) =
      (match stepPexprRaw tds ext file ρ pe with
      | none => stepFail tds loc ext file ρ pe
      | some r =>
        match valueFromPexpr r with
        | some v => convIntOut ity v
        | none => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_wrapI (a : List _root_.annot) (ity : integerType) (op : iop)
    (pe1 pe2 : generic_pexpr Unit sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEwrapI ity op pe1 pe2)) =
      (match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match stepPexprRaw tds ext file ρ pe2 with
        | none => stepFail tds loc ext file ρ pe2
        | some r2 =>
          match valueFromPexpr r1, valueFromPexpr r2 with
          | some v1, some v2 => wrapIOut ity op v1 v2
          | _, _ => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_catch (a : List _root_.annot) (ity : integerType) (op : iop)
    (pe1 pe2 : generic_pexpr Unit sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEcatch_exceptional_condition ity op pe1 pe2)) =
      (match stepPexprRaw tds ext file ρ pe1 with
      | none => stepFail tds loc ext file ρ pe1
      | some r1 =>
        match stepPexprRaw tds ext file ρ pe2 with
        | none => stepFail tds loc ext file ρ pe2
        | some r2 =>
          match valueFromPexpr r1, valueFromPexpr r2 with
          | some v1, some v2 => catchOut loc ity op v1 v2
          | _, _ => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_is_unsigned (a : List _root_.annot) (pe : generic_pexpr Unit sym) :
    stepFail tds loc ext file ρ (Pexpr a () (PEis_unsigned pe)) =
      (match stepPexprRaw tds ext file ρ pe with
      | none => stepFail tds loc ext file ρ pe
      | some r =>
        match valueFromPexpr r with
        | some v => isUnsignedOut v
        | none => StepFail.uncovered) := by
  rw [stepFail]

theorem stepFail_call (a : List _root_.annot) (nm : generic_name sym)
    (pes : List (generic_pexpr Unit sym)) :
    stepFail tds loc ext file ρ (Pexpr a () (PEcall nm pes)) =
      (match stepPexprsRaw tds ext file ρ pes with
      | none => stepFailList tds loc ext file ρ pes
      | some rs =>
        match valueFromPexprs rs with
        | none => StepFail.uncovered
        | some vs =>
          match callBody file nm vs with
          | some _ => StepFail.uncovered
          | none => callOut file nm) := by
  rw [stepFail]

theorem stepFailList_nil : stepFailList tds loc ext file ρ [] = StepFail.uncovered := by
  rw [stepFailList]

theorem stepFailList_cons (pe : generic_pexpr Unit sym) (pes : List (generic_pexpr Unit sym)) :
    stepFailList tds loc ext file ρ (pe :: pes) =
      (match stepPexprRaw tds ext file ρ pe with
      | some _ => stepFailList tds loc ext file ρ pes
      | none =>
        match stepFail tds loc ext file ρ pe with
        | .kill e => StepFail.kill e
        | .undef l u =>
          match stepPexprsRaw tds ext file ρ pes with
          | some _ => StepFail.undef l u
          | none => StepFail.uncovered
        | _ => StepFail.uncovered) := by
  rw [stepFailList]

end StepFailEqns

/-! ## The exception monad's failure laws -/

theorem fail0_eq {a b : Type} (err : b) : (fail0 err : exceptM a b) = Exception err := rfl

theorem exception_undef_bind_exception {a b c : Type} (err : b)
    (f : c → exceptM (t0 a) b) :
    exception_undef_bind (Exception err) f = Exception err := rfl

theorem exception_undef_fmap_exception {a b c : Type} (f : a → b) (err : c) :
    exception_undef_fmap f (Exception err) = Exception err := rfl

theorem except_sequence_cons {a b : Type} (m : exceptM a b) (ms : List (exceptM a b)) :
    except_sequence (m :: ms) =
      except_bind m (fun x => except_bind (except_sequence ms)
        (fun xs => except_return (x :: xs))) := rfl

theorem exception_undef_mapM_eq {a b c : Type} (f : c → exceptM (t0 a) b) (xs : List c) :
    exception_undef_mapM f xs =
      except_bind (except_sequence (List.map f xs))
        (fun us => except_return (mapM1 (fun x => x) us)) := rfl

/-- The constructor operand map at a head whose pass RAISES: the raise
    (`except_sequence` stops at the first exception). -/
theorem exception_undef_mapM_cons_exception
    {self : generic_pexpr Unit sym → exceptM (t0 (generic_pexpr Unit sym)) core_run_cause}
    {pe : generic_pexpr Unit sym} {pes : List (generic_pexpr Unit sym)} {err : core_run_cause}
    (h : self pe = Exception err) :
    exception_undef_mapM self (pe :: pes) = Exception err := by
  rw [exception_undef_mapM_eq, List.map_cons, except_sequence_cons, h]
  rfl

/-- The constructor operand map at a head whose pass is an UNDEF and a
    tail whose passes all succeed: the undef (collected by
    `except_sequence`, raised by `sequence0`). -/
theorem exception_undef_mapM_cons_undef
    {self : generic_pexpr Unit sym → exceptM (t0 (generic_pexpr Unit sym)) core_run_cause}
    {pe : generic_pexpr Unit sym} {pes rs : List (generic_pexpr Unit sym)}
    {l : CerbLocation.Loc} {u : List undefined_behaviour}
    (h : self pe = Result (Undef l u))
    (hrest : exception_undef_mapM self pes = exception_undef_return rs) :
    exception_undef_mapM self (pe :: pes) = Result (Undef l u) := by
  rw [exception_undef_mapM_eq, List.map_cons, except_sequence_cons, h]
  rw [exception_undef_mapM_eq] at hrest
  cases hseq : except_sequence (List.map self pes) with
  | Exception e => rw [hseq] at hrest; cases hrest
  | Result xs => rfl

/-- The constructor operand map at a head whose pass SUCCEEDS: the
    tail's raise or undef is the list's (a `Defined` head is transparent
    to both layers). -/
theorem exception_undef_mapM_cons_defined
    {self : generic_pexpr Unit sym → exceptM (t0 (generic_pexpr Unit sym)) core_run_cause}
    {pe r : generic_pexpr Unit sym} {pes : List (generic_pexpr Unit sym)} {fl : EvalFail}
    (h : self pe = exception_undef_return r)
    (hrest : exception_undef_mapM self pes = fl.pure (List (generic_pexpr Unit sym))) :
    exception_undef_mapM self (pe :: pes) = fl.pure (List (generic_pexpr Unit sym)) := by
  rw [exception_undef_mapM_eq, List.map_cons, except_sequence_cons, h]
  rw [exception_undef_mapM_eq] at hrest
  cases hseq : except_sequence (List.map self pes) with
  | Exception e =>
    rw [hseq] at hrest
    cases fl with
    | kill err => cases hrest; rfl
    | undef l u => cases hrest
  | Result xs =>
    rw [hseq] at hrest
    cases fl with
    | kill err => cases hrest
    | undef l u =>
      show except_return (mapM1 (fun x => x) (Defined r :: xs)) = _
      have hxs : mapM1 (fun x => x) xs = Undef l u := by
        have h' : (Result (mapM1 (fun x => x) xs) : exceptM _ core_run_cause) =
          Result (Undef l u) := hrest
        injection h'
      unfold mapM1 sequence0 at hxs ⊢
      rw [List.map_cons, List.foldr_cons, hxs]
      rfl

/-! ## THE FAILURE BRIDGE, level by level (the failure twin of the success
bridge in Soundness.lean: `step_eval_bridge` → `aux2_bridge` →
`full_eval_bridge`/`eval1_bridge`) -/

/-- E3: where the mirror finds no callee (`callBody = none`) and classifies
    a KILL, `call_function` raises exactly it (core_eval.lem:124–146: the
    lookups fail before the arity check). -/
theorem call_function_exception_of_callOut {file : generic_file Unit core_run_annotation}
    {nm : generic_name sym} (vs : List value) {err : core_run_cause}
    (h : callOut file nm = .kill err) :
    call_function file nm vs = Exception err := by
  unfold callOut at h
  unfold call_function
  dsimp only [CerbDebug.print_debug_pure]
  cases nm with
  | Sym f =>
    dsimp only at h ⊢
    cases hstd : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
        f file.stdlib with
    | some d => rw [hstd] at h; cases h
    | none =>
      rw [hstd] at h
      dsimp only at h ⊢
      cases hfn : fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
          f file.funs with
      | some d => rw [hfn] at h; cases h
      | none => rw [hfn] at h; cases h; rfl
  | Impl c =>
    dsimp only at h ⊢
    cases himpl : fmapLookupBy implementation_constant_compare c file.impl0 with
    | some d =>
      rw [himpl] at h
      cases d with
      | IFun _ _ _ => cases h
      | Def _ _ => cases h; rfl
    | none => rw [himpl] at h; cases h; rfl

/-- LEVEL 1, the failing faces: where one pass fails on a covered operand
    and the classification is a raise or an undef, the engine's one-call
    evaluator delivers exactly that outcome. Quantified over the level
    counter, the call location, the memory state; the current location
    `loc` and the file are READ (the `Unresolved_symbol` payload, the
    undef's location, and the procedure-pointer arm). -/
theorem stepFail_bridge {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym}
    (hp : PePure pe) (hn : stepPexprRaw tds ext file ρ pe = none) {fl : EvalFail}
    (hf : (stepFail tds loc ext file ρ pe).fail? = some fl) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel →
    ∀ (n : Nat) (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    step_eval_pexpr_lemFuel fuel tds n loc cloc ext ρ mem file false pe =
      fl.pure (generic_pexpr Unit sym) := by
  induction hp generalizing fl with
  | val a v => rw [stepPexprRaw] at hn; cases hn
  | ctorTy a c hc pb ty =>
    -- the one operand is a value: the list classifier is `.uncovered`
    exfalso
    rw [stepFail_ctor, stepFailList_cons, stepPexprRaw] at hf
    dsimp only at hf
    rw [stepFailList_nil] at hf
    cases hf
  | sym a x =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEsym x)); omega⟩
    rw [stepFail_sym] at hf
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases hres : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2) x ext with
    | none =>
      rw [show resolveExtern ext x = x by unfold resolveExtern; rw [hres]] at hf
      dsimp only
      cases hl : lookup_env x ρ with
      | some v => rw [hl] at hf; cases hf
      | none =>
        rw [hl] at hf
        cases hfn : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
            Lem_Basic_classes.ordCompare s1 s2) x file.funs with
        | none => rw [hfn] at hf; cases hf; rfl
        | some d =>
          rw [hfn] at hf
          cases d with
          | Proc _ _ _ _ _ => cases hf
          | Fun _ _ _ => cases hf; rfl
          | ProcDecl _ _ _ => cases hf; rfl
          | BuiltinDecl _ _ _ => cases hf; rfl
    | some y =>
      rw [show resolveExtern ext x = y by unfold resolveExtern; rw [hres]] at hf
      dsimp only
      cases hl : lookup_env y ρ with
      | some v => rw [hl] at hf; cases hf
      | none =>
        rw [hl] at hf
        cases hfn : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
            Lem_Basic_classes.ordCompare s1 s2) y file.funs with
        | none => rw [hfn] at hf; cases hf; rfl
        | some d =>
          rw [hfn] at hf
          cases d with
          | Proc _ _ _ _ _ => cases hf
          | Fun _ _ _ => cases hf; rfl
          | ProcDecl _ _ _ => cases hf; rfl
          | BuiltinDecl _ _ _ => cases hf; rfl
  | undef a uloc ub =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEundef uloc ub)); omega⟩
    rw [stepFail_undef] at hf
    show exception_undef_fmap (Pexpr [] ()) _ = _
    cases ub <;> (dsimp only [undefOut, StepFail.fail?] at hf) <;> (cases hf) <;>
      (cases cloc <;> rfl)
  | @op a op hop pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    rw [stepFail_op] at hf
    rw [stepPexprRaw] at hn
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only [step_eval_peop]
    cases h1 : stepPexprRaw tds ext file ρ pe1 with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih1 h1 hf f hd1 (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 =>
      rw [h1] at hf hn
      dsimp only at hf
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      rw [step_eval_bridge hp1 (by rw [stepPexpr_of_PePure hp1]; exact h1) f hd1 (n+1) loc cloc
        mem]
      cases h2 : stepPexprRaw tds ext file ρ pe2 with
      | none =>
        rw [h2] at hf
        dsimp only at hf
        dsimp only [exception_undef_bind, exception_undef_return, except_return, return1]
        rw [ih2 h2 hf f hd2 (n+1) cloc mem]
        first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
      | some r2 =>
        rw [h2] at hf hn
        dsimp only at hf
        simp only [Option.bind_some] at hn
        rw [step_eval_bridge hp2 (by rw [stepPexpr_of_PePure hp2]; exact h2) f hd2 (n+1) loc cloc
          mem]
        dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
          except_return, return1]
        cases hv1 : valueFromPexpr r1 with
        | none => rw [hv1] at hf; cases hf
        | some v1 =>
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          cases hv2 : valueFromPexpr r2 with
          | none => rw [hv1, hv2] at hf; cases hf
          | some v2 =>
            obtain rfl := stepPexprRaw_valPe_of_value h2 hv2
            rw [hv1, hv2] at hf hn
            dsimp only at hf hn
            -- the binop dispatch: the mirrored operator (`hop`) at every
            -- pair of value shapes; the engine's arm and the classifier's
            -- agree case by case
            cases op <;> (try (cases hop)) <;>
              rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
              rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov2)) <;>
              (dsimp only [binopOut, StepFail.fail?] at hf
               first
               | (cases hf; rfl)
               | (split at hf <;> cases hf)
               | (exact absurd hf (by simp)))
  | @arrayShift a ty pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    rw [stepFail_array_shift] at hf
    rw [stepPexprRaw] at hn
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases h1 : stepPexprRaw tds ext file ρ pe1 with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih1 h1 hf f hd1 (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 =>
      rw [h1] at hf hn
      dsimp only at hf
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      rw [step_eval_bridge hp1 (by rw [stepPexpr_of_PePure hp1]; exact h1) f hd1 (n+1) loc cloc
        mem]
      cases h2 : stepPexprRaw tds ext file ρ pe2 with
      | none =>
        rw [h2] at hf
        dsimp only at hf
        dsimp only [exception_undef_bind, exception_undef_return, except_return, return1]
        rw [ih2 h2 hf f hd2 (n+1) cloc mem]
        first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
      | some r2 =>
        rw [h2] at hf hn
        dsimp only at hf
        simp only [Option.bind_some] at hn
        rw [step_eval_bridge hp2 (by rw [stepPexpr_of_PePure hp2]; exact h2) f hd2 (n+1) loc cloc
          mem]
        dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
          except_return, return1]
        cases hv1 : valueFromPexpr r1 with
        | none => rw [hv1] at hf; cases hf
        | some v1 =>
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          cases hv2 : valueFromPexpr r2 with
          | none => rw [hv1, hv2] at hf; cases hf
          | some v2 =>
            obtain rfl := stepPexprRaw_valPe_of_value h2 hv2
            rw [hv1, hv2] at hf hn
            dsimp only at hf hn
            unfold shiftOut at hf
            cases hb : evalArrayShift tds ty v1 v2 with
            | some w => rw [hb] at hf; cases hf
            | none =>
              rw [hb] at hf
              dsimp only [StepFail.fail?] at hf
              obtain rfl := Option.some.inj hf
              rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
              rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov2)) <;>
                first
                | rfl
                | (cases hb)
  | @ctor a c hc pes hps ih =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [stepFail_ctor] at hf
    rw [stepPexprRaw] at hn
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    -- the operand list: walk to the first failing pass
    have hlist : ∀ (pes' : List (generic_pexpr Unit sym)),
        (∀ q ∈ pes', PePure q) →
        (∀ q ∈ pes', peDepth q ≤ f) →
        (∀ q ∈ pes', ∀ {fl' : EvalFail}, stepPexprRaw tds ext file ρ q = none →
          (stepFail tds loc ext file ρ q).fail? = some fl' →
          step_eval_pexpr_lemFuel f tds (n + 1) loc cloc ext ρ mem file false q =
            fl'.pure (generic_pexpr Unit sym)) →
        ∀ {fl' : EvalFail}, (stepFailList tds loc ext file ρ pes').fail? = some fl' →
        exception_undef_mapM
          (fun pe => step_eval_pexpr_lemFuel f tds (n + 1) loc cloc ext ρ mem file false pe)
          pes' = fl'.pure (List (generic_pexpr Unit sym)) := by
      intro pes'
      induction pes' with
      | nil => intro _ _ _ fl' hf'; rw [stepFailList_nil] at hf'; cases hf'
      | cons q qs ihl =>
        intro hps' hds' ihs' fl' hf'
        rw [stepFailList_cons] at hf'
        have hpq : PePure q := hps' q List.mem_cons_self
        have hdq : peDepth q ≤ f := hds' q List.mem_cons_self
        cases hq : stepPexprRaw tds ext file ρ q with
        | some r =>
          rw [hq] at hf'
          dsimp only at hf'
          exact exception_undef_mapM_cons_defined
            (step_eval_bridge hpq (by rw [stepPexpr_of_PePure hpq]; exact hq) f hdq (n+1) loc cloc
              mem)
            (ihl (fun q' hq' => hps' q' (List.mem_cons_of_mem _ hq'))
              (fun q' hq' => hds' q' (List.mem_cons_of_mem _ hq'))
              (fun q' hq' => ihs' q' (List.mem_cons_of_mem _ hq')) hf')
        | none =>
          rw [hq] at hf'
          dsimp only at hf'
          cases hfq : stepFail tds loc ext file ρ q with
          | kill e =>
            rw [hfq] at hf'
            dsimp only [StepFail.fail?] at hf'
            obtain rfl := Option.some.inj hf'
            exact exception_undef_mapM_cons_exception
              (ihs' q List.mem_cons_self hq (fl' := .kill e) (by rw [hfq]; rfl))
          | undef l u =>
            rw [hfq] at hf'
            dsimp only at hf'
            cases hrs : stepPexprsRaw tds ext file ρ qs with
            | none => rw [hrs] at hf'; cases hf'
            | some rs =>
              rw [hrs] at hf'
              dsimp only [StepFail.fail?] at hf'
              obtain rfl := Option.some.inj hf'
              refine exception_undef_mapM_cons_undef (rs := rs)
                (ihs' q List.mem_cons_self hq (fl' := .undef l u) (by rw [hfq]; rfl)) ?_
              apply exception_undef_mapM_bridge
              have hpairs := stepPexprsRaw_some_iff.mp hrs
              clear hrs hf' hfq hq ihl
              induction hpairs with
              | nil => exact .nil
              | cons hpr hrest ihp =>
                rename_i q' r' qs' rs'
                have hsub : ∀ {q'' : generic_pexpr Unit sym}, q'' ∈ q :: qs' → q'' ∈ q :: q' :: qs' := by
                  intro q'' hq''
                  rcases List.mem_cons.mp hq'' with rfl | h
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
                refine .cons ?_ (ihp
                  (fun q'' hq'' => hps' q'' (hsub hq''))
                  (fun q'' hq'' => hds' q'' (hsub hq''))
                  (fun q'' hq'' => ihs' q'' (hsub hq'')))
                have hpq' : PePure q' := hps' q' (List.mem_cons_of_mem _ List.mem_cons_self)
                exact step_eval_bridge hpq' (by rw [stepPexpr_of_PePure hpq']; exact hpr) f
                  (hds' q' (List.mem_cons_of_mem _ List.mem_cons_self)) (n+1) loc cloc mem
          | uncovered => rw [hfq] at hf'; cases hf'
    rw [hlist pes hps (fun q hq => by
        have := peDepth_le_list_of_mem hq; simp only [peDepth_ctor] at hfuel; omega)
      (fun q hq {fl'} hq' hf' => ih q hq hq' hf' f
        (by have := peDepth_le_list_of_mem hq; simp only [peDepth_ctor] at hfuel; omega)
        (n+1) cloc mem) hf]
    first
      | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
      | (cases fl <;> rfl)
  | @case_ a pe pats hpe hpats ih ihs =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd : peDepth pe ≤ f := by simp at hfuel; omega
    rw [stepFail_case] at hf
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases h1 : stepPexprRaw tds ext file ρ pe with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih h1 hf f hd (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 => rw [h1] at hf; cases hf
  | @convInt a ity pe hpe ih =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd : peDepth pe ≤ f := by simp at hfuel; omega
    rw [stepFail_conv_int] at hf
    rw [stepPexprRaw] at hn
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases h1 : stepPexprRaw tds ext file ρ pe with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih h1 hf f hd (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 =>
      rw [h1] at hf hn
      dsimp only at hf
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      rw [step_eval_bridge hpe (by rw [stepPexpr_of_PePure hpe]; exact h1) f hd (n+1) loc cloc mem]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      rcases r1 with ⟨a1, u1, p1⟩
      cases u1
      cases hv1 : valueFromPexpr (Pexpr a1 () p1) with
      | none => rw [hv1] at hf; cases hf
      | some v1 =>
        obtain ⟨a1', hp1⟩ := valueFromPexpr_some_iff.mp hv1
        injection hp1 with _ _ hp1'
        subst hp1'
        rw [hv1] at hf hn
        dsimp only at hf hn
        unfold convIntOut at hf
        cases hb : evalConvInt ity v1 with
        | some w => rw [hb] at hf; cases hf
        | none =>
          rw [hb] at hf
          dsimp only [StepFail.fail?] at hf
          obtain rfl := Option.some.inj hf
          rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
            first
            | rfl
            | (cases hb)
  | @wrapI a ity op pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    rw [stepFail_wrapI] at hf
    rw [stepPexprRaw] at hn
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases h1 : stepPexprRaw tds ext file ρ pe1 with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih1 h1 hf f hd1 (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 =>
      rw [h1] at hf hn
      dsimp only at hf
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      rw [step_eval_bridge hp1 (by rw [stepPexpr_of_PePure hp1]; exact h1) f hd1 (n+1) loc cloc mem]
      cases h2 : stepPexprRaw tds ext file ρ pe2 with
      | none =>
        rw [h2] at hf
        dsimp only at hf
        dsimp only [exception_undef_bind, exception_undef_return, except_return, return1]
        rw [ih2 h2 hf f hd2 (n+1) cloc mem]
        first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
      | some r2 =>
        rw [h2] at hf hn
        dsimp only at hf
        simp only [Option.bind_some] at hn
        rw [step_eval_bridge hp2 (by rw [stepPexpr_of_PePure hp2]; exact h2) f hd2 (n+1) loc cloc mem]
        dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
          except_return, return1]
        cases hv1 : valueFromPexpr r1 with
        | none => rw [hv1] at hf; cases hf
        | some v1 =>
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          cases hv2 : valueFromPexpr r2 with
          | none => rw [hv1, hv2] at hf; cases hf
          | some v2 =>
            obtain rfl := stepPexprRaw_valPe_of_value h2 hv2
            rw [hv1, hv2] at hf hn
            dsimp only at hf hn
            unfold wrapIOut at hf
            cases hb : evalWrapI ity op v1 v2 with
            | some w => rw [hb] at hf; cases hf
            | none =>
              rw [hb] at hf
              dsimp only [StepFail.fail?] at hf
              obtain rfl := Option.some.inj hf
              rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
              rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov2)) <;>
                first
                | rfl
                | (cases hb)
  | @catchExc a ity op pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    rw [stepFail_catch] at hf
    rw [stepPexprRaw] at hn
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases h1 : stepPexprRaw tds ext file ρ pe1 with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih1 h1 hf f hd1 (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 =>
      rw [h1] at hf hn
      dsimp only at hf
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      rw [step_eval_bridge hp1 (by rw [stepPexpr_of_PePure hp1]; exact h1) f hd1 (n+1) loc cloc mem]
      cases h2 : stepPexprRaw tds ext file ρ pe2 with
      | none =>
        rw [h2] at hf
        dsimp only at hf
        dsimp only [exception_undef_bind, exception_undef_return, except_return, return1]
        rw [ih2 h2 hf f hd2 (n+1) cloc mem]
        first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
      | some r2 =>
        rw [h2] at hf hn
        dsimp only at hf
        simp only [Option.bind_some] at hn
        rw [step_eval_bridge hp2 (by rw [stepPexpr_of_PePure hp2]; exact h2) f hd2 (n+1) loc cloc mem]
        dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
          except_return, return1]
        cases hv1 : valueFromPexpr r1 with
        | none => rw [hv1] at hf; cases hf
        | some v1 =>
          obtain rfl := stepPexprRaw_valPe_of_value h1 hv1
          cases hv2 : valueFromPexpr r2 with
          | none => rw [hv1, hv2] at hf; cases hf
          | some v2 =>
            obtain rfl := stepPexprRaw_valPe_of_value h2 hv2
            rw [hv1, hv2] at hf hn
            dsimp only at hf hn
            unfold catchOut at hf
            cases hb : evalCatch ity op v1 v2 with
            | some w => rw [hb] at hf; cases hf
            | none =>
              rw [hb] at hf
              rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
              rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov2)) <;>
                dsimp only [StepFail.fail?] at hf <;>
                first
                | -- two object integers: the mirror's `none` is the engine's UB036 undef
                  (rename_i i1 i2
                   obtain rfl := Option.some.inj hf
                   cases hm : mk_call_catch_exceptional_condition ity op i1 i2 with
                   | some iv => exfalso; simp [evalCatch, hm] at hb
                   | none => simp only [hm]; try rfl)
                | (obtain rfl := Option.some.inj hf; rfl)
                | (cases hb)
  | @isUnsigned a pe hpe hd1 ih =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd : peDepth pe ≤ f := by simp at hfuel; omega
    rw [stepFail_is_unsigned] at hf
    rw [stepPexprRaw] at hn
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases h1 : stepPexprRaw tds ext file ρ pe with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih h1 hf f hd (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 =>
      rw [h1] at hf hn
      dsimp only at hf
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      rw [step_eval_bridge hpe (by rw [stepPexpr_of_PePure hpe]; exact h1) f hd (n+1) loc cloc mem]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      rcases r1 with ⟨a1, u1, p1⟩
      cases u1
      cases hv1 : valueFromPexpr (Pexpr a1 () p1) with
      | none => rw [hv1] at hf; cases hf
      | some v1 =>
        obtain ⟨a1', hp1⟩ := valueFromPexpr_some_iff.mp hv1
        injection hp1 with _ _ hp1'
        subst hp1'
        rw [hv1] at hf hn
        dsimp only at hf hn
        unfold isUnsignedOut at hf
        cases hb : evalIsUnsigned v1 with
        | some w => rw [hb] at hf; cases hf
        | none =>
          rw [hb] at hf
          dsimp only [StepFail.fail?] at hf
          obtain rfl := Option.some.inj hf
          rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
            first
            | rfl
            | (cases hb)
  | @call a nm pes hps ih =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [stepFail_call] at hf
    rw [stepPexprRaw] at hn
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    -- the argument list: walk to the first failing pass (the `ctor` arm's walk)
    have hlist : ∀ (pes' : List (generic_pexpr Unit sym)),
        (∀ q ∈ pes', PePure q) →
        (∀ q ∈ pes', peDepth q ≤ f) →
        (∀ q ∈ pes', ∀ {fl' : EvalFail}, stepPexprRaw tds ext file ρ q = none →
          (stepFail tds loc ext file ρ q).fail? = some fl' →
          step_eval_pexpr_lemFuel f tds (n + 1) loc cloc ext ρ mem file false q =
            fl'.pure (generic_pexpr Unit sym)) →
        ∀ {fl' : EvalFail}, (stepFailList tds loc ext file ρ pes').fail? = some fl' →
        exception_undef_mapM
          (fun pe => step_eval_pexpr_lemFuel f tds (n + 1) loc cloc ext ρ mem file false pe)
          pes' = fl'.pure (List (generic_pexpr Unit sym)) := by
      intro pes'
      induction pes' with
      | nil => intro _ _ _ fl' hf'; rw [stepFailList_nil] at hf'; cases hf'
      | cons q qs ihl =>
        intro hps' hds' ihs' fl' hf'
        rw [stepFailList_cons] at hf'
        have hpq : PePure q := hps' q List.mem_cons_self
        have hdq : peDepth q ≤ f := hds' q List.mem_cons_self
        cases hq : stepPexprRaw tds ext file ρ q with
        | some r =>
          rw [hq] at hf'
          dsimp only at hf'
          exact exception_undef_mapM_cons_defined
            (step_eval_bridge hpq (by rw [stepPexpr_of_PePure hpq]; exact hq) f hdq (n+1) loc cloc
              mem)
            (ihl (fun q' hq' => hps' q' (List.mem_cons_of_mem _ hq'))
              (fun q' hq' => hds' q' (List.mem_cons_of_mem _ hq'))
              (fun q' hq' => ihs' q' (List.mem_cons_of_mem _ hq')) hf')
        | none =>
          rw [hq] at hf'
          dsimp only at hf'
          cases hfq : stepFail tds loc ext file ρ q with
          | kill e =>
            rw [hfq] at hf'
            dsimp only [StepFail.fail?] at hf'
            obtain rfl := Option.some.inj hf'
            exact exception_undef_mapM_cons_exception
              (ihs' q List.mem_cons_self hq (fl' := .kill e) (by rw [hfq]; rfl))
          | undef l u =>
            rw [hfq] at hf'
            dsimp only at hf'
            cases hrs : stepPexprsRaw tds ext file ρ qs with
            | none => rw [hrs] at hf'; cases hf'
            | some rs =>
              rw [hrs] at hf'
              dsimp only [StepFail.fail?] at hf'
              obtain rfl := Option.some.inj hf'
              refine exception_undef_mapM_cons_undef (rs := rs)
                (ihs' q List.mem_cons_self hq (fl' := .undef l u) (by rw [hfq]; rfl)) ?_
              apply exception_undef_mapM_bridge
              have hpairs := stepPexprsRaw_some_iff.mp hrs
              clear hrs hf' hfq hq ihl
              induction hpairs with
              | nil => exact .nil
              | cons hpr hrest ihp =>
                rename_i q' r' qs' rs'
                have hsub : ∀ {q'' : generic_pexpr Unit sym}, q'' ∈ q :: qs' → q'' ∈ q :: q' :: qs' := by
                  intro q'' hq''
                  rcases List.mem_cons.mp hq'' with rfl | h
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
                refine .cons ?_ (ihp
                  (fun q'' hq'' => hps' q'' (hsub hq''))
                  (fun q'' hq'' => hds' q'' (hsub hq''))
                  (fun q'' hq'' => ihs' q'' (hsub hq'')))
                have hpq' : PePure q' := hps' q' (List.mem_cons_of_mem _ List.mem_cons_self)
                exact step_eval_bridge hpq' (by rw [stepPexpr_of_PePure hpq']; exact hpr) f
                  (hds' q' (List.mem_cons_of_mem _ List.mem_cons_self)) (n+1) loc cloc mem
          | uncovered => rw [hfq] at hf'; cases hf'
    cases hrs : stepPexprsRaw tds ext file ρ pes with
    | none =>
      rw [hrs] at hf
      dsimp only at hf
      rw [hlist pes hps (fun q hq => by
          have := peDepth_le_list_of_mem hq; simp only [peDepth_call] at hfuel; omega)
        (fun q hq {fl'} hq' hf' => ih q hq hq' hf' f
          (by have := peDepth_le_list_of_mem hq; simp only [peDepth_call] at hfuel; omega)
          (n+1) cloc mem) hf]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some rs =>
      rw [hrs] at hf hn
      dsimp only at hf
      simp only [Option.bind_eq_bind, Option.bind_some] at hn
      have hmap : exception_undef_mapM
          (fun pe => step_eval_pexpr_lemFuel f tds (n + 1) loc cloc ext ρ mem file false pe)
          pes = exception_undef_return rs := by
        apply exception_undef_mapM_bridge
        have h1 := stepPexprsRaw_some_iff.mp hrs
        clear hrs hn hf hlist
        induction h1 with
        | nil => exact .nil
        | cons hpr hrest ihl =>
          rename_i pe r' pes' rs'
          refine .cons ?_ (ihl (fun q hq => hps q (List.mem_cons_of_mem _ hq))
            (fun q hq => ih q (List.mem_cons_of_mem _ hq))
            (by simp only [peDepth_call, peDepthList_cons] at hfuel ⊢; omega))
          have hpq : PePure pe := hps pe List.mem_cons_self
          exact step_eval_bridge hpq (by rw [stepPexpr_of_PePure hpq]; exact hpr) f
            (by simp only [peDepth_call, peDepthList_cons] at hfuel; omega) (n+1) loc cloc mem
      rw [hmap]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      cases hvs : valueFromPexprs rs with
      | none => rw [hvs] at hf; cases hf
      | some vs =>
        rw [hvs] at hf hn
        dsimp only at hf hn
        cases hcb : callBody file nm vs with
        | some body => rw [hcb] at hf; cases hf
        | none =>
          rw [hcb] at hf
          cases hco : callOut file nm with
          | kill err =>
            rw [hco] at hf
            dsimp only [StepFail.fail?] at hf
            obtain rfl := Option.some.inj hf
            dsimp only
            rw [call_function_exception_of_callOut vs hco]
            rfl
          | undef l u =>
            exfalso
            unfold callOut at hco
            cases nm with
            | Sym f =>
              dsimp only at hco
              split at hco
              · cases hco
              · split at hco <;> cases hco
            | Impl c =>
              dsimp only at hco
              split at hco <;> cases hco
          | uncovered => rw [hco] at hf; cases hf
  | @not_ a pe hpe ih =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd : peDepth pe ≤ f := by simp at hfuel; omega
    rw [stepFail_not] at hf
    rcases pe with ⟨ap, up, pp⟩
    cases up
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases h1 : stepPexprRaw tds ext file ρ (Pexpr ap () pp) with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih h1 hf f hd (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 =>
      rw [h1] at hf
      dsimp only at hf
      rw [step_eval_bridge hpe (by rw [stepPexpr_of_PePure hpe]; exact h1) f hd (n+1) loc cloc
        mem]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      rcases r1 with ⟨a1, u1, p1⟩
      cases u1
      cases hv1 : valueFromPexpr (Pexpr a1 () p1) with
      | none => rw [hv1] at hf; cases hf
      | some w =>
        obtain ⟨a1', hp1⟩ := valueFromPexpr_some_iff.mp hv1
        injection hp1 with _ _ hp1'
        subst hp1'
        rw [hv1] at hf
        cases w <;> dsimp only [StepFail.fail?] at hf <;> cases hf <;> rfl
  | @if_ a pe1 pe2 pe3 hp1 hp2 hp3 ih1 ih2 ih3 =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    have hd3 : peDepth pe3 ≤ f := by simp at hfuel; omega
    rw [stepFail_if] at hf
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases h1 : stepPexprRaw tds ext file ρ pe1 with
    | none =>
      rw [h1] at hf
      dsimp only at hf
      rw [ih1 h1 hf f hd1 (n+1) cloc mem]
      first
        | rw [exception_undef_bind_fail, exception_undef_fmap_fail]
        | (cases fl <;> rfl)
    | some r1 =>
      rw [h1] at hf
      dsimp only at hf
      rw [step_eval_bridge hp1 (by rw [stepPexpr_of_PePure hp1]; exact h1) f hd1 (n+1) loc cloc
        mem]
      dsimp only [exception_undef_bind, exception_undef_return, exception_undef_fmap,
        except_return, return1]
      cases hv1 : valueFromPexpr r1 with
      | none => rw [hv1] at hf; cases hf
      | some w =>
        rw [hv1] at hf
        cases w <;> dsimp only at hf <;> (try (cases hf))
        case Vtrue =>
          cases h2 : stepPexprRaw tds ext file ρ pe2 with
          | none =>
            rw [h2] at hf
            dsimp only at hf
            rw [ih2 h2 hf f hd2 (n+1) cloc mem]
            first
              | rw [exception_undef_fmap_fail, exception_undef_fmap_fail]
              | (cases fl <;> rfl)
          | some _ => rw [h2] at hf; cases hf
        case Vfalse =>
          cases h3 : stepPexprRaw tds ext file ρ pe3 with
          | none =>
            rw [h3] at hf
            dsimp only at hf
            rw [ih3 h3 hf f hd3 (n+1) cloc mem]
            first
              | rw [exception_undef_fmap_fail, exception_undef_fmap_fail]
              | (cases fl <;> rfl)
          | some _ => rw [h3] at hf; cases hf
        all_goals rfl

/-- LEVEL 1, the failing faces at the classified pass. -/
theorem stepClass_bridge_fail {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {fl : EvalFail}
    (hp : PePure pe) (hf : (stepClass tds loc ext file ρ pe).fail? = some fl) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel →
    ∀ (n : Nat) (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    step_eval_pexpr_lemFuel fuel tds n loc cloc ext ρ mem file false pe =
      fl.pure (generic_pexpr Unit sym) := by
  unfold stepClass at hf
  cases hn : stepPexprRaw tds ext file ρ pe with
  | some r => rw [hn] at hf; cases hf
  | none =>
    rw [hn] at hf
    dsimp only at hf
    rw [StepFail.lift_fail?] at hf
    exact stepFail_bridge hp hn hf

/-- LEVEL 1, the kill face (E1's statement at E2's one-pass classifier:
    the classified pass RAISES exactly `err`). -/
theorem step_eval_bridge_kill {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {err : core_run_cause}
    (hp : PePure pe) (hk : stepClass tds loc ext file ρ pe = .kill err) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel →
    ∀ (n : Nat) (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    step_eval_pexpr_lemFuel fuel tds n loc cloc ext ρ mem file false pe =
      Exception err :=
  stepClass_bridge_fail (fl := .kill err) hp (by rw [hk]; rfl)

/-- LEVEL 1, the undef face: the classified pass is the engine's
    `Undef`. -/
theorem step_eval_bridge_undef {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {l : CerbLocation.Loc} {u : List undefined_behaviour}
    (hp : PePure pe) (hk : stepClass tds loc ext file ρ pe = .undef l u) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel →
    ∀ (n : Nat) (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    step_eval_pexpr_lemFuel fuel tds n loc cloc ext ρ mem file false pe =
      Result (Undef l u) :=
  stepClass_bridge_fail (fl := .undef l u) hp (by rw [hk]; rfl)

/-- LEVEL 3a, the iteration: where `classIter` (at `k` rounds) classifies
    a failure, `eval_pexpr_aux2` (at least `k` rounds of fuel; each
    interior evaluator at the default budget) delivers it. -/
theorem classIter_bridge {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation} :
    ∀ (k : Nat) {pe : generic_pexpr Unit sym}, PePure pe →
      peDepth pe ≤ lemDefaultFuel → ∀ {fl : EvalFail},
      (classIter tds loc ext file ρ k pe).fail? = some fl →
      ∀ (fuel : Nat), k ≤ fuel + 1 →
    ∀ (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    eval_pexpr_aux2_lemFuel (fuel + 1) tds loc cloc ext ρ mem file pe =
      fl.pure (Sum (generic_pexpr Unit sym) value) := by
  intro k
  induction k with
  | zero => intro pe hp hd fl hf; cases hf
  | succ k ih =>
    intro pe hp hd fl hf fuel hfuel cloc mem
    unfold classIter at hf
    have hpull : pull_constrained 0 pe = peStrip pe :=
      pull_bridge hp lemDefaultFuel hd 0
    unfold eval_pexpr_aux2_lemFuel
    dsimp only [CerbDebug.print_debug_pure]
    rw [hpull]
    obtain ⟨pex, hpex, hne⟩ := peStrip_root hp
    have hps : PePure (peStrip pe) := hp.strip
    have hdps : peDepth (peStrip pe) ≤ lemDefaultFuel := by rw [peDepth_peStrip hp]; exact hd
    -- the round: the pass's outcome `m` under the engine's continuation
    -- (the value test, then the next round)
    suffices hround : ∀ (m : exceptM (t0 (generic_pexpr Unit sym)) core_run_cause),
        step_eval_pexpr_lemFuel lemDefaultFuel tds 0 loc cloc ext ρ mem file false (peStrip pe)
          = m →
        exception_undef_bind m (fun pe' => match valueFromPexpr pe' with
          | some cval => exception_undef_return (Sum.inr cval)
          | none => eval_pexpr_aux2_lemFuel fuel tds loc cloc ext ρ mem file pe') =
        fl.pure (Sum (generic_pexpr Unit sym) value) by
      rw [hpex] at hround ⊢
      cases pex <;> first
        | (exfalso; apply hne; rfl)
        | (exact hround _ (by
            rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl]))
    intro m hm
    cases hsc : stepClass tds loc ext file ρ (peStrip pe) with
    | kill err =>
      rw [hsc] at hf
      dsimp only [EvalOut.fail?] at hf
      obtain rfl := Option.some.inj hf
      rw [← hm, step_eval_bridge_kill hps hsc lemDefaultFuel hdps 0 cloc mem]
      rfl
    | undef l u =>
      rw [hsc] at hf
      dsimp only [EvalOut.fail?] at hf
      obtain rfl := Option.some.inj hf
      rw [← hm, step_eval_bridge_undef hps hsc lemDefaultFuel hdps 0 cloc mem]
      rfl
    | uncovered => rw [hsc] at hf; cases hf
    | next r =>
      rw [hsc] at hf
      dsimp only at hf
      have hr : stepPexprRaw tds ext file ρ (peStrip pe) = some r := by
        unfold stepClass at hsc
        cases h : stepPexprRaw tds ext file ρ (peStrip pe) with
        | some r' => rw [h] at hsc; cases hsc; rfl
        | none =>
          rw [h] at hsc
          dsimp only at hsc
          cases hsf : stepFail tds loc ext file ρ (peStrip pe) <;> rw [hsf] at hsc <;> cases hsc
      rw [← hm, step_eval_bridge hps (by rw [stepPexpr_of_PePure hps]; exact hr)
        lemDefaultFuel hdps 0 loc cloc mem]
      dsimp only [exception_undef_bind, exception_undef_return, except_return, return1]
      cases hvr : valueFromPexpr r with
      | some _ => rw [hvr] at hf; cases hf
      | none =>
        rw [hvr] at hf
        dsimp only at hf
        split at hf
        · rename_i hguard
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
          obtain ⟨hpr, hlt⟩ := hguard
          have hpr' : PePure r := PePure.of_isPePure hpr
          obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := by
            refine ⟨fuel - 1, ?_⟩
            rcases k with _ | k
            · cases hf
            · omega
          exact ih hpr' (by omega) hf f' (by omega) cloc mem
        · cases hf

/-- LEVEL 3a: `eval_pexpr_aux2` delivers the classified failure, at any
    fuel of at least `peDepth pe` rounds (the engine's own budgets, as
    for the success bridge `aux2_bridge`). -/
theorem aux2_bridge_fail {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {fl : EvalFail}
    (hp : PePure pe) (hf : (evalClass tds loc ext file ρ pe).fail? = some fl)
    (hd : peDepth pe ≤ lemDefaultFuel) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel + 1 →
    ∀ (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    eval_pexpr_aux2_lemFuel (fuel + 1) tds loc cloc ext ρ mem file pe =
      fl.pure (Sum (generic_pexpr Unit sym) value) := by
  intro fuel hfuel cloc mem
  unfold evalClass at hf
  cases hv : evalPexpr tds ext file ρ pe with
  | some v => rw [hv] at hf; cases hf
  | none =>
    rw [hv] at hf
    exact classIter_bridge (peDepth pe) hp hd hf fuel hfuel cloc mem

/-- LEVEL 3a, the kill face (E1's `aux2_bridge_kill`, with E2's round
    budget). -/
theorem aux2_bridge_kill {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {err : core_run_cause}
    (hp : PePure pe) (hk : evalClass tds loc ext file ρ pe = .kill err)
    (hd : peDepth pe ≤ lemDefaultFuel) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel + 1 →
    ∀ (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    eval_pexpr_aux2_lemFuel (fuel + 1) tds loc cloc ext ρ mem file pe = Exception err :=
  aux2_bridge_fail (fl := .kill err) hp (by rw [hk]; rfl) hd

/-- LEVEL 3b: `full_eval_pexpr` (the Eif/Erun/action-operand evaluator)
    delivers the classified failure at every run state. -/
theorem full_eval_bridge_fail {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {b : Type} {ext : Fmap sym sym} {th : thread_state}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {fl : EvalFail}
    (hp : PePure pe)
    (hf : (evalClass tds th.current_loc ext file th.env pe).fail? = some fl)
    (hd : peDepth pe ≤ lemDefaultFuel) (σ : CerbMem.MemState) :
    full_eval_pexpr (b := b) tds th ext σ file pe = fl.run value b := by
  rw [show (full_eval_pexpr (b := b) tds th ext σ file pe) =
    full_eval_pexpr_lemFuel (b := b) (999999 + 1) tds th ext σ file pe
    from rfl]
  show stExceptUndef_bind _ _ = _
  funext st
  rw [stExceptUndef_bind_apply]
  rw [show E.eval_pexpr20 (a := b) tds th ext σ file pe =
    runEU ((eval_pexpr_aux2 tds) th.current_loc
      (match th.exec_loc with
        | ELoc_globals => none
        | ELoc_normal [] => none
        | ELoc_normal ((_, loc1) :: _) => some loc1)
      ext th.env (some σ) file pe) from rfl]
  rw [show (eval_pexpr_aux2 (tds)) = eval_pexpr_aux2_lemFuel (999999 + 1) tds
    from rfl]
  rw [aux2_bridge_fail hp hf hd 999999
    (by rw [show lemDefaultFuel = 999999 + 1 from rfl] at hd; exact hd) _ (some σ)]
  rw [runEU_fail]
  cases fl <;> rfl

/-- LEVEL 3b, the kill face (E1's statement, verbatim). -/
theorem full_eval_bridge_kill {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {b : Type} {ext : Fmap sym sym} {th : thread_state}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {err : core_run_cause}
    (hp : PePure pe)
    (hk : evalClass tds th.current_loc ext file th.env pe = .kill err)
    (hd : peDepth pe ≤ lemDefaultFuel) (σ : CerbMem.MemState) :
    full_eval_pexpr (b := b) tds th ext σ file pe = fun _ => Exception err :=
  full_eval_bridge_fail (fl := .kill err) hp (by rw [hk]; rfl) hd σ

/-- LEVEL 3b, the undef face: the evaluator's `Undef`, state untouched. -/
theorem full_eval_bridge_undef {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {b : Type} {ext : Fmap sym sym} {th : thread_state}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {l : CerbLocation.Loc} {u : List undefined_behaviour}
    (hp : PePure pe)
    (hk : evalClass tds th.current_loc ext file th.env pe = .undef l u)
    (hd : peDepth pe ≤ lemDefaultFuel) (σ : CerbMem.MemState) :
    full_eval_pexpr (b := b) tds th ext σ file pe = fun st => Result (Undef l u, st) :=
  full_eval_bridge_fail (fl := .undef l u) hp (by rw [hk]; rfl) hd σ

/-- The one-iteration evaluator under its `Sum` readout (step_ctx's
    `eval_pexpr1`, Core_reduction.lean:484 — the Ememop/Esave operand
    evaluator) delivers the classified failure. -/
theorem eval1_bridge_fail {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {th : thread_state}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {fl : EvalFail}
    (hp : PePure pe)
    (hf : (evalClass tds th.current_loc ext file th.env pe).fail? = some fl)
    (hd : peDepth pe ≤ lemDefaultFuel) (σ : CerbMem.MemState)
    (k : Sum (generic_pexpr Unit sym) value → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (rs : core_run_state) :
    stExceptUndef_bind (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe) k rs =
      fl.run (generic_pexpr Unit sym) core_run_state rs := by
  rw [stExceptUndef_bind_apply]
  rw [show E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe =
    runEU ((eval_pexpr_aux2 tds) th.current_loc
      (match th.exec_loc with
        | ELoc_globals => none
        | ELoc_normal [] => none
        | ELoc_normal ((_, loc1) :: _) => some loc1)
      ext th.env (some σ) file pe) from rfl]
  rw [show (eval_pexpr_aux2 (tds)) = eval_pexpr_aux2_lemFuel (999999 + 1) tds
    from rfl]
  rw [aux2_bridge_fail hp hf hd 999999
    (by rw [show lemDefaultFuel = 999999 + 1 from rfl] at hd; exact hd) _ (some σ)]
  rw [runEU_fail]
  cases fl <;> rfl

/-- ... the kill face (E1's statement, verbatim). -/
theorem eval1_bridge_kill {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {th : thread_state}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {err : core_run_cause}
    (hp : PePure pe)
    (hk : evalClass tds th.current_loc ext file th.env pe = .kill err)
    (hd : peDepth pe ≤ lemDefaultFuel) (σ : CerbMem.MemState)
    (k : Sum (generic_pexpr Unit sym) value → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (rs : core_run_state) :
    stExceptUndef_bind (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe) k rs =
      Exception err :=
  eval1_bridge_fail (fl := .kill err) hp (by rw [hk]; rfl) hd σ k rs

/-! ## Operand LISTS -/

/-- The engine's outcome on an operand list: all values, or a raise, or
    an undef, or the residual (the operand is carried as the witness). -/
inductive EvalListOut : Type where
  | vals (vs : List value)
  | kill (err : core_run_cause)
  | undef (loc : CerbLocation.Loc) (ubs : List undefined_behaviour)
  | uncovered (pe : generic_pexpr Unit sym)

def EvalListOut.fail? : EvalListOut → Option EvalFail
  | .kill err => some (.kill err)
  | .undef l u => some (.undef l u)
  | _ => none

/-- The MAP-shaped list (`stExceptUndef_mapM`: Ememop/Esave/Eproc
    operands; every operand is evaluated, undefs are collected at the
    exceptM layer and the FIRST raise in list order wins over them,
    `except_sequence`/`sequence0`): a raise anywhere before the first
    uncovered operand is the list's; otherwise the first undef; otherwise
    the first uncovered operand (which hides the rest); otherwise the
    values. -/
def evalClassList (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → EvalListOut
  | [] => .vals []
  | pe :: pes =>
    match evalClass tds loc ext file ρ pe with
    | .kill err => .kill err
    | .uncovered => .uncovered pe
    | .val v =>
      match evalClassList tds loc ext file ρ pes with
      | .vals vs => .vals (v :: vs)
      | .kill err => .kill err
      | .undef l u => .undef l u
      | .uncovered pe' => .uncovered pe'
    | .undef l u =>
      match evalClassList tds loc ext file ρ pes with
      | .vals _ => .undef l u
      | .kill err => .kill err
      | .undef _ _ => .undef l u
      | .uncovered pe' => .uncovered pe'

/-- The FOLD-shaped list (`stExceptUndef_foldM`: Erun arguments; the
    first failing operand stops the fold). -/
def evalClassFold (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    List (generic_pexpr Unit sym) → EvalListOut
  | [] => .vals []
  | pe :: pes =>
    match evalClass tds loc ext file ρ pe with
    | .kill err => .kill err
    | .undef l u => .undef l u
    | .uncovered => .uncovered pe
    | .val v =>
      match evalClassFold tds loc ext file ρ pes with
      | .vals vs => .vals (v :: vs)
      | .kill err => .kill err
      | .undef l u => .undef l u
      | .uncovered pe' => .uncovered pe'

section ListFacts
variable (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc)
    (ext : Fmap sym sym) (file : generic_file Unit core_run_annotation) (ρ : EnvStack)

theorem evalClassList_cons (pe : generic_pexpr Unit sym) (pes : List (generic_pexpr Unit sym)) :
    evalClassList tds loc ext file ρ (pe :: pes) =
      (match evalClass tds loc ext file ρ pe with
      | .kill err => .kill err
      | .uncovered => .uncovered pe
      | .val v =>
        match evalClassList tds loc ext file ρ pes with
        | .vals vs => .vals (v :: vs)
        | .kill err => .kill err
        | .undef l u => .undef l u
        | .uncovered pe' => .uncovered pe'
      | .undef l u =>
        match evalClassList tds loc ext file ρ pes with
        | .vals _ => .undef l u
        | .kill err => .kill err
        | .undef _ _ => .undef l u
        | .uncovered pe' => .uncovered pe') := rfl

theorem evalClassFold_cons (pe : generic_pexpr Unit sym) (pes : List (generic_pexpr Unit sym)) :
    evalClassFold tds loc ext file ρ (pe :: pes) =
      (match evalClass tds loc ext file ρ pe with
      | .kill err => .kill err
      | .undef l u => .undef l u
      | .uncovered => .uncovered pe
      | .val v =>
        match evalClassFold tds loc ext file ρ pes with
        | .vals vs => .vals (v :: vs)
        | .kill err => .kill err
        | .undef l u => .undef l u
        | .uncovered pe' => .uncovered pe') := rfl

theorem evalClassList_vals_iff (pes : List (generic_pexpr Unit sym)) (vs : List value) :
    evalClassList tds loc ext file ρ pes = .vals vs ↔ evalPexprs tds ext file ρ pes = some vs := by
  induction pes generalizing vs with
  | nil =>
    show EvalListOut.vals [] = EvalListOut.vals vs ↔ some [] = some vs
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  | cons pe pes ih =>
    rw [evalClassList_cons, evalPexprs_cons]
    cases hc : evalClass tds loc ext file ρ pe with
    | val v =>
      rw [(evalClass_val_iff tds loc ext file ρ pe v).mp hc]
      cases hl : evalClassList tds loc ext file ρ pes with
      | vals vs' =>
        rw [(ih vs').mp hl]
        constructor
        · intro h; cases h; rfl
        · intro h; cases h; rfl
      | kill err =>
        have : evalPexprs tds ext file ρ pes = none := by
          cases h' : evalPexprs tds ext file ρ pes with
          | none => rfl
          | some w => rw [← ih w, hl] at h'; cases h'
        rw [this]
        constructor <;> intro h <;> cases h
      | undef l u =>
        have : evalPexprs tds ext file ρ pes = none := by
          cases h' : evalPexprs tds ext file ρ pes with
          | none => rfl
          | some w => rw [← ih w, hl] at h'; cases h'
        rw [this]
        constructor <;> intro h <;> cases h
      | uncovered pe' =>
        have : evalPexprs tds ext file ρ pes = none := by
          cases h' : evalPexprs tds ext file ρ pes with
          | none => rfl
          | some w => rw [← ih w, hl] at h'; cases h'
        rw [this]
        constructor <;> intro h <;> cases h
    | kill err =>
      rw [evalPexpr_none_of_kill hc]
      constructor <;> intro h <;> cases h
    | undef l u =>
      rw [evalPexpr_none_of_fail (fl := .undef l u) (by rw [hc]; rfl)]
      cases evalClassList tds loc ext file ρ pes <;> constructor <;> intro h <;> cases h
    | uncovered =>
      rw [evalPexpr_none_of_uncovered hc]
      constructor <;> intro h <;> cases h

theorem evalClassFold_vals_iff (pes : List (generic_pexpr Unit sym)) (vs : List value) :
    evalClassFold tds loc ext file ρ pes = .vals vs ↔ evalPexprs tds ext file ρ pes = some vs := by
  induction pes generalizing vs with
  | nil =>
    show EvalListOut.vals [] = EvalListOut.vals vs ↔ some [] = some vs
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  | cons pe pes ih =>
    rw [evalClassFold_cons, evalPexprs_cons]
    cases hc : evalClass tds loc ext file ρ pe with
    | val v =>
      rw [(evalClass_val_iff tds loc ext file ρ pe v).mp hc]
      cases hl : evalClassFold tds loc ext file ρ pes with
      | vals vs' =>
        rw [(ih vs').mp hl]
        constructor
        · intro h; cases h; rfl
        · intro h; cases h; rfl
      | kill err =>
        have : evalPexprs tds ext file ρ pes = none := by
          cases h' : evalPexprs tds ext file ρ pes with
          | none => rfl
          | some w => rw [← ih w, hl] at h'; cases h'
        rw [this]
        constructor <;> intro h <;> cases h
      | undef l u =>
        have : evalPexprs tds ext file ρ pes = none := by
          cases h' : evalPexprs tds ext file ρ pes with
          | none => rfl
          | some w => rw [← ih w, hl] at h'; cases h'
        rw [this]
        constructor <;> intro h <;> cases h
      | uncovered pe' =>
        have : evalPexprs tds ext file ρ pes = none := by
          cases h' : evalPexprs tds ext file ρ pes with
          | none => rfl
          | some w => rw [← ih w, hl] at h'; cases h'
        rw [this]
        constructor <;> intro h <;> cases h
    | kill err =>
      rw [evalPexpr_none_of_kill hc]
      constructor <;> intro h <;> cases h
    | undef l u =>
      rw [evalPexpr_none_of_fail (fl := .undef l u) (by rw [hc]; rfl)]
      constructor <;> intro h <;> cases h
    | uncovered =>
      rw [evalPexpr_none_of_uncovered hc]
      constructor <;> intro h <;> cases h

end ListFacts

theorem evalClassList_uncovered {tds : CerbTags.TagDefsMap} {loc : CerbLocation.Loc}
    {ext : Fmap sym sym} {file : generic_file Unit core_run_annotation} {ρ : EnvStack}
    {pes : List (generic_pexpr Unit sym)} {pe : generic_pexpr Unit sym}
    (h : evalClassList tds loc ext file ρ pes = .uncovered pe) :
    pe ∈ pes ∧ evalClass tds loc ext file ρ pe = .uncovered := by
  induction pes with
  | nil => cases h
  | cons pe' pes ih =>
    rw [evalClassList_cons] at h
    cases hc : evalClass tds loc ext file ρ pe' with
    | val v =>
      rw [hc] at h
      cases hl : evalClassList tds loc ext file ρ pes with
      | vals vs => rw [hl] at h; cases h
      | kill err => rw [hl] at h; cases h
      | undef l u => rw [hl] at h; cases h
      | uncovered pe'' =>
        rw [hl] at h
        cases h
        obtain ⟨hm, hu⟩ := ih hl
        exact ⟨List.mem_cons_of_mem _ hm, hu⟩
    | undef l u =>
      rw [hc] at h
      cases hl : evalClassList tds loc ext file ρ pes with
      | vals vs => rw [hl] at h; cases h
      | kill err => rw [hl] at h; cases h
      | undef l' u' => rw [hl] at h; cases h
      | uncovered pe'' =>
        rw [hl] at h
        cases h
        obtain ⟨hm, hu⟩ := ih hl
        exact ⟨List.mem_cons_of_mem _ hm, hu⟩
    | kill err => rw [hc] at h; cases h
    | uncovered =>
      rw [hc] at h
      cases h
      exact ⟨List.mem_cons_self, hc⟩

theorem evalClassFold_uncovered {tds : CerbTags.TagDefsMap} {loc : CerbLocation.Loc}
    {ext : Fmap sym sym} {file : generic_file Unit core_run_annotation} {ρ : EnvStack}
    {pes : List (generic_pexpr Unit sym)} {pe : generic_pexpr Unit sym}
    (h : evalClassFold tds loc ext file ρ pes = .uncovered pe) :
    pe ∈ pes ∧ evalClass tds loc ext file ρ pe = .uncovered := by
  induction pes with
  | nil => cases h
  | cons pe' pes ih =>
    rw [evalClassFold_cons] at h
    cases hc : evalClass tds loc ext file ρ pe' with
    | val v =>
      rw [hc] at h
      cases hl : evalClassFold tds loc ext file ρ pes with
      | vals vs => rw [hl] at h; cases h
      | kill err => rw [hl] at h; cases h
      | undef l u => rw [hl] at h; cases h
      | uncovered pe'' =>
        rw [hl] at h
        cases h
        obtain ⟨hm, hu⟩ := ih hl
        exact ⟨List.mem_cons_of_mem _ hm, hu⟩
    | undef l u => rw [hc] at h; cases h
    | kill err => rw [hc] at h; cases h
    | uncovered =>
      rw [hc] at h
      cases h
      exact ⟨List.mem_cons_self, hc⟩

theorem evalClassList_of_none {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {ρ : EnvStack} {pes : List (generic_pexpr Unit sym)} (loc : CerbLocation.Loc)
    (file : generic_file Unit core_run_annotation)
    (h : evalPexprs tds ext file ρ pes = none) :
    (∃ fl, (evalClassList tds loc ext file ρ pes).fail? = some fl) ∨
    (∃ pe, evalClassList tds loc ext file ρ pes = .uncovered pe) := by
  cases hc : evalClassList tds loc ext file ρ pes with
  | vals vs => rw [(evalClassList_vals_iff tds loc ext file ρ pes vs).mp hc] at h; cases h
  | kill err => exact .inl ⟨_, rfl⟩
  | undef l u => exact .inl ⟨_, rfl⟩
  | uncovered pe => exact .inr ⟨pe, rfl⟩

theorem evalClassFold_of_none {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {ρ : EnvStack} {pes : List (generic_pexpr Unit sym)} (loc : CerbLocation.Loc)
    (file : generic_file Unit core_run_annotation)
    (h : evalPexprs tds ext file ρ pes = none) :
    (∃ fl, (evalClassFold tds loc ext file ρ pes).fail? = some fl) ∨
    (∃ pe, evalClassFold tds loc ext file ρ pes = .uncovered pe) := by
  cases hc : evalClassFold tds loc ext file ρ pes with
  | vals vs => rw [(evalClassFold_vals_iff tds loc ext file ρ pes vs).mp hc] at h; cases h
  | kill err => exact .inl ⟨_, rfl⟩
  | undef l u => exact .inl ⟨_, rfl⟩
  | uncovered pe => exact .inr ⟨pe, rfl⟩

/-! ### The MAP-shaped fold (`stExpect_mapM` under `stExceptUndef_mapM`),
generically: a per-element body `h` over elements `x` carrying an operand
`proj x`, characterized pointwise — a value delivers `Defined (wrap x v)`
with the state untouched, a classified failure delivers it. -/

/-- `sequence0` at a list whose head is `Defined`: the tail decides. -/
theorem sequence0_cons_defined {α : Type} (y : α) (us : List (t0 α)) :
    sequence0 (Defined y :: us) = bind2 (sequence0 us) (fun ys => return1 (y :: ys)) := rfl

theorem sequence0_cons_undef {α : Type} (l : CerbLocation.Loc) (u : List undefined_behaviour)
    (us : List (t0 α)) :
    sequence0 (Undef l u :: us) = Undef l u := rfl

theorem stExpect_mapM_cons {a b msg s : Type} (f : a → s → exceptM ((b × s)) msg)
    (x : a) (xs : List a) :
    stExpect_mapM f (x :: xs) =
      stExpect_bind (f x) (fun y => stExpect_bind (stExpect_mapM f xs)
        (fun ys => stExpect_return (y :: ys))) := rfl

/-- THE MAP-SHAPED LIST BRIDGE: the three faces of `evalClassList` on the
    inner `stExpect_mapM`. -/
theorem stExpect_mapM_class {X Y : Type}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {ext : Fmap sym sym}
    {th : thread_state} {file : generic_file Unit core_run_annotation}
    (h : X → core_run_state → exceptM (t0 Y × core_run_state) core_run_cause)
    (proj : X → generic_pexpr Unit sym) (wrap : X → value → Y)
    (hval : ∀ (x : X) (rs : core_run_state) (v : value),
      evalPexpr tds ext file th.env (proj x) = some v → h x rs = Result (Defined (wrap x v), rs))
    (hfail : ∀ (x : X) (rs : core_run_state) (fl : EvalFail),
      (evalClass tds th.current_loc ext file th.env (proj x)).fail? = some fl →
      h x rs = fl.run Y core_run_state rs)
    (xs : List X) (rs : core_run_state) :
    (∀ err, evalClassList tds th.current_loc ext file th.env (xs.map proj) = .kill err →
      stExpect_mapM h xs rs = Exception err) ∧
    (∀ l u, evalClassList tds th.current_loc ext file th.env (xs.map proj) = .undef l u →
      ∃ us, stExpect_mapM h xs rs = Result (us, rs) ∧ mapM1 (fun x => x) us = Undef l u) ∧
    (∀ vs, evalClassList tds th.current_loc ext file th.env (xs.map proj) = .vals vs →
      ∃ us ys, stExpect_mapM h xs rs = Result (us, rs) ∧ mapM1 (fun x => x) us = Defined ys) := by
  induction xs with
  | nil =>
    refine ⟨(fun err h' => by cases h'), (fun l u h' => by cases h'), (fun vs _ => ⟨[], [], rfl, rfl⟩)⟩
  | cons x xs ih =>
    obtain ⟨ihk, ihu, ihv⟩ := ih
    rw [List.map_cons, stExpect_mapM_cons, stExpect_bind_apply]
    cases hc : evalClass tds th.current_loc ext file th.env (proj x) with
    | val v =>
      rw [hval x rs v ((evalClass_val_iff _ _ _ _ _ _ _).mp hc)]
      dsimp only
      rw [stExpect_bind_apply]
      refine ⟨fun err h' => ?_, fun l u h' => ?_, fun vs h' => ?_⟩
      · rw [evalClassList_cons, hc] at h'
        dsimp only at h'
        cases hl : evalClassList tds th.current_loc ext file th.env (xs.map proj) with
        | vals _ => rw [hl] at h'; cases h'
        | kill e => rw [hl] at h'; cases h'; rw [ihk _ hl]
        | undef _ _ => rw [hl] at h'; cases h'
        | uncovered _ => rw [hl] at h'; cases h'
      · rw [evalClassList_cons, hc] at h'
        dsimp only at h'
        cases hl : evalClassList tds th.current_loc ext file th.env (xs.map proj) with
        | vals _ => rw [hl] at h'; cases h'
        | kill e => rw [hl] at h'; cases h'
        | undef l' u' =>
          rw [hl] at h'; cases h'
          obtain ⟨us, hus, hseq⟩ := ihu _ _ hl
          refine ⟨Defined (wrap x v) :: us, ?_, ?_⟩
          · rw [hus]; rfl
          · unfold mapM1 at hseq ⊢
            rw [List.map_id'] at hseq ⊢
            rw [sequence0_cons_defined, hseq]
            rfl
        | uncovered _ => rw [hl] at h'; cases h'
      · rw [evalClassList_cons, hc] at h'
        dsimp only at h'
        cases hl : evalClassList tds th.current_loc ext file th.env (xs.map proj) with
        | vals vs' =>
          rw [hl] at h'; cases h'
          obtain ⟨us, ys, hus, hseq⟩ := ihv _ hl
          refine ⟨Defined (wrap x v) :: us, wrap x v :: ys, ?_, ?_⟩
          · rw [hus]; rfl
          · unfold mapM1 at hseq ⊢
            rw [List.map_id'] at hseq ⊢
            rw [sequence0_cons_defined, hseq]
            rfl
        | kill e => rw [hl] at h'; cases h'
        | undef _ _ => rw [hl] at h'; cases h'
        | uncovered _ => rw [hl] at h'; cases h'
    | kill err =>
      rw [hfail x rs (.kill err) (by rw [hc]; rfl)]
      refine ⟨fun err' h' => ?_, fun l u h' => ?_, fun vs h' => ?_⟩
      · rw [evalClassList_cons, hc] at h'
        cases h'; rfl
      · rw [evalClassList_cons, hc] at h'; cases h'
      · rw [evalClassList_cons, hc] at h'; cases h'
    | undef l u =>
      rw [hfail x rs (.undef l u) (by rw [hc]; rfl)]
      dsimp only [EvalFail.run]
      rw [stExpect_bind_apply]
      refine ⟨fun err h' => ?_, fun l' u' h' => ?_, fun vs h' => ?_⟩
      · rw [evalClassList_cons, hc] at h'
        dsimp only at h'
        cases hl : evalClassList tds th.current_loc ext file th.env (xs.map proj) with
        | vals _ => rw [hl] at h'; cases h'
        | kill e => rw [hl] at h'; cases h'; rw [ihk _ hl]
        | undef _ _ => rw [hl] at h'; cases h'
        | uncovered _ => rw [hl] at h'; cases h'
      · rw [evalClassList_cons, hc] at h'
        dsimp only at h'
        cases hl : evalClassList tds th.current_loc ext file th.env (xs.map proj) with
        | vals vs' =>
          rw [hl] at h'; cases h'
          obtain ⟨us, ys, hus, -⟩ := ihv _ hl
          refine ⟨Undef l u :: us, ?_, ?_⟩
          · rw [hus]; rfl
          · unfold mapM1
            rw [List.map_id']
            rfl
        | kill e => rw [hl] at h'; cases h'
        | undef l'' u'' =>
          rw [hl] at h'; cases h'
          obtain ⟨us, hus, -⟩ := ihu _ _ hl
          refine ⟨Undef l u :: us, ?_, ?_⟩
          · rw [hus]; rfl
          · unfold mapM1
            rw [List.map_id']
            rfl
        | uncovered _ => rw [hl] at h'; cases h'
      · rw [evalClassList_cons, hc] at h'
        dsimp only at h'
        cases hl : evalClassList tds th.current_loc ext file th.env (xs.map proj) <;>
          rw [hl] at h' <;> cases h'
    | uncovered =>
      refine ⟨fun err h' => ?_, fun l u h' => ?_, fun vs h' => ?_⟩ <;>
        (rw [evalClassList_cons, hc] at h'; cases h')

/-- `stExceptUndef_mapM` delivers the classified failure of the
    MAP-shaped list. -/
theorem stExceptUndef_mapM_class_fail {X Y : Type}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {ext : Fmap sym sym}
    {th : thread_state} {file : generic_file Unit core_run_annotation}
    (h : X → core_run_state → exceptM (t0 Y × core_run_state) core_run_cause)
    (proj : X → generic_pexpr Unit sym) (wrap : X → value → Y)
    (hval : ∀ (x : X) (rs : core_run_state) (v : value),
      evalPexpr tds ext file th.env (proj x) = some v → h x rs = Result (Defined (wrap x v), rs))
    (hfail : ∀ (x : X) (rs : core_run_state) (fl : EvalFail),
      (evalClass tds th.current_loc ext file th.env (proj x)).fail? = some fl →
      h x rs = fl.run Y core_run_state rs)
    (xs : List X) {fl : EvalFail}
    (hf : (evalClassList tds th.current_loc ext file th.env (xs.map proj)).fail? = some fl)
    (rs : core_run_state) :
    stExceptUndef_mapM h xs rs = fl.run (List Y) core_run_state rs := by
  obtain ⟨hk, hu, -⟩ := stExpect_mapM_class h proj wrap hval hfail xs rs
  unfold stExceptUndef_mapM
  rw [stExpect_bind_apply]
  cases hc : evalClassList tds th.current_loc ext file th.env (xs.map proj) with
  | vals _ => rw [hc] at hf; cases hf
  | uncovered _ => rw [hc] at hf; cases hf
  | kill err =>
    rw [hc] at hf; cases hf
    rw [hk err hc]
    rfl
  | undef l u =>
    rw [hc] at hf; cases hf
    obtain ⟨us, hus, hseq⟩ := hu l u hc
    rw [hus]
    show Result (mapM1 (fun x => x) us, rs) = _
    rw [hseq]
    rfl

/-- The Ememop/Esave operand map (`stExceptUndef_mapM` over the
    one-iteration evaluator) delivers the first classified failure. The
    per-operand body is abstract with a pointwise characterization
    (`mapM_eval1_bridge`'s pattern). -/
theorem mapM_eval1_fail {ext : Fmap sym sym} {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = stExceptUndef_bind
        (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
        (fun x => match x with
          | Sum.inl pe' => stExceptUndef_return pe'
          | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs')
    (pes : List (generic_pexpr Unit sym)) {fl : EvalFail}
    (hp : ∀ pe ∈ pes, PePure pe) (hd : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (h : (evalClassList tds th.current_loc ext file th.env pes).fail? = some fl)
    (rs : core_run_state) :
    stExceptUndef_mapM f pes rs = fl.run (List (generic_pexpr Unit sym)) core_run_state rs := by
  -- the body characterized only on the list's own operands: restrict
  -- `f` to `pes` through the subtype of its members
  let X := { pe : generic_pexpr Unit sym // pe ∈ pes }
  have hmap : pes = (pes.attach.map Subtype.val) := (List.attach_map_subtype_val pes).symm
  have hfold : stExceptUndef_mapM f pes rs =
      stExceptUndef_mapM (fun (x : X) => f x.val) pes.attach rs := by
    conv => lhs; rw [hmap]
    unfold stExceptUndef_mapM stExpect_mapM
    rw [List.map_map]
    rfl
  have hval : ∀ (x : X) (rs' : core_run_state) (v : value),
      evalPexpr tds ext file th.env x.val = some v →
      f x.val rs' = Result (Defined (mk_value_pe v), rs') := by
    intro x rs' v hv
    exact (hf x.val rs').trans (eval1_bridge hv (hd x.val x.property) σ rs')
  have hfail : ∀ (x : X) (rs' : core_run_state) (fl' : EvalFail),
      (evalClass tds th.current_loc ext file th.env x.val).fail? = some fl' →
      f x.val rs' = fl'.run (generic_pexpr Unit sym) core_run_state rs' := by
    intro x rs' fl' hf'
    exact (hf x.val rs').trans
      (eval1_bridge_fail (hp x.val x.property) hf' (hd x.val x.property) σ _ rs')
  have hcls : (evalClassList tds th.current_loc ext file th.env
      (pes.attach.map Subtype.val)).fail? = some fl := by
    rw [← hmap]; exact h
  rw [hfold]
  exact stExceptUndef_mapM_class_fail (fun (x : X) => f x.val) Subtype.val
    (fun _ v => mk_value_pe v) hval hfail pes.attach hcls rs

/-- ... the kill face (E1's statement, verbatim). -/
theorem mapM_eval1_kill {ext : Fmap sym sym} {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = stExceptUndef_bind
        (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
        (fun x => match x with
          | Sum.inl pe' => stExceptUndef_return pe'
          | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs')
    (pes : List (generic_pexpr Unit sym)) {err : core_run_cause}
    (hp : ∀ pe ∈ pes, PePure pe) (hd : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel)
    (h : evalClassList tds th.current_loc ext file th.env pes = .kill err)
    (rs : core_run_state) :
    stExceptUndef_mapM f pes rs = Exception err :=
  mapM_eval1_fail f hf pes (fl := .kill err) hp hd (by rw [h]; rfl) rs

/-- The Esave parameter map (`mapM_save_bridge`'s shape) delivers the
    first classified failure among the initializers. -/
theorem mapM_save_fail {ext : Fmap sym sym} {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = stExceptUndef_bind
        (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
        (fun x => match x with
          | Sum.inl pe' => stExceptUndef_return pe'
          | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs')
    (g : (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) →
      core_run_state → exceptM ((t0 (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) ×
        core_run_state)) core_run_cause)
    (hg : ∀ (p : sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
        (rs' : core_run_state),
      g p rs' = stExceptUndef_bind (f p.2.2)
        (fun pe' => stExceptUndef_return (p.1, (p.2.1, pe'))) rs')
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    {fl : EvalFail}
    (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe)
    (hd : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)
    (h : (evalClassList tds th.current_loc ext file th.env (saveParamPexprs ps)).fail? = some fl)
    (rs : core_run_state) :
    stExceptUndef_mapM g ps rs =
      fl.run (List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
        core_run_state rs := by
  let X := { p : sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym) // p ∈ ps }
  have hmap : ps = (ps.attach.map Subtype.val) := (List.attach_map_subtype_val ps).symm
  have hfold : stExceptUndef_mapM g ps rs =
      stExceptUndef_mapM (fun (x : X) => g x.val) ps.attach rs := by
    conv => lhs; rw [hmap]
    unfold stExceptUndef_mapM stExpect_mapM
    rw [List.map_map]
    rfl
  have hproj : (ps.attach.map (fun (x : X) => x.val.2.2)) = saveParamPexprs ps := by
    unfold saveParamPexprs
    conv => rhs; rw [hmap]
    rw [List.map_map]
    rfl
  have hval : ∀ (x : X) (rs' : core_run_state) (v : value),
      evalPexpr tds ext file th.env x.val.2.2 = some v →
      g x.val rs' = Result (Defined (x.val.1, (x.val.2.1, mk_value_pe v)), rs') := by
    intro x rs' v hv
    have hm : x.val.2.2 ∈ saveParamPexprs ps := by
      unfold saveParamPexprs; exact List.mem_map.mpr ⟨x.val, x.property, rfl⟩
    rw [hg, stExceptUndef_bind_apply, (hf _ rs').trans (eval1_bridge hv (hd _ hm) σ rs')]
    rfl
  have hfail : ∀ (x : X) (rs' : core_run_state) (fl' : EvalFail),
      (evalClass tds th.current_loc ext file th.env x.val.2.2).fail? = some fl' →
      g x.val rs' = fl'.run (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
        core_run_state rs' := by
    intro x rs' fl' hf'
    have hm : x.val.2.2 ∈ saveParamPexprs ps := by
      unfold saveParamPexprs; exact List.mem_map.mpr ⟨x.val, x.property, rfl⟩
    rw [hg]
    exact stExceptUndef_bind_fail_apply _
      ((hf _ rs').trans (eval1_bridge_fail (hp _ hm) hf' (hd _ hm) σ _ rs'))
  have hcls : (evalClassList tds th.current_loc ext file th.env
      (ps.attach.map (fun (x : X) => x.val.2.2))).fail? = some fl := by
    rw [hproj]; exact h
  rw [hfold]
  exact stExceptUndef_mapM_class_fail (fun (x : X) => g x.val) (fun x => x.val.2.2)
    (fun x v => (x.val.1, (x.val.2.1, mk_value_pe v))) hval hfail ps.attach hcls rs

/-- ... the kill face (E1's statement, verbatim). -/
theorem mapM_save_kill {ext : Fmap sym sym} {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = stExceptUndef_bind
        (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
        (fun x => match x with
          | Sum.inl pe' => stExceptUndef_return pe'
          | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs')
    (g : (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) →
      core_run_state → exceptM ((t0 (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) ×
        core_run_state)) core_run_cause)
    (hg : ∀ (p : sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))
        (rs' : core_run_state),
      g p rs' = stExceptUndef_bind (f p.2.2)
        (fun pe' => stExceptUndef_return (p.1, (p.2.1, pe'))) rs')
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    {err : core_run_cause}
    (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe)
    (hd : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel)
    (h : evalClassList tds th.current_loc ext file th.env (saveParamPexprs ps) = .kill err)
    (rs : core_run_state) :
    stExceptUndef_mapM g ps rs = Exception err :=
  mapM_save_fail f hf g hg ps (fl := .kill err) hp hd (by rw [h]; rfl) rs

/-- The arguments a jump actually evaluates: the `pes` entries zipped
    against the label's parameters (step_ctx's Erun arm folds over
    `zip sym_bTys pes`, truncating on length mismatch). -/
def zipArgs (params : List (sym × core_base_type))
    (pes : List (generic_pexpr Unit sym)) : List (generic_pexpr Unit sym) :=
  (List.zip params pes).map Prod.snd

theorem zipArgs_sub {params : List (sym × core_base_type)}
    {pes : List (generic_pexpr Unit sym)} {pe : generic_pexpr Unit sym}
    (h : pe ∈ zipArgs params pes) : pe ∈ pes := by
  unfold zipArgs at h
  obtain ⟨⟨p, pe'⟩, hmem, rfl⟩ := List.mem_map.mp h
  exact List.of_mem_zip hmem |>.2

/-- The Erun argument fold (`foldM_args_bridge`'s shape; FOLD-shaped:
    the first failing argument stops it) delivers the classified failure
    of the zipped arguments. -/
theorem foldM_args_fail {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation} {ext : Fmap sym sym}
    (f : EnvStack → (sym × core_base_type) × generic_pexpr Unit sym →
      core_run_state → exceptM ((t0 EnvStack × core_run_state)) core_run_cause)
    (hf : ∀ (acc : EnvStack) (s : sym) (bTy : core_base_type)
      (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f acc ((s, bTy), pe) rs' =
        stExceptUndef_bind (full_eval_pexpr tds th ext σ file pe)
          (fun cval =>
            stExceptUndef_return (update_env (mk_sym_pat s bTy) cval acc)) rs') :
    ∀ (params : List (sym × core_base_type))
      (pes : List (generic_pexpr Unit sym)) {fl : EvalFail}
      (acc : EnvStack) (rs : core_run_state),
      (∀ pe ∈ pes, PePure pe) → (∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) →
      (evalClassFold tds th.current_loc ext file th.env (zipArgs params pes)).fail? = some fl →
      stExceptUndef_foldM f acc (List.zip params pes) rs = fl.run EnvStack core_run_state rs := by
  intro params
  induction params with
  | nil => intro pes fl acc rs _ _ h; cases h
  | cons p params ih =>
    intro pes fl acc rs hp hd h
    cases pes with
    | nil => cases h
    | cons pe pes =>
      have h' : (match evalClass tds th.current_loc ext file th.env pe with
        | .kill err => EvalListOut.kill err
        | .undef l u => EvalListOut.undef l u
        | .uncovered => EvalListOut.uncovered pe
        | .val v =>
          match evalClassFold tds th.current_loc ext file th.env (zipArgs params pes) with
          | .vals vs => EvalListOut.vals (v :: vs)
          | .kill err => EvalListOut.kill err
          | .undef l u => EvalListOut.undef l u
          | .uncovered pe' => EvalListOut.uncovered pe').fail? = some fl := h
      have hpe : PePure pe := hp pe List.mem_cons_self
      have hde : peDepth pe ≤ lemDefaultFuel := hd pe List.mem_cons_self
      obtain ⟨p1, p2⟩ := p
      rw [List.zip_cons_cons, stExceptUndef_foldM_cons, stExceptUndef_bind_apply,
        hf acc p1 p2 pe rs]
      cases hc : evalClass tds th.current_loc ext file th.env pe with
      | kill e =>
        rw [hc] at h'
        dsimp only [EvalListOut.fail?] at h'
        obtain rfl := Option.some.inj h'
        rw [stExceptUndef_bind_fail_apply _ (by
          rw [full_eval_bridge_fail (fl := .kill e) hpe (by rw [hc]; rfl) hde σ])]
        rfl
      | undef l u =>
        rw [hc] at h'
        dsimp only [EvalListOut.fail?] at h'
        obtain rfl := Option.some.inj h'
        rw [stExceptUndef_bind_fail_apply _ (by
          rw [full_eval_bridge_fail (fl := .undef l u) hpe (by rw [hc]; rfl) hde σ])]
        rfl
      | uncovered => rw [hc] at h'; cases h'
      | val v =>
        rw [hc] at h'
        have hv := (evalClass_val_iff tds th.current_loc ext file th.env pe v).mp hc
        rw [stExceptUndef_bind_apply, full_eval_bridge hv hde σ, stExceptUndef_return_apply]
        dsimp only []
        rw [stExceptUndef_return_apply]
        dsimp only []
        cases hl : evalClassFold tds th.current_loc ext file th.env (zipArgs params pes) with
        | vals vs => rw [hl] at h'; cases h'
        | uncovered pe' => rw [hl] at h'; cases h'
        | kill e =>
          rw [hl] at h'
          exact ih pes _ rs (fun pe' hpe' => hp pe' (List.mem_cons_of_mem _ hpe'))
            (fun pe' hpe' => hd pe' (List.mem_cons_of_mem _ hpe')) (by rw [hl]; exact h')
        | undef l u =>
          rw [hl] at h'
          exact ih pes _ rs (fun pe' hpe' => hp pe' (List.mem_cons_of_mem _ hpe'))
            (fun pe' hpe' => hd pe' (List.mem_cons_of_mem _ hpe')) (by rw [hl]; exact h')

/-- ... the kill face (E1's `foldM_args_kill`, at E2's FOLD-shaped list
    classifier — forced: the MAP-shaped classifier raises past a
    collected undef where the fold stops at it). -/
theorem foldM_args_kill {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation} {ext : Fmap sym sym}
    (f : EnvStack → (sym × core_base_type) × generic_pexpr Unit sym →
      core_run_state → exceptM ((t0 EnvStack × core_run_state)) core_run_cause)
    (hf : ∀ (acc : EnvStack) (s : sym) (bTy : core_base_type)
      (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f acc ((s, bTy), pe) rs' =
        stExceptUndef_bind (full_eval_pexpr tds th ext σ file pe)
          (fun cval =>
            stExceptUndef_return (update_env (mk_sym_pat s bTy) cval acc)) rs') :
    ∀ (params : List (sym × core_base_type))
      (pes : List (generic_pexpr Unit sym)) {err : core_run_cause}
      (acc : EnvStack) (rs : core_run_state),
      (∀ pe ∈ pes, PePure pe) → (∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) →
      evalClassFold tds th.current_loc ext file th.env (zipArgs params pes) = .kill err →
      stExceptUndef_foldM f acc (List.zip params pes) rs = Exception err :=
  fun params pes {err} acc rs hp hd h =>
    foldM_args_fail f hf params pes (fl := .kill err) acc rs hp hd (by rw [h]; rfl)

/-! ## The operands of a configuration (the residual's witness is one
of them) -/

mutual
/-- The pure operands the engine evaluates at a fragment configuration's
    redex: the guard of `Eif`, the arguments of `Erun` and of `Eproc` (calls
    arc C2), the initializers
    of `Esave`, the operand of a pure exit, the scrutinee of a `case`
    (E2), the pointer operand of a load
    (and the value operand of a store), the operands of a memop; frames
    (`Esseq`/`Ewseq`/`Eannot`) are transparent. -/
def operandsOf : CoreExpr → List (generic_pexpr Unit sym)
  | Expr _ (Esseq _ e1 _) => operandsOf e1
  | Expr _ (Ewseq _ e1 _) => operandsOf e1
  | Expr _ (Eannot _ b) => operandsOf b
  | Expr _ (Eif g _ _) => [g]
  | Expr _ (Erun _ _ pes) => pes
  | Expr _ (Eproc _ _ pes) => pes
  | Expr _ (Esave _ ps _) => saveParamPexprs ps
  | Expr _ (Epure pe) => [pe]
  | Expr _ (Ecase pe _) => [pe]
  | Expr _ (Eaction (Paction _ (Action _ _ (Load0 _ pe2 _)))) => [pe2]
  | Expr _ (Eaction (Paction _ (Action _ _ (Store0 _ _ pe2 pe3 _)))) => [pe2, pe3]
  | Expr _ (Eaction (Paction _ (Action _ _ (Kill _ pe)))) => [pe]
  | Expr _ (Eaction (Paction _ (Action _ _ (Alloc0 pe1 pe2 _)))) => [pe1, pe2]
  | Expr _ (Eaction (Paction _ (Action _ _ (Create pe1 pe2 _)))) => [pe1, pe2]
  | Expr _ (Ememop _ pes) => pes
  | Expr _ (Ebound b) => operandsOf b
  | Expr _ (Eunseq es) => operandsOfU es
  | _ => []
/-- E4: the focused (last reducible) component's operands under the
    `Cunseq` frame (`jumpRedexU?`'s spine); `[]` at all values. -/
def operandsOfU : List CoreExpr → List (generic_pexpr Unit sym)
  | [] => []
  | e :: es => if valsOnly es then operandsOf e else operandsOfU es
end

theorem operandsOfU_focus {es1 : List CoreExpr} {e : CoreExpr} {es2 : List CoreExpr}
    (hnv : toVal e = none) (hv2 : valsOnly es2 = true) :
    operandsOfU (es1 ++ e :: es2) = operandsOf e := by
  induction es1 with
  | nil => simp only [List.nil_append, operandsOfU, hv2, ↓reduceIte]
  | cons x xs ih =>
    simp only [List.cons_append, operandsOfU, valsOnly_append_cons_false hnv, Bool.false_eq_true,
      ↓reduceIte]
    exact ih

/-- A decomposition's frames are transparent to `operandsOf`. -/
theorem Decomp.operandsOf_eq {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) : operandsOf e = operandsOf r := by
  induction hd with
  | root _ => rfl
  | sseq _ ih => exact ih
  | sseq_spec _ ih => exact ih
  | sseq_sym _ ih => exact ih
  | annot _ _ _ _ ih => exact ih
  | wseq _ ih => exact ih
  | bound _ ih => exact ih
  | sseq_tuple _ ih => exact ih
  | wseq_tuple _ ih => exact ih
  | wseq_sym _ ih => exact ih
  | unseq hv2 _ hd ih =>
    rw [show operandsOf (Expr _ (Eunseq _)) = operandsOfU _ from rfl,
      operandsOfU_focus hd.toVal_none hv2]
    exact ih

end CerberusHeapLang
