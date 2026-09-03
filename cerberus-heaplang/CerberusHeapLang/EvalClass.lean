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
  "PEarray_shift: type error ==> …"`). The shipped driver turns the
  exception into the kill `Other (DErr_core_run err)` (`liftCore_run`,
  Driver.lean:245) — a `ShippedRefusal.killed` (Round.lean).
- `EvalOut.uncovered` — the engine SUCCEEDS with a value the mirror does
  not compute, or the outcome is not characterized here: a symbol unbound
  in the environment but naming a `Proc` of the file (the engine returns
  the null function pointer); the eight mirrored binops at two floating
  operands (`opFval`, the float comparisons); `OpEq` at two ctypes
  (`ctypeEqual`); the six non-mirrored binops (`Div`/`Rem_t`/`Rem_f`/
  `Exp` — integer successes; `And`/`Or` — the boolean arms), which
  `PePure` excludes syntactically. `.uncovered` is decided at the FIRST
  uncovered LEAF — the `PEop`/`PEarray_shift` arms propagate a child's
  `.uncovered` without evaluating the rest — so a compound operand with
  an accepted-but-unmirrored leaf is `.uncovered` whatever the engine then
  does with that leaf's value: succeed, KILL (`f + 1` with `f` a
  `Proc`-named unbound symbol is `PePure`, `.uncovered`, and the engine's
  `Illformed_program … ill-typed PEop` — 2026-09-03 audit, by execution),
  or PANIC (a float guard under `Eif`). This is the RESIDUAL of mirror
  completeness (`OpenRound.eval_uncovered`, Round.lean) — a SUPERSET of
  the engine-accepted shapes: every occurrence is environment- or
  file-dependent, so no syntactic narrowing of `Frag` removes it; the
  mover is computing the engine's value at the three leaf shapes here,
  which reserves `.uncovered` for the leaf itself and puts the downstream
  rejections under the KILL bridge.

`evalClass` is a CLASSIFICATION VOCABULARY like `PePure`: it is not a
mirror rule, and it appears in no `Step`. Its `.val` face is the mirror
evaluator (`evalClass_val_iff`); its `.kill` face is certified against
the engine level by level (`step_eval_bridge_kill`, `aux2_bridge_kill`,
`full_eval_bridge_kill`, `eval1_bridge_kill`) in the same shape as the
success bridge; its `.uncovered` face carries no engine claim. The
ill-typed-`PEop` message quotes the PULLED operands (`pull_constrained`
renormalizes annotations before `step_eval_pexpr` runs — `peStrip`),
which is why the classifier strips the children in that message.
-/
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-- The engine's outcome on one operand (module header). -/
inductive EvalOut : Type where
  | val (v : value)
  | kill (err : core_run_cause)
  | uncovered

/-- step_eval_peop's ill-typed-operands exception (Core_eval.lean:135,
    the `_, some _, some _` arm), at the pulled operands. -/
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

/-- The binop dispatch classified (step_eval_peop's value match,
    Core_eval.lean:135): two integers — the mirror's answer at a mirrored
    op, an engine success outside the mirror otherwise; two floats — an
    engine success outside the mirror; two ctypes — a success at `OpEq`,
    ill-typed otherwise; `And`/`Or` — not characterized (outside
    `PePure`); everything else — the ill-typed-`PEop` exception. -/
def binopOut (loc : CerbLocation.Loc) (op : binop) (pe1 pe2 : generic_pexpr Unit sym)
    (v1 v2 : value) : EvalOut :=
  match op, v1, v2 with
  | op, Vobject (OVinteger i1), Vobject (OVinteger i2) =>
      match evalBinop op (Vobject (OVinteger i1)) (Vobject (OVinteger i2)) with
      | some v => EvalOut.val v
      | none => EvalOut.uncovered
  | _, Vobject (OVfloating _), Vobject (OVfloating _) => EvalOut.uncovered
  | .OpEq, Vctype _, Vctype _ => EvalOut.uncovered
  | .OpAnd, _, _ => EvalOut.uncovered
  | .OpOr, _, _ => EvalOut.uncovered
  | op, _, _ => EvalOut.kill (illtypedPEop loc op pe1 pe2)

/-- The array-shift dispatch classified: (pointer, integer) is the
    mirror's answer; anything else is the type error. -/
def shiftOut (tds : CerbTags.TagDefsMap) (ty : ctype) (v1 v2 : value) : EvalOut :=
  match evalArrayShift tds ty v1 v2 with
  | some v => .val v
  | none => .kill (illtypedArrayShift v1 ty v2)

/-- THE CLASSIFIER (module header). Parameters: the tag environment, the
    thread's current location (the engine's `loc1`), the extern map, the
    file (its `funs` decide the procedure-pointer arm) and the
    environment stack. -/
def evalClass (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ext : Fmap sym sym)
    (file : generic_file Unit core_run_annotation) (ρ : EnvStack) :
    generic_pexpr Unit sym → EvalOut
  | Pexpr _ _ (PEval v) => .val v
  | Pexpr _ _ (PEsym x) =>
      match lookup_env (resolveExtern ext x) ρ with
      | some v => .val v
      | none =>
        match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
            (resolveExtern ext x) file.funs with
        | some (Proc _ _ _ _ _) => .uncovered
        | _ => .kill (Unresolved_symbol loc (resolveExtern ext x))
  | Pexpr _ _ (PEop op pe1 pe2) =>
      match evalClass tds loc ext file ρ pe1 with
      | .kill err => .kill err
      | .uncovered => .uncovered
      | .val v1 =>
        match evalClass tds loc ext file ρ pe2 with
        | .kill err => .kill err
        | .uncovered => .uncovered
        | .val v2 => binopOut loc op (peStrip pe1) (peStrip pe2) v1 v2
  | Pexpr _ _ (PEarray_shift pe1 ty pe2) =>
      match evalClass tds loc ext file ρ pe1 with
      | .kill err => .kill err
      | .uncovered => .uncovered
      | .val v1 =>
        match evalClass tds loc ext file ρ pe2 with
        | .kill err => .kill err
        | .uncovered => .uncovered
        | .val v2 => shiftOut tds ty v1 v2
  | _ => .uncovered

/-! ## The `.val` face is the mirror evaluator -/

theorem binopOut_val_iff (loc : CerbLocation.Loc) (op : binop)
    (pe1 pe2 : generic_pexpr Unit sym) (v1 v2 v : value) :
    binopOut loc op pe1 pe2 v1 v2 = .val v ↔ evalBinop op v1 v2 = some v := by
  constructor
  · intro h
    unfold binopOut at h
    split at h
    · revert h
      split <;> intro h
      · cases h; assumption
      · cases h
    all_goals cases h
  · intro h
    have hop := evalBinop_mirrored h
    unfold binopOut
    -- a mirrored op evaluates only at two integers
    unfold evalBinop at h
    split at h <;> first | (cases h; rfl) | cases h

theorem shiftOut_val_iff (tds : CerbTags.TagDefsMap) (ty : ctype) (v1 v2 v : value) :
    shiftOut tds ty v1 v2 = .val v ↔ evalArrayShift tds ty v1 v2 = some v := by
  unfold shiftOut
  constructor
  · intro h
    revert h
    split <;> intro h
    · cases h; assumption
    · cases h
  · intro h
    rw [h]

/-- `evalClass` answers `.val v` exactly where the mirror evaluator
    answers `some v` (at every location and file). -/
theorem evalClass_val_iff (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc)
    (ext : Fmap sym sym) (file : generic_file Unit core_run_annotation) (ρ : EnvStack)
    (pe : generic_pexpr Unit sym) (v : value) :
    evalClass tds loc ext file ρ pe = .val v ↔ evalPexpr tds ext ρ pe = some v := by
  induction pe using evalPexpr.induct generalizing v with
  | case1 a u v' =>
    cases u
    show EvalOut.val v' = EvalOut.val v ↔ some v' = some v
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  | case2 a u x =>
    cases u
    show (match lookup_env (resolveExtern ext x) ρ with
      | some v => EvalOut.val v
      | none => match fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
            Lem_Basic_classes.ordCompare s1 s2) (resolveExtern ext x) file.funs with
        | some (Proc _ _ _ _ _) => EvalOut.uncovered
        | _ => EvalOut.kill (Unresolved_symbol loc (resolveExtern ext x))) = EvalOut.val v ↔
      lookup_env (resolveExtern ext x) ρ = some v
    cases hl : lookup_env (resolveExtern ext x) ρ with
    | some w =>
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; rfl
    | none =>
      cases hf : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
          Lem_Basic_classes.ordCompare s1 s2) (resolveExtern ext x) file.funs with
      | none => constructor <;> intro h <;> cases h
      | some d => cases d <;> constructor <;> intro h <;> cases h
  | case3 a u op pe1 pe2 ih1 ih2 =>
    cases u
    show (match evalClass tds loc ext file ρ pe1 with
      | .kill err => EvalOut.kill err
      | .uncovered => EvalOut.uncovered
      | .val v1 =>
        match evalClass tds loc ext file ρ pe2 with
        | .kill err => EvalOut.kill err
        | .uncovered => EvalOut.uncovered
        | .val v2 => binopOut loc op (peStrip pe1) (peStrip pe2) v1 v2) = EvalOut.val v ↔ _
    rw [evalPexpr_op]
    cases h1 : evalClass tds loc ext file ρ pe1 with
    | val v1 =>
      rw [(ih1 v1).mp h1]
      cases h2 : evalClass tds loc ext file ρ pe2 with
      | val v2 =>
        rw [(ih2 v2).mp h2]
        exact binopOut_val_iff loc op _ _ v1 v2 v
      | kill err =>
        have h2' : evalPexpr tds ext ρ pe2 = none := by
          cases h2' : evalPexpr tds ext ρ pe2 with
          | none => rfl
          | some w => rw [← ih2 w, h2] at h2'; cases h2'
        rw [h2']
        constructor <;> intro h <;> cases h
      | uncovered =>
        have h2' : evalPexpr tds ext ρ pe2 = none := by
          cases h2' : evalPexpr tds ext ρ pe2 with
          | none => rfl
          | some w => rw [← ih2 w, h2] at h2'; cases h2'
        rw [h2']
        constructor <;> intro h <;> cases h
    | kill err =>
      have h1' : evalPexpr tds ext ρ pe1 = none := by
        cases h1' : evalPexpr tds ext ρ pe1 with
        | none => rfl
        | some w => rw [← ih1 w, h1] at h1'; cases h1'
      rw [h1']
      constructor <;> intro h <;> cases h
    | uncovered =>
      have h1' : evalPexpr tds ext ρ pe1 = none := by
        cases h1' : evalPexpr tds ext ρ pe1 with
        | none => rfl
        | some w => rw [← ih1 w, h1] at h1'; cases h1'
      rw [h1']
      constructor <;> intro h <;> cases h
  | case4 a u pe1 ty pe2 ih1 ih2 =>
    cases u
    show (match evalClass tds loc ext file ρ pe1 with
      | .kill err => EvalOut.kill err
      | .uncovered => EvalOut.uncovered
      | .val v1 =>
        match evalClass tds loc ext file ρ pe2 with
        | .kill err => EvalOut.kill err
        | .uncovered => EvalOut.uncovered
        | .val v2 => shiftOut tds ty v1 v2) = EvalOut.val v ↔ _
    rw [evalPexpr_array_shift]
    cases h1 : evalClass tds loc ext file ρ pe1 with
    | val v1 =>
      rw [(ih1 v1).mp h1]
      cases h2 : evalClass tds loc ext file ρ pe2 with
      | val v2 =>
        rw [(ih2 v2).mp h2]
        exact shiftOut_val_iff tds ty v1 v2 v
      | kill err =>
        have h2' : evalPexpr tds ext ρ pe2 = none := by
          cases h2' : evalPexpr tds ext ρ pe2 with
          | none => rfl
          | some w => rw [← ih2 w, h2] at h2'; cases h2'
        rw [h2']
        constructor <;> intro h <;> cases h
      | uncovered =>
        have h2' : evalPexpr tds ext ρ pe2 = none := by
          cases h2' : evalPexpr tds ext ρ pe2 with
          | none => rfl
          | some w => rw [← ih2 w, h2] at h2'; cases h2'
        rw [h2']
        constructor <;> intro h <;> cases h
    | kill err =>
      have h1' : evalPexpr tds ext ρ pe1 = none := by
        cases h1' : evalPexpr tds ext ρ pe1 with
        | none => rfl
        | some w => rw [← ih1 w, h1] at h1'; cases h1'
      rw [h1']
      constructor <;> intro h <;> cases h
    | uncovered =>
      have h1' : evalPexpr tds ext ρ pe1 = none := by
        cases h1' : evalPexpr tds ext ρ pe1 with
        | none => rfl
        | some w => rw [← ih1 w, h1] at h1'; cases h1'
      rw [h1']
      constructor <;> intro h <;> cases h
  | case5 pe hne1 hne2 hne3 hne4 =>
    rw [evalPexpr_none_of_shape hne1 hne2 hne3 hne4]
    have : evalClass tds loc ext file ρ pe = .uncovered := by
      unfold evalClass
      split
      · exact absurd rfl (hne1 _ _ _)
      · exact absurd rfl (hne2 _ _ _)
      · exact absurd rfl (hne3 _ _ _ _ _)
      · exact absurd rfl (hne4 _ _ _ _ _)
      · rfl
    rw [this]
    constructor <;> intro h <;> cases h

/-- Where the mirror answers `none`, the classifier answers a kill or
    the residual. -/
theorem evalClass_of_none {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} (loc : CerbLocation.Loc)
    (file : generic_file Unit core_run_annotation)
    (h : evalPexpr tds ext ρ pe = none) :
    (∃ err, evalClass tds loc ext file ρ pe = .kill err) ∨
    evalClass tds loc ext file ρ pe = .uncovered := by
  cases hc : evalClass tds loc ext file ρ pe with
  | val v => rw [(evalClass_val_iff tds loc ext file ρ pe v).mp hc] at h; cases h
  | kill err => exact .inl ⟨err, rfl⟩
  | uncovered => exact .inr rfl

theorem evalPexpr_none_of_kill {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym} {ρ : EnvStack}
    {pe : generic_pexpr Unit sym} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation} {err : core_run_cause}
    (h : evalClass tds loc ext file ρ pe = .kill err) :
    evalPexpr tds ext ρ pe = none := by
  cases hv : evalPexpr tds ext ρ pe with
  | none => rfl
  | some v => rw [← evalClass_val_iff tds loc ext file ρ pe v, h] at hv; cases hv

theorem evalPexpr_none_of_uncovered {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {ρ : EnvStack} {pe : generic_pexpr Unit sym} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    (h : evalClass tds loc ext file ρ pe = .uncovered) :
    evalPexpr tds ext ρ pe = none := by
  cases hv : evalPexpr tds ext ρ pe with
  | none => rfl
  | some v => rw [← evalClass_val_iff tds loc ext file ρ pe v, h] at hv; cases hv

/-! ## Annotation renormalization is invisible to the classifier -/

theorem peStrip_idem {pe : generic_pexpr Unit _root_.sym} (hp : PePure pe) :
    peStrip (peStrip pe) = peStrip pe := by
  induction hp with
  | val a v => rfl
  | sym a x => rfl
  | op a op hop hp1 hp2 ih1 ih2 =>
    show Pexpr [] () (PEop op (peStrip (peStrip _)) (peStrip (peStrip _))) = _
    rw [ih1, ih2]
    rfl
  | arrayShift a ty hp1 hp2 ih1 ih2 =>
    show Pexpr [] () (PEarray_shift (peStrip (peStrip _)) ty (peStrip (peStrip _))) = _
    rw [ih1, ih2]
    rfl

theorem evalClass_peStrip {tds : CerbTags.TagDefsMap} {loc : CerbLocation.Loc}
    {ext : Fmap sym sym} {file : generic_file Unit core_run_annotation} {ρ : EnvStack}
    {pe : generic_pexpr Unit _root_.sym} (hp : PePure pe) :
    evalClass tds loc ext file ρ (peStrip pe) = evalClass tds loc ext file ρ pe := by
  induction hp with
  | val a v => rfl
  | sym a x => rfl
  | @op a op hop pe1 pe2 hp1 hp2 ih1 ih2 =>
    show (match evalClass tds loc ext file ρ (peStrip pe1) with
      | .kill err => EvalOut.kill err
      | .uncovered => EvalOut.uncovered
      | .val v1 =>
        match evalClass tds loc ext file ρ (peStrip pe2) with
        | .kill err => EvalOut.kill err
        | .uncovered => EvalOut.uncovered
        | .val v2 => binopOut loc op (peStrip (peStrip pe1)) (peStrip (peStrip pe2)) v1 v2) = _
    rw [ih1, ih2, peStrip_idem hp1, peStrip_idem hp2]
    rfl
  | @arrayShift a ty pe1 pe2 hp1 hp2 ih1 ih2 =>
    show (match evalClass tds loc ext file ρ (peStrip pe1) with
      | .kill err => EvalOut.kill err
      | .uncovered => EvalOut.uncovered
      | .val v1 =>
        match evalClass tds loc ext file ρ (peStrip pe2) with
        | .kill err => EvalOut.kill err
        | .uncovered => EvalOut.uncovered
        | .val v2 => shiftOut tds ty v1 v2) = _
    rw [ih1, ih2]
    rfl

/-! ## The exception monad's failure laws -/

theorem fail0_eq {a b : Type} (err : b) : (fail0 err : exceptM a b) = Exception err := rfl

theorem exception_undef_bind_exception {a b c : Type} (err : b)
    (f : c → exceptM (t0 a) b) :
    exception_undef_bind (Exception err) f = Exception err := rfl

theorem exception_undef_fmap_exception {a b c : Type} (f : a → b) (err : c) :
    exception_undef_fmap f (Exception err) = Exception err := rfl


/-! ## THE KILL BRIDGE, level by level (the failure twin of the success
bridge in Soundness.lean: `step_eval_bridge` → `aux2_bridge` →
`full_eval_bridge`/`eval1_bridge`) -/

/-- LEVEL 1: where the classifier answers `.kill err` at a STRIPPED
    operand (`peStrip pe = pe` — the shape `pull_constrained` hands to
    `step_eval_pexpr`), the engine's one-call evaluator RAISES exactly
    `err`. Quantified over the level counter, the call location, the
    memory state; the current location `loc` and the file are READ (the
    `Unresolved_symbol` payload and the procedure-pointer arm). -/
theorem step_eval_bridge_kill {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {err : core_run_cause}
    (hp : PePure pe) (hs : peStrip pe = pe)
    (hk : evalClass tds loc ext file ρ pe = .kill err) :
    ∀ (fuel : Nat), peDepth pe ≤ fuel →
    ∀ (n : Nat) (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    step_eval_pexpr_lemFuel fuel tds n loc cloc ext ρ mem file false pe =
      Exception err := by
  induction hp generalizing err with
  | val a v =>
    exact absurd hk (by simp [evalClass])
  | sym a x =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by have := peDepth_pos (Pexpr a () (PEsym x)); omega⟩
    have hk' : (match lookup_env (resolveExtern ext x) ρ with
      | some v => EvalOut.val v
      | none =>
        match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
            (resolveExtern ext x) file.funs with
        | some (Proc _ _ _ _ _) => EvalOut.uncovered
        | _ => EvalOut.kill (Unresolved_symbol loc (resolveExtern ext x))) =
        EvalOut.kill err := hk
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases hres : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
        Lem_Basic_classes.ordCompare s1 s2) x ext with
    | none =>
      rw [show resolveExtern ext x = x by unfold resolveExtern; rw [hres]] at hk'
      dsimp only
      cases hl : lookup_env x ρ with
      | some v => rw [hl] at hk'; cases hk'
      | none =>
        rw [hl] at hk'
        cases hf : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
            Lem_Basic_classes.ordCompare s1 s2) x file.funs with
        | none => rw [hf] at hk'; cases hk'; rfl
        | some d =>
          rw [hf] at hk'
          cases d with
          | Proc _ _ _ _ _ => cases hk'
          | Fun _ _ _ => cases hk'; rfl
          | ProcDecl _ _ _ => cases hk'; rfl
          | BuiltinDecl _ _ _ => cases hk'; rfl
    | some y =>
      rw [show resolveExtern ext x = y by unfold resolveExtern; rw [hres]] at hk'
      dsimp only
      cases hl : lookup_env y ρ with
      | some v => rw [hl] at hk'; cases hk'
      | none =>
        rw [hl] at hk'
        cases hf : fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
            Lem_Basic_classes.ordCompare s1 s2) y file.funs with
        | none => rw [hf] at hk'; cases hk'; rfl
        | some d =>
          rw [hf] at hk'
          cases d with
          | Proc _ _ _ _ _ => cases hk'
          | Fun _ _ _ => cases hk'; rfl
          | ProcDecl _ _ _ => cases hk'; rfl
          | BuiltinDecl _ _ _ => cases hk'; rfl
  | @op a op hop pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    have hs' : Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2)) =
        Pexpr a () (PEop op pe1 pe2) := hs
    injection hs' with ha hu hpe
    injection hpe with hop' h1 h2
    subst ha
    have hk' : (match evalClass tds loc ext file ρ pe1 with
      | .kill e => EvalOut.kill e
      | .uncovered => EvalOut.uncovered
      | .val v1 =>
        match evalClass tds loc ext file ρ pe2 with
        | .kill e => EvalOut.kill e
        | .uncovered => EvalOut.uncovered
        | .val v2 => binopOut loc op (peStrip pe1) (peStrip pe2) v1 v2) =
        EvalOut.kill err := hk
    rw [h1, h2] at hk'
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only [step_eval_peop]
    cases hc1 : evalClass tds loc ext file ρ pe1 with
    | kill e1 =>
      rw [hc1] at hk'
      cases hk'
      rw [ih1 h1 hc1 f hd1 (n+1) cloc mem]
      rfl
    | uncovered => rw [hc1] at hk'; cases hk'
    | val v1 =>
      rw [hc1] at hk'
      have hv1 := (evalClass_val_iff tds loc ext file ρ pe1 v1).mp hc1
      rw [step_eval_bridge hp1 hv1 f hd1 (n+1) loc cloc mem file]
      cases hc2 : evalClass tds loc ext file ρ pe2 with
      | kill e2 =>
        rw [hc2] at hk'
        cases hk'
        rw [ih2 h2 hc2 f hd2 (n+1) cloc mem]
        rfl
      | uncovered => rw [hc2] at hk'; cases hk'
      | val v2 =>
        rw [hc2] at hk'
        have hv2 := (evalClass_val_iff tds loc ext file ρ pe2 v2).mp hc2
        rw [step_eval_bridge hp2 hv2 f hd2 (n+1) loc cloc mem file]
        dsimp only [exception_undef_bind, exception_undef_return,
          exception_undef_fmap, valueFromPexpr]
        -- the binop dispatch: the mirrored operator (`hop`) at every
        -- pair of value shapes; the engine's arm and the classifier's
        -- agree case by case
        cases op <;> (try (cases hop)) <;>
          rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
          rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov2)) <;>
          (dsimp only [binopOut] at hk'
           first
           | (cases hk'; rfl)
           | (cases hk')
           | (split at hk' <;> cases hk'))
  | @arrayShift a ty pe1 pe2 hp1 hp2 ih1 ih2 =>
    intro fuel hfuel n cloc mem
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hd1 : peDepth pe1 ≤ f := by simp at hfuel; omega
    have hd2 : peDepth pe2 ≤ f := by simp at hfuel; omega
    have hs' : Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2)) =
        Pexpr a () (PEarray_shift pe1 ty pe2) := hs
    injection hs' with ha hu hpe
    injection hpe with h1 hty h2
    subst ha
    have hk' : (match evalClass tds loc ext file ρ pe1 with
      | .kill e => EvalOut.kill e
      | .uncovered => EvalOut.uncovered
      | .val v1 =>
        match evalClass tds loc ext file ρ pe2 with
        | .kill e => EvalOut.kill e
        | .uncovered => EvalOut.uncovered
        | .val v2 => shiftOut tds ty v1 v2) = EvalOut.kill err := hk
    show exception_undef_fmap (Pexpr [] ()) _ = _
    dsimp only
    cases hc1 : evalClass tds loc ext file ρ pe1 with
    | kill e1 =>
      rw [hc1] at hk'
      cases hk'
      rw [ih1 h1 hc1 f hd1 (n+1) cloc mem]
      rfl
    | uncovered => rw [hc1] at hk'; cases hk'
    | val v1 =>
      rw [hc1] at hk'
      have hv1 := (evalClass_val_iff tds loc ext file ρ pe1 v1).mp hc1
      rw [step_eval_bridge hp1 hv1 f hd1 (n+1) loc cloc mem file]
      cases hc2 : evalClass tds loc ext file ρ pe2 with
      | kill e2 =>
        rw [hc2] at hk'
        cases hk'
        rw [ih2 h2 hc2 f hd2 (n+1) cloc mem]
        rfl
      | uncovered => rw [hc2] at hk'; cases hk'
      | val v2 =>
        rw [hc2] at hk'
        dsimp only at hk'
        have hv2 := (evalClass_val_iff tds loc ext file ρ pe2 v2).mp hc2
        rw [step_eval_bridge hp2 hv2 f hd2 (n+1) loc cloc mem file]
        dsimp only [exception_undef_bind, exception_undef_return,
          exception_undef_fmap, valueFromPexpr]
        unfold shiftOut at hk'
        cases hb : evalArrayShift tds ty v1 v2 with
        | some w => rw [hb] at hk'; cases hk'
        | none =>
          rw [hb] at hk'
          cases hk'
          rcases v1 with ov1 | lv1 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov1)) <;>
          rcases v2 with ov2 | lv2 | _ | _ | _ | _ | ⟨_, _⟩ | _ <;> (try (cases ov2)) <;>
            first
            | rfl
            | (cases hb)

/-- LEVEL 3a: `eval_pexpr_aux2` (one iteration: pull, then one
    full-depth `step_eval`) RAISES the classified exception. -/
theorem aux2_bridge_kill {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {ext : Fmap sym sym} {ρ : EnvStack} {loc : CerbLocation.Loc}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {err : core_run_cause}
    (hp : PePure pe) (hk : evalClass tds loc ext file ρ pe = .kill err)
    (hd : peDepth pe ≤ lemDefaultFuel) :
    ∀ (fuel : Nat) (cloc : Option CerbLocation.Loc) (mem : Option CerbMem.MemState),
    eval_pexpr_aux2_lemFuel (fuel + 1) tds loc cloc ext ρ mem file pe = Exception err := by
  intro fuel cloc mem
  have hpull : pull_constrained 0 pe = peStrip pe :=
    pull_bridge hp lemDefaultFuel hd 0
  have hstep := step_eval_bridge_kill hp.strip (peStrip_idem hp)
    (by rw [evalClass_peStrip hp]; exact hk) lemDefaultFuel
    (by rw [peDepth_peStrip hp]; exact hd) 0 cloc mem
  unfold eval_pexpr_aux2_lemFuel
  dsimp only [CerbDebug.print_debug_pure]
  rw [hpull]
  cases hp with
  | val a v' =>
    rw [show peStrip (Pexpr a () (PEval v')) = Pexpr [] () (PEval v') from rfl]
    rw [show peStrip (Pexpr a () (PEval v')) = Pexpr [] () (PEval v')
      from rfl] at hstep
    dsimp only
    rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl,
      hstep]
    rfl
  | sym a x =>
    rw [show peStrip (Pexpr a () (PEsym x)) = Pexpr [] () (PEsym x) from rfl]
    rw [show peStrip (Pexpr a () (PEsym x)) = Pexpr [] () (PEsym x)
      from rfl] at hstep
    dsimp only
    rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl,
      hstep]
    rfl
  | @op a op hop pe1 pe2 hp1 hp2 =>
    rw [show peStrip (Pexpr a () (PEop op pe1 pe2)) =
      Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2)) from rfl]
    rw [show peStrip (Pexpr a () (PEop op pe1 pe2)) =
      Pexpr [] () (PEop op (peStrip pe1) (peStrip pe2)) from rfl] at hstep
    dsimp only
    rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl,
      hstep]
    rfl
  | @arrayShift a ty pe1 pe2 hp1 hp2 =>
    rw [show peStrip (Pexpr a () (PEarray_shift pe1 ty pe2)) =
      Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2)) from rfl]
    rw [show peStrip (Pexpr a () (PEarray_shift pe1 ty pe2)) =
      Pexpr [] () (PEarray_shift (peStrip pe1) ty (peStrip pe2)) from rfl]
      at hstep
    dsimp only
    rw [show step_eval_pexpr = step_eval_pexpr_lemFuel lemDefaultFuel from rfl,
      hstep]
    rfl

/-- LEVEL 3b: `full_eval_pexpr` (the Eif/Erun/action-operand evaluator)
    RAISES the classified exception at every run state. -/
theorem full_eval_bridge_kill {tds : Fmap sym (CerbLocation.Loc × tag_definition)}
    {b : Type} {ext : Fmap sym sym} {th : thread_state}
    {file : generic_file Unit core_run_annotation}
    {pe : generic_pexpr Unit sym} {err : core_run_cause}
    (hp : PePure pe)
    (hk : evalClass tds th.current_loc ext file th.env pe = .kill err)
    (hd : peDepth pe ≤ lemDefaultFuel) (σ : CerbMem.MemState) :
    full_eval_pexpr (b := b) tds th ext σ file pe = fun _ => Exception err := by
  rw [show (full_eval_pexpr (b := b) tds th ext σ file pe) =
    full_eval_pexpr_lemFuel (b := b) (999999 + 1) tds th ext σ file pe
    from rfl]
  show stExceptUndef_bind _ _ = _
  funext st
  show (match E.eval_pexpr20 tds th ext σ file pe st with
    | _ => _ : exceptM _ _) = _
  rw [show E.eval_pexpr20 (a := b) tds th ext σ file pe =
    runEU ((eval_pexpr_aux2 tds) th.current_loc
      (match th.exec_loc with
        | ELoc_globals => none
        | ELoc_normal [] => none
        | ELoc_normal ((_, loc1) :: _) => some loc1)
      ext th.env (some σ) file pe) from rfl]
  rw [show (eval_pexpr_aux2 (tds)) = eval_pexpr_aux2_lemFuel (999999 + 1) tds
    from rfl]
  rw [aux2_bridge_kill hp hk hd 999999 _ (some σ)]
  rfl

/-- The one-iteration evaluator under its `Sum` readout (step_ctx's
    `eval_pexpr1`, Core_reduction.lean:484 — the Ememop/Esave operand
    evaluator) RAISES the classified exception. -/
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
      Exception err := by
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
  rw [aux2_bridge_kill hp hk hd 999999 _ (some σ)]
  rfl

/-! ## Operand LISTS: the first non-value operand decides -/

/-- The engine's outcome on an operand list, evaluated left to right
    (the `stExceptUndef_mapM`/`stExceptUndef_foldM` order): all values,
    or the FIRST operand that is not a value — a kill, or the residual
    (the operand is carried as the witness). -/
inductive EvalListOut : Type where
  | vals (vs : List value)
  | kill (err : core_run_cause)
  | uncovered (pe : generic_pexpr Unit sym)

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
      | .uncovered pe' => .uncovered pe'

theorem evalClassList_vals_iff (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc)
    (ext : Fmap sym sym) (file : generic_file Unit core_run_annotation) (ρ : EnvStack)
    (pes : List (generic_pexpr Unit sym)) (vs : List value) :
    evalClassList tds loc ext file ρ pes = .vals vs ↔ evalPexprs tds ext ρ pes = some vs := by
  induction pes generalizing vs with
  | nil =>
    show EvalListOut.vals [] = EvalListOut.vals vs ↔ some [] = some vs
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  | cons pe pes ih =>
    show (match evalClass tds loc ext file ρ pe with
      | .kill err => EvalListOut.kill err
      | .uncovered => EvalListOut.uncovered pe
      | .val v =>
        match evalClassList tds loc ext file ρ pes with
        | .vals vs => EvalListOut.vals (v :: vs)
        | .kill err => EvalListOut.kill err
        | .uncovered pe' => EvalListOut.uncovered pe') = EvalListOut.vals vs ↔ _
    rw [evalPexprs_cons]
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
        have : evalPexprs tds ext ρ pes = none := by
          cases h' : evalPexprs tds ext ρ pes with
          | none => rfl
          | some w => rw [← ih w, hl] at h'; cases h'
        rw [this]
        constructor <;> intro h <;> cases h
      | uncovered pe' =>
        have : evalPexprs tds ext ρ pes = none := by
          cases h' : evalPexprs tds ext ρ pes with
          | none => rfl
          | some w => rw [← ih w, hl] at h'; cases h'
        rw [this]
        constructor <;> intro h <;> cases h
    | kill err =>
      rw [evalPexpr_none_of_kill hc]
      constructor <;> intro h <;> cases h
    | uncovered =>
      rw [evalPexpr_none_of_uncovered hc]
      constructor <;> intro h <;> cases h

theorem evalClassList_uncovered {tds : CerbTags.TagDefsMap} {loc : CerbLocation.Loc}
    {ext : Fmap sym sym} {file : generic_file Unit core_run_annotation} {ρ : EnvStack}
    {pes : List (generic_pexpr Unit sym)} {pe : generic_pexpr Unit sym}
    (h : evalClassList tds loc ext file ρ pes = .uncovered pe) :
    pe ∈ pes ∧ evalClass tds loc ext file ρ pe = .uncovered := by
  induction pes with
  | nil => cases h
  | cons pe' pes ih =>
    have h' : (match evalClass tds loc ext file ρ pe' with
      | .kill err => EvalListOut.kill err
      | .uncovered => EvalListOut.uncovered pe'
      | .val v =>
        match evalClassList tds loc ext file ρ pes with
        | .vals vs => EvalListOut.vals (v :: vs)
        | .kill err => EvalListOut.kill err
        | .uncovered pe'' => EvalListOut.uncovered pe'') = EvalListOut.uncovered pe := h
    cases hc : evalClass tds loc ext file ρ pe' with
    | val v =>
      rw [hc] at h'
      cases hl : evalClassList tds loc ext file ρ pes with
      | vals vs => rw [hl] at h'; cases h'
      | kill err => rw [hl] at h'; cases h'
      | uncovered pe'' =>
        rw [hl] at h'
        cases h'
        obtain ⟨hm, hu⟩ := ih hl
        exact ⟨List.mem_cons_of_mem _ hm, hu⟩
    | kill err => rw [hc] at h'; cases h'
    | uncovered =>
      rw [hc] at h'
      cases h'
      exact ⟨List.mem_cons_self .., hc⟩

theorem evalClassList_of_none {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {ρ : EnvStack} {pes : List (generic_pexpr Unit sym)} (loc : CerbLocation.Loc)
    (file : generic_file Unit core_run_annotation)
    (h : evalPexprs tds ext ρ pes = none) :
    (∃ err, evalClassList tds loc ext file ρ pes = .kill err) ∨
    (∃ pe, evalClassList tds loc ext file ρ pes = .uncovered pe) := by
  cases hc : evalClassList tds loc ext file ρ pes with
  | vals vs => rw [(evalClassList_vals_iff tds loc ext file ρ pes vs).mp hc] at h; cases h
  | kill err => exact .inl ⟨err, rfl⟩
  | uncovered pe => exact .inr ⟨pe, rfl⟩

/-- The Ememop/Esave operand map (`stExpect_mapM` over the one-iteration
    evaluator) RAISES the first classified kill. The per-operand body is
    abstract with a pointwise characterization (`mapM_eval1_bridge`'s
    pattern). -/
theorem stExpect_mapM_eval1_kill {ext : Fmap sym sym} {th : thread_state}
    {tds : Fmap sym (CerbLocation.Loc × tag_definition)} {σ : Mem}
    {file : generic_file Unit core_run_annotation}
    (f : generic_pexpr Unit sym → core_run_state →
      exceptM ((t0 (generic_pexpr Unit sym) × core_run_state)) core_run_cause)
    (hf : ∀ (pe : generic_pexpr Unit sym) (rs' : core_run_state),
      f pe rs' = stExceptUndef_bind
        (E.eval_pexpr20 (a := core_run_state) tds th ext σ file pe)
        (fun x => match x with
          | Sum.inl pe' => stExceptUndef_return pe'
          | Sum.inr cval => stExceptUndef_return (mk_value_pe cval)) rs') :
    ∀ (pes : List (generic_pexpr Unit sym)) {err : core_run_cause},
      (∀ pe ∈ pes, PePure pe) → (∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) →
      evalClassList tds th.current_loc ext file th.env pes = .kill err →
      ∀ rs, stExpect_mapM f pes rs = Exception err := by
  intro pes
  induction pes with
  | nil => intro err _ _ h; cases h
  | cons pe pes ih =>
    intro err hp hd h rs
    have h' : (match evalClass tds th.current_loc ext file th.env pe with
      | .kill err => EvalListOut.kill err
      | .uncovered => EvalListOut.uncovered pe
      | .val v =>
        match evalClassList tds th.current_loc ext file th.env pes with
        | .vals vs => EvalListOut.vals (v :: vs)
        | .kill err => EvalListOut.kill err
        | .uncovered pe' => EvalListOut.uncovered pe') = EvalListOut.kill err := h
    have hpe : PePure pe := hp pe (List.mem_cons_self ..)
    have hde : peDepth pe ≤ lemDefaultFuel := hd pe (List.mem_cons_self ..)
    rw [show stExpect_mapM f (pe :: pes) =
      stExpect_bind (f pe) (fun x =>
        stExpect_bind (stExpect_mapM f pes) (fun xs =>
          stExpect_return (x :: xs))) from rfl]
    cases hc : evalClass tds th.current_loc ext file th.env pe with
    | kill e =>
      rw [hc] at h'
      cases h'
      rw [stExpect_bind_apply, hf pe rs, eval1_bridge_kill hpe hc hde σ _ rs]
    | uncovered => rw [hc] at h'; cases h'
    | val v =>
      rw [hc] at h'
      have hv := (evalClass_val_iff tds th.current_loc ext file th.env pe v).mp hc
      have hres : f pe rs = Result (Defined (mk_value_pe v), rs) :=
        (hf pe rs).trans (eval1_bridge hv hde σ file rs)
      rw [stExpect_bind_result _ _ _ _ _ hres]
      cases hl : evalClassList tds th.current_loc ext file th.env pes with
      | vals vs => rw [hl] at h'; cases h'
      | uncovered pe' => rw [hl] at h'; cases h'
      | kill e =>
        rw [hl] at h'
        cases h'
        rw [stExpect_bind_apply,
          ih (fun pe' hpe' => hp pe' (List.mem_cons_of_mem _ hpe'))
            (fun pe' hpe' => hd pe' (List.mem_cons_of_mem _ hpe')) hl rs]

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
    stExceptUndef_mapM f pes rs = Exception err := by
  unfold stExceptUndef_mapM
  rw [stExpect_bind_apply, stExpect_mapM_eval1_kill f hf pes hp hd h rs]

/-- The Esave parameter map (`mapM_save_bridge`'s shape) RAISES the first
    classified kill among the initializers. -/
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
    stExceptUndef_mapM g ps rs = Exception err := by
  have hmap : stExpect_mapM g ps rs = Exception err := by
    induction ps with
    | nil => cases h
    | cons p ps ih =>
      have h' : (match evalClass tds th.current_loc ext file th.env p.2.2 with
        | .kill err => EvalListOut.kill err
        | .uncovered => EvalListOut.uncovered p.2.2
        | .val v =>
          match evalClassList tds th.current_loc ext file th.env (saveParamPexprs ps) with
          | .vals vs => EvalListOut.vals (v :: vs)
          | .kill err => EvalListOut.kill err
          | .uncovered pe' => EvalListOut.uncovered pe') = EvalListOut.kill err := h
      have hpe : PePure p.2.2 := hp _ (List.mem_cons_self ..)
      have hde : peDepth p.2.2 ≤ lemDefaultFuel := hd _ (List.mem_cons_self ..)
      rw [show stExpect_mapM g (p :: ps) =
        stExpect_bind (g p) (fun x =>
          stExpect_bind (stExpect_mapM g ps) (fun xs =>
            stExpect_return (x :: xs))) from rfl]
      cases hc : evalClass tds th.current_loc ext file th.env p.2.2 with
      | kill e =>
        rw [hc] at h'
        cases h'
        rw [stExpect_bind_apply, hg p rs, stExceptUndef_bind_apply, hf _ rs,
          eval1_bridge_kill hpe hc hde σ _ rs]
        rfl
      | uncovered => rw [hc] at h'; cases h'
      | val v =>
        rw [hc] at h'
        have hv := (evalClass_val_iff tds th.current_loc ext file th.env p.2.2 v).mp hc
        have hres : g p rs = Result (Defined (p.1, (p.2.1, mk_value_pe v)), rs) := by
          rw [hg p rs, stExceptUndef_bind_apply,
            (hf _ rs).trans (eval1_bridge hv hde σ file rs)]
          rfl
        rw [stExpect_bind_result _ _ _ _ _ hres]
        cases hl : evalClassList tds th.current_loc ext file th.env (saveParamPexprs ps) with
        | vals vs => rw [hl] at h'; cases h'
        | uncovered pe' => rw [hl] at h'; cases h'
        | kill e =>
          rw [hl] at h'
          cases h'
          rw [stExpect_bind_apply,
            ih (fun pe' hpe' => hp pe' (List.mem_cons_of_mem _ hpe'))
              (fun pe' hpe' => hd pe' (List.mem_cons_of_mem _ hpe')) hl]
  unfold stExceptUndef_mapM
  rw [stExpect_bind_apply, hmap]

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

/-- The Erun argument fold RAISES the first classified kill among the
    zipped arguments (`foldM_args_bridge`'s shape). -/
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
      evalClassList tds th.current_loc ext file th.env (zipArgs params pes) = .kill err →
      stExceptUndef_foldM f acc (List.zip params pes) rs = Exception err := by
  intro params
  induction params with
  | nil => intro pes err acc rs _ _ h; cases h
  | cons p params ih =>
    intro pes err acc rs hp hd h
    cases pes with
    | nil => cases h
    | cons pe pes =>
      have h' : (match evalClass tds th.current_loc ext file th.env pe with
        | .kill err => EvalListOut.kill err
        | .uncovered => EvalListOut.uncovered pe
        | .val v =>
          match evalClassList tds th.current_loc ext file th.env (zipArgs params pes) with
          | .vals vs => EvalListOut.vals (v :: vs)
          | .kill err => EvalListOut.kill err
          | .uncovered pe' => EvalListOut.uncovered pe') = EvalListOut.kill err := h
      have hpe : PePure pe := hp pe (List.mem_cons_self ..)
      have hde : peDepth pe ≤ lemDefaultFuel := hd pe (List.mem_cons_self ..)
      obtain ⟨p1, p2⟩ := p
      rw [List.zip_cons_cons, stExceptUndef_foldM_cons, stExceptUndef_bind_apply,
        hf acc p1 p2 pe rs, stExceptUndef_bind_apply]
      cases hc : evalClass tds th.current_loc ext file th.env pe with
      | kill e =>
        rw [hc] at h'
        cases h'
        rw [full_eval_bridge_kill hpe hc hde σ]
        rfl
      | uncovered => rw [hc] at h'; cases h'
      | val v =>
        rw [hc] at h'
        have hv := (evalClass_val_iff tds th.current_loc ext file th.env pe v).mp hc
        rw [full_eval_bridge hv hde σ file, stExceptUndef_return_apply]
        dsimp only []
        rw [stExceptUndef_return_apply]
        dsimp only []
        cases hl : evalClassList tds th.current_loc ext file th.env (zipArgs params pes) with
        | vals vs => rw [hl] at h'; cases h'
        | uncovered pe' => rw [hl] at h'; cases h'
        | kill e =>
          rw [hl] at h'
          cases h'
          exact ih pes _ rs (fun pe' hpe' => hp pe' (List.mem_cons_of_mem _ hpe'))
            (fun pe' hpe' => hd pe' (List.mem_cons_of_mem _ hpe')) hl


/-! ## The operands of a configuration (the residual's witness is one
of them) -/

/-- The pure operands the engine evaluates at a fragment configuration's
    redex: the guard of `Eif`, the arguments of `Erun`, the initializers
    of `Esave`, the operand of a pure exit, the pointer operand of a load
    (and the value operand of a store), the operands of a memop; frames
    (`Esseq`/`Ewseq`/`Eannot`) are transparent. -/
def operandsOf : CoreExpr → List (generic_pexpr Unit sym)
  | Expr _ (Esseq _ e1 _) => operandsOf e1
  | Expr _ (Ewseq _ e1 _) => operandsOf e1
  | Expr _ (Eannot _ b) => operandsOf b
  | Expr _ (Eif g _ _) => [g]
  | Expr _ (Erun _ _ pes) => pes
  | Expr _ (Esave _ ps _) => saveParamPexprs ps
  | Expr _ (Epure pe) => [pe]
  | Expr _ (Eaction (Paction _ (Action _ _ (Load0 _ pe2 _)))) => [pe2]
  | Expr _ (Eaction (Paction _ (Action _ _ (Store0 _ _ pe2 pe3 _)))) => [pe2, pe3]
  | Expr _ (Eaction (Paction _ (Action _ _ (Kill _ pe)))) => [pe]
  | Expr _ (Eaction (Paction _ (Action _ _ (Alloc0 pe1 pe2 _)))) => [pe1, pe2]
  | Expr _ (Ememop _ pes) => pes
  | _ => []

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

end CerberusHeapLang
