# Fragment closure after E3 — the residual arms (2026-09-05)

Successor to `docs/2026-09-05_fragment-closure-e2-notes.md` (E2),
`docs/2026-09-05_fragment-closure-e1-notes.md` (E1) and
`docs/2026-09-02_fragment-closure-notes.md`, for the dialect arc's third
slice, E3 (`docs/2026-09-05_e3-notes.md`). Provenance: [USER] = operator
ruling quoted from `docs/DECISIONS.md`; [AGENT] = a decision taken in E3
by the worker, open to operator veto.

`frag_round_complete` (Round.lean) is re-established at the E3 fragment:
every configuration in `Frag` at a cons-shaped environment within `esize
e ≤ lemDefaultFuel` either takes a mirror step, or the shipped round is a
classified refusal (`ShippedRefusal`), or it is one of the registered
residuals (`OpenRound`). The statement is verbatim the 2026-09-02 one.
E3 adds NO `Frag` constructor at the expression level and NO new
`complete_*` row: the new admissions are all OPERAND grammar (`PePure`:
`convInt`, `wrapI`, `catchExc`, `isUnsigned`, `call`; two new `ctorTy`
ctors, `Civmin`/`Civmax`; `isMirroredOp` gains `OpAnd`/`OpOr` and the
ctype `OpEq`), so every existing operand-evaluating row (`pure_op`,
`store_op`, `load_op`, `kill_op`, `create_op`, `alloc_op`, `memop_op`,
`if_`, `run`, `save`, `call`) reaches them through the SAME classifier
dispatch (`evalClass … = .val v ∨ (∃ fl, fail? = some fl) ∨ .uncovered`),
re-proved at the file-carrying evaluator.

## What changed in the classifier's faces

| operand shape | mirror | classifier | shipped round |
|---|---|---|---|
| `__conv_int__(ty, e)` at an integer | `evalConvInt` (= `mk_conv_int`) | `.val` | PURE / ACTION_EVAL, the mirror step |
| `__conv_int__` at a non-integer | — | `.kill (illtypedConvInt …)` | the engine's `Illformed_program` KILL (`stepFail_conv_int`, bridged) |
| `wrapI_<op>(ty, e1, e2)` at integers / otherwise | `evalWrapI` (= `mk_wrapI_op`) / — | `.val` / `.kill (illtypedWrapI …)` | mirror step / KILL |
| `catch_exceptional_condition_<op>(ty, e1, e2)` at integers, result IN range | `evalCatch` (= `mk_call_catch_exceptional_condition`) | `.val` | mirror step |
| … result OUT of range | `none` | `.undef loc [UB036_exceptional_condition]` (`catchOut`) | the shipped driver's `Undef0 loc [UB036]` KILL — E2's `ShippedRefusal.killed` face, now reached by an ARITHMETIC node (`stepFail_cAddBranch_overflow`, `evalClass_cAdd_overflow`; OverflowExhibit over the genuine driver's round) |
| … at non-integers | — | `.kill (illtypedCatch …)` | KILL |
| `is_unsigned(ty)` at a LEAF ctype / non-ctype leaf | `evalIsUnsigned` / — | `.val` / `.kill (illtypedIsUnsigned …)` | mirror step / KILL |
| `Ivmin(ty)`/`Ivmax(ty)`; `ty1 = ty2`; `/\`, `\/` at booleans / at non-booleans | `evalCtor`/`evalBinop` | `.val` / `.kill (illtypedAnd …)`, `.kill (illtypedOr …)` | mirror step / KILL |
| `f(args)` at a `Sym` of the file's `stdlib`/`funs`, matching arity, body in `PePure` within `stdBudget f` | `callBody` (= `call_function`'s success path) | the body's own class (the unfolding is one pass; `pull_constrained 0` mirrored by `peStrip`) | the PURE/ACTION_EVAL round continues into the body (`call_function_of_callBody`) |
| `f(args)` at a name NOT in the file (`Sym` outside `stdlib`/`funs`; `Impl` outside `impl`) | — | `.kill unknownFunction` / `.kill (unknownImpl c)` | the engine's `Illformed_program "calling an unknown function"` KILL (`call_function_exception_of_callOut`) |
| `f(args)` at a WRONG arity, or at a callee FOUND in `stdlib`/`funs` that is not a `Fun` declaration | — | `.uncovered` (`callOut`: the callee is found, the mirror does not unfold) | `OpenRound.eval_uncovered` — the engine's own `failwithI` in `call_function` (core_eval.lem:149–162) is a PANIC the classifier does NOT certify; the round is the residual, not a `ShippedRefusal`. [CORRECTED at E4 — E3 range audit R-3: this row said `ShippedRefusal.panic`, which `callOut` never produces.] No exhibit reaches it |
| `f(args)` whose body EXCEEDS its static budget, or is outside `PePure` | `none` (`stepPexprRaw`'s guard) | `.uncovered` | `OpenRound.eval_uncovered` — a NEW FACE of the existing residual ([AGENT]): the engine unfolds and continues, the mirror stops; the operand is carried as witness. Reached by no std.core function E3 transcribes (their budgets are their depths) |

## The residual after E3

`OpenRound.eval_uncovered`'s leaf shapes: a symbol UNBOUND in the
environment but naming a `Proc` of the file; a mirrored binop at two
floats; a comparison at symbolic integers (`PEconstrained`); a `case`
whose selected branch the depth guard rejects; and (E3) a std.core call
whose body exceeds `stdBudget`. REMOVED from the residual by E3: `OpEq`
at two ctypes (mirrored, `ctypeEqual`). `OpenRound.run_surplus` is
unchanged (its statement changed shape only: the evaluator's file
argument).

## The narrowing premises after E3 — verbatim

```lean
-- Step.lean: the std.core call is unfolded only under the static budget
--   | PEcall nm pes => … if isPePure (peStrip body) && decide (peDepth (peStrip body) ≤ stdBudget nm)
--                        then some (peStrip body) else none
-- Soundness.lean: isPePure's E3 arms
--   | PEis_unsigned pe => isPePure pe && decide (peDepth pe = 1)
--   | PEcall _ pes => isPePureList pes
```

The `is_unsigned` leaf restriction is the mirror's honesty about the
engine's rebuild quirk (core_eval.lem:1086, E3 notes §2/§5), not a gap in
the engine's reach: at a deeper operand the engine computes `is_scalar`
of the rebuilt operand, which no emitted program relies on.

## Census

`frag_round_complete`, `cerberusRound_classify`, `step_iff_cerberusRound`:
statements unchanged except the evaluator's file argument (the E3 notes'
census class "file-parameter-forced"). `ShippedRefusal`, `OpenRound`: no
new constructor; `OpenRound.eval_uncovered` gains a face by DESCRIPTION
(its witness list is the operand; the classification's `.uncovered`
answer now also arises from the budget guard).
