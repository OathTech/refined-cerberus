# Fragment closure after E2 — the residual arms (2026-09-05)

Successor to `docs/2026-09-05_fragment-closure-e1-notes.md` (E1) and
`docs/2026-09-02_fragment-closure-notes.md` (the four gaps closed
fail-closed on 2026-09-02/03), for the dialect arc's second slice, E2
(`docs/2026-09-05_e2-notes.md`). Provenance: [USER] = operator ruling
quoted from `docs/DECISIONS.md`; [AGENT] = a decision taken in E2 by the
worker, open to operator veto.

`frag_round_complete` (Round.lean) is re-established at the E2
fragment: every configuration in `Frag` at a cons-shaped environment
within `esize e ≤ lemDefaultFuel` either takes a mirror step, or the
shipped round is a classified refusal (`ShippedRefusal`), or it is one
of the registered residuals (`OpenRound`). The statement is verbatim
the 2026-09-02 one (`(hf : Frag e) (hsz) (hnv : toVal e = none) :
RoundComplete M (e, ev0 :: evs, ctl, σ)`; census: unchanged). The
dispatch gains the PURE round at any covered operand (replacing the
E1 `pure_sym` arm), the two tuple-binder betas and the weak
symbol-binder beta. No new `ShippedRefusal` or `OpenRound` ARM was
needed; one EXISTING arm gained a face: `ShippedRefusal.killed` now
also carries the shipped driver's `Undef0 loc ubs` kill (the
`undef(<<UB…>>)` operand) beside its `Other (DErr_core_run err)` face —
both reached through `liftCore_run` (Driver.lean:245) on the two
failing faces of the classifier's one currency `EvalFail`.

## New rows of the dispatch

| `Frag`/`Redex` root | shipped round | classification | where |
|---|---|---|---|
| `Frag.pure_op` — `pure(e)` at a `PePure` non-value operand (E1's `pure_sym` was the `PEsym` instance) | PURE (one_step0's Epure arm "reduction: PURE", core_reduction.lem:288–299: `full_eval_pexpr pe >>= cval -> return (Expr annots (Epure (mk_value_pe cval)))`, a `Step_with_runstate2 (RSK_eval …)` round; `step_ctx_pure_op_raw` is the engine shape) | (i) the mirror evaluator has a value → the mirror step `Step.pure_eval`; (ii) the classifier's `.kill err` face → the KILL `Other (DErr_core_run err)` (`step_ctx_pure_op_fail`); (iii) the classifier's `.undef loc ubs` face → the KILL `Undef0 loc ubs` (same lemma; `EvalFail.reason`); (iv) `.uncovered` → the residual `OpenRound.eval_uncovered` | `complete_pure_op` (`complete_pure_sym` is its `PEsym` corollary) |
| `Frag.sseq_tuple` at a BARE tuple head (`lets (x1, …) = (v1, …) in e2`) | LETS-PURE (core_reduction.lem:407–414) through `update_env`'s `CaseCtor Ctuple pats', Vtuple cvals` arm (core_aux.lem:2444–2447, a `foldr` over the truncating `zip`) | ALWAYS a mirror step (`Step.sseq_tuple_pure`) | `complete_beta_tuple` |
| `Frag.sseq_tuple` at an ANNOTATED tuple head | LETS-ANNOT (:416–423) | ALWAYS a mirror step (`Step.sseq_tuple_annot`) | `complete_beta_tuple` |
| `Frag.sseq_tuple` at a NON-tuple head value | the binder is `update_env_aux`'s `failwithI` PANIC (core_aux.lem:2448–2450, the catch-all) | `ShippedRefusal.panic_env` (`update_env_aux_tuple_mismatch`; the arm's statement: the step is a TAU whose successor thread's environment head is `failwithI msg`) — classified, not mirrored (the fragment admits the shape because the head is any fragment term; the type checker never emits it) | `complete_beta_tuple` |
| `Frag.wseq_tuple` at a bare / annotated / non-tuple head | LETW-PURE (:389–396) / LETW-ANNOT (:397–405) / the PANIC | as the strong binder: `Step.wseq_tuple_pure` / `Step.wseq_tuple_annot` / `ShippedRefusal.panic_env` | `complete_wbeta_tuple` |
| `Frag.wseq_sym` at a bare / annotated head value | LETW-PURE / LETW-ANNOT (`update_env_aux`'s `CaseBase (Just sym, _)` arm binds any value) | ALWAYS a mirror step (`Step.wseq_sym_pure` / `Step.wseq_sym_annot`) | `complete_wbeta_sym` |
| (mirror-only, NOT a `Frag` row) `Ecase` at a covered NON-value scrutinee | EVAL "Ecase" (core_reduction.lem:323–339) | `Step.case_eval` mirrored and certified (`stepDischarge`/`engine_step_matchU`); `Frag` admits only `case_value`, so no `complete_*` row — [AGENT] deferred: the emitted corpus reaches `case` only inside `pure(…)` | — |

## What changed in the existing rows

- Every operand-evaluating row (`if_`, `run`, `save`, `load_op`,
  `store_op`, `kill_op`, `alloc_op`, `create_op`, `memop_op`, `call`,
  `pure_op`) now distinguishes the classifier's two failing faces: the
  `*_kill` lemmas are corollaries of `*_fail` twins stated at `EvalFail`
  (`EvalFail.reason : EvalFail → kill_reason driver_error` is
  `Other (DErr_core_run err)` / `Undef0 loc ubs`), and every
  `complete_*` case-splits `evalClass … = .val v ∨ (∃ fl, fail? = some fl)
  ∨ .uncovered`. The operand LISTS are classified in the engine's two
  fold shapes: `evalClassList` (Exception-first over collected undefs —
  `stExceptUndef_mapM`, the Ememop/Esave/Eproc operands) and
  `evalClassFold` (first failure — `stExceptUndef_foldM`, the Erun
  arguments); `complete_run` is restated at `evalClassFold` (a forced
  statement change, recorded in the E2 notes §7).
- `OpenRound.eval_uncovered`'s witness list `operandsOf` gains the
  `Ecase` scrutinee (for the mirror-level `case_eval`; unused by any
  `Frag` row).
- The round budget of the evaluator bridge is `peDepth pe ≤ fuel + 1`
  (`aux2_bridge`, `aux2_bridge_kill`): the engine's `eval_pexpr_aux2`
  iterates {pull, `step_eval_pexpr`, value test} and `case` returns the
  selected branch UNEVALUATED, so a branch's value costs one more pass
  than E1's bound allowed (the E1 statement was at `peDepth pe ≤ fuel`,
  correct for E1's grammar, too tight for `case`). [ERRATUM 2026-09-05,
  E2 range audit R-1: the parenthetical's history is WRONG — see the
  erratum appended below.]

## The narrowing premises after E2 — verbatim

```lean
-- Soundness.lean
  | pure_op {an : List _root_.annot} {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) (hp : PePure pe)
      (hd : peDepth pe ≤ lemDefaultFuel) :
      Frag (pureRedex an pe)
  | sseq_tuple {an pa : List _root_.annot} {ls : List TupleLeaf} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (tuplePat pa ls) e1 e2))
  | wseq_tuple {an pa : List _root_.annot} {ls : List TupleLeaf} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Ewseq (tuplePat pa ls) e1 e2))
  | wseq_sym {an pa : List _root_.annot} {x : sym} {bty : core_base_type} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Ewseq (symPat pa x bty) e1 e2))
  -- PePure (the E2 arms)
  | ctorTy (a : List _root_.annot) (c : ctor) (hc : isTyCtor c = true)
      (pb : List _root_.annot) (ty : ctype) :
      PePure (Pexpr a () (PEctor c [Pexpr pb () (PEval (Vctype ty))]))
  | ctor (a : List _root_.annot) (c : ctor) (hc : isMirroredCtor c = true)
      {pes : List (generic_pexpr Unit sym)} :
      (∀ pe ∈ pes, PePure pe) → PePure (Pexpr a () (PEctor c pes))
  | case_ (a : List _root_.annot) {pe : generic_pexpr Unit sym}
      {pats : List (pattern × generic_pexpr Unit sym)} :
      PePure pe → (∀ q ∈ pats, PePure q.2) → PePure (Pexpr a () (PEcase pe pats))
  | not_ (a : List _root_.annot) {pe : generic_pexpr Unit sym} :
      PePure pe → PePure (Pexpr a () (PEnot pe))
  | if_ (a : List _root_.annot) {pe1 pe2 pe3 : generic_pexpr Unit sym} :
      PePure pe1 → PePure pe2 → PePure pe3 → PePure (Pexpr a () (PEif pe1 pe2 pe3))
  | undef (a : List _root_.annot) (loc : CerbLocation.Loc) (ub : undefined_behaviour) :
      PePure (Pexpr a () (PEundef loc ub))
```

`isTyCtor` = `Civalignof | Civsizeof | Cunspecified`; `isMirroredCtor` =
those plus `Cspecified | Ctuple` (Step.lean:1474, :1538). `TupleLeaf :=
List annot × Option sym × core_base_type` — a FLAT tuple pattern only
(`tuplePat pa ls = Pattern pa (CaseCtor Ctuple (ls.map leafPat))`);
nested tuple patterns at an `Esseq`/`Ewseq` binder are outside `Frag`
([AGENT]: the corpus's binders are flat; the engine's `update_env`
would zip nested patterns too — a later slice's mechanical extension).

## Residual register (unchanged in kind)

`OpenRound` keeps exactly its two arms (`eval_uncovered`,
`run_surplus`); `ShippedRefusal` keeps its rows. The pure evaluator's
`.uncovered` face now covers, besides E1's three leaf shapes, the
`case` whose value matches NO pattern (the engine's `failwithI` PANIC,
opaque to the classifier), a `case` whose selected branch the mirror's
depth guard rejects, `UB088_reached_end_of_function` (its location is
the call-location parameter, not decidable from the operand), and a
constructor operand list whose FIRST failing operand is an undef
followed by another failure (the engine's `except_sequence` collects
undefs and raises the first EXCEPTION — Exception-first — so the
outcome is not decided by the first failure; `evalClassList` mirrors
this fold for Ememop/Esave/Eproc operand lists, but the classifier's
`PEctor` arm inside ONE operand answers `.uncovered` there). Each is
recorded in the EvalClass.lean header and the `Frag.pure_op`
OUT-OF-SCOPE manifest row. The manifest
(`docs/CAPABILITY_MANIFEST.md`) records the classification per
variant: 28 constructors, 58 rows, 0 red.

## Erratum (2026-09-05, E2 range audit R-1) — [AGENT], appended

Two corrections to the text above, left in place and corrected here:

1. The arm that classifies the tuple binder at a NON-tuple head is
   `ShippedRefusal.panic_env` (Round.lean; the pre-existing arm whose
   statement is "the step is a TAU whose successor thread's environment
   head is `failwithI msg`"), not `ShippedRefusal.panic` as the first
   version of the table said (corrected in place in the two rows).
2. "the E1 statement was at `peDepth pe ≤ fuel`" is false. E1's
   `aux2_bridge`/`aux2_bridge_kill` carried NO round-fuel premise at all
   (any `fuel + 1` sufficed: the E1 grammar evaluated in one pass —
   `docs/2026-09-04_e1-signatures-post.txt`). E2 ADDED the premise
   `peDepth pe ≤ fuel + 1`: a forced weakening, correctly listed in the
   E2 record's census as value-currency-forced (§7.2 there states it
   correctly: "restated at the round budget"). Measured by the E2 range
   auditor from the two signature snapshots (`docs/2026-09-05_audit-e2-range.md`
   §1, R-1).

