# Fragment closure after E5, slice 1 — the residual arms (2026-09-05)

Successor to `docs/2026-09-05_fragment-closure-e4-notes.md` (E4), for the
dialect arc's fifth slice, first half (`docs/2026-09-05_e5-notes.md`).
Provenance: [USER] = operator ruling quoted from `docs/DECISIONS.md`;
[AGENT] = a decision taken in E5 by the worker, open to operator veto.

`frag_round_complete` (Round.lean) is re-established at the E5 fragment:
every configuration in `Frag` at a cons-shaped environment within `esize e ≤
lemDefaultFuel` either takes a mirror step, or the shipped round is a
classified refusal (`ShippedRefusal`), or it is one of the registered
residuals (`OpenRound`). The STATEMENT is unchanged in its words. E5 adds
SIX `Frag` constructors (`neg_store`, `neg_store_op`, `excluded_store`,
`excluded_store_op`, `case_op`, `nd`), three `Step` rules (`neg_bound`,
`excluded_store`, `excluded_store_eval`; `case_eval` is E2's, first reached
by `Frag` now), ONE new `ShippedRefusal` arm (`panic_step`: the engine's
step IS the opaque panic) and ONE new `OpenRound` arm (`neg_sseq`).

## The new rows

| configuration | mirror | classifier / engine | shipped round |
|---|---|---|---|
| `neg(store(…))` (any operands) under a `bound`, no strong sequence between, no nested `bound` (`break_at_bound_and_sseq ctx = BOUND_NO_SSEQ ctxB ctxA`, i.e. `break_at_sseq ctxA = none`) | `Step.neg_bound` through the frames above the outermost `bound` (`Decomp.lift_neg`): `bound(ctxA[neg act]) → bound(negRewrite n s ctxA act)`, `(ctl.upd a).draw` | `complete_neg_act`, BOUND_NO_SSEQ arm | `Step_with_runstate2 (RSK_tau "Neg Action, no break ==> …" TSK_Misc) m` (core_reduction.lem:1293–1309); `m` draws `excluded_supply`/`sym_supply` and writes both back (`step_ctx_neg`, `advance_withrs_tau_rs`, `loop_step_withrs_tau_rs`) — the mirror step with the supplies written |
| `neg(store(…))` with NO `bound` in its context (`NO_BOUND`) | — | `ShippedRefusal.panic_step "TODO: NO_BOUND (Neg)"` (`step_ctx_neg_nobound`) | the engine's step is `failwithI "TODO: NO_BOUND (Neg)"` itself (:1294–1295): the OCaml interpreter aborts; Lean's opaque `failwithI` is the whole step — neither a kill nor a value |
| `neg(store(…))` under a `bound` WITH a strong sequence between (`BOUND_WITH_SSEQ`) | — (stuck, fail-closed) | `OpenRound.neg_sseq` (new residual) | the in-place re-polarisation / the `sseq`-tuple rewrite (:1319–1338) — NOT mirrored; the corpus's assignments sit under `let weak` frames only. Mover: two `Step` rules (`neg_sseq_repol`, `neg_sseq_rewrite`) and a `Frag.sseq_tuple` at the nested pattern the second produces |
| `neg(store(…))` under a NESTED `bound` (a `Cbound` inside `ctxA`) | — (stuck: `Step.bound_ctx`'s guard `negRedex? b = none` fails, `Step.neg_bound`'s `break_at_sseq ctxA = none` is unprovable) | not a `Frag` row reached by the corpus; the classification's `cases hbr : break_at_bound_and_sseq ctx` covers the value classically | the engine PANICS: `break_at_sseq`'s `Cbound` arm is `failwithI "break_at_sseq, Cbound"` (Core_reduction.lean:427); fail-closed on both sides |
| `Eexcluded n (store(ty, p, v))` at canonical operands | `Step.excluded_store` (`process_action (Just n)`: the store request, continuation `{DA_neg n [] fp}pure(Unit)`) | `complete_excluded_store`: ILLTYPED when `v` does not encode (`Step_error2 "…didn't match the lvalue type…"`, `step_ctx_excluded_store_illtyped`) / `storeM`'s kill (`ars_store_killed`) / the step | `Step_action_request2 "StoreRequest" … (StoreRequest2 mo ty lk pv mv k)` (:1345–1346, :694–711; `step_ctx_excluded_store`), `is_unseq_with_ccall` false at the frame |
| `Eexcluded n (store(ty, pe2, pe3))` at `PePure` operands not all values | `Step.excluded_store_eval` (the node rebuilt at the evaluated operands) | `complete_excluded_store_op`: the step / ILLTYPED AT DISTANCE ONE at a non-pointer pointer operand (`ShippedRefusal.error_next`, `step_ctx_excluded_store_illtyped'`) / the first rejected operand's KILL (`_fail2`/`_fail3`) / the first uncovered operand's `eval_uncovered` | ACTION_EVAL (:721–727): `Step_with_runstate2 (RSK_eval s) m` into `Expr a (Eexcluded n act')` (`step_ctx_excluded_store_eval_ws'`) |
| `case pe of …` at a `PePure` NON-value scrutinee (every alternative in `Frag`, the selected branch in `Frag` and within the size) | `Step.case_eval` (the scrutinee evaluates, the node is rebuilt at the value) | `complete_case_op`: the step / the classified KILL (`step_ctx_case_eval_fail`) / `eval_uncovered` at the scrutinee | one_step0's `Ecase` EVAL arm: `Step_with_runstate2 (RSK_eval s) m` (`step_ctx_case_eval_ws`, `_shape`) |
| `nd(e_1, …, e_n)`, `2 ≤ n`, every alternative in `Frag` | — (no rule: the choice is the driver's) | `ShippedRefusal.fork` (`complete_nd`, `nd_fork`) | one_step0's `End es => ND es` (:447–449) → `Step_nd2 (map wrap_expr es)` (:1473–1474); `advance_step` runs `pick (SK_misc ["nd"]) th_sts` (Driver.lean:336): the `NDnd` node with one `nd_return` branch per alternative (Nondeterminism.lean:277); `CerbND.runND` explores `n` executions |

## What did NOT change

- `OpenRound.eval_uncovered`'s LEAF set: `operandsOf` gains the excluded
  store's two operands (`EvalClass.lean`), so the residual's members are
  E3's leaves at a possibly new operand position; no new leaf.
- The `bound` frame's REMOVE-BOUND rows (`bound_pure`, `bound_annot`) and
  the congruence `bound_ctx` — the latter now GUARDED by `negRedex? b =
  none`: at a body whose focused redex is a negative action the frame's own
  round (`neg_bound`) is the only step, as in the engine.
- The value protocol, the jump/call rows, and every E1–E4 row.

## The `Frag` premises added

- `Frag.case_value` and `Frag.case_op` carry `hall : ∀ q ∈ pats, Frag q.2`
  (every alternative in the cone), with E4's `hbr`/`hbsz` (the selected
  branch in the cone and within the size — now DERIVABLE from the branches'
  sizes by `case_hbsz_of_branches`, the substitution shape lemma
  `esize_subst_fold`; KOI B7's mechanism is closed, the premise form is kept
  for this slice).
- `Frag.nd` requires `2 ≤ es.length` (the singleton `nd` is `pick`'s
  deterministic branch — not emitted; the empty `nd` is `pick`'s panic).
- `Frag.step` and `Frag.pot_step_bound` take `hsz : esize e ≤ lemDefaultFuel`
  (the `case_value` case substitutes at the engine's fuel).

## The static premise of the `bound` rules (the soundness finding)

`wps_bound`/`wpt_bound` require `negFree b = true` and `pot b ≤
lemDefaultFuel` (E5 notes §3): a body that can reach a negative redex is not
a `bound` congruence — the frame performs the round. `negFree` is preserved
by every stack-preserving non-jump round (`Step.negFree_preserved`), `pot`
is non-increasing along them (`Step.pot_le`), and `esize ≤ pot` for every
term (`esize_le_pot`), so the Löb invariant holds at every reachable body.
