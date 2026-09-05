# Fragment closure after E4 — the residual arms (2026-09-05)

Successor to `docs/2026-09-05_fragment-closure-e3-notes.md` (E3),
`…-e2-notes.md`, `…-e1-notes.md` and `docs/2026-09-02_fragment-closure-notes.md`,
for the dialect arc's fourth slice, E4 (`docs/2026-09-05_e4-notes.md`).
Provenance: [USER] = operator ruling quoted from `docs/DECISIONS.md`;
[AGENT] = a decision taken in E4 by the worker, open to operator veto.

`frag_round_complete` (Round.lean) is re-established at the E4 fragment:
every configuration in `Frag` at a cons-shaped environment within `esize
e ≤ lemDefaultFuel` either takes a mirror step, or the shipped round is a
classified refusal (`ShippedRefusal`), or it is one of the registered
residuals (`OpenRound`). The STATEMENT is unchanged in its words; the
DEFINITIONS it ranges over changed shape: `CerberusRound`,
`ShippedRefusal` (every arm) and `OpenRound` (both arms) are stated in
HEAD form since E4 — the engine's step list is `s :: post` (resp.
`Step_error2 msg :: post`, …), not `[s]` — because at a reducible `unseq`
the engine's list has one entry per reducible component, last-first
(`get_ctx_unseq_aux`, core_reduction.lem:544–548, :590–601; measured, E4
notes §1), and the shipped sequential loop reads its head
(`find_can_advance`). The singleton reading remains a theorem for value
arenas, root redexes (`step_ctx_singleton_of_root`) and `Cunseq`-free
decompositions (`Decomp.get_ctx_single`), so every pre-E4 exhibit
statement that quoted `= [s]` (OverflowExhibit's `overflow_step_ctx`, the
`engine_complete_*U` witnesses) is unchanged.

E4 adds ONE `Frag` constructor, `Frag.unseq`, and two `Step` rules; the
completeness proof gains ONE new `complete_*` row and one new `Frag.decomp`
case.

## The new rows

| configuration | mirror | classifier / engine | shipped round |
|---|---|---|---|
| `unseq(es)` with a reducible component `e` (last reducible; `valsOnly es2`, `ccallFreeList (es1 ++ es2)`) — the redex is inside `e` | `Step.unseq_ctx` (the component's own step under the `Cunseq` frame; `Decomp.unseq`) | the component's own row | the head of the engine's list is the focused component's context (`Decomp.get_ctx_at`, head form); `is_unseq_with_ccall` is `false` at the frame (`Decomp.unseq_ccall_false` from `ccallFreeList`), so `can_advance` holds; every row of the focused redex is re-proved at `pre = []` |
| `unseq(v_1, …, v_n)` — every component a value, no race between the annotated components' `DA_pos` footprints | `Step.unseq_vals` (`collectUnseq ([], []) ws = some (fps, cvals)`) | — | UNSEQ-PURE/UNSEQ-ANNOT (`one_step0`'s `Eunseq` arm, core_reduction.lem:375–386; `one_step_unseq_aux` = `collectUnseq`, `one_step_unseq_aux_collect`): TAU `Step_tau2 "Eunseq" TSK_Misc` into `Eannot fps (pure((v_1, …, v_n)))` — the mirror step (`step_ctx_unseq_vals`) |
| `unseq(v_1, …, v_n)` with a RACE (`do_race`) | — | the engine's `Step_with_runstate2 (RSK_eval "unsequenced race") (stExceptUndef_undef loc [UB035_unsequenced_race])` | `ShippedRefusal.killed (Undef0 current_loc [UB035_unsequenced_race])` — E2's KILL face reached by a new node (`complete_unseq_vals`, `step_ctx_unseq_race`, `loop_step_withrs_eval_killed`) |
| `unseq(…, run l(…), …)`, `unseq(…, pcall f(…), …)` — a jump/call in the last reducible component | `Step.run`/`Step.call` at the plugged `Cunseq` context (`jumpRedexU?`/`callRedexU?`; `Step.unseq_inv`'s run/call disjuncts) | the existing `run`/`call` rows (`complete_run`, `complete_run_noproc`, the call classification) | the existing rounds; no rule face (manifest NO-RULE) |

## What did NOT change

- No new `OpenRound` arm and no new `eval_uncovered` LEAF: `operandsOf`
  descends into the focused component (`operandsOfU`), so the residual's
  members are E3's (a `Proc`-named unbound symbol, two floats, a symbolic
  comparison, a std.core call over its budget) at a possibly deeper
  operand position.
- `ShippedRefusal`: no new constructor; the race kill is the existing
  `killed` face.
- The sibling condition `ccallFree` EXCLUDES an `Ecase`/`Elet`/`End`
  component as well as `Eccall` ([AGENT], E4 notes §5): the engine's
  `is_unseq_with_ccall_aux` walks the siblings and a `case` inside an
  `unseq` would make the frame non-advanceable only when its branches
  carry a `ccall`; the mirror's coarser condition is fail-closed (a
  program with a `case` component is outside `Frag`, never mis-stepped).
  The corpus (t1–t10) places no `case`/`let`/`nd` component inside an
  `unseq`.

## The narrowing premises after E4 — verbatim

```lean
-- Soundness.lean
  | unseq {an : List _root_.annot} {es : List CoreExpr}
      (hne : es ≠ []) (hcc : ccallFreeList es = true) :
      (∀ e ∈ es, Frag e) → Frag (Expr an (Eunseq es))
-- Step.lean: the focus rule's guards (the LAST reducible component)
  | unseq_ctx {a} {es1} {e e'} {es2} {ρ ρ'} {ctl ctl'} {σ σ'}
      (hv2 : valsOnly es2 = true) (hcc : ccallFreeList (es1 ++ es2) = true)
      (hnj : jumpRedex? e = none) (hnc : callRedex? e = none) (hnv : toVal e = none) :
      Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ') →
      Step M (Expr a (Eunseq (es1 ++ e :: es2)), ρ, ctl, σ) (Expr a (Eunseq (es1 ++ e' :: es2)), ρ', ctl', σ')
```

## Census

`frag_round_complete`, `cerberusRound_classify`, `step_iff_cerberusRound`:
statements textually unchanged; `CerberusRound`/`ShippedRefusal`/`OpenRound`
and every `step_ctx_*`/`stepDischarge_*`/`loop_step_*` equation restated
in head form (the E4 notes' census class "head-form-forced"). New:
`complete_unseq_vals`, `step_ctx_unseq_vals`, `step_ctx_unseq_race`,
`step_ctx_length`, `step_ctx_singleton_of_root`, `Decomp.get_ctx_single`,
`Step.unseq_inv`, `Step.callOf_of_call_unseq`, `Step.ccallFree_preserved`.
