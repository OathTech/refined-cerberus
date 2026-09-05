# Fragment closure after E1 — the residual arms (2026-09-05)

Successor to `docs/2026-09-02_fragment-closure-notes.md` (the four gaps
closed fail-closed on 2026-09-02/03) for the dialect arc's first slice,
E1 (`docs/2026-09-04_e1-notes.md`). Provenance: [USER] = operator
ruling quoted from `docs/DECISIONS.md`; [AGENT] = a decision taken in
E1 by the worker, open to operator veto.

`frag_round_complete` (Round.lean) is re-established at the E1
fragment: every configuration in `Frag` at a cons-shaped environment
within `esize e ≤ lemDefaultFuel` either takes a mirror step, or the
shipped round is a classified refusal (`ShippedRefusal`), or it is one
of the registered residuals (`OpenRound`). The statement is verbatim
the 2026-09-02 one (`(hf : Frag e) (hsz) (hnv : toVal e = none) :
RoundComplete M (e, ev0 :: evs, ctl, σ)`); the dispatch gains the two
new redex roots and the two REMOVE-BOUND value shapes. No new
`ShippedRefusal` or `OpenRound` arm was needed — the design
measurement's prediction (E0 §C.1 "no new refusal or residual arm")
held.

## New rows of the dispatch

| `Frag`/`Redex` root | shipped round | classification | where |
|---|---|---|---|
| `Frag.bound` at a BARE value (`bound(v)`) | REMOVE-BOUND, step_ctx's general arm (core_reduction.lem:1221–1226, Core_reduction.lean:484: `Ebound (expr'@(Expr _ (Epure (Pexpr _ _ (PEval _))))) => Step_tau2 "CTX, Ebound(value)" TSK_Misc (wrap_expr expr')`) | ALWAYS a mirror step (`Step.bound_pure`; the value node returned verbatim, location updated) | `complete_bound_pure` |
| `Frag.bound` at an ANNOTATED value (`bound({A}v)`) | REMOVE-BOUND (core_reduction.lem:1214–1219: `Ebound (Expr _ (Eannot _ (expr'@(Expr _ (Epure (Pexpr _ _ (PEval _))))))) => …`) | ALWAYS a mirror step (`Step.bound_annot`; the dynamic annotations DISCARDED) | `complete_bound_annot` |
| `Frag.bound` over a reducible body | the body's round under the `Cbound` frame (get_ctx's Ebound arm, core_reduction.lem:563–568; `is_unseq_with_ccall_aux false` at `Cbound`, :514) | the BODY's classification, lifted through the frame (`Decomp.bound`, `Decomp.lift_step`) | every `complete_*` (the frame is a `Decomp` row, not a redex root) |
| `Frag.create_op` — `create(pe1, pe2)` at `PePure` operands not all values | ACTION_EVAL "eval operands of Create" (core_reduction.lem:656–661; `Step_with_runstate2 (RSK_eval …)`) | (i) both operands evaluate to an INTEGER and a CTYPE → the mirror step `Step.create_eval` (the successor is the canonical create redex, `Frag.create`); (ii) an evaluable pair that is NOT (integer, ctype) → `ShippedRefusal.error_next`, ILLTYPED AT DISTANCE ONE (the rebuilt action's `ACTION_ILLTYPED "Create"`, :654) — `step_ctx_create_illtyped'`; (iii) the first operand (alignment before type, the engine's order) the classifier rejects → the KILL `Other (DErr_core_run err)` — `step_ctx_create_eval_kill1`/`_kill2`; (iv) the first operand the classifier leaves uncovered → the residual `OpenRound.eval_uncovered` | `complete_create_op` (the `alloc_op` template, cloned) |
| `Frag.sseq_sym` at an ANNOTATED head value (`lets x = {A}v in e2`) | LETS-ANNOT at the symbol binder (the same arm as the wildcard binder's, core_reduction.lem:416–423) | ALWAYS a mirror step (`Step.sseq_sym_annot`: `x ↦ v`, `{A}` re-wrapped around `e2`) — the 2026-09-02 gap (a) is now MIRRORED rather than narrowed away; `BareHead` is retired | `complete_beta_sym` (both LETS betas at the binder) |

## What changed in the existing rows

- Every classification lemma is stated at a located redex node
  (`{an : List annot}`); the shipped round's successor thread is the
  location-updated one (`locUpdTh an th`, `MachineCtx.locUpdTh_thread`),
  the mirror's successor control `ctl.upd an`. The evaluation kills
  (`*_kill`) are stated at the ORIGINAL thread's `current_loc` — the
  engine evaluates operands with the thread as it was before the
  general arm's write, then advances the written thread
  (`Core_reduction.lean:484`: `full_eval_pexpr` is applied to the
  operands with the thread state bound BEFORE the `let th_st := match
  maybe_loc …` rebinding takes effect in the successor).
- `OpenRound.eval_uncovered` carries the evaluation location off the
  configuration (`c.2.2.1.curLoc`), not off `MachineCtx.currentLoc`
  (deleted).
- `MachineCtx.Embeds` ties the run state's supplies to the control
  (`sym`, `excl` fields); `CerberusRound` fixes the successor run
  state's `sym_supply`/`excluded_supply` to the successor control's
  `sup` — every E1 round threads them verbatim.

## The narrowing premises after E1 — verbatim

```lean
-- Soundness.lean
  | sseq_sym {an pa : List _root_.annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (symPat pa x bty) e1 e2))
  | bound {an : List _root_.annot} {b : CoreExpr} :
      Frag b → Frag (Expr an (Ebound b))
  | create_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      Frag (createOpRedex an loc ann pe1 pe2 pref)
  -- PePure
  | ctorTy (a : List _root_.annot) (c : ctor) (hc : isTyCtor c = true)
      (pb : List _root_.annot) (ty : ctype) :
      PePure (Pexpr a () (PEctor c [Pexpr pb () (PEval (Vctype ty))]))
```

`BareHead` (the 2026-09-02 narrowing of gap (a)) is DELETED: its
purpose was to keep annotated values away from the symbol binder; E1
mirrors the arm instead. Its exports `BareHead.step` (a trio-exact pin)
and `BareHead.decomp_call_root` (sub-trio, swept) are gone — the census
in `docs/2026-09-04_e1-notes.md` lists them under REMOVED.

## Residual register (unchanged in kind)

`OpenRound` keeps exactly its two arms (`eval_uncovered`,
`run_surplus`); `ShippedRefusal` keeps its rows (`error_next` gains the
create shape, `ACTION_ILLTYPED "Create"`, alongside Load/Store/Alloc).
The manifest (`docs/CAPABILITY_MANIFEST.md`) records the classification
per variant: 25 constructors, 52 rows, 0 red.
