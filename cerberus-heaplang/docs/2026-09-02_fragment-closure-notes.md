# Fragment closure — slice notes (2026-09-02/03)

Ruling ([USER 2026-09-02], verbatim): "Are (a-c) actually in scope for
our demo though? Another reasonable way to handle this is to fail-closed
if we've achieved complete coverage." — the fragment is declared as
EXACTLY what the mirror covers; the four registered gaps of the
2026-09-02 mirror-completeness slice (`docs/2026-09-02_mirror-completeness-notes.md`,
§"Coverage gaps found") are closed fail-closed, NO new mirror rule.
Worker record; four commits, one change at a time;
`scripts/signature_snapshot.lean` before (`…-signatures-pre.txt`, 20,059
lines = the previous slice's post2) and after (`…-signatures-post.txt`,
21,326 lines).

Provenance tags: [USER] = operator ruling quoted from DECISIONS.md;
[AGENT] = decision taken in this slice by the worker, open to operator
veto.

## Gap → disposition → theorem

| gap | disposition | where |
|---|---|---|
| (a) LETS-ANNOT at the plain-symbol binder (`lets x = {A}v in e`) — engine success, no mirror rule | NARROWED: `Frag.sseq_sym`'s head is restricted to the bare-value producers `BareHead` (a literal value, `create`, the `PtrEq` memop at values / at operands to evaluate); the annotated value never reaches the binder | `BareHead`, `BareHead.step` (closure under `Step`), `BareHead.not_annot`, `BareHead.redex`, `BareHead.frag` (Soundness.lean); `complete_beta_sym` restated at `ofVal (.pure v)` — always a step |
| (b) load/store ACTION_EVAL whose pointer operand evaluates to a non-pointer — engine success into the ill-typed action | RECLASSIFIED: `ShippedRefusal.error_next` — ILLTYPED AT DISTANCE ONE (the round succeeds AND the successor's step list is `[Step_error2 "Load"]`/`"Store"`) | `step_ctx_load_illtyped'`, `step_ctx_store_illtyped'` (at the rebuilt arena, via `Decomp.get_ctx_rebuild_action`, `Decomp.rebuild_not_irreducible`, `get_ctx_annot_sseq`/`_wseq`/`_action`); `complete_load_op`, `complete_store_op` |
| (c) operand evaluation outside the mirror evaluator | NARROWED + CLASSIFIED: `Frag.if_`/`run`/`save` take `PePure` operands (the three operand-evaluation constructors already did); `PePure.op` takes only the eight mirrored binops; where the mirror answers `none` on a `PePure` operand the engine's outcome is classified by `evalClass` — KILL where the engine rejects, THE RESIDUAL where it accepts | EvalClass.lean (`evalClass`, `evalClassList`, `evalClass_val_iff`, the KILL bridge `step_eval_bridge_kill` → `aux2_bridge_kill` → `full_eval_bridge_kill`/`eval1_bridge_kill`, the list bridges `stExpect_mapM_eval1_kill`/`mapM_eval1_kill`/`mapM_save_kill`/`foldM_args_kill`); Round.lean (`step_ctx_if_kill`, `_run_kill`, `_save_eval_kill`, `_pure_sym_kill`, `_load_eval_kill`, `_store_eval_kill2`/`_kill3`, `_memop_eval_kill`, `advance_withrs_killed_eval`/`_tau`, `runOne_liftCore_run_exception`); `complete_if`, `_run`, `_save`, `_pure_sym`, `_load_op`, `_memop_op`, `_store_op` |
| (d) a jump with no current procedure | RECLASSIFIED: `ShippedRefusal.panic_noproc` — the Erun step's monad is exhibited: the `labeled` read keyed by the engine's `failwithI "Core_reduction ==> Erun outside of a proc"` | `step_ctx_run_noproc`; `complete_run_noproc` |

`OpenRound` loses `unmirrored_success` and `no_current_proc`; the
residual is stated in two arms (below). `RoundClass.open_` is kept for
the residual. `frag_round_complete` and `cerberusRound_classify` keep
their statements verbatim (their meaning strengthens through
`OpenRound`/`ShippedRefusal`).

## The narrowing premises — verbatim

```lean
-- Soundness.lean
inductive BareHead : CoreExpr → Prop where
  | val_pure (v : value) : BareHead (Expr [] (Epure (Pexpr [] () (PEval v))))
  | create {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0} :
      BareHead (createRedex loc ann align ty pref)
  | memop_vals (v1 v2 : value) : BareHead (memopPtrEqVals v1 v2)
  | memop_op {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2)
      (hd1 : peDepth pe1 ≤ lemDefaultFuel)
      (hd2 : peDepth pe2 ≤ lemDefaultFuel) :
      BareHead (memopRedex PtrEq [pe1, pe2])

  | sseq_sym {pa : List annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} (hb : BareHead e1) :
      Frag e1 → Frag e2 →
      Frag (Expr [] (Esseq (symPat pa x bty) e1 e2))

  | save {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr}
      (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe)
      (hd : ∀ pe ∈ saveParamPexprs ps, peDepth pe ≤ lemDefaultFuel) :
      Frag body → Frag (saveRedex sb ps body)
  | if_ {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      (hpg : PePure g) (hdg : peDepth g ≤ lemDefaultFuel) :
      Frag e2 → Frag e3 → Frag (ifRedex g e2 e3)
  | run {ra : core_run_annotation} {l : sym}
      {pes : List (generic_pexpr Unit sym)}
      (hpes : ∀ pe ∈ pes, PePure pe)
      (hdep : ∀ pe ∈ pes, peDepth pe ≤ lemDefaultFuel) :
      Frag (runRedex ra l pes)

def isMirroredOp : binop → Bool
  | .OpAdd | .OpSub | .OpMul | .OpEq | .OpLt | .OpLe | .OpGt | .OpGe => true
  | _ => false

  | op (a : List annot) (op : binop) (hop : isMirroredOp op = true)
      {pe1 pe2 : generic_pexpr Unit sym} :
      PePure pe1 → PePure pe2 → PePure (Pexpr a () (PEop op pe1 pe2))
```

[AGENT] `create` is in `BareHead` beyond the brief's list ("bare values
and the memop forms"): the exhibits bind `create`'s result at the plain-
symbol binder (ProdExhibit, StructExhibit, ProdLoopExhibit — `lets p =
create(…) in …`), and its continuation is `mk_value_e (Vobject
(OVpointer ptrval))`, a bare value (step_action's Create arm). Closure
under the mirror step: create → its bare pointer value; memop-operand
evaluation → the memop at values; the memop at values → its bare
boolean (`BareHead.step`). `Frag e1` is kept alongside `hb : BareHead e1`
(redundant — `BareHead.frag` — but it keeps every induction that used
`ih1` unchanged).

[AGENT] The `PePure.op` narrowing (the brief named `PePure` as the target
grammar; the brief's premise that a `PePure` operand fails in the engine
"only on an unbound symbol or an ill-typed/UB binop at non-integer
operands or division-class UB" was checked against `step_eval_peop`,
Core_eval.lean:135, and is INCOMPLETE — measured: `PePure` admitted every
binop, and `OpDiv`/`OpRem_t`/`OpRem_f`/`OpExp` at two integers, every
arithmetic/comparison binop at two floats, `OpEq` at two ctypes and
`OpAnd`/`OpOr` at two booleans are engine SUCCESSES the mirror lacks).
The six non-mirrored operators are syntactically excludable, so they
are excluded (the brief's own rule: leave in the residual exactly what
is not syntactically excludable). The float/ctype successes are value-
dependent — a float or ctype can enter the environment through a load —
and stay in the residual. `isPePure` + `PePure.of_isPePure rfl` discharge
membership at every authored operand.

Every exhibit and production statement is inside the narrowed fragment:
31 `Frag` proof sites updated (8 for `sseq_sym`, 23 for `if_`/`run`/
`save`), all by constructor rebuilds or `rfl`; no statement of any
exhibit changed.

## The (b) two-round refusal — verbatim

```lean
  | error_next (c' : Config) (msg : String) :
      CerberusRound M c c' →
      (∀ dst, M.Embeds dst c' →
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c'.1 c'.2.1) = [Step_error2 msg]) →
      ShippedRefusal M c
```

The engine facts: the round's success is `step_ctx_load_eval_ws'`/
`store_eval_ws'` + `advance_withrs_eval` (unchanged from the previous
slice); the successor's ILLTYPED report is
`step_ctx_load_illtyped'`/`store_illtyped'` — at the arena `apply_ctx ctx
(Expr [] (Eaction (Paction Pos (Action loc ann (Load0 (PEval (Vctype ty))
(PEval v) mo)))))` with `∀ pv, v ≠ Vobject (OVpointer pv)`, the step list
is `[Step_error2 "Load"]` (step_action's `some _, some _ =>
ACTION_ILLTYPED "Load"` arm, Core_reduction.lean:424; process_action's
`ACTION_ILLTYPED str => Step_error2 str`); the store twin is
`[Step_error2 "Store"]`. The successor arena is not a `Decomp` (its root
is not a `Redex`), so the get_ctx singleton is
`Decomp.get_ctx_rebuild_action`: replacing a decomposition's hole by an
action node keeps `get_ctx` at `[(ctx, action)]` under the ORIGINAL
size bound (frames draw one fuel level each; the annotation frame's
body is never annotation-rooted — `hroot`).

## The (d) panic — verbatim

```lean
  | panic_noproc (msg : String) :
      M.proc = none →
      (∀ dst, M.Embeds dst c →
        ∃ (s : String) (l : sym) (inst : Inhabited sym)
          (k : Option (List (sym × core_base_type) × CoreExpr) → core_run_state →
            exceptM (t0 thread_state × core_run_state) core_run_cause),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) =
          [Step_with_runstate2 (RSK_eval s)
            (stExceptUndef_bind
              (runSE (state_except_read (fun rs : core_run_state =>
                Lem_Maybe.bind0
                  (fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
                      Lem_Basic_classes.ordCompare s1 s2)
                    (resolveExtern dst.core_extern (@failwithI sym inst msg)) rs.labeled)
                  (fmapLookupBy (fun (s1 : sym) (s2 : sym) =>
                    Lem_Basic_classes.ordCompare s1 s2) l))))
              k)]) →
      ShippedRefusal M c
```
(`step_ctx_run_noproc` proves it by `rfl` at `msg = "Core_reduction ==>
Erun outside of a proc"`: the panic term IS the lookup key.)

## The (c) classification

`evalClass tds loc ext file ρ : pexpr → EvalOut` (`.val v` / `.kill err`
/ `.uncovered`) mirrors `step_eval_pexpr`'s arms: PEsym — bound →
`.val`; unbound and `file.funs` holds a `Proc` → `.uncovered`; unbound
otherwise → `.kill (Unresolved_symbol loc (resolveExtern ext x))`. PEop —
the first failing child decides; at two values `binopOut`: two integers
→ the mirror's answer (`.uncovered` at a non-mirrored op); two floats →
`.uncovered`; two ctypes → `.uncovered` at `OpEq`, else the kill;
`OpAnd`/`OpOr` → `.uncovered` (outside `PePure`); anything else → `.kill
(Illformed_program "[loc] ill-typed PEop ==> <mk_op_pe op pe1' pe2'>")`
with pe1', pe2' the PULLED children (`pull_constrained` strips
annotations before `step_eval_pexpr` runs — `peStrip`). PEarray_shift —
(pointer, integer) → the mirror's answer; else `.kill (Illformed_program
"PEarray_shift: type error ==> …")` at the evaluated operands. Facts:
`evalClass_val_iff` (the `.val` face IS `evalPexpr`), `evalClass_of_none`
(`none` is a kill or the residual), `evalClass_peStrip`. Lists
(`evalClassList`, left to right, the first non-value decides — the
`stExceptUndef_mapM`/`foldM` order): `evalClassList_vals_iff`,
`evalClassList_uncovered` (the witness is a member), `evalClassList_of_none`.

The KILL bridge (EvalClass.lean), the failure twin of the success
bridge: `step_eval_bridge_kill` (level 1, at a stripped operand: the
engine's one-call evaluator RAISES exactly `err`; the binop case is the
mirrored operator at every pair of value shapes — 8 × 13 × 13 goals,
each `rfl`/no-confusion, ~8 s for the module), `aux2_bridge_kill`,
`full_eval_bridge_kill` (`full_eval_pexpr … = fun _ => Exception err`),
`eval1_bridge_kill`; then the per-construct KILL step equations in
Round.lean (each `∀ rs, m rs = Exception err`, or under the label tie for
Erun) and the driver's response `advance_withrs_killed_eval`/`_tau`:
`liftCore_run`'s `Exception err => kill (Other (DErr_core_run err))`
(Driver.lean:245), state untouched — so the refusal is
`ShippedRefusal.killed (Other (DErr_core_run err))`.

Engine order matters and is followed: Store evaluates the pointer
operand before the value operand (`complete_store_op` classifies pe2
first — before this slice the proof evaluated pe3 first, which was fine
for the success case only); Ememop and Esave map left to right; Erun
folds over `zip params pes` (the prefix `zipArgs params pes`).

## The residual — verbatim, and why it stays

```lean
inductive OpenRound (M : MachineCtx) (c : Config) : Prop where
  | eval_uncovered (pe : generic_pexpr Unit sym) :
      (∀ c'', ¬ Step M c c'') →
      pe ∈ operandsOf c.1 → PePure pe →
      evalClass M.tagDefs M.currentLoc M.extern M.file c.2.1 pe = .uncovered →
      (∀ dst, M.Embeds dst c → ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) = [Step_with_runstate2 rsk m]) →
      OpenRound M c
  | run_surplus (l : sym) (pes : List (generic_pexpr Unit sym)) (p : sym)
      (params : List (sym × core_base_type)) (cont : CoreExpr) :
      (∀ c'', ¬ Step M c c'') →
      jumpRedex? c.1 = some (l, pes) → M.proc = some p →
      lookupLabel M.labels l = some (params, cont) →
      (∃ vs, evalPexprs M.tagDefs M.extern c.2.1 (zipArgs params pes) = some vs) →
      evalPexprs M.tagDefs M.extern c.2.1 pes = none →
      (∀ dst, M.Embeds dst c → ∃ (rsk : runstate_step_kind) (m : core_runM thread_state),
        step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
          (M.parent, M.thread c.1 c.2.1) = [Step_with_runstate2 rsk m]) →
      OpenRound M c
```

`eval_uncovered` is the brief's anticipated residual (the procedure-
named symbol: the engine's PEsym arm consults `file.funs` — Core_eval.lean:145
— and returns `PEval (Vobject (OVpointer (nullPtrval (Ctype [] Void0))))`)
PLUS, loudly: the eight mirrored binops at two floating-point operands
(`opFval`, `eqFval`/`ltFval`/`leFval` — engine successes the mirror's
integer-only `evalBinop` lacks) and `OpEq` at two ctypes (`ctypeEqual`).
[AGENT] These are value-dependent, not syntactic: a float or a ctype
enters the environment through a load (`valueFromMemValue` of a float
cell) or a literal, and the operand is a symbol. No narrowing of `Frag`
removes them; the mover is a mirror evaluator complete relative to
`eval_pexpr_aux2` on `PePure` (`M.file` threaded into `evalPexpr`, the
float/ctype arms), which turns the arm into `Step`s. The arm's witness
(`pe ∈ operandsOf c.1`, the redex's operands through the frames —
`Decomp.operandsOf_eq`) pins the class: the residual is exactly the
configurations with an accepted-but-unmirrored operand.

`run_surplus` was NOT anticipated by the brief and is reported loudly:
step_ctx's Erun arm folds `stExceptUndef_foldM … th_st.env (List.zip
sym_bTys pes)` (Core_reduction.lean:484) — `zip` TRUNCATES, so a jump
with MORE arguments than the label's parameters evaluates only the
zipped prefix and SUCCEEDS; the mirror's `Step.run` requires `evalPexprs
… pes = some vs` over EVERY argument. When the prefix evaluates and a
surplus argument does not, the engine jumps and the mirror is stuck: an
engine success, label-map-dependent (the parameter list lives in
`M.labels`, not in the syntax), so not a refusal and not removable by a
`Frag` premise. The mover is a prefix-evaluating `Step.run` (evaluate
`zipArgs params pes`), a mirror-rule change this slice may not make.
Every exhibit's jumps have matching arity (their `Step.run` derivations
exist), so no production statement touches this arm.

## Public statements changed (snapshot diff, classified)

`…-signatures-pre.txt` (20,059 lines, 2,054 entries) →
`…-signatures-post.txt` (21,326 lines, 2,180 entries). Diff by
name/statement comparison (derived; counts derived):

- REMOVED (2): `OpenRound.unmirrored_success`, `OpenRound.no_current_proc`
  — gaps (a)/(b) and (d) closed.
- CHANGED (32), every one either a NARROWING sanctioned by the ruling
  or a classification restated with the narrowed fragment's premises:
  `Frag.sseq_sym` (+`hb : BareHead e1`), `Frag.if_` (+`hpg`), `Frag.run`
  (+`hpes`), `Frag.save` (+`hp`), `PePure.op` (+`hop`) and their
  recursors/`below` (`Frag.rec`/`recOn`/`casesOn`/`below.*`, `PePure.rec`/
  `recOn`/`casesOn`/`below.*`) — the ruling's narrowing;
  `OpenRound.eval_uncovered` (the residual witness: mirror stuck, the
  operand, `PePure`, `evalClass … = .uncovered`) and `OpenRound`'s
  recursors, `ShippedRefusal`'s recursors (two new arms) — the
  classification restated, strictly stronger (the old `eval_uncovered`
  is derivable by forgetting the witness; the old `refused`-or-`open_`
  reading is derivable by merging arms); `complete_beta_sym` (at
  `ofVal (.pure v)`, the unused `hsz` dropped — the fragment no longer
  contains the annotated head), `complete_if` (+`hpg`), `complete_run`
  (+`hpes`, `hdep`), `complete_save` (+`hp`, `hdep`), `complete_memop_op`
  (+`hp1 hp2 hd1 hd2`) — each per-constructor lemma now takes exactly the
  constructor's premises (`frag_round_complete` supplies them from
  `Frag`; its statement is unchanged).
- ADDED (128): `BareHead` (+ `frag`/`step`/`not_annot`/`redex`),
  `isMirroredOp`, `isPePure` (+ `PePure.of_isPePure`/`all_of_isPePure`),
  `evalBinop_mirrored`, `saveParams_pure_of_vals`,
  `saveParamsWithValues_pure`; EvalClass.lean whole (`EvalOut`,
  `EvalListOut`, `illtypedPEop`, `illtypedArrayShift`, `binopOut`,
  `shiftOut`, `evalClass`, `evalClassList`, `zipArgs`, `operandsOf`, the
  `_val_iff`/`_of_none`/`_uncovered` facts, `peStrip_idem`,
  `evalClass_peStrip`, the monad laws `fail0_eq`/
  `exception_undef_bind_exception`/`exception_undef_fmap_exception`, the
  KILL bridge and list bridges, `Decomp.operandsOf_eq`); Round.lean:
  `ShippedRefusal.error_next`/`panic_noproc`, `OpenRound.run_surplus`,
  `Decomp.rebuild_not_irreducible`/`get_ctx_rebuild_action`,
  `get_ctx_annot_sseq`/`_wseq`/`_action`, `step_ctx_load_illtyped'`/
  `_store_illtyped'`, `step_ctx_run_noproc`, the eight `step_ctx_*_kill`
  equations, `runOne_liftCore_run_exception`, `advance_withrs_killed_eval`/
  `_tau`; plus the auto-generated companions (`EvalOut.*`/`EvalListOut.*`
  no-confusion/injectivity/sizeOf, `evalClass.eq_def`, `isPePure.induct`).

No other statement changed: `frag_round_complete`, `cerberusRound_classify`,
`RoundComplete`, `RoundClass`, `CerberusRound`, `engine_step_matchU`,
`step_iff_cerberusRound`, every rule, every exhibit and production
statement are byte-identical in the two snapshots.

## The final statement — verbatim

```lean
abbrev RoundComplete (M : MachineCtx) (c : Config) : Prop :=
  (∃ c', Step M c c') ∨ ShippedRefusal M c ∨ OpenRound M c

theorem frag_round_complete {M : MachineCtx}
    {e : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel) (hnv : toVal e = none) :
    RoundComplete M (e, ev0 :: evs, σ)
```
with `ShippedRefusal` = ILLTYPED / ILLTYPED-at-distance-one / KILL /
FORK / PANIC / PANIC-env / PANIC-memop / PANIC-noproc and `OpenRound` =
the two residual arms above. Reading: on the declared fragment, mirror
steps iff the engine has a successful deterministic round; every stuck
configuration is classified — a shipped refusal, or one of the two
residual shapes (an accepted-but-unmirrored operand; a surplus-argument
jump), each named exactly.

## Pins

139 → 159 trio-exact (Audit.lean): `BareHead.step`,
`step_ctx_load_illtyped'`, `step_ctx_store_illtyped'`,
`step_ctx_run_noproc`, `evalClass_val_iff`, `evalClassList_vals_iff`,
`step_eval_bridge_kill`, `aux2_bridge_kill`, `full_eval_bridge_kill`,
`eval1_bridge_kill`, `step_ctx_if_kill`, `step_ctx_run_kill`,
`step_ctx_save_eval_kill`, `step_ctx_pure_sym_kill`,
`step_ctx_load_eval_kill`, `step_ctx_store_eval_kill2`,
`step_ctx_store_eval_kill3`, `step_ctx_memop_eval_kill`,
`advance_withrs_killed_eval`, `advance_withrs_killed_tau`.
`BareHead.not_annot` ([propext]) and `Decomp.get_ctx_rebuild_action`
([Quot.sound, propext]) have SUB-trio cones and cannot sit in the
EXACT-trio pin list (measured with `collectAxioms`); the exhaustive
sweep bounds them. `scripts/test_unit.sh`'s core-module list gains
`EvalClass` (import-direction speedbump).

## Build cost

The whole package rebuilds in ~35 s (capped); EvalClass.lean alone ~8 s
(the 1,352-goal binop split), Round.lean ~38 s. The fast gate's 4-5
minutes are the root package. No pass approached the tripwire; no
heartbeat or recursion-depth option was touched; kernel-only proofs.

## Stopped / reported, not deferred

- The residual's float/ctype successes and `run_surplus` (above) —
  outside what the brief anticipated, stated exactly, with their movers.
- The `hsz` premise of `complete_beta_sym` was unused at the bare head
  and is dropped (a generalization of a pinned lemma).

## FULL gate (final tree) — verbatim tail

Run on the final tree (`scripts/test_unit.sh`, exit 0); only this tail
paste and the commit follow it:

```text
Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
ℹ [445/447] Built CerberusHeapLang.Audit (1.2s)
info: CerberusHeapLang/Audit.lean:253:0: CerberusHeapLang export pins: 159 trio-exact
info: CerberusHeapLang/Audit.lean:253:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (2581 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:253:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (4065 constants of every kind swept, internal details included — count informational, environment-dependent)
✔ [446/447] Built CerberusHeapLang (766ms)
Build completed successfully (447 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
scripts/test_unit.sh > .tmp-full-gate.log 2>&1  457.58s user 22.20s system 157% cpu 5:03.75 total
exit=0
```
