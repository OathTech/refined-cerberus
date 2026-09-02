# Mirror completeness — slice notes (2026-09-02)

Charter: DECISIONS.md "MIRROR COMPLETENESS — GO" ([USER 2026-09-02])
and "THE DEMO'S ACCEPTANCE GOALS" (goal 2). Worker record; two
commits, one change at a time; `scripts/signature_snapshot.lean`
before/after each.

Provenance tags: [USER] = operator ruling quoted from DECISIONS.md;
[AGENT] = decision taken in this slice by the worker, open to operator
veto.

## Commit 1 — the round over the SHIPPED driver (spec restatement)

### The finding this commit closes

Before: `CerberusRound M aid c c' := outcomesU M aid c.1 c.2.1 c.2.2 =
[.next (M.thread c'.1 c'.2.1) c'.2.2]`, and the exports
`engine_step_matchU`, `step_iff_cerberusRound`,
`cerberusRound_classify`, `cerberusRound_refused_*` were stated over
`outcomesU`, i.e. over the hand-written `dischargeStep`
(Soundness.lean) — a package definition in an export's referent, which
the trust rule ([USER 2026-09-02], CLAUDE.md "The referent of every
export is the genuine semantics") forbids.

### `CerberusRound` — verbatim (Round.lean)

```lean
/-- The driver states that EMBED a machine context and a live
    configuration: the single thread `M.tid` (parent `M.parent`) holds
    `M.thread c.1 c.2.1`, the memory is `c.2.2`, and the file, extern
    map and run state are the context's. Every other driver-state field
    (trace, step counter, concurrency and file-system state, …) is
    free: the fragment's rounds read none of them. -/
structure MachineCtx.Embeds (M : MachineCtx) (dst : driver_state) (c : Config) : Prop where
  thread : dst.core_state0.thread_states = [(M.tid, (M.parent, M.thread c.1 c.2.1))]
  layout : dst.layout_state = c.2.2
  file : dst.core_file = M.file
  extern : dst.core_extern = M.extern
  runState : dst.core_run_state0 = M.runState

def CerberusRound (M : MachineCtx) (c c' : Config) : Prop :=
  ∀ dst : driver_state, M.Embeds dst c →
    ∃ s : core_step2,
      step_ctx M.tagDefs dst.layout_state dst.core_file dst.core_extern M.tid
        (M.parent, M.thread c.1 c.2.1) = [s] ∧
      can_advance s = true ∧
      ∃ (rs' : core_run_state) (tr : List trace_event) (ctr : Nat),
        rs'.labeled = dst.core_run_state0.labeled ∧
        runOne (advance_step M.tagDefs M.tid s) dst =
          (NDactive NOWAKEUP,
           { dst with
              core_state0 := update_thread_state M.tid (M.thread c'.1 c'.2.1) dst.core_state0,
              layout_state := c'.2.2,
              core_run_state0 := rs', trace := tr, dr_step_counter := ctr })
```

The charter's placeholder name was `ShippedRound`; the definition keeps
the name `CerberusRound` ([AGENT]: continuity with every doc, pin and
diagram; the refusal vocabulary is `ShippedRefusal`).

**What it says.** One iteration of the shipped driver's thread loop
`drive_nonmemory_steps_aux2_lemFuel` (Driver.lean:346-351), decomposed
exactly as the loop body is: the `nd_read` of the engine's step list
(`step_ctx`), `find_can_advance` (a singleton list is selected iff
`can_advance s = true`), and `advance_step` — one active, wakeup-free
transition to the driver state embedding `c'`. The three components and
`update_thread_state` are the engine's own functions. `runOne`
(DriverCollapse.lean) is `match m with | ND f => f s`, the `ND`
constructor's eliminator — the operation `nd_bind` itself performs on
its left argument (Nondeterminism.lean:188) — and carries no driver,
discharge or scheduler content ([AGENT] classification: destructor
plumbing, like `Prod.fst`; recorded in the Round.lean header). The
alternative of stating the advance through the shipped runner
`CerbND.runND` was considered and rejected for the DEFINITION: a
runner-level singleton does not imply a one-layer active result (an
`NDnd` with one productive branch also yields a singleton), so the
loop-level reading and the injectivity the two-sided arm needs would be
lost; the runner-level reading is the derived `CerberusRound.runND`.

**Why no fuel dependency.** The statement is at the loop BODY: the step
list, `find_can_advance` and `advance_step` are not fuelled (`nd_bind`
spends one layer of its own fresh budget per bind, never accumulating —
`runOne_bind_active`). The loop-level reading `CerberusRound.loop_step`
— `runOne (drive_nonmemory_steps_aux2_lemFuel (fl+1) M.tagDefs acc
[M.tid]) dst = runOne (drive_nonmemory_steps_aux2_lemFuel fl M.tagDefs
acc [M.tid]) dst'` — is proved for EVERY `fl` and `acc`
(`loop_step_of_advance`): the continuation at `fl` is the same shipped
function on both sides, and no fuel-zero arm is evaluated by the
statement.

**Generality.** The round is stated at the context's own `M.tagDefs`
(the driver's reader argument) and `M.extern`/`M.file`/`M.runState`
(the embedding), at any thread id `M.tid` and parent `M.parent`.
`loop_step_frag` (DriverCollapse.lean, pinned, unchanged) is the
production-profile instance (`fmapEmpty`, tid 0, parent none). No pin
was deep: every `step_ctx_*` equation and every `*_ws` singleton takes
`tds`/`ext`/`tid`/`parent` as arguments.

### The refusal vocabulary `ShippedRefusal` (Round.lean)

Stated in the same discipline, each arm a fact at every embedding
driver state with the payload fixed by the configuration:

| arm | shipped fact |
|---|---|
| `error msg` | the engine's step list is `[Step_error2 msg]` (one_step0 `ILLTYPED` / step_action `ACTION_ILLTYPED`). The shipped driver's response to this step is the panic `failwithI ("can_advance: Step_error2 ==> " ++ msg)` (Driver.lean:310) — recorded, not modelled |
| `killed r` | `steps = [s]`, `can_advance s = true`, `runOne (advance_step M.tagDefs M.tid s) dst = (NDkilled r, dst')` — `r : kill_reason driver_error` in the engine's own vocabulary (`Undef0 loc ubs` / `Error0 loc msg` / `Other err`; memory kills arrive through `liftMem`'s `DErr_memory`) |
| `fork` | `steps = [s]`, `can_advance s = true`, `2 ≤ (CerbND.runND (advance_step M.tagDefs M.tid s) dst).length` — determinism not baked in |
| `panic msg` | `steps = [Step_with_runstate2 rsk m]` and `m dst.core_run_state0 = (failwithI msg : core_runM thread_state) dst.core_run_state0` — the engine's own `failwithI` (LemLib's opaque rendering of OCaml `failwith`) |
| `panic_memop msg` | `steps = [Step_memop_request2 loc mop cvals M.tid uw k]` and `perform_memop_request2 M.tagDefs loc mop cvals M.tid k = nd_bind (failwithI msg) g` (Driver.lean:288's `INVALID memop request` arm) |

The `fork`/`panic`/`panic_memop` arms are defined here and instantiated
in commit 2.

### Restated exports — before → after, with the derivability argument

| export | before (over `outcomesU`) | after (over the shipped round) | old statement's status |
|---|---|---|---|
| `engine_step_matchU` | `Step M (e, ev0::evs, σ) (e',ρ',σ') → outcomesU M aid e (ev0::evs) σ = [.next (M.thread e' ρ') σ']` | `Step M (e, ev0::evs, σ) (e',ρ',σ') → CerberusRound M (e, ev0::evs, σ) (e',ρ',σ')` | RETAINED verbatim as the proof device `outcomesU_of_step` (Soundness.lean; consumed by `driveU`'s lane: Adequacy/TotalAdequacy/DivergeExhibit). Not derivable from the new statement (different referent — the device is not the shipped driver) and not meant to be: the device is the `driveU` lane's, PROVISIONAL |
| `CerberusRound` | `outcomesU … = [.next …]` (graph of the discharge) | the shipped loop body (above) | the old definition is gone; its content is `outcomesU_of_step` + list injectivity (device level) |
| `step_iff_cerberusRound` | `hstep → (Step M c c' ↔ CerberusRound(old) M aid c c')` | `hstep → (Step M c c' ↔ CerberusRound M c c')` | the mirror-facing content (two-sided given a step, hence mirror determinism) is identical; the old iff is `outcomesU_of_step` + injectivity of `[.next (M.thread e ρ) σ]` in (e, ρ, σ) — five lines at the device, not restated |
| `cerberusRound_classify` | `RoundClass M aid c` with value arms over `outcomesU` and `step`'s iff over the old round | `RoundClass M c`: `value_done` = the step list is `[Step_done2 v]` at every embedding; `value_annot` = a shipped round to the bare value; `step` = the iff over the new round; `refused` unchanged (commit 2 adds the engine fact) | strictly stronger referent; the arms and their exhaustiveness are unchanged. The old value arms follow from `step_ctx_done`/`step_ctx_remove_annot` at the device (`outcomesU_done`/`outcomesU_remove_annot`, both retained) |
| `cerberusRound_refused_store/_load/_create/_case` | `hstuck → ∃ o, o.isRefusal ∧ outcomesU … = [o]` | `hstuck → ShippedRefusal M c` (store: ILLTYPED or `storeM`'s kill; load: `loadM`'s kill; create: the out-of-memory kill; case: the ILLTYPED no-match) | the old statements are RETAINED as device lemmas: `engine_complete_storeU`/`_caseU` (Soundness.lean) and `engine_complete_loadU`/`_createU` (Round.lean) + `EngineMatchU.refusal_of_stuck` — their refusal readings are one line each and were the old exports' whole proofs; not re-exported (device level) |

New public statements (all in Round.lean): `MachineCtx.Embeds`,
`MachineCtx.embeds_exists`, `ShippedRefusal`, `CerberusRound.loop_step`,
`CerberusRound.runND`, `loop_step_of_advance`, `advance_tau`,
`advance_withrs_eval`, `advance_withrs_tau`, `advance_action`,
`advance_action_killed`, `advance_memop`, `storeM_layer`, `loadM_layer`,
`allocateObject_layer`, `applyMemM_eq_ndProj`, `applyMemM_none_killed`,
`runOne_liftMem_killed`, `ars_store_killed`, `ars_load_killed`,
`ars_create_killed`, `lemNatBeq_self`, `lookupBy_single`,
`update_thread_state_single'`, `shipped_done`, `shipped_remove_annot`.
Retired: `RoundClass`'s `aid` index (the shipped driver draws the action
id from its own run state — `perform_action_request2`, Driver.lean:284;
the round has no `aid` parameter).

### Pins

`engine_complete_loadU`/`engine_complete_createU` (devices) unpinned;
`cerberusRound_refused_store`/`_load`/`_create`/`_case` pinned. 116 → 118
trio-exact pins.

### Snapshot (commit 1)

`docs/2026-09-02_mirror-completeness-signatures-pre.txt` (18,687 lines)
→ `docs/2026-09-02_mirror-completeness-signatures-post1.txt` (19,289
lines). Diff (derived by name/statement comparison; counts derived):

- REMOVED: 0.
- CHANGED (17): `CerberusRound` (the definition, above);
  `RoundClass` + its `rec`/`recOn`/`casesOn` and the four arms
  `value_done`/`value_annot`/`step`/`refused` (the `aid` index retired;
  the value arms in the shipped vocabulary); `Step.toCerberusRound`,
  `engine_step_matchU`, `step_iff_cerberusRound`,
  `cerberusRound_classify`, `cerberusRound_refused_store`/`_load`/
  `_create`/`_case` — the restatements tabulated above. Every one is a
  referent change from the discharge device to the shipped driver, none
  a weakening of the mirror-facing content.
- ADDED (45): `outcomesU_of_step` (the OLD `engine_step_matchU`,
  renamed — its statement is unchanged; the snapshot shows it as added
  because the name is new); the new public statements listed above
  (`MachineCtx.Embeds` with its structure projections/recursors,
  `ShippedRefusal` with its five arms and recursors, the driver
  plumbing and layer lemmas); and `Lem_List.find.eq_def`, an equation
  lemma Lean generated for LemLib's `find` when `simp only [find]` was
  first used in this package (an artifact of the proof of
  `lookupBy_single`, not a statement of ours).

### Fast gate (commit 1) — verbatim tail

```text
ℹ [444/446] Built CerberusHeapLang.Audit (1.3s)
info: CerberusHeapLang/Audit.lean:220:0: CerberusHeapLang export pins: 118 trio-exact
info: CerberusHeapLang/Audit.lean:220:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (2297 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:220:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (3610 constants of every kind swept, internal details included — count informational, environment-dependent)
✔ [445/446] Built CerberusHeapLang (790ms)
Build completed successfully (446 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-3 only — not a claim-point result; say fast-gate in the commit)
scripts/test_unit.sh --fast  425.37s user 29.14s system 158% cpu 4:47.10 total
exit=0
```

Build cost: the whole package rebuilt below Soundness in under five
minutes (capped; no UNCAPPED warning).

## Commit 2 — completeness, per constructor (spec addition)

### The statement

```lean
abbrev RoundComplete (M : MachineCtx) (c : Config) : Prop :=
  (∃ c', Step M c c') ∨ ShippedRefusal M c ∨ OpenRound M c

theorem frag_round_complete {M : MachineCtx}
    {e : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel) (hnv : toVal e = none) :
    RoundComplete M (e, ev0 :: evs, σ)
```

`RoundClass.refused` now carries `ShippedRefusal M c`; a fifth arm
`RoundClass.open_` carries `OpenRound M c`; `cerberusRound_classify`
(same hypotheses as before) is proved through `frag_round_complete`.
The old `cerberusRound_classify` statement is derivable from the new
one (map `refused`/`open_` to the old `refused`, dropping the engine
fact) — a strict strengthening with no added premise.

### Refusal vocabulary changes in this commit

- `ShippedRefusal.panic` restated: `steps = [Step_with_runstate2 rsk m]`,
  `m = stExceptUndef_bind step_m k`, and `step_m dst.core_run_state0 =
  failwithI msg dst.core_run_state0` — the redex's own monad panics at
  the head under step_ctx's TAU_WITH_RUNSTATE/EVAL wrapper `k`
  (Core_reduction.lean:484); for `Erun`, whose monad has no wrapper,
  `k` is the return by the right unit law
  `stExceptUndef_bind_return_right`. Commit 1's head form `m rs =
  failwithI msg rs` was FALSE for `Eif`: the wrapper's bind sits
  between the panic and `m` ([AGENT] finding while proving
  `step_ctx_if_panic`). The message and the `Inhabited` instance are
  quantified inside the embedding (they are the engine's literals; the
  proof extracts them from the shape lemma).
- `ShippedRefusal.panic_env` added: a TAU whose successor thread's
  environment head IS `failwithI msg` — the engine's `update_env_aux`
  pattern-mismatch arm (Core_aux.lean:861) at the `Cspecified` binder
  meeting a non-`Specified` value. In OCaml the strict `update_env`
  raises during the round; Lean's opaque `failwithI` defers the abort to
  the first read. [AGENT]: classified as PANIC (the OCaml referent
  aborts), not as an unmirrored success.
- `OpenRound` (new): the registered gaps, each an engine fact —
  `unmirrored_success c'` (the mirror is stuck AND `CerberusRound M c
  c'`), `eval_uncovered` (the step is an operand-evaluation
  with-runstate step), `no_current_proc` (`M.proc = none` and the step
  is the `Erun` with-runstate step).

### The per-constructor table

Mirror-step condition and the engine classification of the stuck case,
per `Frag` constructor (the lemma is at the redex root reached by
`Frag.decomp`; frames `sseq`/`wseq`/`annot` inherit the classification
of their redex through `Decomp` — `Decomp.lift_step` lifts the redex's
step, the `step_ctx_*` equations are stated at `Decomp`):

| `Frag` constructor | lemma | the mirror steps iff | the mirror is stuck ⇒ (shipped fact) |
|---|---|---|---|
| `val_pure v` | `cerberusRound_classify` `value_done` | never (value protocol) | the step list is `[Step_done2 v]` (PROGRAM-DONE at `SeqWF`) |
| `annot ds (val_pure v)` | `value_annot` | never (value protocol) | a shipped round (REMOVE-ANNOT tau) to the bare value |
| `annot ds b`, `b` not a value | via `Decomp.annot` / `complete_merge` | `b` steps; the double-annot merge always steps | `b`'s classification |
| `store` | `complete_store` | `memValueFromValue = some mv` ∧ `storeM` active | ILLTYPED `"…the value of a store(…) didn't match the lvalue type…"` (encoding), else KILL — `storeM`'s `failReason err (requestLoc th loc)`: `MerrAccess` UB kills as `Undef0 loc [ub]`, `MerrOther`/`MerrOutsideLifetime` as `Other (DErr_memory err)` |
| `load` | `complete_load` | `loadM` active | KILL — `loadM`'s `failReason` (null/function/out-of-bounds/dead pointer UB as `Undef0`; trap representation, outside lifetime) |
| `create` | `complete_create` | `allocateObject` active | KILL — `Other (DErr_memory (MerrOther "out of memory"))` |
| `sseq` (wildcard), value head | `complete_beta_pure`/`_annot` | always (cons env) | — |
| `wseq` (wildcard), value head | `complete_wbeta_pure`/`_annot` | always | — |
| `sseq`/`wseq` frames, non-value head | `Decomp.sseq`/`wseq` | head steps (or the head's jump fires at the whole term) | head's classification |
| `sseq_spec`, value head | `complete_beta_spec` | payload is `Vloaded (LVspecified _)` | PANIC-env — `update_env_aux`'s mismatch `failwithI "WIP: Core_aux.update_env_aux ==> ctor= specified, …"` |
| `sseq_sym`, value head | `complete_beta_sym` | the head is a BARE value | GAP (a): `unmirrored_success` — the engine's LETS-ANNOT tau to `(Expr [] (Eannot ds e2), update_env (symPat …) v ρ, σ)` |
| `save` | `complete_save` | initializers are values, or all evaluate (`evalPexprs`) | GAP (c): `eval_uncovered` |
| `if_` | `complete_if` | guard evaluates to `Vtrue`/`Vfalse` | PANIC `"TODO(use the core_runM) ILLTYPED, the first operand of an Eif didn't evaluated to a boolean"` (other value); GAP (c) (uncovered guard) |
| `run` | `complete_run` (`M.proc = some p`), `complete_run_noproc` | label registered ∧ arguments evaluate | PANIC `"Erun couldn't resolve label: `l' for procedure `p'"` (unregistered label — head form, unit law); GAP (c) (uncovered argument); GAP (d) (no current procedure) |
| `pure_sym` | `complete_pure_sym` | the symbol is bound (`evalPexpr`) | GAP (c) — the engine: a procedure name evaluates to the null function pointer; otherwise `Exception (Unresolved_symbol …)` → the driver's `Other (DErr_core_run …)` kill (not characterized here) |
| `load_op` | `complete_load_op` | the pointer operand evaluates to a pointer | GAP (b): `unmirrored_success` to the ill-typed load (non-pointer value); GAP (c) (uncovered operand) |
| `memop_vals` | `complete_memop_vals` | both operands pointers ∧ `eqPtrval` deterministic (same provenance / null / function cases) | FORK — differing-provenance `msum`: `CerbND.runND` delivers exactly two executions (`memop_fork`); PANIC-memop `"INVALID memop request: …"` (non-pointer operands) |
| `memop_op` | `complete_memop_op` | both operands evaluate | GAP (c) |
| `store_op` | `complete_store_op` | pointer operand → pointer ∧ value operand evaluates | GAP (b) (non-pointer); GAP (c) (uncovered operand) |
| `case_value` | `complete_case` | `select_case = some` | ILLTYPED `"Ecase, mismatched ==> …"` |

### Coverage gaps found — STOP-AND-REPORT items ([AGENT])

All four are stated as `OpenRound` arms (engine facts) rather than
fixed in this slice; the charter's rule "fix at the engine's generality
… if the fix is large, STOP AND REPORT with the shape" applies to
(a)–(c); (d) is a context malformation, not a construct.

(a) **LETS-ANNOT at the symbol binder** (`lets x = {A}v in e2`,
`Frag.sseq_sym` with an annotated value head). Engine: the tau
`Step_tau2 "Esseq Eannot" TSK_Misc {th with env := update_env (symPat
pa x bty) v ρ, arena := apply_ctx ctx (Expr [] (Eannot ds e2))}`
(`step_ctx_beta_sym_annot`, proved) — a shipped SUCCESS. Mirror: no
rule (Step.lean's recorded divergence "the annot variant is a
mechanical extension when needed"). Fix: add `Step.sseq_sym_annot`
(clone of `sseq_spec_annot`), its engine equation (exists now), and an
8th disjunct to `Step.sseq_inv` — whose consumers are 38 `rcases`
sites across Soundness/Potential/Wps/Wpt/TotalAdequacy/DriverCollapse/
Round (measured by grep), plus the exhaustive `cases` in
`Step.env_cons'`/`jump_inv`. Mechanical, ~1 day of re-certification.

(b) **ACTION_EVAL to a non-pointer value** (`Frag.load_op`/`store_op`
whose pointer operand evaluates to a non-pointer). Engine: the
evaluation round SUCCEEDS into `Load0 (Vctype ty) (PEval v)` /
`Store0 … (PEval v) (PEval cv)` (`step_ctx_load_eval_ws'`/
`store_eval_ws'`, proved at any value), whose next round is
`ACTION_ILLTYPED "Load"/"Store"`. Mirror: `Step.load_eval`/`store_eval`
require a pointer value (so the successor lands in `Frag.load`/`store`).
Fix at the engine's generality: generalize the pointer slot of
`Frag.load`/`Frag.store` (and `Redex.load`/`store`,
`loadRedex`/`storeRedex`) to any value and `Step.load_eval`/`store_eval`
to `some v`; then `Frag.load`/`store` at a non-pointer value classify
as ILLTYPED (new `step_ctx_load_illtyped`, the store twin). Ripple:
`Frag.decomp`, `Frag.step`, `Frag.esize_step_bound`, `pot_step_bound`,
`outcomesU_of_step`, `engine_step_matchU`, `loop_step_frag`, the
`load_op_inv`/`store_op_inv` consumers in Wps/Wpt determinism proofs.
Not a new manifest row (the constructors keep their names). ~1 day.

(c) **Operand evaluation outside the mirror evaluator** (`if_`, `run`,
`save`, `pure_sym`, `load_op`, `memop_op`, `store_op` when `evalPexpr`
returns `none`). The mirror's `evalPexpr` covers `PEval`, `PEsym`
(environment lookup), `PEop` at the eight binops
Add/Sub/Mul/Eq/Lt/Le/Gt/Ge on integers, `PEarray_shift`; `PePure`
(the declared covered grammar, a premise of `load_op`/`memop_op`/
`store_op` but NOT of `if_`/`run`/`save`) admits every binop. The
engine's `eval_pexpr_aux2`/`step_eval_peop` (Core_eval.lean:135-152)
on the uncovered cases: a symbol unbound in the environment but naming
a `Proc` in `file.funs` evaluates to the null function pointer (a
SUCCESS the mirror lacks); an unbound symbol otherwise is
`Exception (Unresolved_symbol loc x)` → the driver's KILL `Other
(DErr_core_run …)`; `OpEq` on ctypes/floats, `OpLt/Le/Gt/Ge` on floats,
`OpDiv/OpRem_t/OpRem_f/OpExp` on integers, `OpAnd/OpOr` on booleans and
floating arithmetic SUCCEED; ill-typed operands are `Illformed_program`
exceptions → KILL; `Core_eval.eval_pexpr, PEop …` panics on the
remaining operator/value combinations; the non-`PePure` language
(`PEctor`, `PEcall`, `PEcase`, `PEundef`, …) has its own outcomes. Fix
at the engine's generality: a mirror evaluator complete relative to
`eval_pexpr_aux2` on the fragment's operand grammar (with `M.file` as a
new `evalPexpr` argument for the procedure-name arm — a signature
change at ~340 call sites), or a RECORDED narrowing of the fragment's
operand grammar (`PePure` to the eight ops; `if_`/`run`/`save` to
`PePure` operands) — a `Frag` change the charter reserves for the
operator. Large; reported.

(d) **A jump without a current procedure** (`M.proc = none`). Engine:
`current_proc := failwithI "Core_reduction ==> Erun outside of a proc"`
and the `labeled` lookup at that key — in OCaml a `failwith` during
the round; in Lean the opaque key makes the monad's value
uncharacterizable as an equation. Mirror: `M.labels = fmapEmpty`,
fail-closed. Stated as `OpenRound.no_current_proc` with the step's
shape. Every shipped thread inside a procedure body has a current
procedure (`loop_step_frag`'s `hproc`, ProdEntry's production
contexts).

No coverage gap of the store/save kind was FIXED in this slice: the
two candidates (a), (b) both touch the frozen certification broadly
and are reported per the charter instead.

### What was NOT attempted (measured, not guessed)

- The `PEsym` failure bridge (an unbound symbol's `Unresolved_symbol`
  kill through the evaluator tower) — the success bridge is ~400 lines
  (Soundness.lean 1515-1927); the failure twin would be comparable and
  is subsumed by gap (c)'s proper fix.

### Pins (commit 2)

`frag_round_complete` and the twenty per-redex lemmas (`complete_store`,
`_load`, `_create`, `_beta_pure`, `_beta_annot`, `_wbeta_pure`,
`_wbeta_annot`, `_merge`, `_case`, `_beta_spec`, `_beta_sym`, `_if`,
`_run`, `_run_noproc`, `_save`, `_pure_sym`, `_load_op`, `_memop_op`,
`_store_op`, `_memop_vals`) pinned trio-exact. 118 → 139 pins.
`frag_round_complete` added to `scripts/parametric_inventory.lean`'s
export seeds.

### Snapshot (commit 2)

`…-signatures-post1.txt` (19,289 lines) → `…-signatures-post2.txt`
(20,059 lines). Diff (derived by name/statement comparison; counts
derived):

- REMOVED: 0.
- CHANGED (8): `RoundClass.refused` (now carries `ShippedRefusal M c`)
  and `RoundClass`'s recursors (a fifth arm `open_`);
  `ShippedRefusal.panic` (the bind form, message and instance inside
  the embedding) and `ShippedRefusal`'s recursors (the new
  `panic_env` arm). No public theorem's statement changed:
  `cerberusRound_classify`'s statement is unchanged (its conclusion's
  type gained arms — the old classification is derivable by forgetting
  the engine fact and merging `open_` into `refused`).
- ADDED (59): the assembled theorem `frag_round_complete`, the
  twenty `complete_*` lemmas, `OpenRound` (four arms + recursors),
  `RoundClass.open_`, `RoundComplete`, `ShippedRefusal.panic_env`,
  `Decomp.lift_step`, the engine equations at any value
  (`step_ctx_beta_spec_pure'`/`_annot'`, `step_ctx_beta_sym_annot`,
  `step_ctx_load_eval_ws'`, `step_ctx_store_eval_ws'`), the shape and
  panic lemmas (`step_ctx_if_shape`/`_panic`, `step_ctx_run_shape`/
  `_unresolved`, `step_ctx_save_eval_shape`, `step_ctx_pure_sym_shape`,
  `step_ctx_load_eval_shape`, `step_ctx_store_eval_shape`,
  `step_ctx_memop_eval_shape`), `update_env_aux_spec_mismatch`,
  `stExceptUndef_bind_return_right`, and the fork machinery
  (`eqPtrval_layer`, `runOne_bindF_active`, `runOne_bind_nd`,
  `runOne_liftNDF_active`/`_nd`, `runNDFuel_active`/`_nd`,
  `foldl_append_singletons_length`, `bind_branch_active`, `memop_fork`,
  `perform_memop_ptreq_panic`).

### Build cost (commit 2)

Round.lean alone rebuilds in ~13 s (capped, 2.3k lines added over the
slice); the heaviest single proofs are `step_ctx_store_eval_ws'`/
`_shape` (the value split: 13 value shapes × 3 operand grammars × 6
contexts) and `perform_memop_ptreq_panic` (169 constructor pairs), each
a few seconds. No pass approached the tripwire; no heartbeat or
recursion-depth option was touched.

### FULL gate (commit 2, final tree) — verbatim tail

Run on the final Lean tree (every `.lean` of this commit; only this
tail paste and the commit follow it):

```text
The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
ℹ [444/446] Replayed CerberusHeapLang.Audit
info: CerberusHeapLang/Audit.lean:234:0: CerberusHeapLang export pins: 139 trio-exact
info: CerberusHeapLang/Audit.lean:234:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (2434 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:234:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (3802 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (446 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
scripts/test_unit.sh  324.18s user 15.21s system 119% cpu 4:43.76 total
exit=0
```
