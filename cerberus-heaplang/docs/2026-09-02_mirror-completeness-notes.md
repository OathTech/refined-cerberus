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
