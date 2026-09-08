# Fuel — what is quantified, what is hypothesised, what can be exhausted

[AGENT 2026-09-07, L2] The fuel account of this package at semantics pin
cerberus-lean `89f7e688530c6910884518811d645e4e892e4507` (mainline
`mdd/cerberus-lean`, 2026-09-05) with LemLib
`f6542f8e6860d12d4655e6648bc4c45dabd1d798`, Lean 4.32.2. Every claim below
is measured on the primed workspace `.cerberus-ws/lean_frontend/` (cites
`generated/<file>.lean:<line>`) or on this package (cites
`CerberusHeapLang/<file>.lean:<line>`). Record:
`docs/2026-09-07_l2-repin-notes.md`. The requirement this document answers
is the fuel review's §2 (`../../docs/2026-09-04_review-of-fuel-parameter-design.md`):
every fuelled function on the execution path must be (A) measured, (B)
absorbing, or (C) unreachable — an opaque-default exhaustion on the path
is a silent fail-open.

## 1. The parameter

Fuel is the ambient type class `LemFuel` (LemLib, `.lake/packages/LemLib/lean-lib/LemLib.lean:66`),
an instance-implicit `[LemFuel]` binder on every fuelled engine function;
`LemFuel.fuel : Nat` is the budget. Nothing installs an instance: not
LemLib (`lemDefaultFuel` is gone — `.lake/packages/LemLib/lean-lib/LemLib.lean:63`, HISTORY), not the
semantics (`CerbFuel.driverFuel` is gone — generated `CerbFuel.lean:22`),
not this package. The shipped binary's default `--fuel 100000000`
(cerberus-lean `Main.lean`) is the ONLY numeral of the arc ([USER
2026-09-03], "no magic values"); in this package it appears only in the
`*_shipped` corollaries (`CerberusHeapLang/Shipped.lean`), and
the gate `scripts/fuel_numeral_check.sh` (gate 1b of
`../../scripts/test_unit.sh`) reds it anywhere else.

The same instance reaches every fuelled function of one run: the scheduler
`driver2 [LemFuel] := driver2_lemFuel LemFuel.fuel` (`Driver.lean:427`,
worker `:422`), the per-thread loop
`drive_nonmemory_steps_aux2 [LemFuel] := drive_nonmemory_steps_aux2_lemFuel LemFuel.fuel`
(`:390`, worker `:385`), which `new_drive_core_threads` runs at that
instance (`:399`), the ND bind `nd_bind [LemFuel]`
(`Nondeterminism.lean:214`), the result enumerator `runND [LemFuel]`
(`CerbND.lean:163`, over `runNDFuel`, `:117`), the composite `drive`, the
finalizer `finalize [LemFuel]` (`Driver.lean:468`) and the pure-expression
evaluator (§4). There is no separate fuel-parametric mirror of `drive`
any more (`CerbND.drive_lemFuel` and `drive_wrapper_defeq` of pin
`f95ef8d9c` are gone): a statement about `drive` at `[LemFuel]` IS the
statement about the shipped driver at that budget.

One qualification to "the same instance reaches every fuelled function":
every `nd_bind` starts at the ambient budget, but when its left operand
FORKS (`NDnd`) the bind of each branch continues at `lemFuel − 1`
(`nd_bind_lemFuel`'s `Nat.succ` arm, generated `Nondeterminism.lean:212`;
`runOne_bind_nd`, `Round.lean:6827`: "each branch carries the continuation
at the caller's fuel minus one"), so the binds under a fork run one unit
below the ambient and nested forks compound — the source of the floor of
four in §3.

## 2. The budgets, and what each one is

| Quantity | Where it lives | What it bounds |
|---|---|---|
| `LemFuel.fuel` (ambient) | the caller's instance | every fuelled worker's starting counter in the run: scheduler rounds, per-thread rounds, ND layering, pure-evaluator passes, the finalizer |
| the explicit loop counter `fl` | `drive_nonmemory_steps_aux2_lemFuel fl` in `DriverSafeCtl` (`Adequacy.lean:936`) and `DriverDoneCtl` (`ProdLoop.lean:631`) | iterations of one per-thread worker; the generic shipped-loop theorems quantify it independently of the ambient budget (the production instance starts it at `LemFuel.fuel`, `Driver.lean:390`) |
| the total cost `k` | the total judgment `wpt … k` | the number of shipped rounds a public total proof certifies; delivery uses `k + 2` iterations (the PROGRAM-DONE recording and the drain pass) |
| `peDepth pe` / `evalDepth e` | `Step.lean:2571` / `Fragment.lean:86` | the pure evaluator's passes on one operand / the largest such depth over the operands an expression can evaluate (a value or a symbol read costs one pass, `PEop`/`PEarray_shift` one more than the deepest child) |
| `allocBudget B` | `Heap.lean` | allocation capacity from the cold-start cursor — unrelated to fuel |

## 3. The hypotheses on the exports

- **`hfuel : 2 ≤ LemFuel.fuel`** on every shipped-loop statement: the
  shipped round is one `nd_bind` layer around the thread step and one
  around the value delivery (`loop_step_frag`, `DriverCollapse.lean:2888`;
  `loop_step_frag'`, `:2814`). At fuel 0 the loop is the exhaustion kill
  (`loop_zero_exhausts`, `:3021`); at fuel 1 a delivered value is the
  drain pass's exhaustion (`loop_step_done_exhaust`, `:3030`); PROGRAM-DONE
  needs two (`loop_step_done`, `:436`). The classification of every
  fragment round (`frag_round_complete`, `cerberusRound_classify`,
  `Round.lean:7874`/`:7917`) needs four, because its FORK refusal is
  proved by `memop_fork` (`Round.lean:6961`, `hfuel : 4 ≤ LemFuel.fuel`):
  the `PtrEq` memop's forked memory answer is carried through three
  further `nd_bind`s (the boolean-to-value continuation, the thread
  install, the advance — `runOne_bind_nd` at `:6987`/`:6990`/`:7001`)
  after one active bind (the debug print, `:6985`), and every bind under
  the fork continues at `lemFuel − 1` (§1) — so 4 = the memop round's
  ND-fork depth 3 + 1 (the proof peels `LemFuel.fuel = n + 4`, `:6970`).
  A different theorem domain from adequacy, which consumes the round, not
  the classification.
- **`hdep : evalDepth e ≤ LemFuel.fuel`** on the program, `hQd` on every
  registered label body, `hPd : M.ProcsDepth LemFuel.fuel` on every declared
  procedure body (`Adequacy.lean:728`): the pass budget of the pure
  evaluator suffices for every operand the run can evaluate (§4). R2 ([USER
  2026-09-07]): the fragment `Frag` (`Fragment.lean:491`) is SYNTACTIC —
  no fuel field; the depth is a hypothesis beside it, discharged by
  `decide`-free arithmetic (`Nat.le_of_ble_eq_true rfl` on the transcribed
  program's depth, then `omega` against `hfuel`). The design note's
  `pot e ≤ LemFuel.fuel` (`../../docs/2026-09-04_fuel-restatement-design.md`
  §3) named the wrong measure: the additive potential `pot` bounded `esize`
  for the former `get_ctx` ceiling, which the pin's MEASURED `get_ctx`
  retired; the measure that bounds the evaluator is `evalDepth`
  (`Fragment.lean` header, [AGENT 2026-09-07]).
- **`hfuel : N ≤ LemFuel.fuel`** on every closed total statement, `N` the
  certified round count plus two: `12` (`exhibitA_prod`), `2 * n.toNat + 6`
  (fib), `6 * n.toNat + 8` (counter), `56` (list reversal), `53` (dispose),
  `7 * n.toNat + 5` (region loop), `25 * n.toNat + 9` (malloc'd list),
  `fibRounds n.toNat + 4` (recursive fib), `3 * n.toNat + 6` (even/odd),
  `50` (both whole-file t1 and its retained wrapper regression), `917`
  (t4), `90` (t5), `80` (t6). The generic pipeline theorems
  `prod_run_eqJ_procs` and `prod_run_eqJ_file` use `k + 2 ≤ LemFuel.fuel`
  (`ProdEntry.lean`).
- **No hypothesis** on the closed PARTIAL forms `prod_run_safe_procs`
  (`ProdEntry.lean:621`), `fib_rec_certified`, `even_odd_certified`: at
  every ambient `[LemFuel]`, `CerbND.runND (drive fmapEmpty false F args)
  (initial_driver_state sup F fs).1` is exactly one outcome — the kill
  `CerbND.fuelExhaustedKill` or the postcondition. Their `DriverSafeCtl`
  premise is needed only under `2 ≤ LemFuel.fuel`; below that the setup
  itself exhausts. Since the ambient instance is the budget of both loops
  (§1), this quantifier bounds the run; the "outer scheduler only" caveat of
  pin `f95ef8d9c` (KNOWN-OPEN-ITEMS A2) is retired.
- **The shipped instances.** `X_shipped` (`Shipped.lean`) is `X`
  at `letI : LemFuel := ⟨100000000⟩`, in the statement; the side condition
  is closed by `show _ ≤ 100000000; omega`, and for the six parametric
  programs becomes a bound on the parameter: `n.toNat ≤ 49999997` (fib),
  `≤ 16666665` (counter), `≤ 14285713` (region), `≤ 3999999` (malloc),
  `≤ 33` (recursive fib, through `fibRounds_33`/`fibRounds_mono`),
  `≤ 33333331` (even/odd). Never `decide` on the numeral.

**Whole-file t1 separates capture fuel from execution fuel.**
`CorpusA7.T1.certified_production` (`EmittedT1Exhibit.lean`) quantifies
every execution instance with `50 ≤ LemFuel.fuel` for the fixed captured
file, under its three comparator-check hypotheses. Its body proof has
budget 48; the public `wpt_driver_done_alloc_extern` takes syntactic
`Frag` and separate `evalDepth` bounds for the body and registered labels.
`CorpusA7.T1.certified_production_shipped` instantiates the execution
fuel only. The old `t1_certified_production_shipped` keeps its synthetic
wrapper contract.

The frontend runs separately at the documented fixed capture fuel 50;
the theorem does not quantify arbitrary frontend runs. The input supply
36 is captured data, checked against the fresh frontend result, not a
derived universal supply bound. The transfer theorem
`CorpusA7.T1.certified_production_of_capture_eq` keeps supply equality,
capture equality and the original comparator checks as explicit premises.
Executable comparisons do not discharge those premises in the kernel.
Capture commands and validation status are in the
[implementation record](../../docs/2026-09-08_whole-file-t1-implementation.md).

## 4. Exhaustion on the fragment's execution path — the classification

Every fuelled function reachable from `drive` on the path the exports
prove (the fragment: integer and pointer memory at `fmapEmpty` tag
definitions, no `printf`, no C call, no concurrency), classified per the
review's §2. "Exhaustion value" is the `_lemFuel_zero` lemma's right-hand
side, `rfl` in the generated tree. `fuelExhaustedKill` is
`Error0 CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg`
(`CerbND.lean:98`). The eight rows cerberus-lean's own register
`scripts/fuel_forms_pending.txt` lists as neither measured nor absorbing
are marked (D).

| Function | Cite (generated) | Class | Exhaustion value | On the proved path |
|---|---|---|---|---|
| `driver2` | `Driver.lean:422`–`:429` | (B) | `NDkilled fuelExhaustedKill` | the scheduler's one round; its kill is the admitted outcome of the closed partial forms (`driver2_killed`, `DriverCollapse.lean`) |
| `drive_nonmemory_steps_aux2` | `Driver.lean:385`–`:392` | (B) | `NDkilled fuelExhaustedKill` | every round; `DriverSafeCtl` admits the kill at every counter (`loop_zero_exhausts`, `DriverCollapse.lean:3021`) |
| `nd_bind` | `Nondeterminism.lean:214`–`:216` | (B) | `NDkilled fuelExhaustedKill` | every ND layer; hence `2 ≤ LemFuel.fuel` (§3) |
| `runND` / `runNDFuel` | `CerbND.lean:163` / `:117` | (B) | `[(Killed st0 fuelExhaustedKill, [], st0)]` | the outcome enumeration; the singleton equation's kill arm |
| `eval_pexpr_aux2` | `Core_eval.lean:162`–`:164` | (B) | `Result (Error fuelExhaustedLoc fuelExhaustedMsg)` — absorbing in `exceptM`, lifted by the driver to the same kill | the pure evaluator's pass loop; EXCLUDED on the proved path by `evalDepth e ≤ LemFuel.fuel` (the bridge `step_eval_bridge`/`aux2_bridge`, `Soundness.lean:6541`/`:7148`) |
| `full_eval_pexpr` | `Core_reduction.lean:100`–`:102` | (B) | the same error | the action-operand evaluation; excluded as above |
| `step_eval_pexpr` | `Core_eval.lean:150` (wrapper at `lemSize pexpr1`; `Core_eval_lemMeasureProofs.lean:8`) | (A) MEASURED | its worker's sentinel (`:151`–`:152`) is unreachable through the wrapper | one rewriting pass; `[LemFuel]` only because its callees are |
| `memValueFromValue` | `Core_aux.lean:108` (measure `ctype.lemSize`, `Core_aux_lemMeasureProofs.lean:14`) | (A) MEASURED | — | the value-to-bytes conversion of a store; its `Struct`/`Struct` arm (`:106`) calls the (D) `are_compatible0`, which no fragment store reaches (integer and pointer cells only) |
| `get_ctx`, `subst_sym_pexpr`, `subst_sym_expr`, `update_env_aux` | `Core_reduction.lean:387`, `Core_aux.lean:517`, `:531`, `:903` | (A) MEASURED | — | the redex search, substitution and environment update; no `esize`/`pot` ceiling exists any more |
| `CerbMem.sizeofCtype` and the five layout rows | `CerbMem.lean`; cerberus-lean `scripts/fuel_hypotheses.txt` | (A) MEASURED under the reviewed hypothesis `CerbTagsWf.Acyclic` | — | consumed through the fuel-free wrapper; the package states no `Acyclic` hypothesis (at `fmapEmpty` there is nothing to be cyclic) |
| `hack` | `Driver.lean:438`–`:440` | (D) | `fuelExhausted Vunit` (opaque) | ON THE PATH: `finalize` (`:469`) evaluates the final arena through it — its ONLY caller in the generated tree (`grep` over the pinned `generated/`, L2 audit fixes). Excluded by `0 < LemFuel.fuel`: a value arena is one pass (`hack_value`, `DriverCollapse.lean:660`) |
| `to_pure` | `Core_aux.lean:600`–`:602` | (D) | `fuelExhausted none` (opaque) | ON THE PATH: `finalize` (`Driver.lean:469`) reads the arena's pure expression through it. Excluded by `0 < LemFuel.fuel` (`finalize_done`, `DriverCollapse.lean:677`). A SECOND `drive`-path site: `driver_globals` (`Driver.lean:518`–`:527`) reads each global definition's arena through it (`:526`, inside the `nd_mapM_` over `glob_defs`) before `main` runs — (C) for THIS package only because every certified file has `globs := []` (`prodFile`, `ProdEntry.lean:82`; `prodFileWith`/`prodFileLib` inherit it, `:376`/`:686`), so the map is over the empty list; a file with a global definition would reach this row before `main`, under no exclusion lemma of this package. Its third caller is the elaboration-time rewriter (`Core_rewrite.lean:233`–`:271`), which the driver does not call |
| `to_pures` | `Core_aux.lean:605` | (D) | `fuelExhausted none` | (C) for the fragment: callers are the elaboration-time rewriter (`Core_rewrite.lean:255`) and `core_thread_step2` (`Core_run.lean:424`), which the shipped driver does not call |
| `many`, `many1` | `Monadic_parsing.lean:138`, `:143` | (D) | `fuelExhausted (ParserM (fun _ => []))` | (C) for the fragment: the printf format parser `format0` (`Formatted.lean:391`) under `print_eval_conv_aux` (`Driver.lean:274`), a `printf` builtin — no `Frag` construct |
| `are_compatible_aux`, `_params_aux0`, `_params0` | `Ctype_aux.lean:112`–`:114` | (D) | `fuelExhausted false` | (C) for the fragment: struct/union compatibility (`are_compatible0`, `Ctype_aux.lean:128`) from `memValueFromValue`'s `Struct`/`Struct` arm; the fragment's memory values are integers and pointers |
| `print_eval_conv_aux` | `Driver.lean:268`–`:276` | (B) | `NDkilled fuelExhaustedKill` | (C) for the fragment (`printf`) |

Reading. (i) Every driver-family worker on the path is (B): its
exhaustion is the one kill the partial statements admit and the total
statements exclude by `hfuel`. (ii) The one ambient worker that could
exhaust INSIDE a round — the pure evaluator's pass loop — is (B) and is
in any case kept away from exhaustion by the depth hypotheses. (iii) The
two (D) rows on the path, `hack` and `to_pure`, are evaluated exactly
once (at `globs = []`), at PROGRAM-DONE, on a VALUE arena, where one unit of fuel suffices;
`0 < LemFuel.fuel` follows from `hfuel`. So on the proved path no
opaque-default exhaustion arm is evaluated, and the closed partial forms
are unconditional theorems at every ambient budget. (iv) Outside the
fragment the six other (D) rows are live: a struct-typed store, a
`printf`, the rewriter. They are cerberus-lean's open register
(KNOWN-OPEN-ITEMS A1, residual) — an engine fact, not a premise of any
export here.

## 5. What is deliberately not claimed

- No tightness: every `N` above is a sufficient bound (KNOWN-OPEN-ITEMS
  B6 for the slack that is disclosed).
- No frontend-fuel adequacy theorem: the whole-file t1 execution theorem
  is about the captured file, produced at one documented capture fuel.
- No ambient-one theorem for a live start: `DriverSafeCtl` at
  `LemFuel.fuel = 1` from an arbitrary live configuration is not stated;
  the closed forms classify fuel 0 and 1 through the setup collapse before
  the program runs.
- Fuel adequacy is not assertion-freedom: the hand-written seams' `panic!`
  arms (KNOWN-OPEN-ITEMS A5) are a separate item; the rules' premises keep
  proved programs away from them.
