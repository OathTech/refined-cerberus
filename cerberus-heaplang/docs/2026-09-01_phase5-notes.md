# Foundations Phase 5 — production attachment completed; boundary endgame (design record + oracle + exit criteria)

Worker slice record, foundations arc Phase 5 (arc plan
`docs/2026-08-31_foundations-arc-plan.md` §Phase 5; audit F-05, F-08
and the F-07 strengthening items,
`docs/2026-08-31_cerberus-heaplang-foundational-audit.md`).
Commits: `7a656bf` (1/5, the collapse + fib production), `22ed0d4`
(2/5, the counter on the shipped pipeline + the counter's total
lane), `2bbcf35` (3/5, list reversal on the shipped pipeline),
`2e1455f` (4/5, the boundary endgame + carry-forwards), this commit
(5/5, oracle + records). Gates: `scripts/test_unit.sh` ALL GREEN at
every commit.

EXTERNAL FACT (orchestrator-checked at dispatch, 2026-09-01): the
upstream `runEffectful` retirement has NOT landed (lem-lean mainline
LemLib.lean:54 still carries the axiom) — item 2 below is the arc
plan's documented FALLBACK, and the retirement remains the
registered mover (status line recorded in the Audit.lean header).

## 1. THE LOOP PRODUCTION COLLAPSE (audit F-05 closed)

The phase-1-profile pinning of the driver collapse is removed: the
production driver's round algebra now covers the FULL `Frag` cone at
proc-carrying, populated-label threads.

- **The with-runstate round** (DriverCollapse): the loop fragment's
  remaining constructs reach the driver as `Step_with_runstate2`
  (Eif / Erun / PURE / ACTION_EVAL / memop-EVAL) and
  `Step_memop_request2` (PtrEq). `liftCore_run` WRITES the monad's
  returned run state back into the driver state, so the raw
  singleton lemmas (`step_ctx_*_ws`, the composite `stepDischarge_*`
  scripts re-run with the `Step_with_runstate2` payload kept) prove
  the fragment's monads return it VERBATIM — that is what keeps the
  run-state `labeled` fiber, and with it every later jump,
  certifiable across production rounds. Round equations:
  `loop_step_withrs_eval`/`loop_step_withrs_tau` (the trace arm is a
  no-op at `RSK_eval`/`RSK_tau _ TSK_Misc` — the only kinds the
  fragment produces), `loop_step_memop` + `ars_memop_active`
  (perform_memop_request2's PtrEq discharge; no aid draw, no counter
  tick).
- **The driver step-match** (`loop_step_frag`): wherever the mirror
  steps at a cone configuration, ONE production round advances the
  singleton thread to exactly the mirror's successor — the
  driver-level `engine_step_matchU`, per-redex over all 18 roots +
  the jump disjunct, each case discharged by the raw singleton lemma
  + the matching round equation. The mirror step is taken at any
  context agreeing with the driver's on the three projections `Step`
  reads (tagDefs/extern — both empty on the production path — and
  the label map, tied to the DRIVER'S CURRENT run state); the
  returned run state is untouched (taus, with-runstate) or
  aid-ticked (actions) — `labeled` preserved either way.
- **The total-driven driver simulation** (ProdLoop, TRIO-ONLY):
  `DriverDoneAt` (the pure driver-delivery fact, quantified over the
  whole driver-state context with the `LabeledAt` tie as the only
  run-state condition) + `wpt_driver_aux` — the `wpt_drive_aux`
  clone at the driver level: strong induction on the total
  judgment's budget, one production round per budget unit, jump
  rounds included, delivery prepaid by the value clause
  (`driverDone_value`/`driverDone_annot` — the D20 value protocol at
  the driver; `driverDone_step` — the round composition with the
  field transport). Launch: `wpt_driver_done` (the
  `wpt_engine_boundU` clone). WHY the total lane drives the
  simulation rather than the exported driveJ equations: a driveJ
  `.done` equation alone cannot classify configurations where the
  MIRROR's premises fail but the engine proceeds (the cone is
  deliberately one-sided outside store/case — the audit-sanctioned
  direction); the judgment supplies the mirror step at every
  reachable configuration, exactly as in the drive-lane simulation.
  The drive-lane theorems (driveJ) remain as lemmas, per the plan.
- **The pipeline equation** (`prod_run_eqJ`, ProdLoopExhibit):
  `drive_after_setup` (the ProdEntry cold-start prefix — reused
  verbatim, it was already generic in the program) + `DriverDoneAt`
  at `prodEntryState` + `driver2_done`/`finalize_done`/`runND_active`
  (reused). No termination hypothesis remains — only the in-budget
  bound on the certified step count (fuel honesty, D19; fuel
  parametricity stays the registered residual).

## 2. THE EXPORTS (the audit's acceptance test 6, three times over)

All three conclude about
`CerbND.runND (Driver.drive tagDefs false file args)
(initial_driver_state file fs)` from the COLD START; no package
`drive`/`driveJ` appears in any statement; the label maps are
computed by the shipped registration
(`collect_labeled_continuations_NEW`, the `*_labeledAt` ties).

- `fib_certified_production`: the state-inert back-edge loop;
  hypotheses `0 ≤ n`, the engine's own budget
  (`2·n + 6 ≤ lemDefaultFuel`), fs/argv; delivers
  `ivVal (fibSpec n.toNat)`.
- `counter_loop_certified_production`: HEAP-EFFECTING; the program
  is SELF-CONTAINED (the exhibitA_prod pattern — a cold-start
  production statement cannot quantify a seeded cell, so the program
  CREATES its own with the engine's real allocator, deterministically
  `pxPtr`, and loops against the concrete production pointer; the
  create prefix crosses the driver as two certified rounds with
  ProdExhibit's concrete facts). Conclusion: value `Vunit`, the
  cell's final bytes pinned data-dependently as `CellCoh` of the
  final layout state. New total lane for the counter loop
  (LoopExhibit: `loopLsT` at variant `5·i + 2`, `loop_body_wpt`,
  `loop_blockSpecsT`, `loop_wpt` at `5·n + 3`,
  `loopPost_to_readout`) riding the new whole-cell total store rule
  `wpt_store_cell` (Wpt — the `wps_store` analog: the `off := 0`
  instance of the generic subrange rule, splice collapsed to the
  stored image, write-side decode-independence from
  `StorableAt.stored_dec`).
- `list_reverse_certified_production`: the flagship's production
  instance, a SELF-CONTAINED two-node demo — the chain ENGINE-BUILT
  cold (two node creates at the production allocator's deterministic
  addresses, ids 1 and 2 at 0xFFFFFFFFFFE8/0xFFFFFFFFFFD8, plus four
  field stores authored at the concrete production pointers), then
  reversed by the AUTHORED flagship loop `lrProg`. The creates cross
  the driver as certified rounds; the four stores and the loop ride
  ONE total judgment (`wpt_seq` + `wpt_store_cell_at` per field; the
  stores' LETS-ANNOT residue is absorbed by the erased-value readout
  — `readoutPost_mergeInto_annot`, ProdLoop). Conclusion: one Active
  execution whose delivered pointer heads a footprint
  `SeedChain Q p' [(2,2),(1,1)]` — the same two engine-allocated
  nodes, own values, reversed relinking — satisfied by the final
  production memory. DESIGN NOTE (honest scope): this is the
  flagship's DEMO INSTANCE on the pipeline — a quantified-`ns`
  production statement is impossible at the cold start (programs are
  finite artifacts and the initial memory is pinned to the shipped
  constructor); the quantified flagship theorems remain the
  drive-lane `list_reverse_certified{,_total}`.

## 3. THE BOUNDARY ENDGAME (F-07 strengthening; F-08 fallback)

- The allowance is narrowed to the minimal STATEMENT-CARRYING module
  set: ProdEntry / ProdExhibit / ProdLoopExhibit. The entire
  collapse machinery (DriverCollapse incl. the new with-runstate
  layer, ProdLoop incl. the driver simulation) is TRIO-ONLY.
- THE ORIGIN DISCIPLINE (the audit's strengthening items 2–3, gate
  form): the in-build sweep now checks, for every boundary-module
  theorem whose cone carries `runEffectful`, that the axiom is
  reachable through the STATEMENT's constants (memoized reachability
  `carriesAx` over types+bodies); a proof-borne boundary axiom fails
  the build. Together with the upper bound, every boundary cone is
  EXACT-BY-CONSTRUCTION: trio + runEffectful iff statement-borne.
  Sweep report at close: 1123 theorems bounded; 71 in the boundary
  modules, of which 13 carry the boundary axiom, each
  statement-borne; the other 58 are trio-bounded (they live in the
  boundary modules for locality — cold-start facts, registration
  ties' scaffolding — and the sweep now proves they carry nothing).
  PLANT-TESTED both directions: a planted proof-borne `runEffectful`
  theorem in ProdLoopExhibit fails the build with the origin
  message; the clean tree is green (plant added and removed inside
  commit 4's session; the gate ran green on the clean tree).
- New exact pins: `loop_step_frag`, `wpt_driver_done`,
  `wpt_store_cell` (trio); `prod_run_eqJ`, `fib_certified_production`,
  `counter_loop_certified_production`,
  `list_reverse_certified_production` (trio + runEffectful,
  statement-borne); the renamed
  `counter_loop_certified_registration` re-pinned.

## 4. SANCTIONED STATEMENT CHANGES (itemized; the oracle's complete
list)

- `counter_loop_certified_production` — REPLACED: the old
  registration-tie statement (driveJ at the production run state) now
  lives under its honest name `counter_loop_certified_registration`
  (the F-05 naming debt paid; also de-GF'd, below); the name
  `counter_loop_certified_production` now denotes the REAL production
  `runND` equation (§2). This is the audit's F-05 remediation
  executed exactly: rename + reserve "production" for shipped-runner
  statements, restored only after the scheduler collapse.
- GF-binder removals (the phase-4 §7 carry-forward; mechanical
  SpikeGF-concretization, the `fib_certified_total` pattern):
  `counter_loop_certified`, `fib_certified`, `array_sum_certified`,
  and `counter_loop_certified_registration` — no ghost-functor
  binder remains on any loop export; proofs instantiate `SpikeGF`
  internally.
- NOTHING ELSE changed: the oracle (§5) confirms zero deletions and
  exactly the four names above changed.

## 5. The oracle (frozen-corpus regression)

Snapshots: `docs/2026-09-01_phase4-signatures-post.txt (byte-identical to the former 2026-09-01_phase5-signatures-pre.txt, deduplicated 2026-09-02)` (= the
phase-4 post, 17860 lines, byte-identical — verified at slice start)
/ `docs/2026-09-01_phase5-signatures-post.txt` (18701 lines).
Derived tally (labeled as derived; the snapshots are the record,
compared per-declaration): 0 DELETED, 4 CHANGED, 80 ADDED.

- CHANGED (4) — exactly the sanctioned list of §4:
  `counter_loop_certified_production` (statement replaced by the
  production equation), `counter_loop_certified`, `fib_certified`,
  `array_sum_certified` (GF-binder removals).
- ADDED (80): the DriverCollapse with-runstate/memop layer
  (`runOne_liftCore_run_of_eq`, `loop_step_withrs_{eval,tau}`,
  `loop_step_memop`, `ars_memop_active`, the seven `step_ctx_*_ws`
  raw singletons, `loop_step_frag`), the ProdLoop module
  (`DriverDoneAt`, `driverDone_{value,annot,step}`,
  `wpt_driver_aux`, `wpt_driver_done`, `val_mergeInto_annot`,
  `readoutPost_mergeInto_annot`), `wpt_store_cell` (Wpt), the
  counter total lane (`loopLsT`, `loop_body_wpt`, `loop_blockSpecsT`,
  `loop_wpt`, `loopPost_to_readout`), the ProdLoopExhibit module
  (`prod_run_eqJ`, the three `*_production` theorems, the
  counter/listrev production programs + their registration ties +
  concrete cold-start facts + the compositional collect/pot lemmas),
  `counter_loop_certified_registration` (the rename), and the
  sweep's `Audit.carriesAx`.
- Axiom cones: sweep 1123 theorems bounded, boundary exact via the
  origin discipline (§3); every new headline pinned exactly in-build.

## 6. Audit Phase-5 items and the exit criteria, checked

1. **"Prove the loop scheduler/driver collapse for proc-carrying
   threads with populated labels."** — DONE (§1: `loop_step_frag` +
   `wpt_driver_aux`; the driver's round = one certified engine step,
   iterated, jumps through the run-state tie).
2. **"Export total loop examples as `_root_.drive`/`CerbND.runND`
   theorems."** — DONE ×3 (§2), fib and the counter and the
   reversal demo instance.
3. **"Retire runEffectful upstream …"** — NOT LANDED upstream
   (external fact, top); the registered mover unchanged.
4. **"Narrow the boundary module while retirement is in progress and
   exact-pin all public theorems that still carry the axiom."** —
   DONE in the strengthened gate form (§3): minimal
   statement-carrying module set + origin discipline (exactness by
   construction, mechanical, not curated) + curated pins for every
   production export.
5. **"Re-run semantic-pin and differential validation gates after
   any upstream pin change."** — no pin change this slice (the
   semantics workspace pin untouched).

**Exit criteria**: "Public production theorems mention no package
drive/driveJ" — MET for every `*_production` statement (the
execution function is the shipped runner; program artifacts —
prodFile, the concrete programs/addresses — are data, not execution
functions). "No project theorem depends on runEffectful" /
"exhaustive audit reports only the classical base" — takes the
FALLBACK form honestly: the axiom remains, statement-borne only,
origin-checked in-build, boundary minimal, mover registered
(§3; the full-trio end state arrives with the upstream retirement
at a pin bump, no restatement on our side).

## 7. Registered follow-ons (honest, named)

- `hfuel2` (the second in-budget hypothesis on the PARTIAL driveJ
  lane exports — `counter_loop_certified`,
  `counter_loop_certified_registration`, `fib_certified`) STAYS: the
  production collapse rides the total lane and does not make the
  partial lane's label-budget hypothesis free. Carried unchanged.
- Fuel parametricity of the production equations remains the
  registered residual (README divergence register).
- The listrev production export is the demo instance (§2 design
  note); a quantified-seed production statement is structurally
  unavailable at the cold start.
- `wpt_create` still does not exist (manifest create row): the
  production creates cross the driver as certified rounds instead
  (`driverDone_step`), which is why no total-lane create rule was
  needed. A future in-judgment create (cursor-owning wpt launch)
  remains the named mechanical extension.
- The census freeze-gate future (phase-4 §7) remains open, untouched
  this slice.

## 8. Operational findings

- **Kernel/elaborator whnf term duplication on nested spines** (the
  slice's one real fight): whole-term `rfl` on expressions nested
  through `Esseq` spines re-evaluates shared subterms without
  sharing — measured EXPONENTIAL (a 2-layer `pot` rfl is instant, 3
  layers exceeds the default heartbeat budget; same pathology for
  `collect_saves` over the 6-layer listrev build spine, while the
  1-layer counter program was fine). No heartbeat bump (house ban);
  the honest remedy is COMPOSITIONAL REWRITING: per-arm equations
  proved by one-layer `rfl` (`col_aux_sseq`/`col_aux_action`,
  fuel-peeled with explicit literals; `pot_sseqExpr` etc.) chained
  by `rw` — syntactic, linear, each step cheap — with the inner
  program's computation one bounded-fuel `rfl` at cushioned variable
  fuel (`col_lrProg` at `m + 9`). Recorded as the pattern for any
  future concrete-program registration/measure facts.
- Struct-instance field values do NOT continue onto a new line after
  the walrus (`{ x with f := g a` ⏎ `(b) }` is a parse error);
  wrap the value in parentheses or keep the application head and its
  arguments on one line.
- `iapply`/`iexact` unification at record-typed cells is
  order-sensitive: pin the store rules' implicit `mv` explicitly
  (`(mv := longMval 1)`) and author programs at the RULE-READY
  pointer spellings (`cellPtr id (a + ((off : Nat) : Int))`) instead
  of rewriting mid-proof — a mid-proof `rw [show (8:Int) = …]`
  rewrites every syntactic `8` in the goal, including later stores'.
- `cases h : e with` substitutes the scrutinee's occurrences in the
  goal — a following `rw [h]` then fails with "no occurrence" (hit
  twice; the composite proofs already relied on this).
- The `Std.HashMap` allocation-table lookups at concrete keys close
  by plain `rfl` after rewriting the table shape; `simp` stalls on
  the inserted-map `getElem` normal form.
