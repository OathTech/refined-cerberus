# cerberus-heaplang while-arc close audit (branch `heaplang-phase1`)

[AGENT 2026-08-31] Skeptical arc-close audit, dispatched on operator
order, against the standard of the 2026-08-31 merge audit
(`docs/2026-08-31_heaplang-merge-audit.md`): a legitimate,
NO-QUALIFIERS "heaplang-on-cerberus" whose claims never outrun its
theorems — every qualifier absent from claims or a registered
divergence with a retirement/growth path. The auditor built none of
this; everything below was re-derived in this session (signature
diffs re-computed from the committed snapshots AND a fresh
regeneration, engine sources re-read at the pin, gates re-run,
plants re-planted in three directions, cones and signatures
re-probed, one decode premise discharged concretely).

## VERDICT: FIX-FIRST (docs only, three one-line edits), then merge

No proof-content defect was found. The new certification chain is
legitimate: `driveJ` is literally the engine's
`step_ctx → dischargeStep` composite iterated (Adequacy.lean:526 —
re-read against `generated/Core_reduction.lean:484` at the pin);
the Erun context-discard, Eif big-step guard, Esave fold, and
Ecase-value equations match the engine's own arms (re-read at
source, §Evidence); every WF/panic channel is a stated premise or a
rule-absence, never absorbed; `fib_certified_total` is genuinely
unconditional beyond `0 ≤ n` (signature elaborated and cone probed
in-session: exactly the classical trio, no Iris instance, no fuel);
the regression discipline holds end-to-end (all three phase diffs
re-derived to the digit; headline exports byte-stable across the
whole 15-commit arc); the audit gate fires in all three planted
directions and the tree is clean after revert.

The fix list is documentation, ~15 minutes, no Lean changes:

1. (F1) README first paragraph: scope the production-composite
   sentence to the phase-1 exports (finding 1).
2. (F2) README loop-claims paragraph: one clause naming the
   pre-state hypotheses (finding 2), and "the exhibits' label maps"
   → the two exhibits that actually have the tie (finding 4).
3. (F3 — optional) Correct the S4 notes' boundary-tally sentence or
   append a correction line (finding 3).

With F1+F2 landed this is merge-ready; F3 may be handled as a
correction note at any time.

## What was re-derived (evidence base)

- **Merge hygiene**: `git status` clean; `main..HEAD` = 15 coherent
  commits matching the slice records' own hashes (S1 `a7adaa2`, S2
  `2f5c652`, S3.1-3 `ad79ff0`/`9ab441f`/`ca4b777`, S4.1-4
  `61eaeea`/`fe835ab`/`4654e67`/`6e66074`, ruling `b545b68`);
  `.cerberus-ws` HEAD = `58ec50779…` = `scripts/semantics-pin.env`.
  DECISIONS.md carries the arc plan ruling, the acceptance
  amendment, and the [USER 2026-08-31] array pre-state ruling; the
  ArrayExhibit header matches the ruling's record verbatim in
  substance (provenance forcing fact, donor alignment, element
  views as the registered growth step).
- **Gates, auditor-run**: `scripts/test_unit.sh` → `ALL GATES
  GREEN`; demo sweep verbatim: `643 theorems within the declared
  boundary (40 in the production-entry boundary modules, trio +
  runEffectful; all others trio-exact)`; banned-axiom sweep `1319
  constants of every kind checked`. Both match the README's quoted
  expected tail exactly. Root package sweep 2 theorems, no
  boundary.
- **The regression discipline, re-derived from scratch** (own
  parser over the four committed snapshot files, name-keyed):
  - phase1-pre → phase1-post: 743 unchanged / 1 removed
    (`instLanguageCoreExprMemEmptySpikeVal`, the auto-renamed
    instance) / 81 changed / 75 added — matches the phase-1 notes.
  - phase1-post → s3-post: 817 / 4 removed (exactly the four
    pre-declared retirements) / 78 / 255 — matches the S3 notes.
  - s3-post → s4-post: **1107 unchanged / 1 removed
    (`DecompJ.toDecomp`) / 42 changed / 170 added** — matches the
    S4 notes to the digit. The 42 decompose exactly as itemized:
    23 recursor-family entries of the five extended inductives
    (Step 5, DecompJ 5, FragJ 5, PePure 5, RedexJ 3),
    `Step.sseq_inv`, the 7 step_ctx + 7 engineSteps
    Decomp→DecompJ generalizations, and 4 def-equation artifacts.
  - The one non-pre-declared removal is honestly documented: the
    S4 notes present `DecompJ.toDecomp` as FALSIFIED (with the
    falsifying frame named), and the in-file retirement note exists
    at the former site (Soundness.lean:3008-3015) with the consumer
    re-route stated. Not a silent re-baseline.
  - **Headline exports byte-stable across the WHOLE arc**
    (phase1-pre vs s4-post, entry-for-entry): `SemTriple`,
    `sem_triple_prod`, `prod_run_eq`, `exhibitA_prod`,
    `exhibitA/B/C_engine`, `exhibitA_terminates`,
    `semantic_triple_sound`, `semantic_frame`, `prod_loop_done`,
    `driver2_done`, `finalize_done`, `Sat`. The four whole-arc
    changes found (`engine_complete`, `wp_store`, `wp_load`,
    `triple_seq`) each trace to a reported sanctioned class in the
    slice that made them (env generalization ×3 in phase 1;
    label-generality / `EnvStable` in S3) — none silent.
  - **The committed s4-post snapshot regenerates byte-identical**
    from this tree (`signature_snapshot.lean` re-run in-session,
    `diff` empty, 11082 lines).
- **Engine equations vs the pinned source** (4 spot-verified,
  `generated/Core_reduction.lean` at `58ec50779`):
  - `stepDischarge_run` vs step_ctx's Erun arm (:484): the engine's
    successor is `{th_st with env := env', arena := cont_expr}` —
    **no `apply_ctx`; the context is discarded in the engine
    itself**; the label read is `state_except_read` over
    `run_st.labeled` through the `core_extern1` redirect (identity
    fallback at the frozen `fmapEmpty`, as the proof rewrites);
    the argument fold evaluates each argument against the FIXED
    entry `th_st.env` (the `full_eval_pexpr'` closure) while the
    accumulator threads — exactly `foldM_args_bridge`'s
    characterization; both failwithI panic channels ("Erun outside
    of a proc", "Erun couldn't resolve label") are excluded by the
    stated `hproc`/`hl` premises. `runRedex` pins `Expr []` so the
    `get_loc`/current_loc mutation is provably inert.
  - `stepDischarge_if_true/false` vs one_step0's Eif arm: ONE
    `TAU_WITH_RUNSTATE` with the big-step guard through
    `full_eval_pexpr1`; the non-boolean arm is a failwithI PANIC,
    excluded because the premise says the evaluator RETURNS
    `Vtrue`/`Vfalse`; env and state verbatim, context kept.
  - `step_ctx_save` vs one_step0's Esave value fast-path: the
    `update_env (mk_sym_pat …)` foldl over the zip =
    `bindSaveParams`; the non-value EVAL arm is unmirrored
    (absence of a rule, registered).
  - `step_ctx_case_value` vs one_step0's Ecase value arm: TAU into
    `select_case`'s branch; the PEconstrained PANIC pre-arm is
    bypassed by the canonical `PEval` scrutinee shape; the
    no-match ILLTYPED is a refusal excluded by the `hsel` premise.
  All four proofs unfold the engine's real `step_ctx`/`one_step0`
  and close by `rfl`-grade steps — the statements are
  kernel-checked against the pinned engine, and my source reading
  confirms they SAY what the engine DOES.
- **WF-premise hunt (absorbed-panic sweep of the new Step rules)**:
  `run` (hj/hl/hvs + cons env), `save` (hvals + cons env),
  `if_true/false` (evaluator returns the boolean),
  `case_value` (hv excludes PEconstrained; hsel excludes no-match),
  `pure_eval` (hnv/hv), `load_eval` (hnv2/hv2 to a pointer value),
  `sseq_spec_pure/annot` (fire only at `Vloaded (LVspecified _)` —
  the update_env mismatch panic is rule-absence). No absorbed
  panic found; empty-env `update_env` panics are everywhere
  excluded by cons-shaped env indices.
- **Boundary**: `boundaryModules = [ProdEntry, ProdExhibit]`,
  unchanged; the only other files mentioning
  `runEffectful`/`initial_core_run_state` do so in comments
  (DriverCollapse.lean:563, Soundness.lean:78 — checked). Boundary
  theorem count 40 (sweep), +6 from S4 as reported.
- **Plant tests, re-run by the auditor** (all reverted; post-revert
  build green, sweeps at 643/1319, `git status` clean):
  - D1: `runEffectful` in a statement in a NON-boundary module
    (ArrayExhibit) → build FAILS with the axiom-sweep message.
  - D2: theorem-level `sorry` in a BOUNDARY module (ProdExhibit) →
    build FAILS (`sorryAx … outside the declared boundary`).
  - D3 (the gate ADDED at the merge-audit fix, finding 3's
    closure): bare `def … : Nat := sorry` in a non-boundary module
    → build FAILS in the pass-2 banned-axiom sweep ("a def-level
    hole is still a hole"). The previous audit's gate gap is
    demonstrably closed.
- **Cone probes** (this session, `lake env lean --stdin`): the
  README's eight "How to verify me" theorems plus
  `fib_labeledAt_production`, `wps_sound`, `engine_adequacyJ`,
  `stepDischarge_run`, `engine_step_matchJ`, `driveJ_step` — all
  exactly trio, except the three production-entry statements
  (`exhibitA_prod`, `counter_loop_certified_production`,
  `fib_labeledAt_production`) at exactly trio + `runEffectful`.
  Output matches the README's quoted observed output.
- **`fib_certified_total` unconditionality, re-derived**: the
  elaborated signature (`#check @…`) is
  `∀ ra ibty abty bbty sbty n, 0 ≤ n → ∀ σ₀ aids, driveJ … (2 *
  n.toNat + 4) … = .done (ivVal (fibSpec n.toNat)) σ₀` — the ONLY
  propositional hypothesis is `0 ≤ n`; no fuel, no typeclass
  beyond the quantified metadata, no Iris; cone exactly the trio.
  The README's "no fuel hypotheses at all" is exact. The proof
  chains `driveJ_step` (= `engine_step_matchJ` under the hood, the
  certification theorem) by induction on the variant — the drive
  really is the engine function, not a mirror re-run.
- **The ruling's implementation probed**: `hdec` discharged by
  `rfl` in-session at a concrete two-element array whose byte image
  is the ENGINE's own serialization (`memValueToBytes` of
  `MVinteger`), with the base address, `lum`, and `fpm` all left
  FREE — stronger than the notes claim ("at concrete byte images").
  `arrayShift_cellPtr` is the engine's `arrayShiftPtrval` at the
  concrete shape (provenance preserved, +4); `loadM_interior_int`
  concludes an equation about the engine's `loadM` with the bound
  premise stated. One allocation, per-element structure in the
  invariant + decode premises, big-sep delivery — as ruled.
- **Exhibit honesty**: fib and array-sum invariant proofs go
  through `blockSpecs_intro` (per-label, no Löb) → `wps_sound`
  (the one Löb) → `engine_adequacyJ` → `drive_classifyJ` →
  `engine_step_matchJ` — compositional, no monolithic unfolding;
  the exhibits' `FragJ`/esize side conditions discharge at
  concrete values. `blockSpecs_intro_variant` is a meta-level
  strong induction (classical WF derivation principle) — its
  step-bound product is honestly NOT claimed as a general theorem
  (registered residual; the fib total theorem is the
  exhibit-level product, stated as such in notes and README).

## Findings

### MAJOR

None.

### MINOR

**1. The README's first paragraph still makes the phase-1
production claim universally.** README.md:5-10: "the exported
theorems quantify over the shipped `initial_driver_state` and
conclude equations about the very `CerbND.runND (Driver.drive …)`
composite that the cerberus-lean executable runs." True of the
phase-1 exports (`exhibitA_prod`, `prod_run_eq`,
`sem_triple_prod`); NOT true of the new loop exports, which
conclude `driveJ` equations at a (derived or hand-built) run state
— and the scope section itself says the loop `runND` export "is
NOT yet established". Mitigations, verified: the same paragraph
points to "Scope of the claims", and that section states the
driveJ-lane scope and the production-face residual crisply
(unmissable, in bold-adjacent prose, plus a divergence-table row).
Under the no-qualifiers bar the shop window's opening sentence
should not need the correction. **Fix: scope the sentence to the
phase-1/flagship exports (one line).**

**2. The loop-claims paragraph carries the fuel/partiality/lane
qualifiers but not the pre-state hypotheses.** `counter_loop_
certified` and `array_sum_certified` require a coherently-seeded
cell (`hcoh` at the singleton map), and the array additionally
`hsz`, `hlib`, and the `hdec` decode premises; `fib_certified` is
the only footprint-free one. The README paragraph states partial
correctness, the in-budget fuel hypotheses, the driveJ-lane
projection, and the production residual — but a reader can take
"the engine never kills, never derails" as memory-unconditional
for all three. The decode premises ARE registered (ArrayExhibit
header; divergence table row; S4 notes with the rfl-discharge
claim, which I verified). **Fix: one clause, e.g. "from a memory
carrying the exhibit's seeded footprint (fib's is empty; the
array's cell carries rfl-dischargeable per-element decode
premises)".**

**3. Record-integrity slip in the S4 notes' boundary tally.**
`2026-08-31_phase2-s4-notes.md` §3: "boundary theorem count 34 →
40 (+6: the S4 registration-tie theorems, each carrying exactly
trio + `runEffectful` through the `initial_core_run_state`
STATEMENTS)". Probed in-session: `collect_saves_fib`,
`collect_saves_loop`, `collect_new_fib` are TRIO-only (their
statements never mention the initial state). Three of the six do
not carry the boundary axiom; the sweep bound (trio+runEffectful
as an upper bound) is unaffected, the Audit pins are accurate
(they pin only the two that do carry it), and the error
over-claims axioms rather than hiding them — but a derived tally
in a slice record is wrong as stated, and record integrity is a
standing rule. **Fix: correct the line or append a correction
note.**

**4. "the exhibits' label maps are exactly what the shipped
registration computes" (README:81-84) — the plural overreaches.**
The registration tie exists for fib and the counter loop
(`fib_labeledAt_production`, `loop_labeledAt_production` — both
named in the same sentence, which mitigates); there is NO
`arr…_labeledAt_production`: the array exhibit's run state remains
hand-built (`arrRS`), tied by construction only. The slice notes
scope the tie correctly. **Fix: one word ("the fib and counter-loop
exhibits' label maps"), or add the array tie (it is the same
`rfl`-grade equation).**

### NOTES (no action required for merge)

**5. "UNCONDITIONAL" for `fib_certified_total` means "beyond
`0 ≤ n`".** Verified: `hn : 0 ≤ n` is the only propositional
hypothesis; the README's precise claim ("no fuel hypotheses at
all") is exact. Since `n.toNat` clamps negatives, the theorem is
plausibly provable without `hn` (guard false at entry, 4 ≤ budget)
— a candidate strengthening, not a defect.

**6. "certified faithful for this fragment" (README, the drive-lane
sentence) leans on the phase-1-profile DriverCollapse equations
plus the D2 aid_supply honesty note.** The J-profile drive's
production-face tie is exactly the registered residual, stated in
the same sentence — acceptable as written; watch that future
claims do not drift into "the driver runs driveJ".

**7. `SymFrame` is a deliberate superset** of the frames engine
update-chains actually produce (any tree captured at `symOrd`,
plus empty). Sound — it is only an invariant carrier for the
lookup law — and `envAdd_lookup`'s proof goes through Std's
`getElem?_insert` under the in-session-verified `TransCmp`
transport (`digest_compare` re-read at the pin: a real definition,
not extern, as EnvLaws claims). The non-`LawfulEqCmp` caveat
(comparator-EQ symbols differing in description) is recorded.

**8. `hdec` quantifies over ALL `lum`/`fpm`** — a stronger premise
than the specific σ tables need, in the honest direction (no
hidden coupling to the memory's union/funptr state), and still
rfl-dischargeable (verified with both free).

**9. Scope-narrowing register, checked item by item**: PEsym-only
pure exits (Soundness S4 + divergence table + S4 notes — OK, with
the measured-blowup rationale and the bounded extension named);
Load0-only ACTION_EVAL (positive-scope fragment enumeration in the
README carries it — OK); Ecase EVAL arm out + Ewseq out (register
row, path named — OK); Esave non-value initializers out (rule-doc
absence note — OK); list-reverse a registered stretch, not started
(amendment + register row — OK); the memory-order and tagDefs
seams from the baseline audit remain registered — OK. No
off-register divergence found this pass.

## The new-claims qualifier table (theorem hypothesis → claims-surface treatment → verdict)

| Qualifier / hypothesis | Where it lives | README treatment | Verdict |
|---|---|---|---|
| Loop claims live at the driveJ lane, not the `runND` composite | Adequacy.lean §S3; ProdEntry S4 header; notes | Stated explicitly, incl. the residual, in "Scope of the claims" | **OK** — but the FIRST paragraph contradicts it (finding 1) |
| Production `.done`/`runND` equation for a loop run NOT established | ProdEntry.lean:354-360 ("HONEST RESIDUAL"); S4 notes; divergence table row | Stated ("NOT yet established") + table row with the named discharge path | **OK (unmissable)** |
| `fib_certified` fuel hypotheses (`hfuel`, `hfuel2`), partial correctness | FibExhibit docstring; S4 notes §4 | "PARTIAL-correctness statements with in-budget fuel hypotheses" | **OK** |
| `fib_certified_total`: only `0 ≤ n`; no fuel | verified by signature + cone probe | "TOTAL AND UNCONDITIONAL … no fuel hypotheses at all" | **OK** (`0 ≤ n` unstated; note 5) |
| `array_sum_certified`: `hdec` decode premises, `hsz`, `hlib`, `hcoh` seeded cell | ArrayExhibit header; divergence table (decode premises); S4 notes | Pre-state hypotheses not in the loop-claims paragraph | **GAP → finding 2 (MINOR)** |
| `hdec` rfl-dischargeable at concrete bytes | S4 notes §4 | (not claimed in README) | **OK — verified true, stronger than stated** |
| One-allocation array (vs the amendment's ∗-of-cells) | [USER] ruling in DECISIONS.md; ArrayExhibit header; register row | Register row with the forcing fact + growth step | **OK** |
| `LabeledAt` derivation scope = authored programs, fib + counter loop only | ProdEntry S4 section; S4 notes | "the exhibits' label maps" (plural) | **PARTIAL → finding 4 (MINOR)** |
| Run state constant through driveJ; real driver ticks `aid_supply` | Adequacy §S3; LoopExhibit honesty note | Stated in the scope paragraph | **OK** |
| PEsym-only pure exits / Load0-only ACTION_EVAL / Ecase-EVAL, Ewseq out | Soundness/Step headers; register rows | Fragment enumeration + register rows | **OK** |
| General variant-rule→step-bound theorem not established | S4 notes ("honest residual"); Wps docstring | Not claimed (exhibit-level product only) | **OK** |
| `blockSpecs` premise on `wps_sound` (pre-declared S3 change) | Wps.lean docstring; S3 notes | Not separately claimed | **OK** |
| `runEffectful` in the registration-tie statement cones | Audit.lean header (temporal, mover named) | Trust story + register row | **OK** |

## Bottom line

The while-arc's mechanism is real and the discipline held: the
loop exhibits run through the engine's own step function under a
certification layer whose per-construct equations I re-checked
against the pinned source; the one genuinely unconditional theorem
(`fib_certified_total`) survives hostile re-derivation with exactly
the advertised hypothesis set and a trio-exact cone; the
frozen-corpus gates are reproducible to the digit from the
committed instruments, including the honest handling of the one
falsified lemma; and the audit gate now catches all three planted
hole classes, including the def-level hole the previous audit
found. The holes found are, again, claims-surface precision items
— one over-broad legacy sentence in the shop window, one missing
pre-state clause, one over-broad plural, one wrong derived tally in
a slice note. Land F1+F2 (docs only), decide findings 3/4's
disposition, and this merges.
