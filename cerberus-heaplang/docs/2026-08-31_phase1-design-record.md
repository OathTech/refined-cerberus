# Phase-1 design record: the unified configuration (S1a probe)

Status: PROBE-VALIDATED DESIGN, [AGENT] proposal for the [USER]
Phase-1 checkpoint (arc plan: "the Phase-1 design decision record"
is an operator checkpoint). The probe implementation lives in
`CerberusHeapLang/Phase1Probe/` (marked probe-only; consumed by
nothing in the exported corpus); slice notes:
`docs/2026-08-31_foundations-notes.md`. Audit basis: F-03 and F-01
(2026-08-31 foundational audit), arc plan Phase 1.

STATUS UPDATE [AGENT 2026-09-01]: **PHASE 1 CLOSED at S1c.** The §8
prescription is executed in full — S1b (commits `7dcb497`,
`d4f4084`, `e3cb802`, `4d3e99e`, `7ea6cf2`: the swap, extern
threading, the Ecase consumer, the Ewseq drift test, the oracle) and
S1c (the cone-derived manifest / gate-4 upgrade, the RelSem
two-presentations paragraph, the exit-criteria sweep). The
per-criterion checklist verified against the tree, with theorem
names and plant transcripts: `docs/2026-08-31_foundations-notes.md`,
S1c sections. The probe modules were retired in S1b (their content
is the migrated code). The PHASE MERGE remains the [USER]
checkpoint (arc plan: pause for merge word per phase) — CLOSED here
means the work and its record are complete on this branch, not that
the merge has been sanctioned.

## 1. The decision

The authoritative relation remains the hand-written syntax-facing
mirror (compositionality-guard compliant), REBUILT as one relation
over an explicit configuration:

```
StepU (M : MachineCtx) :
  CoreExpr × EnvStack × Mem → CoreExpr × EnvStack × Mem → Prop
```

- **`MachineCtx` = every immutable component of an engine
  configuration.** An engine sequential step is exactly
  `step_ctx tds σ file ext tid (parent, th)` discharged by
  `dischargeStep aid rs σ`; everything in that application except
  `(th.arena, th.env, σ)` is immutable under the supported fragment
  (the per-rule step_ctx/discharge lemmas return
  `{th with arena, env}` record updates and the run state
  verbatim). The context names all of it:

  | Field | Engine slot | Read by the supported fragment? |
  |---|---|---|
  | `tagDefs` | step_ctx `_lemReader_tagDefs` | YES — store's `memValueFromValue` encoding premise (the old `Step.store` hard-coded `fmapEmpty` here; the old `wp_store` statement inherited that constant) |
  | `file` | step_ctx `file1` | no (proc/impl/funinfo lookups only — outside fragment); quantified |
  | `extern` | step_ctx `core_extern1` | YES — Erun's proc resolution AND the evaluator's PEsym indirection (both identity-fallback; see §5.2) |
  | `tid` | step_ctx `current_tid` | passed into requests; discarded by the fragment's memory ops (`allocateObject`/`eqPtrval` `_`-binders — the rfl bridges `allocateObject_arg_irrel`/`eqPtrval_loc_irrel`) |
  | `parent` | the `(parent, th)` slot | YES — value protocol (THREAD-DONE vs PROGRAM-DONE); constrained by `SeqWF` |
  | `stack` | `th.stack0` | YES — value protocol (RETURN vs PROGRAM-DONE); constrained by `SeqWF` |
  | `errno` | `th.errno` | no (builtin territory); quantified |
  | `proc` | `th.current_proc_opt` | YES — Erun's label-fiber selection |
  | `execLoc` | `th.exec_loc` | no (call push); quantified |
  | `currentLoc` | `th.current_loc` | read on library-location substitution (excluded by the cone's `isLibraryLocation = false`) and passed to memops (discarded by `eqPtrval`); quantified |
  | `runState` | discharge `rs` | YES — Erun reads `labeled` through it (read-only: `state_except_read`); `aid` draws stay per-step parameters as in the driver |

- **Live state is unchanged**: `(CoreExpr × EnvStack × Mem)` — the
  arena, the thread env stack, the memory. The audit's "expr tuple ×
  env × label map × Mem" is realized with the label map DERIVED
  (below), not tuple-carried.

- **The frozen profiles become instances.** `spikeCtx` and
  `procCtx p rs` are `MachineCtx` values definitionally equal to
  the old frozen profiles (`engineStepsU_spike`/`_proc`,
  `spikeCtx_thread`/`procCtx_thread` are `rfl`). No frozen example
  constant remains inside any judgment; the constants
  `Soundness.lean:73-109` freeze become one point of the context
  space, used only where exported statements pin the launch profile.

- **The label map is derived, not carried.** `MachineCtx.labels`
  computes the current procedure's registered fiber from
  `proc`/`extern`/`runState.labeled` exactly as step_ctx's Erun arm
  reads it (identity-fallback extern resolution; lookup-failure and
  no-proc panic channels collapse to the empty map = fail-closed
  absence of a step). Consequence proved in the probe: the
  `LabeledAt` TIE HYPOTHESIS DISAPPEARS from every theorem
  (`engine_step_matchU` has no tie; `labels_lookup_some` recovers
  the old tie as a derived fact when needed engine-side).

- **`primStep` IS the authoritative relation.** The iris Language
  instance is over `CoreRtU = (e, ρ, M)` / `CoreRValU`;
  `primStep p q = StepU p.M ... ∧ q.M = p.M ∧ no-forks`. The
  ghost/heap layer (`SpikeGS`, `StateInterp Mem Empty GF`,
  `pointsToCell`, all of Heap.lean) is expression-type-independent
  and is SHARED — only the `IrisGS_gen` bundle is per-language
  (probe: `instIrisGSU`, 7 lines).

- **One cone, one decomposition.** `FragU` is the single capability
  predicate over the same relation the logic and the engine
  characterization use; closure under steps is ONE theorem
  (`FragU.step`) with the jump successors' membership from the
  label-cone hypothesis. The manifest generates FROM it (§4). The
  decomposition judgment: `DecompJ` (with its `RedexJ` root set) is
  ALREADY the single decomposition — the six parallel cones are
  FragP/FragJ (unify → `Frag` = migrated `FragU`), Redex/RedexJ
  (RedexJ subsumes via `RedexJ.base`), Decomp/DecompJ (DecompJ
  subsumes via `Decomp.toJ`). S1b DELETES the P-variants and renames
  the J-variants; no new decomposition machinery is needed — the
  probe feeds the existing `DecompJ.root` directly.

- **One drive.** `driveU M` is the {step_ctx → discharge} loop with
  every immutable drawn from the context; `drive` and `driveJ rs`
  are definitionally its `spikeCtx`/`procCtx` instances
  (`driveU_spike`, `driveU_procJ` — proved). The drive/driveJ split
  disappears in S1b; exported statements keep their `drive`/`driveJ`
  vocabulary via the instance equations (zero statement change).

## 2. Alternatives rejected (criteria = the audit's requirements)

1. **Rehabilitate the pinned RelSem spine as the Iris language**
   (audit F-03 remediation option 1, first arm). Rejected for
   Phase 1: RelSem's state split is not syntax-facing (the audit
   itself flags atomicity/state-split unsuitability), the package
   has no import of it, and the arc plan's item 6 already scopes
   RelSem to trust-diagram documentation. The audit's acceptance
   criterion (one theorem tying primStep to the engine relation on
   the fragment) is met by the mirror + characterization route
   without a second derived layer to bridge.
2. **Carry the label map (or the whole context) as a separate Step
   index with tie hypotheses** (the status quo generalized).
   Rejected: this is exactly the F-03 "family of example profiles"
   failure mode — every new context component would grow a new
   index + tie. Deriving from one explicit context removes the tie
   class entirely (probe-demonstrated).
3. **Put MachineCtx in the Iris STATE rather than the expression
   tuple.** Rejected: the state interpretation would have to
   constrain it (stateInterp is about ownership, not immutable
   configuration), every points-to statement would drag the
   context, and `primStep`'s context-preservation (`q.M = p.M`)
   would become a state invariant needing its own bookkeeping. In
   the tuple it is preserved by construction, exactly as the label
   map was.
4. **A thread_state template field instead of named fields.**
   Rejected: hides which components the fragment reads (the F-03
   "hide it in a profile" defect in new clothes); the per-field
   table above is the point.
5. **Modeling the engine's panic channels as refusal outcomes to
   get two-sidedness for `run`.** Rejected for Phase 1: the
   fail-closed discipline (panic = absence of a step, excluded by
   WF shape) is load-bearing across the whole mirror; the J-lane
   classification needs only match-given-step (NotStuck supplies
   the step), which the audit explicitly sanctions when the needed
   direction is documented per-construct (§3).

## 3. Probe results (representative subset: store / run / case)

All probe theorems: `CerberusHeapLang/Phase1Probe/*.lean`; gates
green; probe cones consumed by nothing exported.

| Construct | Re-indexed rule | Characterization | Two-sided? |
|---|---|---|---|
| store | `StepU.store` (encoding premise at `M.tagDefs`) | `engine_step_matchU` + `engine_complete_storeU` | **YES, at any MachineCtx** (both directions; the per-rule step_ctx/discharge lemmas were already context-general — only the frozen `engineSteps` entries hid it) |
| case (value scrutinee) | `StepU.case_value` (verbatim re-index) | `engine_step_matchU` + `engine_complete_caseU` (+ new `step_ctx_case_illtyped` for the no-match refusal) | **YES, at any MachineCtx** — the F-01 row's engine pair now exists |
| run | `StepU.run` (label lookup in the DERIVED `M.labels`) | `engine_step_matchU` | **ONE-SIDED** (match-given-step) — the direction `drive_classifyU` consumes; the refusal channels at a jump are failwithI panics (unresolvable label / no proc / empty env), deliberately unmodeled (§2 item 5). Documented per-construct in the probe manifest row. |
| values | (terminal protocol) | `outcomesU_done` / `outcomesU_remove_annot` | two-sided under `SeqWF` |

- **The store small axiom re-proves over the unified language**
  (`wp_storeU`): statement = `wp_store` with the label-map slot
  generalized to the context and `hmv` at `M.tagDefs` (a frozen
  constant leaves a LOGIC RULE's statement); proof = the old proof
  with the unified inversions substituted, near-verbatim.
- **The adequacy chain re-derives at any context**:
  `spike_step_adequacyU` → `drive_classifyU` → `engine_adequacyU`
  (SeqWF + extern restriction as explicit hypotheses; tie
  hypothesis gone).
- **THE ORACLE RE-PROOF (K1)**: `exhibitB_semantic_unified` proves
  the exported `exhibitB_semantic` STATEMENT VERBATIM — old
  `SemTriple`, old `drive`, old footprints — through the unified
  route end to end (wp_storeU → adequacyU at `spikeCtx` →
  `driveU_spike`). Statement diff: ZERO. Downstream consumers
  (`exhibitB_engine`) use the semantic theorem opaquely, so their
  re-proofs are unchanged text.
- **THE ECASE PATH TO GREEN (F-01)**: `case_value` joins the
  unified cone (`FragU.case_value`, branch-closure and branch-size
  premises explicit), is covered by the closure theorem and the
  classification generically, has the two-sided engine pair, and
  has an engine-facing regression executing the rule —
  `case_regression_engine` (any SeqWF context) and
  `case_regression_drive` (over the OLD `drive`, verbatim
  vocabulary). Remaining for the full manifest row (S1b): the
  WP-consumer rule (wps_case over the unified language), binder
  patterns (substitution closure, §5.1), and the esize extension
  (§5.3).

## 4. The manifest generates from `Frag` (K4)

`scripts/phase1_probe_manifest.lean`: the row set is ENUMERATED
from `FragU`'s constructor list read out of the built environment —
no hand-authored row list. A cone constructor without a row mapping
throws (fail-closed: extending the cone without the manifest is a
red run); mapped cells stay name-and-kind checked (the Phase-0
discipline). S1c replaces `capability_manifest.lean`'s hand list
with this enumeration over the migrated full cone; Phase-0's
asserted constructor lists become derived.

## 5. Findings the probe surfaced (each with its S1b/S1c owner)

1. **Substitution closure is real Phase-1 work** (expected):
   binder-pattern `Ecase` needs `Frag` closed under
   `subst_sym_expr` (branch bodies are substituted before entering
   the cone). The probe's regression uses the wildcard pattern
   (empty substitution); the closure lemma
   (`Frag e → Frag (subst_sym_expr x v e)` on the cone's grammar)
   is S1b, mechanical induction.
2. **`extern` is load-bearing beyond Erun**: the engine resolves
   EVERY `PEsym` through the extern indirection
   (Core_eval.lean:142) — the whole evaluator bridge is pinned at
   `extern = fmapEmpty`. The probe carries the explicit hypothesis
   `M.extern = fmapEmpty` on the run characterization ONLY
   (registered probe restriction, named mover: S1b threads extern
   through `evalPexpr` + the bridge tower — mechanical but broad).
   This was invisible while extern was a frozen constant.
3. **The fuel measure was never extended to Ecase**:
   `esize (Ecase …) = 1` — branch sizes are uncounted, so the
   additive fuel accounting (`esize` grows ≤1 per step) is FALSE
   for case steps with non-flat branches. One more face of the F-01
   cone gap. S1b: add the `Ecase` arm to `esize`
   (`1 + max` over branches, the `Eif` precedent) + prove
   esize-invariance of `subst_sym_expr`; the probe's cone
   constructor carries the branch-size premise in exactly the shape
   the extended measure discharges. NOTE: this changes a
   SPECIFICATION-IDIOM definition (`esize` occurs in exported fuel
   side conditions). All existing exported programs are case-free,
   so every existing statement keeps its meaning and truth value
   verbatim; flagged for the operator as a statement-adjacent
   change class to sanction (§6).
4. **`SeqWF` (empty stack, no parent) is a permanent explicit WF
   constraint** — the value protocol genuinely reads both (RETURN /
   THREAD-DONE dispatch); nonempty stacks are procedure-return
   territory, outside the supported fragment. It replaces the
   frozen thread constants with a named, checkable hypothesis.
5. **The per-rule engine lemmas were already general.** The frozen
   context lived ONLY in the entry-point definitions
   (`engineSteps*`, the profiles, `drive`/`driveJ`) — the per-rule
   step_ctx/discharge lemmas quantify tds/file/ext/tid/parent/th.
   Migration cost is therefore concentrated in the RELATION,
   CONE, and THEOREM-STATEMENT layers, not the engine-equation
   layer (this is why the probe's characterization is thin).

## 6. Statement-change classes for the migration (K1 discipline)

Observed on the probe's re-proofs, proposed as the sanctioned
classes for S1b/S1c (everything else = itemized stop-and-ask):

- **(A) index plumbing**: `Q : LabelMap` slots become
  `M : MachineCtx` (interior theorems only; exported
  `drive`/`driveJ` statements are reached via the instance
  equations with ZERO text change — demonstrated by
  `exhibitB_semantic_unified`, `case_regression_drive`).
- **(B) tie-hypothesis deletion**: `LabeledAt`/`hQ` hypotheses
  disappear (statement WEAKENING of hypotheses = strengthening of
  theorems; audit-aligned).
- **(C) frozen-constant naming**: `fmapEmpty`-as-tagDefs inside
  rule statements becomes `M.tagDefs` (e.g. wp_store's `hmv`);
  at the spike instance the old statement is the definitional
  specialization.
- **(D) explicit WF hypotheses**: `SeqWF` (+ the temporary extern
  restriction) appear where frozen profiles silently assumed them.
- **(E) the esize extension** (§5.3) — definition change in the
  spec idiom, meaning-preserving on the existing corpus; needs
  explicit sanction.

## 7. Kill assessment

- **K1 (statement changes beyond sanctioned plumbing): NOT
  TRIGGERED.** The re-proved export is statement-identical; the
  observed change classes are enumerated above (§6), all
  plumbing-shaped except (E), which is flagged, not smuggled.
- **K2 (two-sidedness resists everywhere): NOT TRIGGERED.** Store
  two-sided at any context; case two-sided (new); run one-sided
  with the needed direction stated and consumed in the unified
  shape (the audit-sanctioned outcome).
- **K3 (perf wall): NOT TRIGGERED.** The probe adds ~1500 lines /
  4 modules; full-package build times unchanged in kind (minutes,
  not the tripwire); no heartbeat/maxRecDepth bumps anywhere.
- **K4 (manifest cannot generate from Frag): NOT TRIGGERED.**
  Demonstrated (§4).

## 8. Migration prescription (S1b/S1c)

**S1b — the relation/cone/soundness migration** (one slice, big):
1. `Step.lean`: re-index all 21 rules `Step Q` → `Step M`
   (mechanical: `Q` → `M.labels` in `run`; `M.tagDefs` in `store`;
   everything else verbatim); port the inversion suite (the probe's
   3-constructor versions show the per-rule shape; the full
   relation's inversions are the old proofs with the extra
   constructors' refutations unchanged).
2. Thread extern through `evalPexpr` (+ the PEsym arm's identity
   fallback) and re-run the evaluator-bridge tower at quantified
   extern; retire the probe's extern restriction.
3. `Soundness.lean`: delete `FragP`/`Redex`/`Decomp` (consumers
   switch through `FragP.toJ`/`Decomp.toJ`); rename
   `FragJ`/`RedexJ`/`DecompJ` → `Frag`/`Redex`/`Decomp`; add
   `Frag.case_value` (canonical value scrutinee; branch premises
   per the probe) + the substitution-closure lemma (§5.1) + the
   esize extension (§5.3); replace `engineSteps`/`engineStepsP`/
   `engineOutcomes*` with `engineStepsU`/`outcomesU` instances;
   re-prove `engine_step_matchJ` as `engine_step_matchU` over the
   full cone (per-construct cases are the existing proofs with the
   context threaded — probe-validated shape) and keep
   `engine_complete` as the straight-line completeness instance
   until per-construct completeness rows absorb it.
4. `Lang.lean`/`Heap.lean`: swap `CoreRt` → the context tuple
   (Heap untouched — shared); `Rules.lean`/`Wps.lean`: re-prove the
   small axioms and the statement judgment over the unified
   language (wp_storeU shows the per-rule cost: near-verbatim
   proofs; `wps` gains the `case` rule's consumer, closing the
   F-01 manifest row).
   Order within S1b: constructs first (relation + cone + match),
   then theorems per stratum (Rules → Wps → Adequacy) — the probe's
   file order, which kept every intermediate state buildable.
5. `Adequacy.lean`: replace `drive`/`driveJ` bodies with `driveU`
   instances (exported statements unchanged via the instance
   equations); re-prove classification/adequacy in the unified
   shape (probe-validated proofs, full cone).
6. Frozen-corpus oracle at the slice gate: every exported theorem
   re-proves with statement diffs only in classes (A)-(E);
   signature snapshot diffed and itemized.
7. The Ecase export completes: cone + match + completeness +
   `wps_case` consumer + an adequacy-level regression through the
   WP lane (the probe's drive-level regression is the interim).
8. One NEW non-example construct through the generic route (arc
   plan item 7's drift test) — candidate: `Ewseq` wildcard or the
   `Eif` at a fresh guard shape; pick at S1b briefing.

**S1c — instruments + claims surfaces** (one slice, small):
manifest generation from the migrated cone (replace the hand list
per §4); README/walkthrough/trust-diagram updates incl. the RelSem
paragraph (arc plan item 6); gate-4 upgrade to the cone-derived
manifest; retire the probe modules (their content IS the migrated
code by then) — prune-don't-merge applies to any probe text the
migration superseded.

Estimated slice count: S1b one heavy slice (the probe de-risked
its three hardest joints: index shape, adequacy re-derivation,
oracle reachability), S1c one light slice. If S1b's evaluator
extern-threading (§5.2) balloons, split it out as S1b′ before the
Wps stratum — pre-registered fallback, not a replan.
