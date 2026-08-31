# Phase-1 S1/S2 slice notes: restratification, coverage-preserving

[AGENT] S1/S2 worker record, per the two-phase arc plan
(`2026-08-31_two-phase-arc-plan.md` §Phase 1), the S0 probe
prescription (`2026-08-31_s0-probe-report.md` §6), and the mission
order (env into the language tuple + ACTION_EVAL phrasing; corpus
onto the stratified layer; frozen-corpus regression gate).

Commits: S1 `a7adaa2` (snapshot instrument + env/ACTION_EVAL
migration), S2 `2f5c652` (the `wps` layer over Core), this record.
Gates green at each commit (`scripts/test_unit.sh`: grep ban + both
package builds with in-build audits).

## 1. THE FROZEN-CORPUS REGRESSION GATE — RESULT: PASS

Instrument: `scripts/signature_snapshot.lean` (deterministic dump of
every CerberusHeapLang constant's kind + pretty-printed type), run
pre (commit `0bf3ddd` tree → `2026-08-31_phase1-signatures-pre.txt`,
825 constants) and post (this tree →
`…-signatures-post.txt`, 899 constants). Diff tallies (derived from
the two committed files by name-keyed comparison):

- **UNCHANGED: 743** — including, verbatim at the statement level,
  every headline export: `SemTriple` (type AND body — it still
  speaks `spikeThread e`), `Sat`/`Sat.mono`,
  `semantic_triple_sound`, `semantic_frame`, `prod_run_eq`,
  `sem_triple_prod`, `engine`-face exhibits
  (`exhibitA/B/C_engine`, `exhibitA_terminates`, `exhibitA_prod`),
  the semantic exhibits (`exhibitA/B/C_semantic`), the triple-level
  exhibits (`exhibit`, `exhibitC_triple`), `triple_seq`,
  `provenA/B/C/AProd`, the whole DriverCollapse surface
  (`prod_loop_done`, `driver2_done`, `finalize_done`), `drive`,
  `dischargeStep`, `FragP`/`Decomp`/`Redex`/`esize`, the entire
  Heap layer (`Coh`, `CellCoh`, `pointsToCell`, `storeM_success`,
  `loadM_success`, `StorableAt`), `spikeThread`(signature),
  `spikeRunState`, `spikeFile`, and the whole StmtProbe.
- **CHANGED: 81** (63 hand-stated + 18 auto-generated companions of
  the changed inductives). EVERY change falls in the two SANCTIONED
  delta classes (below); nothing else changed.
- **REMOVED: 1** — `instLanguageCoreExprMemEmptySpikeVal`, the
  AUTO-NAMED Language instance; its successor
  `instLanguageCoreRtMemEmptyCoreRVal` is the same instance renamed
  by the type change (the name encodes the expression/value types).
  Finding class (a) below; no content was removed.
- **ADDED: 75** — the runtime tuple (`CoreRt`/`CoreRVal` + record
  machinery), `EnvStack`/`spikeEnv`/`envThread`, the canonical-
  instance step constructors, `Step.env_invariant('),
  `wp_env_invariant`, tuple value-test lemmas, and the whole S2
  `wps` layer (`LabelMap`/`LabelSpec`/`wps(.pre)`/rules/collapse +
  the two stratified exhibit shapes).
- Sweep counts: 377 → **417** theorems (never decreased); boundary
  modules unchanged (`ProdEntry`/`ProdExhibit`), boundary theorem
  count **34 → 34**, boundary axioms unchanged (trio +
  `runEffectful` there, trio-exact everywhere else); banned-axiom
  sweep 899 constants clean; curated pins: all pre-existing pins
  pass UNCHANGED, +3 new pins (`wps_seq`, `wps_sound`, `wps_store`).
  No new axioms, no new qualifiers (no sorry/partial/unsafe
  anywhere; in-build sweeps enforce).

### Finding class (a): env-tuple plumbing [SANCTIONED, mission order]

The expected delta class — the environment joining the language
tuple. One justification for the class: the probe-validated S1
prescription makes the env a configuration component, so every
statement that mentions the step relation, the language types, or a
WP subject gains the componentwise env (a `ρ`/`EnvStack` component,
`CoreRt`/`CoreRVal` in place of `CoreExpr`/`SpikeVal` at the
Language layer, cons-shaped env parameters where the betas fire).
Instances (hand-stated, 60 of the 63): `Step` + its 8 constructors +
7 inversion/metatheory lemmas + `esize_succ`; `FragP.step`;
`Decomp.rebuild`/`step_factor`; the Language instance +
`primStep_eq`/`language_toVal_eq`/`instContextSseq`/`instIrisGS` +
the three determinism lemmas; `engineSteps(_*)`/`engineOutcomes`/
`EngineMatch`(+ctors)/`engine_complete` (env-GENERALIZED: the old
statements are the `spikeEnv` instances — strengthenings; the beta
lemmas and `engine_complete` take cons-shaped env per the engine's
`update_env` read); `drive_scrutinee`/`drive_value_pure`/
`drive_classify`/`DriveOk`/`Reach`(+`toPool`)/
`spike_step_adequacy`/`spike_engine_adequacy`; `wp_store`/`wp_load`/
`wp_ofVal`/`wp_annot(_reindex)`/`wp_sseq`/`spike_wp_wand`/`triple`/
`triple_frame`/`triple_conseq`/`mergeInto` (now `CoreRVal`-level;
the `SpikeVal`-level content is `SpikeVal.mergeInto`, added).
Def-BODY deltas invisible to the type diff, audited by hand:
`ProvenTriple` (WP subject `⟨e, spikeEnv⟩`, readout `CoreRVal.val`),
`spikeThread` (body refactored through `envThread e spikeEnv` —
definitionally the identical record literal), `drive_scrutinee` RHS
(`engineOutcomes` at `spikeEnv`). All class (a).

Two deliberate sub-decisions inside the class, each recorded:
- **Cons-shaped betas** (readiness R2 panic discipline): the
  engine's wildcard `update_env` is the identity on a NONEMPTY env
  stack and a `failwithI` PANIC on an empty one; the mirror rules
  fire only at `ev0 :: evs` — the panic channel is ABSENCE of a
  step, fail-closed, never absorbed. `wp_sseq`/`wps_seq`/
  `engine_complete` therefore quantify cons-shaped envs; the old
  statements are their `[fmapEmpty]` instances (strengthenings).
- **Exports pinned at `spikeEnv`**: `triple`/`ProvenTriple`/
  `SemTriple` and the exhibits stay at the frozen entry env (what
  the production driver parks for a parameterless `main`), keeping
  the exported statements textually stable; env-general triples
  arrive with binding patterns (phase 2), whose slice charter owns
  that restatement. The LANGUAGE and certification layers are
  env-general now (jump-ready).

### Finding class (b): ACTION_EVAL operand-premise phrasing
[SANCTIONED, mission order]

`Step.store/load/create` are stated over EVALUATED-OPERAND premises
(`valueFromPexpr peᵢ = some vᵢ`, Core_aux.lean:472) instead of
syntactic `PEval` patterns — the engine's own request-path dispatch
(step_action, Core_reduction.lean:424, fires ACTION_REQUEST exactly
when `act_valueFromPexpr` succeeds on every operand). Delta from
`act_valueFromPexpr`: only the `PEconstrained` PANIC channel, which
the `valueFromPexpr` premise excludes fail-closed
(`valueFromPexpr (PEconstrained …) = none`). `store(x, a+b)`
(non-value operands) is expressible by these STATEMENTS once phase
2 adds the engine's separate ACTION_EVAL step rule; the pexpr
lemma library was NOT built (mission order — one `rfl` recognizer
lemma `valueFromPexpr_val` only). The certified cone (FragP —
canonical shapes) is unchanged; `Step.*_canonical` restate the old
rule forms and are what the certification and small axioms apply.

## 2. Prescription deviations (probe report §6), each with reason

1. **`wp_sseq` re-proved by direct Löb over the Esseq factor
   structure** (`Step.sseq_inv`), not kept on `wp_bind`/Context and
   not derived as a corollary of `wps_seq` + a completeness lemma.
   Reasons: (i) the bind route's pointwise `wp_mono` step cannot see
   that e1's delivered values carry a cons-shaped env, which the
   beta step now requires — the direct proof (or the also-added
   `wp_env_invariant`) transports it; (ii) the frozen statement is
   generic in `(s, E)` while the probe's `wps` is `NotStuck`/⊤ —
   deriving would have weakened the statement or forced an
   (s,E)-parametrized `wps` the probe did not validate; (iii) a
   `wps`-completeness lemma (base WP → wps) would be FALSIFIED by
   S3's jump clause — a doomed lemma. The direct proof IS the
   base-WP face of the jump-aware sequencing argument: S3's jump
   disjunct lands as one more case. `instContextSseq` is RETAINED
   (still true and certified for the jump-free relation; its S3
   retirement is pre-declared in the Lang.lean header).
2. **The `wps` jump clause: the ABSENCE option** (of the mission's
   sanctioned "honest hypothesis/absence" pair). `wps.pre` has two
   clauses (value/step); `(Q : LabelMap, Ls : LabelSpec)` ride
   uncertified. Reason: the clause's payload (per-procedure label
   map indirection through `current_proc_opt`, jump-argument
   evaluation via the fuelled, state-threaded `full_eval_pexpr'`)
   is exactly S3's certification target; committing a clause shape
   now, with the toy's pure `evalOp` as the only model, would be
   speculative design — stop-short rather than redesign solo. The
   S3 delta is definition-local: the rule statements (all carrying
   `Q`/`Ls`) survive verbatim, proofs gain one case each;
   `wps_sound` gains the `blockSpecs` premise (pre-declared in the
   module header). Consequence: no `wps_run`/`blockSpecs` in phase 1
   (nothing to consult), exactly "no certified jump rules yet".
3. **`wps_seq` follows the probe statement literally** (no ▷ on the
   continuation; `SpikeVal.mergeInto` carries the LETS-ANNOT flow —
   the Core-only annotation residue the toy did not have; its cost
   is the `wps_annot(_reindex)` layer re-paid at this stratum, the
   known R-i price).
4. **`wps_store`/`wps_load` continuation form**: the footprint is
   ∀-quantified in the continuation wand (the toy had no footprint;
   `wp_store`'s ∃-post is mirrored premise-side). House seams
   `storeM_success`/`loadM_success` reused verbatim.
5. **No `wps_create`** at any layer: registered D26 (allocator
   cursor) — phase 2; cold-start creates ride the production entry
   unchanged. (The mission's "`wps_create`-level rules" item is
   satisfied by this recorded absence + the untouched
   allocateObject seams: there was no create small axiom in the
   frozen corpus to migrate.)
6. **New phase-1-only lemmas with pre-declared S3 retirement**:
   `Step.env_invariant(')` (no phase-1 rule writes the env) and
   `wp_env_invariant` (its WP internalization, needed by
   `triple_seq`'s value-forgetting assertion posts). Their S3
   deletion is an anticipated, documented statement removal — the
   jump rebinds the env.

## 3. Mechanical frictions (probe §6 list confirmed + additions)

Confirmed as house discipline: per-constructor simp lemmas for the
value tests (`toValRt_mk`, `toVal_sseq_node`, …; never unfolding
matches over variable scrutinees); cons-normalization; the
`ihave`-pure-assert borrow for `genHeap_valid`; `omega`.
Subst-direction discipline bit REPEATEDLY during this slice
(the surviving variable must end on the LEFT — several component
equations from triple-tuple inversions eliminate the wrong variable
otherwise; the `obtain rfl : kept = killed := h.symm` idiom is the
fix). New frictions solved here, recorded for S3:
- **Successor eta in reducibility witnesses**: `Reducible` witnesses
  over the record language need `⟨[], ⟨_, _⟩, _, [], …⟩` (an
  explicit constructor for the successor) — bare `_` leaves the
  projection `?r.e` stuck in unification.
- **Def-transparency at proof-mode leaves**: `iexact`/`iapply` match
  at reducible transparency, so plain defs (`ofVal`, `sseqExpr`,
  byte-image defs, `SpikeVal.mergeInto` under a binder) need a
  shell `rw [show lhs = rhs from rfl]` conversion at the use site.
- **Snapshot instrument scope**: the signature dump captures
  TYPES; for theorems that is the full statement, but def BODIES
  (e.g. `ProvenTriple`) must be audited by hand — done above; a
  body-including dump is a possible instrument upgrade for the
  phase-2 gate.

## 4. Gate record

- `scripts/test_unit.sh` ALL GREEN at each commit (grep ban; root
  package build + audit; cerberus-heaplang build + audit).
- cerberus-heaplang audit at this record: exhaustive sweep 417
  theorems within the declared boundary (34 in the production-entry
  boundary modules at trio+runEffectful, all others trio-exact);
  banned-axiom sweep 899 constants clean; all curated pins green
  (pre-existing pins byte-identical; +3 S2 pins).
- Build behavior: per-module elaboration seconds-scale throughout;
  no grind events; no heartbeat/maxRecDepth changes anywhere.
