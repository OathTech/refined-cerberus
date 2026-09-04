# ar5-manifest — the truthful capability report, one module classification, the fail-closed inventory, the client-boundary check, the claim matrix (2026-09-04)

Worker record. Branch `ar5-manifest` (from main `5d08237`). Scope: the
external audit `../../docs/2026-09-04_reynolds-ohearn-separation-logic-audit.md`
— **Finding 1** (the capability manifest overstates rule coverage) in full,
the **script/inventory half of Finding 2** (module inventories, stale seeds,
`(MISSING)` fail-open), and **remediations 3** (negative architectural
checks) and **6** (a claim matrix). The concurrent worker `ar5-readout` owns
the other half of Finding 2 (relocating the dead-object readout helpers of
`DisposeExhibit`/`MallocListExhibit` into Adequacy/API); this slice touched
none of `Adequacy.lean`, `API.lean`, `DisposeExhibit.lean`,
`MallocListExhibit.lean`, `Audit.lean`, and changed NO theorem or definition
anywhere in `CerberusHeapLang/`. The audit is copied verbatim into this
repository (byte-identical to the primary checkout's untracked copy,
verified by `cmp` at commit time).

Provenance tags as in `../../docs/DECISIONS.md`. The user was offline: every
decision below is [AGENT] and is stated as such.

## 1. The premise, measured

At `5d08237` the manifest generator's `declaredNoRule` was `| _ => none`
while ARCHITECTURE/README/Soundness described no-rule variants; its rows were
(constructor, rule) pairs and its prose said "covering rule" and "0 red".
Reading the rules' hypotheses against the engine's admitted successes:

- `wps_store`/`wpt_store` and every store rule are stated at `storeExpr` =
  `Store0 false` (Rules.lean:63-69); `Frag.store` admits `lk = true`, whose
  engine success flips `isReadonly` (CerbMem `storeM`, `isLocking` arm).
- `kill_atomic` carries `hstatic : is_dynamic kind = false` over
  `pointsToCell`; `free_atomic` carries `hdyn : is_dynamic kind = true` over
  `regionOwn id a n (.own 1)` at `cellPtr id a`. `killM` succeeds at the
  static kill of a live REGION (the `dynamicAddrs` check is guarded by
  `isDynamic`) and at `free(NULL)` (`PVnull` arm, `isDynamic = true`): no
  rule for either.
- `create_atomic` carries `hsz : 0 < sizeofCtype`, `hatom : atomicTy ty =
  false`, `hinert`; `allocateObject` pads a zero-size type to size 1 and
  succeeds; `alloc_atomic` carries `hcost : 0 < regionCost alignN sizeN`;
  `allocateRegion` succeeds at `sizeN.toNat = 0` (every non-positive size).
- Found by reading further (not in the brief): the bundles fix the pointer
  shape `cellPtr id a = PVconcrete none a`, so loads/stores through a
  UNION-MEMBER pointer (`PVconcrete (some membr) addr`, an engine success
  that also updates `lastUsedUnionMembers`) have no rule; the read-only
  cell load has the atomic specification `load_atomic_readonly` but no
  `wps_`/`wpt_` face; `eqPtrval` at a FUNCTION pointer against a CONCRETE
  pointer reads the state's `funptrmap`, so `wps_memop_ptreq`'s premise
  `∀ σ, applyMemM (eqPtrval …) σ = some (b, σ)` cannot be met in general;
  `eqPtrval` at differing provenance forks (`msum`) and the mirror is
  fail-closed there.
- `parametric_inventory.lean` was not run by the gate, listed 6 client
  modules against the manifest's 18, and its `analyze` rendered a missing
  name as a `(MISSING)` row with exit 0. MEASURED (a twenty-line probe
  script over the built environment at this pin, `env.contains` per old
  seed, run at `3f21303`; verbatim): 14 `EXISTS`, and
  `CerberusHeapLang.engine_adequacyU: MISSING`,
  `CerberusHeapLang.engine_adequacyU_alloc: MISSING`,
  `CerberusHeapLang.semantic_triple_soundU: MISSING`,
  `CerberusHeapLang.semantic_frameU: MISSING`,
  `CerberusHeapLang.wpt_engine_boundU: MISSING`,
  `CerberusHeapLang.wpt_engine_boundU_alloc: MISSING` — the F1 renaming and
  the `driveU` deletion. `Decomp.step_factor`, `Frag.step`, `Frag.decomp`,
  `Frag.pot_step_bound` EXIST (Soundness.lean:1004/4611/4375,
  Potential.lean:190) — the brief's "ten stale" counted them; corrected here
  to SIX ([AGENT], measured as stated).

## 2. The variant classification, as landed (docs/CAPABILITY_MANIFEST.md)

Data: `variants` in `scripts/capability_manifest.lean` — 47 rows over the 23
constructors of `Frag`. Classes: RULE (partial + total, both theorems, both
in a consumer's proof-term cone), RULE-TOTAL-UNDEMONSTRATED (see §3),
PARTIAL-ONLY (none at present), NO-RULE (reason + deciding record),
OUT-OF-SCOPE (reason + record). Engine kills/UB/panics are not rows.

| Constructor | Variant (engine-success shape) | Class | Rules / reason |
|---|---|---|---|
| `val_pure` | the delivered value | RULE | `wps_ofVal`/`wpt_ofVal` |
| `store` | `Store0 false`, whole object cell, full ownership | RULE | `wps_store`/`wpt_store` (also `_plain`, `store_atomic`) |
| `store` | `Store0 false`, typed sub-range of an object | RULE | `wps_store_at`/`wpt_store_at` (also `_cell_at`, `storeAt_atomic`) |
| `store` | `Store0 false`, typed sub-range of a region (K5) | RULE | `wps_store_region_at`/`wpt_store_region_at` (also `_regionOwn_at`, `regionStoreAt_atomic`) |
| `store` | `Store0 true` — the locking store | NO-RULE | K1 audit N-2; `Frag.store` docstring |
| `store` | through a union-member pointer | NO-RULE | bundles fix `cellPtr`; [AGENT] this slice |
| `load` | whole object cell, any fraction, non-trap | RULE-TOTAL-UNDEMONSTRATED | `wps_load` consumed (Exhibit, StructExhibit); `wpt_load` proved, no consumer |
| `load` | typed sub-range of an object | RULE | `wps_load_at`/`wpt_load_at` |
| `load` | typed sub-range of a region (K5) | RULE | `wps_load_region_at`/`wpt_load_region_at` |
| `load` | at a read-only cell (`readonlyCell`) | NO-RULE | `load_atomic_readonly` exists, no statement-level face, no consumer; [AGENT] this slice |
| `load` | through a union-member pointer | NO-RULE | as the store; [AGENT] this slice |
| `create` | positive-size non-atomic decode-inert type, from budget | RULE | `wps_create`/`wpt_create` |
| `create` | zero-size type (engine pads to 1) | NO-RULE | `hsz`; `create_atomic` docstring; [AGENT] this slice |
| `create` | atomic object type | NO-RULE | `hatom`; [AGENT] this slice |
| `create` | type whose unspecified image is not decode-inert | NO-RULE | `hinert`; [AGENT] this slice |
| `kill` | static kill of a live created object, full ownership | RULE | `wps_kill`/`wpt_kill` (also `_emp`, `kill_atomic`) |
| `kill` | dynamic kill (`free`) of a live region, full ownership | RULE | `wps_free`/`wpt_free` (also `_emp`, `free_atomic`) |
| `kill` | static kill of a live REGION | NO-RULE | K2 audit N-2 → K3 notes §6; DECISIONS 2026-09-03 K3 entry |
| `kill` | `free(NULL)` | NO-RULE | K3 notes §6 |
| `kill` | `free` of a created object at a colliding base | NO-RULE | KNOWN-OPEN-ITEMS A3; K3 notes §6 |
| `kill_op` | operand evaluates to a pointer | RULE | `wps_kill_eval`/`wpt_kill_eval` |
| `alloc` | positive cost (`n > 0`, or `n ≤ 0` at `al ≥ 2`) | RULE | `wps_alloc`/`wpt_alloc` |
| `alloc` | zero cost (`n ≤ 0 ∧ al ≤ 1`) | NO-RULE | K3 audit N-2; K3 notes §4(c)/§6 |
| `alloc_op` | operands evaluate to integers | RULE | `wps_alloc_eval`/`wpt_alloc_eval` |
| `sseq` | wildcard sequencing, either head value shape | RULE | `wps_seq`/`wpt_seq` |
| `annot` | dyn-annotation frame + ANNOTS merge | RULE | `wps_annot`/`wpt_annot` |
| `save` | `PePure` initializers, TAU or EVAL arm | RULE | `wps_save`/`wpt_save` (also `_vals`, `_eval`) |
| `if_` | guard `Vtrue` | RULE | `wps_if_true`/`wpt_if_true` (also `wps_if`/`wpt_if`) |
| `if_` | guard `Vfalse` | RULE | `wps_if_false`/`wpt_if_false` |
| `run` | label resolves, every argument evaluates | RULE | `wps_run`/`wpt_run` |
| `run` | surplus argument that does not evaluate | OUT-OF-SCOPE | `OpenRound.run_surplus`; fragment closure |
| `sseq_spec` | head delivers `Specified(ov)` | RULE | `wps_seq_spec`/`wpt_seq_spec` |
| `pure_sym` | symbol bound in the environment | RULE | `wps_pure`/`wpt_pure` |
| `pure_sym` | unbound symbol naming a `Proc` | OUT-OF-SCOPE | `OpenRound.eval_uncovered`; fragment closure |
| `load_op` | operand evaluates to a pointer | RULE | `wps_load_eval`/`wpt_load_eval` |
| `sseq_sym` | `BareHead` head, bare value | RULE | `wps_seq_sym`/`wpt_seq_sym` |
| `sseq_sym` | head delivering an annotated value | OUT-OF-SCOPE | `hb : BareHead e1`; fragment closure |
| `memop_vals` | `PtrEq`, state-independent verdict (null/null, null/concrete, function/function, same-provenance concrete) | RULE | `wps_memop_ptreq`/`wpt_memop_ptreq` |
| `memop_vals` | `PtrEq`, differing provenance (engine forks) | OUT-OF-SCOPE | `applyMemM` none at an ND fork; `memop_fork` |
| `memop_vals` | `PtrEq`, function vs concrete (reads `funptrmap`) | NO-RULE | the rule's `∀ σ` premise; [AGENT] this slice |
| `memop_op` | evaluating round | RULE | `wps_memop_eval`/`wpt_memop_eval` |
| `store_op` | evaluating round (either locking mode; successor classified by the `store` rows) | RULE | `wps_store_eval`/`wpt_store_eval` |
| `case_value` | matching pattern at a value scrutinee | RULE-TOTAL-UNDEMONSTRATED | `wps_case_value` consumed (CaseExhibit); `wpt_case_value` proved, no consumer |
| `wseq` | weak sequencing | RULE-TOTAL-UNDEMONSTRATED | `wps_wseq` consumed (WseqExhibit); `wpt_wseq` proved, no consumer |
| `call` | declared procedure, arity matches, at the root | RULE | `wps_call_root`/`wpt_call_root` |
| `call` | declared procedure, in an evaluation context | RULE | `wps_call`/`wpt_call` |
| `call` | `Eproc _ (Impl _) _` | OUT-OF-SCOPE | `callRedex?` none; C2 |

Tally (derived from the generator's machine line): 27 RULE, 3
RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 12 NO-RULE, 5 OUT-OF-SCOPE.
Consumer modules: 16 (§5). All 27 RULE rows have BOTH judgments consumed —
measured, not assumed: the first generator run (with those three rows as
RULE) reported exactly `wpt_load`, `wpt_case_value`, `wpt_wseq` as "consumed
by no consumer module"; every other total rule has a consumer.

**What green now establishes, exactly** (the manifest header says the same):
the hand-maintained variant table covers every constructor of `Frag` in the
built environment and names no stale constructor; every theorem a row names
exists and is a theorem; every RULE row's partial AND total rule, and every
PARTIAL-ONLY rule, lies in the proof-term dependency cone of at least one
consumer module (the modules classified `positive-client` or
`declared-smoke`), listed in the row; the module classification is complete
and exact; every declaration the claim matrix names exists. Green does NOT
establish that the variant table is exhaustive over the engine's success
shapes (it is a reviewed reading of the engine arms, not a theorem), that a
rule is the strongest statement of its variant, or that a consumer's
dependency on a rule is the load-bearing step of its headline proof rather
than incidental; a NO-RULE or OUT-OF-SCOPE row is a stated absence, not
coverage. The former "0 red = every constructor has a covering rule" reading
is removed from the manifest header, ARCHITECTURE (§7 K5/K3 bullets) and
README ("Scope", "How to build and verify"); `Examples/MirrorCoverage.lean`'s
header made no such claim and is untouched.

## 3. [AGENT] deviation: the class RULE-TOTAL-UNDEMONSTRATED

The brief asked for exactly four classes and for a RULE row to be red when
either judgment's rule has no consumer. Three total rules — `wpt_load`,
`wpt_case_value`, `wpt_wseq` — are proved and consumed by no client. The
slice forbids theorem and exhibit changes (no consumer can be added here);
classifying them PARTIAL-ONLY would misstate that no total rule exists;
leaving them RULE would land a red gate. Decision: a fifth class,
RULE-TOTAL-UNDEMONSTRATED — the partial rule must be consumed (red
otherwise), the total rule must exist as a theorem, and the row turns RED
the day a consumer of the total rule appears ("reclassify as RULE"), so the
data cannot go stale in the flattering direction. Each row names its mover:
a total exhibit loading a whole cell (every total client loads through a
view), total twins of `CaseExhibit` and `WseqExhibit`. The class is stated
in the generator header, the manifest header, ARCHITECTURE §7 and README.
The three are ALSO the claim matrix's stated exclusion of C3 (the
root-of-trust lane runs on no closed statement over them).

## 4. The module classification and the inventory decision

`scripts/module_classes.tsv` (39 rows, TAB-separated: module, class,
internals-allow, note) is the one authoritative classification; the manifest
reprints it. Classes and members:

| Class | Members | Consumer | Boundary check |
|---|---|---|---|
| `core` | Step, Lang, Heap, EnvLaws, Rules, Wps, Wpt, Soundness, EvalClass, Potential, Round, Adequacy, TotalAdequacy, DriverCollapse, API (15) | no | exempt; the import-direction speedbump's protected set |
| `production-core` | ProdLoop, ProdEntry | no | exempt |
| `audit` | Audit | no | exempt |
| `positive-client` | Exhibit, LoopExhibit, FibExhibit, ArrayExhibit, ListRevExhibit, TreeRotExhibit, CaseExhibit, WseqExhibit, StructExhibit, AllocExhibit, DisposeExhibit, RegionLoopExhibit, MallocListExhibit, FibRecExhibit (14) | yes | applies |
| `declared-smoke` | Examples.CallSmoke, Examples.ReadinessSmoke | yes | applies |
| `semantic-test` | Examples.MirrorCoverage | no | exempt |
| `engine-mirror-test` | — (vocabulary reserved; MirrorCoverage holds its `engine_step_matchU` instances beside its `Step` witnesses and is classified by its own header) | no | exempt |
| `production-wrapper` | ProdExhibit, ProdLoopExhibit | no | exempt |
| `negative-test` | DivergeExhibit | no | exempt |
| `example-support` | Examples.Layout | no | applies |

Changes against the former 18-module consumer set: `ProdExhibit`,
`ProdLoopExhibit` (production wrappers) and `DivergeExhibit` (negative test)
are no longer consumers — their rule use is through the clients they wrap
(no rule lost a consumer by this: the first run over the 16 showed the same
red set as §2); `Examples.ReadinessSmoke` joins (its `twoField_*` derived
rules consume `wps_load_at`/`wps_store_at`/`wps_create` — it IS a client of
the rules, "API practice" notwithstanding). Every instrument fails hard on
an unclassified package module, a classified module absent from the build,
or a class outside the vocabulary (plant D below).

**Inventory decision [AGENT]: `parametric_inventory.lean` stays ON DEMAND**,
fail-closed on its configuration. Reasons: (i) its client-module section
has a cheap text-based twin in the gate now (the boundary check), (ii) it
reports counts without a verdict — a measurement per claim point that
nobody diffs is gate cruft under the speedbump ruling, (iii) it costs a
full-import Lean run (97 s measured) per invocation. Consequence for the
advertising: README's "on demand" sentence now says how the line is checked
(textually in the gate, at the proof-term level on demand);
`API.lean:19-22` still says "measured, not gated … on demand" — TRUE and
unchanged (API.lean is the concurrent slice's file; the sentence should gain
a pointer to the boundary check when that slice or the next one touches the
header — noted as a follow-up, not a defect). Seeds refreshed: the six
stale names go; the total lane's `wpt_driver_done`, `wpt_driver_done_alloc`,
`wpt_driver_done_procs`, `prod_run_eqJ`, `prod_run_eqJ_procs`,
`prod_run_safe_procs` are added; the script imports the whole package.
Its 2026-09-04 reading (verbatim lines from the run at `56e1fed`):

```
INVENTORY: 132 rule theorems, 24 export seeds (all resolved), 16 client modules
- Step relation unfolded by definition in the rule's OWN proof (StepDef direct > 0): 38
- Judgment unfolded (`wps.pre`/`wpt.pre` direct): 34
- Ghost/cursor/CohG internals: direct > 0: 8; transitive > 0: 40
- AllocExhibit: 16 theorems; Ghost-direct 0; StepDef-direct 0; StepLem-direct 0; Judg-direct 0; Plan-direct 0
- ArrayExhibit: 29 theorems; Ghost-direct 1: `arr_wp_readout`; StepDef-direct 0; StepLem-direct 0; Judg-direct 0; Plan-direct 1: `arr_wp_readout`
- ListRevExhibit: 89 theorems; Ghost-direct 0; StepDef-direct 0; StepLem-direct 0; Judg-direct 0; Plan-direct 0
- StructExhibit: 33 theorems; Ghost-direct 2: `struct_create_store_adequacy`, `struct_create_store_adequacy_prodMem₀`; StepDef-direct 0; StepLem-direct 0; Judg-direct 0; Plan-direct 2: `struct_create_store_adequacy`, `struct_create_store_adequacy_prodMem₀`
```

Every client has StepDef/StepLem/Judg-direct = 0. The `Ghost-direct = 1` of
the `*_wp_readout`/`*_adequacy` theorems in ten clients is the documented
exception (API.lean): `project_triple_pure`'s `hpost` premise names
`CohG`/`metaInterp`, which therefore appear in the client's proof term
through the projection lemma's TYPE — the text-based check finds no such
mention in those modules, consistently.

## 5. The client-boundary check and its plants

`scripts/boundary_check.sh` (repository root; hooked into the full tier of
`scripts/test_unit.sh` as "speedbump: client boundary"). Comments are
stripped with a nesting-aware perl substitution that keeps newlines (line
numbers are the source's); then `grep -nE` for the coupling invariant and
state interpretation (`CohG`, `metaInterp`, `byteInterp`, `cursorInterp`,
`budgetInterp`, `budgetAuth`, `stateInterp_iff`, `stateInterp_eq`), the
judgment unfoldings (`wps.pre`, `wpt.pre`, `wps_unfold`, `wpt_unfold`), the
mirror transition (`Step.<name>`) and the generated engine's transition and
driver definitions (`step_ctx`, `one_step0`, `step_action`,
`drive_nonmemory_steps*`, `driver2`, `loop_step_frag*`,
`engine_step_matchU`, `CerberusRound`, `cerberusRound*`). Subjects: the
classes `positive-client`, `declared-smoke`, `example-support`. Exempt by
class: everything else. Allowances (the TSV's third cell) print as
ALLOWLISTED with the reason; an allowance with no hits left prints a
WARNING, not red.

Landed allowances: `DisposeExhibit` (9 mentions: `deadObj_dead_keep`,
`deadNodes_dead` over `CohG`/`metaInterp`) and `MallocListExhibit` (6:
`deadRegions_dead`) — "being removed by ar5-readout"; and `Exhibit` (1:
`progA_wpt` at Exhibit.lean:585 opens `stateInterp_iff` directly) — FOUND BY
THE CHECK on its first run, not in the brief; `progA_wpt` is consumerless
since F1 (KNOWN-OPEN-ITEMS C3), so its deletion or a rewrite over the public
`stateInterp_readout` removes the entry. Measured hits in every other
subject module: 0 (the `Step.`/`step_ctx` mentions of LoopExhibit,
FibExhibit, ListRevExhibit, CaseExhibit, WseqExhibit, FibRecExhibit are in
comments and are correctly not counted).

Current tree (verbatim tail): `BOUNDARY: 17 modules checked, 16 internals
mention(s) in total, exit=0`.

Plants (verbatim):

- PLANT 1 — `theorem plant_cohg … have := @CohG` appended to
  `LoopExhibit.lean` (positive-client, no allowance):
  `FAIL: LoopExhibit — 1 internals mention(s) in a positive-client module (no allowance):`
  `      LoopExhibit:551:  have := @CohG`
  `BOUNDARY: 17 modules checked, 17 internals mention(s) in total, exit=1` — exit 1.
- PLANT 2 — the same names inside a block comment and a `--` comment only:
  `ok:   LoopExhibit — 0 internals mentions` … `exit=0`.
- PLANT 3 — an allowlisted module with its hits removed (every `CohG`/
  `metaInterp` in `DisposeExhibit.lean` renamed):
  `ok:   DisposeExhibit — 0 internals mentions; WARNING: allowlist entry unused, remove it (readout helpers …)`
  `BOUNDARY: 17 modules checked, 7 internals mention(s) in total, exit=0` — exit 0.

Files restored after each plant (`git status` clean on the planted file).

## 6. The manifest generator's plants (verbatim)

Each plant is a copy of the generator (or a temporary edit of the TSV /
CLAIMS.md, restored afterwards) run with `lake env lean`; exit 1 in every
case, the diagnostic as printed:

- A — a row naming `Frag.wseq_plant` instead of `Frag.wseq`:
  `- **RED**: constructor `Frag.wseq` has NO variant row (MISSING — classify it)`
  `- **RED**: variant row names `Frag.wseq_plant`, not a constructor of `Frag` (stale row)`
  `… error: capability manifest: 2 red finding(s) — see the table and PROBLEMS above`
- B — a RULE row naming `wpt_alloc_eval_plant`:
  `| `Frag.alloc_op` | … | RULE | `wps_alloc_eval` — AllocExhibit | `wpt_alloc_eval_plant` — **RED: not in the environment** | |`
  `… 1 red finding(s)`
- C — `wpt_case_value` classified RULE (its total has no consumer):
  `| `Frag.case_value` | … | RULE | `wps_case_value` — CaseExhibit | `wpt_case_value` — **RED: consumed by no consumer module** | |`
  `… 1 red finding(s)`
- D — `TreeRotExhibit` deleted from the TSV:
  `- **RED**: module `TreeRotExhibit` is in the environment but NOT classified in scripts/module_classes.tsv`
  `… 1 red finding(s)`
- E — a claim row naming `project_triple_pure_plant`:
  `- **RED**: docs/CLAIMS.md C2: `project_triple_pure_plant` is not in the environment`
  `… 1 red finding(s)`
- F — `wpt_store` declared RULE-TOTAL-UNDEMONSTRATED though consumed:
  `| `Frag.store` | … | RULE-TOTAL-UNDEMONSTRATED | `wps_store` — Exhibit, LoopExhibit | `wpt_store` — **RED: now consumed by Exhibit — reclassify the row as RULE** | mover: plant |`
  `… 1 red finding(s)`

Inventory plant — the stale seed `engine_adequacyU` appended to
`exportSeeds`: exit 1, the whole output being the one line
`… error: parametric_inventory FAIL: export seed `CerberusHeapLang.engine_adequacyU` is not a declaration of the built environment (stale configuration — refresh it)`
(no measurement printed — the resolution check precedes the measurement).

Generator cost: 8 s per run (the cone is memoized and pruned to modules
whose import closure reaches a rule module); the old constructor-level
generator had the same shape. The full gate's speedbump section therefore
grew by the boundary check (< 1 s) only.

## 7. Surfaces changed

- `scripts/capability_manifest.lean`, `scripts/module_classes.tsv` (new),
  `scripts/parametric_inventory.lean`, `docs/CAPABILITY_MANIFEST.md`
  (regenerated), `docs/CLAIMS.md` (new), `../scripts/boundary_check.sh`
  (new), `../scripts/test_unit.sh` (hook; the import-direction protected
  set is now the TSV's `core` class — 15 modules, the same list as before;
  wording), `ARCHITECTURE.md` (§7: the two "0 red" tallies replaced; a new
  paragraph "The instruments around the claims"), `README.md` ("Scope"
  manifest paragraph; the rule-table consumer sentence; the API-line
  paragraph; "How to build and verify"), `../docs/2026-09-04_reynolds-ohearn-separation-logic-audit.md`
  (the audit, verbatim copy), this record.
- NOT changed: any `.lean` under `CerberusHeapLang/` (zero theorem or
  definition changes; the FAST gate rebuilt nothing — 373 pins trio-exact
  as at `e34b30b`/`5d08237`), `docs/DECISIONS.md`, `KNOWN-OPEN-ITEMS.md`
  (the orchestrator maintains it; candidate entries: the `progA_wpt`
  finding belongs under C3; the three undemonstrated totals and the
  union-member / read-only / function-vs-concrete NO-RULE variants are new
  B-class disclosures).

## 8. Follow-ups handed on (not done here, by scope)

1. Consumers for `wpt_load`, `wpt_case_value`, `wpt_wseq` (total twins of
   the whole-cell load, `CaseExhibit`, `WseqExhibit`) — turns the three
   RULE-TOTAL-UNDEMONSTRATED rows into RULE (the generator will demand it).
2. `progA_wpt` (Exhibit.lean): delete (KNOWN-OPEN-ITEMS C3) or rewrite over
   `stateInterp_readout`; then drop the `Exhibit` allowance.
3. When `ar5-readout` lands: drop the `DisposeExhibit`/`MallocListExhibit`
   allowances (the check warns until then).
4. `API.lean:19-22`: add the boundary check beside "on demand" at the next
   header touch.
5. The union-member-pointer, read-only-cell-load and function-vs-concrete
   `PtrEq` NO-RULE rows are [AGENT] classifications from reading the engine;
   a reviewer confirming or promoting them (a `readonlyCell` statement-level
   rule is one lemma away from `load_atomic_readonly`) closes the
   "[AGENT] this slice" provenance.

## 9. The gates (verbatim)

Commit 1, `56e1fed` (the instruments, the audit copy, the regenerated
manifest, the claim matrix), on the FAST gate (no Lean source changed):
```
info: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang export pins: 373 trio-exact
Build completed successfully (456 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

FULL gate, run on the tree `56e1fed` + the prose edits of commit 2
(ARCHITECTURE.md, README.md, this record — no file any gate reads), 17 s
wall (the build was up to date). Verbatim, the gate and speedbump lines:
```
info: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5161 constants of every kind swept, internal details included — 
Build completed successfully (456 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 15 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
[… 33 per-module boundary lines, three ALLOWLISTED with their hits …]
BOUNDARY: 17 modules checked, 16 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```
Exit status 0. The same FULL gate is re-run on the committed head after
commit 2 and its tail reported to the orchestrator (the record cannot
contain its own commit's hash).
