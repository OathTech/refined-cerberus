# The demo logic — state of the union and master plan to "finished"

Status: DRAFT for the operator's ratification [AGENT orchestrator, 2026-09-07],
written at main `777ca0f`. This document is the single place that says what
"finished" means for the Reynolds/O'Hearn demo (`cerberus-heaplang/`), what
exists, what is missing against that definition, where every partial solution
sits, and the ordered work to close the gap. It supersedes the ordering in the
2026-09-05 status snapshot §4 and the landing charter's L-list as the plan of
record; both remain as records. It is a plan, not a ruling: §7 lists the
decisions that are the operator's. Companion: the cerberus-lean requests
register, `docs/2026-09-07_cerberus-lean-requests-register.md`.

Every count below was measured at `777ca0f` and is labelled DERIVED where it is
a tally; every quoted ruling is verbatim from `docs/DECISIONS.md`.

## 0. The definition of done ([USER 2026-09-07], verbatim)

"The done state … is that our logic (1) is recognisably Reynolds/O'Hearn
reasoning, i.e a separation logic (2) it is built on a real, faithful iris
layer which can be extended later to build refined-cerberus (3) the iris layer
is built on cerberus-lean, and (4) the programs that are proved are genuine
outputs of the Cerberus-pipeline, i.e not synthetic core programs. And that a
reasonable PL expert reviewer would view the logic as good and complete".

Standing rulings that bound the scope: [USER 2026-09-04] "The demo should be
the best possible version of Reynolds/O'Hearn … Fancy logic features aren't
needed for that purpose" (masks and function pointers → the RefinedC arc);
[USER 2026-09-04] the aim is "a logic over Core emitted as an output from C
code. Authored-core is just a confection"; the feature set is CLOSED on the
logic axis and OPEN on the dialect axis for covered features (arc E);
[USER 2026-09-07, R5] E6/E7 (calls, the scheduler lift) "stays as residual
until we've finished the scheduler completely".

How each criterion is made checkable in this plan:

| criterion | checkable form | status at `777ca0f` |
|---|---|---|
| (1) recognisably Reynolds/O'Hearn | the classical rule set exists, is proved sound against the engine, and is USED by clients: local memory axioms, frame, consequence, sequencing, conditionals, loops, procedures; partial AND total judgments with the refinement between them | MET for the covered fragment (§2.1); three visible blemishes a reviewer would name (§3.1) |
| (2) a real, faithful, extensible iris layer | iris-lean's WP instantiated on a `Language` instance of the engine's rounds; the coupling (`stateInterp`) is a genuine Iris ghost-state coupling; the layer can be extracted as a library the RefinedC-family layer imports | MET as a layer; NOT yet extracted (§5, item V2-1) |
| (3) built on cerberus-lean | every export's referent is `CerbND.runND (_root_.drive …) (initial_driver_state …)` of the pinned semantics, at every fuel above a program-derived floor; the mirror and the collapse are proof devices only | MET; boundaries recorded (A5 panic arms, A3 upstream defect, B9, B12) |
| (4) genuine pipeline outputs | the certified programs are the elaborator's emitted Core for real C files, and the FILE in the statement is the pipeline's whole file, not a hand-built one | HALF MET: the programs are emitted and text-checked; the file is hand-built with a transcribed three-function std.core fragment (A7) — the largest gap (§3.4, item V1-1) |
| reviewer standard | a fresh PL-expert review against (1)–(4) finds no gap it would call disqualifying | NOT YET RUN; defined as the v1 exit gate (§5, item V1-6) |

## 1. What exists — the inventory at `777ca0f`

### 1.1 The package, in numbers (DERIVED)

| quantity | value | source |
|---|---|---|
| Lean in `cerberus-heaplang/CerberusHeapLang/` | 79 560 lines; largest: Soundness 10 539, Round 7 455, Step 6 398, Wps 5 556, Wpt 5 318, Heap 4 859, DriverCollapse 2 970, EvalClass 2 744, Adequacy 2 358, Rules 1 826 | `wc -l` |
| modules classified | 60 (19 `core`, 26 consumer = 24 `positive-client` + 2 `declared-smoke`, 2 `negative-test`, 2 `semantic-test`, 3 `production-wrapper`, 3 `production-core`, 4 `example-support`, 1 `audit`) | `scripts/module_classes.tsv`; manifest `MODULES:` line |
| pinned exports | 906 trio-exact (`propext`, `Classical.choice`, `Quot.sound` exactly) + 6 axiom-free | `Audit.lean` `trioExports`/`axiomFreeExports`; gate line `export pins: 906 trio-exact, 6 axiom-free-exact` |
| claims | 18 rows C1–C18, 195 declaration names checked | `docs/CLAIMS.md`; manifest `CLAIMS:` line |
| construct coverage | 35 `Frag` constructors, 78 engine-success variants: 47 RULE, 24 NO-RULE, 7 OUT-OF-SCOPE, 0 undemonstrated | `docs/CAPABILITY_MANIFEST.md` `MANIFEST:` line |
| whole-run production theorems at the shipped fuel | 13 shipped-fuel corollaries (`*_shipped`, Shipped.lean): exhibitA, fib, counter_loop, list_reverse, dispose_list, region_loop, malloc_list, fib_rec, even_odd, t1, t4, t5, t6 | `Shipped.lean` |
| emitted corpus | 10 C programs (`docs/corpus-e0/t1 … t10`); 4 certified end to end (t1, t4, t5, t6) | `scripts/corpus_skeleton.lean` table |
| package warnings | 33 (KOI C5 baseline) | gate log |
| semantics pin | cerberus-lean `89f7e688530c6910884518811d645e4e892e4507`, LemLib `f6542f8e…`, Lean 4.32.2 | `scripts/semantics-pin.env` |

### 1.2 The logic (criterion 1)

- **Judgments.** `wps M p Ls Θ Ψ e ρ` (Wps.lean:322), the partial judgment:
  a guarded fixpoint over iris-lean's WP; four clauses (value, jump at the
  label specification, call at the procedure table, step). `wpt M p Ls Θ k Ψ
  e ρ` (Wpt.lean:203), the total judgment by well-founded recursion on a
  step budget; a jump must decrease the budget, a call splits it. Both at the
  top mask (classical sequential separation logic; masks are the RefinedC
  arc's, KOI B11). **Refinement**: `wps_of_wpt` (Wpt.lean:5257) — total
  refines partial at the empty procedure table, with the label
  specification's variant index forgotten (`LabelSpecT.forget`); claim C18.
- **The rule families** (README "The logic"; the public/internal table is
  `API.lean`'s header): the five atomic specifications (`AtomicStep`,
  Rules.lean) lifted to the raw WP and both judgments by `wp_of_atomic`/
  `wps_of_atomic`/`wpt_of_atomic`; allocation from a budget (`wps_create`/
  `wpt_create`, `alloc`); frame incl. across back edges (`wps_frame`,
  `wps_frame_labels`, `wpt_frame_labels`); consequence (`wps_wand`,
  `wpt_mono_k` — budgets are upper bounds); sequencing at the three binder
  shapes and `Ewseq`; conditionals with the guard's verdict as a pure premise
  (`wps_if`) and value-scrutinee `case`; loops through the label context
  (`wps_save`/`wps_run`/`blockSpecs_intro`, the total twins with `1 + m ≤
  k`); procedures through the specification table (Hoare's rule for
  recursive procedures, claim C9; `fib_rec`, `even_odd`); operand
  evaluation, the `PtrEq` memop, the value protocol; the assertion laws;
  the environment laws (`SymFrame`, `envAdd_lookup`). The local memory rules
  are the classical shapes (claim C10): `{p ↦ -} store {p ↦ v}`, load at any
  fraction, budgeted `cons`, `free`.
- **Metatheory over the engine.** Mirror soundness and completeness (claim
  C6: wherever the mirror steps the shipped round is the singleton discharged
  match; at ambient fuel ≥ 4 every fragment round is a mirror step; three
  `OpenRound` arms characterised not closed, B7); the total collapse
  `wpt_sound` and the negative test `diverge_total_unprovable` (C5: the
  self-jump loop has NO total derivation — false, not merely unprovable); the
  driver lanes `wpt_driver_done_alloc` (ProdLoop.lean:444) and the partial
  closed form (C4); the global memory well-formedness invariant `MemWF`
  (C7); frame over heap AND label/procedure specifications (C8).
- **Negative results.** `OverflowExhibit`: the UB036 kill at the overflow
  round is a theorem; the whole-run kill is a MEASUREMENT (KOI B16; the
  kill-adequacy design note, §4.4 below).

### 1.3 The iris layer (criterion 2)

iris-lean pinned in `cerberus-heaplang/lakefile.toml` (`../deps/iris-lean`);
the engine's per-thread rounds as a `Language` instance (Lang.lean); the
coupling `stateInterp` over the engine's memory state with the ghost heap
`CohG`, the allocator cursor and the budget authority `budgetAuth`
(Heap.lean; `SpikeGS`); the atomic-step layer (Rules.lean) is mask-generic,
the judgments are top-mask. The Lane C design note
(`docs/2026-09-04_refinedc-layer-design-2.md`) §6 measures the module graph
and recommends the fragment-independent coupling be extracted as a second
Lake package the RefinedC-family layer imports (the demo becomes its
regression suite) — the concrete form of "can be extended later".

### 1.4 The connection to cerberus-lean (criterion 3)

Every production statement is over `CerbND.runND (_root_.drive fmapEmpty
false FILE args) ((initial_driver_state sup FILE fs).1)` — the shipped
driver, scheduler loop included, at every `[LemFuel]` above a
program-derived floor (KOI A1/A2 closed at the re-pin; `docs/FUEL.md`). The
pinned workspace `.cerberus-ws` is verified seam by seam
(`scripts/setup-cerberus-dep.sh --check`, 37 hand-written seams). Declared
boundaries: A5 (117 `panic!` arms in the hand-written semantics, provider
PROVISIONAL sense — no faithful outcome theorem yet), A3 (`dynamic_addrs`
upstream defect, outside the logic), B9 (rules proved directly against
`Step`, parametric interfaces deferred), B12 (two engine-round bridges,
documented design), B21 (allocator preconditions carried from the pin).

### 1.5 The programs (criterion 4)

| program | what it exercises | status | blocker |
|---|---|---|---|
| t1 | int variable, store, load, return | CERTIFIED (`t1_certified_production`, claim C13/E4 milestone) | — |
| t4_while | while loop, two-load race check, short-circuit `&&` | CERTIFIED (budget 915; C17) | — |
| t5_ifelse | conditional | CERTIFIED (budget 88; C15); partial too (`t5_wps`) | — |
| t6_switch | switch | CERTIFIED (budget 78; C16) | — |
| t2 | helper call in a `for` loop | pending | E6 — calls (`Eccall` is a scheduler-round path) |
| t3_ptrarg | pointer argument, `PtrValidForDeref` | pending | E6 + a memory-model op outside `Frag` |
| t7_struct | struct | pending | B4/D8 — tag definitions (every adequacy export carries `htd : M.tagDefs = fmapEmpty`) |
| t8_array | arrays, `PtrValidForDeref` | pending | the corpus table files it under E6 (arrays; `PtrValidForDeref`): new `Frag` shapes for the array idiom and the deref check |
| t9_fact | recursion under `unseq` | pending | E7 — the outcome-list closed form |
| t10_evenodd | mutual recursion | pending | E6 |

All ten are the elaborator's emitted `.annot.core` files
(`docs/corpus-e0/`), transcribed into Lean terms and checked against the
emitted text token for token by the corpus speedbump (D6; blind spots =
exactly the annotation kinds the printer never prints, KOI C20). The FILE
in every statement is `prodFileLib stdlibE3 [] tMain`: a hand-built file
with a transcribed THREE-function std.core fragment and `impl0 = ∅` (KOI
A7) — so the referent is the pipeline's program inside a file the pipeline
did not produce. Also in the package: nine synthetic (authored-Core)
exhibits from before arc E (exhibitA, fib, counter_loop, list_reverse,
dispose_list, region_loop, malloc_list, fib_rec, even_odd) and the E1–E3
synthetic emitted-shape exhibits — kept as shared-lemma hosts and
regression, not as evidence for criterion 4.

### 1.6 The instruments

Trust base: the capped build with the in-build exact-pin axiom audit
(`Audit.lean`), the banned-method grep (gate 1), the fuel-numeral grep
(gate 1b). Speedbumps ([USER 2026-09-02]: not adversarial gates): the
rule-use manifest with the claims-matrix name check, the corpus whole-text
check, the import-direction check, the client-boundary check; outside the
gate: `scripts/cite_check.sh` (decision pending whether it joins), the
signature census per slice (`scripts/signature_snapshot.lean`), the
workspace seam check. Every Lean build through `scripts/capped`.

### 1.7 The records

`docs/`: 40 files — `DECISIONS.md` (3 787 lines, append-only register with
[USER]/[AGENT] provenance), `KNOWN-OPEN-ITEMS.md` (A1–A7, B1–B21, C1–C21),
`AUDIT-BRIEF.md`, the charters, designs, requests and audits.
`cerberus-heaplang/docs/`: 130 records + 63 signature snapshots.
Reviewer-facing: `README.md`, `ARCHITECTURE.md` (§7 the acceptance ledger),
`docs/CLAIMS.md`, `docs/FUEL.md`, `docs/CAPABILITY_MANIFEST.md`,
`API.lean`'s header table. Every merge to main has a fresh-reviewer range
audit committed beside it.

## 2. The register of partial solutions on branches

Everything not on main that a slice below draws on. Heads measured at
`777ca0f`; "disposition" is what this plan does with it.

| branch @ head | what is there | salvage target | disposition |
|---|---|---|---|
| `parked/demo-expansion-2026-09-07` = `demo-repin` @ a41292d (65 beyond main) | the other agent's expansion, assessed as G1–G6 in `docs/2026-09-07_landability-demo-repin.md`: G1 re-pin (LANDED as L2); **G2 the actual t1 file** (3aac95d..5bfe992, 10 commits: the emitted file as a Lean data term produced by `scripts/inspect-emitted-file.sh`, a round-trip check, the `mkAuxLemma` kernel-certificate device — [USER 2026-09-04 Q3] option (b) mechanised); **G3 E6/E7 scheduler scaffolding** (14e7dc3..6c8e7e3, 13: kernel-sound over shipped engine functions; no acceptance program; changes `Step`/`wps`/`wpt`/`Frag`); **G4 `seq_rmw`** (567c578..19292c0, 4: engine arms mirrored, rules at cost 8, PROVISIONAL); G5 a failing WIP patch (rejected); G6 records | G2 → V1-1; G4 → V1-2; G3 → the REFERENCE for V2-1 | keep parked (record); never merge as is |
| `dialect-e5` @ cb46e4c | the other agent's E5 completion (t4/t5/t6), landed re-cut as L1 | — | keep as record |
| `codex/park-D1` @ 55b54b5 | stage-2 D1 investigation: the total judgment has no kill face (the finding behind the kill-adequacy design) | V1-5 | keep as record |
| `codex/park-D2` @ 09f9b90 | D2 investigation: `wps_c_add`'s int-range premises; the implementation path via `emittedInt_storable`/`intToBytes_*` | V1-4b | keep |
| `codex/park-D3` @ 450c87e | D3: the exact census of the 14 `hsup : 600 ≤` premises (T5 2, T6 3, T4 9) + `Shipped.lean`'s 3 | V1-4a | keep |
| `codex/park-D4` @ 2ad35c7 | D4: the `FreshAbove` placement/pin finding | V1-4a | keep |
| `design/kill-adequacy` @ e87a97c | the kill-adequacy options note (§4.4) | V1-5 | merge after the decisions |
| `refinedc/dev` @ b82e472 (an ANCESTOR of main) | the RefinedC layer's Lake package `RefinedCerberus/` + design notes as they stood on 2026-09-03; removed from main at `24c2410` ("main-share") | V2-1 onward | the package is retrievable at that commit; CLAUDE.md's "lives on `refinedc/dev`" means this commit, not a branch ahead of main — fix the wording at V1-6 |
| `lane-b-seed` @ f4f9a20 (3) | `cerberus-heaplang-ext/`, a namespace-renamed COPY of the demo at 1d2bb95 (the "Lane B derisking sibling"), with its range audit | none | superseded; keep per R7 |
| `repin-scout` @ 8847a2f, `repin-scout2` @ 07ceb44 | dry-run records of the re-pin | none | superseded by L2; keep per R7 |
| `charter-aims-amendment` @ 7838941 (4, 2026-08-30) | pre-demo charter revisions (aims check, boundary (b) retired, "the excavation") and a pin bump | none | historical; keep per R7 |
| `codex/demo-residuals-2` @ bf4554d | the original stage-2 branch; its content landed rebased as `land/codex-stage2` | none | superseded |
| worktree `demo-fuel-t1` (branch merged) — UNCOMMITTED, another agent's | a "demo completion master plan" and a "fuel, adequacy and t1 charter" dated 2026-09-07 00:05 | none: both plan work that L2/E4 landed | the other agent's to commit as record or discard; NOT adopted here |

Filed requests to the semantics side and their state: see the companion
register.

## 3. Gap analysis — what a PL-expert reviewer would name, per criterion

Severity: **D** would be called disqualifying for "good and complete";
**V** visible, would be named and must be answered or fixed; **N** a note.

### 3.1 Criterion 1 — the logic

| # | gap | sev | closes at |
|---|---|---|---|
| G1.1 | the numeral `600` as the symbol-supply floor in 17 statement sites (14 `hsup : 600 ≤ …` premises + 3 `600 ≤ sup →` in Shipped.lean) — a magic value in root-of-trust statements, against [USER 2026-09-03] no-magic-values; the rules expose the engine's symbol-generation scheme at the client interface (B19, B20) | V | V1-4a |
| G1.2 | no logical-variable index on `ProcSpec` (Lane C §1.4): Hoare-style procedure specifications need auxiliary variables; today a spec is fixed per call site's values | V | V2-2 (the RefinedC arc; ratify the Lane C recommendation) |
| G1.3 | negative results are measurements (B16): no must-reach-UB judgment | V | V1-5 |
| G1.4 | the empty tag-definitions premise on every adequacy export (B4): no structs | V for "complete", N for the covered fragment | V2-3 (D8) |
| G1.5 | mirror completeness has three open `OpenRound` arms (B7), fifteen NO-RULE variants classified by [AGENT] from the engine's admitted cases (B14) | N (honestly disclosed) | docs at V1-6; no code |
| G1.6 | symbolic-int storability proved at the literal 3 only (B15) | N | V1-4b |
| G1.7 | loops are label loops (`save`/`run`), not `while` — a reviewer used to structured rules will ask; the answer is that Core IS label-based and the rule is the classical one at the label context | N (answer in docs) | V1-6 |
| G1.8 | duplication and consumerless declarations (C17, C14) | N | V1-4c |

### 3.2 Criterion 2 — the iris layer

| # | gap | sev | closes at |
|---|---|---|---|
| G2.1 | the coupling is not yet a separable library; the RefinedC-family layer cannot import it without importing the demo | V (for "extensible") | V2-1 |
| G2.2 | top-mask judgments (B11) | N (ruled) | RefinedC arc |
| G2.3 | located Core / the annotation path (Lane C §4): the demo strips locations; a spec-carrying layer needs them | V for refined-cerberus, N for the demo | V2-1 design |

### 3.3 Criterion 3 — cerberus-lean

| # | gap | sev | closes at |
|---|---|---|---|
| G3.1 | 117 `panic!` arms (A5): fail-stop natively, default-denotation logically; no faithful outcome theorem; provider's typed-failure work PARKED after a census found 0 discardable sites | N for the covered programs (none reaches an arm — provider census), V for negative claims | provider; tracked in the companion register |
| G3.2 | two per-program `hQd`/`evalDepth` fuel premises stand in for a structural size lemma the provider has not proved (`subst_esize` note) | N | provider (no action requested) |
| G3.3 | the pin is a specific commit; any re-pin re-opens the mirror's soundness facts | N (process) | re-pin scouts, as done |

### 3.4 Criterion 4 — genuine outputs

| # | gap | sev | closes at |
|---|---|---|---|
| G4.1 | **the FILE is hand-built** (`prodFileLib stdlibE3 [] tMain`): a transcribed three-function std.core fragment with `impl0 = ∅`; the pipeline's file links the whole std.core and the gcc impl map, and an out-of-range `conv_loaded_int` WRAPS through the impl there (A7) | **D** | V1-1 |
| G4.2 | 4 of 10 corpus programs certified; the six pending are calls (3), recursion closed form (1), structs (1), arrays (1) | V for "complete" — ruled residual (R5); the v1 boundary must SAY "call-free" | V1-6 wording; V2 |
| G4.3 | transcription is by hand, checked token for token against the emitted text (D6); the check cannot see what the printer does not print (C20) | N (disclosed); becomes moot for the file once V1-1 lands its data-term route | V1-1 |
| G4.4 | `seq_rmw` (the emitted `i++` shape) is on the parked branch only | V (a covered feature's emitted shape) | V1-2 |

## 4. The plan

Two phases. **V1** = the definition of done for the CALL-FREE emitted-Core
demo (R5's "v1a" reading: "emitted Core, call-free programs"); **V2** = the
deferred set, each with its unlock condition. Owner: O = orchestrator
landing slice (fresh-reviewer range audit + merge ask each); X = a Codex
slice under a charter written to the discipline that produced the
refinement slice (statements verified derivable, fence-closure table,
hostile pre-launch review, launch only after the worktree is verified).
Sizes are measured velocity (the landing charter §4; the refinement slice's
two fixed theorems took the agent about an hour, and the charter, review,
audit and landing around it about half a day of orchestration).

Constraint while any Codex slice runs: main receives docs-only landings
(a Lean landing breaks the agent's frozen-surface census after its rebase).
So Lean landings and Codex slices are SERIALISED below.

### 4.1 V1 — the call-free emitted-Core demo

| item | what | owner | size | depends on | acceptance |
|---|---|---|---|---|---|
| **V1-1 the actual emitted file** (G4.1, A7; landing charter L3) | from G2 on the parked branch: the pipeline's whole file for t1 as a Lean data term produced by `scripts/inspect-emitted-file.sh`, the round-trip check as a gate speedbump (plant it), an independent `BEq` beside `toExpr`, the `mkAuxLemma` device named and documented in ARCHITECTURE §3; then the same for t4, t5, t6 (G2 did t1 only — V1-1b); `impl0` = the pinned gcc map, the std.core as linked; A7 rewritten | O | M (t1) + M (t4–t6) | — | each `t*_certified_production` states the pipeline's file; the check red on a perturbed term; range audit |
| **V1-2 `seq_rmw`** (G4.4; L4) | re-cut G4 without G3: engine arms mirrored, the mirror rule, the public rules, the `negFree → boundFree` premise change with its census; an emitted `i++` certified | O | M | V1-1 (file form) | a corpus or elaborator-transcribed `i++` program certified; PROVISIONAL dropped only if final |
| **V1-3 docs for V1-1/2** | ARCHITECTURE §3/§7, README, CLAIMS, KOI A7 | O | S | V1-2 | cite check clean |
| **V1-4 logic-quality Codex slices** (serialised, docs-only main while each runs): **4a symbol floor** (G1.1: the corrected D3+D4 — `FreshAbove`, a program-derived bound, the 17 sites, gate 1b extended to `600`, fences incl. `Audit.lean`, `EnvLaws.lean`, `Shipped.lean`, the gate scripts); **4b symbolic int** (G1.6: corrected D2 — the two int-range premises copied verbatim from `wps_c_add`); **4c hygiene** (G1.8: C17/C14 dedupe; C5 warnings) | X | 4a M, 4b S, 4c S | V1-2 landed (so their baselines are final) | per charter; each a range audit |
| **V1-5 kill adequacy** (G1.3, B16) | per the design note's decisions (§7 (a)–(e)): option A — the must-reach-UB judgment `wpu` with a pure-evaluation kill terminal, its rules for the overflow path, `wpu_driver_killed_alloc`, `overflow_certified_killed` replacing the measurement | X (after the design is fixed with the operator) | M | operator decisions; V1-4a (the floor appears in the statements) | the whole-run kill is a theorem over the pipeline at every fuel above the floor |
| **V1-6 the exit review and the tag** | (i) `cite_check.sh` into the gate (decision pending); (ii) the docs pass: G1.7's answer, the v1 boundary stated as "emitted Core, call-free", `refinedc/dev` wording, the synthetic exhibits' role; (iii) a FRESH full ARCHITECTURE review (new reviewer); (iv) **the PL-expert review**: a fresh reviewer briefed with §0's four criteria and this document, asked to say what a competent separation-logic referee would find missing or wrong — PASS = no D-severity finding; (v) the v1 tag | O | M | V1-1 … V1-5 | the review report committed; the tag |

Estimate (measured velocity): V1-1 1–2 days; V1-2 ½–1; V1-3 ½; V1-4 ≈ ½ day
each including charter, review, audit and landing (≈ 1½ days serialised);
V1-5 ≈ 1–2 (design first); V1-6 ≈ 1. About a week and a half to the tag.

### 4.2 V2 — deferred by ruling, with unlock conditions

| item | what | unlock | reference material |
|---|---|---|---|
| **V2-1 the coupling library** (G2.1; landing charter L6; Lane C §6) | extract the fragment-independent coupling (`Heap`, `MemWF`, the bundles, `EnvLaws`, `MachineCtx`/`Ctl`/`Config`, the ND collapse, the cold start) into a second Lake package; the demo imports it; every pin byte-identical | the v1 tag (a stable surface to extract from); Lane C question 3 ratified | Lane C §6 module graph; residuals charter D9 (statement shape) |
| **V2-2 `ProcSpec` logical variables** (G1.2) | the spec table indexed by a logical variable (Lane C §1.4 option (i)) | Lane C question 1 | Lane C §1.4 |
| **V2-3 structs / tag definitions** (G1.4; t7) | lift `htd : M.tagDefs = fmapEmpty` to the file's tag table; t7 certified | provider: arbitrary tag environments need `Acyclic`/`AcyclicPair` for the sufficiency theorems (risk map §3) | residuals charter D8 |
| **V2-4 calls — E6** (t2, t3, t10) | the C call protocol, `Eccall` as a scheduler round, the `driver2` induction | [USER R5]: after the scheduler is finished; the concurrency merge on cerberus-lean is a re-pin scout event | G3 as REFERENCE (sound scaffolding, not taken as is); dialect design §B6/§C E6; Lane C §3 |
| **V2-5 the outcome-list closed form — E7** (t9) | factorial's fork under `unseq` | with V2-4 | Lane C §3.2 |
| **V2-6 arrays and `PtrValidForDeref`** (t8, t3) | new `Frag` shapes for the emitted array idiom and the deref check | dialect-axis decision | corpus t8/t3 emitted text |
| **V2-7 general-table refinement** (C21) | `ProcSpecT.forget`; needs a table-equality or Θ-monotonicity lemma | a consumer appears (V2-1/V2-2) | refinement charter §6; its review F5 |
| **V2-8 masks** (B11) | mask-polymorphic judgments | the first invariant-backed type in the RefinedC layer | Lane C §2.4 (sized) |

## 5. What is explicitly NOT in "finished" for the demo

Function pointers, concurrency, external C calls (B8, ruled to the RefinedC
arc or out); the memory-model UB family beyond pure-evaluation kills;
provider-side items (the companion register); the nine Lane C questions
except where V1/V2 items above name them.

## 6. How this plan is kept true

One change at a time ([USER 2026-09-04]); every landing a fresh-reviewer
range audit and an explicit merge sign-off; gate tails verbatim in
`DECISIONS.md`; this document re-dated and re-issued at the v1 tag with the
V1 table replaced by the review's verdict.

## 7. Decisions for the operator

1. **The v1 boundary**: call-free emitted Core (V1 above) — or wait for E6
   (R5 offered both; this plan recommends the former, with the boundary
   stated on every surface).
2. **Kill adequacy** (`docs/2026-09-07_kill-adequacy-design.md` §6 (a)–(e)):
   option A now / B target; pure-evaluation kills first; existential
   location + a pinning lemma; name `wpu`; V1-5's place in the order.
3. **`cite_check.sh` into the gate** as a drift speedbump (open since the
   2026-09-05 snapshot).
4. **Lane C questions 1 and 3** (logical variables; the shared library) —
   the two that V2-1/V2-2 wait on.
5. **E5 §S2.5** (supplies normalised to `⟨0,0⟩` in the seeded profiles,
   B18): ratify or veto — open since 2026-09-05.
6. **The other agent's uncommitted plan** in the `demo-fuel-t1` worktree:
   commit as a record or discard (theirs to do).
7. **Branch pruning** (R7 "keep them for now"): the eleven fully-merged
   Codex/landing branches and the six parked worktrees on merged branches.

## 8. Provenance

[USER 2026-09-07]: the request ("a single 'master plan' doc … a register of
everything we have at hand, and pointers to the partial solutions that are
on branches … exactly what needs to be done to get to finished") and the
definition of done (§0, verbatim). [AGENT]: the inventory (measured), the
gap analysis, the plan and its sizes, the recommendations. Sources:
`docs/DECISIONS.md`, `docs/KNOWN-OPEN-ITEMS.md`, `docs/2026-09-07_landing-charter.md`,
`docs/2026-09-07_branch-landability-assessment.md`,
`docs/2026-09-07_landability-demo-repin.md`, `docs/2026-09-05_status-snapshot-handoff.md`,
`docs/2026-09-04_refinedc-layer-design-2.md`, `docs/2026-09-04_emitted-core-dialect-design.md`,
`docs/2026-09-07_kill-adequacy-design.md`, `cerberus-heaplang/{README,ARCHITECTURE}.md`,
`cerberus-heaplang/docs/{CLAIMS,FUEL,CAPABILITY_MANIFEST}.md`, `Audit.lean`,
`scripts/module_classes.tsv`, `git` (branch heads, ancestry).
