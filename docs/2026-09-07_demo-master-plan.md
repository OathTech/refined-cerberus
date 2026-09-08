# The demo logic — state of the union and master plan to "finished"

Status: DRAFT for the operator's ratification [AGENT orchestrator, 2026-09-07],
revision 2 after the hostile review `docs/2026-09-07_review-demo-master-plan.md`
(verdict CREDIBLE WITH FIXES, C+ → B once its seventeen fixes were applied;
every fix is applied in this revision and named where it changed a claim).
Written at main `777ca0f`. This document is the single place that says what
"finished" means for the Reynolds/O'Hearn demo (`cerberus-heaplang/`), what
exists, what is missing against that definition, where every partial solution
sits, and the ordered work to close the gap. It supersedes the ordering in the
2026-09-05 status snapshot §4 and the landing charter's L-list as the plan of
record; both remain as records. It is a plan, not a ruling: §7 lists the
decisions that are the operator's — including the one this plan PROPOSES to
change (§7.1). Companion: the cerberus-lean requests register,
`docs/2026-09-07_cerberus-lean-requests-register.md`.

Provenance of quotations: §0's definition of done and the request in §8 are
the operator's words in the working session of 2026-09-07, registered in
`docs/DECISIONS.md` in the commit that carries this revision (review fix 1);
every other quoted ruling is verbatim from `docs/DECISIONS.md` with its date.
Every count is measured at `777ca0f` and labelled DERIVED where it is a tally.

**2026-09-08 progress update — V1-1a, whole-file t1.** The authorized
`demo-whole-file-t1` slice re-cuts G2 onto main `7040406`; its contract is
`docs/2026-09-07_whole-file-t1-charter.md`. The feature implements generic
file capture/reconstruction, comparator-check correctness and startup with
the actual runtime extern map, consumed by
`CorpusA7.T1.certified_production`. The theorem runs the retained complete
file at captured supply 36 and every execution fuel at least 50, under
three explicit comparator checks; its capture-transfer theorem keeps
data/supply equality as premises. The old synthetic t1 theorem and shipped
corollary remain wrapper regressions. `EmittedStdCore` reuses this captured
library's declarations under lookup/data premises; the generic capture,
map and driver machinery does not depend on t1.

R-4's referent is settled for this slice: the pinned Lean frontend consumes
OCaml Cabs, links std.core and the gcc implementation, and converts the
whole one-TU/no-libc file. Its frontend/quoter/structural comparison is an
executable boundary, not a kernel frontend theorem or equality with OCaml's
printed Core. The implementation record
`docs/2026-09-08_whole-file-t1-implementation.md` owns verification and
review status. V1-1b (t4/t5/t6), option (a), and the scheduler/call work
remain open. The baseline inventory and counts below remain measurements
at `777ca0f`; this update does not assert the whole V1-1 row complete or
authorize a merge.

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
code. Authored-core is just a confection"; [USER 2026-09-02] one change at a
time, Reynolds/O'Hearn is the stable spec; the feature set is CLOSED on the
logic axis and OPEN on the dialect axis for covered features (arc E).
On calls and the scheduler lift, [USER 2026-09-07] R5, verbatim: "R5, E6 and
E7 - okay so this stays as residual until we've finished the scheduler
completely? Yes, this is fine to leave until later." The RECORDED
DISPOSITION of that ruling (DECISIONS, the same entry) is: "the v1 tag waits
for E6 proper (L5)". The alternative "v1a after L4 as 'emitted Core,
call-free programs'" was the orchestrator's bracketed recommendation in the
landing charter §1 R5, not a ruling. **This plan recommends changing the
recorded disposition — §7.1 — and until that decision the definition of done
includes E6.**

How each criterion is made checkable in this plan:

| criterion | checkable form | status at `777ca0f` |
|---|---|---|
| (1) recognisably Reynolds/O'Hearn | the classical rule set exists, is proved sound against the engine, and is USED by clients: local memory axioms, frame, consequence, sequencing, conditionals, loops, procedures; partial AND total judgments with the refinement between them | MET for statements and loops; procedures MET at value-indexed specifications only (no logical variables, G1.2); statement-level artefacts a reviewer will name (G1.1, G1.9) |
| (2) a real, faithful, extensible iris layer | iris-lean's WP machinery instantiated on a `Language` instance of the engine's rounds; the coupling (`stateInterp`) is a genuine Iris ghost-state coupling; the layer can be extracted as a library the RefinedC-family layer imports | MET as a layer (the judgments are the same construction as iris-lean's `wp`, collapsing into it); "extensible" UNTESTED until the extraction (V2-1) |
| (3) built on cerberus-lean | every export's referent is `CerbND.runND (_root_.drive …) (initial_driver_state …)` of the pinned semantics, at every fuel above a program-derived floor; the mirror and the collapse are proof devices only | MET (measured: none of the 13 production statements mentions `Step`, `Frag`, `CerberusRound` or a `Driver*` device); boundaries recorded (A5 panic arms, A3 upstream defect, B9, B12) |
| (4) genuine pipeline outputs | the certified programs are the elaborator's emitted Core for real C files, and the FILE in the statement is the pipeline's whole file, not a hand-built one | HALF MET: the programs are emitted and text-checked; the file is hand-built with a transcribed three-function std.core fragment and `impl0 = ∅` (A7) — the largest gap. V1-1 closes it in the [USER 2026-09-04 Q3] OPTION (b) sense (a machine-quoted data term of the whole file plus an executable round-trip check); option (a), the elaborator in the statement, remains the named target (§3.4) |
| reviewer standard | a fresh PL-expert review against (1)–(4) finds no gap it would call disqualifying | NOT YET RUN on the finished artefact; defined as the exit gate (V1-6); the review of THIS PLAN (C+, fixes applied) is its first instalment |

## 1. What exists — the inventory at `777ca0f`

### 1.1 The package, in numbers (DERIVED)

| quantity | value | source |
|---|---|---|
| Lean in `cerberus-heaplang/CerberusHeapLang/` | 84 343 lines in 60 modules (79 560 at the top level + 4 783 under `Examples/`); largest: Soundness 10 539, Round 7 455, Step 6 398, Wps 5 556, Wpt 5 318, Heap 4 859, DriverCollapse 2 970, EvalClass 2 744, Adequacy 2 358, ListRevExhibit 1 985, Rules 1 826 | `wc -l` |
| modules classified | 60 (19 `core`, 26 consumer = 24 `positive-client` + 2 `declared-smoke`, 2 `negative-test`, 2 `semantic-test`, 3 `production-wrapper`, 3 `production-core`, 4 `example-support`, 1 `audit`) | `cerberus-heaplang/scripts/module_classes.tsv`; manifest `MODULES:` line |
| pinned exports | 906 trio-exact (`propext`, `Classical.choice`, `Quot.sound` exactly) + 6 axiom-free; no duplicate pin | `Audit.lean` `trioExports`/`axiomFreeExports`; gate line `export pins: 906 trio-exact, 6 axiom-free-exact` |
| claims | 18 rows C1–C18, 195 declaration names checked | `cerberus-heaplang/docs/CLAIMS.md`; manifest `CLAIMS:` line |
| construct coverage | 35 `Frag` constructors, 78 engine-success variants: 47 RULE, 24 NO-RULE, 7 OUT-OF-SCOPE, 0 undemonstrated — i.e. 31 of 78 classified variants (40 %) have no rule, by design or by boundary | `cerberus-heaplang/docs/CAPABILITY_MANIFEST.md` `MANIFEST:` line |
| whole-run production theorems at the shipped fuel | 13 shipped-fuel corollaries (`*_shipped`, Shipped.lean): exhibitA, fib, counter_loop, list_reverse, dispose_list, region_loop, malloc_list, fib_rec, even_odd, t1, t4, t5, t6 | `Shipped.lean` |
| emitted corpus | 10 C programs (`docs/corpus-e0/t1 … t10`); 4 certified end to end (t1, t4, t5, t6 by `t{1,4,5,6}_certified_production`) | `Examples/CorpusE0.lean` `corpusTable`/`pendingCorpus`, consumed by `cerberus-heaplang/scripts/corpus_skeleton.lean` |
| package warnings | 33 (KOI C5 baseline; the landing gate of `ed82837`) | gate log |
| semantics pin | cerberus-lean `89f7e688530c6910884518811d645e4e892e4507`, LemLib `f6542f8e…`, Lean 4.32.2; iris-lean `34390a01…` | `scripts/semantics-pin.env`; `cerberus-heaplang/lakefile.toml` |
| unpushed state | local `main` is 107 commits ahead of `origin/main` (`04059dc`); pushes are operator-gated | `git rev-list --count` |

### 1.2 The logic (criterion 1)

- **Judgments.** `wps M p Ls Θ Ψ e ρ` (Wps.lean:322), the partial judgment:
  the guarded fixpoint of a pre-functional with four clauses (value, jump at
  the label specification, call at the procedure table, step). `wpt M p Ls Θ
  k Ψ e ρ` (Wpt.lean:203), the total judgment by well-founded recursion on a
  step budget; a jump must decrease the budget, a call splits it. Both are
  THE SAME CONSTRUCTION AS iris-lean's `wp` (they re-state its step clause
  over `stateInterp`, reducibility and later credits) and COLLAPSE INTO it
  (`wps_sound` Wps.lean:4752, `wpt_sound` Wpt.lean:4520 target iris-lean's
  `WP … @ NotStuck; ⊤`); adequacy through `wp_strong_adequacy_gen`
  (Adequacy.lean). Both at the top mask (classical sequential separation
  logic; masks are the RefinedC arc's, KOI B11). **Refinement**:
  `wps_of_wpt` (Wpt.lean:5257) — total refines partial at the empty procedure
  table, with the label specification's variant index forgotten
  (`LabelSpecT.forget`); claim C18.
- **The rule families** (README "The logic"; the public/internal table is
  `API.lean`'s header): the five atomic specifications (`AtomicStep`,
  Rules.lean:220) lifted to the raw WP and both judgments by `wp_of_atomic`/
  `wps_of_atomic`/`wpt_of_atomic`; allocation from a budget (`wps_create`/
  `wpt_create`, `alloc`); frame on the judgment (`wps_frame`) and across back
  edges/calls (`wps_frame_labels`, `wpt_frame_labels`); consequence
  (`wps_wand`, `wpt_mono_k` — budgets are upper bounds); sequencing at the
  three binder shapes and `Ewseq`; conditionals with the guard's verdict as a
  pure premise (`wps_if`) and value-scrutinee `case`; loops through the label
  context (`wps_save`/`wps_run`/`blockSpecs_intro`, the total twins with the
  mandatory decrease `1 + m ≤ k`); procedures through the specification table
  (Hoare's rule for mutually recursive procedures, `procSpecs_intro`, claim
  C9; `fib_rec`, `even_odd`); operand evaluation, the `PtrEq` memop, the value
  protocol; the assertion laws; the environment laws (`SymFrame`,
  `envAdd_lookup`). The local memory rules are the classical shapes (claim
  C10): `{p ↦ -} store {p ↦ v}`, load at any fraction, budgeted `cons`, `free`.
  Conjunction, disjunction and existentials at the judgment come from Iris's
  BI in the postcondition (`∃`, `∨` inside `Ψ`), not from rules of their own —
  a one-line statement the rule table should carry (V1-6).
- **Metatheory over the engine.** Mirror soundness and completeness (claim
  C6: wherever the mirror steps the shipped round is the singleton discharged
  match; at ambient fuel ≥ 4 every fragment round is a mirror step; three
  `OpenRound` arms characterised not closed, KOI B7 — CLAIMS C6 still says
  "two", a docs item); the total collapse and the negative test
  `diverge_total_unprovable` (C5: the self-jump loop has NO total derivation —
  false, not merely unprovable); the driver lane `wpt_driver_done_alloc`
  (ProdLoop.lean:444) and the partial closed form (C4); the global memory
  well-formedness invariant `MemWF` (Heap.lean:1640; C7); frame over heap AND
  label/procedure specifications (C8). **Two adequacy routes**: the seeded
  exhibits go through the collapse into Iris adequacy; the production lane
  runs its own induction (`wpt_driver_aux`) and consumes neither `wps_sound`
  nor `wpt_sound` (ARCHITECTURE §2.1 says so). Why the load-bearing lane is
  not a corollary of collapse + Iris adequacy is a question for the fresh
  ARCHITECTURE review (V1-6); the honest answer today is the singleton-
  equation shape (B5).
- **Negative results.** `OverflowExhibit`: the UB036 kill at the overflow
  round is a theorem; the whole-run kill is a MEASUREMENT (KOI B16; the
  kill-adequacy design note on branch `design/kill-adequacy` @ e87a97c,
  §7.2 below).

### 1.3 The iris layer (criterion 2)

iris-lean `34390a01` (2026-08-20) pinned in `cerberus-heaplang/lakefile.toml`
(`../deps/iris-lean`); the engine's per-thread rounds as `Language CoreRt Mem
Empty CoreRVal` (Lang.lean:58) with `IrisGS_gen` (Lang.lean:112); the
coupling `stateInterp` over the engine's memory state with the ghost heap
`CohG` (Heap.lean:2663), the allocator cursor and the budget authority
`budgetAuth` (Heap.lean:2493); `SpikeGS` (Heap.lean:2437); later credits and
fancy updates as in Iris; the atomic-step layer (Rules.lean) is
mask-generic, the judgments are top-mask. The Lane C design note
(`docs/2026-09-04_refinedc-layer-design-2.md`) §6 measures the module graph
and recommends the fragment-independent coupling be extracted as a second
Lake package (estimate 2–4 worker-days) the RefinedC-family layer imports,
the demo becoming its regression suite — the concrete form of "can be
extended later", untested until done.

### 1.4 The connection to cerberus-lean (criterion 3)

Every production statement is over `CerbND.runND (_root_.drive fmapEmpty
false FILE args) ((initial_driver_state sup FILE fs).1)` — the shipped
driver, scheduler loop included, ONE thread, at every `[LemFuel]` above a
program-derived floor (KOI A1/A2 closed at the re-pin; `docs/FUEL.md`), with
`htd : M.tagDefs = fmapEmpty` (37 sites) and `hex : M.extern = fmapEmpty` (38
sites) on the adequacy chain. Measured: none of the 13 production statements
mentions `Step`, `Frag`, `CerberusRound` or a `Driver*` device — the mirror
and the collapse are proof devices only. After V1-1 the referent's FILE
becomes a data term plus an executable check (§3.4), not `drive`'s input as
the pipeline computes it. The pinned workspace `.cerberus-ws` is verified
seam by seam (`scripts/setup-cerberus-dep.sh --check`, 37 hand-written
seams; it fails loudly on drift — measured at this landing, §1.6). Declared
boundaries: A5 (119 `panic!` arms in ten hand-written seams — the L2 audit's
"117 in nine" is corrected at this landing by two independent counts, KOI A5
erratum; provider PROVISIONAL sense: no faithful outcome theorem; the
covered programs avoid every arm by the RULES' premises, ARCHITECTURE §3 —
not by a census), A3 (`dynamic_addrs` upstream defect, outside the logic), B9
(rules proved directly against `Step`, parametric interfaces deferred), B12
(two engine-round bridges, documented design), B21 (allocator preconditions
carried from the pin).

### 1.5 The programs (criterion 4)

| program | what it exercises | status | blocker |
|---|---|---|---|
| t1 | int variable, store, load, return | CERTIFIED (`t1_certified_production`, `hfuel : 50 ≤`; C13/E4 milestone) | — |
| t4_while | while loop, two-load race check, short-circuit `&&` | CERTIFIED (budget 915, `hfuel : 917 ≤`; C17) | — |
| t5_ifelse | conditional | CERTIFIED (budget 88, `hfuel : 90 ≤`; C15); partial too (`t5_wps`) | — |
| t6_switch | switch | CERTIFIED (budget 78, `hfuel : 80 ≤`; C16) | — |
| t2 | helper call in a `for` loop | pending | E6 — calls (`Eccall` is a scheduler-round path) |
| t3_ptrarg | pointer argument, `PtrValidForDeref` | pending | E6 + a memory-model op outside `Frag` |
| t7_struct | struct | pending | B4/D8 — tag definitions (every adequacy export carries `htd : M.tagDefs = fmapEmpty`) |
| t8_array | arrays, `PtrValidForDeref` | pending | the corpus table files it under E6 (arrays; `PtrValidForDeref`); the dialect design §C.8 says arrays are "not an E slice" — a dialect-axis decision (V2-6) |
| t9_fact | recursion under `unseq` | pending | E7 — the outcome-list closed form |
| t10_evenodd | mutual recursion | pending | E6 |

All ten are the OCaml Cerberus elaborator's emitted `.annot.core` files
(`docs/corpus-e0/`), transcribed into Lean terms and checked against the
emitted text token for token by the corpus speedbump (D6; blind spots =
exactly the annotation kinds the printer never prints, KOI C20). The FILE
in every statement is `prodFileLib stdlibE3 [] tMain`: a hand-built file
with a transcribed THREE-function std.core fragment and `impl0 = ∅` (KOI
A7) — so the referent is the pipeline's program inside a file the pipeline
did not produce. Also in the package: sixteen authored (synthetic-Core)
positive clients from before arc E — nine of them with shipped-fuel
corollaries — and the E1–E3 synthetic emitted-shape exhibits; kept as the
regression suite and as shared-lemma hosts ([USER] E0 Q7), not as evidence
for criterion 4.

### 1.6 The instruments and the environment

Trust base: the capped build with the in-build exact-pin axiom audit
(`Audit.lean`), the banned-method grep (gate 1), the fuel-numeral grep
(gate 1b). Speedbumps ([USER 2026-09-02]: not adversarial gates): the
rule-use manifest with the claims-matrix name check, the corpus whole-text
check, the import-direction check, the client-boundary check; outside the
gate: `cerberus-heaplang/scripts/cite_check.sh` (decision pending whether it
joins), the signature census per slice
(`cerberus-heaplang/scripts/signature_snapshot.lean`), the workspace seam
check. Every Lean build through `scripts/capped`. After V1-1 the trust base
gains two components that are not in it today: the quoter
`scripts/derive_file_to_expr.lean` and the loader `scripts/emitted_frontend.lean`
(G2), whose output is checked by the round-trip and an independent `BEq`
— checks, not proofs; they need a named place in ARCHITECTURE §3 and a
mover. Environment finding at this landing: the PRIMARY checkout's
`.cerberus-ws` had drifted to the pre-L2 pin (`f95ef8d9c`) with a `.lake`
from 2026-09-02 while KOI §E called it primed; `--check` reported the drift
loudly (exit 1); re-primed from the gated `codex-refinement` worktree and
re-verified (37 seams, FULL gate green, 0 rebuilt). Never prime from the
primary; verify by `--check` and a gate (Codex lesson 1).

### 1.7 The records

`docs/`: 40 files at `777ca0f` — `DECISIONS.md` (3 787 lines, append-only
register with [USER]/[AGENT] provenance), `KNOWN-OPEN-ITEMS.md` (A1–A7,
B1–B21, C1–C21), `AUDIT-BRIEF.md`, the charters, designs, requests and
audits. `cerberus-heaplang/docs/`: 130 records + 63 `.txt` evidence files (54
signature snapshots, 9 axiom/census dumps). Reviewer-facing: `README.md`,
`ARCHITECTURE.md` (§7 the acceptance ledger), `docs/CLAIMS.md`,
`docs/FUEL.md`, `docs/CAPABILITY_MANIFEST.md`, `API.lean`'s header table.
Every merge to main has a fresh-reviewer range audit committed beside it.

## 2. The register of partial solutions on branches

Everything not on main that a slice below draws on. Heads measured at
`777ca0f`; "disposition" is what this plan does with it. Completeness: the
review's sweep found every unmerged branch present here.

| branch @ head | what is there | salvage target | disposition |
|---|---|---|---|
| `parked/demo-expansion-2026-09-07` = `demo-repin` @ a41292d (65 beyond main) | the other agent's expansion, assessed as G1–G6 in `docs/2026-09-07_landability-demo-repin.md`: G1 re-pin (17 commits; LANDED as L2); **G2 the actual t1 file** (3aac95d..5bfe992, 10 commits: the pinned Lean frontend's in-memory `file` for t1 quoted into a 42 841-line data term `Examples/EmittedT1Data.lean` by `scripts/derive_file_to_expr.lean`, loaded by `scripts/emitted_frontend.lean`, with an executable round-trip check; the statement drives `restoredFile cmp` under quantified comparators and three finite `Bool` checks (the comparator CLOSURES are functions and cannot be quoted, which is why `EmittedFile.Data` omits them and the statement quantifies `cmp`), at `frontendSupply` — a CAPTURED literal (`def frontendSupply : Nat := 36`, checked by the round-trip, the same shape G1.1 criticises, not a derivation) — [USER 2026-09-04 Q3] option (b) mechanised); **G3 E6/E7 scheduler scaffolding** (14e7dc3..6c8e7e3, 12 commits: kernel-sound over shipped engine functions; no acceptance program; changes `Step`/`wps`/`wpt`/`Soundness`/`DriverCollapse`); **G4 `seq_rmw`** (567c578..19292c0, 4: engine arms mirrored, rules at cost 8, PROVISIONAL); G5 a failing WIP patch (rejected); G6 records | G2 → V1-1; G4 → V1-2; G3 → the REFERENCE for V2-4 | keep parked (record); never merge as is |
| `dialect-e5` @ cb46e4c (21) | the other agent's E5 completion (t4/t5/t6), landed re-cut as L1 | — | keep as record |
| `codex/park-D1` @ 55b54b5 | stage-2 D1 investigation: the total judgment has no kill face (the finding behind the kill-adequacy design) | V1-5 | keep as record |
| `codex/park-D2` @ 09f9b90 | D2 investigation: `wps_c_add`'s int-range premises; the implementation path via `emittedInt_storable`/`intToBytes_*` | V1-4b | keep |
| `codex/park-D3` @ 450c87e | D3: the census of the `hsup : 600 ≤` premises at `1e1f584` (14 = T5 2, T6 3, T4 9) + `Shipped.lean`'s 3; at `777ca0f` it is 15 + 3 (T4 has 10: `t4_wps_of_wpt` carries the premise) | V1-4a | keep |
| `codex/park-D4` @ 2ad35c7 | D4: the `FreshAbove` placement/pin finding | V1-4a | keep |
| `design/kill-adequacy` @ e87a97c | the kill-adequacy options note (five decisions, its §6) | V1-5 | merge after the decisions |
| `refinedc/dev` @ b82e472 (an ANCESTOR of main) | the RefinedC layer's stub Lake package `RefinedCerberus/` (3 files) + design notes as they stood on 2026-09-03; removed from main at `24c2410` ("main-share") | V2-1 onward | the package is retrievable at that commit; CLAUDE.md's "lives on `refinedc/dev`" means this commit, not a branch ahead of main — fix the wording at V1-6 |
| `lane-b-seed` @ f4f9a20 (3) | `cerberus-heaplang-ext/`, a namespace-renamed COPY of the demo at 1d2bb95 (the "Lane B derisking sibling"), with its range audit | none | superseded; keep per R7 |
| `repin-scout` @ 8847a2f, `repin-scout2` @ 07ceb44 | dry-run records of the re-pin | none | superseded by L2; keep per R7 |
| `charter-aims-amendment` @ 7838941 (4, all 2026-08-30) | pre-demo charter revisions (aims check + pin bump, boundary (b) retired, "the excavation", rev 3) | none | historical; keep per R7 |
| `codex/demo-residuals-2` @ bf4554d (8) | the original stage-2 branch; every patch present in main (`git cherry`: all `-`), landed rebased as `land/codex-stage2` | none | superseded |
| `docs/master-plan` | this document and the companion | — | the merge candidate |
| worktree `demo-fuel-t1` (branch merged) — UNCOMMITTED, another agent's | `docs/2026-09-05_demo-completion-charter.md` (titled "Demo completion master plan", mtime 2026-09-07 00:05), `docs/2026-09-07_fuel-adequacy-t1-charter.md` (00:07), AND uncommitted edits `README.md | 8 +`, `docs/DECISIONS.md | 55 +` — a pending edit to the append-only register | none: they plan work that L2/E4 landed | the other agent's to commit as record or discard; NOT adopted here; §7.6 |

Filed requests to the semantics side and their state: the companion
register §3.

## 3. Gap analysis — what a PL-expert reviewer would name, per criterion

Severity: **D** would be called disqualifying for "good and complete";
**V** visible, would be named and must be answered or fixed; **N** a note.

### 3.1 Criterion 1 — the logic

| # | gap | sev | closes at |
|---|---|---|---|
| G1.1 | the numeral `600` as the symbol-supply floor in 18 statement sites (15 `hsup : 600 ≤ …` premises — T4 10, T5 2, T6 3 — + 3 `600 ≤ sup →` in Shipped.lean) — a magic value in root-of-trust statements, against [USER 2026-09-03] no-magic-values; the rules expose the engine's symbol-generation scheme at the client interface (B19, B20). G2's `frontendSupply` is a captured literal (`36`) checked by a round-trip, not a derivation — V1-4a must cover it too | V | V1-4a |
| G1.2 | **no logical-variable index on `ProcSpec`** (Wps.lean:130: pre and post share only the argument values; `reverse(p)` with `list p xs`/`list ret (rev xs)` is not statable — Lane C §1.4). For a Reynolds/O'Hearn logic WITH procedures this is the classical Hoare-logic ingredient, not a "fancy feature" | V (the review would grade it toward D for "complete") | V2-2 as recorded; this plan RECOMMENDS pulling Lane C option (i) into V1 (§7.4) |
| G1.3 | negative results are measurements (B16): no must-reach-UB judgment | V | V1-5 |
| G1.4 | the empty tag-definitions premise on every adequacy export (B4; 37 sites) and the empty extern map (38 sites): no structs, no externs | V for "complete", N for the covered fragment | V2-3 (D8); the extern premise is answered by G2's `runtimeExtern` route at V1-1 |
| G1.5 | mirror completeness has three open `OpenRound` arms (B7); 24 NO-RULE + 7 OUT-OF-SCOPE variants (31 of 78) are stated absences; the NO-RULE classification is [AGENT]'s reading of the engine (B14) | N (honestly disclosed; the number must be stated) | docs at V1-6; no code |
| G1.6 | symbolic-int storability proved at the literal 3 only (B15) | N | V1-4b |
| G1.7 | loops are label loops (`save`/`run`), not `while` — Core IS label-based; the reviewer-facing answer is a DERIVED `while` rule stated once over the emitted `while` idiom (t4's shape), not prose alone | N → V after the derived rule | V1-4c (the rule) + V1-6 (the prose) |
| G1.8 | duplication and consumerless declarations (C17, C14) | N | V1-4c |
| G1.9 | **numeral fuel floors** in every root-of-trust statement (`hfuel : 50/917/90/80 ≤ LemFuel.fuel`): principled (FUEL.md §3: the certified round count plus two) but hand-derived numerals in statements — the same class as `600` under the no-magic-values ruling (why is `917` not a named cost by `rfl`?) | V | V1-4a's scope, or an explicit exemption recorded in FUEL.md (§7.8) |

### 3.2 Criterion 2 — the iris layer

| # | gap | sev | closes at |
|---|---|---|---|
| G2.1 | the coupling is not yet a separable library; the RefinedC-family layer cannot import it without importing the demo — "extensible" is untested | V (for "extensible") | V2-1 |
| G2.2 | top-mask judgments (B11) | N (ruled) | RefinedC arc |
| G2.3 | located Core / the annotation path (Lane C §4): the demo strips locations; a spec-carrying layer needs them | V for refined-cerberus, N for the demo | V2-1 design |
| G2.4 | two adequacy routes to the engine, never connected (§1.2) | V (a design question, not a soundness gap) | V1-6 names it for the fresh reviewer |

### 3.3 Criterion 3 — cerberus-lean

| # | gap | sev | closes at |
|---|---|---|---|
| G3.1 | 119 `panic!` arms (A5): fail-stop natively, default-denotation logically; no faithful outcome theorem; the provider's typed-failure design PARKED after a census of the 231 pure `failwith` sites found 0 discardable (that census is about `failwith`, not `panic!`) | N for the covered programs (the rules' premises keep them off every arm), V for negative claims | provider; companion R-2 |
| G3.2 | two per-program `hQd`/`evalDepth` premises (ProdLoop.lean:380, :451) stand in for a structural size lemma the provider has not proved (`subst_esize` note) | N | provider (no action requested) |
| G3.3 | the pin is a specific commit; a re-pin re-opens the mirror's soundness facts; the concurrency branch changes the driver's `.lem` sources (companion §1) | N (process) | re-pin scouts, as done |

### 3.4 Criterion 4 — genuine outputs

| # | gap | sev | closes at |
|---|---|---|---|
| G4.1 | **the FILE is hand-built** (`prodFileLib stdlibE3 [] tMain`): a transcribed three-function std.core fragment with `impl0 = ∅`; the pipeline's file links the whole std.core and the gcc impl map, and an out-of-range `conv_loaded_int` WRAPS through the impl there (A7) | **D** | V1-1, in the option (b) sense: the statement then drives a machine-quoted DATA TERM of the pipeline's whole file (`EmittedFile.restore cmp data`, comparators quantified under three finite `Bool` checks), equal to the pinned Lean frontend's file by an EXECUTABLE round-trip; option (a) — the elaborator in the statement — remains the named target and is NOT delivered by V1-1 |
| G4.2 | 4 of 10 corpus programs certified; the six pending are calls (3), the recursion closed form (1), structs (1), arrays (1); no certified program contains a call | V for "complete"; under the recorded disposition E6 is IN the definition of done (§0) | V2-4/V2-5, or §7.1's proposed boundary |
| G4.3 | transcription is by hand, checked token for token against the OCaml printer's text (D6); the check cannot see what the printer does not print (C20). "The pipeline" is TWO things in this repository: the OCaml Cerberus that emitted `docs/corpus-e0/*.annot.core`, and the pinned Lean frontend whose in-memory `file` G2 quotes — a referee asks which Cerberus the theorem is about | N today; V at V1-1 unless answered | V1-1 must state the referent; companion R-4 asks the provider whether the two are promised equal |
| G4.4 | `seq_rmw` (the emitted `i++` shape) is on the parked branch only | V (a covered feature's emitted shape) | V1-2 |
| G4.5 | globals and initialisers: every current and G2 statement has `globs = []`; `driver_globals` reads globals through `to_pure`, a pending fuel row on the provider side | V for "genuine outputs" of real C files | V2 item V2-9; companion §4 |

## 4. The plan

Two phases. **Phase I (proposed tag "v1a")** = the call-free emitted-Core
demo; **Phase II** = the deferred set with unlock conditions, INCLUDING E6,
which the recorded disposition places before the v1 tag. If the operator
keeps the recorded disposition, "finished" = Phase I + V2-4/V2-5 and the
exit review runs after them; if the operator adopts §7.1, Phase I ends at
"v1a" and Phase II's E6 is the road to "v1". Owner: O = orchestrator landing
slice (fresh-reviewer range audit + merge ask each); X = a Codex slice under
a charter written to the discipline that produced the refinement slice
(statements verified derivable, fence-closure table, hostile pre-launch
review, launch only after the worktree is verified). Sizes are estimates
against measured velocity (the landing charter §4; five landings on
2026-09-07 alone — L1, L2, D5, stage 2, the refinement; the refinement slice's two theorems fell within a
seven-minute snapshot span, under an hour from activation to record).

Constraint while any Codex slice runs: main receives docs-only landings (a
Lean landing breaks the agent's frozen-surface census after its rebase —
refinement charter rules 2 and 8). So Lean landings and Codex slices are
SERIALISED below; each Codex slice costs the operator a charter review, a
launch, a range audit and a merge sign-off — about ten sign-offs across
Phase I.

### 4.1 Phase I — the call-free emitted-Core demo (PROPOSED boundary "v1a"; recorded disposition: v1 waits for E6)

| item | what | owner | size | depends on | acceptance |
|---|---|---|---|---|---|
| **V1-1 the actual emitted file** (G4.1, A7; landing charter L3) | from G2 on the parked branch: the pipeline's whole file for t1 as a machine-quoted data term (`EmittedT1Data.lean`) produced by `scripts/derive_file_to_expr.lean`/`emitted_frontend.lean`, the round-trip check as a gate speedbump (plant it), an independent `BEq` beside `toExpr`, the `mkAuxLemma` kernel-certificate device named in ARCHITECTURE §3 with the quoter/loader as trusted components with a mover; `impl0` = the pinned gcc map, the std.core as linked (110 stdlib + 6 impl entries), the extern map as `runtimeExtern`; the retained wrapper `CorpusT1Exhibit` decided (keep beside the actual-file form or retire — E0 Q7); the referent stated (G4.3); then the same for t4, t5, t6 (V1-1b — G2 did t1 only); A7 rewritten | O | M (t1) + M (t4–t6) | companion R-4 answered | each `t*_certified_production` drives the data term of the pipeline's file; the check red on a perturbed term; range audit |
| **V1-2 `seq_rmw`** (G4.4; L4) | re-cut G4 without G3: engine arms mirrored, the mirror rule, the public rules, the `negFree → boundFree` premise change with its census; an emitted `i++` certified | O | M | V1-1 (file form) | a corpus or elaborator-transcribed `i++` program certified; PROVISIONAL dropped only if final |
| **V1-3 docs for V1-1/2** | ARCHITECTURE §3/§7, README, CLAIMS (C6's "two residuals" → three), KOI A7 | O | S | V1-2 | cite check clean |
| **V1-4 logic-quality Codex slices** (serialised, docs-only main while each runs): **4a symbol floor** (G1.1: the corrected D3+D4 — `FreshAbove`, a program-derived bound, the 18 sites, gate 1b extended to `600`; fences incl. `Audit.lean`, `EnvLaws.lean`, `Shipped.lean`, the gate scripts; G1.9's fuel floors in scope or exempted per §7.8); **4b symbolic int** (G1.6: corrected D2 — the two int-range premises copied verbatim from `wps_c_add`); **4c hygiene** (G1.8: C17/C14 dedupe; C5 warnings; G1.7's derived `while` rule over t4's idiom) | X | 4a M, 4b S, 4c S–M | V1-2 landed (so their baselines are final) | per charter; each a range audit |
| **V1-5 kill adequacy** (G1.3, B16) | per the design note's decisions (§7.2; note §6 (a)–(e)): option A — the must-reach-UB judgment `wpu` with a pure-evaluation kill terminal, its OWN structural rules for every construct on the overflow path (the E3 integer faces, `bound`, `unseq`, the binders), `DriverKilledAt`, `wpu_driver_killed_alloc`, `wpu_certified_killed` replacing the measurement | X (after the design is fixed with the operator) | M–L, own stop-and-report | operator decisions; V1-4a (the floor appears in the statements) | the whole-run kill is a theorem over the pipeline at every fuel above the floor |
| **V1-6 the exit review and the tag** | (i) `cite_check.sh` into the gate (§7.3); (ii) the docs pass: G1.7's answer with the derived rule, the conjunction/existential line in the rule table, the 40 % no-rule figure stated, the sequential-one-thread property stated on every surface, the boundary of the tag stated as "emitted Core, call-free" if §7.1 is adopted, `refinedc/dev` wording, the synthetic exhibits' role, CLAIMS C6; (iii) a FRESH full ARCHITECTURE review (new reviewer) with G2.4 (the two adequacy routes) as a named question; (iv) **the PL-expert review**: a fresh reviewer briefed with §0's four criteria and this document, asked what a competent separation-logic referee would find missing or wrong — PASS = no D-severity finding; (v) the tag | O | M | V1-1 … V1-5 | the review report committed; the tag |

Estimate: V1-1 1–2 days; V1-2 ½–1; V1-3 ½; V1-4 ≈ ½ day each including
charter, review, audit and landing (≈ 1½ days serialised); V1-5 1–3 (design
first; M–L); V1-6 ≈ 1. About two weeks to the "v1a" tag.

### 4.2 Phase II — deferred, with unlock conditions

| item | what | unlock | reference material |
|---|---|---|---|
| **V2-1 the coupling library** (G2.1; landing charter L6; Lane C §6) | extract the fragment-independent coupling (`Heap`, `MemWF`, the bundles, `EnvLaws`, `MachineCtx`/`Ctl`/`Config`, the ND collapse, the cold start) into a second Lake package; the demo imports it; every pin byte-identical (Lane C §6.5: 2–4 worker-days) | the tag (a stable surface to extract from); Lane C question 3 ratified | Lane C §6 module graph; residuals charter D9 (statement shape) |
| **V2-2 `ProcSpec` logical variables** (G1.2) | the spec table indexed by a logical variable (Lane C §1.4 option (i)): a judgment-text change on `wps_call`/`procSpecs_intro` and the `wpt` twins, `emptyProcSpec` surviving at the unit index | Lane C question 1 — or §7.4 pulls it into Phase I | Lane C §1.4 |
| **V2-3 structs / tag definitions** (G1.4; t7) | lift `htd : M.tagDefs = fmapEmpty` to the file's tag table; t7 certified | provider: arbitrary tag environments need `Acyclic`/`AcyclicPair` for the sufficiency theorems (risk map §6) | residuals charter D8 |
| **V2-4 calls — E6** (t2, t3, t10) | the C call protocol, `Eccall` as a scheduler round, the `driver2` induction; acceptance t2/t3/t10 certified with oracle cross-checks (landing charter L5) | [USER R5]: after the scheduler is finished; the concurrency merge on cerberus-lean is a forced re-pin with a scout (companion §1) | G3 as REFERENCE (sound scaffolding, not taken as is); dialect design §B6/§C E6; Lane C §3 |
| **V2-5 the outcome-list closed form — E7** (t9) | factorial's fork under `unseq` | with V2-4 | Lane C §3.2 |
| **V2-6 arrays and `PtrValidForDeref`** (t8, t3) | new `Frag` shapes for the emitted array idiom and the deref check | dialect-axis decision (the corpus table says E6, the dialect design says "not an E slice") | corpus t8/t3 emitted text |
| **V2-7 general-table refinement** (C21) | `ProcSpecT.forget`; needs a table-equality or Θ-monotonicity lemma | a consumer appears (V2-1/V2-2) | refinement charter §6; its review F5 |
| **V2-8 masks** (B11) | mask-polymorphic judgments | the first invariant-backed type in the RefinedC layer | Lane C §2.4 (sized) |
| **V2-9 globals and initialisers** (G4.5) | `globs ≠ []` on the adequacy chain; the `to_pure` fuel row on the provider side | provider: an absorbing or measured `to_pure` (companion §4) | G2's a7 record ("Empty globals, empty tags and parameterless main remain explicit restrictions") |

## 5. What is explicitly NOT in "finished" for the demo

Function pointers, concurrency, external C calls (B8, ruled to the RefinedC
arc or out); the memory-model UB family beyond pure-evaluation kills;
provider-side items (the companion register); the nine Lane C questions
except where V1/V2 items above name them. Properties of EVERY export that
are disclosed, not gaps: one thread and the sequential scheduler (`drive
fmapEmpty false …`), the top mask, the fuel floors (G1.9 until decided).

## 6. How this plan is kept true

One change at a time ([USER 2026-09-02]); every landing a fresh-reviewer
range audit and an explicit merge sign-off; gate tails verbatim in
`DECISIONS.md`; this document re-dated and re-issued at the tag with the
Phase I table replaced by the exit review's verdict.

## 7. Decisions for the operator

1. **The boundary of the first tag.** The recorded disposition ([USER
   2026-09-07] R5, DECISIONS): "the v1 tag waits for E6 proper (L5)". This
   plan RECOMMENDS an interim tag "v1a — emitted Core, call-free programs"
   at the end of Phase I, with "v1" kept for E6 — because a C demo in which
   every program with a call is excluded is an interim milestone, and naming
   it so keeps the definition of done honest. Ratify or reject.
2. **Kill adequacy** (`docs/2026-09-07_kill-adequacy-design.md` §6 (a)–(e),
   branch `design/kill-adequacy`): option A now / B target; pure-evaluation
   kills first; existential location + a pinning lemma; name `wpu`; V1-5's
   place in the order (M–L).
3. **`cite_check.sh` into the gate** as a drift speedbump (open since the
   2026-09-05 snapshot).
4. **Procedure logical variables in Phase I?** Lane C question 1 / option
   (i): a judgment-text change; the review of this plan recommends it for
   "recognisably Reynolds/O'Hearn with procedures". Also Lane C question 3
   (the shared library), which V2-1 waits on.
5. **The other agent's uncommitted work** in the `demo-fuel-t1` worktree:
   two plan/charter files AND uncommitted edits to README and the append-only
   `DECISIONS.md` — commit as a record or discard (theirs to do; the register
   edit is material).
6. **Branch pruning** (R7 "keep them for now"): 25 fully-merged non-main
   branches (R7 counted eighteen on 2026-09-07 morning) and 4 worktrees
   parked on merged branches (`codex-charter-2`, `codex-refinement`,
   `demo-fuel-t1`, `land-repin`).
7. **The push**: local `main` is 107 commits ahead of `origin/main`;
   operator-gated.
8. **The numeral fuel floors** (G1.9): in scope for V1-4a (derived costs by
   `rfl`) or an explicit, recorded exemption in FUEL.md.

Not open (corrected from revision 1): E5 §S2.5's supply normalisation was
ACCEPTED as an inert limitation by R3 on 2026-09-07 (KOI B18).

## 8. Provenance

[USER 2026-09-07] (the working session; registered in DECISIONS with this
revision): the request — "collect all this into a single 'master plan' doc
… a register of everything we have at hand, and pointers to the partial
solutions that are on branches … exactly what needs to be done to get to
finished on the demo logic" — and the definition of done (§0); then "send a
fable-class agent to audit and critique the plan, make sure all factual
claims are correct and the plan is credible". [AGENT]: the inventory
(measured), the gap analysis, the plan and its sizes, the recommendations.
Review: `docs/2026-09-07_review-demo-master-plan.md` (fresh, hostile,
Fable-class; CREDIBLE WITH FIXES, C+; its seventeen fixes and Part B
recommendations are applied in this revision; its F4 census correction was
independently re-measured before the KOI A5/ARCHITECTURE/README erratum was
written). Sources: `docs/DECISIONS.md`, `docs/KNOWN-OPEN-ITEMS.md`,
`docs/2026-09-07_landing-charter.md`, `docs/2026-09-07_branch-landability-assessment.md`,
`docs/2026-09-07_landability-demo-repin.md`, `docs/2026-09-05_status-snapshot-handoff.md`,
`docs/2026-09-04_refinedc-layer-design-2.md`, `docs/2026-09-04_emitted-core-dialect-design.md`,
`docs/2026-09-07_kill-adequacy-design.md`, `cerberus-heaplang/{README,ARCHITECTURE}.md`,
`cerberus-heaplang/docs/{CLAIMS,FUEL,CAPABILITY_MANIFEST}.md`, `Audit.lean`,
`cerberus-heaplang/scripts/module_classes.tsv`, `git` (branch heads, ancestry).
