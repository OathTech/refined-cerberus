# Hostile review: the demo master plan and the cerberus-lean requests register

Reviewer: fresh external auditor [AGENT], 2026-09-07, standing of a senior PL
researcher (separation logic / Iris / mechanised semantics). Subject: branch
`docs/master-plan` @ `a446672` (= main `777ca0f` + one docs commit) in the
worktree `worktrees/codex-residuals`; every claim of
`docs/2026-09-07_demo-master-plan.md` (PLAN) and
`docs/2026-09-07_cerberus-lean-requests-register.md` (REG) was checked by
measurement against this worktree, the sibling `cerberus-lean` repository
(read-only, `git -C`) and the RefinedC donor (read-only). Nothing was
committed, checked out, built or modified; this file is the only file created;
`git status --short` shows only it. Where a check could not be run, the row
says so. Quoted outputs are verbatim; my tallies are labelled DERIVED.

## Verdict: CREDIBLE WITH FIXES

The plan's inventory is mostly accurate (the module classification, the 906/6
pins, the manifest lines, the 13 corollaries, the corpus table, the pin, the
line cites, the branch heads and the branch completeness all measure as
stated) and its sequence (file first, `seq_rmw`, serialised Codex hygiene,
kill adequacy, exit review) is a sensible order. It is NOT ratifiable as
written because (i) its central boundary decision is presented with the wrong
provenance — the recorded [USER] disposition of R5 says the v1 tag WAITS for
E6, and "v1a / call-free" is the orchestrator's own bracketed proposal; (ii)
the definition of done that anchors the whole document is not in the
append-only register at all, although the document says every quoted ruling is
verbatim from it; (iii) the companion's reassurance that the concurrency
branch does not touch the mirrored driver files rests on a VACUOUS
measurement (the files are untracked in git); and (iv) a factual error in the
`panic!` census (117 in nine seams) is inherited from ARCHITECTURE §3 / KOI A5
and is wrong at the pin (119 in ten seams — one seam is described there as
"comments only" and is not). Exact textual fixes:

1. PLAN line 13–14 ("every quoted ruling is verbatim from `docs/DECISIONS.md`")
   → either append the [USER 2026-09-07] definition-of-done ruling and the §8
   request quotes to `docs/DECISIONS.md` in the same commit, or change the
   sentence to name the chat as the source of §0 and §8 and DECISIONS for the
   rest. The register is the record; a plan whose anchor ruling exists only in
   the plan has no provenance.
2. PLAN §0 bullet 3, §4 header, §4.1 title, §7.1: replace `[USER 2026-09-07,
   R5] … (R5 offered both)` and `R5's "v1a" reading` with: "[USER 2026-09-07]
   R5, verbatim: 'okay so this stays as residual until we've finished the
   scheduler completely? Yes, this is fine to leave until later.' The recorded
   disposition (DECISIONS, the same entry) is 'the v1 tag waits for E6 proper
   (L5)'. The 'v1a … emitted Core, call-free programs' alternative was the
   orchestrator's bracketed recommendation in the landing charter §1 R5, not a
   ruling. This plan RECOMMENDS changing the recorded disposition; decision
   §7.1 is that change." Title §4.1 "V1 — the call-free emitted-Core demo
   (PROPOSED boundary; recorded disposition: v1 waits for E6)".
3. REG §1 last bullet: delete the parenthesis "DERIVED, `git diff --stat` on
   `Driver.lean`, `Core_run.lean`, `Nondeterminism.lean`, `Core_reduction.lean`
   is empty" and the claim it supports. Replace with the true measurement:
   `lean_frontend/generated/` is untracked in cerberus-lean (`git ls-files
   lean_frontend/generated` → 0 files); against the merge-base `31eba718e` the
   branch changes the `.lem` SOURCES of exactly those generated files
   (`frontend/model/driver.lem | 708`, `core_run.lem | 50`,
   `core_reduction.lem | 141`, `core_run_aux.lem | 211`, plus
   `cmm_csem.lem | 45`, `cmm_op.lem | 5`, `mini_pipeline.lem | 2`). Its merge
   is a forced re-pin with a scout; R-9 already says so — §1 must not say the
   opposite.
4. PLAN §1.4/§3.1 G3.1, REG R-2/F-3, and (outside these two documents)
   ARCHITECTURE §3 and KOI A5: "117 `panic!` arms … nine of the 37 seams" →
   pending a second independent verification (errata rule): 119 code arms in
   TEN manifest seams; `CerbFloat.lean:183` and `:307` are code arms
   (verbatim below), `CerbFloat.lean` is manifest line 32, and the primed
   `generated/CerbFloat.lean` is byte-identical. Strike ARCHITECTURE §3's
   "`CerbFloat.lean` and `CerbND.lean` mention `panic!` in comments only" (true
   only of `CerbND.lean`).
5. PLAN §3.1 G1.1 and §4.1 V1-4a: "17 statement sites (14 `hsup : 600 ≤ …` +
   3)" → at `777ca0f`: 18 (15 + 3); T4 has 10, not 9 — the refinement slice's
   `t4_wps_of_wpt` (CorpusT4Exhibit.lean:1469) carries the premise. The D3
   census (branch `codex/park-D3`, "2 + 3 + 9 = 14") was taken at `1e1f584`.
6. PLAN §2 parked-branch row: "G3 … (14e7dc3..6c8e7e3, 13)" → 12 commits
   (inclusive; `git rev-list --count 14e7dc3^..6c8e7e3` = 12). G2 "10" and G4
   "4" are inclusive counts and correct.
7. PLAN §0 row (4) and §4.1 V1-1 acceptance: "the FILE in the statement is the
   pipeline's whole file" / "each `t*_certified_production` states the
   pipeline's file" → "states a machine-quoted DATA TERM of the pipeline's
   whole file (`EmittedFile.restore cmp data`, comparators quantified under
   three finite `Bool` checks), equal to the pinned Lean frontend's file by an
   EXECUTABLE round-trip check — the [USER 2026-09-04 Q3] option (b)
   mechanised; option (a), the elaborator in the statement, remains the named
   target and is not delivered by V1-1". Add the quoter
   (`scripts/derive_file_to_expr.lean`, `emitted_frontend.lean`) to §1.6 as a
   new trusted component with a mover (the independent `BEq` is a check, not a
   proof).
8. PLAN §3.1 G1.5: "fifteen NO-RULE variants" → 24 (the manifest line at
   `777ca0f`; "fifteen" is the Lane C note's 2026-09-04 count).
9. PLAN §1.2: "§4.4 below" → "§4.1 V1-5 / §7.2" (there is no §4.4). §4.1 V1-5
   "(§7 (a)–(e))" → "(§6 (a)–(e))" (the note's §7 is Provenance);
   `overflow_certified_killed` → the note's `wpu_certified_killed` (or say the
   name is the plan's). Say that
   `docs/2026-09-07_kill-adequacy-design.md` is on branch
   `design/kill-adequacy` @ e87a97c, not on main.
10. REG §1 bullet 6 (fuel-measure cost): the monotonicity-rejection text ("not
    statable for `drive`", "opaque sentinels") is from
    `lean_frontend/docs/2026-09-07_pure-failure-correspondence-design.md` §4
    (rows "The 8 pending fuel rows" and "Fuel monotonicity (lem TODO 13 …)"),
    not from the fuel-measure-cost charter, which does not mention
    monotonicity. Re-attribute.
11. REG R-10: "status not visible in their mainline records" → the mainline's
    `2026-09-06_concurrency-integration-charter.md` names it (I3 "deliver
    provider agreement … under the reviewed `epar_free`/fragment/state/fuel
    hypotheses"), and the branch's `2026-09-05_concurrency-S5-record.md` §4
    reads "NOT done: the agreement lemma — an ACCEPTED Phase-0 obligation, not
    discharged". Cite both.
12. PLAN §2 worktree row / §7.6: name the files (`docs/2026-09-05_demo-
    completion-charter.md` — titled "Demo completion master plan", filename
    dated 09-05, mtime 2026-09-07 00:05:43 — and
    `docs/2026-09-07_fuel-adequacy-t1-charter.md`, 00:07:06) AND the
    uncommitted modifications `README.md | 8 +` and `docs/DECISIONS.md | 55 +`
    in that worktree; a pending edit to the append-only register is material.
13. PLAN §7.7: "the eleven fully-merged Codex/landing branches and the six
    parked worktrees on merged branches" → measured: 25 fully-merged non-main
    branches (26 of 40 refs are ancestors of main, incl. `main`; the landing
    charter's R7 said eighteen); 4 worktrees sit on merged branches (`codex-charter-2`, `codex-refinement`, `demo-fuel-t1`,
    `land-repin`). Name the set or drop the numbers.
14. PLAN §1.1 row 1: "79 560 lines" is `CerberusHeapLang/*.lean` WITHOUT
    `Examples/` (4 783; whole tree 84 343); the "largest" list skips
    `ListRevExhibit` (1 985 > `Rules` 1 826). §1.7 "63 signature snapshots" →
    63 `.txt` files, 54 of them `*signatures*`. §6 "One change at a time
    ([USER 2026-09-04])" → [USER 2026-09-02] (DECISIONS line 349). §1.1/§1.6
    paths: `scripts/module_classes.tsv`, `scripts/corpus_skeleton.lean`,
    `scripts/cite_check.sh`, `scripts/signature_snapshot.lean` are
    `cerberus-heaplang/scripts/…`; `scripts/semantics-pin.env` and
    `scripts/setup-cerberus-dep.sh` are repo-root — use two prefixes.
15. REG §1 bullet 1: "the only Lean/lem additions are … `FailureReachProbe.lean`
    and its `.lem` fixture" → also added (all under `tests/`):
    `FailureMain.lean`, `FailureReach.lean`, `failure_main.ml`, nine
    `reach/*.c`, and `tests/provider-smoke/ProviderSmoke.lean`. The
    substantive point (no change under `lean_frontend/generated`, the seams,
    `frontend/`, `lean_frontend/native`) holds.
16. PLAN §4 sizes sentence: "the refinement slice's two fixed theorems took the
    agent about an hour" → the record's snapshots are 20:26:28 (baseline) →
    20:29:31 (T1-post) → 20:33:32 UTC (T2-post): seven minutes between
    snapshots; no launch time is recorded. Either cite a source for "an hour"
    or write "under an hour from activation to record (snapshot span 7 min)".
17. PLAN §7.5: strike the decision — R3 ACCEPTED it on 2026-09-07 (KOI B18;
    DECISIONS 3009–3011); or restate it as "lift later (mover per B18)".

## Findings table

| id | sev | doc § | claim (one line) | how verified |
|---|---|---|---|---|
| F1 | Critical | REG §1 bullet 7 | `feature/concurrency`'s diff "does not touch the four generated driver files … `git diff --stat` … is empty" | `git -C cerberus-lean ls-files lean_frontend/generated \| wc -l` → `0` (untracked; the diff is empty vacuously). `git diff --stat 31eba718e feature/concurrency -- '*.lem'` → `frontend/model/driver.lem \| 708 ++++…`, `core_run.lem \| 50`, `core_reduction.lem \| 141`, `core_run_aux.lem \| 211`, `cmm_csem.lem \| 45`, `cmm_op.lem \| 5`, `mini_pipeline.lem \| 2`; `7 files changed, 966 insertions(+), 196 deletions(-)` |
| F2 | High | PLAN lines 13–14, §0, §8; REG §6 | "every quoted ruling is verbatim from `docs/DECISIONS.md`" — the §0 definition of done and the §8/REG §6 request quotes | newline-joined `grep -F` of `docs/DECISIONS.md` (3 787 lines): `The done state` 0, `recognisably Reynolds` 0, `reasonable PL expert reviewer would view the logic as good and complete` 0, `master plan` 0, `register of everything we have at hand` 0, `get to finished` 0, `companion document` 0, `what has landed on main in the other repo` 0; no DECISIONS entry was added by `a446672` |
| F3 | High | PLAN §0 bullet 3, §4, §4.1, §7.1 | "[USER 2026-09-07, R5] … 'stays as residual until we've finished the scheduler completely'"; "R5 offered both"; "R5's 'v1a' reading: 'emitted Core, call-free programs'" | DECISIONS 3002–3004 (verbatim [USER]): `R5, E6 and E7 - okay so this stays as residual until we've finished the scheduler completely? Yes, this is fine to leave until later.` Disposition, same entry: `R5 E6/E7 PARKED as a residual until the scheduler work is finished completely — the v1 tag waits for E6 proper (L5)`. `v1a` in DECISIONS: 0 hits. `docs/2026-09-07_landing-charter.md:54–58` (the [AGENT] bracket): `[Park now; E6 proper after L4; the v1 tag waits for E6 — or, if the operator prefers an earlier tag, v1a after L4 as "emitted Core, call-free programs".]` |
| F4 | High | PLAN §1.4, §3.1 G3.1; REG R-2, F-3; (ARCHITECTURE §3; KOI A5) | "117 `panic!` arms in the hand-written semantics", "nine of the 37 seams" | Stripper (block/line comments removed, strings kept) over `.cerberus-ws/lean_frontend/*.lean`: `CerbMem.lean 60, CerbFS.lean 36, CerbDecode.lean 7, CerbUtils.lean 4, CerberusImpl.lean 4, CerbFloat.lean 2, CerbLocation.lean 2, Main.lean 2, CerbTags.lean 1, CoreParser.lean 1`, `TOTAL … 119`. `CerbFloat.lean:183: \| none => panic! s!"CerbFloat.of_string: {s} (OCaml Cerb_floating.of_string raises Failure)"`; `:307: panic! "CerbFloat.truncToInt: nan/inf (OCaml Z.of_float raises Z.Overflow)"`. `handwritten_copy.manifest:32:CerbFloat.lean`. `cmp CerbFloat.lean generated/CerbFloat.lean` → IDENTICAL. ARCHITECTURE.md:614: "`CerbFloat.lean` and `CerbND.lean` mention `panic!` in comments only" — false for CerbFloat. Needs a second verification before the KOI erratum |
| F5 | Medium | PLAN §3.1 G1.1, §2 park-D3 row, §4.1 V1-4a | "17 statement sites (14 `hsup : 600 ≤ …` premises + 3 …)", "(T5 2, T6 3, T4 9)" | `grep -rn 'hsup : 600 ≤' CerberusHeapLang` → 15 (`CorpusT4Exhibit 10, CorpusT5Exhibit 2, CorpusT6Exhibit 3`); the 10th T4 site is `1469` in `theorem t4_wps_of_wpt` (the refinement slice); `600 ≤ sup →` in Shipped.lean → 3. DERIVED total 18. The park-D3 record: `Complete hsup : 600 ≤ … census at this head (2 + 3 + 9 = 14)` at activation `1e1f584` |
| F6 | Medium | PLAN §2 | "G3 … (14e7dc3..6c8e7e3, 13)" | `git rev-list --count 14e7dc3^..6c8e7e3` → 12; exclusive 11. (G2 `3aac95d^..5bfe992` → 10 ✓; G4 `567c578^..19292c0` → 4 ✓; G1 `8ddfeb8^..520654f` → 17 ✓.) The landability doc carries the same 13 |
| F7 | Medium | PLAN §0 row (4), §4.1 V1-1 | V1-1 makes each `t*_certified_production` "state the pipeline's file" | `a41292d:EmittedT1Exhibit.lean:605–617`: `theorem certified_production [LemFuel] (hfuel : 50 ≤ LemFuel.fuel) (cmp : EmittedFile.Comparators) (hstd : … intLibraryCheck cmp.stdlib = true) (hmain : mainLookupCheck cmp.funs = true) (hlabels : labelUnionCheck cmp = true) … CerbND.runND (_root_.drive (restoredFile cmp).tagDefs false (restoredFile cmp) args) …`; `EmittedFile.lean:81 def restore (cmp : Comparators) (d : Data) : file …`, `:86 impl0 := restoreMap cmp.impl d.impl`; `Examples/EmittedT1Data.lean \| 42841 +`. Landability §4.1: "NOT option (a) … It is option (b) … mechanised". DECISIONS 2472–2476: option (b) is the ruled form; "the elaborator-in-the-statement form is the named target, not done" |
| F8 | Medium | REG §1 bullet 6 | fuel monotonicity "explicitly rejected as that charter's subject" with the quoted reasoning | `git show arc/fuel-measure-cost:lean_frontend/docs/2026-09-07_codex-charter-fuel-measure-cost.md \| grep -i monoton` → no line; the wording is in `2026-09-07_pure-failure-correspondence-design.md:237–238`: `\| The 8 pending fuel rows (fail-open) \| opaque sentinel value at exhaustion \| …`, `\| Fuel monotonicity (lem TODO 13, consumer §3 bullet 3) \| not statable for \`drive\` \| …` |
| F9 | Medium | REG R-10 | S5 agreement lemma "status not visible in their mainline records" | mainline `lean_frontend/docs/2026-09-06_concurrency-integration-charter.md:43`: `\| I3 — deliver provider agreement \| Kernel-checked observer agreement under the reviewed \`epar_free\`/fragment/state/fuel hypotheses …`; branch `2026-09-05_concurrency-S5-record.md:172`: `## 4. NOT done: the agreement lemma — an ACCEPTED Phase-0 obligation, not discharged` |
| F10 | Medium | PLAN §3.1 G1.5 | "fifteen NO-RULE variants classified by [AGENT]" | `CAPABILITY_MANIFEST.md:183`: `MANIFEST: 35 constructors, 78 variant rows (47 RULE, … 24 NO-RULE, 7 OUT-OF-SCOPE)`; "fifteen" is `docs/2026-09-04_refinedc-layer-design-2.md:191 ### 1.5 The fragment boundary and the fifteen NO-RULE variants` (2026-09-04) |
| F11 | Medium | PLAN §2 worktree row, §7.6 | the other agent's uncommitted work is "a 'demo completion master plan' and a 'fuel, adequacy and t1 charter' dated 2026-09-07 00:05" | `git -C worktrees/demo-fuel-t1 status --short`: ` M README.md`, ` M docs/DECISIONS.md`, `?? docs/2026-09-05_demo-completion-charter.md`, `?? docs/2026-09-07_fuel-adequacy-t1-charter.md`; `diff --stat`: `README.md \| 8 ++++++++`, `docs/DECISIONS.md \| 55 ++…`; mtimes 00:05:43 / 00:07:06 |
| F12 | Medium | PLAN §7.7 | "eleven fully-merged Codex/landing branches and the six parked worktrees on merged branches" | branch sweep (below): 40 refs, 26 ancestors of main incl. `main` (25 non-main), 14 unmerged; `git worktree list`: 10 worktrees, 4 non-primary ones on merged branches (`codex-charter-2`, `codex/total-refines-partial`, `demo-fuel-t1`, `land/repin-89f7e68`); landing charter R7: "Delete the eighteen fully-merged branches" |
| F13 | Low | PLAN §1.2, §4.1 V1-5, §7.2, §8 | cross-references to the kill-adequacy note | "§4.4 below" has no target; V1-5 says "§7 (a)–(e)" but decisions are `## 6. Decisions for the operator (a)–(e)` and `## 7. Provenance` (branch `design/kill-adequacy` @ e87a97c; the file is absent on main); the note names `wpu_certified_killed`, not `overflow_certified_killed`; its commit message says "six operator decisions", the note has five |
| F14 | Low | PLAN §1.1 | "79 560 lines"; "largest: … Rules 1 826" | `wc -l CerberusHeapLang/*.lean` → `79560 total`; whole tree → `84343 total`; `ListRevExhibit.lean 1985`, `Examples/CorpusE0.lean 1792` |
| F15 | Low | PLAN §6 | "One change at a time ([USER 2026-09-04])" | DECISIONS:349 `- **2026-09-02 [USER] ONE CHANGE AT A TIME; REYNOLDS/O'HEARN IS THE STABLE SPEC**` |
| F16 | Low | REG §1 bullet 1 | "the only Lean/lem additions are a failure-reach probe test … and its `.lem` fixture" | `git diff --name-status 89f7e68 mdd/cerberus-lean \| grep ^A \| grep -E '\.(lean\|lem\|ml\|c)$'` → 15 files: `…census-evidence/FailureReachProbe.lean`, `tests/failure-probes/{FailureMain.lean, FailureReach.lean, discarded_failures.lem, failure_main.ml}`, `tests/failure-probes/reach/*.c` ×9, `tests/provider-smoke/ProviderSmoke.lean`. No path under `lean_frontend/generated/`, `lean_frontend/<seam>.lean`, `lean_frontend/native/`, `frontend/`, `backend/` |
| F17 | Low | REG §1 bullet 2 | "Tier A 13 gates" | `scripts/LADDER.md` `## Tier A` table rows numbered 1–11 (DERIVED); 13 not found in the ladder |
| F18 | Low | PLAN §1.1/§1.6/§1.7 paths | `scripts/module_classes.tsv`, `scripts/corpus_skeleton.lean`, `scripts/cite_check.sh`, `scripts/signature_snapshot.lean` | `find` → all four under `cerberus-heaplang/scripts/`; `scripts/semantics-pin.env`, `scripts/test_unit.sh`, `scripts/setup-cerberus-dep.sh` at the repo root |
| F19 | Low | PLAN §4 sizes | "the refinement slice's two fixed theorems took the agent about an hour" | `codex-refinement-notes.md:139–140, 324–325`: baseline `2026-09-07 20:26:28`, T1-post `20:29:31`, T2-post `20:33:32 +0000`; orchestrator gates 20:59:44 and 21:23:51 (DECISIONS 3757–3759); no launch time recorded |
| F20 | Info | PLAN §1.5 | "nine synthetic (authored-Core) exhibits" | `module_classes.tsv`: 24 `positive-client` = 16 authored (`Exhibit, LoopExhibit, FibExhibit, ArrayExhibit, ListRevExhibit, TreeRotExhibit, CaseExhibit, WseqExhibit, StructExhibit, AllocExhibit, DisposeExhibit, RegionLoopExhibit, MallocListExhibit, FibRecExhibit, TwoLabelExhibit, EvenOddExhibit`) + 3 `Emitted*` + 4 `CorpusT*` + `PartialClients`; nine = those with `*_shipped` corollaries. DECISIONS 2479–2480 (E0 Q7): "the sixteen authored exhibits stay as the regression suite" |
| F21 | Info | PLAN §1.2 | "`wps` … a guarded fixpoint over iris-lean's WP" | `Wps.lean:322 def wps … := fixpoint (wps.pre M p Ls Θ)`; `wps.pre` (232–265) re-states the WP step case over `stateInterp`/`PrimStep.Reducible`/`£ 1` rather than calling `wp`; iris-lean's `WP` is the raw stratum (`Rules.lean:236 wp_of_atomic`) and the collapse target (`Wps.lean:4752 wps_sound … ⊢ … WP (⟨e, ρ, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Ψ w.sv w.ρ }}`); adequacy via `wp_strong_adequacy_gen` (Adequacy.lean:524, 626). "Over" is defensible; "the same construction as" is the exact wording |
| F23 | Medium | PLAN §7.5 | "E5 §S2.5 … (B18): ratify or veto — open since 2026-09-05" | KOI B18: `ACCEPTED as an INERT limitation ([USER 2026-09-07], the landing charter's R3, verbatim in DECISIONS: "R3 - okay so this is a limitation we will have to lift later, but here is inert? Sure that's fine")`; DECISIONS 3009–3011 disposition `R3 the E5 §S2.5 seeded-supply normalisation ACCEPTED as an inert limitation to be lifted later → a KOI row with that mover`. The decision is not open |
| F22 | Info | PLAN §1.7 | "63 signature snapshots" | 63 `.txt` in `cerberus-heaplang/docs/`; 54 match `signatures`; the other 9: `2026-09-05_e5b-axioms.txt`, `2026-09-05_e5-t6-execution-axioms.txt`, `2026-09-07_codex-D5b-post.txt`, `…D5-post.txt`, `…D7-post.txt`, `…refinement-baseline.txt`, `…T1-post.txt`, `…T2-post.txt`, `2026-09-07_l2-signature-census.txt` |

## Part A — claim-by-claim

Legend: ✓ measured as stated; ≈ true in substance, imprecise or differently
scoped; ✗ wrong. "PLAN" = the master plan, "REG" = the requests register.

### A.1 PLAN §1.1 — the package in numbers

| claim | measurement | verdict |
|---|---|---|
| Lean in `CerberusHeapLang/`: 79 560 lines | `wc -l CerberusHeapLang/*.lean … 79560 total`; incl. `Examples/`: `84343 total` (60 files) | ≈ (top level only; say so) |
| largest: Soundness 10 539, Round 7 455, Step 6 398, Wps 5 556, Wpt 5 318, Heap 4 859, DriverCollapse 2 970, EvalClass 2 744, Adequacy 2 358, Rules 1 826 | all ten numbers exact; but `ListRevExhibit.lean 1985` and `Examples/CorpusE0.lean 1792` sit between Adequacy and Rules / below Rules — the list is not the top-10 | ≈ |
| 60 modules = 19 core, 24 positive-client, 2 declared-smoke, 2 negative-test, 2 semantic-test, 3 production-wrapper, 3 production-core, 4 example-support, 1 audit; 26 consumer | `module_classes.tsv` non-comment rows: 60; `uniq -c`: `1 audit, 19 core, 2 declared-smoke, 4 example-support, 2 negative-test, 24 positive-client, 3 production-core, 3 production-wrapper, 2 semantic-test` (DERIVED); manifest line 98 `MODULES: 60 classified, 26 consumer modules` | ✓ |
| 906 trio-exact + 6 axiom-free pins; gate line `export pins: 906 trio-exact, 6 axiom-free-exact` | Audit.lean:271–1104 backticked names with comment lines stripped: 906, distinct 906, `uniq -d` empty (DERIVED); `axiomFreeExports` (1111–1118): 6; DECISIONS 3766 quotes `info: CerberusHeapLang/Audit.lean:1123:0: CerberusHeapLang export pins: 906 trio-exact, 6 axiom-free-exact` | ✓ |
| claims 18 rows C1–C18, 195 declaration names checked | `docs/CLAIMS.md` rows `\| C1 — … \| C18 — ` at lines 36–53 (18); manifest line 184 `CLAIMS: 18 claim rows, 195 declaration names checked in the theorem cell, 352 …` | ✓ |
| 35 `Frag` constructors, 78 variants: 47 RULE, 24 NO-RULE, 7 OUT-OF-SCOPE, 0 undemonstrated | `Fragment.lean:491 inductive Frag`, 35 constructors (DERIVED); manifest line 183 `MANIFEST: 35 constructors, 78 variant rows (47 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 7 OUT-OF-SCOPE), 0 red, 26 consumer modules` | ✓ |
| 13 `*_shipped` corollaries: exhibitA, fib, counter_loop, list_reverse, dispose_list, region_loop, malloc_list, fib_rec, even_odd, t1, t4, t5, t6 | `Shipped.lean` theorems: `exhibitA_prod_shipped, fib_certified_production_shipped, counter_loop_…, list_reverse_…, dispose_list_…, region_loop_…, malloc_list_…, fib_rec_…, even_odd_…, t1_…, t4_…, t5_…, t6_certified_production_shipped` — 13 (DERIVED) | ✓ |
| corpus: 10 C programs t1…t10; 4 certified end to end (t1, t4, t5, t6) | `ls docs/corpus-e0/*.c \| wc -l` → 10 (50 files: `.c/.core/.annot.core/.seq.core/.seqrw.core` ×10); `Examples/CorpusE0.lean:1676 corpusTable` = t1, t5_ifelse, t6_switch, t4_while; `pendingCorpus` = t2, t3, t7, t8, t9, t10 | ✓ (the table is in `Examples/CorpusE0.lean`, consumed by `scripts/corpus_skeleton.lean`) |
| the four certified by `t{1,4,5,6}_certified_production` | `CorpusT1Exhibit.lean:806 theorem t1_certified_production [LemFuel] (hfuel : 50 ≤ LemFuel.fuel) (sup : Nat) …`; `CorpusT4Exhibit.lean:1425 … (hfuel : 917 ≤ …)`; `CorpusT5Exhibit.lean:542 … (hfuel : 90 ≤ …)`; `CorpusT6Exhibit.lean:748 … (hfuel : 80 ≤ …)` | ✓ |
| 33 package warnings (KOI C5 baseline), source "gate log" | DECISIONS 3756 `… 0 UNCAPPED, 33 warnings,` (the `ed82837` landing gate); KOI C5 `… 44 (L2 re-pin) → 33 after the L2 audit's H-1 fix`; `codex-refinement-notes.md:104` `DERIVED baseline package warning count: 33` | ✓ |
| pin cerberus-lean `89f7e688530c6910884518811d645e4e892e4507`, LemLib `f6542f8e…`, Lean 4.32.2 | `scripts/semantics-pin.env`: `CERBERUS_LEAN_COMMIT="89f7e688530c6910884518811d645e4e892e4507"`; comment: `LemLib pin 045dcb0 -> f6542f8`; `lakefile.toml`/README toolchain 4.32.2 | ✓ |

### A.2 PLAN §1.2–§1.5 — the logic, the layer, the connection, the programs

| claim | measurement | verdict |
|---|---|---|
| `wps M p Ls Θ Ψ e ρ` at Wps.lean:322; four clauses (value, jump, call, step) | `Wps.lean:322 def wps [SpikeGS hlc GF] (M : MachineCtx) (p : Option sym) (Ls : LabelSpec GF) (Θ : ProcSpec GF) : … := fixpoint (wps.pre M p Ls Θ)`; `wps.pre` at :232 matches `toVal e` / `jumpRedex? e` / `callRedex? e` / step | ✓ |
| `wpt M p Ls Θ k Ψ e ρ` at Wpt.lean:203, well-founded on the budget; a jump must decrease, a call splits | `Wpt.lean:203 def wpt … \| k => wpt.pre … (fun k' _ => wpt M p Ls Θ k')  termination_by k => k`; `wpt.pre`: jump `⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ`; call `(m k' : Nat) (hb : 1 + m + k' ≤ k)` | ✓ |
| both at the top mask | `wps.pre`: `\|={⊤}=>`, `={⊤,∅}=∗`, `={∅,⊤}=∗`; `wpt.pre` same; `wps_sound` target `WP … @ Stuckness.NotStuck; ⊤`; KOI B11 "21 + 26 sites" | ✓ |
| `wps_of_wpt` at Wpt.lean:5257; empty procedure table; `LabelSpecT.forget` | `Wpt.lean:5252 def LabelSpecT.forget (Ls : LabelSpecT GF) : LabelSpec GF := fun l vs ρ => iprop(∃ (m : Nat), Ls l m vs ρ)`; `:5257 theorem wps_of_wpt … wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ wps M p (LabelSpecT.forget Ls) emptyProcSpec Ψ e ρ` | ✓ |
| claim C18 says total refines partial | CLAIMS row `C18 — Total refines partial: … \| LabelSpecT.forget, wps_of_wpt, t4_wps_of_wpt \| metatheorem / corollary …` | ✓ |
| `AtomicStep` (Rules.lean), `wp_of_atomic`/`wps_of_atomic`/`wpt_of_atomic` | `Rules.lean:220 def AtomicStep`, `:236 theorem wp_of_atomic`; `Wps.lean:377 wps_of_atomic`; `Wpt.lean:680 wpt_of_atomic` | ✓ |
| `wps_create`/`wpt_create`, `wps_frame`, `wps_frame_labels`, `wpt_frame_labels`, `wps_wand`, `wpt_mono_k`, `wps_if`, `wps_save`/`wps_run`/`blockSpecs_intro`, `SymFrame`, `envAdd_lookup` | Wps.lean: 4203, 697, 728, 516, 1718, 1872, 414, 4312; Wpt.lean: 4028, 568, 299; EnvLaws.lean: 309 (`def SymFrame`), 325 | ✓ |
| "the total twins with `1 + m ≤ k`" | `wpt.pre` jump clause `⌜1 + m ≤ k⌝` | ✓ |
| Hoare's rule for recursive procedures, claim C9; `fib_rec`, `even_odd` | `Wps.lean:4404 theorem procSpecs_intro`; CLAIMS C9 names `procSpecs_intro, procSpecsT_intro, wps_call, wps_call_root, wpt_call, wpt_call_root, wps_sound_cps, wpt_sound_cps, fib_rec_certified(_production), even_odd_certified(_production)` | ✓ |
| C10 classical local memory rules | CLAIMS C10 row as quoted in the plan | ✓ |
| C6 mirror soundness/completeness; fuel ≥ 4; three `OpenRound` arms (B7) | CLAIMS C6: "at ambient fuel at least four every fragment round is a mirror step, a classified kill/panic, or one of two characterized residuals"; `Round.lean:402 inductive OpenRound`; KOI B7: `eval_uncovered`, `run_surplus`, `neg_sseq` | ≈ (C6's text says "two characterized residuals"; B7 says three arms — the plan follows B7; the CLAIMS row is stale by one arm, not the plan's error) |
| `wpt_sound`; `diverge_total_unprovable` (C5 "false, not merely unprovable") | `Wpt.lean:4520 theorem wpt_sound`; `DivergeExhibit.lean:178 theorem diverge_total_unprovable [LemFuel] (hfuel : 2 ≤ LemFuel.fuel) …`; CLAIMS C5 as quoted | ✓ |
| `wpt_driver_done_alloc` at ProdLoop.lean:444; partial closed form (C4); `MemWF` (C7); frame incl. specs (C8) | `ProdLoop.lean:444 theorem wpt_driver_done_alloc (hfuel : 2 ≤ LemFuel.fuel) … (htd : M₀.tagDefs = fmapEmpty) (hex : M₀.extern = fmapEmpty) …`; CLAIMS C4 (`prod_run_safe_procs, fib_rec_certified, even_odd_certified`), C7 (`MemWF` …), C8 (`wps_frame, wps_frame_labels, …, semantic_frame`); `Heap.lean:1640 structure MemWF` | ✓ |
| `OverflowExhibit`: the kill at the round is a theorem; the whole run a measurement (B16) | KOI B16 as quoted; `module_classes.tsv: CerberusHeapLang.OverflowExhibit negative-test` | ✓ |
| iris-lean pinned in `lakefile.toml` (`../deps/iris-lean`) | `lakefile.toml`: `rev = "34390a0133986385c62bf59a6eb01938945b48ec"`; `deps/iris-lean` HEAD `34390a01… 2026-08-20 fix: wp_rec keeps the evaluation context flat (#657)` | ✓ |
| `Language` instance (Lang.lean); `stateInterp` with `CohG`, allocator cursor, `budgetAuth` (Heap.lean; `SpikeGS`) | `Lang.lean:58 instance [LemFuel] : Language CoreRt Mem Empty CoreRVal`; `:112 instance instIrisGS [LemFuel] [SpikeGS hlc GF] : IrisGS_gen hlc CoreRt GF` (`stateInterp_mono` at :116); `Heap.lean:2437 class SpikeGS`, `:2493 def budgetAuth`, `:2663 structure CohG` | ✓ |
| Lane C §6 measures the module graph and recommends extraction as a second Lake package | `2026-09-04_refinedc-layer-design-2.md:768 ## 6. A shared coupling library?`, `:770 ### 6.1 The module graph (imports, measured …)`, `:866 ### 6.5 Recommendation` ("share (a), copy (b) and (c), never (d) — but not as the first move … producing `cerberus-iris/`"; "Estimate 2–4 worker-days") | ✓ |
| every production statement is over `CerbND.runND (_root_.drive fmapEmpty false FILE args) ((initial_driver_state sup FILE fs).1)` | `t1_certified_production` statement as quoted (`CorpusT1Exhibit.lean:806–814`); the awk sweep over the 13 `*_certified_production` + `exhibitA_prod` statements: `no Step/Frag \| no device \| prodFile*` for all 13 | ✓ |
| `setup-cerberus-dep.sh --check`, 37 hand-written seams | `handwritten_copy.manifest` non-comment lines: 37; `setup-cerberus-dep.sh:132 # --- C: hand-written seam identity (runs in BOTH modes; fail-closed)`; KOI E "(37 seams)" | ✓ |
| A5 117 `panic!` arms | 119 in ten seams (F4) | ✗ |
| A3, B9, B12, B21 as declared boundaries | KOI rows A3 (`dynamic_addrs`), B9 (`Step`-direct rules, "possibly forever" DECISIONS:382), B12 (two bridges), B21 (allocator preconditions) | ✓ |
| §1.5 t1 CERTIFIED (`t1_certified_production`, C13/E4) | CLAIMS C13/C14 (E3/E4), theorem exists | ✓ |
| t4 budget 915 (C17), t5 88 (C15) + `t5_wps`, t6 78 (C16) | CLAIMS C15/C16/C17 rows quote budgets 88/78/915; `Examples/PartialClients.lean:536 theorem t5_wps` | ✓ |
| t2 → E6; t3 → E6 + `PtrValidForDeref`; t7 → B4/D8; t8 → E6 (arrays; `PtrValidForDeref`); t9 → E7; t10 → E6 | `pendingCorpus`: `("t2…", "E6 (Eccall; the helper call in a for loop)"), ("t3…", "E6 (Eccall, PtrValidForDeref)"), ("t7…", "outside E — KOI B4 (tagDefs)"), ("t8…", "E6 (arrays; PtrValidForDeref)"), ("t9…", "E7 (the outcome-list closed form)"), ("t10…", "E6 (Eccall; mutual recursion)")` | ✓ (note the dialect design §C.8 says arrays are "Not an E slice" — the corpus table and the design disagree; the plan's V2-6 "dialect-axis decision" is the honest reading) |
| every adequacy export carries `htd : M.tagDefs = fmapEmpty` | `grep -rn 'htd : .*tagDefs = fmapEmpty'` → 37 sites; `hex : .*extern = fmapEmpty` → 38 | ✓ |
| D6 token-for-token check; blind spots = printer's (C20) | KOI C20 as quoted; gate speedbump `corpus skeleton` in `test_unit.sh:74` | ✓ |
| FILE = `prodFileLib stdlibE3 [] tMain`, three-function std.core, `impl0 = ∅` (A7) | `ProdEntry.lean:680 def prodFileLib`, `StdCore.lean:153 def stdlibE3`; KOI A7; CLAIMS C13 "`impl0 = ∅`" | ✓ |
| nine synthetic exhibits + E1–E3 exhibits kept as regression | F20: the package has 16 authored positive clients; nine is the `_shipped` subset | ≈ |
| §1.6 gate 1 banned grep, gate 1b fuel numeral, Audit.lean; speedbumps manifest/corpus/import/boundary; `cite_check.sh` outside the gate | `test_unit.sh` lines 28, 41, 48, 56, 74, 85, 108; no `cite_check` in `test_unit.sh` | ✓ |
| §1.7 `docs/`: 40 files; DECISIONS 3 787 lines; A1–A7, B1–B21, C1–C21; `cerberus-heaplang/docs/` 130 records + 63 snapshots | `git ls-tree main docs/` → 41 entries, 40 `.md` (+`corpus-e0/`); `wc -l docs/DECISIONS.md` → 3787; KOI rows present: A1–A7, B1–B21, C1–C21; `ls cerberus-heaplang/docs` → 193 = 130 `.md` + 63 `.txt` | ✓ (63 "snapshots": ≈, F22) |

### A.3 PLAN §2 — the branch register

Sweep (`git for-each-ref refs/heads` + `merge-base --is-ancestor` + `rev-list --count`; DERIVED):

```
charter-aims-amendment                   7838941 UNMERGED  ahead=4    behind=388
codex/demo-residuals-2                   bf4554d UNMERGED  ahead=8    behind=27
codex/park-D1                            55b54b5 UNMERGED  ahead=5    behind=27
codex/park-D2                            09f9b90 UNMERGED  ahead=6    behind=27
codex/park-D3                            450c87e UNMERGED  ahead=7    behind=27
codex/park-D4                            2ad35c7 UNMERGED  ahead=8    behind=27
demo-repin                               a41292d UNMERGED  ahead=65   behind=75
design/kill-adequacy                     e87a97c UNMERGED  ahead=1    behind=7
dialect-e5                               cb46e4c UNMERGED  ahead=21   behind=75
docs/master-plan                         a446672 UNMERGED  ahead=1    behind=0
lane-b-seed                              f4f9a20 UNMERGED  ahead=3    behind=233
parked/demo-expansion-2026-09-07         a41292d UNMERGED  ahead=65   behind=75
repin-scout                              8847a2f UNMERGED  ahead=1    behind=224
repin-scout2                             07ceb44 UNMERGED  ahead=1    behind=152
```
(The other 26 of the 40 refs — incl. `main`, `refinedc/dev`, `demo-fuel-t1` — are ancestors of main: ahead=0.)

| claim | measurement | verdict |
|---|---|---|
| `parked/demo-expansion-2026-09-07` = `demo-repin` @ a41292d, 65 beyond main | both refs a41292d, ahead=65 | ✓ |
| G1 re-pin LANDED as L2; G2 3aac95d..5bfe992 (10); G3 14e7dc3..6c8e7e3 (13); G4 567c578..19292c0 (4) | inclusive counts 10 / 12 / 4 (F6); G1 17 | G2 ✓, G3 ✗, G4 ✓ |
| G2 content: emitted file as a Lean data term produced by `scripts/inspect-emitted-file.sh`, round-trip check, `mkAuxLemma` device, option (b) mechanised | `git diff --stat 3aac95d 5bfe992`: `Examples/EmittedT1Data.lean \| 42841 +`, `scripts/derive_file_to_expr.lean \| 107 +`, `scripts/emitted_frontend.lean \| 55 +`, `scripts/inspect-emitted-file.sh \| 93 +-`; landability §4.3 "`reference_main_labels` submits `Eq.refl` to the kernel through `mkAuxLemma`"; §4.1 "option (b) … mechanised" | ✓ |
| G3: kernel-sound over shipped engine functions; no acceptance program; changes `Step`/`wps`/`wpt`/`Frag` | landability §5.1–§5.4 as quoted; inclusive Lean diff `14e7dc3^..6c8e7e3`: `Step.lean \| 736`, `Wps.lean \| 308`, `Wpt.lean \| 228`, `Soundness.lean \| 1241`, `DriverCollapse.lean \| 883`, … (12 files) — `Frag` lived in Soundness/Step at that base | ✓ |
| G4 `seq_rmw` (4): engine arms mirrored, rules at cost 8, PROVISIONAL | commits `5c8a5ed fix: recognize SeqRMW in public bound guards`, `c8a973f feat: certify SeqRMW mirror against engine`, `19292c0 feat: add bound SeqRMW public rules`; landability §6 | ✓ |
| G5 failing WIP patch (rejected); G6 records | landability §0 rows G5/G6 | ✓ |
| `dialect-e5` @ cb46e4c, landed re-cut as L1 | head `cb46e4c 2026-09-06 docs: record current dependency and fuel contracts for the next scout`; KOI C19 "re-cut from the other agent's `dialect-e5`" | ✓ |
| `codex/park-D1` 55b54b5 (kill face), `-D2` 09f9b90 (int ranges), `-D3` 450c87e (14 `hsup` census), `-D4` 2ad35c7 (`FreshAbove`) | heads and messages: `codex D1: park driver-kill adequacy — current total judgment has no kill terminal interface`; `codex D2: park symbolic-int generalization — verbatim rule has numeric range contrary to fixed goal`; `codex D3: park program-derived symbol bound — gate fence conflict and 14 premises verified`; `codex D4: park fresh-symbol abstraction — required placement and audit pin fence conflicts verified` | ✓ (D3's "14" is at 1e1f584 — F5) |
| `design/kill-adequacy` @ e87a97c, the options note | `e87a97c 2026-09-07 docs: kill-adequacy design options for the operator … options A–D … recommendation A-now/B-target … six operator decisions`; one file `docs/2026-09-07_kill-adequacy-design.md \| 206 +` | ✓ (note says five decisions (a)–(e)) |
| `refinedc/dev` @ b82e472 is an ANCESTOR of main; the package removed at `24c2410` ("main-share") | `merge-base --is-ancestor b82e472 main` → yes (ahead=0); `24c2410 2026-09-03 main-share: … Removed from main (retained on branch refinedc/dev at b82e472): the stub root package RefinedCerberus (3 files) …`; `git ls-tree main` has no `RefinedCerberus/` | ✓ |
| CLAUDE.md's "lives on `refinedc/dev`" means this commit — fix wording | CLAUDE.md line "That work … lives on the branch `refinedc/dev` until it is presentable" — a branch with ahead=0 | ✓ (the finding is right) |
| `lane-b-seed` @ f4f9a20 (3): `cerberus-heaplang-ext/`, a renamed COPY at 1d2bb95 | commits `cf58455 Lane B seed: cerberus-heaplang-ext/ — the derisking sibling, a COPY of the demo at 1d2bb95 (namespace CerberusHeapLang → CerberusHeapLangExt) …`, `0ac611f …seed-notes.md`, `f4f9a20 … range audit (1d2bb95..0ac611f) PASS`; tree has `cerberus-heaplang-ext` | ✓ |
| `repin-scout` 8847a2f, `repin-scout2` 07ceb44 dry-run records | `8847a2f 2026-09-03 repin-scout DRY RUN …`, `07ceb44 2026-09-03 Re-pin SCOUT 2 (record only) …` | ✓ |
| `charter-aims-amendment` 7838941 (4, 2026-08-30): aims check, boundary (b) retired, "the excavation", pin bump | four commits all dated 2026-08-30: `c777f1a aims alignment + pin bump …`, `7f9a6ff charter: boundary (b) retired …`, `870e20b THE EXCAVATION …`, `7838941 charter rev 3 …` | ✓ |
| `codex/demo-residuals-2` bf4554d; content landed rebased as `land/codex-stage2` | `git cherry main codex/demo-residuals-2` → 8 lines all `-` (every patch present in main) | ✓ |
| worktree `demo-fuel-t1` (branch merged), UNCOMMITTED plan + charter dated 2026-09-07 00:05 | branch `demo-fuel-t1` ahead=0; F11 (two untracked docs + uncommitted README/DECISIONS edits) | ≈ |
| Completeness: branches not merged into main that the register omits | every UNMERGED branch above appears in §2 (docs/master-plan is the document's own branch). Remote: `origin/main` = 04059dc, an ancestor of main, 107 behind — not a branch to salvage but an unpushed state the plan could note | none omitted |

### A.4 PLAN §3 — the gap tables vs KOI

| gap | KOI/source match | closes-at points at an item that addresses it |
|---|---|---|
| G1.1 `600` (B19, B20) | B19/B20 as quoted; count wrong (F5) | V1-4a ✓ |
| G1.2 logical variables (Lane C §1.4) | §1.4 text: "`ProcSpec GF := sym → List value → IProp GF × (value → IProp GF)` … The only data a pre- and postcondition can SHARE is therefore the argument value list" | V2-2 ✓ |
| G1.3 negative results measurements (B16) | B16 ✓ | V1-5 ✓ |
| G1.4 empty tag definitions (B4) | B4 ✓ (37 `htd` sites) | V2-3 ✓ |
| G1.5 three `OpenRound` arms (B7); "fifteen NO-RULE" (B14) | B7 ✓; B14 says "seven exactly … two added by the audit"; manifest 24 NO-RULE | ≈ (F10) |
| G1.6 storability at the literal 3 (B15) | B15 ✓ | V1-4b ✓ |
| G1.7 label loops vs `while` | README "The logic" says loops are `wps_save`/`wps_run` | V1-6 docs ✓ |
| G1.8 duplication (C17, C14) | C17/C14 ✓ | V1-4c ✓ |
| G2.1–G2.3 | Lane C §6, B11, §4 ✓ | V2-1 / RefinedC arc ✓ |
| G3.1 117 arms; provider census "0 discardable" | 119 (F4); `2026-09-07_pure-failure-reachability-census.md:8 DISCARDABLE positions: 0` ✓ | provider ✓ |
| G3.2 two `hQd`/`evalDepth` premises; `subst_esize` note | `(hQd :` at ProdLoop.lean:380 and :451 (two theorem statements); note exists, "No action requested." at line 22 | provider ✓ |
| G4.1 hand-built FILE (A7): out-of-range `conv_loaded_int` WRAPS through the impl | KOI A7 ✓; CLAIMS C13 ✓ | V1-1 ✓ (in the (b) sense — F7) |
| G4.2 4/10 certified; six pending = calls (3), recursion (1), structs (1), arrays (1) | `pendingCorpus` ✓ | V1-6 wording; V2 ✓ |
| G4.3 transcription by hand, C20 | ✓ | V1-1 ✓ |
| G4.4 `seq_rmw` parked only | G4 on `demo-repin` ✓ | V1-2 ✓ |

### A.5 PLAN §4 — plan items

| claim | measurement | verdict |
|---|---|---|
| V1-1 from G2 (L3): speedbump (plant), `BEq` beside `toExpr`, `mkAuxLemma` in ARCHITECTURE §3, `impl0` = pinned gcc map, A7 rewritten; then t4–t6 | landing charter L3 (a)–(e) and landability §9 F4 list the same items PLUS "(e) decide the retained wrapper `CorpusT1Exhibit`" (Q7) — the plan omits (e); `EmittedFile.restore … impl0 := restoreMap cmp.impl d.impl`; landability §4.1 "110 stdlib + 6 impl entries" | ≈ (add the Q7 decision) |
| V1-2 re-cut G4 without G3; `negFree → boundFree` census | landing charter L4 text matches | ✓ |
| V1-4 depends on V1-2 "so their baselines are final"; docs-only main while a Codex slice runs | refinement charter rule 2 (`Frozen surface` … "The diff must be EXACTLY the deliverable's ADDED list … anything else added, removed or changed = the deliverable failed → rule 7") + rule 8 (`Rebase. Before each deliverable's final gate: git rebase main`): a Lean landing on main during the slice changes the post-rebase census ⇒ rule 2 fails. Reasoning holds | ✓ |
| V1-4a fences incl. `Audit.lean`, `EnvLaws.lean`, `Shipped.lean`, gate scripts | residuals charter §9: D3 "fence + `scripts/fuel_numeral_check.sh`, `scripts/test_unit.sh`, `Shipped.lean`, negative theorem dropped"; D4 "fence + `Audit.lean`, `EnvLaws.lean`" | ✓ |
| V1-4b "the two int-range premises copied verbatim from `wps_c_add`" | charter §9 D2: "`wps_c_add` (IntRules.lean:596) has `(hs : -2147483648 ≤ n1 + n2) (hs' : n1 + n2 ≤ 2147483647)`" | ✓ |
| V1-5 option A `wpu`, pure-evaluation kill terminal, `wpu_driver_killed_alloc`, `overflow_certified_killed` | design note §2 option A "`wpu` … `wpu_driver_killed_alloc` (dual of `wpt_driver_done_alloc`) via `DriverKilledAt`"; §4 names `wpu_certified_killed`; decisions §6 (a)–(e) | ≈ (F13) |
| V1-6: `cite_check.sh` decision pending since the 2026-09-05 snapshot | status snapshot §5 "Whether the cite checker joins the gate as a drift speedbump" | ✓ |
| sizes vs landing charter §4 | charter §4: `L1 ≈ ½ day; L2 ≈ 1 day; L3 ≈ ½–1 day; L4 ≈ ½–1 day; L5 ≈ 2–3 days; L6 ≈ 1 day. About a week to v1 with E6 in`; plan: V1-1 1–2 (t1 + t4–t6), V1-2 ½–1, V1-3 ½, V1-4 ≈ ½ each, V1-5 1–2, V1-6 ≈ 1 → "about a week and a half" without E6 | ≈ consistent; labelled "measured velocity"/"Estimate" ✓; F19 on the hour claim |
| V2-3 unlock: "arbitrary tag environments need `Acyclic`/`AcyclicPair`" (risk map §3) | risk map §6: "Arbitrary tag environments require `Acyclic` or `AcyclicPair` when using the six conditional sufficiency theorems" | ✓ |
| V2-7 C21 `ProcSpecT.forget` needs table-equality or Θ-monotonicity | KOI C21 as quoted | ✓ |
| V2-8 masks Lane C §2.4 sized | `:322 ### 2.4 The minimal generalisation, sized (for when it comes)` | ✓ |
| §7.5 E5 §S2.5 (B18) open since 2026-09-05 | KOI B18: "ACCEPTED as an INERT limitation ([USER 2026-09-07], the landing charter's R3 …)"; status snapshot §5 lists it as open on 09-05 | ✗ stale: B18 records R3 as ACCEPTED on 2026-09-07 (the DECISIONS R3 quote); the plan lists it as still open |

### A.6 REG §1 — what landed on `mdd/cerberus-lean`

| claim | measurement | verdict |
|---|---|---|
| mainline at `94f339eb4`; 30 commits `89f7e68..94f339eb4` | `git rev-parse --short=9 mdd/cerberus-lean` → `94f339eb4`; `rev-list --count 89f7e68..mdd/cerberus-lean` → 30; 89f7e68 is an ancestor | ✓ |
| no change under `lean_frontend/generated`, seams, `.lem` except the probe fixture | `diff --name-only` filtered to `^lean_frontend/[^/]+\.lean$ \| generated/ \| native/ \| ^frontend/ \| ^backend/ \| \.lem$ \| manifest \| lakefile \| ocaml_frontend/` → only `tests/failure-probes/discarded_failures.lem` | ✓ (F16 on "only Lean additions") |
| validation foundations, `NO_COLOR=1`/`TERM=dumb`, Tier A 13 gates | `NO_COLOR=1` in `scripts/common.sh`, `observations.py`, `test_observations.py`; docs `2026-09-06_validation-foundations-*.md`, `2026-09-06_supported-profile.md` exist; LADDER Tier A rows 1–11 | ≈ (F17) |
| csmith sweep after P0, 6 shards, `mismatch=0` everywhere, two MATCH → TIMEOUT at 15 s | `2026-09-06_csmith-sweep-post-p0.md`: shards 1/6–6/6 each `mismatch=0`; `REGRESSION: sa_csmith_369.c baseline=MATCH current=TIMEOUT`, `… 371.c …`, `TIMEOUT_SECS=15`; "At `TIMEOUT_SECS=90` both MATCH" | ✓ |
| risk-map baseline with orchestrator's review §8; §6 = our consumer surface; ten change manifests since anchor B adopted | `2026-09-07_risk-map-baseline.md:732 ## 6. Consumer surface`, `:742 All ten change manifests newly added since B lie at or before the consumer's current provider pin`, `:792 ## 8. Orchestrator review of this record` | ✓ |
| pure-failure: 231 sites, `Outcome` type, strict twin, connection theorem; PARKED "0 discardable sites; option C; flip conditions" | `94f339eb4 docs: pure-failure correspondence design → PARKED with the reachability census outcome (0 discardable sites; option C; flip conditions)`; census `# Pure-failure reachability census (the 231 pure sites of the execution closure)` | ✓ |
| fuel-measure-cost charter on `arc/fuel-measure-cost`; monotonicity rejected with the quoted reasoning | branch `cee6b4639 2026-09-07 charter: Codex fuel-measure-cost …` exists; the reasoning is in the pure-failure design (F8) | ≈/✗ |
| `feature/concurrency` S0–S7, 13 beyond mainline | `086d8762d`, `rev-list --count mdd/cerberus-lean..feature/concurrency` → 13 (45 behind) | ✓ |
| its diff does not touch the four generated driver files | VACUOUS (F1) | ✗ |

### A.7 REG §2 — provider statements vs risk-map §6

All six rows are faithful paraphrases; the two quoted fragments are verbatim:
`native fail-stop and in-process default denotation are not yet connected by
a faithful outcome theorem` (§6, first bullet) and `General absorbing
propagation/monotonicity is not among the delivered conclusions` (fourth
bullet). Row 3 (`Acyclic`/`AcyclicPair`, "six conditional sufficiency
theorems") ✓; row 4 (Z2 narrowing: positive alignment, nonnegative size,
requested-address create has no rule) ✓; row 6 ("master plan steps 2–3 and
step 5"; "KNOWN-OPEN-ITEMS A7") ✓. Note §6 also says the 117 figure "is its
own dated census, not a count certified by this audit" — consistent with F4.

### A.8 REG §3 — the requests

| id | claim | measurement | verdict |
|---|---|---|---|
| R-1 | FILED `docs/2026-09-02_request-…fuel-exhaustion-outcome.md` → ANSWERED by `CerbND.fuelExhaustedKill = Error0 fuelExhaustedLoc fuelExhaustedMsg`, distinguishable from `Undef0` | file exists (asks for "A distinguished outcome for fuel exhaustion in the nondeterminism …"); `.cerberus-ws/lean_frontend/CerbND.lean:98 def fuelExhaustedKill {err : Type} : kill_reason err := Error0 CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg` — a `kill_reason` constructor distinct from `Undef0` | ✓ |
| R-2 | 117 arms; census; PARKED with flip conditions | 119 (F4); PARKED ✓ | ≈ |
| R-3 | NONE; kill-adequacy note §5 | note §5 "Nothing on the critical path" | ✓ |
| R-4 | OPEN; G2 reads emitted text with a script | G2 reads the pinned LEAN frontend's in-memory `file` from the OCaml oracle's `--cabs-json` (landability §4.1), not the `.annot.core` text; the corpus D6 check reads the OCaml text. Two pipelines — the note should ask which is "the pipeline" (Part B) | ≈ |
| R-5 | `hQd` 2 sites; FILED note "no action requested" | `(hQd :` ProdLoop.lean:380, :451; note line 22 "No action requested." | ✓ |
| R-6 | FILED conv-int note, "not a request" | header: "Not a request; a latent-divergence note for your register." | ✓ |
| R-7 | `pp_core.ml` never prints `Aexpr, Astmt, Alabel, Acerb, Ainlined_label, Auid, Aattrs, Avalue`; C20 | KOI C20 lists exactly these; `pp_core.ml:577 \| Aattrs (Attrs attrs) -> :578 if Cerb_debug.get_debug_level () > 3 then` | ✓ (Aattrs printed at debug > 3 — REG F-1 says so) |
| R-8 | A3 DEFERRED upstream | KOI A3 "ISO-fix register R4 DEFERRED upstream" | ✓ |
| R-9 | every export runs `drive fmapEmpty false …` one thread; concurrency merge = re-pin scout | statements ✓; F1 makes this MORE than an expectation | ✓ |
| R-10 | S5 lemma accepted "not discharged"; FILED via S1 response; status not visible on mainline | `2026-09-04_response-concurrency-S1-interface-review.md:16` "PLUS the one-tree agreement lemma (Q4, please prove it …)"; F9 | ≈/✗ |
| R-11 | ~90 s wall for 56 modules | DECISIONS 3603 `19:07:25–19:08:55 UTC, 56 modules recompiled` | ✓ |

### A.9 REG §4 — the F-items' "what exists at the pin"

| id | cell | measurement | verdict |
|---|---|---|---|
| F-1 | `Aattrs` printed only at debug > 3 | `pp_core.ml:577–578` as above | ✓ |
| F-2 | `Eccall` not covered by the mirror | manifest OUT-OF-SCOPE / KOI B8 | ✓ |
| F-3 | 60 of 117 in `CerbMem.lean`; "defacto model unreachable from drive (F-C2-4)"; byte contracts on small-items | `CerbMem.lean 60` ✓ (of 119); `TODO.md:56 - **The defacto memory model is unreachable from drive (F-C2-4)**`; `## Small items` … `Byte representation and printer producer contracts (M)` | ✓ (117→119) |
| F-4 | UB list in the generated AST; kills classified by `EvalFail` | `EvalClass.lean` module; design note §4 ".undef loc ubs" | ✓ (not re-measured beyond names) |
| F-5 | `impl0 = ∅` in our file | ✓ |
| F-6 | PARKED (0 discardable) | ✓ |
| F-8 | S0–S7 unmerged | ✓ |
| F-9 | fuel-measure-cost charter; F-C3-4 | `TODO.md:96 Performance backlog: the eager lemSize measure of get_ctx (F-C3-4 …` | ✓ |
| F-10 | `decide +kernel` does not reduce the driver (E3 notes) | KOI B16 "kernel reduction of the prefix measured not to reduce" | ✓ |

### A.10 Quotes presented as verbatim [USER] rulings

| quote (as in the documents) | in DECISIONS.md? | verdict |
|---|---|---|
| §0 "The done state … is that our logic (1) … good and complete" | NO (0 hits on three distinct substrings) | ✗ unregistered |
| "The demo should be the best possible version of Reynolds/O'Hearn … Fancy logic features aren't needed for that purpose" | 2130–2133 verbatim, elided middle ("just because it's a nice stable interface but it shakes out many of the theory difficulties.") | ✓ |
| "a logic over Core emitted as an output from C code. Authored-core is just a confection" | 2384–2385 verbatim (source continues "which we do to make the build possible …") | ✓ |
| R5 "stays as residual until we've finished the scheduler completely" | 3003 verbatim substring | ✓ (the framing around it is not — F3) |
| R7 "keep them for now" | 3002 | ✓ |
| R3 "R3 - okay so this is a limitation we will have to lift later, but here is inert? Sure that's fine" (KOI B18, cited by the plan) | 2999–3000 | ✓ |
| [USER 2026-09-03] "no magic values" | 1795 ("all such magic values deleted and replaced with positions that can be quantified over") — the phrase "no magic values" is the register's label; the plan's use is as a label | ✓ |
| §8 / REG §6 request quotes | NO | ✗ unregistered |
| "v1a", "emitted Core, call-free programs" attributed to R5 | NO in DECISIONS; landing charter [AGENT] bracket | ✗ misattributed |
| "One change at a time ([USER 2026-09-04])" | 349, dated 2026-09-02 | ≈ |

## Part B — credibility, as a PL referee

**B1. The §0 grading.**

*(1) "recognisably Reynolds/O'Hearn — MET for the covered fragment."*
Overstated in one respect and correctly hedged in others. What a separation-
logic referee finds present and proved against the engine: the small axioms
in classical shape (C10), a frame rule on the judgment (`wps_frame`,
Wps.lean:697) and frame across back edges/calls (`wps_frame_labels`),
consequence (`wps_wand`, `wpt_mono_k`), sequencing at the binder shapes,
conditionals, loops through the label context with a decreasing variant in
the total judgment, Hoare's rule for (mutually) recursive procedures with a
specification table (`procSpecs_intro`), a partial/total pair with the
refinement `wps_of_wpt`, adequacy through Iris (`wp_strong_adequacy_gen`) and
a negative result (C5). That is a real, if small, separation logic. What is
missing that the referee will name:
- **Procedure specifications with logical (auxiliary) variables.** `ProcSpec
  GF := sym → List value → IProp GF × (value → IProp GF)` (Wps.lean:130):
  pre and post share only the argument values; `reverse(p)` with
  `list p xs` / `list ret (rev xs)` is not statable (Lane C §1.4). For a
  Reynolds/O'Hearn logic *with procedures* this is not a "fancy feature"; it
  is the 1970s Hoare-logic ingredient. The plan grades (1) MET and defers this
  to V2-2 "the RefinedC arc". Recommend: grade (1) "MET for statements and
  loops; procedures MET at value-indexed specs only (G1.2)", and consider
  pulling V2-2 option (i) into V1 — it is a judgment-text change on
  `wps_call`/`procSpecs_intro`/`wpt` twins with `emptyProcSpec` surviving at
  `A := Unit`, and the two exhibits already carry integer-indexed specs.
- **Conjunction rule / disjunction, existential introduction at the
  judgment.** Implicit through Iris's BI (`∃`, `∨` in `Ψ`) — fine, but say so
  in one line; a referee looks for the rule table (API.lean's header) and
  finds no conjunction row. Not a gap, a doc item for V1-6.
- **A `while` rule.** G1.7's answer is right (Core is label-based); the
  reviewer-facing fix is a derived rule, stated once as a lemma over the
  emitted `while` shape (t4's `save/run` idiom), not only prose.
- **Soundness in one place.** `wps_sound`/`wpt_sound` collapse into iris-
  lean's WP, but ARCHITECTURE §2.1 states "No shipped-driver statement
  consumes any of them: the driver lanes (§2.4) run their own inductions."
  Two adequacy routes to the engine (Iris adequacy for the seeded exhibits;
  `wpt_driver_done_alloc`'s own induction for the production lane) is a
  design smell a referee asks about: why is the load-bearing lane not a
  corollary of the collapse plus Iris adequacy? Either connect them (a
  theorem that the driver lane is derivable from `wpt_sound` +
  `wp_strong_adequacy_gen`) or state in ARCHITECTURE why the production
  lane must bypass Iris (the singleton-equation shape, B5). V1-6 should carry
  this as a named question for the fresh ARCHITECTURE reviewer.
- **Statement-level artefacts.** Every root-of-trust statement carries a
  numeral fuel floor (`hfuel : 50/917/90/80 ≤ LemFuel.fuel`) and, for
  t4/t5/t6, `hsup : 600 ≤ sup`; plus `htd : … = fmapEmpty` (37 sites) and
  `hex : … = fmapEmpty` (38). The plan treats only `600` (G1.1). The fuel
  floors are principled (FUEL.md §3: "the certified round count plus two") but
  they are hand-derived numerals in statements — the [USER 2026-09-03] ruling
  is that bounds not forced by OCaml/ISO are quantified or derived, and a
  referee will ask why `917` is not `t4Cost + 2` by `rfl`. Add to G1.1's
  scope or state the exemption.

*(2) "a real, faithful, extensible iris layer — MET as a layer."* Genuinely
Iris: iris-lean `34390a01` (2026-08-20) pinned in `lakefile.toml`; `Language
CoreRt Mem Empty CoreRVal` (Lang.lean:58); `IrisGS_gen` with `stateInterp`
over the engine's `Mem`, ghost heap `CohG`, `budgetAuth`, later credits,
fancy updates, guarded fixpoint (`fixpoint (wps.pre …)`, contractive
instance proved), `wp_strong_adequacy_gen` used. The judgments are NOT
iris-lean's `wp` (they re-state its step clause; F21) — write "the same
construction as iris-lean's `wp`, collapsing into it" rather than "over
iris-lean's WP". "Extensible" is an untested claim until the extraction
(Lane C §6.5 estimates 2–4 worker-days; every pin re-baselined by name); the
plan grades it "NOT yet extracted" — honest.

*(3) "built on cerberus-lean — MET."* Measured: all thirteen
`*_certified_production` statements plus `exhibitA_prod` mention no `Step`,
`Frag`, `CerberusRound`, `DriverDone*`, `DriverSafe*` — the mirror and the
collapse are proof devices only. They do mention the package's `prodFileLib
stdlibE3 [] tMain` — a package-built FILE, which the plan correctly files
under (4)/A7. The G2 successor statement quantifies `cmp :
EmittedFile.Comparators` under three `Bool` checks and drives `restoredFile
cmp`; the meaning "for the ACTUAL comparators" is `certified_production_of_
capture_eq`. Fine, but §1.4 should say that after V1-1 the referent's file is
a data term plus a check, not `drive`'s input as the pipeline computes it.

*(4) "genuine pipeline outputs — HALF MET; V1-1 closes the file gap."* The
characterisation of A7 is right (the three-function `stdlibE3`, `impl0 = ∅`,
the wrap-vs-kill divergence). V1-1 does NOT close it in the sense §0 writes:
G2 delivers a script-produced data term (`EmittedT1Data.lean`, 42 841 lines,
quoted by a hand-written `ToExpr` deriver from the pinned LEAN frontend's
in-memory `file`, itself built from the OCaml oracle's `--cabs-json`),
equal to the pipeline's file by an EXECUTABLE round-trip that is not in the
gate yet. That is exactly the [USER 2026-09-04 Q3] option (b) "mechanised
over the whole file" (landability §4.1); option (a) — the elaborator in the
statement — "remains the named target, not done" (DECISIONS 2476; landing
charter R4). After V1-1, criterion (4) is met modulo two new trusted
components (`derive_file_to_expr.lean`, `emitted_frontend.lean`) that
appear nowhere in the plan's trust base (§1.6). Also: "the pipeline" is two
things in these documents — the OCaml Cerberus that emitted
`docs/corpus-e0/*.annot.core` (checked by D6) and the pinned Lean frontend
that produced the quoted `file` (checked by G2's round-trip). A referee asks
which Cerberus the theorem is about. R-4 should ask the provider that
question in those words.

**B2. Gaps the plan omits that a referee would name.**
(i) numeral fuel floors in root-of-trust statements (above); (ii) the
`hex`/extern premise (38 sites) — every proved configuration has an empty
extern map, while G2's statement already switches to `runtimeExtern`; say
which shape V1-1 lands; (iii) the trusted quoter/loader (above); (iv) the
`Comparators` quantification and what `EmittedFile.Data` omits (comparator
closures) — a reader must be told why a `file` cannot be quoted whole; (v)
the fragment boundary as numbers: 24 NO-RULE + 7 OUT-OF-SCOPE of 78 engine-
success variants — 40 % of the classified surface has no rule; the plan's
G1.5 says "fifteen"; (vi) the sequential-only driver (`drive fmapEmpty false
…`, one thread) is stated in REG R-9 but not in the plan's §5 "not in
finished" list as a property of every export; (vii) `deliveryCost`/`k + 2`
slack (B6) — disclosed, fine; (viii) `panic!` arms: the plan says "none
reaches an arm — provider census"; the provider census is about pure
`failwith` sites (231), not `panic!` arms; the claim that no covered program
reaches a `panic!` arm is the RULES' premises (ARCHITECTURE §3), not a census
— reword; (ix) the E5 §S2.5 decision listed as open (§7.5) was recorded as
ACCEPTED on 2026-09-07 (KOI B18) — stale; (x) `origin/main` is 107 commits
behind local main — not a logic gap, but a "state of the union" that omits
the unpushed state omits a fact the operator needs.

**B3. The V1/V2 split against the rulings.** "Authored-core is just a
confection" is satisfied by call-free EMITTED Core — the confection ruling is
about authored vs emitted, and V1's programs are emitted. R5 is the problem:
the recorded disposition is "the v1 tag waits for E6 proper (L5)"; the plan
proposes to change that and presents the change as R5's own alternative
(F3). On the merits: a C demo in which every program with a function call is
excluded is an INTERIM milestone, not "finished" for a logic whose
definition of done says the programs are "genuine outputs of the Cerberus-
pipeline" — four of ten corpus programs, none with a call. It is a retreat
relative to the recorded plan (landing charter L5 "E6 proper … Acceptance:
t2/t3/t10 certified"), defensible only if named as such: tag it "v1a —
emitted Core, call-free" and keep "v1 = with E6" as the definition of done.
The plan's §4 sentence "V1 = the definition of done for the CALL-FREE
emitted-Core demo" redefines done; strike it.

**B4. Sizes and sequence.** Plausible against the record's velocity for
V1-1..V1-4 (four landings on 2026-09-07 alone; the refinement slice's two
theorems in seven minutes between snapshots). V1-5 at "M, 1–2 days" is
optimistic: option A is a NEW judgment with its own structural rules for
every construct on the overflow path (the E3 integer faces, `bound`,
`unseq`, binders), a new `DriverKilledAt` and an adequacy dual — the design
note itself lists "its own structural rules for the constructs on the path to
a kill". Rate it M–L with an explicit stop-and-report. The serialisation
constraint is correctly derived from rules 2/8 (A.5) and is the plan's real
critical path: three serialised Codex slices each needing charter + review +
audit + merge ask means ~10 operator sign-offs in "a week and a half".

**B5. Completeness of the companion for a RefinedC-family layer.** F-1..F-10
cover attributes, calls/function pointers, layout/provenance/UB in the memory
seam, the UB catalogue, the impl map, typed failures, dialect stability,
concurrency, performance, kernel runs. Against what the donor actually needs
(`theories/caesium/{layout,loc,heap,val,int_type,struct,bitfield,byte}.v`;
`typing/{function,globals,intptr,tagged_ptr,malloc,union,padded}.v`), add:
- **Globals and initialisers.** Every current and G2 statement has `globs =
  []` ("Empty globals, empty tags and parameterless main remain explicit
  restrictions", a7-t1-production.md); `driver_globals` reads each global
  through the (D) row `to_pure` (FUEL.md §4). RefinedC's `globals.v` and
  every real C file need them. This is a demo-side V2 item AND a provider
  need (an absorbing or measured `to_pure` on the globals path).
- **Pointer↔integer casts and provenance (`intptr.v`, `tagged_ptr.v`).**
  F-3 says "provenance" once; Caesium's `loc = alloc_id × addr` with
  `alloc_id_alive`/`block_alive` is the model RefinedC's types are stated
  over. Ask which Cerberus memory model (concrete vs PNVI-ae) is the
  semantics of record for casts, and whether `CerbMem`'s provenance is
  observable through `PtrEq`/`intFromPtr`.
- **The `Impl` call row.** With the whole std.core and impl map linked
  (V1-1), `Eproc _ (Impl _) _` (manifest OUT-OF-SCOPE) becomes live on
  every integer conversion; the layer needs it as a rule or a proven
  unfolding. Demo-side, but the provider should confirm the impl map's
  stability across pins (F-5 partially).
- **Two pipelines, one referent (R-4).** Ask explicitly whether the OCaml
  `.core` printer output and the Lean frontend's in-memory `file` are
  promised equal (structurally, up to symbol digests), and which is "the
  pipeline".
- **Locations in kills.** The kill-adequacy design's (c1)/(c2) needs the
  engine's `loc` in `Undef0 loc ubs` to be stable and documented (F-4 partly).
Strike or demote: R-3 and R-11 are not needs (the register says so; keep them
as one line each). F-10 "not requested" is right — a refutation lane through
`wpu` is the better route.

## Omitted-branches list

None: every branch not merged into `main` (14 refs, two of them the same
commit `a41292d`, one of them this document's own `docs/master-plan`) appears
in §2. Not a branch, but omitted state: `origin/main` = `04059dc`, 107
commits behind local `main`.

## Grade: C+

The measurements are largely right and the sequence is sound, but the
document misstates the provenance of its own anchor (the definition of done
is not in the register), misattributes its central boundary decision to a
ruling whose recorded disposition says the opposite, inherits a false
`panic!` census while calling it a boundary, and its companion's key
reassurance about the concurrency branch is a vacuous measurement. With the
seventeen fixes applied it is a B: an honest state-of-the-union with a
defensible interim plan.

## Revision 2 verification (2026-09-07)

Fresh pass [AGENT, same reviewer, read-only] over branch `docs/master-plan` @
`1595c3e` (= `a446672` + one commit touching `ARCHITECTURE.md`, `README.md`,
both plan documents, `docs/DECISIONS.md` (+65), `docs/KNOWN-OPEN-ITEMS.md`,
and adding this report — `git show HEAD:docs/2026-09-07_review-demo-master-plan.md
| md5sum` = the working file's `984b8d69b087195f5fceaec48f4c9c28`, i.e. my
earlier sections were committed unchanged). Nothing was committed or modified
by me except this appended section; the one command run outside this
worktree was the read-only `scripts/setup-cerberus-dep.sh --check` in the
primary checkout (its `--check` path only runs `check_lem_sync.sh --check-lean`
and `cmp`; the priming/`--record-lean` writes are behind `check_only == 0`).

### Revised verdict: CREDIBLE WITH FIXES (minor residues) — grade B

All seventeen fixes and every Part B recommendation are applied in
substance; the plan now states its own provenance correctly, presents the
boundary decision as a proposal against the recorded disposition, and the
companion's concurrency paragraph is a true measurement. Five residues, all
textual, two of them on shop-window surfaces: (R1) ARCHITECTURE §3 now
contradicts itself ("119 … in nine files — [nine files summing to 117] …
CORRECTED … to 119 in TEN seams"); (R2) KOI A5's disposition cell still says
"(117)"; (R3) the plan calls G2's `frontendSupply` "program-derived" twice —
it is `def frontendSupply : Nat := 36` (a captured literal checked by the
round-trip), exactly the shape G1.1 criticises; (R4) the DECISIONS entry
claims a FULL gate at the landing but quotes fragments, not the verdict tail
(the record-gate-tails rule); (R5) two small imprecisions ("four landings on
2026-09-07" — five; a register gloss presented as the provider's words).
B+ once R1–R4 are fixed.

### (A) The seventeen fixes and Part B — applied / partial / missing

| fix | status | revised text (where it differs) and whether it matters |
|---|---|---|
| 1 provenance sentence; register the DoD | APPLIED | PLAN 17–20: "§0's definition of done and the request in §8 are the operator's words in the working session of 2026-09-07, registered in `docs/DECISIONS.md` in the commit that carries this revision (review fix 1); every other quoted ruling is verbatim from `docs/DECISIONS.md` with its date." DECISIONS: new entry `2026-09-07 [USER] THE MASTER PLAN, AND THE DEFINITION OF DONE FOR THE DEMO` (verbatim, the working session). Correct form |
| 2 R5 framing | APPLIED | PLAN §0 39–47 quotes R5 verbatim (matches DECISIONS 3002–3004), then "The RECORDED DISPOSITION of that ruling (DECISIONS, the same entry) is: 'the v1 tag waits for E6 proper (L5)'. The alternative 'v1a …' was the orchestrator's bracketed recommendation in the landing charter §1 R5, not a ruling. **This plan recommends changing the recorded disposition — §7.1 — and until that decision the definition of done includes E6.**" §4.1 title "PROPOSED boundary 'v1a'; recorded disposition: v1 waits for E6". §7.1 rewritten as "Ratify or reject". Exactly as asked |
| 3 REG concurrency | APPLIED | REG §1 last bullet: "`lean_frontend/generated/` is UNTRACKED in cerberus-lean … against the merge-base `31eba718e` the branch changes the `.lem` SOURCES … `driver.lem \| 708`, `core_run.lem \| 50`, `core_reduction.lem \| 141`, `core_run_aux.lem \| 211`, plus `cmm_csem.lem \| 45`, `cmm_op.lem \| 5`, `mini_pipeline.lem \| 2` (7 files, 966 insertions, 196 deletions; DERIVED). **Its merge is a FORCED re-pin for us, with a scout first** (R-9). (Revision 1 said the opposite on a vacuous measurement — review F1.)" Numbers match my measurement exactly |
| 4 panic 119/ten | PARTIAL | PLAN §1.4, G3.1; REG R-2, F-3; KOI A5 body; README: all 119/ten ✓. ARCHITECTURE §3 line 604 "119" and 614–616 "CORRECTED 2026-09-07 to 119 in TEN seams: `CerbFloat.lean:183` and `:307` are code arms the D-3 stripper missed" ✓ — but lines 606–609 still read "in nine files — `CerbMem.lean` 60, `CerbFS.lean` 36, `CerbDecode.lean` 7, `CerberusImpl.lean` 4, `CerbUtils.lean` 4, `CerbLocation.lean` 2, `Main.lean` 2, `CerbTags.lean` 1, `CoreParser.lean` 1" (sums to 117; no `CerbFloat.lean`); KOI A5's last cell still reads "Arm count re-measured at the re-pin (117); re-check `MemWF.killM`." Both matter: ARCHITECTURE is the reviewer-facing surface and now contradicts itself within one paragraph |
| 5 `600` = 18 sites | APPLIED | G1.1 "18 statement sites (15 `hsup : 600 ≤ …` premises — T4 10, T5 2, T6 3 — + 3 …)"; §2 park-D3 row "at `1e1f584` (14 = …); at `777ca0f` it is 15 + 3 (T4 has 10: `t4_wps_of_wpt` carries the premise)"; V1-4a "the 18 sites" |
| 6 G3 = 12 | APPLIED | §2 "14e7dc3..6c8e7e3, 12 commits: … changes `Step`/`wps`/`wpt`/`Soundness`/`DriverCollapse`" (matches the inclusive diff) |
| 7 option (b) sense; quoter as trusted component | APPLIED | §0 row (4) "V1-1 closes it in the [USER 2026-09-04 Q3] OPTION (b) sense …; option (a) … remains the named target"; G4.1 as asked; V1-1 acceptance "each `t*_certified_production` drives the data term of the pipeline's file"; §1.6 "the trust base gains two components … the quoter `scripts/derive_file_to_expr.lean` and the loader `scripts/emitted_frontend.lean` … checks, not proofs; they need a named place in ARCHITECTURE §3 and a mover" |
| 8 G1.5 = 24 | APPLIED | "24 NO-RULE + 7 OUT-OF-SCOPE variants (31 of 78) are stated absences"; §1.1 adds "31 of 78 classified variants (40 %) have no rule" |
| 9 cross-references | APPLIED | §1.2 "§7.2 below"; V1-5 "(§7.2; note §6 (a)–(e))", `wpu_certified_killed`; §1.2/§7.2 name branch `design/kill-adequacy` @ e87a97c; §2 "(five decisions, its §6)" |
| 10 REG monotonicity attribution | APPLIED (one gloss) | REG §1 pure-failure bullet: "That design's §4 is also where the provider states that fuel MONOTONICITY … is 'not statable for `drive`' while eight fuel rows exhaust into opaque sentinels — its shape must be fixed with the operator first." The quoted words are the design's (§4 rows 2–3); "its shape must be fixed with the operator first" is the register's own reading of the design being PARKED pending §8's operator decisions — not the provider's sentence. Low: mark it as [AGENT] reading |
| 11 R-10 | APPLIED | R-10 quotes the S1 response line 16, the mainline charter I3 and the branch S5 record §4 verbatim (all three verified) |
| 12 worktree row | APPLIED | §2 names both files with mtimes 00:05 / 00:07 "AND uncommitted edits `README.md \| 8 +`, `docs/DECISIONS.md \| 55 +` — a pending edit to the append-only register"; §7.5 |
| 13 §7.7 counts | APPLIED | §7.6 "25 fully-merged non-main branches (R7 counted eighteen on 2026-09-07 morning) and 4 worktrees … (`codex-charter-2`, `codex-refinement`, `demo-fuel-t1`, `land-repin`)" — matches my recount (40 refs, 26 ancestors incl. main) |
| 14 line counts, snapshots, date, paths | APPLIED | §1.1 "84 343 lines in 60 modules (79 560 at the top level + 4 783 under `Examples/`)", ListRevExhibit 1 985 inserted; §1.7 "63 `.txt` evidence files (54 signature snapshots, 9 axiom/census dumps)"; §0/§6 "[USER 2026-09-02] one change at a time"; `cerberus-heaplang/scripts/…` for the four scripts, `scripts/semantics-pin.env` at the root |
| 15 REG added files | APPLIED | REG §1 bullet 1 lists `FailureMain.lean`, `FailureReach.lean`, `discarded_failures.lem`, `failure_main.ml`, nine `reach/*.c`, `tests/provider-smoke/ProviderSmoke.lean` — the measured set |
| 16 the hour claim | APPLIED | §4 "the refinement slice's two theorems fell within a seven-minute snapshot span, under an hour from activation to record" — "under an hour" is now supportable from main's own timestamps (launch-incident entry `6df8982` 20:05 → T2 record `a994676` 20:36) |
| 17 §7.5 B18 | APPLIED | §7 "Not open (corrected from revision 1): E5 §S2.5's supply normalisation was ACCEPTED as an inert limitation by R3 on 2026-09-07 (KOI B18)." |
| B1 (1) | APPLIED | criterion row: "MET for statements and loops; procedures MET at value-indexed specifications only (no logical variables, G1.2); statement-level artefacts … (G1.1, G1.9)"; G1.2 raised to "V (the review would grade it toward D for 'complete')" with §7.4 proposing Lane C option (i) for Phase I; the conjunction/existential line (§1.2, V1-6); the derived `while` rule (G1.7 → V1-4c); the two adequacy routes as G2.4 + a named question for the fresh ARCHITECTURE review; the fuel floors as G1.9 + §7.8 |
| B1 (2) | APPLIED | "MET as a layer (the judgments are the same construction as iris-lean's `wp`, collapsing into it); 'extensible' UNTESTED until the extraction"; §1.2 cites `wps_sound` 4752 / `wpt_sound` 4520 / `wp_strong_adequacy_gen` (all verified in my first pass) |
| B1 (3) | APPLIED | "MET (measured: none of the 13 production statements mentions `Step`, `Frag`, `CerberusRound` or a `Driver*` device)"; §1.4 adds "After V1-1 the referent's FILE becomes a data term plus an executable check" |
| B1 (4) | APPLIED | option (b) sense; G4.3 "'The pipeline' is TWO things in this repository …"; R-4 asks the provider "(i) are the OCaml printer's Core and the Lean frontend's `file` promised structurally equal … and which is 'the pipeline' of record" |
| B2 (i)–(x) | APPLIED, (iv) partial | (i) G1.9 ✓; (ii) G1.4 "the empty extern map (38 sites) … answered by G2's `runtimeExtern` route at V1-1" — note `runtimeExtern` on `a41292d` is `Examples/EmittedT1.lean:86 def runtimeExtern : Fmap sym sym := symAdd mainSym mainSym fmapEmpty`, a hand-authored singleton proved equal to the file's actual extern map for t1 (`restoredFile_extern`) — fine for t1, say so; (iii) §1.6 ✓; (iv) §2/G4.1 say "comparators quantified under three finite `Bool` checks" but never say WHY a `file` cannot be quoted whole (its `Fmap`s carry comparator closures) — a referee will ask; one sentence missing; (v) §1.1/G1.5 "31 of 78 (40 %)" ✓; (vi) §1.4 "ONE thread", §5, V1-6 ✓; (viii) §1.4 "the covered programs avoid every arm by the RULES' premises … not by a census", G3.1 "(that census is about `failwith`, not `panic!`)" ✓; (ix) §7 ✓; (x) §1.1 row + §7.7 ✓ |
| B3 boundary framing | APPLIED | §4 "Phase I (proposed tag 'v1a') … Phase II … INCLUDING E6, which the recorded disposition places before the v1 tag. If the operator keeps the recorded disposition, 'finished' = Phase I + V2-4/V2-5 …"; the sentence "V1 = the definition of done for the CALL-FREE emitted-Core demo" is gone |
| B4 sizes / sign-offs | APPLIED | V1-5 "its OWN structural rules for every construct on the overflow path … \| M–L, own stop-and-report"; estimate "V1-5 1–3 (design first; M–L) … About two weeks to the 'v1a' tag"; §4 "each Codex slice costs the operator a charter review, a launch, a range audit and a merge sign-off — about ten sign-offs across Phase I" |
| B5 companion additions | APPLIED | F-6 globals/`to_pure` ("their fuel-parameter C2 follow-up" — verified: `TODO.md:43` sits under `## Fuel-parameter arc — C2 follow-ups`; `scripts/fuel_forms_pending.txt` has 2 `to_pure` rows); F-3 pointer↔integer casts, `loc = alloc_id × addr`, `intptr.v`/`tagged_ptr.v`, "which model (concrete vs PNVI-ae)"; F-5 the `Impl` call row becoming LIVE after V1-1; F-4 the kill location; R-4 the two-pipelines question; R-3/R-11 reduced to one line each; the donor file list quoted matches `deps/refinedc/theories/` |

### (B) The new claims of revision 2

| new claim | measurement | verdict |
|---|---|---|
| DECISIONS: the [USER] definition-of-done ruling and the three requests, "verbatim, the working session" | I have no access to the session; internal consistency only: the plan's §0 quote is the entry's text with ", as you say" elided by the ellipsis ("The done state, as you say is that our logic (1) …"); §8's request quote is the entry's second sentence group with honest ellipses ("Yes, can you collect all this into a single 'master plan' doc. You can spend significant effort making sure we have a register …"); REG §6's quote and the "send a fable-class agent …" quote match the entry character for character | ✓ consistent (unverifiable against the source) |
| DECISIONS: the entry's account of what changed, (i)–(vi) | (i) registration ✓; (ii) R5 disposition ✓; (iii) "rewrites `driver.lem` (708 lines) and three sibling `.lem` sources" — `driver.lem \| 708` and `core_run`/`core_reduction`/`core_run_aux` in `frontend/model/` ✓ (plus `cmm_csem`, `cmm_op`, `mini_pipeline` outside that directory); (iv)–(vi) ✓ against the revised text | ✓ |
| DECISIONS: `2026-09-07 [USER] TWO MERGES` "main 6df8982 → 7698a71 … → 777ca0f" | `git log --oneline 6df8982..777ca0f` = 7 commits: the four Codex T1/T2 commits, `ed82837`, `7698a71` (= `codex/total-refines-partial`), `777ca0f` (= `hygiene/agents-md`) | ✓ |
| ERRATUM 119 in ten seams, "two independent verifications … the orchestrator's independent string-aware lexer" | My stripper re-run on the PRIMARY checkout's `.cerberus-ws` (a second workspace, manifest seams only): `CerbMem.lean 60, CerbFS.lean 36, CerbDecode.lean 7, CerberusImpl.lean 4, CerbUtils.lean 4, CerbFloat.lean 2, CerbLocation.lean 2, Main.lean 2, CerbTags.lean 1, CoreParser.lean 1 \| TOTAL 119 \| seams with arms 10` — identical to the coordinator's per-file list. The orchestrator's lexer itself is not in the tree; its result is recorded, not its code | ✓ (KOI A5 body; residues R1/R2 above) |
| KOI §E / PLAN §1.6 / DECISIONS: the primary's `.cerberus-ws` had drifted to `f95ef8d9c` with a `.lake` from 2026-09-02; `--check` reported it (exit 1); re-primed from `worktrees/codex-refinement`; re-verified | Current state, measured in the primary: `git -C .cerberus-ws rev-parse HEAD` → `89f7e688530c6910884518811d645e4e892e4507`; manifest entries 37; `scripts/setup-cerberus-dep.sh --check` (verbatim): `== setup-cerberus-dep: A ok: workspace at pinned commit` / `== setup-cerberus-dep: B ok: primed (89f7e688530c6910884518811d645e4e892e4507 2026-09-07T02:06:21Z)` / `check_lem_sync: lean OK (src 977326511c…, gen 11c6b37a5d…)` / `== setup-cerberus-dep: B ok: Lean lem-sync stamp verified in the workspace` / `== setup-cerberus-dep: C ok: 37 hand-written seams byte-identical to the pin` / `== setup-cerberus-dep: DONE …`; `CHECK-EXIT=0`. The `.primed-from` stamp `2026-09-07T02:06:21Z` is byte-identical to `worktrees/codex-refinement/.cerberus-ws/.primed-from`, consistent with a wholesale copy from that worktree; `cerberus-heaplang/.lake` in the primary is dated `2026-09-07 21:21:47` (a build at the landing). The historical drift (`f95ef8d9c`, the `.lake` date, the exit-1 transcript) cannot be re-observed; `.cerberus-ws/lean_frontend/.lake` now shows `2026-08-20` (`cp -a` preserves mtimes) | ✓ current state; historical claim unverifiable, plausible |
| DECISIONS: "FULL gate `EXIT=0`, `export pins: 906 trio-exact`, 0 modules rebuilt, `ALL GATES GREEN`" at this landing | Only fragments are quoted; no verbatim verdict tail for this gate appears in DECISIONS or in any record of the commit (the rule "gate tails verbatim in `DECISIONS.md`" is the plan's own §6). The `.lake` mtime supports that a build ran | ≈ record gap (R4) |
| PLAN §1.1 unpushed row: local `main` 107 ahead of `origin/main` (`04059dc`) | `git rev-list --count 04059dc..main` → 107; `origin/main` is an ancestor | ✓ |
| PLAN §2 G2 row: data term `Examples/EmittedT1Data.lean` (42 841 lines), quoter `derive_file_to_expr.lean`, loader `emitted_frontend.lean`, round-trip, "the statement drives `restoredFile cmp` under quantified comparators and three finite `Bool` checks, at a program-derived `frontendSupply`" | data term / quoter / loader / comparators / checks ✓ (`a41292d:EmittedT1Exhibit.lean:605–617`). `frontendSupply`: `a41292d:Examples/EmittedT1Data.lean:7 def frontendSupply : Nat := 36` — a LITERAL captured from the frontend run and compared by the round-trip's supply check, not derived from the program term | ✗ "program-derived" (R3) |
| PLAN G1.1: "G2's `frontendSupply` shows the program-derived form" | same measurement | ✗ (R3) — it shows the captured-literal form, the very shape G1.1 objects to |
| PLAN G1.9: fuel floors `50/917/90/80` | `t1_certified_production (hfuel : 50 ≤ …)`, `t4 … 917`, `t5 … 90`, `t6 … 80` (first pass) | ✓ |
| PLAN §4: "four landings on 2026-09-07 alone" | main's log for 2026-09-07 shows five landings (L1 01:50, L2 04:01, D5 06:28, stage-2 19:34, refinement 21:21) plus the AGENTS.md merge | ≈ undercount; harmless |
| PLAN §1.2 "`wpt_driver_aux`" as the production lane's own induction | `ProdLoop.lean:191 theorem wpt_driver_aux` | ✓ |
| PLAN §1.5 t8 row: "the dialect design §C.8 says arrays are 'not an E slice'" | `2026-09-04_emitted-core-dialect-design.md:882 ### C.8 — Not an E slice: tagDefs (t7) and arrays (t8)` | ✓ |
| REG §1 corrected concurrency paragraph; R-4/R-9/R-10 rewrites | numbers and quotations verified (A above) | ✓ |
| REG §1: "(Tier A, 11 rows in `scripts/LADDER.md`)"; "(both MATCH at 90 s)" | LADDER Tier A rows 1–11; csmith record line 46 "At `TIMEOUT_SECS=90` both MATCH the oracle" | ✓ |
| REG F-6 (globals, `to_pure`) and F-5 (`Impl` call row) | `TODO.md:43` under C2 follow-ups; `fuel_forms_pending.txt` 2 `to_pure` rows; FUEL.md §4 `to_pure` (D) row; manifest OUT-OF-SCOPE row `Frag.call \| Eproc _ (Impl _) _` | ✓ |
| REG §1 "our 117 `panic!` figure 'is its own dated census, not a count certified by this audit'" | risk-map §6 bullet 1, verbatim | ✓ |

### (C) Worse than revision 1?

Nothing lost its measurement, and no correction over-shot except one: (R3)
`frontendSupply` is presented twice as the exemplar of the program-derived
supply bound while it is a captured numeral (`:= 36`) — the plan adopted the
reviewer's vocabulary without checking the definition. New inconsistencies
introduced by the half-applied erratum: (R1) ARCHITECTURE §3's paragraph now
asserts 119 and lists nine files summing to 117 in the same sentence; (R2)
KOI A5 body says 119/ten while its disposition cell says "(117)". New record
gap: (R4) the landing's FULL gate is asserted in DECISIONS without its
verbatim verdict lines. Minor: (R5) "four landings" (five); REG §1's "its
shape must be fixed with the operator first" is the register's gloss on a
PARKED design, presented inside the provider's statement.

Exact fixes for revision 3: ARCHITECTURE.md:606–609 → "in ten files —
`CerbMem.lean` 60, `CerbFS.lean` 36, `CerbDecode.lean` 7, `CerberusImpl.lean`
4, `CerbUtils.lean` 4, `CerbFloat.lean` 2, `CerbLocation.lean` 2, `Main.lean`
2, `CerbTags.lean` 1, `CoreParser.lean` 1"; KOI A5 last cell "(117)" →
"(119, erratum 2026-09-07)"; PLAN §2 G2 row "at a program-derived
`frontendSupply`" → "at the captured supply `frontendSupply := 36`
(`Examples/EmittedT1Data.lean:7`), equal to the frontend's by the round-trip
check"; G1.1 "G2's `frontendSupply` shows the program-derived form" → "G2's
`frontendSupply` is a captured numeral, the same class — V1-1 should state
it as a derived bound or exempt it with G1.9"; DECISIONS: quote the landing
gate's verdict lines verbatim or state that no gate was run for a docs-only
landing; §4 "four landings" → "five"; REG §1 mark the operator clause as
[AGENT].

Revised grade: **B** (B+ with R1–R4 fixed). The document is now an honest
state-of-the-union with its provenance in order; what remains is copy-editing
on two shop-window surfaces and one record-integrity habit.
