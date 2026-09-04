# ARCHITECTURE.md rewrite — the record (2026-09-04)

Author: the rewrite worker (fresh author; not the reviewer of
`2026-09-04_architecture-review-3.md`). Branch `hygiene-h1`, worktree
`worktrees/hygiene-h1`, base `b8413a5` (= main `e242342` + H1a/H1b).
Scope: DOCS ONLY — `ARCHITECTURE.md`, the new archive record, this
record, one sentence of `WALKTHROUGH.md`. No `.lean`, no script, no
`docs/DECISIONS.md`, no `docs/KNOWN-OPEN-ITEMS.md` change; no `lake`/`lean`
invocation (the orchestrator's gate runs in this worktree); every claim
was verified by READING the sources at `b8413a5` and the pinned
workspace at `f95ef8d9c`. No Lean gate is required for these commits.

Commits: (1) `240d640` the review copied verbatim (`cmp`-identical to
`worktrees/review-arch/cerberus-heaplang/docs/2026-09-04_architecture-review-3.md`);
(2) `cd05543` the archive record + the rewritten ARCHITECTURE + the WALKTHROUGH
sentence; (3) this record.

Result: ARCHITECTURE.md 686 lines / 5882 words → 734 lines / 5873 words
(DERIVED, `wc`). See "Deviations" (2) for why the line count did not fall
to the brief's expected third-to-half: about 250 lines of arc narrative
left the document and about 260 lines of REQUIRED new content entered
it (glossary, two verbatim theorem readings, the premise list, the
enumerated NO-RULE variants, the closed-statement table, the ruled
reading, the negative result).

## 1. Finding-by-finding disposition

| Review id | What was done | Where (rewritten ARCHITECTURE) |
|---|---|---|
| T-1 (15 NO-RULE listed as 12) | All fifteen enumerated by constructor, read off the manifest's NO-RULE rows (3 store, 3 load, 3 create, 4 kill, 1 alloc, 1 memop_vals = 15) | §6 "The fifteen NO-RULE variants" |
| T-2 ("metatheorems no export consumes" false) | Consumers named: `wps_sound` — CallSmoke:330, FibRecExhibit:648, EvenOddExhibit:501; `wps_sound_empty` — Exhibit, StructExhibit, CaseExhibit, LoopExhibit, FibExhibit, ArrayExhibit; `wpt_sound` — the pinned `cs_twp_readout` (CallSmoke:455, at :461). The true statement: no SHIPPED-DRIVER statement consumes them. The same false sentence in WALKTHROUGH (line ~833) corrected | §2.1 last paragraph; WALKTHROUGH §3.3 |
| T-3 (stale `CerbMem.lean:1619`) | The region-rule fact restated with `isAtomicMemberAccess` at generated `CerbMem.lean:1949` (definition), `:2003`/`:2067` (the `loadM`/`storeM` checks) — verified by grep at the pin | §2.1 |
| T-4 (package definitions in root-of-trust statements; `hcost` undisclosed) | A table of the nine statements with EVERY input-dependent premise incl. `hcost : 0 < regionCost al sz`; a paragraph stating exactly which conclusions use readout predicates/constants (`CellCoh`, `Sat`/`SeedChain`, `fibSpec`, …) and which two statements carry package definitions in a PREMISE (`fibRounds`; `regionCost`/`headroom`/`prodMem₀`) | §2.5 |
| T-5 (instrument overclaim) | "the two Lean instruments fail on a package module absent from the list; all three on a classified module absent from the build or a class outside the vocabulary" (TSV header lines 8–11, verified) | §5 "One module classification" |
| T-6 ("exactly the trio") | "exactly the trio" scoped to the pinned exports (402); the sub-trio unpinned lemmas named with Audit.lean cites; "bounded by the trio" for every theorem | §3 "What the build checks" |
| D-1 (`pot … ≤ lemDefaultFuel` absent) | Stated as THE STATIC FUEL PREMISE in the premise list, with `pot` (Potential.lean:43), `lemDefaultFuel = 1000000` (LemLib.lean:56), `CerbFuel.driverFuel` (CerbFuel.lean:71), KOI A1, the [USER 2026-09-03] ruling, and the planned restatement (`../docs/2026-09-04_review-of-fuel-parameter-design.md` §5); repeated in §6 | §4 premise list; §6 "The fuel constants" |
| D-2 (annotation-free fragment absent) | Stated where `Frag` is introduced, with Soundness.lean:4129–4147: `Expr []` at every node; located Core (every C-elaborated program) outside; why (the `current_loc` equation); the programs are authored Core; the mover | §1 "The fragment" |
| D-3 (top mask absent) | Both judgments at `⊤` (21/26 sites measured by grep), `AtomicStep`/`wp_of_atomic` mask-generic, "classical sequential SL, no invariants", KOI B11, deferral cited from the register | §1 "The two judgments"; §6 "Masks" |
| D-4 (ruled Reynolds/O'Hearn reading absent) | The [USER 2026-09-03] ruling quoted verbatim from DECISIONS ("the outer loop is the 'scheduler' loop … the scheduler is degenerate, we never see schedule changes"); thread-level statement = the triple's semantics; outer fuel does no run-length work (KOI A2); the singleton equation as the sequential strengthening of the outcome-list meaning (KOI B5) | §4 "The ruled reading" |
| D-5 (`tagDefs = fmapEmpty` absent) | `htd`/`hex` first in the premise list, tied to `drive fmapEmpty false`, KOI B4; repeated in §6 | §4; §6 |
| S-1 (three CLOSED arc chronicles under "open items") | Deleted from ARCHITECTURE; verbatim in the archive; §7 keeps the three goals with status/provenance and points at §6 for what is open | §7; archive §7 |
| S-2 (paragraph about a `sorry` that no longer exists) | One present-tense sentence: no `axiom`, no `sorry` at the pin, how measured; history in the archive / `2026-09-03_repin-fuel-notes.md` | §3 "The trust base" |
| S-3 (the mirror paragraph as a changelog) | Rewritten in the present tense: `Ctl` is live, `Step.call` pushes …; the discharge devices are proof devices in no export's statement; the auditor quote deleted | §1 "Configurations and the mirror"; §2.2 |
| S-4 (slice ids and dates as vocabulary) | Zero occurrences of `driveU`, "former", "formerly", "until", "deleted", "since" (grep); no K<n>/C<n>/F1/AR5/P3.5 id as vocabulary — the only remaining `K3`/`AR5` tokens are inside the titles of the two DECISIONS entries cited; every date is inside a `[USER date]`/`[AGENT date]` tag or a record path | whole document |
| C-1 (negative total result absent) | `dg_loop_exhausts` (DivergeExhibit.lean:126) and `diverge_total_unprovable` (:172) with their shapes and the "false, not merely unprovable" reading | §2.3 |
| C-2 (undefined house terms) | A glossary at the head: engine, shipped driver, `Frag`, mirror, round, collapse, lane, profile, seeded, closed shipped-driver statement / production statement, root of trust, speedbump | head |
| C-3 (14-line and 40-line sentences) | The root-of-trust sentence is a table (statement / file:line / premises); the mirror paragraph is split into three; the longest remaining prose sentences were split in a second pass | §2.5; §1; throughout |
| C-4 (`spikeCtl`/`procCtx` uncited) | Cited in the glossary (`Step.lean:3331`, `:3336`, `:3355`, `:3363`; `ProdEntry.lean:580`, `:567`) | glossary |
| P-1 (unattributed auditor quote) | Deleted; the claim is stated directly | §2.2 |
| P-2 (uneven tags) | Every ruling carries `[USER date]` (2026-08-29 trust architecture; 2026-09-02 fail-closed boundary, referent rule, speedbumps, acceptance goals; 2026-09-03 fuel defect / R-O'H reading); every agent decision `[AGENT date]` (inventory ON DEMAND; `la_pos`); the mask deferral is cited as the register has it — see Deviations (1) | throughout |
| H1 staleness (brief) | Nine closed statements everywhere (the table lists nine; `even_odd_certified_production`, EvenOddExhibit.lean:721); the deleted `outcomesU_done`/`outcomesU_of_step` no longer named; manifest 30 RULE / 0 RULE-TOTAL-UNDEMONSTRATED / 0 PARTIAL-ONLY / 15 NO-RULE / 5 OUT-OF-SCOPE / 18 consumer modules; boundary check 19 modules, 0 allowances (the gate line quoted); pins 402 | §2.5, §3, §5 |

## 2. What moved to the archive

`docs/2026-09-04_architecture-history-archive.md` = a header (what it
is; where each arc's authoritative record lives; a per-section table of
carried-forward vs. moved) followed by the COMPLETE superseded text of
ARCHITECTURE.md at `b8413a5`, verbatim (`git show
b8413a5:cerberus-heaplang/ARCHITECTURE.md`, appended unmodified — nothing
is lost, and the reader can diff). The narrative that left the front
document, by superseded section: §2 the calls-arc genesis of `Ctl`, the
trust-rule/standards-audit dating, the "since the fuel-lane restatement"
clauses, the auditor quotation; §3 the K2/K3/C3 tags; §4 the F1/C4
dating and the declined-restatement note; §5 the audit-finding dating;
§6 the `Cmm_op.lean` `sorry` history, the 40-line root-of-trust
sentence's asides, the `driveU` paragraph and the fuel-arc request
narrative; §7 the three CLOSED arc chronicles (region access K5,
kill/free K0–K5.1, calls C1–C4), the two-label and mutual-recursion
closure narratives, the instrument paragraphs' slice history.

## 3. Claims verified, and how

Method: `grep -n`/`sed -n` over `CerberusHeapLang/*.lean` at `b8413a5`,
over `.cerberus-ws/lean_frontend/{CerbND.lean,generated/*.lean}` at
`f95ef8d9c` (`git -C .cerberus-ws rev-parse` = `f95ef8d9c`), over
`scripts/*`, `../scripts/*`, `docs/CAPABILITY_MANIFEST.md`,
`docs/2026-09-04_h1-notes.md` §8 and `../docs/DECISIONS.md`. Every
`file:line` in the rewrite was produced by one of these reads; the ones
first estimated from the review were re-read and corrected before the
commit (`prodCtx` :580, `hjmp` :2035, `boundary_check.sh` :46, Audit
sweep ranges :617–:636 / :637–:653, sub-trio note :354–:356, Rules
header :35–:44, `engine_adequacy` premises :1278–:1296).

- Statements read in full: `engine_step_matchU` (Round.lean:1010),
  `cerberusRound_classify` (:5476), `frag_round_complete` (:5369),
  `CerberusRound` (:195), `ShippedRefusal` arms (:220–:325), `OpenRound`
  (:357), `RoundClass` (:1631); `DriverSafeCtl` (Adequacy.lean:932),
  `engine_adequacy` (:1278), `MemTriple` (:1518), `project_triple_pure`
  (:1605), `FragProcs` (:767), `ControlOk` (:800), `LaunchCoh` (:422);
  `DriverDoneCtl` (ProdLoop.lean:456), `wpt_driver_cps` (:609),
  `wpt_driver_done_procs` (:799), `DriverDoneAt` (:56); `prod_run_eqJ`
  (ProdEntry.lean:402), `prod_run_eqJ_procs` (:716), `prod_run_safe_procs`
  (:768), `prodFileWith` (:544), `prodFile_eq_with` (:549), `prodCtl` (:567),
  `prodCtx` (:580); `loop_step_frag` (DriverCollapse.lean:2118),
  `loop_step_frag'` (:2024, `hjmp` :2035), `ctlThread` (:2162),
  `LabeledProcs` (:2178), `CtlTied` (:2205); the nine production
  statements and the two closed partial forms (every premise transcribed
  into the §2.5 table from the source); `dg_loop_exhausts`/
  `diverge_total_unprovable` (DivergeExhibit.lean:126/:172);
  `counter_loop_certified` (LoopExhibit.lean:427) and
  `fib_certified_production` (ProdLoopExhibit.lean:75) quoted verbatim.
- Declarations located by grep: everything cited in §2.1 (Rules, Wps,
  Wpt, Heap line numbers), `Frag` and its 23 constructors
  (Soundness.lean:4149–:4314, counted), `BareHead` (:3981, seven
  constructors), `PePure` (:2007), the annotation-free header
  (:4129–:4147), `hbsz` (:4296), `Ctl`/`Config`/`MachineCtx`/`SeqWF`
  (Step.lean:371/:400/:405/:448), `Step.call`/`ret`/`ret_annot`/`ctl_cases`
  (:2047/:2079/:2096/:2250), `callRedex?` (:703), the profiles
  (:3331–:3363), `Lang.lean:58`, `pot` (Potential.lean:43), `MemWF`
  (Heap.lean:1583, ten fields listed by `grep` of the structure body),
  `CohG` (:2632, `wf` field), the `MemWF.*` preservation theorems,
  `create_fresh_global` (:1801), `regionCost`/`headroom`/`regionCost_pos`
  (:2322/:2267/:2329), `fibRounds`/`fibRounds_closed`
  (FibRecExhibit.lean:450/:470), `ml_budget_bridge`
  (MallocListExhibit.lean:1626), `SeedChain` (ListRevExhibit.lean:1210),
  `Sat`/`CellMap` (Adequacy.lean:1415/:1407), `DeadAt` (:1900), the
  `*_consequence` lemmas (:1909–:2007), `drive_safe_aux` (:1079, private).
- Consumers: `wps_sound`/`wps_sound_empty`/`wpt_sound` by grep over all
  package modules, non-comment lines only (listed in §2.1);
  `wps_sound_cps`/`wpt_sound_cps` reach only Wps/Wpt/ProdLoop/Step/API/Audit.
- Engine cites at the pin: `drive_nonmemory_steps_aux2_lemFuel`
  (Driver.lean:346, its `| 0 =>` kill arm), `new_drive_core_threads`
  (:352–:355, calls the wrapper), the main-arena block (:528–:531);
  `fuelExhaustedKill` (CerbND.lean:80–:81),
  `drive_nonmemory_steps_aux2_wrapper_defeq` (:396–:397),
  `drive_wrapper_defeq` (:467), `drive_lemFuel` (:450),
  `drive_nonmemory_steps_aux2_lemFuel_zero` (:322); `driverFuel`
  (generated CerbFuel.lean:71 = 100000000); `isAtomicMemberAccess`
  (generated CerbMem.lean:1949, checks :2003 `loadM`/:2067 `storeM`),
  `killM` (:1895), `loadM` (:1961), `storeM` (:2007);
  `lemDefaultFuel = 1000000` (`.lake/packages/LemLib/lean-lib/LemLib.lean:56`).
- Counts: mask sites `grep -c '⊤'` = 21 (Wps.lean) / 26 (Wpt.lean);
  manifest tail line (30/0/0/15/5, 0 red, 18 consumers; CLAIMS 11 rows /
  90 names) read from `docs/CAPABILITY_MANIFEST.md:131–132`; pins 402 and
  `BOUNDARY: 19 modules checked, 0 internals mention(s) in total, exit=0`
  from the FULL gate quoted verbatim in `docs/2026-09-04_h1-notes.md` §8;
  the 15 NO-RULE / 5 OUT-OF-SCOPE rows enumerated from the manifest's
  variant table.
- Scripts: `test_unit.sh` gate/speedbump lines (:28, :39, :47, :65, :88),
  `boundary_check.sh` header and pattern (:46), `module_classes.tsv`
  header lines 8–11 (the fail-hard sentence), `capability_manifest.lean`
  header ("WHAT GREEN DOES NOT ESTABLISH"), `parametric_inventory.lean`
  header (:1–:16, ON DEMAND [AGENT 2026-09-04], fail-closed).
- Rulings: DECISIONS lines 265 (speedbumps), 703 (acceptance goals,
  quoted), 816 (fail-closed boundary), 1135–1142 (K3 landed, `la_pos`
  [AGENT]), 1787–1829 (fuel defect + the R/O'H reading, quoted verbatim),
  1878–1884 (mask deferral, [AGENT], pending the operator), 1916–1930
  (inventory ON DEMAND [AGENT]).
- Record paths: every `docs/…`/`../docs/…` path cited in the rewrite
  exists (scripted check, zero missing).
- Consistency of the other surfaces: README already states nine
  statements, 18 consumers, 30 RULE / 0 undemonstrated, zero allowances
  (README:111, :121, :296, :302, :832); the only contradiction found was
  WALKTHROUGH's "that no export consumes" (line ~833), corrected.

## 4. Deviations from the brief ([AGENT], each with its reason)

1. **The mask deferral's tag.** The brief describes the mask item as
   "moved to the RefinedC arc by [USER 2026-09-04]". The register at
   `b8413a5` has no such entry: the only mask ruling is the [AGENT]
   disposition in the 2026-09-04 external-audit entry ("DEFERRED as a
   design-level slice to schedule with the operator … PENDING THE
   OPERATOR"), and KOI B11 says the same. Provenance is verbatim or it
   does not exist, so ARCHITECTURE cites what the register records
   ("deferred (KOI B11; DECISIONS 2026-09-04 external-audit entry,
   pending the operator's scheduling)"). FOR THE ORCHESTRATOR: if the
   [USER 2026-09-04] ruling exists, append it to DECISIONS and re-tag
   the two sentences (§1 "The two judgments", §6 "Masks").
2. **Length.** 734 lines / 5873 words against the brief's "likely a third
   to a half of the current 674 lines". The arithmetic: the superseded
   text carried about 250 lines of narrative (the three arc chronicles
   alone were 85), all of which left; the brief's mandatory additions —
   a glossary (~40 lines), two theorems quoted VERBATIM with their
   readings (~70), the premise list with every generic premise explained
   (~45), the fifteen NO-RULE variants enumerated (~20), the
   nine-statement table with every premise (~15), the ruled reading
   (~20), the negative result (~10), the manifest's "what green
   establishes" reproduced exactly (~25) — are about 260 lines of
   required content. The document is now a description of the same
   length, not a longer changelog. Further cutting would remove
   disclosures the brief and the review demand.
3. **The archive is the whole superseded text**, not a per-sentence
   extraction. Reason: "verbatim, so nothing is lost" is only checkable
   against the whole; the archive's header table maps each superseded
   section to what was carried forward and what moved, so a reader still
   finds the history sectioned by the paragraph it came from.
4. **The glossary sits before §1**, not "at the head of §2" as the review
   suggested, because the brief's structure makes §1 the first place
   the terms are needed.
5. **README not edited.** Checked for contradictions (counts, the
   allowance sentence, eight/nine, "no export consumes"): none found —
   README was updated by H1a/H1b. WALKTHROUGH: one sentence (T-2's
   twin). README line 97 and WALKTHROUGH line ~1744 say "the eighth
   root-of-trust statement" of `fib_rec_certified_production` — an
   ordinal, still true with nine.
6. **KOI B8 still lists the two-label exhibit and mutual recursion as
   open** (orchestrator-owned register; H1b closed both). ARCHITECTURE
   cites B8 only for the items that ARE open (concurrency, function
   pointers, external calls) and states the two closures as facts of
   the tree (§2.5, the manifest consumers). Flagged, not edited.
7. **`SeqWF` as a premise** is mentioned only for `cerberusRound_classify`
   (§2.2); `shipped_done`'s premise is not separately listed — it is not
   an export.

## 5. Self-check against the standard's seven structure items

| Item | Where | Check |
|---|---|---|
| (i) what the object is: `Frag`, the mirror, the two judgments; what "Reynolds/O'Hearn over Core" means here | §1 (four labelled paragraphs + the closing "means" paragraph) | `Frag` with its 23 constructors and the two boundary facts (annotation-free; fail-closed declaration); `Config`/`Ctl`/`Step`; `wps`/`wpt` with clauses, budget discipline, top mask; the meaning paragraph |
| (ii) what is proved: rules; the collapse; adequacy in both lanes to the genuine shipped driver; the nine closed statements; the negative result | §2.1–§2.5 | atomic specs → judgments → collapses (with consumers); certification + completeness; `dg_loop_exhausts`/`diverge_total_unprovable`; both lanes over `drive_nonmemory_steps_aux2_lemFuel`; the projection; the pipeline theorems; the nine in a table + the two closed partial forms |
| (iii) what is trusted: kernel, iris-lean, the pinned semantics; the trio; the declared boundary; what is NOT trusted | §3 | three trust items; the build's three checks with the pin count; "exactly" vs "bounded"; "There is no declared boundary axiom"; the proof devices; "no hand-written driver loop, scheduler or discharge function occurs in any export's statement" |
| (iv) how to read an export: one production and one thread-level statement, every premise incl. fuel and tag definitions | §4 | `fib_certified_production` and `counter_loop_certified` verbatim with readings; the eight-bullet premise list (`htd`/`hex`, `hκ`, `hfrag`/`hQf`/`hPf`, `hpot`/`hQpot`/`potBound`, `hcl`, `hcoh`/`hl`, `hwp`); the ruled reading |
| (v) the instruments and what green establishes, from the manifest header exactly | §5 | the manifest header's two paragraphs reproduced in substance; classification; import direction; boundary check with the gate line; claim matrix; inventory ON DEMAND |
| (vi) what is not covered / not claimed, each pointing at its register entry | §6 | fragment boundary (B8), 5 OUT-OF-SCOPE, 15 NO-RULE (B14, A3), masks (B11), fuel constants (A1, A2, B5), tag definitions (B4), residual (B7), statement shapes (B1–B3, B6), two bridges (B12), parametric interfaces (B9), instrument limits (C11–C13) |
| (vii) the acceptance-goals ledger | §7 | the three goals, verbatim [USER 2026-09-02] wording, status, the theorems that close each, one record pointer each; "not a goal: covering all of Core"; pointer to §6 and the archive |

Terminology: "shipped driver", "lane", "collapse", "round", "profile",
"seeded", "closed shipped-driver statement", "root of trust", "speedbump"
are defined in the glossary and used in that sense throughout (grep).
No sentence of prose exceeds four wrapped lines after the second pass
except list items that enumerate names with cites. Zero dates outside
`[USER …]`/`[AGENT …]` tags and record paths; zero "former/until/since/
deleted"; zero `driveU`.

## Second pass (reviewer 4)

Author: the second-pass worker (not reviewer 4; not the first-pass
author). Branch `hygiene-h1`, worktree `worktrees/hygiene-h1`, base
`cd68c46`. Scope: DOCS ONLY — `ARCHITECTURE.md`, two stale section
pointers (`docs/CLAIMS.md:44`, `README.md:835`), this record. No `.lean`,
no script, no `docs/DECISIONS.md`, no `docs/KNOWN-OPEN-ITEMS.md` change;
no `lake`/`lean` invocation. Every fix below was verified by READING the
`.lean` text at `cd68c46`, the pinned workspace at `f95ef8d9c`
(`git -C .cerberus-ws rev-parse` = `f95ef8d9c`), `docs/DECISIONS.md`,
`docs/KNOWN-OPEN-ITEMS.md` and `docs/CAPABILITY_MANIFEST.md`. Commits:
(1) `1856685` review 4 copied verbatim (`cmp`-identical to
`worktrees/review-arch-4/cerberus-heaplang/docs/2026-09-04_architecture-review-4.md`);
(2) `b61a9c0` the edits; (3) this record.

### Disposition table

| Id | Done | Where (ARCHITECTURE at `b61a9c0`) | Verified against |
|---|---|---|---|
| P-1 | **DISPUTED — not applied** ([AGENT]). The phrase "And for our logic, which (for now) is sequential," IS in the register verbatim: `docs/DECISIONS.md:1753`–`:1756`, the fuel-scope paragraph of the entry "2026-09-03 [AGENT] F1 RANGE AUDIT 328be1a..2bbfd70". The reviewer matched the later entry's re-quote with an ellipsis (`:1823`, "FUEL IS A DEFECT…"). The full quotation is kept, set as a block quote so the register text is not re-wrapped inside a sentence, with BOTH register cites beside it so the next reviewer finds the source line. | §4 "The ruled reading" (block quote) | `grep -n "for now) is sequential" docs/DECISIONS.md` → `1755`; `sed -n 1752,1757p` read |
| T-1 | Sentence fixed: the raw-WP layer of `Rules.lean` is mask-generic — `AtomicStep` `:194`, `wp_of_atomic` `:210`, `wp_store` `:1584`, `wp_load` `:1614`, `spike_wp_wand` `:1676` — the two statement judgments are not | §1 "The two judgments" | `grep -n CoPset Rules.lean` → exactly lines 196, 210, 1584, 1614, 1676 (no other mask-generic declaration exists) |
| T-2 | `wps_sound_empty` consumers completed to nine, with lines; the three lists made a table | §2.1 consumer table | grep over `CerberusHeapLang/**/*.lean`, non-comment lines: Exhibit :349/:701, StructExhibit :199/:830, CaseExhibit :143, LoopExhibit :391, FibExhibit :402, ArrayExhibit :592, WseqExhibit :107, ListRevExhibit :1434, TwoLabelExhibit :531; `wps_sound` CallSmoke :330, FibRecExhibit :648, EvenOddExhibit :501; `wpt_sound` CallSmoke :461 |
| T-3 | Paragraph replaced by a per-statement table re-derived from the nine statement texts (not patched): exhibitA `sevenVal`/`sevenBytes`/`intTy` (`Examples/Layout.lean:57`/`:65`/`:50`) + `CellCoh`; fib `ivVal` (`LoopExhibit.lean:63`) + `fibSpec` (`FibExhibit.lean:60`); counter `intUndefBytes` (`AllocExhibit.lean:88`) + `sevenBytes`/`intTy`/`CellCoh`; list_reverse `ptrVal` (`ListRevExhibit.lean:466`), `SeedChain` (`:1210`), `CellMap` (`Adequacy.lean:1407`), `Sat` (`:1415`); dispose/region/malloc engine fields only; fib_rec `ivVal`/`fibSpec` (+ premise `fibRounds`); even/odd `ivVal`. A lead sentence exempts the authored program and its wrapper explicitly | §2.5 second table | all nine signatures read in full (`ProdExhibit.lean:264`; `ProdLoopExhibit.lean:75`, `:620`, `:1435`; `DisposeExhibit.lean:1479`; `RegionLoopExhibit.lean:633`; `MallocListExhibit.lean:1654`; `FibRecExhibit.lean:865`; `EvenOddExhibit.lean:721`); `Vunit` is the engine's (`generated/Core.lean:459`) |
| D-1 | `hbsz` explained at its one remaining mention: the selected branch's `esize` is bounded by the case node's; a membership premise the client discharges per program, `rfl` for authored programs (`caseProg_select`, `CaseExhibit.lean:68`), not a theorem | §6 "The mirror-completeness residual"; §7 Goal 2 only points there | `Soundness.lean:4296`–`:4297` read (`hbsz : ∀ e', select_case … = some e' → esize e' ≤ esize (caseRedex …)`); the header note `:4292` ("both premises are `rfl`") |
| C-1 | Every reviewer-listed long sentence split (95–103 → a two-item list; 79–86; 142–151; 165–172; 194–200; 269–276; 278–284; 305–311; 484–492; 545–551; 564–574; 605–616) and every other prose sentence brought to ≤ 4 wrapped lines (checker below: 0 over). §5's manifest bullet no longer copies the header: green in short (4 lines) + the header cite `CAPABILITY_MANIFEST.md:8`–`:26`. §7 Goals 1–2 are one status line each pointing at §2.4/§2.2/§6. §6's mask/fuel/tag items are one to two lines each pointing at §1/§4. Goal 3's `MemWF` content moved to a new §2.6 "The memory invariant"; §7 points at it. Three enumerations became tables (collapse consumers, package definitions, NO-RULE variants). Length: see the deviation below | whole document | — |
| T-4 | "`_op` forms" now exactly `store`/`load`/`kill`/`alloc` (no `create_op`) | §1 "The fragment" | `Frag` constructors `Soundness.lean:4150`–`:4314` listed: `store_op`, `load_op`, `kill_op`, `alloc_op`, `memop_op`; `create` only at evaluated operands |
| T-5 | `Driver.lean:355`–`:358` | §4 "The ruled reading" | generated `Driver.lean`: `def new_drive_core_threads` at `:355`, the call `(drive_nonmemory_steps_aux2 _lemReader_tagDefs) fmapEmpty … tids` at `:358` |
| T-6 | "(§5; KOI C11, C12); the claim matrix is prose, as its own header states (CLAIMS.md)" | §6 "The instruments' limits" | `docs/KNOWN-OPEN-ITEMS.md:57`–`:59` (C11 stripper, C12 per-module allowances, C13 CLOSED at H1a); `docs/CLAIMS.md:3` "HAND-WRITTEN PROSE, stated as such" |
| T-7 | (a) `MachineCtx`'s eight fields named: `tagDefs`, `file`, `extern`, `tid`, `parent`, `errno`, `currentLoc`, `runState`; (b) `../scripts/semantics-pin.env` | §1 "Configurations and the mirror"; header | `Step.lean:405`–`:413` read; `ls ../scripts/semantics-pin.env` from the package |
| D-2 | "`false` is the shipped driver's own sequential mode (the generated `drive` fails with "CONCURRENCY IS BROKEN" at `true`, `Driver.lean:530`); `fmapEmpty` is the wrapped file's tag-definition table, empty — the `htd` narrowing of KOI B4" | §4 production reading | generated `Driver.lean:530` (one line: the `drive` body, containing both `current_proc_opt := (some main_sym)` and `"CONCURRENCY IS BROKEN"`); KOI B4 row `docs/KNOWN-OPEN-ITEMS.md:31` ("a narrowing") |
| S-1 | "added on orchestrator direction" removed (the `la_pos` provenance tag alone remains, now in §2.6); the closing sentence is "The records of the arcs that closed the goals are indexed in …" | §2.6; §7 | grep: zero "slice"/"slices"/"orchestrator direction" |
| C-2 | Glossary entries "the trio" / "trio-exact" and "PCALL, RETURN, PROGRAM-DONE" added before first use; the parametric deferral tagged [USER 2026-09-02] | glossary; §6 | `Audit.lean:159`–`:160`; `reduction: PCALL`/`RETURN`/`PROGRAM-DONE` in generated `Core_reduction.lean` (`step_ctx`, one occurrence each); `docs/DECISIONS.md:372` "2026-09-02 [USER] PARAMETRIC INTERFACES NOT ADOPTED" |
| S-2 | `docs/CLAIMS.md:44` "ARCHITECTURE §7, KOI B8" → "ARCHITECTURE §6, KOI B8"; `README.md:835` "not a gate — ARCHITECTURE §7" → "§5". KOI B7/B9: not edited (orchestrator-owned); replacement text below. Also checked: KOI B8 "ARCHITECTURE §6" still right; KOI B12 "ARCHITECTURE §2" still resolves (the bridges are §2.2); `capability_manifest.lean:97` "ARCHITECTURE §7 Goal 2" still resolves; `EvenOddExhibit.lean:4`/`TwoLabelExhibit.lean:4` are module-header history, not touched (no `.lean` edits) | CLAIMS.md; README.md | `grep -n "ARCHITECTURE §"` over the package docs, scripts, KOI |

### KOI pointer fixes FOR THE ORCHESTRATOR (`docs/KNOWN-OPEN-ITEMS.md`, not edited here)

- B7 (line 34), "Where" cell: replace `ARCHITECTURE §6 (lines ~412–444); docs/2026-09-02_fragment-closure-notes.md`
  with `ARCHITECTURE §2.2 (the residual) and §6 "The mirror-completeness residual" (the hbsz premise); docs/2026-09-02_fragment-closure-notes.md`.
- B9 (line 36), "Where" cell: replace `ARCHITECTURE §7; docs/2026-09-02_parametric-semantics-spike.md (DEFERRED banner)`
  with `ARCHITECTURE §6 "Deferred parametric semantics interfaces"; docs/2026-09-02_parametric-semantics-spike.md (DEFERRED banner)`.
- Optional precision, B12 (line 39): `ARCHITECTURE §2` → `ARCHITECTURE §2.2` (still resolves as is).
- Still open from the first pass (deviation 6 above): B8 lists mutual recursion/two-label as exhibited already — consistent; nothing further.

### [AGENT] deviation: length 731, not ~630

The reviewer's concrete cuts were all applied: the manifest bullet 26 → 20
lines (the class definitions and the header copy are gone; green is stated
in four lines and the header is cited); §7 39 → 23 (Goal 3 moved out;
Goals 1–2 one status line each); §6's mask/fuel/tag items 12 → 8; the
glossary's "round"/"lane" one to two lines. These save about 30 lines.
Against them the review REQUIRES additions: a §2.6 (the `MemWF` content
plus a heading, +3 net), two glossary entries (+5), the block-quoted
quotation with its two register cites (+6 net), three consumer lines and
the table framing (+4), the exact package-definitions table (+5 net vs.
the paragraph), the `hbsz` explanation (+3), the eight `MachineCtx`
fields and the two-item list (+3), and — the dominant term — splitting
every sentence over four lines, which adds roughly one line per split
across ~25 splits. Net: 738 → 731 (DERIVED, `wc -l`; words 5882 → 5883).
Reaching ~630 would require removing content the review itself lists as
disclosure (the fifteen variants, the nine-statement premises, the
generic premise list, the two verbatim readings, the negative result).
Decision: keep every disclosure, record the arithmetic, and let the
re-reviewer judge whether 731 lines of ≤ 4-line sentences reads.

### Self-check

- **Sentence length**: a script (prose only; code blocks, tables and the
  block quote excluded; a sentence ends at `.`/`?`/`!`/`:` followed by a
  capital, backtick or end of line) counts 298 sentences, **0 over four
  wrapped lines** (DERIVED). Long lines > 90 characters are exactly the
  table rows, the code block's comment line and the three unbreakable
  `CerbND.runND …` identifiers.
- **Line count**: 731 (`wc -l`); words 5883.
- **Dates**: 25 `2026-` tokens, every one inside a `[USER 2026-…]`/`[AGENT
  2026-…]` tag or a `docs/2026-…` record path; **0 outside** (DERIVED,
  `grep -v` of the two forms).
- **Vocabulary**: zero "former/formerly/until/since/deleted/driveU/slice";
  `K3`, `F1`, `AR5` occur only inside the three cited DECISIONS entry
  titles; `C5`/`C10` are CLAIMS row ids, `C11`/`C12` KOI ids.
- **Record paths**: every `docs/…`/`../docs/…` path cited exists (scripted
  `ls`, zero missing).
- **Every finding's fix re-read against the source**: the "Verified
  against" column above; additionally the round-name glossary entry
  against generated `Core_reduction.lean` (`reduction: PCALL` at `Eproc`,
  `reduction: RETURN` at "end of procedure", `reduction: PROGRAM-DONE` at
  the startup thread's `Step_done2`), the `MemWF` field list against
  `Heap.lean:1583`–`:1613` (ten fields: `live_lt`, `dead_lt`, `live_dead`,
  `disj`, `cursor_lo`, `size_nonneg`, `la_wf`, `la_pos`, `dyn_lo`,
  `dyn_disj`), the manifest header range against
  `docs/CAPABILITY_MANIFEST.md:8`–`:26`.
- **Nothing lost**: every disclosure the review lists as present in the
  first pass is present (grep for each: `pot … ≤ lemDefaultFuel`,
  annotation-free, `⊤` with 21/26, `tagDefs = fmapEmpty`, the ruled
  reading, the fifteen NO-RULE and five OUT-OF-SCOPE variants,
  `diverge_total_unprovable`, "There is no declared boundary axiom", the
  nine premises, `hcost`, the two verbatim theorem texts unchanged).

## Third pass (reviewer 5)

Author: the third-pass worker (not reviewer 5; not the first- or
second-pass author). Branch `hygiene-h1`, worktree `worktrees/hygiene-h1`,
base `b623107`. Scope: DOCS ONLY — `ARCHITECTURE.md`, one README trust
sentence, this record. No `.lean`, no script, no `docs/DECISIONS.md`, no
`docs/KNOWN-OPEN-ITEMS.md` change; no `lake`/`lean` invocation. Every fix
was verified by READING the `.lean` text at `b623107`, the pinned
workspace at `f95ef8d9c` (`git -C ../.cerberus-ws log -1 --format=%h` =
`f95ef8d9c`), LemLib at `.lake/packages/LemLib`, `../docs/DECISIONS.md`
and `../docs/KNOWN-OPEN-ITEMS.md`. Commits: (1) `284a556` review 5 copied
verbatim (`cmp`-identical to
`worktrees/review-arch-5/cerberus-heaplang/docs/2026-09-04_architecture-review-5.md`);
(2) `f477504` the edits + the README sentence; (3) this record.

### Disposition table

| Id | Done | Where (ARCHITECTURE at `f477504`) | Verified against |
|---|---|---|---|
| T-1 | The sub-trio list restated exactly as `Audit.lean`'s comments record it: `fibRounds_closed`, `regionCost_pos` and the `freshBase_*` bounds `[propext, Quot.sound]`; `BareHead.decomp_call_root` `[propext]`; `regionCost_eq` and `runND_killed` no axioms. The rule stated: "exactly the trio" = the pinned exports; every other theorem bounded by the trio, by the sweep; the sub-trio public names are therefore unpinned. The five-line sentence split into three | §3 "What the build checks" | `Audit.lean:354`–`:356` ("sub-trio cones `[propext, Quot.sound]` … `freshBase_ne_zero_of_cost`/`headroom_freshBase`"), `:380`–`:384` ("SUB-trio cones `[propext, Quot.sound]` … `freshBase_ne_zero_of_cost'`/`headroom_freshBase'`/`freshBase_pos_nat`/`regionCost_pos` (`regionCost_eq` has no axioms at all)"), `:523`–`:525` ("`BareHead.decomp_call_root` — `[propext]` — and `fibRounds_closed` — `[propext, Quot.sound]`"), `:552`–`:553` ("`runND_killed` has NO axioms — measured"); pin loop `:615`–`:616`, sweep `:617`–`:636`, banned sweep `:637`–`:653` re-read. Cones as the comments record them, not re-measured (no `lake`) |
| D-1 | New §3 paragraph "The `panic!` arms" (18 lines; see deviation 1): the counts (61 code arms in the hand-written seams, 40 in `CerbMem.lean`, none in lem-generated code; DERIVED), what they are (OCaml `assert false`/`failwith` mirrors, where the OCaml aborts), the kernel reading (`Inhabited` default, `= default` by `rfl`), why it matters (a theorem about `drive` is about the Lean definition, which continues where the OCaml faults), how the rules stay away (`create_atomic`'s `hsz`; the NO-RULE `create` rows), what is NOT checked (no theorem says an export's run reaches none; the sweep sees axioms, not terms), the owner (KOI A5, the typed-failure-outcomes pass), and the distinction from §2.2's `panic` family (`failwithI`/`fuelExhaustedWith` are `opaque`: no kernel equation, theorems hold at every value). §2.2's "`panic` family" sentence now says "LemLib's kernel-opaque failure (not the `panic!` arms of §3)". §6 item "The engine's `panic!` arms" with KOI A5 (and the pin-vs-mainline `killM` fact, below). README "What you are asked to take on faith", second bullet: two sentences after "…stay away from `fuelExhaustedWith` and `failwithI`." | §3; §2.2; §6; `README.md:592`–`:597` | Counts: the command and output below. Kernel reading: generated `CerbMem.lean:1127`–`:1132` (comment "every such term is definitionally `default`" and `have hp : … (panicWithPosWithDecl m d l c msg : α) = default := … rfl`), `:2553`–`:2556` ("a plain `panic!` body is kernel-visible, making the fuel-exhausted branch provably equal to `default` — semantically false. Opaque core ⇒ no equations"); cerberus-lean `lean_frontend/docs/2026-09-03_typed-failure-outcomes-ruling.md` header ("for the semantics AS A MATHEMATICAL OBJECT, the failure site DENOTES the default value — the definition disagrees with the oracle exactly where the oracle crashes"; read-only reference). `failwithI`/`fuelExhaustedWith`: `.lake/packages/LemLib/lean-lib/LemLib.lean:160`–`:187` (`opaque failwithI … := default`, "opaque: NO equations"; `opaque fuelExhaustedWith … := witness`). `create_atomic` `Rules.lean:991`, `hsz : 0 < CerbMem.sizeofCtype M.tagDefs ty` at `:995`; `sizeofCtype` returns `Nat`, `Void0` arm `panic!` at generated `CerbMem.lean:380`. Hand-written = generated copies: `cmp` identical for all nine files with `panic!`; `handwritten_copy.manifest` is the copy list |
| D-2 | "It is a pin, not the mainline; the queued re-pin and its one exported-text change (`killM_killed_inv`) are KOI A6." | §3 "The trust base" (iii) | KOI A6 row (`../docs/KNOWN-OPEN-ITEMS.md:22`): "mainline is ≥ 34 commits ahead (`de2fbf1`) … `killM` re-mirroring (one exported text change: `killM_killed_inv`)" |
| T-2 | `:501` → `:502` (the `wps_sound` call), `:673` → `:674` (`theorem even_odd_certified`), `:721` → `:722` (`theorem even_odd_certified_production`). Every `EvenOddExhibit.lean:` cite in the document re-verified at HEAD: exactly these three, all now exact | §2.1 table; §2.5 both tables | `sed -n 502p` = "(wps_sound (ctl := ⟨[], some mainSym, ℓ⟩) rfl (eoMain ra n) [fmapEmpty])) .rfl)).trans ?_"; `:674` = "theorem even_odd_certified (hn : 0 ≤ n) …"; `:722` = "theorem even_odd_certified_production (hn : 0 ≤ n)"; `git show dd7b852 -- CerberusHeapLang/EvenOddExhibit.lean` hunk `@@ -307,11 +307,12 @@` (one line added at the `eo_parity_even` docstring; the four later hunks are same-length). `FibRecExhibit.lean` untouched by `dd7b852` (`--stat`: only EvenOddExhibit.lean and the audit report) |
| C-1 | `../.cerberus-ws/lean_frontend/` | header | `ls ../.cerberus-ws/lean_frontend/generated/Driver.lean` from the package directory |
| C-2 | "`pot` … is a step-monotone size potential on terms; it dominates §2.2's round-level measure `esize` (`Frag.esize_le_pot : esize e ≤ pot e`, `:100`), so this premise discharges the certification's `hsz`." | §4 premise list, `hpot` | `Potential.lean:100` "theorem Frag.esize_le_pot {e : CoreExpr} (hf : Frag e) : esize e ≤ pot e"; `esize` `Soundness.lean:289`; the use `Adequacy.lean:1208` "have hsz : esize e ≤ lemDefaultFuel := Nat.le_trans hf.esize_le_pot hpot" |
| C-3 | Glossary entries *pinned*/*unpinned*, *the sweep*, *a tie*, *a readout*; "drain iteration" glossed in place ("the loop's last pass over the emptied thread list"); "wakeup-free" replaced by "Active means `NDactive NOWAKEUP`: no other thread is woken"; "the certification equation" → "the certification (§2.2)" | glossary; §2.4; §2.2; §1 | `Audit.lean:159`–`:160`, `:604`–`:636` (`trioExports`, the pin loop, the sweep); `DriverSafeCtl` `Adequacy.lean:935`–`:940` (six hypotheses: thread, `layout_state`, `core_extern`, `core_file`, `LabeledProcs`, `CtlTied`), `DriverDoneCtl` `ProdLoop.lean:459`–`:463` (the first five; `k + 2 ≤ fl` is the budget, not a tie); `loop_step_done_exhaust` docstring `DriverCollapse.lean:2253`–`:2256` ("the drain iteration on the empty thread list has no fuel"), the loop's `[] => nd_return acc` arm generated `Driver.lean:348`; `CerberusRound` `Round.lean:203` "(NDactive NOWAKEUP, …)"; `engine_step_matchU` is an implication `Step → CerberusRound` (`Round.lean:1010`–`:1017`) |
| S-1 | (a) "No export carries an interim label." deleted. (b) "(DECISIONS AR5-manifest entry)" → "(DECISIONS \"AR5-MANIFEST LANDED and COMBINED\")" | §3 last paragraph; §5 inventory bullet | `../docs/DECISIONS.md:1916` "2026-09-04 [AGENT] AR5-MANIFEST LANDED and COMBINED (…" |
| S-2 | Both cites: "`docs/2026-09-04_h1-notes.md` §8, the gate at `29d9195`" | §3; §5 boundary bullet | `h1-notes.md:254` "## 8. The FULL gate at `4acb10d`" and `:746` "## 8. The FULL gate at `29d9195`"; the cited lines `:752` ("export pins: 402 trio-exact") and `:781` ("BOUNDARY: 19 modules checked, 0 internals mention(s) in total, exit=0") are in the second |
| C-4 | (i) §5 "In short: …" paraphrase deleted; "Not established: …" kept. (ii) §6 first bullet → "**The fragment boundary** is §1's (KOI B8; CLAIMS \"Not claimed\")." + the five OUT-OF-SCOPE variants. (iii) Header: "The README carries the exhibits table and the build recipe, and gives each limitation its discharge or mover; §6 here lists the limitations with their register numbers (the two overlap by design)." The 430–434 sentence split (T-1) | §5; §6; header | README "Registered divergences and limitations" table (`README.md:628`–`:650`; columns Divergence / Discharge or mover / Home) — the README IS a register of limitations by discharge, §6 by KOI number, so the header now says both |

Reviewer 5's note to the orchestrator (T-2: a `.lean`-touching commit over a
cite-bearing front document must re-check the cites into the touched
file) is relayed unchanged; nothing in this pass addresses process.

### The `panic!` counts, as measured (verbatim; pinned workspace `f95ef8d9c`)

```
$ for f in ../.cerberus-ws/lean_frontend/*.lean; do c=$(grep -c "panic!" "$f"); [ "$c" != 0 ] && echo "$(basename $f): $c"; done
CerbDecode.lean: 6
CerberusImpl.lean: 2
CerbFloat.lean: 5
CerbFS.lean: 8
CerbMem.lean: 42
CerbND.lean: 1
CerbTags.lean: 1
CerbUtils.lean: 4
CoreParser.lean: 1
$ cat ../.cerberus-ws/lean_frontend/generated/*.lean | grep -c "panic!"
70
```

Raw total 70 = the sum over the nine hand-written files (6+2+5+8+42+1+1+4+1),
so the lem-generated files contain none (DERIVED). Of the 70 lines, nine
are comment lines, read one by one: `CerbFS.lean:47`, `:51`, `:91`;
`CerbFloat.lean:84`, `:163`, `:294`; `CerbND.lean:42`; `CerbMem.lean:1127`,
`:2555`. Code arms therefore 61, of which `CerbMem.lean` 40, `CerbDecode`
6, `CerbFS` 5, `CerbUtils` 4, `CerbFloat` 2, `CerberusImpl` 2, `CerbTags` 1,
`CoreParser` 1, `CerbND` 0 (DERIVED). The hand-written files and their
`generated/` copies are byte-identical (`cmp`, all nine). The document
quotes 61 and 40 with "counts DERIVED, `grep -c 'panic!'` less comment
lines"; the README sentence quotes the same two numbers.

### [AGENT] observations for the orchestrator (not edited here)

1. **KOI A5's wording describes the mainline, not the pin.** At the pin,
   `killM`'s dead-static-kill arm is a KILL — generated `CerbMem.lean:1906`–
   `:1907` "if st.deadAllocations.contains allocId then fail_
   (MerrUndefinedFree Free_dead_allocation)"; `grep -n 'panic!'` over the
   pinned `killM` (`:1895`–`:1919`) finds none. The `panic!` arm ("Concrete:
   FREE was called on a dead allocation") is on the cerberus-lean mainline
   (`../../cerberus-lean/lean_frontend/CerbMem.lean:2158` at `1b57bcf26`,
   read-only). A5's own source, scout-2 §8 (γ), says the same in context
   ("re-check `MemWF.killM` at that re-pin"). ARCHITECTURE §6 states the
   pin's fact and the mainline's; A5's first sentence could say "at the
   next pin".
2. **KOI A4–A6 cite `docs/2026-09-03_repin-scout-2.md`, which is not on
   `hygiene-h1`** (nor on `main`): `git branch --contains 07ceb44` =
   `repin-scout2` only; the file exists only in `worktrees/repin-scout2/`.
   The register points at an off-branch record.

### [AGENT] deviations from the brief (each with its reason)

1. **The §3 `panic!` disclosure is 18 lines, not three to six.** The brief
   mandates seven contents (count, what they are, the kernel reading, why
   it matters, what is not checked, the owner, the distinction from
   `failwithI`); written as ≤ 4-line sentences with cites they do not fit
   in six lines without dropping one. Decision: keep all seven, each as
   short as its cite allows. Removing any is a disclosure loss in the
   trust section — the reviewer's ground for the grade.
2. **README: two sentences, not one.** The single sentence ran six wrapped
   lines with a colon splice; split at the colon. Content unchanged.
3. **Length 774, not 731.** Net +43: the glossary +13 (four entries), the
   `panic!` paragraph +19, the §6 `panic!` item +5, the T-1 restatement
   +3, D-2 +2, C-2 +3, the drain/NOWAKEUP glosses +2, the header +1;
   the cuts −5 (§5 paraphrase −4, §6 first bullet −2, S-1a −1, +2 from
   the README/§6 fix). Every addition is one the review asked for.

### Self-check (at `f477504`)

- **Sentence length**: a paragraph-aware script (prose only; headings,
  code blocks, tables and the block quote excluded; list items start a
  paragraph; a sentence ends at `.`/`?`/`!`/`:` followed by whitespace and
  a capital, quote, backtick, bracket or end of paragraph) counts 348
  sentences, **0 over four wrapped lines** (DERIVED).
- **Line count**: 774 (`wc -l`). Long lines > 90 characters: only table
  rows, the code blocks' lines and the `CerbND.runND …` identifiers.
- **Dates**: 25 `2026-` tokens; **0 outside** a `[USER 2026-…]`/`[AGENT
  2026-…]` tag or a `docs/2026-…` record path (DERIVED, `grep -v`).
- **Cites re-verified at HEAD**: every `EvenOddExhibit.lean:` cite (`:502`,
  `:674`, `:722` — the only three) and every `Audit.lean:` cite (`:45`,
  `:159`–`:160`, `:354`–`:356`, `:380`–`:384`, `:523`–`:525`, `:552`–`:553`,
  `:615`–`:616`, `:617`–`:636`, `:637`–`:653`) read at the cited lines;
  the new cites `Potential.lean:100`, `Rules.lean:995`, `Adequacy.lean:935`–
  `:940`, `ProdLoop.lean:459`–`:463`, `DriverCollapse.lean:2253`–`:2257`,
  `Round.lean:203`, generated `CerbMem.lean:380`/`:1127`–`:1132`/`:1906`–
  `:1907`, `LemLib.lean:160`–`:187`, `DECISIONS.md:1916`, `h1-notes.md:254`/
  `:746`/`:752`/`:781`, KOI rows A5/A6 read.
- **Record paths**: every `docs/…`/`../docs/…` path cited exists (scripted
  `ls`, zero missing).
- **Nothing lost**: every disclosure the second pass's self-check lists is
  still present (grep for each); the two verbatim theorem texts unchanged.
