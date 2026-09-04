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
