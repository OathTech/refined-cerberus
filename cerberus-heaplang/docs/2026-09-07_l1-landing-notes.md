# L1 landing record — E5 complete, re-cut from `dialect-e5` onto main (2026-09-07)

Worker record for the FIRST landing slice of `docs/2026-09-07_landing-charter.md`
(§0 ground rules, §2 L1). Branch `land/e5-complete`, worktree
`worktrees/land-e5`; base = main `901ef50` (after the L0 docs merge); the
other agent's source branch `dialect-e5` at `cb46e4c` (READ-ONLY; its
complete record lives on `parked/demo-expansion-2026-09-07`). Semantics pin
UNCHANGED: cerberus-lean `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`
(`scripts/setup-cerberus-dep.sh --check`: primed, lem-sync stamp verified,
23 hand-written seams byte-identical); Lean 4.32.2; LemLib `045dcb0`. Every
lake/lean invocation under `scripts/capped` with `CERB_MEM_MAX=64G`. The
user was offline for the whole slice: every decision below is [AGENT]
(the L1 worker) unless tagged otherwise; [USER] quotations are copied
verbatim from `docs/DECISIONS.md` (the 2026-09-07 rulings entry). Quoted
outputs are verbatim; derived tallies are labelled DERIVED. Inputs: the
charter, `docs/2026-09-07_branch-landability-assessment.md`, the E5
extension audit `docs/2026-09-07_landability-dialect-e5-extension.md`
(its §10 fixes R-1..R-7 = this slice's work list), and the branch's own
records (`2026-09-05_e5-notes.md`, `…_e5-resume.md`, `…_e5-t6-notes.md`,
`…_e5-t4-notes.md`, `2026-09-06_e5-t4-{condition,addition,body,loop}.md`,
`2026-09-05_fragment-closure-e5-notes.md`).

This record is commit 3 of 3 (docs-only). The FULL gate ran at commit 2's
head `d29f2b5` (§8); this commit changes no Lean content, so the gate's
verdict stands for the landing head.

## 1. What was taken — the source commits, rebased onto main (hashes)

The 21 commits of `dialect-e5` past main's base (c2ebeb7) were rebased onto
main; ONE was dropped as empty after the DECISIONS restore (§2); TWO landing
commits follow. Source hash → landed hash (subject), DERIVED by `git log
--reverse` on both sides, matched by subject:

| source (`dialect-e5`) | landed (`land/e5-complete`) | subject (abridged) |
|---|---|---|
| abb9c4b | — DROPPED (DECISIONS-only; empty after the restore) | DECISIONS: [USER] E1–E4 merged at 8eeaf92; E5–E7 approved … |
| aec1c75 | 8d20227 | E5 (1/2): the negative-action protocol mirrored, supplies as writers, bound rules made sound — FAST-GATE |
| f508ef4 | 1d50b6f | E5 (1/2) pins + manifest: 60 trio-exact pins (652 → 712) … |
| b36ebf2 | 9e3538b | E5 (1/2) record: the slice-1 notes … Docs-only. |
| 09a89c7 | a4ae570 | E5 (2/2) a: the WP-level supply floor, the negative-action protocol's rule faces at both strata — FAST-GATE |
| f63f22d | 5c18b56 | E5 (2/2) PARK record … Docs-only. |
| f433820 | 7eb8c31 | DECISIONS: [AGENT] E5 PARKED … KNOWN-OPEN-ITEMS state line + C19 (its DECISIONS hunk dropped; KOI hunk kept) |
| 405261b | 85fe7ef | E5: transcribe t5 and prove complete fragment membership (fast-gate) |
| 1d04dd7 | 62eecd1 | E5: certify emitted t5 through the shipped driver; full gate green |
| 4970bc1 | 9c7c04f | docs: draft demo completion charter for explicit goal adoption (its DECISIONS hunk dropped) |
| 7a1ea1f | 7e22c97 | docs: adopt demo completion charter under active user goal (its DECISIONS hunk dropped) |
| db3967f | a0429f5 | E5: transcribe t6 switch and prove whole-term membership (fast-gate) |
| 41bee5d | fe9f2e0 | E5: certify emitted t6 switch through the shipped driver; full gate green |
| 68bc8d2 | 36b550e | E5: transcribe t4 while and prove whole-term membership (fast-gate) |
| ef0255e | 9f22029 | E5: share emitted load proof and check t4 continuations; full gate green |
| c086678 | 37ea347 | E5: prove t4 short-circuit condition through annotated binding; full gate green |
| 4f06efc | 0eff99d | Prove t4 emitted additions with exact read footprints; full gate green |
| 12a37f9 | 6156b80 | Prove t4 assignments and loop body; full gate green |
| f60cdcf | 0d372a6 | Certify t4 emitted while through the shipped driver; full gate green |
| 7191dec | 2ab48d1 | docs: prepare full E5 range review and partial API disposition proposal (its docs file removed at 4b2bcce) |
| cb46e4c | 7952c9c | docs: record current dependency and fuel contracts for the next scout (its docs file removed at 4b2bcce) |
| — | 4b2bcce | L1 landing (1/3): DECISIONS restored to main's file exactly; process docs removed; provenance edits. Docs-only. |
| — | d29f2b5 | L1 landing (2/3): census snapshot; record truth; hygiene — FAST-GATE (the FULL gate of §8 ran here) |
| — | this commit | L1 landing (3/3): this record. Docs-only. |

The rebase (`git rebase main` at main = 901ef50) conflicted ONLY on
`docs/DECISIONS.md`, sixteen times (every commit that had appended to it);
each was resolved by taking main's file (`git checkout --ours`); the one
commit that became empty was skipped. Verified after the rebase: `git diff
main -- docs/DECISIONS.md | wc -l` = 0; the tree differs from the pre-rebase
tree ONLY in main's own L0 files (`git diff --stat <pre> HEAD` excluding
DECISIONS and the four `docs/2026-09-07_*` files: empty).

Lean content taken from the source, unchanged except by §6's relocations:
`Substitution.lean`, `Examples/CorpusE5.lean`, `Examples/EmittedInt.lean`,
`CorpusT5Exhibit.lean`, `CorpusT6Exhibit.lean`, `CorpusT4Exhibit.lean`
(new); the E5 slice-1/2a changes to Step/Round/Soundness/DriverCollapse/
ProdEntry/ProdLoop/Wps/Wpt/Rules/EnvLaws/Potential/Adequacy/API/Audit and
the exhibits; the instruments (`capability_manifest.lean`,
`corpus_skeleton.lean`, `module_classes.tsv`); the shop-window docs
(README ×2, ARCHITECTURE, CLAIMS, CAPABILITY_MANIFEST, KNOWN-OPEN-ITEMS);
the records of the code (§2 lists the one judgment call).

## 2. What was NOT taken, and why (charter §0)

- **`docs/DECISIONS.md`**: restored to main's content exactly (`git show
  main:docs/DECISIONS.md`; delta 0 lines). The branch's SIXTEEN entries stay
  on the parked branch: the other agent's fourteen `## date — title`
  build-log entries ("Resume E5 and establish the demo acceptance target",
  "E5 t5 execution checkpoint", "Draft a charter for long-cycle demo
  completion", "User adopts the demo completion charter as an active goal",
  "t6 complete-term membership checkpoint", "t6 shipped-driver checkpoint",
  "t4 whole-term membership checkpoint", "Shared emitted load proof and t4
  label-registration checkpoint", "t4 controlling-expression proof and
  annotated strong binding", "t4 additions and exact read footprints", "t4
  assignments and body through the back edge", "t4 complete loop and
  shipped-driver checkpoint", "E5 full range review prepared, dispatch
  pending", "Dependency/fuel preflight while E5 review is pending") AND the
  two ORCHESTRATOR entries that existed only on `dialect-e5`:
  `- **2026-09-05 [USER] E1–E4 MERGED (main 8eeaf92); E5–E7 APPROVED**` and
  `- **2026-09-05 [AGENT] E5 PARKED ON dialect-e5 (f63f22d …)**`. **FLAG for
  the orchestrator's L1 entry**: main's register has NO entry for the E5–E7
  approval ruling or the E5 park (main's only mention: "reassessment before
  E5–E7" in the E4 audit entry) — the L1 entry should carry them (they are
  at `dialect-e5:docs/DECISIONS.md`, and the R6 confirmation is already on
  main).
- **Process documents removed** (they remain on the parked branch):
  `docs/2026-09-05_demo-completion-charter.md`,
  `docs/2026-09-06_e5-range-review-brief.md`,
  `docs/2026-09-06_dependency-fuel-preflight.md`. The brief also named
  `docs/2026-09-06_dependency-fuel-scout.md`: no such file exists on the
  branch (nothing to remove).
- **KEPT — `cerberus-heaplang/docs/2026-09-05_e5-resume.md`** [AGENT]: read
  in full; it is a MIXED document whose second half is the ONLY record of
  the t5 checkpoint's code (budget 88 and its decomposition, the census
  136/2/17 with the e5b snapshot and the e5b axiom dump as its evidence,
  779 pins, the RULE-PARTIAL-UNDEMONSTRATED manifest class and why, the
  FULL gate tail at 1d04dd7, the manifest/skeleton counts). It is cited by
  five generated manifest rows (`capability_manifest.lean:340–359`) and by
  KOI C19. Taken as the t5 record; its process parts (the
  `[USER, this session]` quotation, the build-command correction, the
  forward plan) are handled by the provenance edit of §3 — not deleted, so
  the record stays whole and honest about what it was.
- Not touched by this slice (charter §0: they are not L1's): the
  `demo-repin` content (L2–L4), E6/E7 (parked, R5), the seven
  RULE-PARTIAL-UNDEMONSTRATED faces (the audit's R-5; C19 records the
  disposition class), the audit's optional R-7 (a program-derived supply
  bound instead of the numeral 600 — a statement change, outside a landing).

## 3. Provenance edits (audit §1 / R-1)

Grep of the whole branch (`*.md`, `*.lean`, `*.txt`, `*.sh`; `.lake`,
`.cerberus-ws` excluded) BEFORE the edits:

- `already authorized` → 1 hit, `docs/DECISIONS.md:3143` (the other agent's
  "Draft a charter" entry). Gone with the DECISIONS restore. 0 hits after.
- `paraphrase` → 1 provenance hit, `docs/DECISIONS.md:3166` (`[USER,
  paraphrase] Standing permission to request an early exit …`). Gone with
  the restore. The other 8 hits are pre-existing prose uses of the word in
  the 2026-09-03/04 review records (not provenance tags). 0 provenance hits
  after.
- `[USER` lines ADDED by the branch in non-DECISIONS files (`git diff main`
  restricted to `+` lines): `cerberus-heaplang/docs/2026-09-05_e5-notes.md`
  and `…_fragment-closure-e5-notes.md` — the orchestrator's own worker's
  provenance legend ("[USER] = operator ruling quoted from
  docs/DECISIONS.md"), kept; `cerberus-heaplang/docs/2026-09-05_e5-resume.md`
  `[USER, this session]: "Yes, please work on E5 & beyond …"` — the other
  agent's quotation, unverifiable (the auditor: "I cannot verify the
  quotation"); `docs/2026-09-05_demo-completion-charter.md` (three `[USER]`
  lines) — removed with the file.
- **Edit, e5-resume.md "Authorization and scope"**: the quotation is
  REPLACED by a labelled `[L1 landing note, 2026-09-07, AGENT]` paragraph:
  the record is the t5 record of the code; the resume instruction as the
  other agent recorded it stays with its DECISIONS entry on the parked
  branch; the operator confirmed the resume — [USER 2026-09-07], verbatim
  from the register's rulings entry: "R6 - yes, I approved this, you can
  mark it as such"; "the charter"/"the demo stop-state" in the record
  refer to the other agent's process document on the parked branch; the
  acceptance interpretation that follows is that agent's own [AGENT]
  reading, not a ruling.
- **Six retained records** that say "the charter" / "the active
  demo-completion goal" / "This checkpoint continues the active goal"
  (`2026-09-05_e5-t6-notes.md`, `2026-09-05_e5-t4-notes.md`,
  `2026-09-06_e5-t4-condition.md`, `…-addition.md`, `…-body.md`,
  `…-loop.md`): ONE labelled `[L1 landing note, 2026-09-07, AGENT]` line
  each, inserted under the title, re-pointing to the parked branch by name
  and stating those scope sentences are [AGENT] readings, not rulings. Their
  own text is untouched.
- **README.md (root) :16–18**: the link to the deleted charter ("active
  under the user's explicit goal") → the landing charter
  `docs/2026-09-07_landing-charter.md` (on main since L0) + the parked
  branch by name.
- **KNOWN-OPEN-ITEMS state line**: "branch `dialect-e5` is resumed with user
  authorization … Current execution goal: docs/2026-09-05_demo-completion-
  charter.md" → the L1 candidate state (§5).
- The other agent's `[USER]` claims INSIDE its DECISIONS entries (the
  "already authorized" two-part goal, the paraphrased permission, the resume
  quotation) are not reworded — they are not on this branch; the parked
  branch is their record, and the E5 extension audit §4 is the adjudication.

## 4. Census (audit §2 / R-2)

Snapshot: `cerberus-heaplang/docs/2026-09-07_l1-signatures-post.txt`
(`scripts/signature_snapshot.lean` at the landing head's Lean content,
30.6 s wall, 47 085 lines / 4950 entries). Pre = slice 1's post
`2026-09-05_e5-signatures-post.txt` (4584). Method: the E5 extension
auditor's `census.py` (its Appendix A.2, run verbatim). Verbatim:

```
PRE 4584 entries; POST 4950 entries; ADDED 368 / REMOVED 2 / CHANGED 18
ADDED by kind: {'opaque': 4, 'def': 153, 'theorem': 211}
REMOVED: ['CerberusHeapLang.procCtxF_runState', 'CerberusHeapLang.procCtx_runState']
CHANGED: ['CerberusHeapLang.eo_wp_readout', 'CerberusHeapLang.fr_wp_readout', 'CerberusHeapLang.load_atomic', 'CerberusHeapLang.negFree.eq_def', 'CerberusHeapLang.wps_sound', 'CerberusHeapLang.wps_sound_cps', 'CerberusHeapLang.wps_sound_empty', 'CerberusHeapLang.wps_sound_frame', 'CerberusHeapLang.wps_sound_frame_empty', 'CerberusHeapLang.wpt_driver_aux', 'CerberusHeapLang.wpt_driver_cps', 'CerberusHeapLang.wpt_driver_done', 'CerberusHeapLang.wpt_driver_done_alloc', 'CerberusHeapLang.wpt_driver_done_procs', 'CerberusHeapLang.wpt_sound', 'CerberusHeapLang.wpt_sound_cps', 'CerberusHeapLang.wpt_sound_empty', 'CerberusHeapLang.wpt_step_eq']
```

Cross-checks (DERIVED):

- At the PRE-HYGIENE tree (Lean content = cb46e4c, taken before §6's
  edits; scratch snapshot, not committed): `ADDED 372 / REMOVED 2 / CHANGED
  18`, `ADDED by kind: {'opaque': 4, 'def': 155, 'theorem': 213}` — the
  auditor's numbers REPRODUCED exactly; e5b → that tree: `236 / 0 / 1`,
  `CHANGED: ['CerberusHeapLang.load_atomic']` — reproduced.
- Landing head vs the auditor's: ADDED 368 = 372 − the four deleted
  aliases (`t5IntMval`, `t5IntBytes`, `t5Int_encodes`, `t5Int_storable`,
  §6); REMOVED and CHANGED identical. The 17 changed besides `load_atomic`
  and the 2 removed are the PARK's slice 2a (09a89c7 → a4ae570), exactly
  the park record's §S2.2 list.
- Pre-hygiene tree → landing head: `ADDED 0 / REMOVED 4 / CHANGED 8`; the 8
  = `wpt_t5AssignBlock`, `wpt_t5If`, `wpt_t5Return`, `wpt_t6AssignStmt`,
  `wpt_t6Break`, `wpt_t6Case2`, `wpt_t6Return`, `wpt_t6Switch` — INTERNAL
  lemmas whose printed statement now spells `emittedIntBytes` /
  `emittedIntMval` where it spelled the deleted reducible aliases
  (`abbrev t5IntBytes := emittedIntBytes`): definitionally identical,
  textual only. No exported statement's text changed by the landing.
- Headline statements vs slice-1 post, all `SAME`: `t1_certified_production`,
  `exhibitA_prod`, `fib_rec_certified`, `even_odd_certified`, `MemTriple`,
  `project_triple_pure`, `DriverSafeCtl`, `DriverDoneCtl`,
  `prod_run_eqJ_lib1`, `wps`, `wpt`, `Frag`, `Step`, `procCtx`, `prodCtx`,
  `loop_step_frag`, `engine_step_matchU`; `t5/t6/t4_certified_production`
  `NEW`; the relocated `t1sym_eval`, `prod_two_int_budget_fits` `SAME`.

**`load_atomic` — the range's only pre-existing statement-text change**
(a strengthening: the delivered value's footprint is the concrete
`loadFootprint M.tagDefs pv ty` instead of `∃ fp`; the reason is in
`2026-09-06_e5-t4-addition.md` — the read/read race check of `s + i`;
`wp_load`/`wps_load`/`wpt_load` texts unchanged, they re-introduce the
existential). Verbatim from the two snapshots, the postcondition:

BEFORE (slice-1 post):
```
      iprop(∃ fp,
          ⌜w =
                CerberusHeapLang.SpikeVal.annot [DA_pos [] fp]
                  (CerberusHeapLang.loadedVal M.tagDefs pv ty bs)⌝ ∗
            pv ↦c[M.tagDefs]{dq} ty ; bs)
```
AFTER (landing head):
```
      iprop(⌜w =
              CerberusHeapLang.SpikeVal.annot
                [DA_pos [] (CerberusHeapLang.loadFootprint M.tagDefs pv ty)]
                (CerberusHeapLang.loadedVal M.tagDefs pv ty bs)⌝ ∗
          pv ↦c[M.tagDefs]{dq} ty ; bs)
```
(the binder list and the `cellLoadTrap … = false →
AtomicStep M ctl (loadExpr a loc ann ty pv mo) ρ 2 (pv ↦c[M.tagDefs]{dq} ty ; bs)`
prefix are identical in both.)

Pins: `export pins: 893 trio-exact` (the source's 896 − the two alias
theorems − the generated `.eq_def`, §6). Package warnings 48 = the
baseline (Potential 31, Round 7, Rules 2, Heap 2, EnvLaws 2, TreeRot/
Struct/Soundness/ProdLoopExhibit 1) — the landing introduced none.

## 5. Record truth (audit §3 / R-3) — every line changed

**Measurements first (re-done at the landing head, not copied).** The
auditor's `probe.lean` (its Appendix A.1, run verbatim: `lake env lean
--load-dynlib=libcf.so probe.lean` under `capped`, `libcf.so` = the
workspace's `CerberusFresh.c.o.export` + `native/md5.c`; 2.2 s wall), with
one addition (`t6 sup=0`). Verbatim:

```
"t5Main: first fl with the inner loop ACTIVE (PROGRAM-DONE) = 69; verdict@68 = killed:Error0:lem: fuel exhausted; verdict@67 = killed:Error0:lem: fuel exhausted; verdict@69 = active; verdict@300 = active"
"t6Main: first fl with the inner loop ACTIVE (PROGRAM-DONE) = 67; verdict@66 = killed:Error0:lem: fuel exhausted; verdict@65 = killed:Error0:lem: fuel exhausted; verdict@67 = active; verdict@300 = active"
"t4Main: first fl with the inner loop ACTIVE (PROGRAM-DONE) = 593; verdict@592 = killed:Error0:lem: fuel exhausted; verdict@591 = killed:Error0:lem: fuel exhausted; verdict@593 = active; verdict@1500 = active"
"t5 sup=600: active; value==lint 1: true; ==lint 20: false; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t6 sup=600: active; value==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t4 sup=600: active; value==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''"
"t5 sup=0: active; value==lint 1: true; ==lint 20: false; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t6 sup=0: active; value==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t4 sup=0: active; value==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''"
```

DERIVED slack (KOI B6's convention: the driver theorem delivers
PROGRAM-DONE within `k + 2` inner-loop iterations): t5 88 → 90 vs 69 =
**21**; t6 78 → 80 vs 67 = **13**; t4 915 → 917 vs 593 = **324**. The
`600 ≤ sup` premise is SUFFICIENT, not necessary: all three composites
deliver the theorems' readouts at `sup = 0` (one run each; no theorem —
the auditor's §12 caveat stands).

Erratum (2026-09-07, E5 full-range audit D-2): "sufficient, not necessary"
is literally right but under-reads the floor — it is NOT vacuous. At a
`sup` from which the run's fresh-symbol draws reach a source symbol's
number the composite is KILLED (`killed:Undef0`, after LemLib
`can_advance: Step_error2 ==> Kill`/`Load` panics): t5 at 505/506 (x/r), t6
at 509/510 (x/r; it still delivers at 505/506), t4 at 505/506/508/509
(i = 508, s = 509) — measured at the fixes (the "E5 full-range audit fixes"
section below, verbatim). The half-sentence is added on README, KOI B6,
ARCHITECTURE and the three production docstrings.

**`docs/KNOWN-OPEN-ITEMS.md`** (line numbers at the landing head):

- lines 3–11 — the STATE LINE (was: "main has E1–E4; branch `dialect-e5`
  is resumed with user authorization … the decreasing loop invariant and
  exit/return proof are next … Current execution goal: docs/2026-09-05_
  demo-completion-charter.md", false at HEAD since f60cdcf): now the L1
  candidate state — E5 complete (t5/t6/t4 certified through the shipped
  driver at the pin f95ef8d9c), re-cut per the landing charter §2 L1, the
  process docs and DECISIONS entries on the parked branch, this record as
  the pointer; then the pre-existing "before it" clause.
- line 41 — **B6**: APPENDED "Same class, E5 (measured at the L1 landing by
  executable run …): `t5_wpt`'s budget 88 (`k + 2 = 90`) against
  PROGRAM-DONE at inner-loop fuel 69 — 21 units; `t6_wpt`'s 78 (80) against
  67 — 13; `t4_wpt`'s 915 (917) against 593 — 324, the largest in the
  package …; the docstrings say the bounds are sufficient, not tight.
  Measured there too: the three production theorems' `600 ≤ sup` is a
  SUFFICIENT floor, not a necessary one — the composite delivers the same
  values at `sup = 0`." Where-column: "+ L1 landing notes §5".
- line 52 — **B18 (NEW)**, the R3 row: "**The seeded profiles normalise
  the run-state supplies to `⟨0,0⟩`** (`procCtx`/`procCtxF`,
  `Step.lean:6315`/`:6363` …; only `prodCtx` (`ProdEntry.lean:585`) retains
  the initial supply …). ACCEPTED as an INERT limitation ([USER 2026-09-07],
  the landing charter's R3, verbatim in DECISIONS: "R3 - okay so this is a
  limitation we will have to lift later, but here is inert? Sure that's
  fine")." Mover: "Lift when a seeded exhibit needs a non-zero supply (a
  supply premise on the seeded profile, or the `prodCtx` re-context — B1's
  slice)."
- line 77 — **C19** REWRITTEN to the landed state: E5 COMPLETE at L1; the
  budgets and the sufficient floor (→ B6); the park's slice-2 debts paid
  except the seven RULE-PARTIAL-UNDEMONSTRATED faces (the audit's R-5
  class, not blocking) and `seq_rmw`/`PtrValidForDeref`/`Elet` (dialect
  list; `seq_rmw` = L4); hygiene done at the landing (§6) and the residual
  client→client imports queued with C17; `cite_check`'s manual queue
  disclosed; A7 unchanged. Where: this record + the t5/t6/t4 records +
  the audit. Disposition: the L1 range audit and merge ask are the
  orchestrator's.
- NOT changed (flag): §E's "Expected FULL tail at the E4 candidate: 652
  pins …" is stale-but-labelled (E4) and was not on the brief's list; the
  landing head's tail is §8 here. A6's "Re-pin waits for the NEXT
  cerberus-lean pin" is L2's edit (R1 ruled the pin 89f7e68).

**`cerberus-heaplang/README.md`**: :228–233 "It requires an initial symbol
supply of at least 600 to protect source bindings …" → "Its premise `600 ≤
sup` is a SUFFICIENT floor — above every source symbol number … — not a
necessary one: the compiled composite delivers the same result at `sup = 0`
(measured …; the budgets' slack is in KNOWN-OPEN-ITEMS B6)"; :358–359 "with
the explicit bound `600 ≤ sup`" + "— a sufficient floor, not a necessary
one"; :570 (the exhibits table row) the premise cell gains "(a sufficient
floor, not necessary: the composite delivers the same values at `sup = 0`,
measured at the L1 landing)".

**`cerberus-heaplang/ARCHITECTURE.md`**: :135–138 "Its initial symbol
supply is explicitly at least 600." → the sufficient-not-necessary sentence
with the measurement pointer; :144–148 "All three use the supply floor of
600 … E5's full range audit remains pending." → "carry the sufficient floor
`600 ≤ sup` …; E5 landed as L1 of `docs/2026-09-07_landing-charter.md`
(record …); its full range audit (8eeaf92..the L1 head) is owed at the L1
merge boundary."; :176–178 "This seeded-profile definition change remains
an E5 range-audit item." → "ACCEPTED as an inert limitation ([USER
2026-09-07], the landing charter's R3; KNOWN-OPEN-ITEMS B18 — lift when a
seeded exhibit needs a non-zero supply)."; :487–490 the §2.5 table rows:
`CorpusT1Exhibit.lean:832` → `:803` (moved by §6's deletions;
`cite_check.sh --fix`), and the three E5 rows gain their line cites
`CorpusT5Exhibit.lean:548`, `CorpusT6Exhibit.lean:618`,
`CorpusT4Exhibit.lean:1429` and the premise `hsup : 600 ≤ sup` "a
sufficient floor, not necessary (… measured)".
`cite_check.sh` run LAST, verbatim summary:
`cite-check: ARCHITECTURE.md — 280 cites; EXACT 179; DECL 52 (fixed 0; ranges among them counted in RANGE); USE 19; HAND 21; PIN 9; NOFILE 0; RANGE 25 (never rewritten)`
(before the landing's edits the auditor measured 277 / 176 / 52 / 19 / 21 /
9 / 0 / 25: +3 EXACT cites, the T1 cite fixed; the 52-DECL/21-HAND/25-RANGE
manual queue is the pre-existing one, disclosed, not cleared).

**`cerberus-heaplang/docs/CLAIMS.md`** :48–50 (C15, C16, C17, the
"Not claimed / limits" cell): "requires initial symbol supply at least 600"
/ "Initial symbol supply at least 600" → "the supply premise `600 ≤ sup` is
a sufficient floor, not a necessary one (measured …)". The generator's
D-2 span check (every backticked span of every cell) is unaffected: `600 ≤
sup` is not declaration-shaped; no `hsup`/`sup` span was introduced there.

**The three theorem docstrings** (`t5/t6/t4_certified_production`) say
the same: "The premise `600 ≤ sup` is a SUFFICIENT floor …, not a necessary
one: the compiled composite delivers the same result at `sup = 0`
(measured, docs/2026-09-07_l1-landing-notes.md)".

## 6. Hygiene (audit §7 / R-6) — done, and what remains

Relocations only; no proof text changed; every moved declaration keeps its
name and statement (census-neutral: the snapshot records no module).

- **`Examples/EmittedInt.lean` (example-support) imported a CLIENT**
  (`CorpusT1Exhibit`). Now: `import Examples.CorpusE0`, `IntRules`, `Wpt`,
  `ProdEntry` (core / production-core only). Moved INTO it, from
  `CorpusT1Exhibit`: `specInt_eval`, `t1ConvLoadedInt_eval`, `t1sym_eval`,
  `createInt_eq`, `act_store_eq`, `act_load_eq`,
  `prod_two_int_budget_fits`; from `CorpusT5Exhibit`: `t5CmpBranch`,
  `t5CmpBranch_eval`, `t5Tuple_eval`, `t5frAssign`. `CorpusT1Exhibit`
  imports `EmittedInt`. The names keep their `t1`/`t5` prefixes (a naming
  smell; renaming would touch ~40 call sites — not done).
- **`CorpusT4/T6Exhibit` imported the CLIENT `CorpusT5Exhibit`.** Now they
  import `EmittedInt` + `CorpusE5` + `ProdEntry` + the E1–E3 synthetic
  exhibits whose lemmas they use (T6: `EmittedAExhibit` for
  `alignofIntPe_eval`; T4: + `EmittedBExhibit` for `update_env_tuple2`; T5:
  + `EmittedCExhibit` for `threeBytes`) — `CorpusT1Exhibit`'s pre-existing
  import pattern (on main since E4: it imports `AllocExhibit`,
  `EmittedAExhibit`, `EmittedCExhibit`). The first two build attempts
  failed on exactly these transitive names (my dependency analysis had
  covered T5's own declarations, not T1's transitive closure); the fix was
  the explicit imports above — recorded as the RESIDUAL client→client
  pattern in KOI C19 (queued with C17: the shared E1–E3 lemmas belong in
  example support too; out of L1's range).
- **Aliases** `t5IntMval`/`t5IntBytes`/`t5Int_encodes`/`t5Int_storable`
  DELETED; T5 (5 sites) and T6 (21 sites) use the `emittedInt*` names.
- **`trioExports`**: the two alias theorems and the dependency's GENERATED
  equation lemma ``subst_sym_pexpr_lemFuel.eq_def`` (realised in
  `Substitution.lean` by `unfold`; not a package export) removed, with a
  comment in Audit.lean; the exhaustive sweep still bounds it (it is "ours"
  by module). 896 → 893 pins.
- **Axiom dumps**: the stray `cerberus-lean-proj env: …` stderr banner
  stripped from line 1 of `docs/2026-09-05_e5-t6-execution-axioms.txt`; the
  e5b dump had none (the auditor's "two" was one — measured by grep).
- Build cost: the capped `lake build` after the edits recompiled 7 modules
  (EmittedInt 0.9 s, T1 1.7 s, T5 2.1 s, T6 2.5 s, T4 3.4 s, Audit 1.9 s,
  the root) in 7.6 s wall; far under any tripwire.
- Not done: the two `local macro`s duplicated across T5/T6/T4
  (`t5_frame`/`t5_lookup`-style tactics), the remaining generic-helper
  relocation the other agent's records list, and the DECISIONS "bullet
  style" item (moot: those entries are not landed).

## 7. The OCaml oracle — re-run at the landing (verbatim)

`cd /home/dev/projects/cerberus-lean-proj && scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc <mode> refined-cerberus/worktrees/land-e5/docs/corpus-e0/<t>.c`
(`scripts/ce`'s env banner and `Time spent` lines elided; exit codes from
`PIPESTATUS`):

```
=== t5_ifelse --exec --batch
Defined {value: "Specified(1)", stdout: "", stderr: "", blocked: "false"}
exit=0
=== t5_ifelse --exec
exit=1
=== t6_switch --exec --batch
Defined {value: "Specified(20)", stdout: "", stderr: "", blocked: "false"}
exit=0
=== t6_switch --exec
exit=20
=== t4_while --exec --batch
Defined {value: "Specified(10)", stdout: "", stderr: "", blocked: "false"}
exit=0
=== t4_while --exec
exit=10
```

The binary `cerberus-lean/_build/default/backend/driver/main.exe` is dated
`2026-09-05 19:47` — the mainline build the park record §S2.6 and the E5
extension audit §1.4 used (the cerberus-lean primary is at `89f7e6885`);
NOT the pin `f95ef8d9c` — the standing caveat of every E4/E5 record. The
values agree with the three theorems' readouts (`lint 1`/`lint 20`/`lint 10`,
`dres_blocked = false`, empty streams) and with §5's compiled-composite runs.

## 8. The FULL gate — verbatim verdict lines at d29f2b5

`CERB_MEM_MAX=64G scripts/test_unit.sh` from the worktree root at
`d29f2b5eed4c12a5c4cf732a6faf981dcdd4ac33` (commit 2 of 3; this record's
commit changes no Lean content), Lean 4.32.2, pin `f95ef8d9c`. 16.4 s wall:
gate 2 REPLAYED the artefacts of §6's fast build (identical content; the
recompilation of the 7 changed modules happened there, 7.6 s). Every line
matching `^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE-EXIT|^Build
completed|^BOUNDARY|^ALLOWLISTED|^FAIL`, unmodified and complete (the
per-module `ok:` lines included):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1066:0: CerberusHeapLang export pins: 893 trio-exact
info: CerberusHeapLang/Audit.lean:1066:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6051 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1066:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9141 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (472 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 18 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ok:   Exhibit — 0 internals mentions
ok:   LoopExhibit — 0 internals mentions
ok:   FibExhibit — 0 internals mentions
ok:   ArrayExhibit — 0 internals mentions
ok:   ListRevExhibit — 0 internals mentions
ok:   TreeRotExhibit — 0 internals mentions
ok:   CaseExhibit — 0 internals mentions
ok:   WseqExhibit — 0 internals mentions
ok:   StructExhibit — 0 internals mentions
ok:   AllocExhibit — 0 internals mentions
ok:   DisposeExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
ok:   MallocListExhibit — 0 internals mentions
ok:   FibRecExhibit — 0 internals mentions
ok:   TwoLabelExhibit — 0 internals mentions
ok:   EvenOddExhibit — 0 internals mentions
ok:   EmittedAExhibit — 0 internals mentions
ok:   EmittedBExhibit — 0 internals mentions
ok:   EmittedCExhibit — 0 internals mentions
ok:   CorpusT1Exhibit — 0 internals mentions
ok:   CorpusT5Exhibit — 0 internals mentions
ok:   CorpusT6Exhibit — 0 internals mentions
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
ok:   Examples.CorpusE5 — 0 internals mentions
ok:   Examples.EmittedInt — 0 internals mentions
ok:   CorpusT4Exhibit — 0 internals mentions
BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

Manifest tail (regenerated in the gate, no drift):
`MANIFEST: 35 constructors, 77 variant rows (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 6 OUT-OF-SCOPE), 0 red, 25 consumer modules`;
`CLAIMS: 17 claim rows, 184 declaration names checked in the theorem cell, 341 declaration-shaped spans checked across every cell (45 vocabulary words, 2 retired names); plants (deleted name in a prose cell; retired name without its marker) red as expected`.
Warnings in the gate log: 572 raw lines, 48 from `CerberusHeapLang/*`
(the baseline set, §4); the rest are replayed dependency oleans.

## 9. Deviations and [AGENT] decisions (for the orchestrator's L1 entry)

1. [AGENT] `2026-09-05_e5-resume.md` KEPT as the t5 record (§2), with a
   labelled provenance paragraph replacing the unverifiable quotation (§3).
2. [AGENT] The six retained t4/t6 records received one labelled landing
   note each (§3) instead of being left citing a document not on main.
3. FLAG: the DECISIONS restore drops from this branch the two ORCHESTRATOR
   entries that only existed on `dialect-e5` (the [USER] E5–E7 approval of
   2026-09-05 and the E5 park record's register entry). Main's register
   does not carry the E5–E7 approval ruling; the L1 entry is where it
   should be re-stated (or the two entries cherry-picked as text).
4. [AGENT] Hygiene went one step beyond the brief's "EmittedInt" item: the
   T4/T6 → T5 client imports were also removed (the audit's R-6 named
   them), which required moving eleven declarations and adding the
   explicit E1–E3 exhibit imports (§6); eight INTERNAL statement texts
   changed by the alias rename (§4). Pins 896 → 893.
5. [AGENT] The R3 quotation and the R6 quotation are copied verbatim from
   `docs/DECISIONS.md`'s 2026-09-07 rulings entry (on main since L0), not
   from the operator directly.
6. [AGENT] KOI §E's E4-labelled expected tail left as is (not in the
   brief's KOI list); A6 left for L2.
7. [AGENT] Commit 2 was amended once before the rebase (to include the
   banner strip and correct its message); the rebase then rewrote every
   hash — the table in §1 is the final one.
8. The docs-only commit-1 message says the gate runs "at the landing head
   (commit 3's record)"; it ran at commit 2's head d29f2b5 (§8), which
   commit 3 does not change in Lean content.
9. Not done, by scope: the audit's optional R-7 (a program-derived supply
   bound), R-5 (the partial faces), the residual client→client imports
   (C19/C17), the manual cite queue.

Ephemeral scratch (`worktrees/land-e5/.l1-scratch/`: `census.py`,
`probe.lean`, `libmd5.so`/`libcf.so`, the pre-hygiene snapshot, the build
and gate logs) — deleted at the end of this slice; the recipes are the
auditor's Appendix A, reproduced by the commands stated inline above.

## 10. E5 full-range audit fixes (2026-09-07; the fixes worker — [AGENT] throughout, the user was offline)

Source: `docs/2026-09-07_audit-e5-full-range.md` (this package's docs; the
auditor's report committed VERBATIM at 017054d, `cmp`-identical to the
detached copy). R-1 (the DECISIONS register) was fixed by the orchestrator
at db46800 and is not touched here. The fixes are commit 6edb0f5; this
section is the third commit (docs-only). Worktree `worktrees/land-e5`,
branch `land/e5-complete`, pin `f95ef8d9c` unchanged, Lean 4.32.2; every
lake/lean invocation under `scripts/capped` with `CERB_MEM_MAX=40G`
(another heavy build was running). No pass approached the tripwire (the
one rebuild: `1:15.11 total`).

### 10.1 Disposition table

| id | done | where | verified against |
|---|---|---|---|
| C-1 (MEDIUM) | DONE | `scripts/capability_manifest.lean`: a second `Frag.neg_store` row, OUT-OF-SCOPE, for `BOUND_WITH_SSEQ` (the mover from the closure record); `docs/CAPABILITY_MANIFEST.md` regenerated — the diff is exactly the row and the tail line (77 → 78 rows, 6 → 7 OUT-OF-SCOPE); ARCHITECTURE §2.2 ("three arms" + a `neg_sseq` sentence), §6 ("Seven OUT-OF-SCOPE variants", listing `nd` and the WITH_SSEQ action; "three arms" naming `neg_sseq`); KOI B7 | `Round.lean:383`–`:453` (`OpenRound`; `neg_sseq` at `:448`), `docs/2026-09-05_fragment-closure-e5-notes.md` row 3 (the mover), the gate's manifest speedbump (no drift) |
| R-2 (MEDIUM) | DONE | KOI B7 rewritten to the truth; `../docs/2026-09-05_note-cerberus-lean-subst-esize.md` dated erratum appended | `Soundness.lean:1224` `esize_subst` (from `esize_subst_lemFuel` `:1137`), `:1240` `esize_subst_fold`, `:1350` `ccallFree_subst`, `:1675` `negFree_subst`, `:1385` `case_hbsz_of_branches`; `Potential.lean:514` `pot_subst`; the `hbsz` premises at `Soundness.lean:9552` (`case_value`) and `:9637` (`case_op`) |
| D-1 (MEDIUM) | DONE | ARCHITECTURE: §1 "35 constructors (`:9369`–`:9645`; dialect arc E5)" + the six E5 kinds; §3 "893 exact pins" with the 896 − 2 aliases − 1 `.eq_def` derivation; the glossary's *a tie*, §2.4 (both lanes, `DriverDoneAt`'s `sp`) and §4's export reading state the SUPPLY TIE; the E5 prose in the present tense with the range `901ef50..the L1 head`; WALKTHROUGH §1.1's `DriverSafeCtl` re-printed VERBATIM from `Adequacy.lean:945` (the supply tie, `lcfin`/`spfin`/`afin bfin`, `ofValA`), the prose after it and §1.3 name the supply tie; KOI C19's range | `awk` over `inductive Frag` = 35 arms; the gate line `export pins: 893 trio-exact`; `Adequacy.lean:954`–`:955`, `ProdLoop.lean:493`, `:60`/`:69` |
| D-2 (NOTE) | DONE | README :228–233 and the exhibits-table row; KOI B6; ARCHITECTURE's E5 prose; the three production docstrings (t5 `sup = 505`, t6 `sup = 509`, t4 `sup = 508`); this record's §5 erratum | the re-measurement, §10.2 |
| D-3 (NOTE) | DONE | `scripts/cite_check.sh --fix` (3 DECL cites rewritten) then a hand-check of the ENTIRE non-EXACT queue | §10.4 |
| H-1 (NOTE) | DONE | `Potential.lean` :14, :46, :176–180, :553–554 (the negative leaf is 10; the breakdown now sums to 10; `pot_negRewrite_le` "exactly (equal potentials)"); `Step.lean:644` `negFreeAlts`'s docstring; KOI C17 lists the E5 duplication additions (not refactored) | `pot_neg : … = 10` (`Potential.lean:181`); `pot_negRewrite_le`'s arithmetic (LHS = 9 + pot(ctxA[pure(Unit)]) = RHS by `pot_apply_ctx_plug`); every C17 name located by grep (`Decomp.lift_neg'` Round.lean:2526, `get_ctx_rebuild_excluded` :2934, `step_ctx_excluded_store_eval_ws'` :4216, …) |
| H-2 (NOTE) | REGISTERED | KOI B19 (new) | audit H-2; landability audit R-7; DECISIONS 2026-09-03 no-magic-values |
| H-3 (NOTE) | REGISTERED | KOI B20 (new) | audit H-3; `e5-notes.md` §S2.4 |
| R-1 (HIGH) | orchestrator's, db46800 | — | §10.3 |

### 10.2 D-2 re-measurement (verbatim)

Recipe = the landability audit's Appendix A.1 (`libmd5.so` from the
workspace's `native/md5.c`, `libcf.so` from its
`.lake/build/ir/CerberusFresh.c.o.export`; `lake env lean
--load-dynlib=… probe_d2.lean` under `capped`, 40G; 2.2 s wall). The
`composite` function is the appendix's with ONE extra match arm,
`.Undef0 → "killed:Undef0"` (the auditor's arm order folded
undefined-behaviour kills into `killed:other`). Every `#eval` line and
every `PANIC` line of the run, in order (the backtrace lines elided):

```
"t5 sup=0: active; ==lint 1: true; ==lint 20: false; ==lint 10: false; blocked=false; stdout=''; stderr=''"
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Kill
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Kill]
"t5 sup=505: killed:Undef0"
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Load]
"t5 sup=506: killed:Undef0"
"t5 sup=600: active; ==lint 1: true; ==lint 20: false; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t6 sup=0: active; ==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t6 sup=505: active; ==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t6 sup=506: active; ==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t6 sup=600: active; ==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t4 sup=0: active; ==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''"
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Load]
"t4 sup=505: killed:Undef0"
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Load]
"t4 sup=506: killed:Undef0"
"t4 sup=600: active; ==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''"
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Kill
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Kill]
"t6 sup=509: killed:Undef0"
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Load]
"t6 sup=510: killed:Undef0"
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Load]
"t4 sup=508: killed:Undef0"
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Load]
"t4 sup=509: killed:Undef0"
```

Reading: t5 is KILLED at 505/506 (x = 505, r = 506); t6 DELIVERS at
505/506 and is KILLED at its own 509/510 (x, r); t4 is KILLED at
505/506/508/509 (i = 508, s = 509 — from 505 its loop's draws cross them);
`sup = 0` and `sup = 600` deliver for all three. Every verdict agrees with
the audit's §4.5; the kill kind is refined from `killed:other` to
`killed:Undef0`, reached after the same LemLib `can_advance: Step_error2
==> Kill`/`Load` panics (a `failwithI` on the driver's `can_advance` path
reached by an ordinary ILLTYPED report — noted on KOI B6 for A5's class).

### 10.3 The provenance grep

`git grep -c -e 'already authorized' -e '\[USER, paraphrase\]' -- .
':!docs/DECISIONS.md'` at 017054d (identical at 6edb0f5: no fix touches
these strings) is NOT 0:

```
cerberus-heaplang/docs/2026-09-07_audit-e5-full-range.md:6
cerberus-heaplang/docs/2026-09-07_l1-landing-notes.md:2
docs/2026-09-07_branch-landability-assessment.md:2
docs/2026-09-07_landability-dialect-e5-extension.md:6
docs/2026-09-07_landing-charter.md:2
```

Every one of the 18 lines (read with `git grep -n`) is a QUOTATION of the
defective strings by a record describing the R-1a/R-1b defect: the landing
charter's fix list, the two landability audits' findings, the full-range
audit's R-1, and this record's own §3 (its grep description). None is a
live provenance tag or a permission grant. [AGENT]: left as they are — they
are the record of the defect. `docs/DECISIONS.md` itself: 2 lines
(`:3172`, `:3218`), both quotations inside the orchestrator's L1 entry and
the db46800 erratum. A note for the record: §3 above says "0 hits after";
that was the tree the L1 worker grepped before writing §3 — the grep now
finds §3's own description of it.

### 10.4 `cite_check.sh` (D-3)

Verbatim summary lines, in order. After the content edits, report mode:
`cite-check: ARCHITECTURE.md — 288 cites; EXACT 185; DECL 54 (fixed 0; ranges among them counted in RANGE); USE 19; HAND 21; PIN 9; NOFILE 0; RANGE 28 (never rewritten)`.
`--fix`: `cite-check: ARCHITECTURE.md — 288 cites; EXACT 185; DECL 54 (fixed 3; ranges among them counted in RANGE); USE 19; HAND 21; PIN 9; NOFILE 0; RANGE 28 (never rewritten)`.
Report after `--fix`: `cite-check: ARCHITECTURE.md — 288 cites; EXACT 188; DECL 51 (fixed 0; ranges among them counted in RANGE); USE 19; HAND 21; PIN 9; NOFILE 0; RANGE 28 (never rewritten)`.
After the hand-check (final, the committed file):
`cite-check: ARCHITECTURE.md — 288 cites; EXACT 226; DECL 20 (fixed 0; ranges among them counted in RANGE); USE 12; HAND 21; PIN 9; NOFILE 0; RANGE 28 (never rewritten)`.

The hand-check read ALL 100 non-EXACT lines of the post-`--fix` queue
against the sources (declaration heads located by grep): 62 cite tokens
rewritten by hand (DERIVED, counted from the edit script) — the audit's six
sampled stale cites among them (:44 `spikeCtx`/`spikeCtl` → `:6302`/`:6278`,
:105 the `Frag` header → `:9286`–`:9367`, :288 `loop_step` → `:1097`, :420
`MemTriple_alloc` → `:1733`, :696 `engine_adequacy` → `:1342`–`:1354`, :713
`Frag.esize_le_pot` → `:308`) — plus the cites inside the content edits
(`OpenRound` `:371` → `:383`, the in-block `-- Round.lean:1111` → `:1163`,
`complete_store`…`complete_ret` `:2719`–`:6484` → `:3202`–`:7301`, `hbsz`
`:8252` → `:9552`/`:9637`, the trio `Audit.lean:213`–`:214` (import lines
at HEAD) → `allowedAxioms` `:250`–`:251`). The remaining 32 DECL/USE lines
are attribution noise on cites measured correct (the script credits a
neighbouring identifier — e.g. `Step.lean:6302` is `spikeCtx`, credited to
`spikeCtl`); the 21 HAND lines were checked and are correct; the 9 PIN
lines are not judged by design. Well under the hour.

### 10.5 The FULL gate — verbatim verdict lines at 6edb0f5

`CERB_MEM_MAX=40G scripts/test_unit.sh` from the worktree root on the tree
committed as 6edb0f5 (the trio-cite edit to ARCHITECTURE.md landed in
parallel with the gate's start — docs-only, read by no gate), Lean 4.32.2,
pin `f95ef8d9c`, exit 0, `14.05s user 1.27s system 102% cpu 14.974 total`:
gate 2 REPLAYED the capped build made after the docstring edits (472 jobs,
`1:15.11 total`, Step.lean onward recompiled; `Build completed successfully
(472 jobs)`). Every line matching
`^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE-EXIT|^Build completed|^BOUNDARY|^ALLOWLISTED|^FAIL`,
unmodified and complete (`GATE-EXIT=0` appended by my wrapper):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1066:0: CerberusHeapLang export pins: 893 trio-exact
info: CerberusHeapLang/Audit.lean:1066:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6051 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1066:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9141 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (472 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 18 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ok:   Exhibit — 0 internals mentions
ok:   LoopExhibit — 0 internals mentions
ok:   FibExhibit — 0 internals mentions
ok:   ArrayExhibit — 0 internals mentions
ok:   ListRevExhibit — 0 internals mentions
ok:   TreeRotExhibit — 0 internals mentions
ok:   CaseExhibit — 0 internals mentions
ok:   WseqExhibit — 0 internals mentions
ok:   StructExhibit — 0 internals mentions
ok:   AllocExhibit — 0 internals mentions
ok:   DisposeExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
ok:   MallocListExhibit — 0 internals mentions
ok:   FibRecExhibit — 0 internals mentions
ok:   TwoLabelExhibit — 0 internals mentions
ok:   EvenOddExhibit — 0 internals mentions
ok:   EmittedAExhibit — 0 internals mentions
ok:   EmittedBExhibit — 0 internals mentions
ok:   EmittedCExhibit — 0 internals mentions
ok:   CorpusT1Exhibit — 0 internals mentions
ok:   CorpusT5Exhibit — 0 internals mentions
ok:   CorpusT6Exhibit — 0 internals mentions
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
ok:   Examples.CorpusE5 — 0 internals mentions
ok:   Examples.EmittedInt — 0 internals mentions
ok:   CorpusT4Exhibit — 0 internals mentions
BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
GATE-EXIT=0
```

Manifest tail (regenerated in the gate, no drift; the committed file):
`MANIFEST: 35 constructors, 78 variant rows (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 7 OUT-OF-SCOPE), 0 red, 25 consumer modules`.
Warnings in the gate log: 572 raw, 48 from `CerberusHeapLang/*` — the
baseline (DERIVED by `grep -c`).

### 10.6 KOI lines changed / added

B6 (appended: the floor is not vacuous, with the measurement and the
`can_advance`-panic mechanism), B7 (rewritten: three arms; `esize_subst`
and its twins proved at the engine's fuel; `hbsz` derivable by
`case_hbsz_of_branches`, kept by choice), B19 (NEW: the numeral `600` vs
the no-magic-values ruling, H-2), B20 (NEW: `wps/wpt_neg_bound` expose
`fresh_given_int`, H-3), C17 (appended: the E5 duplication additions),
C19 (disposition cell: the full E5 range audit done, `901ef50..HEAD`).

### 10.7 For the orchestrator — the DECISIONS L1 entry

The register is the orchestrator's; the replacement text for the L1
entry's "sufficient, not necessary" wording:

> The premise `600 ≤ sup` is a SUFFICIENT floor, not a necessary one (the
> compiled composite delivers the same values at `sup = 0`) — and not a
> vacuous one: at a `sup` from which the run's fresh-symbol draws reach a
> source symbol's number (t5 at 505/506, t6 at 509/510, t4 at
> 505/506/508/509) the composite is KILLED (`killed:Undef0` after LemLib
> `can_advance: Step_error2 ==> Kill`/`Load` panics; measured at the L1
> landing and re-measured at the E5 full-range audit fixes, 6edb0f5).

### 10.8 Deviations and [AGENT] decisions

1. The brief's "WALKTHROUGH :126–150 future tense; :147 range" are
   ARCHITECTURE line numbers (the audit's D-1.5); fixed in ARCHITECTURE.
   WALKTHROUGH's own stale items were the `DriverSafeCtl` print (D-1.4)
   and — found on the same page — "The ten production statements" →
   thirteen, with t4/t5/t6 named (the same defect class, one sentence).
2. ARCHITECTURE §6's "Five OUT-OF-SCOPE variants" was stale before C-1
   (the manifest had six; `nd` was unlisted): now "Seven", listing both.
3. `docs/CLAIMS.md` C15–C17 ("a sufficient floor, not a necessary one")
   left untouched — true as written; the generator's span check makes
   prose edits there a separate care point. ARCHITECTURE received the
   D-2 half-sentence although the brief named README/KOI B6/docstrings
   only (the sentence sat inside the E5 prose being rewritten).
4. C-1 classified OUT-OF-SCOPE, not NO-RULE: the manifest's convention is
   NO-RULE = mirrored but no rule, OUT-OF-SCOPE = no mirror step (the
   `run_surplus`/`eval_uncovered` rows' class); the closure record's row
   says "— (stuck, fail-closed)".
5. The probe reports the kill kind (`killed:Undef0`) the auditor's arm
   order hid; every verdict agrees.
6. Nothing in the brief was left undone.

Ephemeral scratch `worktrees/land-e5/.audit-fix-scratch/` (`libmd5.so`,
`libcf.so`, `probe_d2.lean`, `probe_d2.out`, `build1.log`, `manifest.new`,
`cite_*.tsv`, `gate.log`, `gate.tail`) — deleted at the end of this slice;
the probe is the appendix's recipe with the arm and the sixteen `#eval`
lines shown in §10.2.
