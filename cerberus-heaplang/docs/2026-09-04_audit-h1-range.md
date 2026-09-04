# Range audit `e242342..cd68c46` (hygiene-h1: H1a + H1b + records) — 2026-09-04

**VERDICT: PASS WITH FIXES REQUIRED — A−.** No logical or coverage gap in scope.
Every Lean claim of the range reproduced by measurement (census, pins, cones,
manifest, boundary, the two exhibits executed on the shipped loop). The fixes
required are three record-integrity corrections (a KNOWN-OPEN-ITEMS entry that
is now false, a KNOWN-OPEN-ITEMS entry that undercounts, an ARCHITECTURE
enumeration that omits a module of this range) and two new linter warnings.

Auditor: fresh, independent (not the worker, not the orchestrator, not the
ARCHITECTURE reviewer). Copy: `worktrees/audit-h1-cd68c46`, detached at
`cd68c46`. Every Lean invocation through `scripts/capped` with
`CERB_MEM_MAX=64G`; no other worktree, the primary checkout or `main` touched;
nothing committed. Brief: `docs/AUDIT-BRIEF.md`; register read first:
`docs/KNOWN-OPEN-ITEMS.md` (nothing there is re-cited below except where the
entry is now wrong). Longest single pass: the FULL gate at 8.97 s wall
(primed tree; Lake replayed the cached build logs) — nothing approached the
tripwire. Scratch lives in `.lake/audit-logs/` (ignored; deletable).

Tallies marked DERIVED are derived; every quoted block is verbatim.

---

## Findings (ranked)

### H-1 (Hygiene, in-range): TWO NEW linter warnings in `EvenOddExhibit.lean`; KNOWN-OPEN-ITEMS C5 ("zero added since") is now false

Evidence (gate log, verbatim lines):
```
CerberusHeapLang/EvenOddExhibit.lean:311:34: Variable name `h` is not explicitly referenced.
CerberusHeapLang/EvenOddExhibit.lean:314:33: Variable name `h` is not explicitly referenced.
```
`EvenOddExhibit.lean:311`/`:314`: `theorem eo_parity_even {n : Int} (h : 1 ≤ n) : ivVal ((n - 1) % 2) = ivVal (1 - n % 2)` and `eo_parity_odd` — the identities hold for EVERY `Int` (`Int.emod` by 2 is 0 or 1), `omega` never uses `h`. DERIVED tally of `warning: CerberusHeapLang/` lines in the gate log: 64 (Potential 50, Round 3, Rules 2, Heap 2, EnvLaws 2, ProdLoopExhibit 1, StructExhibit 1, TreeRotExhibit 1, **EvenOddExhibit 2**); the C3 audit's baseline of 66 (H-1 there, by file) had TotalAdequacy 4 and no EvenOddExhibit, so the two EvenOddExhibit lines are new to this range (the file is new). KNOWN-OPEN-ITEMS C5 reads "ALL pre-date C3 … zero added since" — no longer true.
Fix: drop the `h` binder from both lemmas (and the `(by omega)` arguments at their four call sites, lines 393/438/555/603) or rename `_h`; amend C5 to "66 → 64 at H1 (TotalAdequacy's 4 gone earlier; 2 added at H1b, removed at …)". Premise verified by measurement: yes.

### R-1 (Record, in-range): the "ten `stepDischarge_*` lemmas" newly consumerless are THIRTEEN — three `dischargeStep_*_active` lemmas also lost their only consumer

Evidence. At `e242342` the deleted `outcomesU_of_step` was the only textual consumer of `dischargeStep_kill_active`, `dischargeStep_alloc_active`, `dischargeStep_memop_active` (Soundness.lean at `e242342`, lines 5253 `rw [dischargeStep_kill_active hmem]`, 5282 `rw [dischargeStep_alloc_active hmem]`, 5574 `rw [dischargeStep_memop_active hmem]`; `git grep` over the whole package at `e242342` finds no other non-definition mention). Proof-term in-degree at HEAD (my cone script, `getUsedConstants` with `allowOpaque := true`, non-internal roots, closure through internal auxiliaries): 0 for all three, 0 for the ten `stepDischarge_*`. Cross of "identifiers in the three deleted bodies" × "zero-consumer unpinned theorems at HEAD" (DERIVED, verbatim output):
```
identifiers in the three deleted bodies that are now zero-consumer, unpinned theorems: 13
['dischargeStep_alloc_active', 'dischargeStep_kill_active', 'dischargeStep_memop_active', 'stepDischarge_alloc_eval', 'stepDischarge_if_false', 'stepDischarge_if_true', 'stepDischarge_kill_eval', 'stepDischarge_load_eval', 'stepDischarge_memop_eval', 'stepDischarge_pure_sym', 'stepDischarge_run', 'stepDischarge_save_eval', 'stepDischarge_store_eval']
```
(`dischargeStep_*_refusal`, `dischargeStep_{create,load,store}_active` are also zero-consumer at HEAD but were NOT referenced by the deleted bodies — pre-existing, not this range's.) The record §3 and KNOWN-OPEN-ITEMS C14 name the ten only. `outcomesU`/`dischargeStep` themselves stay consumed (in-degree 4 / 26), as the record says.
Fix: C14 (and the record's §3/§9.3) → "the ten `stepDischarge_*` and the three `dischargeStep_{kill,alloc,memop}_active` lemmas". Premise verified by measurement: yes.

### R-2 (Record, in-range): ARCHITECTURE.md's `wps_sound_empty` consumer enumeration omits `TwoLabelExhibit` (a module of this range)

Evidence. `ARCHITECTURE.md:186–187` (written in `cd05543`, blame-verified): "`wps_sound_empty` of Exhibit, StructExhibit, CaseExhibit, LoopExhibit, FibExhibit and ArrayExhibit". Code-level consumers at HEAD: those six plus `ListRevExhibit.lean:1434`, `WseqExhibit.lean:107` and **`TwoLabelExhibit.lean:531`** (`(wps_sound_empty (ctl := procCtl p) rfl …` inside `tl_wp_readout`). The `wps_sound` list on the same lines (`CallSmoke:330`, `FibRecExhibit:648`, `EvenOddExhibit:501`) is correct and complete (measured: `wps_sound\b` non-empty uses in FibExhibit/CaseExhibit/FibRecExhibit/CallSmoke/LoopExhibit/Exhibit/StructExhibit/EvenOddExhibit/WseqExhibit are all in comments except the three cited — not re-verified line by line beyond the cited three). Only the TwoLabelExhibit omission is this range's; ListRev/Wseq are pre-existing omissions of the same sentence. Not a prose matter (the separate reviewer's) — a factual enumeration that a reader uses to find consumers.
Fix: "… of the nine seeded exhibits (Exhibit, StructExhibit, CaseExhibit, LoopExhibit, FibExhibit, ArrayExhibit, ListRevExhibit, WseqExhibit, TwoLabelExhibit)". Premise verified by measurement: yes (grep, code lines).

### Note-1 (Record precision, pre-existing, repeated by this range's records): "402 pins" is the LIST LENGTH; the list has two duplicate entries, so 400 DISTINCT names are pinned

Evidence. `Audit.lean:616` prints `{trioExports.length}`; `sort | uniq -d` over the `trioExports` names at HEAD: `CerberusHeapLang.loop_step_frag`, `CerberusHeapLang.loop_step_frag_same` — both already duplicated at `e242342` (376 = 374 distinct). The 26 names added in this range are distinct and not previously present (verified against the diff of `Audit.lean`); "376 → 402 (26 added)" is exact as a delta. Nothing is unsound (a duplicated pin is checked twice); the count on every surface ("402 pins trio-exact") overstates distinct pins by two.
Fix (optional, hygiene slice): dedupe the two entries and restate 400 on the surfaces, or one sentence in KNOWN-OPEN-ITEMS E. Premise verified by measurement: yes.

### Note-2 (Precision, not a defect): the two-label TOTAL budget `5·n₁ + 5·n₂ + 5` is a correct upper bound with per-iteration slack; the even/odd bound `3n + 6` has exactly the known one unit (B6 class)

Evidence — the shipped thread loop executed (method as the C4 audit's R-3: `runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty fmapEmpty [0]) st`, "done" read as a `Step_done2` in `step_ctx` at the final thread; `ctr` = `dr_step_counter`). Even/odd, `prodEntryStateWith (eoProcs default B) 0 (eoMain default n) fs_initial_state`, `B := BTy_object OTy_integer`, verbatim:
```
[(0,
    [(2, "NDkilled ctr=2"), (3, "NDkilled ctr=3"), (4, "NDkilled ctr=3"), (5, "NDactive steps=1 done=[1] ctr=3"),
      (6, "NDactive steps=1 done=[1] ctr=3"), (7, "NDactive steps=1 done=[1] ctr=3"),
      (8, "NDactive steps=1 done=[1] ctr=3")]),
  (1,
    [(5, "NDkilled ctr=5"), (6, "NDkilled ctr=6"), (7, "NDkilled ctr=6"), (8, "NDactive steps=1 done=[0] ctr=6"),
      (9, "NDactive steps=1 done=[0] ctr=6"), (10, "NDactive steps=1 done=[0] ctr=6"),
      (11, "NDactive steps=1 done=[0] ctr=6")]),
  (2,
    [(8, "NDkilled ctr=8"), (9, "NDkilled ctr=9"), (10, "NDkilled ctr=9"), (11, "NDactive steps=1 done=[1] ctr=9"),
      (12, "NDactive steps=1 done=[1] ctr=9"), (13, "NDactive steps=1 done=[1] ctr=9"),
      (14, "NDactive steps=1 done=[1] ctr=9")]),
  (3,
    [(11, "NDkilled ctr=11"), (12, "NDkilled ctr=12"), (13, "NDkilled ctr=12"),
      (14, "NDactive steps=1 done=[0] ctr=12"), (15, "NDactive steps=1 done=[0] ctr=12"),
      (16, "NDactive steps=1 done=[0] ctr=12"), (17, "NDactive steps=1 done=[0] ctr=12")]),
  (4,
    [(14, "NDkilled ctr=14"), (15, "NDkilled ctr=15"), (16, "NDkilled ctr=15"),
      (17, "NDactive steps=1 done=[1] ctr=15"), (18, "NDactive steps=1 done=[1] ctr=15"),
      (19, "NDactive steps=1 done=[1] ctr=15"), (20, "NDactive steps=1 done=[1] ctr=15")])]
```
DERIVED: mirror rounds = `3n + 3` = `k − 1` for `main`'s certified budget `k = 3n + 4` (the budget is exact in the fib sense: it contains the final delivery), the loop turns active at `fl = 3n + 5 = k + 1`; the theorem's `hfuel : 3n + 6 = k + 2` carries the one unit of slack KNOWN-OPEN-ITEMS B6 records for `DriverDoneCtl`'s `k + 2`. Delivered value alternates 1/0 with parity as claimed.

Two-label: a seeded cell obtained by running `create(4, int)` alone on the shipped loop (pointer `(@1, 0xfffffffffff4)`), then `tlProg loc0 empty_annotation default NA BTy_unit B B BTy_unit BTy_unit c n₁ n₂` from `{ prodEntryStateWith [] 0 prog fs_initial_state with layout_state := <the create's memory> }` (the driver's own registration of `l1`/`l2` from the body), `k = 5n₁ + 5n₂ + 5`, `fl ∈ {k−1, …, k+3}`, verbatim:
```
[((0, 0, 5),
    [(4, "NDkilled ctr=4"), (5, "NDkilled ctr=4"), (6, "NDactive done=[Unit] ctr=4"), (7, "NDactive done=[Unit] ctr=4"),
      (8, "NDactive done=[Unit] ctr=4")]),
  ((1, 0, 10),
    [(9, "NDkilled ctr=7"), (10, "NDactive done=[Unit] ctr=7"), (11, "NDactive done=[Unit] ctr=7"),
      (12, "NDactive done=[Unit] ctr=7"), (13, "NDactive done=[Unit] ctr=7")]),
  ((0, 1, 10),
    [(9, "NDkilled ctr=7"), (10, "NDactive done=[Unit] ctr=7"), (11, "NDactive done=[Unit] ctr=7"),
      (12, "NDactive done=[Unit] ctr=7"), (13, "NDactive done=[Unit] ctr=7")]),
  ((1, 1, 15),
    [(14, "NDactive done=[Unit] ctr=10"), (15, "NDactive done=[Unit] ctr=10"), (16, "NDactive done=[Unit] ctr=10"),
      (17, "NDactive done=[Unit] ctr=10"), (18, "NDactive done=[Unit] ctr=10")]),
  ((2, 3, 30),
    [(29, "NDactive done=[Unit] ctr=19"), (30, "NDactive done=[Unit] ctr=19"), (31, "NDactive done=[Unit] ctr=19"),
      (32, "NDactive done=[Unit] ctr=19"), (33, "NDactive done=[Unit] ctr=19")]),
  ((3, 2, 30),
    [(29, "NDactive done=[Unit] ctr=19"), (30, "NDactive done=[Unit] ctr=19"), (31, "NDactive done=[Unit] ctr=19"),
      (32, "NDactive done=[Unit] ctr=19"), (33, "NDactive done=[Unit] ctr=19")])]
```
DERIVED: the shipped loop needs `3n₁ + 3n₂ + 4` mirror rounds (3 per iteration: guard, store-in-`lets`, `run`); the budget charges 5 per iteration (`wpt_store`'s rule constant `3 ≤ k`, `Wpt.lean:2683`, for a store the engine performs in ONE round of the sequential loop — `lets _ = store … in run …` collapses the action and the LETS-PURE into one driver round). At `n₁ = n₂ = 0` the budget is exact (`k = 5`, active at `k + 1`); the slack is `2·(n₁ + n₂)` rounds. This is the class every store-bearing total exhibit already has (`counter_loop_certified_production`'s `hfuel : 6 * n + 8`, ProdLoopExhibit.lean:623) — pre-existing in the rule constant, not in this range; `tl_wpt` is sound (an upper bound is what `wpt` states) and NO surface claims tightness. The module header's "per iteration guard 1 + store 3 + jump 1" is correct as RULE-COST accounting; the record's §2 "Budget accounting" likewise. Optional: one sentence naming the store rule's 3-vs-1 slack, in the header or KNOWN-OPEN-ITEMS beside B6.

Readout check (the nested `if`): the cell read back with a `Load0` after each run, verbatim:
```
[((0, 0), "NDactive done=[Unspecified('signed int')] ctr=1"), ((1, 0), "NDactive done=[Specified(5)] ctr=1"),
  ((0, 1), "NDactive done=[Specified(6)] ctr=1"), ((1, 1), "NDactive done=[Specified(6)] ctr=1"),
  ((2, 3), "NDactive done=[Specified(6)] ctr=1"), ((3, 2), "NDactive done=[Specified(6)] ctr=1")]
```
= `if 0 < n₂ then sixBytes else if 0 < n₁ then fiveBytes else bs0`, as `two_label_certified` states. Sizes: `(esize prog, pot prog, esize body1, esize body2) = (6, 7, 5, 3)` (record: 6 / 7, 5, 3 — matches).

### Note-3 (Record, pre-existing, out of range): DECISIONS.md has one non-chronological entry far before this range

Evidence (DERIVED over `^- \*\*YYYY-MM-DD` headers): entry 63 is dated 2026-09-02 after a 2026-09-03 entry; every entry this range appended (the last eight, all 2026-09-04) is in order. Not this range's; recorded so it is not rediscovered.

---

## What was measured, item by item (the brief's eight points)

### 1. H1a census — REPRODUCED EXACTLY

Compared BY ENTRY (kind + name + printed type) from the committed snapshots with my own script (`.lake/audit-logs/census.py`), pre `docs/2026-09-04_ar5-readout-signatures-post.txt`, post `docs/2026-09-04_h1a-signatures-post.txt` — verbatim:
```
pre 2971 post 2966
ADDED 0
REMOVED 5 ['CerberusHeapLang.outcomesU_done', 'CerberusHeapLang.outcomesU_of_step', 'CerberusHeapLang.outcomesU_remove_annot', 'CerberusHeapLang.procCtx_wf', 'CerberusHeapLang.spikeCtx_wf']
CHANGED 1 ['CerberusHeapLang.wpt_call_eq']
UNCHANGED 2965
```
`wpt_call_eq`: the old printed statement with the four mechanical substitutions (`∀ {q : context × sym × List (generic_pexpr Unit sym)},` → `∀ {ctx : context} {f : sym} {pes : List (generic_pexpr Unit sym)},`; `= some q →` → `= some (ctx, f, pes) →`; `q.snd.fst` → `f`; `q.snd.snd` → `pes`; `q.fst` → `ctx`) is byte-identical to the new one (`MECHANICAL-SUBSTITUTION-EQUAL: True`). Every other entry byte-identical (UNCHANGED 2965, including `progA_wpt`, `ψX`, `wps_empty_call_false`, `wpt_empty_call_false`).
HEAD snapshot regenerated (`lake env lean scripts/signature_snapshot.lean`, 29893 lines): `cmp` against `docs/2026-09-04_h1b-signatures-post.txt` → `CMP-IDENTICAL`.
Projection sites: `grep -cE 'q\.1\b|q\.2\.1|q\.2\.2'` over Wps.lean + Wpt.lean at HEAD = 0 + 0; at `e242342` = 33 + 43 = 76 occurrences on 23 + 33 = 56 lines (the record's numbers); `have hq` 1 + 1 → 0 + 0. The full Wps/Wpt diff read: every hunk is `obtain ⟨ctx, f, pes⟩ := q` after `| some q =>` plus the renaming; `Step.call hcr`/`hs.call_inv hcr` replace the two eta-hacks; the two `_annot_reindex` lemmas destructure `⟨c₀, f₀, pes₀⟩`; no proof content changed.

### 2. `progA_wpt` — statement unchanged, proof through public lemmas, a GENUINE consumer of `wpt_load`; the manifest-red premise VERIFIED

Statement: UNCHANGED in the census (§1). Proof (Exhibit.lean:574–597, diff read): `wpt_mono` → `wpt_load loc0 empty_annotation intTy xPtr NA (.own 1) … (Nat.le_refl 3) htrap_seven` → a local `have hread … := stateInterp_readout fun _ _ _ _ hG => (pointsToCell_consequence hG …).trans (BI.pure_mono …)`; the former `pointsToCell_cellOwn_iff`/`wpt_load_cell_at`/`stateInterp_iff`/`cellOwn_cellCoh` chain is gone. Proof-term cone at HEAD (my script): `wpt_load` in-degree 2 (`progA_wpt`, `wpt_load_plain`) — a real proof-term consumer, not incidental; `progA_wpt` reaches `wpt_load`, `stateInterp_readout`, `pointsToCell_consequence`, `wpt_mono`, `wpt_store`, `wpt_seq` (non-internal cone printed in `.lake/audit-logs/cone.out`). The worker's premise "deleting it turned the manifest red because it was `wpt_store`'s only consumer": `git show e242342:cerberus-heaplang/docs/CAPABILITY_MANIFEST.md`, the `Frag.store` whole-cell row, verbatim cell: `` `wpt_store` — Exhibit `` — Exhibit was the ONLY consumer module of `wpt_store` (at HEAD: `Exhibit, TwoLabelExhibit`). Premise verified: yes. Consequence in the same manifest diff: `wpt_load_at` loses `Exhibit` (the old proof went through the sub-range view), `wpt_load` gains it.

### 3. Deletions — none pinned, none a deliverable; what went dead is measured (R-1)

The five names: not in `trioExports` at `e242342` (grep of the pin list); named on API.lean/ARCHITECTURE/README/WALKTHROUGH only as "proof devices … not exports" (the record's §3 list checked by grep at `e242342`). Build green at HEAD is the kernel-level proof of no term-level consumer. Newly consumerless: thirteen, not ten (R-1). Nothing load-bearing lost: `outcomesU`/`dischargeStep` keep 4 / 26 consumers (Round.lean's `engine_complete_*U` readings). `stepDischarge_*` at HEAD: 10 theorems (`grep -c '^theorem stepDischarge_'`).

### 4. H1b census — REPRODUCED EXACTLY; pins 376 → 402; all 26 trio-exact

Pre `h1a` post, post `h1b` post: `pre 2966 post 3081 / ADDED 115 / REMOVED 0 / CHANGED 0 / UNCHANGED 2966`; my ADDED set equals the record §6's list (`record ADDED list size 115 ; equal to measured: True`). `trioExports` names: 376 at `e242342`, 402 at HEAD (list length; Note-1 on distinctness); the 26 added are exactly the diff of `Audit.lean:573–598` (2 twins + 11 two-label + 13 even/odd, names as the record §4). `#print axioms` (via `collectAxioms`) on all 26 plus `progA_wpt` and `wpt_call_eq`: `trio-exact: 28/28`, each `#[Classical.choice, Quot.sound, propext] TRIO-EXACT` (log `.lake/audit-logs/axioms.lean` output).

### 5. The exhibits — honest

`TwoLabelExhibit`: the program (lines 13–17 of the header, `tlProg`/`tlBody1`/`tlBody2` lines 99–118) has two `save`s in one procedure, the second in the first's exit branch; `tlQ` is the two-entry chain (line 121–124); `tlLs`/`tlLsT` are label-dependent (`if symOrd l tlL2Sym = .eq`) — the only such in the package (`grep -l 'symOrd l '` over `*Exhibit.lean` → TwoLabelExhibit alone). `two_label_certified`'s post traced against the program and CONFIRMED BY EXECUTION (Note-2's readout table). `tl_wpt`'s budget: sound upper bound, slack measured (Note-2). Statement shape = `counter_loop_certified`'s (`DriverSafeCtl (procCtx rs) (procThread …) prog [fmapEmpty] (procCtl …) σ₀ …`, seeded `hcoh`), the nested `if` spelled out — no package definition in the engine statement.

`EvenOddExhibit`: `eoEvenBody` calls `eoOddSym`, `eoOddBody` calls `eoEvenSym` (lines 78–83) — genuine mutual recursion; `eoSpec`/`eoSpecT` read the symbol (`if symOrd g eoOddSym = .eq then n % 2 else 1 - n % 2`); `eoCtx_procSpecs` verifies each body once under the table for both (`procSpecs_intro`), no Löb in the client. `even_odd_certified` (line 673): closed partial ∀ `fuel` over `CerbND.drive_lemFuel fuel fmapEmpty false (prodFileWith …) args` from `(initial_driver_state sup … fs).1` — the genuine driver, no synthetic loop. `even_odd_certified_production` (line 721): over `_root_.drive fmapEmpty false (prodFileWith (eoProcs ra nbty) (eoMain ra n)) args`, `hfuel : 3 * n.toNat + 6 ≤ CerbFuel.driverFuel`; vocabulary = program builders (`prodFileWith`, `eoProcs`, `eoMain`), `initial_driver_state`, `runND`/`drive`, the readout `ivVal (1 - n % 2)`, the budget — no logic-side definition. Registration order re-measured: six `example : collect_labeled_continuations_NEW (eoFile default 3 B) = <chain> := rfl`, one per insertion order — exactly ONE elaborates (`symAdd eoEvenSym ∅ (symAdd eoOddSym ∅ (symAdd mainSym ∅ ∅))`), the other five fail with `rfl` type mismatch (verbatim errors in the first probe run). Budget exactness: Note-2 (needed `3n + 5`, demanded `3n + 6`; the B6 unit). Sign convention: `hn : 0 ≤ n` is a hypothesis of BOTH statements; needed — verbatim, the shipped driver at `fuel = 3` and `1 - n % 2`:
```
[(-1, "Active v=1 blocked=false out=\"\" err=\"\"", 0), (-2, "Active v=1 blocked=false out=\"\" err=\"\"", 1),
  (-3, "Active v=1 blocked=false out=\"\" err=\"\"", 0)]
```
(the program returns 1 for every `n < 1`; the readout would say 0 at `n = -1` — excluded by `hn`). The outer-fuel form at `fuel ∈ {0,1,2,3}`, `n ∈ {0..5}`: `Killed` at 0, `Active v = 1,0,1,0,1,0` at every fuel ≥ 1 (the A2 reading: one scheduler round). Sizes `(esize even, odd, main, pot even, odd, main) = (2, 2, 1, 3, 3, 2)` as the record.

### 6. Manifest / instruments

Manifest at HEAD (`docs/CAPABILITY_MANIFEST.md`, diff read): `MANIFEST: 23 constructors, 50 variant rows (30 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 15 NO-RULE, 5 OUT-OF-SCOPE), 0 red, 18 consumer modules`; the three reclassified rows: `Frag.load` whole-cell `wpt_load — Exhibit`, `Frag.case_value` `wpt_case_value — CaseExhibit`, `Frag.wseq` `wpt_wseq — WseqExhibit` — proof-term in-degrees at HEAD 2 / 1 / 1 (real consumers). Generator diff: exactly those three `cls` fields `.ruleTotalUndemonstrated … → .rule`. TSV: two `positive-client` rows added; `Exhibit`'s allowance cell `-`; `production-wrapper` header reworded. Import direction: gate line `15 core modules, none imports an exhibit/example/production module` (EvenOddExhibit imports FibRecExhibit — client → client, allowed by the check as FibRec → Fib already is). Boundary: 19 modules, ZERO allowances, ZERO mentions (gate tail below). Plant: see the plant log.

### 7. Records

FULL gate run once at `cd68c46` (verdict tail below); DIFFED line for line against the DECISIONS H1 entry's block (orchestrator gate at `b8413a5`): `IDENTICAL line for line` (36 lines each) — and `git diff --stat b8413a5..cd68c46 -- '*.lean' '*.tsv' '*.sh' scripts` is EMPTY (the later commits are docs-only), so the same content was gated. Record counts vs tree: 2971/2966/3081, 76 → 0, 5/1/0, 115/0/0, 376 → 402 (Note-1), 30/0/15/5/18, 19 modules — all as measured. DECISIONS: this range's eight entries chronological (Note-3 is earlier). KNOWN-OPEN-ITEMS closures checked against the tree: B8 (exhibits exist) ✓, B11 (ruling, not a tree fact) —, B13 (three rows RULE, consumers real) ✓, C1 ✓, C3 ✓, C8 ✓ (rewritten, zero allowances), C9 (API.lean:18–24 text) ✓, C13 (TSV header) ✓, C14 — UNDERCOUNTS (R-1), C5 — NOW FALSE (H-1), E's expected tail ✓ (matches the verdict below).

### 8. Grumpy read of the new Lean

The destructured call clause (`wps.pre`/`wpt.pre`) is exactly what the C3 audit asked for: the clause now reads as the call rule; no residue. The two twins (`caseProg_wpt`, `wseqProg_wpt`) are minimal and correct (budget 2 = TAU/drift + delivery). `TwoLabelExhibit`: well organised, proofs readable; nits — (i) `tl_readout_val` (line 506) and `tlPost_to_readout` (line 743) are THE SAME FACT with the same proof term, once as the raw `∀ σ' ns κs nt, stateInterp … ={⊤,∅}=∗ ⌜…⌝` and once as `readoutPost …`; keep one (`readoutPost` unfolds to the other) — the same doubling is in `eo_wp_readout` (inline) vs `eoPost_to_readout`; (ii) the four-times-repeated `obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by have h1 := congrArg (fun l => l.head?) hρ; have h2 := …; simp at h1 h2; exact ⟨h1.symm, h2.symm⟩` (lines 459, 474, 692, 707) is `obtain ⟨rfl, rfl⟩ := List.cons.inj hρ` — and a non-terminal `simp` besides; (iii) the partial/total body proofs are near-verbatim twins — the house pattern, not this slice's to fix. `EvenOddExhibit`: the symbol-dependent table is the right shape and the comparator-verdict plumbing (`eoFile_lookup_inv` handing `symOrd g eoOddSym ≠ .eq` to the even case for free) is a nice touch; nits — the unused `h` binders (H-1); `eoLs`/`eoLsT` and the two `*_blockSpecs` are the same "no labels" boilerplate FibRecExhibit already has (a shared `emptyLabelSpec` lemma would serve every procedure-only exhibit). No `set_option`, no heartbeat/`maxRecDepth` changes, no `sorry`, `decide +kernel` only at symbol comparisons (grep).

---

## The FULL gate at `cd68c46` (verbatim; `CERB_MEM_MAX=64G ./scripts/test_unit.sh` from the audit copy's root; the `GATE-EXIT` line is `echo "GATE-EXIT=$?"` appended by me; lines matching `^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE-EXIT|^Build completed|^BOUNDARY|^ALLOWLISTED|^FAIL`, unmodified)

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:603:0: CerberusHeapLang export pins: 402 trio-exact
info: CerberusHeapLang/Audit.lean:603:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3555 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:603:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5357 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (458 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 15 core modules, none imports an exhibit/example/production module
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
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
BOUNDARY: 19 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
GATE-EXIT=0
```
(`grep -ci uncapped` = 0, `grep -c 'uses sorry'` = 0 over the whole log; wall `8.965 total` — the primed `.lake` replayed the build, the audit elaborated.)

## The plant log (verbatim)

Injected at the end of `CerberusHeapLang/EvenOddExhibit.lean` (code, outside comments):
```
-- PLANT (audit): a live internals mention
example : True := by
  have _h := @CohG
  trivial
```
`scripts/boundary_check.sh` (from `cerberus-heaplang/`), filtered to `EvenOdd|BOUNDARY|WARN|FAIL|exit`:
```
FAIL: EvenOddExhibit — 1 internals mention(s) in a positive-client module (no allowance):
      EvenOddExhibit:766:  have _h := @CohG
BOUNDARY: 19 modules checked, 1 internals mention(s) in total, exit=1
```
(the check turned RED, exit 1; my shell's `|| bash …` fallback re-ran it, printing the same two lines twice). Reverted with `git checkout -- cerberus-heaplang/CerberusHeapLang/EvenOddExhibit.lean`; `git status --short` empty; re-run after revert:
```
ok:   EvenOddExhibit — 0 internals mentions
BOUNDARY: 19 modules checked, 0 internals mention(s) in total, exit=0
```

## What I did NOT check

- I did not rebuild `e242342`; the pre-state was taken from the committed pre snapshot (the worker reports it regenerated byte-identical), `git show` of the old sources, and the old manifest. The 66-warning baseline is the C3 audit's per-file tally (not re-measured at `e242342`).
- I did not re-run the worker's intermediate FAST gates at `903c567`/`4acb10d`; only the range head was gated (its Lean content is identical to `b8413a5`).
- The ARCHITECTURE.md prose (the separate reviewer's) — only the factual claims about this range's Lean that I met were checked (§2.5's line cites `EvenOddExhibit.lean:501/:673/:721`, `Audit.lean:615–616`, the 402/30/18/16 counts, the `wps_sound`/`wps_sound_empty` lists — R-2).
- Prose of README/CLAIMS/WALKTHROUGH beyond the counts and names greppable from this range (eighteen, nine/ninth, 30 RULE / 0 undemonstrated, the four exhibit rows, the "no export consumes" correction).
- Tightness of the two-label PARTIAL statement's premises (`hcoh`, `hn₁`, `hn₂`) beyond reading; the total form has no shipped-loop twin to execute (B1's class, disclosed).
- The three pre-existing zero-consumer `dischargeStep_*_refusal`/`_active` lemmas not touched by this range, and the 1932-entry all-modules zero-in-degree list (mostly pins, projections and `.eq_def`s — not analysed further).
