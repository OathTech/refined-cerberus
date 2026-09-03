# Standards audit of the overnight stack, `9f0c20b..ec25fc2` (2026-09-03)

[AGENT] Independent standards auditor (fresh, Fable-class), on the fixed
detached copy `worktrees/audit-stack` (HEAD `ec25fc2`; `.lake` primed;
`.cerberus-ws` symlinked to the calls-c1 workspace at pin `f95ef8d9c`).
Read-only except this file. No `lake build`. Environment queries: one
`../scripts/capped ~/.elan/bin/lake env lean` run (14 s) of a read-only
script from `cerberus-heaplang/` — at that moment `pgrep -af 'lake build'`
showed a sibling repo's `lake build speclab-test`
(`cerberus-lean-arc/zero-discrepancy`), not a refined-cerberus build;
noted, proceeded. Scratch under the gitignored
`cerberus-heaplang/.lake/audit-scratch/` (deleted at the end).

Brief: the nine cross-cutting areas of the dispatch, graded against
`CLAUDE.md` (working practices, trust rules), `docs/AUDIT-BRIEF.md`, every
2026-09-03 entry of `docs/DECISIONS.md`, and the shop-window standard. The
nine per-slice range audits were NOT redone. Quotations below are verbatim
(character-for-character from the file named) unless labelled DERIVED or
paraphrase; tallies I computed are labelled DERIVED with the method.

---

## Executive verdict

**No High finding. The logic and the trust base hold across the stack**:
every one of the 39 sampled export cones (all eight production statements
+ 31 sampled pins) is exactly the classical trio; the banned-methods grep
over the whole package and its scripts is clean (every hit is prose);
`Audit.lean`'s sweep does include internal details; the seven closed
shipped-driver statements mention no package definition beyond the
authored program, `prodFile`, pure readouts and the budget side
condition; the one-change-at-a-time classes hold at every point I could
re-derive (every slice's snapshot tally re-derived EXACTLY; the eight
production statements byte-identical across C1 and C2; the re-pin moved
exactly the 8 side-condition statements it named and nothing else).

**Four Mediums, all documentation/process, none a logic gap**: (M-1) two
shop-window surfaces still assert a `sorry` admission in the pinned
semantics tree that the re-pin closed and README says is gone; (M-2) the
"proof device appears in no export's statement" sentence is false at HEAD
— C2 pinned `outcomesU_of_call`/`outcomesU_of_ret`/`drive_classifyU_aux`
beside the older `stepDischarge_run`, and none carries a PROVISIONAL
label; (M-3) the orchestrator's independent gate is recorded at one
boundary of eleven — every range auditor states they did not run it;
(M-4) README carries a false statement of a pinned theorem's shape (the
retired plan form) and several stale counts/listings.

**Merge recommendation: MERGE AFTER FIXES M-1, M-2, M-4 (docs-only edits,
plus a one-line pin-list decision in M-2) and after the orchestrator runs
and records ONE FULL gate at the merge candidate (M-3).** The Notes are
polish and can ride along or follow.

---

## Findings

### M-1 (Medium) — ARCHITECTURE §6 and WALKTHROUGH §6 assert an admission the pinned tree no longer has

- Location: `cerberus-heaplang/ARCHITECTURE.md` §6; `cerberus-heaplang/docs/WALKTHROUGH.md` §6.
- Claim (ARCHITECTURE, verbatim): "THE ONE KNOWN ADMISSION IN THE PINNED
  SEMANTICS TREE. The pinned cerberus-lean tree declares no `axiom`, but it
  contains one generated admission: two `(sorry : String)` terms in the
  debug-log branch of `auxAddToRfLoad` in the generated concurrency model
  (`Cmm_op.lean`; Lean reports `declaration uses sorry` for it during the
  build)." WALKTHROUGH §6 (verbatim): "The pinned semantics tree does
  contain one known generated admission: two `(sorry : String)` terms in
  the debug-log branch of `auxAddToRfLoad` in the generated concurrency
  model (`Cmm_op.lean`), which Lean reports as `declaration uses sorry`
  during the build."
- Tree's truth: README (verbatim): "*Admissions in the pinned semantics
  tree: none (measured 2026-09-03).*" My measurement: `grep -rn sorry
  .cerberus-ws/lean_frontend/generated --include='*.lean'` returns comment
  text only (CerbCall.lean:51, Core_reduction.lean:276,
  CerbStepInstances.lean, CerberusFresh.lean:155, CerbFunMapInstances.lean:6);
  `grep -n sorry generated/Cmm_op.lean` returns nothing. The re-pin
  record/commit `f2f9701` claims only "README's 'one known admission'
  paragraph → none at this pin" — the other two surfaces were not updated,
  and the K5.1+re-pin audit did not catch it.
- Consequence: three shop-window documents disagree on a trust-base fact
  (the error is in the conservative direction, but "every sentence names
  its theorem" fails, and a reader of ARCHITECTURE alone is told something
  false about the pin).
- Fix: replace the ARCHITECTURE §6 paragraph and the WALKTHROUGH §6
  sentence with the README's measured statement (pin `f95ef8d9c` closes
  the `cmm_op.lem` `sorry` target_rep; measured zero `sorry` terms in
  `generated/`; the sweep stays in force).

### M-2 (Medium) — "appears in no export's statement" is false at HEAD; four pinned exports mention the discharge/drive devices and carry no PROVISIONAL label

- Location: `ARCHITECTURE.md` §2 (lines 60-62); `docs/WALKTHROUGH.md` §5
  (lines 1282-1284); `CerberusHeapLang/Audit.lean` `trioExports`;
  `CerberusHeapLang/API.lean` row "The engine transition and its certification".
- Claim (ARCHITECTURE, verbatim): "the hand-written discharge
  `dischargeStep`/`outcomesU` is a proof device of the `driveU` lane and
  appears in no export's statement (the trust rule of 2026-09-02)."
  WALKTHROUGH (verbatim): "The hand-written discharge
  `dischargeStep`/`outcomesU` (Soundness.lean) is a PROOF DEVICE of the
  `driveU` lane and appears in no export's statement (the trust rule of
  2026-09-02)."
- Tree's truth (measured by `Expr.getUsedConstants` on the TYPE of each of
  the 316 `trioExports`, direct mentions): `stepDischarge_run` mentions
  `dischargeStep`; `outcomesU_of_call` and `outcomesU_of_ret` (both added
  to `trioExports` by C2, `8d28c21`) mention `outcomesU`;
  `drive_classifyU_aux` (C2) mentions `driveU`. Labels: `stepDischarge_run`
  occurs 0 times in README/ARCHITECTURE/WALKTHROUGH; `outcomesU_of_call`/
  `_ret` once each in ARCHITECTURE §4 as "device lemmas", never as
  PROVISIONAL; `API.lean` lists "all of Soundness except `Frag`
  (`stepDischarge_*`, `engine_step_matchU`, …)" under "The surface (PUBLIC
  — import and use freely)". The 2026-09-02 trust rule (CLAUDE.md): "no
  hand-written definition (driver loop, discharge, scheduler) may appear in
  the statement of an exported theorem; proof devices (the mirror, the
  collapse) live in proofs only."
- Consequence: a shop-window sentence contradicts the pin list; the C2
  slice regressed the K4/K5 standard for the device layer (the K4/K5
  production statements themselves are clean — below). No logic gap: the
  device lemmas are sound, trio-exact, and unreachable from any closed
  statement's TYPE.
- Fix (one of two statements, operator's choice): (a) remove
  `stepDischarge_run`, `outcomesU_of_call`, `outcomesU_of_ret`,
  `drive_classifyU_aux` from `trioExports` (they stay bounded by the
  exhaustive sweep; the pin list is "THE PUBLIC EXPORTS") and keep the
  sentence; or (b) rewrite both sentences to "…appears in the statement of
  no ADEQUACY or production export; the pinned device lemmas
  `stepDischarge_run`, `outcomesU_of_call`, `outcomesU_of_ret`,
  `drive_classifyU_aux` are PROVISIONAL-lane machinery" and add the four
  names to the PROVISIONAL lists in README "The claim", ARCHITECTURE §6,
  WALKTHROUGH §1.3, and move `stepDischarge_*` out of the PUBLIC row of
  `API.lean`.

### M-3 (Medium as a standards deviation; Note under AUDIT-BRIEF's grading) — the orchestrator's independent gate is recorded at one boundary of eleven

- Location: `docs/DECISIONS.md` 2026-09-03 entries (K0, K1, K2, K2.5, K3,
  K4, K5, K5.1, re-pin, C1, C2); the nine range-audit records.
- Standard (CLAUDE.md, verbatim): "the orchestrator independently
  re-verifies gates at boundaries (worker-claimed green is never accepted)".
- Tree's truth: the only recorded orchestrator gate is the re-pin
  addendum (`8aed7a7`, `docs/2026-09-03_repin-fuel-notes.md` "Addendum
  (orchestrator, 2026-09-03): the FULL gate at the COMBINED head" — "296
  trio-exact … ALL GATES GREEN / GATE-EXIT=0"). No DECISIONS entry for any
  other slice records an orchestrator-run gate. Every range auditor states
  they did not run one: k0-audit "I did not run `lake build` or
  `scripts/test_unit.sh`"; k2-audit "The FULL gate (`scripts/test_unit.sh`),
  the manifest regeneration and the import-direction check were NOT
  re-run"; k5-audit "I relied on the worker's verbatim gate tail"; c1-audit
  "I did not re-run the FULL gate"; c2-audit "The orchestrator's own gate
  re-run covers this" — no such run is recorded anywhere for the C2 head
  `8d28c21`/`ec25fc2`.
- Consequence: at the merge candidate the only FULL-gate evidence is the
  C2 worker's own tail (`docs/2026-09-03_c2-notes.md` §12, "export pins:
  316 trio-exact … ALL GATES GREEN"). My independent sample (39 cones
  trio-exact by `collectAxioms`; 316 pins loaded from the primed `.lake`;
  80 `#check`s resolve) found no gap, so under AUDIT-BRIEF this is a Note;
  under the standards remit it is a process deviation at every slice
  boundary.
- Fix: the orchestrator runs `scripts/test_unit.sh` (FULL) once at the
  merge candidate and appends the verbatim tail to DECISIONS. One run
  covers the stack: the Lean tree at `ec25fc2` equals `8d28c21`'s (the
  three later commits are docs-only, verified by `git show --stat`).

### M-4 (Medium) — README states a pinned theorem in its retired shape, and carries stale counts/listings

- Location: `cerberus-heaplang/README.md` exhibits table row (line 360);
  "How to build and verify" (line 749); "Records" (line 820ff); exhibits
  table preamble (line 334) and `docs/WALKTHROUGH.md:15`.
- Claims (verbatim):
  - line 360: "allocate-then-initialize as `MemTripleU_alloc spikeCtx
    spikeEnv prog ∅ [⟨8, structTy⟩] ψ`, an instance of
    `project_triple_pure_alloc`".
  - line 749: "info: CerberusHeapLang/Audit.lean:260:0: CerberusHeapLang
    export pins: 165 trio-exact".
  - line 820: "The kill/free arc (K0–K4, 2026-09-03) has its own record …
    indexing the slice notes `docs/2026-09-03_k{0,1,2,2.5,3,4}-notes.md`
    and the range audits `docs/2026-09-03_k{0,1,2,2.5,3}-audit.md`."
  - line 334: "read off the machine-printed statement of every constant in
    `docs/2026-09-02_pr3-C-signatures-post.txt`".
- Tree's truth: (a) K2.5 (`77c5277`) restated `struct_create_store_adequacy`
  — the k2.5 snapshot lists it CHANGED and k2.5-notes §3 gives the new
  form "`MemTripleU_alloc … ∅ [⟨8, structTy⟩] ψ` → `… ∅ (allocCost fmapEmpty
  structTy 8) ψ`"; the plan type `AllocReq` no longer exists. (b) the pin
  count is 316 (`TRIOEXPORTS 316`, my run). (c) The K4/K5 audits, K5/K5.1
  notes, the re-pin notes/audit, C1/C2 notes/audits are not listed; the arc
  runs K0–K5.1. (d) Thirteen snapshots have been committed since
  `pr3-C`; the current one is `docs/2026-09-03_c2-signatures-post.txt`.
- Consequence: (a) is a false statement about a root-claim-supporting
  theorem in the exhibits table ("Every theorem below is pinned …"); (b)-(d)
  are stale pointers a skeptical reader trips on.
- Fix: (a) `MemTripleU_alloc spikeCtx spikeEnv prog ∅ (allocCost fmapEmpty
  structTy 8) ψ`; (b) "export pins: 316 trio-exact" or "the build prints the
  current count"; (c) "K0–K5.1 … `k{0,1,2,2.5,3,4,5,5.1}-notes.md`,
  `k{0,1,2,2.5,3,4,5}-audit.md`, `k5.1-repin-audit.md`, `repin-fuel-notes.md`,
  `c{1,2}-notes.md`, `c{1,2}-audit.md`"; (d) point at
  `2026-09-03_c2-signatures-post.txt`.

### N-1 (Note) — provenance: agent disposition text untagged inside two [USER] entries

- Location: `docs/DECISIONS.md` "2026-09-03 [USER] INTERMEDIATE STANDARDS
  AUDIT BEFORE THE MERGE; A FURTHER RE-PIN SCHEDULED" and "2026-09-03
  [USER] LANE B PAUSED; THE SEED IS PARKED UNMERGED".
- Tree's truth: the operator quotations are delimited and plausible
  ("we should do an intermediate audit before merge. The cerberus-lean
  project is still moving …"; "the seed is just a copy at the moment …").
  The text after them — "Disposition: … A further re-pin … is scheduled as
  a forced-semantics-change slice after the calls arc (C3/C4), before the
  fuel-lane restatement — each re-pin scouted first" and "Amendment to the
  copy ruling, for whenever a seed does precede a demo arc: forward-port
  demo → ext per merged arc through the rename map, never the reverse; and
  Lane B's fragment-growing slices (Eunseq, pointer ops) come after the
  ports" — is sequencing/design the operator did not say, carried under
  the [USER] header without an [AGENT] tag. The register's own convention
  elsewhere in the range does tag it ("[AGENT] sequence: K2 → K2.5 → …";
  "Decisions taken ([AGENT] recommendations, operator 'Great!')").
- All other 2026-09-03 entries: every design/engineering decision sits
  under an [AGENT] header or is tagged inline ([AGENT], [ORCHESTRATOR
  2026-09-03], "worker"); every [USER] quotation is first-person operator
  speech. Six slice records sampled (k0, k1, k2, k2.5, k3, k4, k5, k5.1,
  c1, c2 notes — all carry a "Provenance: every decision here is [AGENT]
  unless tagged" line; k3/k4/k5 tag the orchestrator's mid-slice direction
  as [ORCHESTRATOR 2026-09-03]).
- Fix: "Disposition [AGENT]:" and "Amendment [AGENT, operator-agreed]:".

### N-2 (Note) — record integrity: "verbatim" engine quotes are lightly normalized without an elision marker

- Location: `docs/2026-09-03_c2-notes.md` §1 (`call_proc`, the value arm);
  §3(f) (`loop_step_frag`).
- Method: every fenced code block ≥ 40 chars in the eleven 2026-09-03
  notes searched as an exact substring (then whitespace-insensitively) over
  the package and `.cerberus-ws/lean_frontend/generated/*.lean`; divergence
  points located by longest common prefix (DERIVED).
- Results: the Kill arm (k2), the Alloc0 arm (k3), the PCALL arm (c2), the
  K5.1 distinctness laws, the K1 bundles/seams (14 blocks), the K2.5
  camera definitions, the K4 abbrevs, the K0 `allocDisjoint` match the
  tree whitespace-insensitively (the generated files are single very long
  lines, so re-wrapping is unavoidable). Not verbatim: (i) c2 `call_proc`
  quote drops the generated comment `/- NOTE: the order of lookups implies
  that user procedure cannot hide the ones from stdlib, do we really want
  that? -/` and rewrites `(fun (sym1 : sym) (sym2 : sym)=> ordCompare sym1
  sym2)` as `ordCompare` and `(fun (acc : Fmap (sym) (value)) (p : (sym
  ×core_base_type)) (cval : value) =>` as `(fun acc p cval =>`
  (Core_run.lean:94-95); (ii) the value-arm quote drops `/- reached the end
  of the execution of a thread. -/` and `/- reduction: THREAD-DONE -/`;
  (iii) `loop_step_frag` is quoted with commas between structure-update
  fields where DriverCollapse.lean uses newline separation. Content is
  preserved in all three. Every other "not found" block is an intentional
  BEFORE-state quotation (K2/K3/K5 atomic specs quoted before C1 inserted
  `{ctl : Ctl}`; k5's `malloc_list_certified_production` at
  `lemDefaultFuel` before the re-pin; k0's `MemWF` before K3's `la_pos`) or
  a gate tail.
- Fix: label such blocks "comments and binder type annotations elided" or
  mark the elisions with `…`.

### N-3 (Note) — the snapshot dedupe rewrote quoted text in place

- Location: commit `1938951`; `docs/2026-09-03_k5-audit.md` Q5;
  `docs/2026-09-03_repin-fuel-notes.md` §6; `docs/2026-09-03_k2.5-notes.md` §6/§7.
- Tree's truth (verbatim, k5-audit): "- `cmp
  docs/2026-09-03_k4-signatures-post.txt (byte-identical to the former
  2026-09-03_k5-signatures-pre.txt, deduplicated 2026-09-03)
  docs/2026-09-03_k4-signatures-post.txt`: byte-identical (verified)." — a
  recorded command has become a self-comparison inside its code span;
  repin-fuel-notes §6 now reads "`…k5-signatures-post.txt (byte-identical
  …)` is a copy of `2026-09-03_k5-signatures-post.txt`". The dedupe's
  factual claim is TRUE: I recomputed md5 of all 12 deleted files from
  `1938951^` against the kept copies — all 12 identical (DERIVED;
  `fragment-closure-signatures-pre` = `mirror-completeness-signatures-post2`,
  which no document referenced).
- Fix: keep the original filename inside the code span and put "(now
  deduplicated to `…`)" outside it.

### N-4 (Note) — "old plan forms derivable" is derivable up to one explicit premise

- Location: DECISIONS "K2.5 LANDED" ("old plan forms derivable
  (`wps_create_of_plan`, `wpt_create_of_plan`)"); `docs/2026-09-03_k2.5-notes.md` §4.
- Tree's truth (snapshots, DERIVED): the K2 `wps_create` has premises
  `atomicTy req.ty = false` and `hinert` only; `wps_create_of_plan` (K2.5
  post) adds `0 < CerbMem.sizeofCtype M.tagDefs req.ty`. The record §3(b)
  discloses the new premise on `wps_create` ("the plan carried it inside
  `PlanFits`") but §4 says "The former public statement … is a theorem".
- Fix: "… is a theorem, up to the explicit positivity premise the plan
  resource carried implicitly".

### N-5 (Note) — stale in-code and heading text

- `CerberusHeapLang/Audit.lean:391-393` (verbatim): "(The malloc'd LINKED
  list is not statable — no load/store rule over `regionOwn`; the K4
  record's finding.)" — false since K5 (the pin list immediately below pins
  `malloc_list_certified_production`).
- `CerberusHeapLang/Step.lean:24` (verbatim): "the fragment `Frag` admits
  the STATIC kill only until K3" — history tense inside the SCOPE statement.
- `ARCHITECTURE.md:394` item heading "The kill/free arc K0–K4 — CLOSED"
  whose body covers K5/K5.1; arc record title "The kill/free arc, K0–K4".
- `docs/WALKTHROUGH.md:1507` "`trioExports` (165 theorems at the time of
  writing, 2026-09-03" — 316.
- `docs/WALKTHROUGH.md` §7 (verbatim): "labelled PROVISIONAL (§1.3) until
  the cerberus-lean fuel-exhaustion request lands" — the same document's
  §1.3 says it landed at the pin; the label now awaits the restatement.

### N-6 (Note) — process jargon in the shop window

ARCHITECTURE cites "the K4 range audit's M-1" (line 230), "the K5 audit's
M-1" (379), "the K5 audit's N-1" (386), "the K4 audit's N-1" (419); README
7 and WALKTHROUGH 8 such item codes (DERIVED, grep). The standard puts
history and process in the Records section. Fix: state the fact ("the
budget side condition is in package vocabulary") and drop the item code.

### N-7 (Note) — miscellany

- Commit `9ea5d71` is titled "K2 (1/3)"; the slice closed with "K2 (2/2)".
- Gate tails quoted as verbatim include wrapper lines the script does not
  emit (`GATE-EXIT=0`, `gate rc=0`, timestamps); c2-notes §12 discloses
  this ("the invoking shell's echo"), k5.1/c1 do not.
- PROVISIONAL list completeness: `SemTripleU_iff_Mem`,
  `MemTripleU_alloc_of_MemTripleU`, `exhibit{A,B,C}_semantic` reach
  `driveU` through `SemTripleU`/`MemTripleU` (measured closure) and are
  covered only by the "every export stated over `driveU`" clause; name them.
- `MemWF.la_pos` (K3): a field added to `MemWF`, which sits in `LaunchCoh`,
  hence in the premises of every allocating export — a public-meaning
  change (the K0 audit's M-1 argument: a stronger launch premise makes those
  exports weaker claims about arbitrary states) taken "on orchestrator
  direction" and recorded [AGENT]. Recorded honestly; arguably an operator
  call. No action needed beyond awareness.

---

## The nine areas

**1. Provenance integrity.** Every 2026-09-03 [USER] entry's quotation
reads as first-person operator speech making operator decisions (audit
scheduling, lane pausing, inclusion of splittable capacity, overnight
autonomy, adoption criterion for RefinedC). Every design/engineering
decision is under an [AGENT] header or tagged inline. Two [USER] entries
carry untagged agent disposition text (N-1). Slice records sampled (ten):
all carry an explicit provenance line; orchestrator direction is tagged
[ORCHESTRATOR 2026-09-03]. No operator ruling is presented as an agent
choice; no agent content sits under a [USER] tag as a quotation.

**2. One-change-at-a-time.** Snapshot tallies re-derived by my own parser
(entries grouped under `kind NAME :` headers incl. `rec`; DERIVED) match
every record EXACTLY: K0→K1 45/1/24; K2→K2.5 47/20/38 (2308→2335 entries);
K3→K4 136/0/0; K4→K5 125/0/0; K5→K5.1 4/0/5; K5→re-pin 0/1/14; C1
43/6/547 (2668→2705); C2 111/0/49 (2705→2816). (a) K2.5: `wps_create`
changed plan→budget (+`hsz`); `wps_create_of_plan`/`wpt_create_of_plan`
exist, are pinned, and restate the old form with `allocCap` read as
`allocBudget ∘ planCost` (N-4 on the `hsz` premise); the K2.5 CHANGED set
is exactly the record's three classes (LaunchCoh family, the allocating
exports/exhibits, `SpikeGS`/`stateInterp`), no non-allocating export moved.
(b) C1: I sampled 20 CHANGED theorems disjoint from the C1 audit's 56
(seeded random over 343 candidates) and hand-read pre/post — all 20 are the
embedding shape (a `{ctl : Ctl}` binder, `M.thread e ρ ctl`, `r.ctl`,
`spikeCtl` in the `CoreRt` literal, `procCtx p rs → procCtx rs`, the
4-tuple). All eight production statements are byte-identical across C1
and C2 (DERIVED by snapshot comparison), and across K5.1 only
`malloc_list_certified_production` moved (the `ids.Nodup` conjunct).
(c) Re-pin: CHANGED is exactly `CerbND.runNDFuel.eq_def`,
`counter_loop_certified_production`, `drive_after_setup`, `driver2_done`,
`fib_certified_production`, `malloc_list_certified_production`,
`prod_run_eqJ`, `region_loop_certified_production`, `runOne_bind_nd` and
five dependency `.eq_def`s; REMOVED `CerbMem.reconstructValue_lemFuel.eq_def`
— the record's table verbatim. K5.1-post → C1-pre (the rebased combined
head) is the same 0/1/14: the rebase added nothing. K3's 25 CHANGED are
`MemWF` (+`la_pos`, recorded), `Frag.kill`/`kill_op` (restriction lifted,
recorded) and their recursors. C2's 49 CHANGED are the record's seven
classes; the `FragProcs` premise on nine PROVISIONAL exports and the
`wps.pre`/`wpt.pre` guard are recorded as [AGENT] deviations with forcing
facts and surfaced for re-adjudication (c2-audit). No unrecorded public
change found.

**3. Genuine-semantics rule.** Measured on the TYPE of every pinned export
(direct constants, and the closure through package-defined definitions):
`driveU`/`dischargeStep` is reached by exactly the documented PROVISIONAL
lane — `engine_adequacyU(_alloc)`, `wpt_engine_boundU(_alloc)`,
`project_triple*`, `semantic_*U`, `SemTripleU_iff_Mem`,
`MemTripleU_alloc_of_MemTripleU`, every `*_certified`/`*_total`/`*_engine`/
`*_semantic`/`*_adequacy`/`*_launch_smoke` exhibit,
`counter_loop_certified_registration`/`_irrelevant_binding` — plus the
device lemmas `stepDischarge_run`, `outcomesU_of_call`, `outcomesU_of_ret`,
`drive_classifyU_aux` (M-2). `procThread` appears only in the `procCtx`
driveU exhibits (PROVISIONAL rows). `CerberusRound` appears in
`engine_step_matchU`, `step_iff_cerberusRound`, `smoke_call_round`,
`smoke_ret_round` (certification exports, stated in the driver's
vocabulary — the accepted 2026-09-02 standard). `runOne` (Step.lean:1385,
`match m with | ND f => f s` — the one-layer application of the engine's ND
monad, no loop) appears directly in `driver2_done`, `loop_step_frag(_same)`,
`loop_step_tau_tsk`, `advance_withrs_killed_*`, `storeM_readonly_kills`,
`killM_killed_inv`, `allocateRegion_killed_inv`, and reaches `prod_run_eqJ`
through `DriverDoneAt` — documented on every surface as "generic collapse
machinery, not a closed statement". The eight shipped-composite exports'
direct package constants (measured): `exhibitA_prod` {prodFile, progAProd,
sevenVal, CellCoh, SpikeCell.mk, intTy, sevenBytes};
`fib_certified_production` {prodFile, fibProg, ivVal, fibSpec};
`counter_loop_certified_production` {prodFile, counterProdProg,
intUndefBytes, sevenBytes, CellCoh, SpikeCell.mk, intTy};
`list_reverse_certified_production` {prodFile, lrProdProg, CellMap, ptrVal,
SeedChain, Sat}; `dispose_list_certified_production` {prodFile, dlProdProg};
`region_loop_certified_production` {regionCost, headroom, prodMem₀,
prodFile, rlProg, loc0} (the documented budget side condition);
`malloc_list_certified_production` {prodFile, mlProg, loc0};
`prod_run_eqJ` {CoreExpr, LabelMap, LabeledAt, prodFile, mainSym, Mem,
DriverDoneAt, prodThread, prodMem₀}. K5.1 and C2 did not regress the K4/K5
standard for the closed statements. Nothing hand-written sits in a
trust-bearing referent.

**4. Axiom/method hygiene.** `collectAxioms` on the eight production
statements + every 10th pin (31): all 39 exactly `[Classical.choice,
Quot.sound, propext]`. Grep for `native_decide|bv_decide|ofReduce|sorry|
admit|axiom|opaque|implemented_by|unsafe|maxHeartbeats|maxRecDepth` over
`CerberusHeapLang/`, `CerberusHeapLang.lean`, `scripts/`: every hit is prose
("small axiom", "opaque" describing engine constants, "admitted" meaning
"zero-size admitted by the engine", `.opaqueInfo`/`.axiomInfo` pattern
matches in the meta scripts); no `set_option maxHeartbeats`/`maxRecDepth`
anywhere (the re-pin's "maximum recursion depth" errors were fixed by
`show`/`rfl` idioms, as recorded). `Audit.lean`: the exhaustive sweep and
banned-axiom sweep iterate `env.constants` filtered by module root only —
`Name.isInternalDetail` is not consulted (read in code). No `axiom`,
`opaque`, `implemented_by`, `unsafe` declarations in the package.

**5. Record integrity.** Verbatim quotations: 3 of the sampled engine-arm/
definition quotes are lightly normalized without markers (N-2); the rest
match whitespace-insensitively or are declared BEFORE-states. Derived
tallies: eight snapshot tallies re-derived exactly (area 2); pin counts
205→221→248→269→294→296→316 consistent across Audit.lean comments, gate
tails and DECISIONS; the dedupe's 12 identity claims verified (N-3). The
K5.1 record's `#check`-printed `regionOwn_ne`/`regionOwn_deadRegion_ne`
match my `#check` output. No paraphrase presented as a theorem statement
was found.

**6. Mirror-OCaml doctrine.** Documented in code with the forcing fact:
`tid` pinned to 0 in `Step.alloc`/`Step.create` ("`allocateRegion` DISCARDS
the thread id (CerbMem.lean:1533, `_ : Nat`), so the rule pins it to `0`;
the certification bridges to the engine's `tid1` by `rfl`");
`requestLoc` (Soundness.lean:1296-1305, Core_reduction.lean:484 cite, "It
reaches only the kill payload and the driver's trace"); `regionCost`
(Heap.lean:2316-2322, "`allocateRegion`'s worst-case cursor descent … no
`max 1` padding"; the conservative bound row in README's divergence
table); `Stack_cons` (the `Ctl` docstring: "not representable by
`Ctl.toStack` and unreachable from `Driver.drive`; step_ctx's value arm
PANICS on it … a fail-closed restriction, stated"); the `_eval` forms
("the mirror pins the evaluated values to INTEGERS … a non-integer value
is the engine's ILLTYPED-at-distance-one round … classified, not
mirrored"); `Step.call`'s stdlib-first `lookupProc` and the whole-expression
statement; `Step.ret_annot`; the congruence guard `toVal e1 = none`. I
found no new deliberate divergence without an in-code forcing fact.

**7. Shop-window truth.** 80 names cited by ARCHITECTURE/README resolve
by `#check` (incl. `Iris.genHeap_init`, `CerbND.fuelExhaustedKill`,
`CerbND.drive_wrapper_defeq`, `MemWF.la_pos`, `Step.ret_annot`,
`Decomp.pot_plug_call_le`). Acceptance ledger: goal 1 OPEN pending the
fuel-lane restatement ✓; goal 2 CLOSED with two characterized residuals ✓;
goal 3 CLOSED ✓. PROVISIONAL story consistent across README/ARCHITECTURE/
WALKTHROUGH §1.3 (every `driveU` row in the exhibits table carries the
label) — except the device lemmas (M-2) and WALKTHROUGH §7's "until the …
request lands" (N-5). Stale/false sentences: M-1, M-4(a), N-5. Process
jargon outside Records: N-6.

**8. Gate/process adherence.** Commit gate claims (checked against
`git show --stat`): `9ea5d71` fast-gate (Lean-changing) ✓; `46ed41f` FULL
with tail in k2-notes ✓; `77c5277` fast-gate ✓; `5bfa4f9` FULL (Heap.lean
doc-comment only + record with tail) ✓; `752eb18`/`af309f4` fast-gate,
`0453ec1` FULL docs-only with tail ✓; `ed3a9fe`/`daa9b5c` fast-gate,
`3dd7843` FULL docs-only with tail ✓; `24264c9` fast-gate, `8eddb24` FULL
with tail ✓; `4e19bdc` fast-gate, `932dfcf` FULL with tail ✓; `a3eb560`
fast-gate, `f2f9701` FULL (pre-rebase tree, 294 pins — disclosed), the
rebased head gated at `8aed7a7` ✓; `cf40966` changes `Audit.lean` (a
comment) in an audit-record commit with no gate claim — covered by the
next commit's recorded gate ✓; `51b2094` fast-gate, `c861031` FULL with
tail ✓; `8d28c21` FULL with tail (c2-notes §12) ✓. No FULL claim on a
Lean-changing commit lacks a recorded tail. Orchestrator independent
gates: present at one boundary only (M-3). Grind ban: longest single pass
≈10 min (C1), C2 ≈2.5 h total, K2.5 time-boxed "at the tripwire (~1 h of
build/proof passes)" — no >1 h pass claimed; no heartbeat/recDepth option
touched (grep).

**9. Grumpy-reviewer items.** Duplication: the K2.5 `freshBase_ne_zero_of_cost`/
`headroom_freshBase` and their K3 primed twins both live and are both
consumed (grep) — kept "frozen" deliberately, recorded; acceptable but a
consolidation candidate. Dead code from prunes: none found — `allocCap`/
`PlanFits`/`advanceCursor` survive only in history comments; `M.labels`/
`M.stack`/`M.proc` survive only in the Audit.lean embedding comment
(correctly describing the OLD fields). Naming across the K-slices is
consistent (`*_atomic` → `wps_*`/`wpt_*` → `_emp`/`_eval`/`_at`/`_regionOwn_at`;
`deadObj`/`deadRegion`, `killM_success`/`killM_success_dynamic`,
`MetaCoh.of_fields`/`_dyn`). `[AGENT]` decisions that touched public
meaning (K2.5's launch-level narrowing, K3's `la_pos`, C2's guard and
`FragProcs`) are each recorded with forcing facts and the C2 ones are
already queued for operator re-adjudication — the process worked as
designed. Commit numbering slip (N-7).

---

## What I could not verify

- The FULL gate at any head (no `lake build` permitted). The primed
  `.lake` was built in the worker tree (`worktrees/calls-c1`); my
  `#print axioms`/`#check`/type queries are against that environment,
  which the C2 record's gate tail says is the final tree; I could not
  confirm olean↔source byte-identity without a build.
- The operator's chat quotations in DECISIONS (plausibility only).
- Wall times and "no park" claims in the records.
- The C1 audit's 56-item hand reading (not redone; my 20 disjoint samples
  all shape-only; my simplified normalizer accepts 249 + 80 auxiliaries of
  the 547 outright and leaves 218 in Config-tuple/projection shapes it does
  not rewrite — not a finding, a limit of my tool).
- Whether `Stack_cons` is unreachable from `Driver.drive` (stated in code,
  not proved — as the C1 audit's N-1 asked and the C2 audit notes).

## Merge recommendation

**Merge after fixes**: M-1, M-2 (choose (a) or (b)), M-4 — docs-only
edits (plus the `trioExports` edit if M-2(a)) — and M-3: one orchestrator
FULL gate at the merge candidate with its verbatim tail in DECISIONS. The
Notes are polish; N-1 (two provenance tags) and N-5 (the false Audit.lean
comment) are one-line edits worth taking in the same pass.

---

## Post-fix verification (same auditor, 2026-09-03, copy `worktrees/audit-final`, HEAD `6eda510`)

Read-only re-verification against the merge candidate (`.lake` primed at
this tree; `.cerberus-ws` linked at `f95ef8d9c`; `pgrep -af 'lake build'`
empty; one 10 s `lake env lean` query, scratch under the gitignored
`.lake/` removed). Records checked: `cerberus-heaplang/docs/2026-09-03_standards-audit-response.md`
(the worker's finding → fix table; note its path is under
`cerberus-heaplang/docs/`, not the repo-level `docs/` the dispatch named)
and the last two DECISIONS entries. The response's Lean edits, by
`git show 787d23e`, are exactly: four names removed from `trioExports`,
comments in `Audit.lean` (header + two pin-list comments), the SCOPE
sentence in `Step.lean`, and the `API.lean` table — no statement or proof
changed, as claimed.

- **M-1 CLOSED.** No "one known admission"/"ONE KNOWN ADMISSION" sentence
  remains in README/ARCHITECTURE/WALKTHROUGH/`CerberusHeapLang/*.lean`
  (grep). The three remaining `auxAddToRfLoad` mentions (ARCHITECTURE
  §6, WALKTHROUGH §6, README trust story) are all in the past tense
  under "Admissions in the pinned semantics tree: none (measured
  2026-09-03)". The quoted measurement is reproducible: `grep -rn '(sorry'
  ../.cerberus-ws/lean_frontend/generated/*.lean` → no hits;
  `Cmm_op.lean` has zero `sorry` occurrences; the bare `sorry` grep
  returns 18 lines here, all comment text (the response says 19 — one
  line of prose difference, not a code hit; DERIVED, grep -c).
- **M-2 CLOSED (option a).** `trioExports` has 312 names (grep of the
  backtick names = 312; `CerberusHeapLang.Audit.trioExports.length`
  evaluated in the environment = 312). `stepDischarge_run`,
  `outcomesU_of_call`, `outcomesU_of_ret`, `drive_classifyU_aux` are
  present in the environment, NOT in the list, and still trio-exact
  (`collectAxioms`: `[Classical.choice, Quot.sound, propext]` each). No
  remaining pin's TYPE mentions `dischargeStep` or `outcomesU` directly
  (measured over all 312). ARCHITECTURE §2 (lines 60-66) and WALKTHROUGH
  §5 (lines 1287-1292) now read "no EXPORT's statement mentions it — the
  lemmas that do (…) are proof devices, unpinned and internal, bounded by
  the package sweep but not exported" — exact against the tree.
  `API.lean`: the worker's premise check is right — the "engine
  transition" row was already in the "Below the line (INTERNAL …)"
  table (my finding mis-attributed it to the PUBLIC table; the
  substantive point, no classification of the Adequacy-side devices,
  stood); the new internal row "The `driveU` lane's proof devices" names
  `dischargeStep`/`outcomesU`/`stepOutcomes`, `stepDischarge_*`,
  `outcomesU_of_step`/`_call`/`_ret`, `drive_classifyU`,
  `drive_classifyU_aux` and states the unpin.
- **M-3 CLOSED.** DECISIONS' last entry quotes the orchestrator's FULL
  gate at `787d23e` with `CerberusHeapLang export pins: 312 trio-exact`,
  `3208 swept`, `4938 constants`, `ALL GATES GREEN`, `GATE-EXIT=0`, and
  makes the recording rule standing. Consistency with the tree: the
  `#eval` that prints those lines is at `Audit.lean:469` (grep `^#eval`),
  the list has 312 names, and README's expected tail, the response
  record (both gate tails) and DECISIONS all say `Audit.lean:469` /
  `312`. `6eda510` is docs-only on top of `787d23e` (`git show --stat`),
  so the recorded gate is at the merge candidate's Lean tree. Not
  independently re-run (no build permitted).
- **M-4 CLOSED.** README exhibits row now
  "`MemTripleU_alloc spikeCtx spikeCtl spikeEnv prog ∅ (allocCost fmapEmpty
  structTy 8) ψ` (the budget form since K2.5)" — the worker correctly
  added the C1 `spikeCtl` argument my proposed text omitted; expected
  tail "export pins: 312 trio-exact"; Records says "K0–K5.1" and names
  the K5/K5.1/re-pin/C1/C2 notes and audits, the standards audit and
  the response; snapshot pointers in README (two) and WALKTHROUGH:15
  read `2026-09-03_c2-signatures-post.txt`.
- **N-1 CLOSED.** `0b86bd2` changes exactly two lines: "Disposition
  [AGENT]:" in the INTERMEDIATE STANDARDS AUDIT entry, and "Disposition
  [AGENT]: the `lane-b-seed` branch …" opening the disposition paragraph
  of LANE B PAUSED — the "Amendment to the copy ruling" sentence sits
  inside that now-tagged paragraph (one tag covers both, an acceptable
  reading; my suggested per-sentence tag was not used).
- **N-2 CLOSED** — c2-notes §1 carries an erratum naming the three
  blocks and each elision. **N-3 CLOSED** — k5-audit Q5 reads
  "`cmp docs/2026-09-03_k5-signatures-pre.txt docs/2026-09-03_k4-signatures-post.txt`"
  again with the dedupe note outside the span; repin-fuel-notes §6
  untangled; the ~30 well-formed in-place rewrites left, reasonably.
  **N-4 CLOSED** — k2.5-notes §4 erratum "holds UNDER the extra premise
  `hsz`". **N-5 CLOSED** — Step.lean SCOPE sentence, Audit.lean K4
  comment, ARCHITECTURE §7 heading and arc-record title now K0–K5.1,
  WALKTHROUGH §6 count and §7 "HAS landed" sentence. **N-6 CLOSED** —
  zero `audit's M-n/N-n` codes in README/ARCHITECTURE/WALKTHROUGH (grep;
  the response's own "before" counts differ slightly from mine because
  it used a broader pattern). **N-7 CLOSED** — K2 record erratum; the
  PROVISIONAL lists name `SemTripleU_iff_Mem` and
  `MemTripleU_alloc_of_MemTripleU` (API.lean header, ARCHITECTURE §6);
  the `la_pos` clause added.

**Verdict: all four Mediums and all Notes are closed as claimed; the
fixes are docs plus the pin-list edit, no statement or proof moved; the
orchestrator's FULL gate at the candidate is recorded verbatim and is
consistent with the tree (312 pins, `Audit.lean:469`). Final merge
recommendation: MERGE AS IS (ff-only, `6eda510`).**
