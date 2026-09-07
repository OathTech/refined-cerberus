# Landability assessment — `dialect-e5` f433820..cb46e4c (the E5 extension past the park record)

Auditor: fresh, independent, skeptical (this file; NOT committed). Fixed
detached copy `worktrees/audit-e5x-cb46e4c` at cb46e4c; semantics pin
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf` (`.cerberus-ws/lean_frontend`
`git rev-parse HEAD` = the pin; `lean-toolchain` 4.32.2). Every lake/lean
invocation under `scripts/capped` with `CERB_MEM_MAX=40G`. Longest single
pass: the FULL gate (a primed replay — 472 jobs, all Replayed, nothing
recompiled; well under the tripwire). Quoted outputs are verbatim; derived
tallies are labelled DERIVED. Graded against `docs/AUDIT-BRIEF.md`; KOI
items are not re-cited unless wrong, worse, or a mover was missed.

**Headline.** The Lean content of the range is sound, mirror-exact by
construction (no `Step`/`Round`/`Soundness`/`DriverCollapse`/`ProdEntry`/
`ProdLoop`/`Adequacy`/`Potential`/`Heap` change — `git diff --stat` empty
on all of them), kernel-only, and honestly stated: three new closed
shipped-driver statements over VERBATIM transcriptions of emitted Core
(`t5`, `t6`, `t4`), each reproduced against the OCaml oracle and against
the compiled Lean composite by me. The range changed the TEXT of exactly
one pre-existing statement (`load_atomic`, strengthened) and removed
nothing. The problems are all on the record/provenance side: an
"already authorized" over-claim in the charter's DECISIONS entry, a
paraphrased `[USER]` permission, a stale state line on the register at
HEAD, a missing candidate-head census snapshot, and an undisclosed budget
slack of 324 units on `t4`. Verdict: **LANDABLE WITH WORK** (record fixes,
one afternoon; no Lean change required).

---

## 0. Range and provenance facts (stated, not judged)

- `git log f433820..cb46e4c`: 14 commits, all authored `Mike Dodds`,
  2026-09-05 21:38 → 2026-09-06 01:28 (+0000). The park record f433820
  (21:01) says verbatim: "A COMMITTED PARK RECORD: THE SLICE HAS ENDED;
  working past it needs the operator's approval." The first range commit
  lands 37 minutes later.
- The agent's authorisation, as it recorded it (DECISIONS, 2026-09-05
  "Resume E5 …"): `[USER] "Yes, please work on E5 & beyond - our intended
  near-term stop-state is that our 'demo' Reynolds/O'Hearn logic is (1)
  good, clean, well-defined in every way, a good demo exemplar, and (2) it
  works on real emitted core produced by cerberus."` I cannot verify the
  quotation; it is plausibly an instruction and is consistent with the
  operator's statement to me that they authorised the continuation.
- `.lake` and `.cerberus-ws` in the audit copy were primed at the pin; the
  gate replayed the build (no module recompiled). I did not force a
  cache-disabled rebuild.

## 1. The three certifications — measured

### 1.1 Statement vocabulary (read off the three statements)

All three have exactly `t1_certified_production`'s shape, with
`hsup : 600 ≤ sup` added:

```
theorem t{5,6,4}_certified_production (sup : Nat) (hsup : 600 ≤ sup) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 [] <tMain>) args)
          ((initial_driver_state sup (prodFileLib stdlibE3 [] <tMain>) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint {1,20,10} ∧ dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = ""
```

Package definitions in the statement: the file builder `prodFileLib`,
the library fragment `stdlibE3`, the program `CorpusE0.t{5,6,4}Main`, the
readout vocabulary `lint`. No driver, loop, discharge, scheduler or mirror
name appears — the referent rule holds. Routes (read off the proofs):
`t*_wpt` (+ `t*_blockSpecsT`) → `wpt_driver_done_alloc` → `prod_run_eqJ_lib1`,
exactly `t1`'s. The `hsb` premise of `wpt_driver_done_alloc` is discharged
by `Nat.le_refl` at `prodCtx … (prodRSLib … sup …)`/`prodCtl sup` — the
production context RETAINS the initial supply (`prodCtx`, ProdEntry.lean:583,
`runState := rs`); only the seeded `procCtx`/`procCtxF` normalise to 0
(Step.lean:6314/:6361, unchanged in the range).

### 1.2 Transcriptions vs `docs/corpus-e0/t{5,6,4}_*.annot.core` — my own structural comparison

The skeleton speedbump covers the WHOLE `main` of each (gate output, verbatim):

```
| t1.annot.core | main | 121 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: n/a; if condition: n/a; case pattern: n/a |
| t5_ifelse.annot.core | main | 271 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: mismatch (expected); if condition: mismatch (expected); case pattern: mismatch (expected) |
| t6_switch.annot.core | main | 299 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: mismatch (expected); if condition: mismatch (expected); case pattern: mismatch (expected) |
| t4_while.annot.core | main | 591 | equal | mismatch (expected) | mismatch (expected) | mismatch (expected) | mismatch (expected) | case scrutinee: mismatch (expected); if condition: mismatch (expected); case pattern: mismatch (expected) |
```

The skeleton is blind to leaf constants, so I compared the LEAVES by hand
against the fixtures (every literal, every printed symbol number, every
printed source region, operand order, pattern shapes, `Astd` strings,
binder types):

- **t5**: `Specified(3)` init; `x > 2` as `OpGt` with `conv_int` on both
  sides, `Specified(1)/Specified(0)` arms, `_ ⇒ Unspecified`; the outer
  `= 0` truth test as `OpEq`; the Boolean decode `not(a_511 = 1)`; the
  `nd(True, False)` arm; then-block `r = 1` at symbols a_523/a_524 and
  regions (46,56)/(48,54)/(48,53,50)/(48,49)/(52,53); else-block `r = 0`
  at a_525/a_526 and (62,72)/(64,70)/(64,69,66)/(64,65)/(68,69); return
  through a_527/a_528, `run ret_507`, `save ret_507 (a_529 := Specified(0))`.
  Every symbol number a_508…a_529, x=505, r=506, ret=507 — MATCH.
- **t6**: inits `2`/`0`; `case a_517 of Specified(a_518) ⇒ let strong
  a_519 = conv_int(a_518) in if a_519 = 1 then run case_521 … ; if a_519 = 2
  then run case_520 … ; run default_522 ; run break_513 ; saves case_521
  (10, a_523/a_524, (52,67)/(60,67)/(60,66,62)/(60,61)/(64,66)), case_520
  (20, a_525/a_526, (75,90)/(83,90)/(83,89,85)/(83,84)/(87,89)),
  default_522 (30, a_527/a_528, (98,114)/(107,114)/(107,113,109)/(107,108)/
  (111,113)); `| Unspecified(_) ⇒ undef(UB036)`; `save break_513`,
  return via a_529/a_530, `save ret_511 (a_531 := Specified(0))` — MATCH.
- **t4**: inits `0`/`0`; the guard's three nested truth conversions with
  the exact symbol pairs (a_519/520, 521/522; a_524/525, 526/527;
  a_529/530, 531/532; a_535/536 → `i < 5` as `OpLt` with `Specified(5)` at
  (50,51), tmp a_534), the short-circuit `case a_540 of Specified(a_541) ⇒
  if a_541 = 0 then (a_542, `<unknown location>`, Specified(0)) else (a_554
  = right side: a_543/544, 545/546 with `not(… = …)`, a_549/550, 551/552,
  `s < 7` with `Specified(7)` at (59,60), tmp a_548)`, `| Unspecified(_) ⇒
  undef(UB_CERB004_unspecified__conditional)`; the Boolean decode on a_517
  /a_518; body: `s = s + i` (a_555/a_563; `unseq(load s via a_561 (68,69),
  load i via a_562 (72,73))`, `catch_exceptional_condition_add` at
  a_558/a_559, regions (64,74)/(64,73,66)/(68,73,70)), `i = i + 1`
  (a_564/a_571; a_565/566, 567/568; a_570 at (79,80); `Specified(1)` at
  (83,84); regions (75,85)/(75,84,77)); `save continue_511`; `run
  while_515(i, s)`; `save break_512`; return via a_572/a_573, `run ret_510`,
  `save ret_510 (a_574 := Specified(0))`; labels while_515/continue_511/
  break_512/ret_510 — MATCH.

Residual blind spots (pre-existing, documented in `CorpusE0.lean`'s
header): the association of `;`-chains (not printed), the unprinted
`Astmt`/`Aexpr` annotations, the unprinted symbol numbers of `x`/`r`/`i`/`s`
(inferred from the sequence), and the locations of unprinted `undef`
leaves. The t4 record states the `;`-association was checked against the
frontend source (`erase_loop_control_aux`/`translate_stmt`/`mk_unit_sseq`);
I did not repeat that inspection (see §9).

### 1.3 `Frag` membership — kernel-decided, compositional

`Examples/CorpusE5.lean`: `t5Main_frag`, `t6Main_frag`, `t4Main_frag` are
compositional `Frag` derivations; leaves discharged by `decide`/`rfl`/
`Nat.le_of_ble_eq_true rfl`; case branches for EVERY scrutinee value via
`t6Switch_select`/`t4And_select` (any `LVspecified o`) and
`Frag.substFold_pure` (Substitution.lean: substitution preserves `PePure`
and depth, by fuel induction on the genuine `subst_sym_pexpr_lemFuel`).
Gate 1: `ok: no banned proof-method references`. The `nd(True, False)` arm
is admitted (`Frag.nd`), OUT-OF-SCOPE for rules, never reached — as the
manifest says.

### 1.4 The oracle — reproduced by me (verbatim)

`cd /home/dev/projects/cerberus-lean-proj && scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc --exec [--batch] refined-cerberus/worktrees/audit-e5x-cb46e4c/docs/corpus-e0/<t>.c`:

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

(`scripts/ce`'s env banner and `Time spent` lines elided.) Binary
`cerberus-lean/_build/default/backend/driver/main.exe` dated 2026-09-05
19:47 — the SAME binary the park record §S2.6 used (built at primary HEAD
9a7f7ad31; the primary is now at 89f7e6885, a docs-only commit later);
NOT the pin. Same caveat as E4/E5 records; the values agree with the three
theorems' readouts (`lint 1`/`lint 20`/`lint 10`, `dres_blocked = false`,
empty streams).

### 1.5 The compiled Lean composite and the budgets — measured

Scratch `probe.lean` (`lake env lean --load-dynlib=<libcf.so>` under
`capped`; the `.so` = the workspace's compiled `ir/CerberusFresh.c.o.export`
linked with `native/md5.c`, needed only because `initial_driver_state`
reaches the `cerb_digest_get` extern; 1.9 s wall). The inner loop is
`drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty fmapEmpty [0]` from
`prodEntryStateLib stdlibE3 [] 600 <tMain> CerbFS.fs_initial_state`;
`firstActive` is a binary search for the least `fl` whose verdict is
`Active` (monotone in `fl`). Verbatim:

```
"t5Main: first fl with the inner loop ACTIVE (PROGRAM-DONE) = 69; verdict@68 = killed:Error0:lem: fuel exhausted; verdict@67 = killed:Error0:lem: fuel exhausted; verdict@69 = active; verdict@300 = active"
"t6Main: first fl with the inner loop ACTIVE (PROGRAM-DONE) = 67; verdict@66 = killed:Error0:lem: fuel exhausted; verdict@65 = killed:Error0:lem: fuel exhausted; verdict@67 = active; verdict@300 = active"
"t4Main: first fl with the inner loop ACTIVE (PROGRAM-DONE) = 593; verdict@592 = killed:Error0:lem: fuel exhausted; verdict@591 = killed:Error0:lem: fuel exhausted; verdict@593 = active; verdict@1500 = active"
"t5 sup=600: active; value==lint 1: true; ==lint 20: false; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t6 sup=600: active; value==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t4 sup=600: active; value==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''"
"t5 sup=0: active; value==lint 1: true; ==lint 20: false; ==lint 10: false; blocked=false; stdout=''; stderr=''"
"t4 sup=0: active; value==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''"
"t4 sup=575: active; value==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''"
```

DERIVED slack (the driver theorem delivers PROGRAM-DONE within `k + 2`
iterations of the inner loop; KOI B6's convention):

| program | `wpt` budget k | driver bound k+2 | measured PROGRAM-DONE fuel | slack |
|---|---|---|---|---|
| t5 | 88 | 90 | 69 | 21 |
| t6 | 78 | 80 | 67 | 13 |
| t4 | 915 | 917 | 593 | **324** |

Nothing in the tree claims tightness ("rule-composed upper bounds",
"proved sufficient budgets, not claims of minimal concrete run lengths" —
e5-resume, t4-loop records). But KOI B6 lists every other statement's
slack numerically and does NOT list these; t4's is the largest in the
package by far (≈ 55 % over the measured run; the per-iteration 159 vs a
measured ≈ 100). Record it (fix R-3).

**The supply premise `600 ≤ sup`.** Honest and disclosed on every surface
(README, ARCHITECTURE §2.5 table, CLAIMS C15–C17 rows, the theorem
docstrings): it is the floor above every program symbol number (t5 max
529, t6 max 531, t4 max 574) that lets `envAdd_lookup … (if_neg
(symOrd_ne_eq_of_num_ne …))` keep source bindings across the fresh
`fresh_given_int k` the assignment protocol draws. It is SUFFICIENT, not
necessary: measured above, the composite delivers the same values at
`sup = 0` and `sup = 575`. The number 600 is a round over-approximation
chosen in the orchestrator's own park plan (§S2.7 item 7), so this is not
a deviation; it is a numeral in a statement where the principled form
would be a program-derived bound (`maxSym tMain < sup`). Optional (R-7).

## 2. The E5 slice-2 debts (KOI C19 as parked) — paid?

| debt (park §S2.7) | status | evidence |
|---|---|---|
| 1. pins for the slice-2 theorems (exhaustive-pins convention) | **PAID** | Audit.lean: the E5 (2/2) paragraph pins the 12 fragment + 55 execution-slice names; every sub-trio name is listed in comments; the gate: `export pins: 896 trio-exact` |
| 2. five stale NO-RULE rows | **PAID, with an instrument change** | the rows are `RULE-PARTIAL-UNDEMONSTRATED` — a NEW manifest class the agent added (`capability_manifest.lean`: `rulePartialUndemonstrated`; the row is red if the partial face acquires a consumer). The park planned `.rule`, which would have turned red (rule (3) needs both faces consumed). The class is honest and symmetric; [AGENT] decision, disclosed in DECISIONS. |
| 3. MirrorCoverage witnesses | **PAID** | `neg_bound_round`, `excluded_store_round`, `excluded_store_eval_round`, `case_eval_round` (MirrorCoverage.lean), all via `engine_step_matchU`, all pinned |
| 4. skeleton extension for scrutinee positions + plant | **PAID** | `cutUntilKw`/`scanOperand`, `if`/`case`/pattern tokenisation; THREE plants (`wrapFirstCaseScrutinee`/`wrapFirstIfScrutinee`/`wrapFirstCasePattern`), each `n/a` on rows without the position and RED if no row exercises it (gate output above) |
| 5–7. transcriptions, `Frag` proofs, derivations, `*_certified_production` with `hsup : 600 ≤ sup` | **PAID** (§1) | |
| 8. `seq_rmw`, `PtrValidForDeref`, `Elet` | not started, **honestly classified** | e5-resume §"Still required": "remain on the wider dialect list" (E6 items; not in the E5 acceptance set) |
| 9. API.lean `Frag.pot_le_two` cell | **PAID** | the cell now reads `Frag.pot_step_bound (for a negative-free step; negative rewriting is bounded separately)`; `pot_le_two` survives only in Potential.lean:33's prose ("false for the additive …") |
| 9. census snapshot for slice 2 | **PARTIAL** | `docs/2026-09-05_e5b-signatures-post.txt` at the t5 checkpoint (1d04dd7) — reproduces the agent's 136/2/17. NO snapshot at the candidate head: t6+t4 add 236 declarations after it (§5). Convention in every prior slice: post snapshot at the slice head. |
| 9. `cite_check.sh` last | **PAID** (report-only) | rerun by me at HEAD: `cite-check: ARCHITECTURE.md — 277 cites; EXACT 176; DECL 52 (fixed 0; ranges among them counted in RANGE); USE 19; HAND 21; PIN 9; NOFILE 0; RANGE 25 (never rewritten)` — identical to the t4-loop record; the manual queue is disclosed, not cleared |
| the range audit 8eeaf92..HEAD (the resumer's FIRST action after slice 2) | **NOT DONE — a brief was prepared, not dispatched** | `docs/2026-09-06_e5-range-review-brief.md`; the agent correctly left dispatch to the operator |

## 3. Soundness and mirror exactness of what the range added

- **Core-module changes: none.** `git diff --stat f433820..cb46e4c` is
  empty on Step/Round/Soundness/DriverCollapse/ProdEntry/ProdLoop/Adequacy/
  Potential/Heap/TotalAdequacy/EvalClass/StdCore/IntRules. No new mirror
  arm, no new round certification obligation, no judgment definition
  change (`wps`/`wpt` SAME in the census).
- **New rules** (all derived against existing `Step` arms; all trio-exact
  by the build and by `#print axioms`, re-measured by me):
  - `wps_seq_sym_annot`/`wpt_seq_sym_annot` (Wps/Wpt): the strong symbol
    binder at an ANNOTATED head, over the E1 mirror arm `Step.sseq_sym_annot`
    (present at f433820:Step.lean:4233, classified by `complete_beta_sym`);
    proof structure = `wps_seq_sym`'s (11-arm `sseq_inv` case split, Löb /
    strong induction on the budget). Correctly re-wraps `Eannot ds e2`.
  - `wps_load_footprint`/`wpt_load_footprint` + `loadFootprint`/
    `do_race_loadFootprint` (Rules): corollaries of `load_atomic`.
  - `wpt_unseq_pure_right`, `wpt_unseq_pure_left`: DERIVED from
    `wpt_unseq_focus`/`wpt_pure`/`wpt_unseq_vals`; the order is the
    engine's (LAST component first): `_right` evaluates the pure operand in
    the initial frame BEFORE `e`; `_left` runs `e` first and evaluates the
    pure operand in `e`'s resulting frame. Sound by construction.
  - `Substitution.lean` (core class): syntactic lemmas over the genuine
    fuelled substitution; `Frag.of_pePure`, `Frag.substFold_pure`.
  - EnvLaws: `SymMap.addLabel`/`labelAdd_lookup` (the collector's `fmapAddBy
    symCmpL` BEq spelling — a real gap the t6 label map exposed, proved
    structurally, no heartbeat bump), `update_env_tuple2_mixed`.
- **The ONE statement-text change of the range**: `load_atomic` — the
  delivered value's footprint is now the concrete `loadFootprint M.tagDefs
  pv ty` instead of `∃ fp` (strictly stronger; `wp_load`/`wps_load`/
  `wpt_load` texts unchanged, they re-introduce the existential). Reason
  recorded (t4-addition record: the read/read race check of `s + i`).
  Census e5b→HEAD: `CHANGED: ['CerberusHeapLang.load_atomic']` only.
- **The E5 §S2.5 design point** (seeded `procCtx`/`procCtxF` normalise
  both supplies to 0): **KEPT UNCHANGED** (Step.lean untouched; `procCtx`
  SAME in the census), disclosed in ARCHITECTURE ("This seeded-profile
  definition change remains an E5 range-audit item") and in the review
  brief. It is STILL an open [USER] decision (open to veto since the park);
  the agent did not decide it — good — and nobody has ruled it (fix R-4).
- The `bound` rules' `negFree` premise is respected: every emitted
  assignment `bound(… neg(store …) …)` goes through `wpt_neg_bound`/
  `wpt_bound_wseq_tuple`, never `wpt_bound`.

## 4. Process and provenance

- **Working past a committed park record.** Facts in §0. The agent's own
  entries repeatedly say "This checkpoint continues the active goal; it is
  not a park", and it prepared but did not dispatch the range review,
  respecting the audit-ask rule. Whether the quoted `[USER]` resume
  instruction satisfied "the operator's approval" is for the operator; the
  operator has told me it did. The register should carry that
  confirmation verbatim (fix R-1c) — today the only record of it is the
  agent's quotation.
- **The charter's authorisation sentence** ("The user has authorized
  execution of this charter in full") is a direct reading of the quoted
  goal text ("Complete the work described in docs/…charter.md in full …"),
  not a stretch. The lowercase "respect" in the quote is consistent with a
  typed command.
- **A paraphrased `[USER]` tag.** DECISIONS 2026-09-05 "User adopts…":
  `[USER, paraphrase] Standing permission to request an early exit … Ordinarily the agent should resolve strategic choices itself.` A paraphrase is labelled as one, but the register's rule is verbatim-or-nothing, and this particular paraphrase grants a broad permission ("resolve strategic choices itself"). Fix R-1b: either the verbatim words or an [AGENT] "my reading of the goal command" line.
- **"Already authorized" over-claim.** DECISIONS "Draft a charter…":
  `[AGENT] … It consolidates the already authorized two-part demo goal, E5–E7 and the dependency/fuel update, the emitted-file/library connection, exemplar cleanup and final review.` Against the standing rulings: E5–E7 are ruled (`[USER] "Agree, Let's do E5-E7."`); "direct emitted C calls and their scheduler protocol" = E6 as designed (C.6) — in scope; "t8's array support is part of the agreed emitted corpus" — yes (ruling (2): "the corpus minus the struct program at arc end"; design C.8: t8 accepts after E6). BUT the "dependency/fuel update" (KOI A6: "Re-pin waits for the NEXT cerberus-lean pin ([USER]: 'it'll likely have moved again')") and "the emitted-file/library connection" (KOI A7: "the option-(a) form when the elaborator can sit in the statement"; E0 ruling (3): the hand-transcribed term + executable-equality speedbump is the ACCEPTED form, the elaborator-in-statement is the "named target, not done") were NOT previously authorised as demo requirements. The charter's Criterion 3 ("The present three-function wrapper and skeleton comparison alone do not meet this criterion") and M2 ("deliberate compatible re-pin" before E6, the preflight's "Target the current clean semantics head") are [AGENT]-authored scope, now [USER]-adopted THROUGH the goal command. That is a legitimate way to gain scope, but the register must say so; "already authorized" is false as written. Fix R-1a.
- **DECISIONS style.** The agent's 14 entries are `## date — title`
  headings (the register's convention is `- **date [TAG] …**` bullets; 129
  bullets vs 1 pre-existing heading before the range); tags sit inside the
  body; no gate tail is quoted in the register (the orchestrator's landing
  entries carry the verbatim tail; the agent's point to records whose
  "selected output, verbatim" omits the `== gate …` headers and
  per-module lines). Substantively the entries are honest checkpoint logs
  and consistently say what is NOT claimed. Hygiene (R-6).
- **"docs: record current dependency and fuel contracts for the next
  scout" (cb46e4c)** = `docs/2026-09-06_dependency-fuel-preflight.md`, a
  read-only inventory. I verified every factual claim against the sibling
  repos: cerberus-lean primary `89f7e688530c6910884518811d645e4e892e4507`,
  `git rev-list --count f95ef8d9c..HEAD` = 109; `0a62dd7f7..89f7e6885` =
  one file (`docs/2026-09-05_orchestrator-handoff.md`); lem-lean primary
  `f6542f8e6860d12d4655e6648bc4c45dabd1d798` = cerberus-lean's Lake
  requirement; `class LemFuel where fuel : Nat` (LemLib.lean:66, no global
  instance); `get_ctx g = get_ctx_lemFuel (generic_expr.lemSize g + 1) g`
  (Core_reduction.lean:387); `Pmap.WF`/`WF_add`/`find?_add_same`/
  `find?_add_other` (LemLibPmapLaws.lean:107/351/359/364); `Acyclic`/
  `AcyclicPair` (CerbTagsWf.lean:144/154); `CerbGlobal` readers with
  `*_eq : … = default` theorems (CerbGlobal.lean:186–191); the fuel
  constants DELETED (CerbFuel.lean:22–23). ACCURATE. Its "Next concrete
  action" (scout against the current clean head) is an [AGENT] proposal in
  tension with KOI A6's [USER] "waits for the next pin" — an operator
  decision before M2 (R-4).

## 5. Census — reproduced

`scripts/signature_snapshot.lean` at HEAD (26.3 s wall) → 4954 entries.
Verbatim (my `census.py`, the E4 auditor's method):

```
===== PRE(slice-1 post) -> HEAD
PRE 4584 entries; POST 4954 entries; ADDED 372 / REMOVED 2 / CHANGED 18
ADDED by kind: {'opaque': 4, 'def': 155, 'theorem': 213}
REMOVED: ['CerberusHeapLang.procCtxF_runState', 'CerberusHeapLang.procCtx_runState']
CHANGED: ['CerberusHeapLang.eo_wp_readout', 'CerberusHeapLang.fr_wp_readout', 'CerberusHeapLang.load_atomic', 'CerberusHeapLang.negFree.eq_def', 'CerberusHeapLang.wps_sound', 'CerberusHeapLang.wps_sound_cps', 'CerberusHeapLang.wps_sound_empty', 'CerberusHeapLang.wps_sound_frame', 'CerberusHeapLang.wps_sound_frame_empty', 'CerberusHeapLang.wpt_driver_aux', 'CerberusHeapLang.wpt_driver_cps', 'CerberusHeapLang.wpt_driver_done', 'CerberusHeapLang.wpt_driver_done_alloc', 'CerberusHeapLang.wpt_driver_done_procs', 'CerberusHeapLang.wpt_sound', 'CerberusHeapLang.wpt_sound_cps', 'CerberusHeapLang.wpt_sound_empty', 'CerberusHeapLang.wpt_step_eq']
===== e5b (t5 checkpoint) -> HEAD
PRE 4718 entries; POST 4954 entries; ADDED 236 / REMOVED 0 / CHANGED 1
ADDED by kind: {'def': 109, 'theorem': 127}
CHANGED: ['CerberusHeapLang.load_atomic']
===== PRE -> e5b
PRE 4584 entries; POST 4718 entries; ADDED 136 / REMOVED 2 / CHANGED 17
```

- The agent's t5-checkpoint tally (136 added / 2 removed / 17 changed; 86
  theorems) REPRODUCES exactly.
- The 17 changed at e5b and the 2 removed are the PARK's slice-2a
  (09a89c7, before f433820): exactly the §S2.2 list (the six `*_sound*`
  faces + both `_cps`, the five `wpt_driver_*`, `wpt_step_eq`,
  `negFree.eq_def`, `eo/fr_wp_readout`) — DERIVED by matching the list and
  confirmed by the range diffs of Wps/Wpt/ProdLoop (no statement edits).
  The range's OWN text change is `load_atomic` alone (§3).
- Headline statements (`exhibitA_prod`, the eight `*_certified_production`,
  `t1_certified_production`, `exhibitA_prod_e1`/`B_e2`/`C_e3`,
  `fib_rec_certified`, `even_odd_certified`, `MemTriple`,
  `project_triple_pure`, `DriverSafeCtl`, `DriverDoneCtl`,
  `prod_run_eqJ_lib1`, `wps`, `wpt`, `Frag`, `Step`, `procCtx`, `prodCtx`,
  `loop_step_frag`, `engine_step_matchU`): ALL `SAME` vs the slice-1 post.
- Pins: 896, all trio-exact (the build). Sub-trio, unpinned, re-measured
  by me: `t4Index_cases`/`t4Sum_le`/`t4Guard`/`t4Budget_succ`
  `[propext, Quot.sound]`; `t4Sum_succ`/`t4Kill_eq`/`t6Kill_eq`/`t5Kill_eq`/
  `t5Store_eq` axiom-free; `t{4,5,6}Main_pot`, `peDepthList_map_eq`,
  `peDepthAlts_map_eq` `[propext]` — as the Audit.lean comments and records
  say. DERIVED reconciliation of e5b→HEAD's 127 theorems: 117 new pins
  (779→896) + 9–10 listed sub-trio ≈ 127.
- **Missing**: no committed snapshot at the candidate head (R-2).

## 6. Shop-window truth at HEAD

Checked: root `README.md`, `cerberus-heaplang/README.md`, `ARCHITECTURE.md`,
`docs/CLAIMS.md`, `docs/CAPABILITY_MANIFEST.md` header, `API.lean` table,
`docs/KNOWN-OPEN-ITEMS.md`, `docs/WALKTHROUGH.md` (unchanged in range; no
stale count found by grep).

- The new exhibits are described honestly everywhere I looked: "emitted",
  "transcribed", "constructor skeleton is checked", "same `prodFileLib
  stdlibE3` file boundary as t1", "KOI A7 open", "initial symbol supply of
  at least 600", "E5's full range review remains open". The count
  "thirteen closed shipped-driver statements" (9 + t1 + t4/t5/t6) is right;
  "eleven one-procedure statements (seven authored + four emitted)" is
  right.
- **False at HEAD**: `docs/KNOWN-OPEN-ITEMS.md` STATE LINE: "t4 has
  whole-term membership and a public total condition proof, both
  assignments and the complete body through its back edge; the decreasing
  loop invariant and exit/return proof are next" — stale since f60cdcf
  (the same commit updated C19 to "t4 closes its decreasing invariant …
  at budget 915"). R-3a.
- Stale-but-labelled: KOI §E "Expected FULL tail at the E4 candidate: 652
  pins … BOUNDARY: 24 modules" (labelled E4; the current tail is below).
- ARCHITECTURE §2.5 table: the t4/t5/t6 rows cite `CorpusT*Exhibit.lean`
  without line numbers (every other row has `:NNN`). Cosmetic.
- ARCHITECTURE/README describe the 600 floor as required "to protect
  source bindings"; add "sufficient, not necessary" (measured, §1.5). R-3b.

## 7. Hygiene / quality

- Warnings: package (`CerberusHeapLang/*`) 48 = baseline (Potential 31,
  Round 7, Rules 2, Heap 2, EnvLaws 2, TreeRot/Struct/Soundness/
  ProdLoopExhibit 1) — the range introduced none (its 572 raw `warning:`
  lines are all replayed DEPENDENCY oleans, `generated/*`, LemLib).
- Tree clean at HEAD (`git status` empty); no stray/WIP files; commit
  messages carry the fast-gate/full-gate labels (two-tier discipline);
  three t4 commits lack the `E5:` prefix (trivial).
- Layering smells (disclosed by the agent as cleanup debt, correct to
  list): `Examples/EmittedInt.lean` (example-support) imports
  `CorpusT1Exhibit` (a positive client) for `t1sym_eval`/
  `t1ConvLoadedInt_eval`; `CorpusT6Exhibit`/`CorpusT4Exhibit` import
  `CorpusT5Exhibit` (client → client) and reuse `t5a`/`t5Pure`/macros; the
  import-direction speedbump only polices `core`, so this is invisible to
  the gate.
- Kept aliases `t5IntMval`/`t5IntBytes`/`t5Int_encodes`/`t5Int_storable`
  delegating to `emittedInt*` (dead names).
- ``subst_sym_pexpr_lemFuel.eq_def`` (a GENERATED equation lemma of the
  semantics dependency) sits in `trioExports` as a package "export".
  Harmless, wrong list.
- Six new `show lemDefaultFuel = 999999 + 1 from rfl` sites (CorpusT5:579,
  CorpusT6:647, CorpusT4:1457, EnvLaws:459, CorpusE0:1118/:1157) — the
  pre-existing package idiom (182 sites at f433820), not the bare-literal
  class the E4 audit's H-1 removed. Note only.
- `docs/2026-09-05_e5b-axioms.txt` and `…e5-t6-execution-axioms.txt`
  (raw `#print axioms` dumps) begin with the `cerberus-lean-proj env: …`
  stderr banner — a stray line in a committed record.
- Records: eight dated notes for one slice (resume, t6, t4, condition,
  addition, body, loop, brief, preflight) — verbose but each states
  scope, gate output, and what is NOT claimed; no false claim found.
- Over-elaboration: none in the Lean; the label specs (`t4LsT`: `ret` and
  `while` only; continue/break un-specified because never jumped to) are
  the minimal honest ones.

## 8. The FULL gate — verbatim verdict tail

`CERB_MEM_MAX=40G scripts/test_unit.sh` from the audit copy's root
(second run; the first run's log landed in a sandbox-private `/tmp` and
was unreadable — its exit code was 0). Lines matching
`^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE|^Build completed|^BOUNDARY`,
per-module boundary lines elided:

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1061:0: CerberusHeapLang export pins: 896 trio-exact
info: CerberusHeapLang/Audit.lean:1061:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6050 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1061:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9140 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (472 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 18 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
GATE-EXIT=0
```

Manifest tail (regenerated, no drift): `MANIFEST: 35 constructors, 77 variant rows (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 6 OUT-OF-SCOPE), 0 red, 25 consumer modules` / `CLAIMS: 17 claim rows, 184 declaration names checked …`.

---

## 9. VERDICTS

| group | commits | verdict | why / the work |
|---|---|---|---|
| **t5** transcription + certification | 405261b, 1d04dd7 | **LANDABLE AS-IS** (Lean); record work shared with the range (R-2, R-3) | verbatim transcription (§1.2), compositional `Frag`, budget 88 (slack 21), oracle + composite agree; pays debts 1–5, 7, 9; the e5b snapshot is included |
| **charter docs** | 4970bc1, 7a1ea1f | **LANDABLE WITH WORK** (provenance) | R-1a: "already authorized" is false for the A7 closure (Criterion 3) and the re-pin (M2) — tag them [AGENT]-proposed / [USER]-adopted-by-goal; R-1b: the `[USER, paraphrase]` permission; R-1c: the operator's confirmation of the resume past the park, verbatim. Content is otherwise consistent with the standing rulings (E5–E7 approved; E6 = direct calls + scheduler protocol; corpus = ten minus t7, so t8 in) |
| **t6** | db3967f, 41bee5d | **LANDABLE AS-IS** | verbatim (§1.2); five engine-registered continuations checked by `rfl` against `collect_saves`; `labelAdd_lookup` closes a real BEq-spelling gap structurally; budget 78 (slack 13); oracle + composite agree |
| **t4** | 68bc8d2, ef0255e, c086678, 4f06efc, 12a37f9, f60cdcf | **LANDABLE WITH WORK** | the logic is right and complete (decreasing invariant `i = n, s = Σ_{j<n} j, n ≤ 5`; both kills; dead cleanup retained); the one statement-text change (`load_atomic`) is a strengthening with a recorded reason; the two new rule pairs and two derived rules are sound by construction. Work: R-3a (stale KOI state line), R-3c (record the 324-unit slack in KOI B6), R-6 (EmittedInt → client import; client → client imports; aliases; the pinned `.eq_def`) |
| **review brief** | 7191dec | **LANDABLE AS-IS** (a proposal, not a ruling) | honest; explicitly unratified; the partial-face disposition is an operator/API choice (see R-5) |
| **dependency/fuel contracts** | cb46e4c | **LANDABLE AS-IS** (docs) with an operator decision attached | every factual claim verified (§4); its "target the current clean head" is an [AGENT] proposal against KOI A6's [USER] "waits for the next pin" — decide before M2 |

Nothing in the range is OFF-TARGET against a standing ruling, and nothing
is a REJECT. The one place scope moved beyond the rulings (Criterion 3 /
M2) was moved by the operator's goal command, and needs only correct
provenance.

## 10. Overall recommendation and the exact fixes required before a merge ask (ranked)

**LANDABLE WITH WORK.** No Lean change is required for landing; the
required work is on the register and shop-window surfaces, plus one
snapshot. The operator's E5 range audit (8eeaf92..HEAD, the park's own
first-action rule) is still owed before the merge ask; this assessment
covers f433820..HEAD only and does not replace it.

1. **R-1 Provenance (DECISIONS + charter).** (a) Amend (append-only, a
   later entry) the "Draft a charter" entry: the A7 closure (Criterion 3)
   and the dependency/fuel re-pin (M2) were NOT "already authorized"; they
   are [AGENT]-proposed scope adopted by the [USER] goal command of
   2026-09-05 — and say so in the charter's status block. (b) Replace the
   `[USER, paraphrase]` early-exit/strategic-choices permission with the
   verbatim words or re-tag it `[AGENT reading of the goal command]`.
   (c) Record the operator's confirmation that the resume past f433820 was
   authorised, verbatim, in the register.
2. **R-2 Census.** Commit `docs/2026-09-06_e5c-signatures-post.txt` (the
   candidate-head snapshot; mine reproduces at 4954 entries) and the
   derived tallies (slice-1 post → HEAD 372/2/18; e5b → HEAD 236/0/1;
   `load_atomic` the only range-owned text change), as every prior slice
   did.
3. **R-3 Record truth.** (a) Fix the KOI state line (t4 is complete at
   915). (b) On README/ARCHITECTURE say the 600 floor is sufficient, not
   necessary (measured: the composite delivers the same values at
   `sup = 0`). (c) Add the measured slack to KOI B6: t5 21, t6 13, t4 324
   (budget 915 vs PROGRAM-DONE at inner-loop fuel 593). (d) Line cites for
   the three new rows of ARCHITECTURE §2.5's table; refresh KOI §E's
   expected tail to HEAD's.
4. **R-4 Two [USER] decisions the range carries forward, unruled.** (a) The
   E5 §S2.5 seeded-profile normalisation (kept, disclosed, still "open to
   veto" since the park) — rule it. (b) M2's re-pin target (current clean
   head vs "the next pin") — rule it before the scout starts.
5. **R-5 The partial faces (7 RULE-PARTIAL-UNDEMONSTRATED rows).** Not
   blocking. Either accept the brief's disposition (proved, undemonstrated,
   honestly classified) or take the cheaper closure the park itself
   suggested (§S2.5 item 4): one partial client — `t5` at `wps`, as `t1`
   carries both strata — would consume five of the seven partial faces;
   `wps_seq_sym_annot`/`wps_load_footprint` are t4-only shapes.
6. **R-6 Hygiene (queue with KOI C17, not blocking).** `EmittedInt` must not
   import a client (move `t1sym_eval`/`t1ConvLoadedInt_eval` to example
   support); drop client→client imports (`CorpusT6/T4 → CorpusT5`); delete
   the `t5Int*` aliases; move ``subst_sym_pexpr_lemFuel.eq_def`` out of
   `trioExports`; strip the env banner from the two axiom dumps; register
   entries in the bullet style with the gate tail verbatim.
7. **R-7 Optional.** State the supply premise as a program-derived bound
   (`maxSym tMain < sup`) instead of the numeral 600 — the no-magic-values
   spirit; the numeral came from the park plan, so this is not a
   deviation.

## 11. Verified true (by measurement in this audit)

- All 896 pins trio-exact; manifest 77 rows / 0 red / no drift; corpus
  skeleton 4 rows equal, 7 plants mismatch, 3 operand plants exercised;
  import direction 18 core; boundary 29 modules / 0; `ALL GATES GREEN`,
  exit 0; package warnings 48 (baseline).
- Oracle: t5 `Specified(1)`/exit 1, t6 `Specified(20)`/exit 20, t4
  `Specified(10)`/exit 10 (binary at primary 9a7f7ad31-era, not the pin —
  the standing caveat).
- Compiled Lean composite at `sup = 600`: t5 → `lint 1`, t6 → `lint 20`,
  t4 → `lint 10`, unblocked, empty streams (and the same at `sup = 0`).
- Inner-loop PROGRAM-DONE fuel: t5 69, t6 67, t4 593 (vs k+2 = 90/80/917).
- The three transcriptions match their fixtures leaf-by-leaf (§1.2) and
  skeleton-by-skeleton (the gate).
- The three production statements use only program / `prodFileLib` /
  `stdlibE3` / `lint` beyond engine vocabulary; the route is t1's.
- Core modules untouched; `procCtx`/`prodCtx`/`wps`/`wpt`/`Frag`/`Step`
  texts SAME; the range's only statement-text change is `load_atomic`.
- Census: the agent's t5-checkpoint tally 136/2/17 reproduces; e5b→HEAD
  236/0/1; all headline statements SAME.
- Sub-trio names as recorded (`#print axioms`, §5).
- `cite_check.sh` at HEAD: 277 / EXACT 176 / DECL 52 / USE 19 / HAND 21 /
  PIN 9 / NOFILE 0 / RANGE 25 — as the t4-loop record states.
- Every factual claim in the dependency/fuel preflight (§4).
- Slice-2 debts paid as tabulated in §2 (census partially).

## 12. Not checked

- A cache-disabled rebuild (the gate replayed the primed `.lake`).
- The `;`-association of t4's/t6's blocks against the frontend source
  (`erase_loop_control_aux`/`translate_stmt`/`mk_unit_sseq`) — the agent's
  claim; the skeleton is blind to it, as is the theorem/oracle agreement.
- The unprinted symbol numbers of `x`/`r`/`i`/`s` (inferred; α-equivalent
  either way).
- The 11-arm `sseq_inv` case analysis of `wps/wpt_seq_sym_annot` line by
  line against the E1 certification of `Step.sseq_sym_annot` (pre-range;
  the proof compiles and pins trio-exact).
- `cite_check`'s manual queue (52 DECL / 21 HAND / 25 RANGE lines)
  individually.
- The full E5 range 8eeaf92..f433820 (slice 1 + the park's slice 2a): not
  in my brief; the range audit the park record demands is still owed.
- The generality of the `sup = 0` observation (one run each; no theorem).

Ephemeral scratch used (container `.tmp/audit-e5x/`: `probe.lean`,
`census.py`, `libmd5.so`/`libcf.so`, `head-signatures.txt`, `gate.log`) —
deleted at the end of this pass; the probe's source is reproduced in §1.5
in prose and the commands are stated inline.

---

## Appendix A — reproduction recipes (verbatim scratch sources)

**A.1 `probe.lean`** (run from `cerberus-heaplang/`:
`CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean --load-dynlib=<libcf.so> probe.lean`;
`libcf.so` = `cc -shared -o libcf.so ../.cerberus-ws/lean_frontend/.lake/build/ir/CerberusFresh.c.o.export libmd5.so -L $TC/lib/lean -lleanshared -Wl,-rpath,$TC/lib/lean`,
`libmd5.so` = `cc -shared -fPIC -I $TC/include -o libmd5.so ../.cerberus-ws/lean_frontend/native/md5.c`,
`TC = ~/.elan/toolchains/leanprover--lean4---v4.32.2`; without the dynlib
the interpreter stops at the `cerb_digest_get` extern reached by
`initial_driver_state`):

```lean
import CerberusHeapLang
open CerberusHeapLang

#print axioms CerberusHeapLang.t4Index_cases
-- … (the sub-trio names of §5, and t{5,6,4}_certified_production, load_atomic,
--     wpt_unseq_pure_left, wps_seq_sym_annot)

def verdict (e : CoreExpr) (fl : Nat) : String :=
  match CerbND.runND (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty fmapEmpty [0])
      (prodEntryStateLib stdlibE3 [] 600 e CerbFS.fs_initial_state) with
  | [(nd_status.Active _, _, _)] => "active"
  | [(nd_status.Killed _ (.Error0 _ msg), _, _)] => s!"killed:Error0:{msg}"
  | [(nd_status.Killed _ (.Undef0 _ _), _, _)] => "killed:Undef0"
  | [(nd_status.Killed _ _, _, _)] => "killed:other"
  | l => s!"n={l.length}"

partial def firstActive (e : CoreExpr) (lo hi : Nat) : Nat :=
  if lo ≥ hi then lo else
  let mid := (lo + hi) / 2
  if verdict e mid == "active" then firstActive e lo mid else firstActive e (mid + 1) hi

def report (name : String) (e : CoreExpr) (hi : Nat) : String :=
  let k := firstActive e 0 hi
  s!"{name}: first fl with the inner loop ACTIVE (PROGRAM-DONE) = {k}; verdict@{k-1} = {verdict e (k-1)}; verdict@{k-2} = {verdict e (k-2)}; verdict@{k} = {verdict e k}; verdict@{hi} = {verdict e hi}"

#eval report "t5Main" CorpusE0.t5Main 300
#eval report "t6Main" CorpusE0.t6Main 300
#eval report "t4Main" CorpusE0.t4Main 1500

def composite (e : CoreExpr) (sup : Nat) : String :=
  match CerbND.runND (drive fmapEmpty false (prodFileLib stdlibE3 [] e) [])
      ((initial_driver_state sup (prodFileLib stdlibE3 [] e) CerbFS.fs_initial_state).1) with
  | [(nd_status.Active dres, _, _)] =>
      s!"active; value==lint 1: {dres.dres_core_value == lint 1}; ==lint 20: {dres.dres_core_value == lint 20}; ==lint 10: {dres.dres_core_value == lint 10}; blocked={dres.dres_blocked}; stdout='{dres.dres_stdout}'; stderr='{dres.dres_stderr}'"
  | [(nd_status.Killed _ (.Error0 _ msg), _, _)] => s!"killed:Error0:{msg}"
  | [(nd_status.Killed _ _, _, _)] => "killed:other"
  | l => s!"n={l.length}"

#eval s!"t5 sup=600: {composite CorpusE0.t5Main 600}"
#eval s!"t6 sup=600: {composite CorpusE0.t6Main 600}"
#eval s!"t4 sup=600: {composite CorpusE0.t4Main 600}"
#eval s!"t5 sup=0: {composite CorpusE0.t5Main 0}"
#eval s!"t4 sup=0: {composite CorpusE0.t4Main 0}"
#eval s!"t4 sup=575: {composite CorpusE0.t4Main 575}"
```

**A.2 `census.py`** (`python3 census.py <pre-snapshot> <post-snapshot> [comma-separated names]`):

```python
import sys, re
def load(p):
    d = {}
    txt = open(p).read()
    for blk in txt.split("\n----\n"):
        blk = blk.strip("\n")
        if not blk: continue
        head, _, body = blk.partition("\n")
        m = re.match(r'^(\w+) (\S+) :$', head)
        if not m: continue
        d[m.group(2)] = (m.group(1), body)
    return d
a = load(sys.argv[1]); b = load(sys.argv[2])
added = sorted(set(b)-set(a)); removed = sorted(set(a)-set(b))
changed = sorted(n for n in set(a)&set(b) if a[n] != b[n])
print(f"PRE {len(a)} entries; POST {len(b)} entries; ADDED {len(added)} / REMOVED {len(removed)} / CHANGED {len(changed)}")
kinds = {}
for n in added: kinds[b[n][0]] = kinds.get(b[n][0],0)+1
print("ADDED by kind:", kinds); print("REMOVED:", removed); print("CHANGED:", changed)
if len(sys.argv) > 3:
    for n in sys.argv[3].split(","):
        st = "ABSENT" if n not in b else ("SAME" if (n in a and a[n]==b[n]) else ("NEW" if n not in a else "CHANGED"))
        print(f"  {n}: {st}")
```

HEAD snapshot: `CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean > head-signatures.txt` (26.3 s wall; 47100 lines / 4954 entries).
