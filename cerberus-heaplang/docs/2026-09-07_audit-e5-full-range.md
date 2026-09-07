# Range audit — the FULL E5 range `901ef50..093b02b` (24 commits): slice 1, slice 2, the other agent's completion, the L1 landing fixes, the DECISIONS commit

**VERDICT: PASS WITH FIXES REQUIRED — A- on the logic, with ONE mandatory record fix (R-1) before the merge ask.**
The Lean content of the range is sound, mirror-exact by kernel-checked engine equations, kernel-only (893/893 pins trio-exact by an independent sweep; no banned constant in any certified cone), and honestly stated: the negative-action protocol is mirrored round for round against the pinned engine (probed on the shipped composite: nine engine rounds, one draw of each supply); the `bound` soundness catch is real and the fix is exactly sufficient; the three certifications transcribe the elaborator's Core leaf for leaf and reproduce against the OCaml oracle and the compiled composite; the census and pins reproduce to the number. The problems are on the RECORD side: HEAD's `docs/DECISIONS.md` contains the other agent's fourteen entries (with the two provenance defects the landing charter required removed), contradicting the L1 record, the L1 entry and the 093b02b commit message; the mirror-completeness residual grew by an arm that no shop-window surface or manifest row names; three ARCHITECTURE counts are stale.

Auditor: fresh, independent, skeptical. Fixed detached copy `worktrees/audit-l1-093b02b` at
`093b02be7f436993496fbda3879f93b1c0d9b8d6` (2026-09-07 01:52:14 +0000); `.cerberus-ws/lean_frontend`
at the pin `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf` (`git rev-parse HEAD` in the workspace;
`scripts/semantics-pin.env` agrees); `lean-toolchain` `leanprover/lean4:v4.32.2`. Every lake/lean
invocation under `scripts/capped` with `CERB_MEM_MAX=40G` (the orchestrator's instruction of this
session; a second heavy build was running). Longest single pass: the FULL gate, a primed replay
(472 jobs, nothing recompiled) — far under the tripwire. No tracked file of the audit copy was
modified (`git status`: only the untracked scratch dir `.audit-scratch/`, deleted at the end).
Quoted outputs are verbatim; derived tallies are labelled DERIVED. Graded against
`docs/AUDIT-BRIEF.md`; KOI entries are cited only where wrong, worse, or a mover was missed.
Read first, as briefed: AUDIT-BRIEF, KNOWN-OPEN-ITEMS, CLAUDE.md, ARCHITECTURE, the DECISIONS tail,
the landing charter §0/§2, the landability assessment (its §10 fixes), the design note §B.9–B.12/§C.5,
`e5-notes.md` §1–§11 and §S2.x, the t4/t6/resume records, the four 2026-09-06 t4 records, the E5
closure record, the L1 landing record — then the FULL Lean diff (14 635 diff lines across 23 files)
plus the three new clients in full, dependency-traced against the generated `Core_reduction.lean`/
`Core_run.lean`/`Driver.lean` and the `.lem` sources at the pin.

---

## 1. Findings, ranked

Grading key: HIGH = must fix before the merge ask; MEDIUM = fix in the landing or register it with a
mover; NOTE = record/hygiene. "Premise verified by measurement" says whether the factual premise of
the finding was established by a command in this audit (yes) or by reading (read).

### R-1 (HIGH, record integrity) — HEAD's `docs/DECISIONS.md` contains the other agent's fourteen entries; the L1 record, the L1 entry and the 093b02b commit message all say it does not. Premise verified by measurement: **yes**.

- `git diff --stat 901ef50..0e161f4 -- docs/DECISIONS.md` → empty (the L1 record's "delta 0 lines" was TRUE at 0e161f4).
- `git diff --stat 0e161f4..093b02b -- docs/DECISIONS.md` → `1 file changed, 498 insertions(+)`.
- The headings the 093b02b diff adds (`git diff 901ef50..HEAD -- docs/DECISIONS.md | grep -nE '^\+## |^\+- \*\*20'`), verbatim:
  ```
  9:+- **2026-09-07 [AGENT] RE-APPENDED FROM THE PARKED BRANCH — two orchestrator entries of
  13:+- **2026-09-05 [USER] E1–E4 MERGED (main 8eeaf92); E5–E7 APPROVED** (verbatim): "yes to
  34:+- **2026-09-05 [AGENT] E5 PARKED ON `dialect-e5` (f63f22d; six commits on main 8eeaf92) —
  146:+## 2026-09-05 — Resume E5 and establish the demo acceptance target
  163:+## 2026-09-05 — E5 t5 execution checkpoint
  188:+## 2026-09-05 — Draft a charter for long-cycle demo completion
  210:+## 2026-09-05 — User adopts the demo completion charter as an active goal
  231:+## 2026-09-05 — t6 complete-term membership checkpoint
  245:+## 2026-09-05 — t6 shipped-driver checkpoint, full gate green
  268:+## 2026-09-05 — t4 whole-term membership checkpoint
  287:+## 2026-09-05 — Shared emitted load proof and t4 label-registration checkpoint
  306:+## 2026-09-06 — t4 controlling-expression proof and annotated strong binding
  331:+## 2026-09-06 — t4 additions and exact read footprints
  362:+## 2026-09-06 — t4 assignments and body through the back edge
  395:+## 2026-09-06 — t4 complete loop and shipped-driver checkpoint
  424:+## 2026-09-06 — E5 full range review prepared, dispatch pending
  440:+## 2026-09-06 — Dependency/fuel preflight while E5 review is pending
  452:+- **2026-09-07 [AGENT] L1 LANDED ON `land/e5-complete` (0e161f4; 23 commits on main 901ef50)
  ```
  i.e. the re-appended block is the whole `dialect-e5` DECISIONS delta (2 orchestrator + 14 other-agent entries), not "two orchestrator entries". Cross-check: `git diff --stat dialect-e5 HEAD -- docs/DECISIONS.md` → `117 insertions(+)` and 0 deletions — HEAD's register is a superset of the other agent's branch file.
- The header the commit wrote (DECISIONS.md:3019–3022, verbatim): `- **2026-09-07 [AGENT] RE-APPENDED FROM THE PARKED BRANCH — two orchestrator entries of 2026-09-05 that were written on `dialect-e5` and never reached main (… re-appended here VERBATIM, in their original order, dated as written):**` — false as to count.
- The L1 entry (DECISIONS.md:3452ff) says: "NOT TAKEN (they stay on `parked/demo-expansion-2026-09-07`): the other agent's DECISIONS delta (main's file restored exactly; the branch's DECISIONS diff vs main = 0 lines)" and (:3478) `Provenance greps after: "already authorized" 0, "[USER, paraphrase]" 0.` Both are FALSE at HEAD: `git grep -n 'already authorized' -- docs/DECISIONS.md` → `docs/DECISIONS.md:3205:explicit adoption. It consolidates the already authorized two-part demo`; `git grep -n 'USER, paraphrase' -- docs/DECISIONS.md` → `docs/DECISIONS.md:3228:[USER, paraphrase] Standing permission to request an early exit if a`.
- The landing record `cerberus-heaplang/docs/2026-09-07_l1-landing-notes.md` §2 says the same ("The branch's SIXTEEN entries stay on the parked branch"); the charter §0 ground rule says "the source's DECISIONS entries are NOT taken". The landability audit's R-1a/R-1b (the two provenance defects) were paid at 0e161f4 and un-paid at 093b02b. Under the operator's standing rule ("[USER]/[AGENT] provenance … failing to distinguish them is a critical trust failure") a `[USER, paraphrase]` permission grant sitting in the register is not a cosmetic slip.
- **Fix (exact).** Either (a) amend `docs/DECISIONS.md` so that the 093b02b block contains ONLY the two orchestrator entries (delete lines 3143–3451 as numbered at HEAD, i.e. the fourteen `## …` entries), which makes the header, the commit message, the L1 record §2 and the L1 entry true again; or (b) if the orchestrator DECIDES to carry the other agent's entries on main, rewrite the header ("sixteen entries"), append an erratum to the L1 entry (the "delta 0 lines" and the "0/0 greps" claims are true of 0e161f4 only), re-apply the landability audit's R-1a/R-1b (an [AGENT] erratum entry: "already authorized" was not; the `[USER, paraphrase]` line is an [AGENT] reading), and fix §2 of the landing record. Either way the register must not contradict itself. This is docs-only; no Lean changes.

### C-1 (MEDIUM, coverage classification) — the mirror-completeness residual gained an arm (`OpenRound.neg_sseq`) that no manifest row, no ARCHITECTURE sentence and no KOI entry names. Premise verified by measurement: **yes** (greps below).

- `Round.lean` (diff hunk `@@ -423,6 +435,23 @@`): `| neg_sseq (ctx ctxB ctxA ctxC : context) … : (∀ c'', ¬ Step M c c'') → negRedex? c.1 = some (ctx, a, act) → break_at_bound_and_sseq ctx = BOUND_WITH_SSEQ ctxB ctxA sseq_pat ctxC sseq_e2 → OpenRound M c` — the engine's `BOUND_WITH_SSEQ` arms (core_reduction.lem:1319–1338: the in-place re-polarisation and the `sseq`-tuple rewrite) are engine SUCCESS rounds on a `Frag` configuration (`Frag.neg_store`/`neg_store_op` admit the redex at ANY context) with no mirror step and no rule. This is precisely the class the OUT-OF-SCOPE rows exist to name ("a shape inside the fragment's constructors but outside the mirror", ARCHITECTURE §6).
- `grep -n 'neg_sseq\|BOUND_WITH_SSEQ\|strong sequence between' docs/CAPABILITY_MANIFEST.md scripts/capability_manifest.lean` → only the `Frag.neg_store` RULE row's shape text "under a `bound` with no strong sequence between (… = `BOUND_NO_SSEQ`)". No row for the WITH_SSEQ variant; the manifest's OUT-OF-SCOPE rows (6) are `run` surplus, `pure_op` uncovered, `pure_op` Impl-call, `nd`, `memop_vals` provenance fork, `call` Impl.
- ARCHITECTURE.md:313 "The residual (`OpenRound`, `:371`) has two arms." and :879 "`OpenRound`'s two arms are characterised, not closed" — three arms at HEAD. KOI B7: "two `OpenRound` arms (`eval_uncovered`, `run_surplus`)".
- The E5 records DO record it (`e5-notes.md` §1 "BOUND_WITH_SSEQ … NOT mirrored: `OpenRound.neg_sseq` (a new residual arm)", §5 item 7; `fragment-closure-e5-notes.md` table row 3 with the mover "two `Step` rules (`neg_sseq_repol`, `neg_sseq_rewrite`) and a `Frag.sseq_tuple` at the nested pattern"). The shop window and the register did not follow.
- Is it reachable from emitted Core? The design note §B.9 says the corpus's assignments sit under `Cwseq` frames only (measured on t2–t8); a `bound` whose full expression strong-sequences before an assignment (e.g. a comma/compound shape) would hit it. Not in the E5 corpus; a fail-closed gap, not a soundness one.
- **Fix.** Add an OUT-OF-SCOPE (or NO-RULE) row for `Frag.neg_store`/`neg_store_op` at `BOUND_WITH_SSEQ` (mover as in the closure record); regenerate the manifest (the gate diffs it); ARCHITECTURE §2.2/§6 "two arms" → three, naming `neg_sseq` beside `eval_uncovered`/`run_surplus`; KOI B7 updated (see R-2).

### R-2 (MEDIUM, register truth) — KOI B7 is stale in two facts. Premise verified by measurement: **yes**.

- B7: "the general size-preservation lemma `esize (subst_sym_expr x v e) = esize e` is NOT proved anywhere in the tree and not planned for E3–E4". At HEAD: `theorem esize_subst {e : CoreExpr} (x : sym) (v : value) (h : esize e ≤ lemDefaultFuel) : esize (subst_sym_expr x v e) = esize e` (Soundness.lean, E5 slice 1; pinned trio-exact) plus `esize_subst_fold`, `case_hbsz_of_branches` ("KOI B7's mechanism is closed, the premise form is kept" — `fragment-closure-e5-notes.md`). The lemma IS proved (under the engine's fuel bound, which is the only form that exists — `subst_sym_expr_lemFuel 0 e` is LemLib's opaque `fuelExhausted`).
- B7: "two `OpenRound` arms" → three (C-1).
- The upstream note `docs/2026-09-05_note-cerberus-lean-subst-esize.md` (which B7 cites as "only flags the duplication") should be re-read against the proved lemma.
- **Fix.** Rewrite B7: the arms are three; `esize_subst`/`negFree_subst`/`ccallFree_subst`/`pot_subst` exist at the engine's fuel; `hbsz` is now DERIVABLE by `case_hbsz_of_branches` and is kept as a premise by choice.

### D-1 (MEDIUM, shop-window truth) — ARCHITECTURE sentences false at HEAD for E5. Premise verified by measurement: **yes** (greps quoted).

1. :87 "`Frag e` (`Soundness.lean:9368`) has 29 constructors (`:8070`–`:8286`; dialect arc E4)" — E5 added six (`neg_store`, `neg_store_op`, `excluded_store`, `excluded_store_op`, `case_op`, `nd`); the manifest's own tail says `35 constructors`. The kinds list in the same paragraph omits them (they appear only in the E5 prose below).
2. :313 and :879 "two arms" (C-1).
3. :576–579 "The t4 production checkpoint has 896 exact pins: E4's 652, E5 slice 1's 60, the second slice/t5's 67, t6's 39 and t4's 78" — HEAD has **893** (L1 unpinned two alias theorems and the generated `.eq_def`; gate line `export pins: 893 trio-exact`).
4. Glossary "*a tie*" (:61–68): "The ties: the thread, the memory, the extern table, the file, the registration predicate `LabeledProcs` and, in the partial fact only, the control's `CtlTied`; … the run-state supplies are tied to the control inside `MachineCtx.Embeds`" — since E5 slice 1 the SUPPLY TIE is a premise of the exported facts themselves: `DriverSafeCtl` (Adequacy.lean:953–954 `dst.core_run_state0.sym_supply = ctl.sup.sym ∧ dst.core_run_state0.excluded_supply = ctl.sup.excl →`), `DriverDoneCtl` (ProdLoop.lean:493), `DriverDoneAt` (ProdLoop.lean:69, with the new parameter `sp`). §4's "How to read an export" for `counter_loop_certified` ("Let `dst`'s single thread hold the program …, with empty extern, the context's file and the registration ties. Then …") omits the new premise: the seeded exports now speak ONLY about driver states whose supplies equal the entry control's (`⟨0,0⟩` at `procCtl`). That narrowing is real (a forced text change recorded in `e5-notes.md` §2/§8 "DriverSafeCtl and DriverDoneCtl changed in BODY") but ARCHITECTURE's reading does not say so. WALKTHROUGH §1.1 prints `DriverSafeCtl` "in full" (line 60ff) — the print is stale by two arcs (a three-field `Ctl` `⟨[], pfin, ℓfin⟩`, `ofVal (.pure v)`, no `lcfin`/`spfin`, no supply tie); it predates the range (E1 drift) but the range widened the gap, and "printed here in full" is false at HEAD.
5. :126–150 E5 prose: "E5's next checkpoint proves … and uses their total faces to certify t5_ifelse" — future tense for landed work; :147 "its full range audit (8eeaf92..the L1 head) is owed" — the range is `901ef50..HEAD` (the L1 entry's own wording); KOI C19 repeats "8eeaf92..the L1 head".
- **Fix.** Five sentence edits + WALKTHROUGH's printed definition refreshed from the source (or the "in full" claim dropped); `cite_check.sh` last.

### D-2 (NOTE) — the `600 ≤ sup` premise is load-bearing; the records' "sufficient, not necessary" should not be read as "any `sup` works". Premise verified by measurement: **yes**.

Probe (compiled composite, `sup` at a source symbol's number): `t5 sup=505 (= x's symbol number): killed:other`, `t5 sup=506 (= r's symbol number): killed:other`, `t4 sup=505: killed:other`, each preceded by LemLib panics `PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Kill` / `… ==> Load` and `Driver.process_core_step2: WRONG STEP ==> Step_error2[Kill]` (verbatim, probe log §4.5). The fresh symbol `fresh_given_int 505` collides with `x` (the runtime `digest ()` is `""`), the kill/load of `x`/`r` then reads a non-pointer, the engine reports ILLTYPED, and the driver's `can_advance` panics. So: at `sup = 0` and `sup = 600` the composites deliver (reproduced), at `sup ∈ {505, 506}` they are KILLED. The theorems are correct (their premise excludes those supplies) and the records are literally right ("not necessary"), but README:228–233 / KOI B6 / the three docstrings would mislead a reader into thinking the floor is vacuous. **Fix (one sentence each):** "sufficient, not necessary (the composite delivers at `sup = 0`), and not vacuous (at `sup` equal to a source symbol's number the composite is killed — measured)". Also worth noting for KOI A5: this is a `failwithI` panic on the driver's `can_advance` path, reached by an ordinary ILLTYPED report.

### D-3 (NOTE) — `cite_check` manual queue: 6 of 10 sampled non-EXACT cites are stale by 4–1 300 lines. Premise verified by measurement: **yes** (hand-check below). Known class (KOI C18: "manual queue disclosed, not cleared"); E5's +1 400 lines in Step/Soundness/Round moved the loose cites further. Not a new finding class; recorded so the next docs pass knows the queue is mostly stale, not mostly fine. Suggest `cite_check --fix` extended to positional groups, or declaration-name cites for the RANGE/HAND classes.

### H-1 (NOTE, hygiene) — the C17 duplication class grew in E5 (disclosed as a class; the additions listed here so the hygiene slice sees them): `step_ctx_excluded_store_eval_ws'`/`_shape`/`_fail2`/`_fail3` are line-for-line clones of the store versions; `Decomp.get_ctx_rebuild_excluded` clones `get_ctx_rebuild_action`; `Decomp.lift_neg'` has ten identical arms; `wps_bound_wseq_tuple_aux`/`wpt_bound_wseq_tuple` re-derive `wps_bound_aux`/`wps_wseq_tuple_annot`'s 11-arm inversion; the clients triplicate `t{4,5,6}Load` (each `= emittedIntLoad …`), `wpt_t{4,5,6}Load` (each one line), `t{4,5,6}Kill_eq`, the `t{4,5,6}_frame`/`_lookup` local macros; `t6frAssign` = `t5frAssign`. Two docstring defects: Potential.lean:14/:176 say the negative-action leaf costs **9** while `pot_neg : … = 10` (:182) and the proofs use `h9 : … = 10`; `negFreeAlts`'s docstring (Step.lean:644) is `ccallFreeAlts`'s ("`has_ccall`'s `Ecase` arm").

### H-2 (NOTE) — the numeral `600` in three root-of-trust statements. Under [USER 2026-09-03] "no magic values … bounds not forced by OCaml or ISO are quantified parameters, never numerals", `hsup : 600 ≤ sup` is a numeral standing for "above every source symbol number of this program" (max 529/531/574). The landability audit listed this as optional (R-7); I re-cite it as the ruling's class: the principled statement is a program-derived bound (`symBound tMain ≤ sup`, `symBound` computed from the transcription by `rfl`). Not blocking; a statement change, so a slice of its own.

### H-3 (NOTE) — the client-facing freshness fact in `wps/wpt_neg_bound` (`∀ s, ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗ …`) exposes the engine's symbol-generation scheme; clients discharge collisions by `symOrd_ne_eq_of_num_ne` on symbol NUMBERS. An abstract `FreshAbove s floor` with one lemma would keep the rule Reynolds/O'Hearn-clean. Sound as is; API taste.

No T- finding. No unsound rule, vacuous statement, misreported theorem, or claimed-but-unproved construct was found in the range.

---

## 2. What was verified, by the brief's items

### 2.1 The negative-action protocol (Step.neg_bound, negRewrite, Ctl.draw, the excluded-store steps, complete_neg_act, the new arms)

Read round by round against `frontend/model/core_reduction.lem:1290–1338` (the Neg arm), `:868–912` (`break_at_bound_and_sseq`), `:819–850` (`break_at_sseq`: `Cbound → error "break_at_sseq, Cbound"`), `:939–958` (`add_exclusion`), `:694–727` (`step_action` Store0), `:1345–1346` (`Eexcluded`), and the generated `Core_reduction.lean:75–82` (`fresh_excluded_id`, `fresh_symbol0`), `Core_run.lean:123–126` (`fresh_symbol'`: `(fresh_given_int n, {rs with sym_supply := n + 1})`), `Symbol.lean:334` (`fresh_given_int n = Symbol (digest ()) n SD_None`), `Core_run_aux.lean:400–409` (`initial_core_run_state sup` seeds `sym_supply := (supplySplit sup).1 = sup`, `excluded_supply := 0`), LemLib.lean:66 (`supplySplit s = (s, s+1)`).

- `negRewrite n s ctxA act = mk_wseq_e (mk_tuple_pat [mk_empty_pat BTy_unit, mk_sym_pat s BTy_unit]) (mk_unseq_e [Expr [] (Eexcluded n act), apply_ctx (add_exclusion n ctxA) (mk_pure_e mk_unit_pe)]) (mk_pure_e (mk_sym_pe s))` is the `.lem`'s `expr'` constructor for constructor (the `.lem` draws `n` first, then `sym`; both supplies advance by one — `Ctl.draw`).
- The engine breaks the context at the OUTERMOST `bound` (first `Cbound` from the root; `break_at_bound_and_sseq` stops there and calls `break_at_sseq` on the inner context, which PANICS at any nested `Cbound`). The mirror states the round at that `bound` (`Step.neg_bound` with `negRedex?`, the spine twin of `callRedex?`), lifts through the frames above it (`Decomp.lift_neg'`: the `Csseq/Cwseq/Cannot/Cunseq` congruences, whose jump/call guards are discharged by the exclusivity lemmas), and GUARDS `Step.bound_ctx` by `negRedex? b = none` so an inner bound can never frame a rewrite the engine performs at the outer one. Nested bounds: `hss : break_at_sseq ctxA = none` is unprovable (the generated `break_at_sseq` at `Cbound` is the opaque `failwithI`) — mirror stuck, engine panics: fail-closed both sides. `BOUND_WITH_SSEQ`: `OpenRound.neg_sseq` (C-1). `NO_BOUND`: `ShippedRefusal.panic_step` via `step_ctx_neg_nobound` (the step IS `failwithI "TODO: NO_BOUND (Neg)"`).
- The kernel-checked engine equation `step_ctx_neg` (Soundness.lean): `∀ rs, m rs = Result (Defined { locUpdTh a th with arena := apply_ctx ctxB (negRewrite rs.excluded_supply (fresh_given_int rs.sym_supply) ctxA act) }, { rs with excluded_supply := rs.excluded_supply + 1, sym_supply := rs.sym_supply + 1 })` — the location write at the ACTION node's annotations, both supplies advanced. `advance_withrs_tau_rs` (Round) and `loop_step_withrs_tau_rs` (DriverCollapse) are the driver's with-runstate arm WITH the run state written; `engine_step_matchU`'s new disjunct returns `rs' = {dst.core_run_state0 with excluded_supply := +1, sym_supply := +1}` and discharges `CerberusRound`'s tie to the successor control by `hsym`/`hexc`.
- `Step.excluded_store` = `Step.store` under `Eexcluded n` with the continuation `Expr [] (Eannot [DA_neg n [] fp] (pure Unit))` — exactly `step_action`'s `is_excluded = Just n` branch (`.lem:704–709`); `excluded_store_eval` = the `(_, _, _)` ACTION_EVAL arm rebuilding `Expr e_annots (Eexcluded n act')`. Classification `complete_excluded_store`/`_op` mirror the positive store's arms (ILLTYPED text identical to `.lem:712–716`). `complete_case_op`, `complete_nd` (`nd_fork`: `pick` on ≥ 2 alternatives is `NDnd`, `runND` explores each — `2 ≤ (runND …).length`) read as stated.
- `frag_round_complete` dispatches the four new roots; `Frag.step`, `Frag.pot_step_bound`, `Step.ccallFree_preserved` gained `hsz` because the `case_value` successor is a substitution at the engine's fuel (`esize_subst`, `ccallFree_subst`, `negFree_subst`, `pot_subst`, all by fuel induction on the genuine `subst_sym_expr_lemFuel`).

**Probe (§4.4).** Executing `CorpusE0.t5Main` through the shipped inner loop from `prodEntryStateLib stdlibE3 [] 600 …` and printing, after each round `k`, the run state's supplies, the head step of the next round and a depth-9 skeleton of the arena: the assignment `r = 1` occupies rounds 41–49 —
41 `withrs-tau[Neg Action, no break ==> …t5_ifelse.c:1:48-53]` with `sym=600 excl=0` before and `sym=601 excl=1` after, the arena going from `bound({A}wseq(neg:store; pure))` to `bound(wseq(unseq[excl[0](store), {A}wseq(…; …)]; pure))` (= `negRewrite 0 (fresh_given_int 600) …`); 42 `tau[Ewseq]` (the wildcard binder over `pure(Unit)`); 43 `withrs-eval[Epure]` (`pure(per)`); 44 `withrs-eval[eval operands of Store]`; 45 `action[StoreRequest]` (the excluded store; arena then `unseq[{A}pure, {A}pure]`); 46 `tau[Eunseq]` (completion); 47 `tau[Ewseq Eannot]` (the `(_, s)` binder); 48 `withrs-eval[Epure]` (`pure(s)`); 49 `tau[CTX, Ebound Eannot(value)]` (REMOVE-BOUND); at 50 the arena is `sseq(sseq(sseq(pure; pure); pure); …)`. NINE engine rounds, exactly the mirror's derivation in `wps_neg_bound`'s docstring ("nine rounds, each a mirrored rule"): neg round · bound congruence over (wseq_pure · pure_eval) · excluded_store_eval · excluded_store · unseq_vals · wseq_tuple_annot · (annot ∘ pure) · bound_annot. Exactly one draw of each supply in the whole run (`sym` 600→601, `excl` 0→1 at round 41 and never again — t5 executes one assignment). No supply moves at any other round (PCALL/RETURN do not occur in t5; the theorems `Step.sup_sym_le`/`Step.ctl_cases` cover call/ret by `rfl`).

### 2.2 The supplies as writers, the WP-level floor, the R3 normalisation

- `Ctl.draw` is the only writer (`Step.ctl_cases`: `upd | (upd).draw | callPush | ret`; `Step.sup_sym_le : ctl.sup.sym ≤ ctl'.sup.sym` by four cases). The tie `dst.core_run_state0.sym_supply = ctl.sup.sym ∧ …excluded_supply = ctl.sup.excl` is a premise of `loop_step_frag_same'/_same/'/frag` and returned at `ctl'` (`rs'.sym_supply = ctl'.sup.sym ∧ …`), threaded through `drive_safe_aux` (all three step branches incl. the new draw branch and the call/return), `driverDone_step`, `driverDoneCtl_step`, `wpt_driver_aux`/`_cps`. `DriverSafeCtl`/`DriverDoneCtl` gained the tie premise (BODY change; texts of the ~20 seeded exports unchanged — the narrowing D-1.4 describes); `DriverDoneAt` gained `(sp : RunSup)` and the tie. `prodCtl sup := ⟨[], some mainSym, …, ⟨sup, 0⟩⟩` = the initial run state's supplies, so every production statement discharges the tie by `⟨rfl, rfl⟩` (`prod_run_eqJ`, `_procs`, `_lib`, `_lib1`, `prod_run_safe_procs`, `_lib` — read in the ProdEntry diff; the 26 supplies-forced statement changes of slice 1 reproduced in the census, §4.2).
- The floor `⌜M.runState.sym_supply ≤ sp.sym⌝ -∗` in `wps.pre` (Wps.lean:261) and `wpt.pre`/`wpt_step_eq` (Wpt.lean:186/:270) — a JUDGMENT TEXT CHANGE — is preserved across the step clause by `Nat.le_trans hsb hs.sup_sym_le` in both collapses (`wps_sound_cps`, `wpt_sound_cps`: the continuation `K` receives `⌜floor ≤ sp'.sym⌝`), and surfaces as `hsb` on the six `*_sound*` faces and `wpt_driver_done(_alloc)`/`_done_procs`/`_aux`/`_cps` (`eo/fr_wp_readout` gain `hsb`). Every `Step.ctl_upd`-shaped consumer was rewritten to destructure the successor control (`obtain ⟨κ', p', ℓ', lc', sp'⟩ := rctl` + `Step.ctl_eq`) — the eight binder rules, `wps_unseq_focus`, both collapses: statements unchanged, proofs no longer assume the `upd` shape.
- **Is the floor the right invariant?** Yes: the drawn symbol is `fresh_given_int k` with `k = sp.sym ≥ floor`, `sp.sym` never decreases, and at entry `floor = M.runState.sym_supply = (prodRSLib … sup …).sym_supply = sup = (prodCtl sup).sup.sym` (by `rfl`). A client whose program symbols all have numbers `< floor` derives `symOrd x s ≠ .eq` by `symOrd_ne_eq_of_num_ne` — whatever the opaque `digest ()` is (the lemma compares numbers, so it does not depend on the digest). The probe of §2.1 shows the invariant holding (600 → 601) and D-2 shows the collision the floor excludes is real.
- **R3 normalisation inert?** Yes for exports: `M.runState` is read at `labeled` only (`labelsAt`, `Embeds.labeled`, `LabeledProcs`, `CtlTied`) and at `sym_supply` for the floor (grep of every `runState` use in Round/DriverCollapse/Adequacy/ProdLoop/ProdEntry/Wps/Wpt/Step); `procCtx rs`/`procCtxF f rs` now carry `{rs with sym_supply := 0, excluded_supply := 0}` (Step.lean:6315/:6363 — KOI B18's cites verified), so at a seeded profile the floor is `0 ≤ _` (trivial) and the freshness fact is never USED (no seeded exhibit assigns). The DriverSafeCtl/DriverDoneCtl premise reads the CONTROL's supply (`⟨0,0⟩` at `procCtl`), not `M.runState`; the production contexts retain `sup`. Census: `procCtx`, `prodCtx`, `DriverSafeCtl`, `DriverDoneCtl` and every headline statement `SAME` (§4.2). What DID change in meaning is the seeded facts' driver-state premise (D-1.4), a slice-1 change recorded in `e5-notes.md` §2, not R3.

### 2.3 The `bound` soundness catch

- The would-be counterexample (`e5-notes.md` §3), reconstructed: with `Step.neg_bound` present and `Step.bound_ctx` UNGUARDED, `bound(b')` for `b' = sseq(bound(wseq(neg act, e2')), e2)` would step by `bound_ctx ∘ sseq_ctx ∘ neg_bound` (the INNER bound performs the round) — a mirror step the engine does not make: the engine breaks at the OUTERMOST bound and `break_at_sseq (Csseq … (Cbound …) …)` panics. So `wps b'` provable ⇒ `wps (bound b')` provable while the engine panics: the one-shot `wps_bound : wps … b ⊢ wps … (bound b)` would be unsound at the E5 fragment; at E4 the fragment had no negative action, so nothing merged was ever unsound. The premise verified by reading the `.lem` and the generated `break_at_sseq` (its `Cbound` arm is `failwithI`).
- The fix is exactly sufficient: `bound_ctx` guarded by `negRedex? b = none`; `wps_bound`/`wpt_bound` require `negFree b = true ∧ pot b ≤ lemDefaultFuel`, carried inside the Löb/strong-induction entailment (`wps_bound_aux`; the `wpt_bound` induction generalises `hnf hpot`) and re-established at every successor by `Step.negFree_preserved` (all 40 `Step` arms; `neg_bound` refuted by `negRedex?_none_of_negFree`; `case_value` via `negFree_subst_fold` at the engine's fuel) and `Step.pot_le` (`pot` non-increasing along every stack-preserving non-jump round of a negative-free term; additive `pot`, `pot_negRewrite_le` shows the leaf weight 10 pays the rewrite exactly), with `esize ≤ pot` (`esize_le_pot`, fragment-free) feeding the fuel premise the substitution lemmas need. The call plug case uses `callRedex?_apply_ctx_eq` + `negFree_apply_ctx_of` + `pot_apply_ctx_plug`; the jump case transfers to the label spec as before. `negFree` admits `Eexcluded` (slice 2) — necessary, since `negRewrite`'s body contains one and `wps_bound` must apply to it. `negFree` descends exactly where a body's own rounds can reach (`Esave` body, `Eif` arms, `Ecase` alternatives, `Elet` body, `End` alternatives) — the condition under which the congruence IS the engine's behaviour (any reachable negative action under the outer bound either makes the outer bound's own round or panics the engine).
- Call sites: every `wps_bound`/`wpt_bound` use in the range discharges the premises by `rfl` and `Nat.le_of_ble_eq_true rfl` (grep over the exhibits' diff: 30 sites rewritten; the E5 clients use `wpt_bound _ _ _ rfl (Nat.le_of_ble_eq_true rfl)` throughout; `wpt_t4Assign` threads `hnf`/`hpot` through to `wpt_bound_wseq_tuple`).

### 2.4 `wps/wpt_neg_bound`

- Statement read: premises are the points-to `pointsToCell … pv (.own 1) ty bs`, the operand evaluations (`hv2`, `hv3`, `hvr` at `ev0 :: evs`), encodability/storability (`hmv`, `hst`), `hnv`/`hnvr` (operands not all values — the emitted shape), `hf : SymFrame ev0`, `hex` (identity extern). The client sees the cell before and after, the delivered value `vr` BARE, and the frame extended by `s ↦ vr` with `∃ k, s = fresh_given_int k ∧ floor ≤ k`. The exclusion id and the footprint never reach the client. Reynolds/O'Hearn-clean up to H-3.
- Derivation traced against the engine's nine rounds (§2.1 probe) — one-to-one. `wpt_neg_bound` at `16 ≤ k`: 1 (neg) + 1 (REMOVE-BOUND) + 11 (unseq: 4 + 4 + 3) + 3 (tail) = 16; measured 9 engine rounds → 7 units of slack inside the rule (the docstrings say "sufficient", nothing claims tightness). Both faces pinned trio-exact (§4.3).
- The `do_race` verdict of the completion is the exclusion protocol's own: `do_race_addExcl_neg : do_race (ds.map (addExcl n)) [DA_neg n [] fp] = false` (the id `n` is in every exclusion list of the other component's annotations — `add_exclusion`'s `Cannot` arm — so the footprints are never compared), plus `do_race_nil_right`. Read against `Core_reduction.lean:300`.

### 2.5 The three certifications

- Vocabulary (read off the statements at CorpusT5Exhibit.lean:548, CorpusT6Exhibit.lean:618, CorpusT4Exhibit.lean:1429): `(sup : Nat) (hsup : 600 ≤ sup) (fs : CerbFS.FsState) (args : List String)`; conclusion `CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 [] <tMain>) args) ((initial_driver_state sup (prodFileLib stdlibE3 [] <tMain>) fs).1) = [(nd_status.Active dres, ([] : List String), dst')] ∧ dres.dres_core_value = lint {1,20,10} ∧ dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = ""`. Package names in the statement: `prodFileLib`, `stdlibE3`, `CorpusE0.t{5,6,4}Main`, `lint`. No mirror/driver/discharge name — the referent rule holds. Route: `t*_wpt` + `t*_blockSpecsT` → `wpt_driver_done_alloc` (at `prodCtx …`/`prodCtl sup`, `hsb` by `Nat.le_refl`) → `prod_run_eqJ_lib1` (tie `⟨rfl, rfl⟩`), t1's route.
- Transcriptions vs `docs/corpus-e0/t{5_ifelse,6_switch,4_while}.annot.core`: the skeleton speedbump covers the whole `main` of each (gate: `corpus-skeleton: ok — 4 corpus row(s) and 3 std.core row(s) equal, every plant mismatches`); I compared the LEAVES by hand — every literal (t5: 3, 2, 0, 1, 0; t6: 2, 0, 1, 2, 10, 20, 30; t4: 0, 0, 5, 0, 7, 0, 1), every printed symbol number (t5 508–529 with x=505/r=506/ret_507; t6 514–531 with x=509/r=510, ret_511, break_513, case_521/case_520/default_522; t4 513–574 with i=508/s=509, ret_510, continue_511, break_512, while_515), every printed source region and cursor (all `t*Reg`/`t*RegP`/`t*RegR` arguments against the `<l:c, l:c> l:c` markers — e.g. t5's (46,56)/(48,54)/(48,53,50)/(48,49)/(52,53) and (62,72)/(64,70)/(64,69,66)/(64,65)/(68,69); t6's (60,67)/(60,66,62)/(60,61)/(64,66), (83,90)/(83,89,85)/(83,84)/(87,89), (107,114)/(107,113,109)/(107,108)/(111,113); t4's (46,60,52), (46,51,48), (55,60,57), (64,74)/(64,73,66)/(64,65)/(68,73,70)/(68,69)/(72,73), (75,85)/(75,84,77)/(75,76)/(79,84,81)/(79,80)/(83,84), (88,97)/(95,96), (0,99) with cursor (4,8)), operand orders, `Astd` strings (with/without `§` as printed), pattern shapes (`Cspecified` binders at `BTy_object OTy_integer`, `Cunspecified [CaseBase (none, BTy_ctype)]`, the `_: (loaded integer, loaded integer)` wildcard as `CaseBase (none, BTy_tuple [lint, lint])`), binder types, `conv_int` as the std.core `PEcall (Sym convIntSym)` vs `__conv_int__` as `PEconv_int`, `catch_exceptional_condition_add` as `PEcatch_exceptional_condition (.Signed .Int_) IOpAdd`, the `UB036`/`UB_CERB004_unspecified UB_unspec_conditional` undefs, the `nd(pure(True), pure(False))` arm, `<unknown location>` as `Aloc .unknown`. ALL MATCH. Residual blind spots as the records state: unprinted action/undef locations (transcribed as the enclosing region), the `;`-association (not observable in the text; the label continuations are computed by the ENGINE's `collect_saves` by `rfl` — `t6Q_eq`, `t4Q_eq` — so what the certification uses is the engine's reading of the transcribed term, not a guess), the unprinted numbers of `x`/`r`/`i`/`s`.
- `Frag` membership: `t{5,6,4}Main_frag` compositional (Examples/CorpusE5.lean); the `case_op` branches for EVERY scrutinee value via `t6Switch_select`/`t4And_select` (`cases v <;> …`) and `Frag.substFold_pure` (Substitution.lean: substitution preserves `PePure` and depth by fuel induction on the genuine `subst_sym_pexpr_lemFuel`); `hbsz` by `case_hbsz_of_branches`; leaves by `decide`/`rfl`. Gate 1 clean; `#print axioms` of the three `*Main_frag` = the trio (§4.3).
- Oracle re-run (§4.1): `Specified(1)`/exit 1, `Specified(20)`/exit 20, `Specified(10)`/exit 10; the binary is the mainline build (2026-09-05 19:47, primary at `89f7e6885`), NOT the pin — the standing caveat.
- Compiled composite (§4.4): PROGRAM-DONE at inner-loop fuel 69/67/593 (killed at 68/66/592) vs `k + 2 = 90/80/917` — slack 21/13/324 as KOI B6 records (DERIVED: 90−69, 80−67, 917−593). Composites deliver `lint 1`/`lint 20`/`lint 10`, unblocked, empty streams at `sup = 600` AND at `sup = 0` (reproducing the L1 record) — and are KILLED at `sup = 505/506` (D-2).
- t4's invariant (`t4LsT`: `while_515 ↦ t4Budget n = 159·(5−n)+98` owning `i = n`, `s = t4Sum n`, `n ≤ 5`; `ret_510 ↦ 2` at `[lint 10]`): `wpt_t4LoopStep` spends 77 (guard+Bool) + 82 (body) and re-enters at `t4Budget (n+1)`; the exit path at `n = 5` spends 77 + 1 + 4 + 16 = 98; `t4Guard` shows the C conjunction equals `n < 5` on the invariant (the `s < 7` side never short-circuits for n ≤ 4 since `t4Sum 4 = 6`; at `n = 5` the LEFT comparison is false and `wpt_t4And`'s `i < 5` false branch follows the emitted zero branch without reading `s` — the short-circuit, as the record says). Continue/break are registered but never jumped to; their saves execute on the normal path (`wpt_t4Save` costs 2 each) — all four continuations retain `Frag`/`pot` proofs (`t4Q_frag`/`t4Q_pot`).

### 2.6 Everything that changed text (census)

Reproduced with the landability auditor's `census.py` (its Appendix A.2, run verbatim) — §4.2. HEAD snapshot regenerated (`signature_snapshot.lean`, 47 085 lines) is `cmp`-identical to the committed `docs/2026-09-07_l1-signatures-post.txt`. Slice-1 post → HEAD: **368 / 2 / 18**, `load_atomic` the only pre-existing text change beyond the park's slice-2a list (the six `*_sound*`, both `_cps`, the five `wpt_driver_*`, `wpt_step_eq`, `negFree.eq_def`, `eo/fr_wp_readout`); E4 post → slice-1 post: **224 / 2 / 82** (16 defs, 184 theorems, 24 ctors; REMOVED `Frag.pot_le_two`, `pot_action`; the 82 CHANGED = 26 supplies-forced + 2 bound rules + 54 other, name-checked against `e5-notes.md` §8); e5b → HEAD: 236 / 4 / 4 (the four deleted `t5Int*` aliases; `load_atomic` + three internal t5 lemmas respelled by the alias deletion). Headline statements all `SAME`. WHOLE RANGE (E4 post → HEAD, not stated by any record; DERIVED from the two committed snapshots): **ADDED 592 / REMOVED 4 / CHANGED 96** — the pre-existing statement-text changes of the L1 landing as a whole are 96 (82 + 14 net new), all in the slice-1/slice-2a lists plus `load_atomic`. Pins 652 → 893: all 893 trio-exact by my independent sweep, 893 distinct names, none missing (§4.3); the recorded sub-trio names reproduce (`t4Index_cases`/`t4Sum_le`/`t4Guard`/`t4Budget_succ` `[propext, Quot.sound]`; `t4Sum_succ`/`t4Kill_eq`/`t6Kill_eq`/`t5Kill_eq`/`t5Store_eq` axiom-free; `t{4,5,6}Main_pot`, `peDepthList_map_eq`, `peDepthAlts_map_eq`, `negFree.eq_def` `[propext]`); `subst_sym_pexpr_lemFuel.eq_def` is trio-exact but correctly OUT of `trioExports` (Audit.lean:931 comment).

### 2.7 The L1 landing itself — see the table in §3. Process docs gone (`docs/2026-09-05_demo-completion-charter.md`, `…e5-range-review-brief.md`, `…dependency-fuel-preflight.md` absent at HEAD); `e5-resume.md` kept with an honest `[L1 landing note, 2026-09-07, AGENT]` paragraph replacing the unverifiable quotation and quoting R6 verbatim from the register; the six t4/t6 records carry one labelled landing line each; hygiene proof-safe (relocations only; `EmittedInt` imports `CorpusE0`/`IntRules`/`Wpt`/`ProdEntry` only; `CorpusT4/T6Exhibit` import no `CorpusT5Exhibit`; the alias deletions show up as the census's REMOVED 4 and 8 internal respellings; the unpinned `.eq_def` is the dependency's generated equation lemma). The regression is R-1.

### 2.8 Shop window — README (root and package), CLAIMS C15–C17, the manifest header (`35 constructors, 77 variant rows (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 6 OUT-OF-SCOPE), 0 red, 25 consumer modules`; `CLAIMS: 17 claim rows, 184 declaration names … 341 declaration-shaped spans`), `module_classes.tsv` (29 boundary-checked modules, 18 core) describe E5 honestly ("transcribed", "checked skeleton", "same `prodFileLib stdlibE3` boundary", "KOI A7 open", "sufficient floor", "E5's full range review remains open", the seven partial faces "proved but not consumed"). ARCHITECTURE's stale sentences are D-1. `cite_check.sh`: `cite-check: ARCHITECTURE.md — 280 cites; EXACT 179; DECL 52 (fixed 0; ranges among them counted in RANGE); USE 19; HAND 21; PIN 9; NOFILE 0; RANGE 25 (never rewritten)` (verbatim; = the L1 record). Ten non-EXACT lines hand-checked (D-3).

### 2.9 Records — the gate (§4.0) matches the DECISIONS L1 entry's tail line for line (893 pins; 6051 swept; 9141 constants; 472 jobs; 18 core modules; 29 modules / 0 mentions; ALL GATES GREEN). DECISIONS chronology: re-appending 2026-09-05 entries after the 2026-09-07 entries under an explicit dated header is acceptable for an append-only register — PROVIDED the header is true (it is not: R-1). Counts/hashes vs the tree: pins 893 ✓, `0e161f4` = 23rd commit on `901ef50` ✓, KOI B18's cites ✓, §2.5's cites ✓, B6's slack ✓ (re-measured).

### 2.10 Grumpy read — H-1/H-2/H-3. Layering: T4/T5/T6 import `EmittedA/B/CExhibit` for shared lemmas (disclosed in C19; the import-direction speedbump polices `core` only). Dead code: none new found (`Frag.pot_le_two` removed; `pot_action` renamed; `DriverDoneAt`'s retirement is a known hygiene item). Linter warnings: 48 in `CerberusHeapLang/*` (Potential 31, Round 7, Rules 2, Heap 2, EnvLaws 2, TreeRot/Struct/Soundness/ProdLoopExhibit 1) = the baseline; the range introduced none.

---

## 3. The L1-fix verification table (the landability audit's §10, applied by L1?)

| landability fix | status at 0e161f4 | status at HEAD 093b02b | evidence |
|---|---|---|---|
| R-1a "already authorized" over-claim removed from the register | DONE (DECISIONS restored to main's) | **UNDONE** — `docs/DECISIONS.md:3205` | R-1 |
| R-1b `[USER, paraphrase]` permission removed/re-tagged | DONE | **UNDONE** — `docs/DECISIONS.md:3228` | R-1 |
| R-1c operator's resume confirmation verbatim | DONE | DONE | L0 rulings entry ("R6 - yes, I approved this, you can mark it as such"), quoted in `e5-resume.md`'s landing note |
| R-2 candidate-head census snapshot + tallies | DONE | DONE | `2026-09-07_l1-signatures-post.txt` `cmp`-identical to my regeneration; 368/2/18 reproduced |
| R-3a KOI state line | DONE | DONE | KOI lines 3–11 |
| R-3b "sufficient, not necessary" on README/ARCHITECTURE | DONE | DONE (see D-2 for the missing half-sentence) | README:228–233/:358; ARCHITECTURE:135–138; CLAIMS C15–C17; the three docstrings |
| R-3c B6 slack rows 21/13/324 | DONE | DONE | KOI B6; re-measured 69/67/593 |
| R-3d §2.5 line cites | DONE | DONE | CorpusT5Exhibit.lean:548, T6:618, T4:1429, T1:803 all `theorem t*_certified_production` |
| R-4a R3 ruled and recorded | DONE | DONE | KOI B18 (cites Step.lean:6315/:6363, ProdEntry.lean:585 — verified); ARCHITECTURE:174–178 |
| R-4b M2's re-pin target ruled | DONE (L0: R1 → 89f7e68) | DONE | L0 rulings entry |
| R-5 partial faces disposition | deferred, disclosed | deferred, disclosed | KOI C19 |
| R-6 `EmittedInt` imports no client; T4/T6 import no T5; aliases deleted; `.eq_def` unpinned; banners stripped | DONE | DONE | imports read; census REMOVED 4; Audit.lean:931; axiom dumps' first lines are content |
| R-7 program-derived supply bound (optional) | not done, disclosed | not done | H-2 |

---

## 4. Probe / plant log (verbatim; commands stated)

### 4.0 The FULL gate — `CERB_MEM_MAX=40G scripts/test_unit.sh` from the audit copy's root, exit 0. Every line matching `^==|^ok:|^info: CerberusHeapLang|^ALL GATES|^GATE|^Build completed|^BOUNDARY|^FAIL|^corpus-skeleton`, unmodified (`GATE-EXIT=0` appended by my wrapper):

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
corpus-skeleton: ok — 4 corpus row(s) and 3 std.core row(s) equal, every plant mismatches
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
Warnings in the gate log: 572 raw `warning:` lines, 48 from `CerberusHeapLang/*` (Potential 31, Round 7, Rules 2, Heap 2, EnvLaws 2, TreeRotExhibit 1, StructExhibit 1, Soundness 1, ProdLoopExhibit 1) — DERIVED by `grep -c`/`uniq -c`.

### 4.1 The OCaml oracle — `cd /home/dev/projects/cerberus-lean-proj && scripts/ce cerberus-lean/_build/default/backend/driver/main.exe --nolibc <mode> refined-cerberus/worktrees/audit-l1-093b02b/docs/corpus-e0/<t>.c` (the `scripts/ce` env banner and `Time spent` lines elided; exit codes from `$?` of the un-piped command):

```
=== t5_ifelse --exec --batch
Defined {value: "Specified(1)", stdout: "", stderr: "", blocked: "false"}
t5_ifelse --exec exit=1
t5_ifelse --exec --batch exit=0
=== t6_switch --exec --batch
Defined {value: "Specified(20)", stdout: "", stderr: "", blocked: "false"}
t6_switch --exec exit=20
t6_switch --exec --batch exit=0
=== t4_while --exec --batch
Defined {value: "Specified(10)", stdout: "", stderr: "", blocked: "false"}
t4_while --exec exit=10
t4_while --exec --batch exit=0
```
Binary: `-r-xr-xr-x … 49026928 Sep  5 19:47 cerberus-lean/_build/default/backend/driver/main.exe`; `git -C cerberus-lean log --oneline -1` → `89f7e6885 docs: orchestrator handoff …` — the mainline build, not the pin (standing caveat).

### 4.2 Census — `scripts/signature_snapshot.lean` at HEAD (`CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean`, 47 085 lines) then `cmp` → identical to `docs/2026-09-07_l1-signatures-post.txt`. `python3 census.py <pre> <post>`:

```
PRE 4584 entries; POST 4950 entries; ADDED 368 / REMOVED 2 / CHANGED 18
ADDED by kind: {'opaque': 4, 'def': 153, 'theorem': 211}
REMOVED: ['CerberusHeapLang.procCtxF_runState', 'CerberusHeapLang.procCtx_runState']
CHANGED: ['CerberusHeapLang.eo_wp_readout', 'CerberusHeapLang.fr_wp_readout', 'CerberusHeapLang.load_atomic', 'CerberusHeapLang.negFree.eq_def', 'CerberusHeapLang.wps_sound', 'CerberusHeapLang.wps_sound_cps', 'CerberusHeapLang.wps_sound_empty', 'CerberusHeapLang.wps_sound_frame', 'CerberusHeapLang.wps_sound_frame_empty', 'CerberusHeapLang.wpt_driver_aux', 'CerberusHeapLang.wpt_driver_cps', 'CerberusHeapLang.wpt_driver_done', 'CerberusHeapLang.wpt_driver_done_alloc', 'CerberusHeapLang.wpt_driver_done_procs', 'CerberusHeapLang.wpt_sound', 'CerberusHeapLang.wpt_sound_cps', 'CerberusHeapLang.wpt_sound_empty', 'CerberusHeapLang.wpt_step_eq']
  CerberusHeapLang.t1_certified_production: SAME
  CerberusHeapLang.exhibitA_prod: SAME
  CerberusHeapLang.fib_rec_certified: SAME
  CerberusHeapLang.even_odd_certified: SAME
  CerberusHeapLang.MemTriple: SAME
  CerberusHeapLang.project_triple_pure: SAME
  CerberusHeapLang.DriverSafeCtl: SAME
  CerberusHeapLang.DriverDoneCtl: SAME
  CerberusHeapLang.prod_run_eqJ_lib1: SAME
  CerberusHeapLang.wps: SAME
  CerberusHeapLang.wpt: SAME
  CerberusHeapLang.Frag: SAME
  CerberusHeapLang.Step: SAME
  CerberusHeapLang.procCtx: SAME
  CerberusHeapLang.prodCtx: SAME
  CerberusHeapLang.loop_step_frag: SAME
  CerberusHeapLang.engine_step_matchU: SAME
  CerberusHeapLang.t5_certified_production: NEW
  CerberusHeapLang.t6_certified_production: NEW
  CerberusHeapLang.t4_certified_production: NEW
  CerberusHeapLang.wps_bound: SAME
  CerberusHeapLang.wpt_bound: SAME
  CerberusHeapLang.prodCtl: SAME
  CerberusHeapLang.fib_certified_production: SAME
  CerberusHeapLang.counter_loop_certified: SAME
  CerberusHeapLang.load_atomic: CHANGED
===== E4 post -> E5 slice-1 post =====
PRE 4362 entries; POST 4584 entries; ADDED 224 / REMOVED 2 / CHANGED 82
ADDED by kind: {'def': 16, 'theorem': 184, 'ctor': 24}
REMOVED: ['CerberusHeapLang.Frag.pot_le_two', 'CerberusHeapLang.pot_action']
===== e5b -> l1 =====
PRE 4718 entries; POST 4950 entries; ADDED 236 / REMOVED 4 / CHANGED 4
REMOVED: ['CerberusHeapLang.t5IntBytes', 'CerberusHeapLang.t5IntMval', 'CerberusHeapLang.t5Int_encodes', 'CerberusHeapLang.t5Int_storable']
CHANGED: ['CerberusHeapLang.load_atomic', 'CerberusHeapLang.wpt_t5AssignBlock', 'CerberusHeapLang.wpt_t5If', 'CerberusHeapLang.wpt_t5Return']
===== WHOLE RANGE: E4 post -> L1 head =====
PRE 4362 entries; POST 4950 entries; ADDED 592 / REMOVED 4 / CHANGED 96
ADDED by kind: {'def': 169, 'opaque': 4, 'theorem': 395, 'ctor': 24}
REMOVED: ['CerberusHeapLang.Frag.pot_le_two', 'CerberusHeapLang.pot_action', 'CerberusHeapLang.procCtxF_runState', 'CerberusHeapLang.procCtx_runState']
```
(The 82 CHANGED of E4→slice-1 are listed in full in the scratch output and match `e5-notes.md` §8's three lists name for name — DERIVED by inspection. "SAME" for `DriverSafeCtl`/`DriverDoneCtl` is the snapshot's TYPE; their bodies changed, as the record says.)

### 4.3 Independent axiom sweep — `probe2.lean` (`open Lean`; `for nm in CerberusHeapLang.Audit.trioExports do … collectAxioms nm`; `lake env lean` under `capped`, 1.4 s):

```
trioExports: 893 names checked; missing: 0; not-trio-exact: 0
trioExports: 893 entries, 893 distinct
  CerberusHeapLang.t5_certified_production: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.t6_certified_production: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.t4_certified_production: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.t1_certified_production: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.wps_neg_bound: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.wpt_neg_bound: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.wps_bound: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.wpt_bound: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.Step.negFree_preserved: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.Step.pot_le: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.engine_step_matchU: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.frag_round_complete: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.loop_step_frag: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.wpt_driver_done_alloc: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.prod_run_eqJ_lib1: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.CorpusE0.t5Main_frag: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.CorpusE0.t6Main_frag: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.CorpusE0.t4Main_frag: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.t4Index_cases: #[Quot.sound, propext]
  CerberusHeapLang.t4Sum_le: #[Quot.sound, propext]
  CerberusHeapLang.t4Guard: #[Quot.sound, propext]
  CerberusHeapLang.t4Budget_succ: #[Quot.sound, propext]
  CerberusHeapLang.t4Sum_succ: #[]
  CerberusHeapLang.t4Kill_eq: #[]
  CerberusHeapLang.t6Kill_eq: #[]
  CerberusHeapLang.t5Kill_eq: #[]
  CerberusHeapLang.t5Store_eq: #[]
  CerberusHeapLang.t4Main_pot: #[propext]
  CerberusHeapLang.t5Main_pot: #[propext]
  CerberusHeapLang.t6Main_pot: #[propext]
  CerberusHeapLang.peDepthList_map_eq: #[propext]
  CerberusHeapLang.peDepthAlts_map_eq: #[propext]
  CerberusHeapLang.load_atomic: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.excluded_store_atomic: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.Step.sup_sym_le: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.do_race_addExcl_neg: #[Quot.sound, propext]
  CerberusHeapLang.esize_le_pot: #[Quot.sound, propext]
  CerberusHeapLang.pot_negRewrite_le: #[Quot.sound, propext]
  subst_sym_pexpr_lemFuel.eq_def: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.negFree.eq_def: #[propext]
  CerberusHeapLang.step_ctx_neg: #[Classical.choice, Quot.sound, propext]
  CerberusHeapLang.neg_bound_round: #[Classical.choice, Quot.sound, propext]
  banned in cone of CerberusHeapLang.t5_certified_production: []
  banned in cone of CerberusHeapLang.t6_certified_production: []
  banned in cone of CerberusHeapLang.t4_certified_production: []
```

### 4.4 The round trace and the composites — `probe1.lean` (`lake env lean --load-dynlib=libcf.so`, 2.3 s; `libcf.so` = the workspace's `CerberusFresh.c.o.export` + `native/md5.c`, needed for the `cerb_digest_get` extern `initial_driver_state` reaches; the trace prints, after `k` inner-loop rounds from `prodEntryStateLib stdlibE3 [] 600 CorpusE0.t5Main CerbFS.fs_initial_state`, the run state's supplies, the head step of round `k+1` and a depth-9 constructor skeleton of the arena — the rows of the assignment, arena cut at 110 chars):

```
40	sym=600	excl=0	next=tau[Ewseq Eannot]	arena={A}sseq(sseq(sseq(bound(wseq({A}pure; wseq(neg:store; pure))); pure); pure); sseq(bound(wseq(pure; load)); …
41	sym=600	excl=0	next=withrs-tau[Neg Action, no break ==> refined-cerberus/worktrees/dialect-e0/docs/corpus-e0/t5_ifelse.c:1:48-53]	arena={A}sseq(sseq(sseq(bound({A}wseq(neg:store; pure)); pure); pure); …
42	sym=601	excl=1	next=tau[Ewseq]	arena={A}sseq(sseq(sseq(bound(wseq(unseq[excl[0](store), {A}wseq(…; …)]; pure)); pure); pure); …
43	sym=601	excl=1	next=withrs-eval[Epure]	arena={A}sseq(sseq(sseq(bound(wseq(unseq[excl[0](store), {A}pure]; pure)); pure); pure); …
44	sym=601	excl=1	next=withrs-eval[eval operands of Store]	arena=(same)
45	sym=601	excl=1	next=action[StoreRequest]	arena=(same)
46	sym=601	excl=1	next=tau[Eunseq]	arena={A}sseq(sseq(sseq(bound(wseq(unseq[{A}pure, {A}pure]; pure)); pure); pure); …
47	sym=601	excl=1	next=tau[Ewseq Eannot]	arena={A}sseq(sseq(sseq(bound(wseq({A}pure; pure)); pure); pure); …
48	sym=601	excl=1	next=withrs-eval[Epure]	arena={A}sseq(sseq(sseq(bound({A}pure); pure); pure); …
49	sym=601	excl=1	next=tau[CTX, Ebound Eannot(value)]	arena={A}sseq(sseq(sseq(bound({A}pure); pure); pure); …
50	sym=601	excl=1	next=tau[Esseq]	arena={A}sseq(sseq(sseq(pure; pure); pure); …
```
(rounds 0–39 and 50–68: creates, stores, the condition's loads/case/if, the return's load, the kills, `Erun`, the `save` — `sym=600 excl=0` throughout 0–40 and `601/1` from 42 to the end; the full 72-row trace is in the scratch log, deleted). Verdicts and composites, verbatim:
```
t5 verdict@68=killed:Error0:lem: fuel exhausted @69=active
t6 verdict@66=killed:Error0:lem: fuel exhausted @67=active
t4 verdict@592=killed:Error0:lem: fuel exhausted @593=active
t5 sup=600: active; ==lint 1: true; ==lint 20: false; ==lint 10: false; blocked=false; stdout=''; stderr=''
t6 sup=600: active; ==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''
t4 sup=600: active; ==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''
t5 sup=0: active; ==lint 1: true; ==lint 20: false; ==lint 10: false; blocked=false; stdout=''; stderr=''
t6 sup=0: active; ==lint 1: false; ==lint 20: true; ==lint 10: false; blocked=false; stdout=''; stderr=''
t4 sup=0: active; ==lint 1: false; ==lint 20: false; ==lint 10: true; blocked=false; stdout=''; stderr=''
```

### 4.5 The collision probe (D-2), verbatim (backtrace lines elided):
```
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Kill
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Kill]
t5 sup=505 (= x's symbol number): killed:other
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Load]
t5 sup=506 (= r's symbol number): killed:other
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: can_advance: Step_error2 ==> Load
PANIC at _private.LemLib.0.failwithIImpl LemLib:171:2: Driver.process_core_step2: WRONG STEP ==> Step_error2[Load]
t4 sup=505: killed:other
```

### 4.6 `cite_check.sh` (report only; `bash scripts/cite_check.sh` from `cerberus-heaplang/`): summary line quoted in §2.8. The ten sampled non-EXACT lines (every tenth of the 101, offset 3) and the hand-check:

| ARCH line | cite | reality at HEAD | verdict |
|---|---|---|---|
| :44 | `Step.lean:5464`, `:5440` (`spikeCtx`/`spikeCtl`) | `:5440` is blank; `spikeCtl` at `:6278` | STALE (E5 shift) |
| :105 | `Soundness.lean:7987`–`:8068` (the `Frag` header) | `:8068` is `phase A)`; `Frag` at `:9368` | STALE |
| :253 | `Rules.lean:35`–`:44` | the "WHAT IS DELIBERATELY NOT HERE" passage | correct |
| :288 | `CerberusRound.loop_step`, `:1045` | at `:1097` | STALE |
| :359 | `diverge_total_unprovable` `:172` | at `:176` (`:172` inside its docstring) | near |
| :420 | `MemTriple_alloc`, `:1682` | at `:1733` | STALE |
| :559 | `CerbFS.lean:47` (pinned) | the refusal comment | correct |
| :696 | `engine_adequacy` `Adequacy.lean:1304`–`:1316` | at `:1342` | STALE |
| :713 | `Frag.esize_le_pot` `:172` (Potential) | `:172` blank; `esize_le_pot` `:241`, `Frag.esize_le_pot` `:260` | STALE |
| :802 | `test_unit.sh:99` (boundary check) | exactly the boundary speedbump line | correct (the script's USE suggestion `96` is wrong) |

### 4.7 DECISIONS greps at HEAD (R-1): `git grep -n 'already authorized' -- docs/DECISIONS.md` → `3205`; `git grep -n 'USER, paraphrase' -- docs/DECISIONS.md` → `3228`; `git diff --stat 0e161f4..093b02b -- docs/DECISIONS.md` → `498 insertions(+)`; `git diff --stat dialect-e5 HEAD -- docs/DECISIONS.md` → `117 insertions(+)` (0 deletions).

---

## 5. Not checked

- A cache-disabled rebuild (the gate replayed the primed `.lake`; certification-integrity doctrine would want `--force` for build-rule changes — the range changed none).
- The `;`-association of the transcriptions against the frontend's `erase_loop_control_aux`/`translate_stmt`/`mk_unit_sseq` (the t4 record's source inspection); the unprinted action/undef locations and the unprinted `x`/`r`/`i`/`s` symbol numbers (α-equivalent; the label continuations the certifications use are the ENGINE's `collect_saves` by `rfl`).
- The OCaml oracle at the PIN (the binary is the mainline build) and at a chosen `sup` (the pipeline fixes the supply); the digest the OCaml `fresh_symbol` uses vs the Lean runtime's `""`.
- The 11-arm `sseq_inv`/`wseq_inv` case analyses of `wps/wpt_seq_sym_annot` and `wps/wpt_bound_wseq_tuple` line by line against the E1/E2 certifications (they compile, pin trio-exact, and their engine arms are pre-range).
- `cite_check`'s remaining 91 non-EXACT lines individually.
- The whole-range census pre-snapshot is the E4 POST snapshot, not a regeneration at `901ef50` (that would need a build of main's Lean in another worktree, which I was told not to touch); the E4-audit fixes between the two added pins only.
- `OpenRound.neg_sseq`'s reachability from the wider emitted corpus (t2/t3/t7–t10) — asserted by the design note's measurement, not re-measured.

Ephemeral scratch (`.audit-scratch/`: `diffs/*.diff`, `census.py`, `probe1.lean`, `probe2.lean`, `libmd5.so`, `libcf.so`, `head-signatures.txt`, `gate.log`, `probe*.out`, `cite_nonexact.tsv`) — deleted at the end of this pass; every command is stated inline above and the probe sources follow the landability audit's Appendix A recipes (probe1 adds a depth-bounded constructor printer over `generic_expr_`/`generic_action_` and a `core_step2` step-kind printer; probe2 is the `collectAxioms` loop over `CerberusHeapLang.Audit.trioExports` quoted in §4.3).
