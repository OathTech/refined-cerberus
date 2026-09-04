# Known open items — the register auditors read FIRST

State: candidate `hygiene-h1` head dd7b852+ (2026-09-04, after the calls arc,
the fuel-lane restatement F1, the external-audit response AR5, the H1
hygiene/coverage slices, their range audit, and the ARCHITECTURE rewrite). Maintained by the orchestrator; every entry
points at the record that owns it. PURPOSE: an auditor should not
re-cite an item listed here as a new finding. Cite it ONLY if (a) the
entry is factually wrong, (b) the item is worse than recorded, or (c) a
listed mover has been missed by a slice that claimed it. Everything
else here is known, disclosed on the surfaces named, and has an owner
or a ruled disposition. Provenance tags as in `docs/DECISIONS.md`.

## A. Semantics-side defects, fixes requested upstream (not ours to fix)

| # | Item | Where recorded | Disposition |
|---|---|---|---|
| A1 | **Fuel constants baked into the port**: two constants (`CerbFuel.driverFuel = 10^8`, LemLib `lemDefaultFuel = 10^6`), ≥ 6 fuelled recursions sealed behind fixed wrappers (scheduler loop `driver2`, single-thread loop `drive_nonmemory_steps_aux2`, exit `hack`, a printer, ND `bind`). Our exports inherit it: `… ≤ lemDefaultFuel` / `≤ CerbFuel.driverFuel` hypotheses at ~60 sites; the nine production statements' `hfuel` bounds are shipped-constant instances. | DECISIONS 2026-09-03 "FUEL IS A DEFECT…"; `docs/2026-09-03_request-lem-lean-pmap-laws-and-fuel-scheme.md` §3 | [USER] ruled a cerberus-lean/lem-lean defect; fix asked of the cerberus-lean team (all magic values → quantifiable positions). Consumer restatement slice follows the fix. |
| A2 | **Closed partial forms quantify the OUTER (scheduler) fuel only** (`prod_run_safe_procs`, `fib_rec_certified` closed form, over `CerbND.drive_lemFuel fuel`): the seam threads fuel to `driver2` alone; for the sequential fragment the scheduler runs one round, so the quantifier is true but does no work. The run-length content is the thread-level `DriverSafeCtl` (∀ inner fuel). | DECISIONS same entry (the two-loop reading, [USER] verbatim); F1 audit §2 "no reword required — disclosed"; ARCHITECTURE/README/API.lean state the scope | Interim by ruling until A1 lands. NOT a soundness item. |
| A3 | **`dynamic_addrs` upstream defect** (free after zero-size malloc sharing a base): Core-level claim confirmed on both oracles and Lean; NOT reproducible from C; Lean is a faithful mirror; ISO-fix register R4 DEFERRED upstream. Our K3 `free` precondition (metadata `dynamic` flag) implies the engine's check; the colliding program is outside the logic. | DECISIONS 2026-09-03 "CERBERUS-LEAN MOVED…"; `docs/2026-09-03_upstream-note-dynamic-addrs.md`; cerberus-lean `lean_frontend/docs/2026-09-03_dynamic-addrs-investigation.md` | CLOSED for us, no change. Our note's C-flavoured consequence was in error (recorded). |
| A4 | **LemLib `Pmap`**: no lookup-after-insert law shipped (our `SymMap`/`symAdd_lookup*` must be re-proved at the re-pin); `Pmap.join` is well-founded recursion, so closed engine maps do not reduce (17 declarations stall at cerberus-lean `de2fbf1`). | `docs/2026-09-03_repin-scout-2.md` §4 (a), (a′), §8; request note above §1–2 | Requested from lem-lean; local interim law allowed. Re-pin slice pending the next cerberus-lean pin. |
| A5 | **`killM`'s dead-static-kill arm is `panic!`, read by the kernel as the `Inhabited` default.** No current export quantifies over all kills (every kill/free rule presupposes a live cell). cerberus-lean's typed-failure-outcomes pass will remove the `Inhabited` semantics. | scout §8 (γ); cerberus-lean Z1 manifest §2 | Re-check `MemWF.killM` at that re-pin. |
| A6 | **Re-pin drift**: main's pin is cerberus-lean `f95ef8d9c`; mainline is ≥ 34 commits ahead (`de2fbf1`), with the LemLib representation change (A4), `killM` re-mirroring (one exported text change: `killM_killed_inv`), fold/zip non-reduction (13 declarations). Everything else on the manifests measured zero for this package. | scout record §4–§6 (plan, 2.5–4 worker-days) | Re-pin waits for the NEXT cerberus-lean pin ([USER]: "it'll likely have moved again"). |

## B. Statement-shape and coverage limitations, disclosed by design

| # | Item | Where | Mover |
|---|---|---|---|
| B1 | **Six any-memory TOTAL equations deleted at F1 without twins** (`exhibitA/fib/list_reverse/dispose_list/region_loop/malloc_list_certified_total`): their cold-start production twins cover the programs, not the arbitrary-seeded-memory termination facts; the surviving seeded forms are partial. **Tree rotation has NO shipped-pipeline statement of any kind** (`tree_rotate_certified_total` deleted; needs a self-contained tree-building program or re-contexting). | F1 notes §6 items 4–5 (erratum applied); F1 audit R-2; DECISIONS F1-audit entry; `FibExhibit.lean` header | Shipped-loop total twins at `procCtx` (`DriverDoneCtl`), in the `prodCtx` re-context slice — deferred until after the re-pin and A1 (would be rewritten twice otherwise; DECISIONS 2026-09-03). |
| B2 | **Straight-line exhibits stay at the no-procedure profile** (`spikeCtx`/`spikeCtl`, a thread state the shipped driver never parks); admitted because the round needs the procedure tie only at a jump (`CtlTied.noproc`). The single-procedure driver lane was kept beside the general N-procedure lane (C4 decision (b)). | F1 notes §6 item 1; C4 notes §9 (b); ARCHITECTURE | Same `prodCtx` re-context slice (B1's mover). |
| B3 | **Seeded exhibits have no closed (cold-start) form**; only `fib_rec_certified` got the closed partial form. | F1 notes §6 items 2–3 | Same slice; low priority. |
| B4 | `hwf : SeqWF` dropped from the partial lane (strict generalization); `htd`/`hex` (empty tag definitions / extern) ADDED to the partial lane — a narrowing that matches the production driver's `drive fmapEmpty false …`. | F1 notes §6 item 6; F1 audit §4 | Accepted; disclosed in WALKTHROUGH §1.1. |
| B5 | **Closed shape is the singleton-execution EQUATION**, stronger than the intended "∀ outcome ∈ the run's outcome list" reading (the sequential driver is deterministic). The outcome-list form is the meaning that survives concurrency. | F1 notes §6 item 7; DECISIONS fuel entry (the R/O'H reading) | Doc surfaces to state the outcome-list reading explicitly — folded into the A1 restatement slice. |
| B6 | **`fib_rec_certified_production`'s `hfuel : fibRounds n + 4` has ONE unit of slack** (shipped loop killed at `+2`, done at `+3`); `fibRounds` itself exact; slack is in `main`'s frozen `wpt` budget. Nothing claims tightness. Same class: `even_odd_certified_production`'s `3·n + 6` (shipped loop active at `3·n + 5`) and `tl_wpt`'s `5·n₁ + 5·n₂ + 5` (shipped loop needs `3·n₁ + 3·n₂ + 4`; the rule constant 3 per store vs one engine round — the ProdLoopExhibit `6n + 8` class) — H1 range audit Note-2. | C4 audit R-3; F1 notes handoffs | Optional `k + 1` mover; not scheduled. |
| B7 | **Mirror-completeness residuals**: two `OpenRound` arms (`eval_uncovered`, `run_surplus`) characterised, not closed; the `hbsz` premise inside `Frag.case_value` carried, not proved. | ARCHITECTURE §2.2 (the residual) and §6 "The mirror-completeness residual" (the `hbsz` premise); `docs/2026-09-02_fragment-closure-notes.md` | By design (fail-closed boundary). |
| B8 | **Not in the fragment, by design**: function pointers (`Eccall`, a scheduler path — [USER 2026-09-04]: belongs to the RefinedC arc), concurrency, external C calls. (Mutual recursion and the two-`save`-label program are EXHIBITED since H1b: `EvenOddExhibit`, `TwoLabelExhibit`.) | ARCHITECTURE §6; DECISIONS 2026-09-04 | Scope rulings; not defects. |
| B9 | **Deferred parametric-semantics interfaces**: rules are proved directly against `Step` and the memory state. | ARCHITECTURE §6 "Deferred parametric semantics interfaces"; `docs/2026-09-02_parametric-semantics-spike.md` (DEFERRED banner) | [USER] deferred, "possibly forever". |
| B10 | **The referent rule's interim clause** ("until it lands the affected exports are labelled PROVISIONAL") remains in `CLAUDE.md` as RULE text; there are ZERO PROVISIONAL labels on any surface after F1. | F1 audit §6 | Not a finding. |
| B11 | **Mask generalisation (external audit F3)**: `wps`/`wpt` hard-code the top invariant mask (21 + 26 sites); mask-polymorphic composition is not available. Classical sequential SL by ruling. | audit F3; DECISIONS 2026-09-04 ("best possible Reynolds/O'Hearn … fancy logic features aren't needed") | [USER 2026-09-04] MOVED TO THE REFINEDC ARC (with function pointers); not a demo item. |
| B12 | **Two engine-round bridges** (`engine_step_matchU` for the mirror's certification; `loop_step_frag` for both adequacy lanes) — a documented design (ARCHITECTURE §2.2), duplication/drift risk noted by the external audit. | audit "Note"; ARCHITECTURE §2.2 | By design; consolidation not scheduled. |
| B13 | ~~Three total rules proved but undemonstrated~~ CLOSED at H1 (`wpt_load` via the rewritten `progA_wpt`; `wpt_case_value`/`wpt_wseq` via `caseProg_wpt`/`wseqProg_wpt`); manifest 30 RULE / 0 undemonstrated. | `docs/2026-09-04_h1-notes.md` | Closed. |
| B14 | **NO-RULE variants classified by [AGENT]** from the engine's admitted cases (union-member-pointer store/load/kill, read-only-cell load face, zero-size/atomic/non-inert `create` types, whole-object load/store at an atomic-typed allocation, `SD_Id`-named-function-vs-concrete `PtrEq`). | manifest rows; AR5-manifest record §1–§2; AR5 range audit §2.2, C-3, C-4 | CONFIRMED by the AR5 range auditor (seven exactly, one sharpened, two added by the audit). Any further variant found is a new row, not a new finding class. |

## C. Hygiene queue (no trust or correctness content)

| # | Item | Where | Status |
|---|---|---|---|
| C1 | CLOSED at H1a: call clause destructured, both eta-hacks gone (76 occurrences → 0); `wpt_call_eq` text changed by exactly the destructuring. | `docs/2026-09-04_h1-notes.md` | Closed. |
| C2 | `LoopOutcome` duplicates `DriverSafeCtl`'s 15-line conclusion verbatim. | F1 audit H-3 | Queued with the A1 restatement (same statements). |
| C3 | CLOSED at H1a: `spikeCtx_wf`, `procCtx_wf`, `outcomesU_done`, `outcomesU_of_step`, `outcomesU_remove_annot` deleted. | `docs/2026-09-04_h1-notes.md` | Closed. |
| C4 | Duplication in ProdEntry: `*With` entry forms copy the one-procedure forms though `prodFile e = prodFileWith [] e` is `rfl`; six one-shape `fr*_pure/_depth` lemmas; `frCtx_labels_cases` vs `frCtx_labeledProcs`. Partly done at F1 (`drive_after_setup_with` is now the `driverFuel` instance). | C4 audit H-2; F1 handoffs | Queued. |
| C5 | Linter warnings in `CerberusHeapLang/*` (unused simp arguments / unused variables; Potential.lean the bulk): 66 at C3 (all pre-C3 by blame) → 62 at the H1 candidate (F1 removed 4 in TotalAdequacy; H1b introduced 2 in EvenOddExhibit, removed again by the H1 range audit's H-1 fix). | C3 audit H-1; H1 range audit H-1; gate log | Queued; low value. |
| C6 | The manifest generator hard-codes the smoke module list (`clientSmokes`). | C3 audit H-4; C4 (H-4 done for the header) | Cosmetic. |
| C7 | The cursor ghost heap as a proof device (kill/free record's item). | `docs/2026-09-03_kill-free-arc-record.md`; C4 notes §12 | Untouched; design note only. |
| C8 | CLOSED at H1a: `progA_wpt` REWRITTEN over the public readout (deleting it turned the manifest red — it was `wpt_store`'s only consumer); the boundary check now runs with ZERO allowances. | `docs/2026-09-04_h1-notes.md` | Closed. |
| C9 | CLOSED at H1a (API.lean pointer). | `docs/2026-09-04_h1-notes.md` | Closed. |
| C10 | `deadObj_dead`/`deadRegion_dead` reclassified below the API line in prose only (statements unchanged). | AR5-readout record §6 | Confirm at the next API pass. |
| C11 | The boundary check's comment stripping is not string-literal-aware: a `"--"` or `"/-"` inside a string literal would hide following code from the grep. No such literal exists in any subject module today (auditor-measured). | AR5 range audit H-1 | Low; fix if a literal ever appears, or make the stripper literal-aware. |
| C12 | Boundary allowances are per-module: a second, new internals mention in an allowlisted module (`Exhibit`) would not turn red. | AR5 range audit H-2 | Optional expected-count cell; moot once C8 removes the last allowance. |
| C13 | CLOSED at H1a (TSV header: "rule use only through imported clients"). | `docs/2026-09-04_h1-notes.md` | Closed. |
| C14 | THIRTEEN consumerless lemmas in Soundness.lean since H1a deleted `outcomesU_of_step`: the ten `stepDischarge_*` plus `dischargeStep_kill_active`/`dischargeStep_alloc_active`/`dischargeStep_memop_active` (in-degree 0 at HEAD, measured by the H1 range audit — the worker's count of ten was corrected there, R-1); DriverCollapse documents the `stepDischarge_*` as its twins. | H1 record + `docs/2026-09-04_audit-h1-range.md` R-1 | Delete or re-home; hygiene. |
| C15 | `Audit.lean`'s pin list has two duplicate entries (`loop_step_frag`, `loop_step_frag_same`): "402 pins" is the list length; 400 distinct names (376 = 374 distinct at the AR5 candidate). | H1 range audit Note-1 | Dedupe; then every "402" on the surfaces becomes 400 — do it in one docs+Audit commit. |

## D. Record errata already applied (append-only register — do not re-report)

- DECISIONS 2026-09-04 external-audit entry: "10 stale seeds" → 6 (worker probe).
- DECISIONS 2026-09-04 AR5 landing entries: gate quotes were trimmed (prefix stripped, lines cut at 200 chars) → re-quoted untrimmed in the AR5 range-audit entry, with the elision rule for all earlier gate quotes stated there (AR5 range audit R-1).
- DECISIONS "28 commits past the pin" → 34 (F1 audit H-1); "ONE CONTENT
  LOSS" → the B1 loss class (F1 audit R-2); "PROVISIONAL … 1 files" → the
  CLAUDE.md rule sentence (B10); "two linter warnings" → 66 pre-existing
  (C3 landing entry, corrected in the C3 audit entry). Each correction
  sits in a LATER entry; the earlier text is left as written by the
  register's rule ("later governs").
- Design-note premises falsified by measurement and recorded as such
  (not defects): RETURN does not restore `exec_loc` (C3); registration
  fold order (C4, then re-measured ascending at the scout); the
  `fibRounds` "≈9" (exact 9); C2's "no judgment change" (a `⌜False⌝`
  guard was forced); `size_pos`/`killM`-`dynamicAddrs` premises (K3).

## E. Tree and environment notes (for anyone running the gates)

- Primary checkout `.cerberus-ws` is primed at the PIN (`f95ef8d9c`);
  `scripts/setup-cerberus-dep.sh --check` is the verification. The
  worktree `worktrees/repin-scout2` holds a `.cerberus-ws` primed at
  `de2fbf1` and a `.lake` dep cone at LemLib `3c88f0d` — for the re-pin
  worker; NOT main's state.
- Untracked, unrelated to the demo, left from the RefinedC exploration
  era: `.refinedc-ws/` (a Rocq/RefinedC workspace, ~3.7 GB) and
  `.opamroot/` (a sandbox opam root, ~150 MB). Both are ignored as of
  this commit; the RefinedC layer lives on branch `refinedc/dev`.
- Gates: `scripts/test_unit.sh` (FULL) / `--fast`; every Lean build
  through `scripts/capped`. Expected FULL tail at the H1 candidate: 402 pins trio-exact, manifest
  (50 rows; 30 RULE / 0 undemonstrated / 15 NO-RULE / 5 OUT-OF-SCOPE) no
  drift, import direction ok, `BOUNDARY: 19 modules checked, 0 internals
  mention(s) in total, exit=0` with NO ALLOWLISTED line, `ALL GATES GREEN`,
  `GATE-EXIT=0` (DECISIONS 2026-09-04 H1 entry, verbatim).
