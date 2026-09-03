# Known open items — the register auditors read FIRST

State: main `e34b30b` (2026-09-03, after the calls arc C1–C4 and the
fuel-lane restatement F1). Maintained by the orchestrator; every entry
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
| B6 | **`fib_rec_certified_production`'s `hfuel : fibRounds n + 4` has ONE unit of slack** (shipped loop killed at `+2`, done at `+3`); `fibRounds` itself exact; slack is in `main`'s frozen `wpt` budget. Nothing claims tightness. | C4 audit R-3; F1 notes handoffs | Optional `k + 1` mover; not scheduled. |
| B7 | **Mirror-completeness residuals**: two `OpenRound` arms (`eval_uncovered`, `run_surplus`) characterised, not closed; the `hbsz` premise inside `Frag.case_value` carried, not proved. | ARCHITECTURE §6 (lines ~412–444); `docs/2026-09-02_fragment-closure-notes.md` | By design (fail-closed boundary). |
| B8 | **Not in the fragment, by design**: mutual recursion (rule admits it, no exhibit), function pointers (`Eccall`, a scheduler path), a two-`save`-label exhibit (the law landed at C4, exhibit absent), concurrency, external C calls. | ARCHITECTURE §7 "still open from the arc" | Scope rulings; not defects. |
| B9 | **Deferred parametric-semantics interfaces**: rules are proved directly against `Step` and the memory state. | ARCHITECTURE §7; `docs/2026-09-02_parametric-semantics-spike.md` (DEFERRED banner) | [USER] deferred, "possibly forever". |
| B10 | **The referent rule's interim clause** ("until it lands the affected exports are labelled PROVISIONAL") remains in `CLAUDE.md` as RULE text; there are ZERO PROVISIONAL labels on any surface after F1. | F1 audit §6 | Not a finding. |

## C. Hygiene queue (no trust or correctness content)

| # | Item | Where | Status |
|---|---|---|---|
| C1 | Call clause uses `q.2.1`/`q.2.2` projections; eta-hack `hq` in both collapses; 56 sites incl. the pinned `wpt_call_eq` text. | C3 audit H-3; C4 notes §9 (c) | Parked; pin-independent, may be done any time (snapshot-checked). |
| C2 | `LoopOutcome` duplicates `DriverSafeCtl`'s 15-line conclusion verbatim. | F1 audit H-3 | Queued with the A1 restatement (same statements). |
| C3 | Consumerless after F1: `spikeCtx_wf`, `procCtx_wf` (Step), `outcomesU_done`, `outcomesU_of_step` (Soundness; `outcomesU_remove_annot` IS consumed by it), `progA_wpt` (Exhibit). | F1 notes §9 (corrected per F1 audit H-2) | Queued. |
| C4 | Duplication in ProdEntry: `*With` entry forms copy the one-procedure forms though `prodFile e = prodFileWith [] e` is `rfl`; six one-shape `fr*_pure/_depth` lemmas; `frCtx_labels_cases` vs `frCtx_labeledProcs`. Partly done at F1 (`drive_after_setup_with` is now the `driverFuel` instance). | C4 audit H-2; F1 handoffs | Queued. |
| C5 | 66 linter warnings in `CerberusHeapLang/*` (unused simp arguments / unused variables; Potential.lean the bulk); ALL pre-date C3 (blame-verified); zero added since. | C3 audit H-1; DECISIONS | Queued; low value. |
| C6 | The manifest generator hard-codes the smoke module list (`clientSmokes`). | C3 audit H-4; C4 (H-4 done for the header) | Cosmetic. |
| C7 | The cursor ghost heap as a proof device (kill/free record's item). | `docs/2026-09-03_kill-free-arc-record.md`; C4 notes §12 | Untouched; design note only. |

## D. Record errata already applied (append-only register — do not re-report)

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
  through `scripts/capped`. Expected FULL tail at `e34b30b`: 373 pins
  trio-exact, `ALL GATES GREEN`, `GATE-EXIT=0` (DECISIONS F1-audit entry,
  verbatim).
