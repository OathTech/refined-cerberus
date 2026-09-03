# F1 range audit (`328be1a..2bbfd70`) — 2026-09-03

[AGENT] Independent auditor record (fresh auditor, not the C3 or C4 one).
Audited in the fixed detached copy `worktrees/audit-f1-2bbfd70` (HEAD
`2bbfd70`, detached; `.lake` and `.cerberus-ws` primed; cerberus-lean pin
`f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`, read off
`git -C .cerberus-ws rev-parse HEAD`). Read-only except this file and an
ephemeral scratch dir (`.audit-scratch/`, deleted after this report was
written; every quoted line below was copied from it verbatim before
deletion). Nothing committed, merged or pushed. Every Lean invocation went
through `scripts/capped` with `CERB_MEM_MAX=40G` exported; `grep -ci
uncapped` over every build log = 0. Brief: `docs/AUDIT-BRIEF.md`. Inputs:
the four-commit range (37 files, +31934/−2939, of which the snapshot is
29041 lines), the worker record `docs/2026-09-03_f1-notes.md`, the two
snapshots (`_c4-signatures-post.txt` as pre, `_f1-signatures-post.txt` as
post), the C3/C4 range audits, `ARCHITECTURE.md` read in full as a core
document at a major revision, `docs/DECISIONS.md` tail, the PINNED
SEMANTICS at `.cerberus-ws/lean_frontend/{generated/Driver.lean,
CerbND.lean, CerbFuel.lean}`, and the three cerberus-lean docs the
DECISIONS "cerberus-lean moved" entry cites (read-only, in
`../../cerberus-lean/lean_frontend/docs/`).

Method. (1) The FULL Lean diff was read (Adequacy, DriverCollapse,
ProdEntry, ProdLoop, Round, TotalAdequacy, Audit, API, Soundness, Step,
Wpt, Lang, Heap, Potential, ProdExhibit, and all 14 exhibit/example
files). (2) `#print`/`#check` on every restated export and `#print axioms`
on the 14 new pins, `runND_killed` and 8 restated names. (3) The engine
facts the record cites were re-read on the pin at the cited lines. (4) The
FULL gate was run by the auditor in the audit copy (§Gate). (5) The
snapshot was regenerated at HEAD and compared byte-for-byte; the census
was re-derived by script from the two committed files; the nine
production statements and eight rule/collapse statements were diffed in
source (statement through `:=`) across the range ends. (6) Six plant
tests (five distinct plants, one re-applied after a mis-count), each with
rebuild-after-revert. (7) The 62 package linter warnings re-tallied by
file. Quotes are verbatim; tallies marked DERIVED were computed by the
auditor's scripts or arithmetic.

## Verdict

**PASS WITH FIXES REQUIRED (docs-only) — grade A−. Merge-ready for
`328be1a..2bbfd70` on operator sign-off, with two docs-only corrections
(R-1, R-2) to land with the merge; no proof changes required.** No T-
(trust) or C- (correctness) finding. The slice's claim holds by
measurement: `driveU` and its whole cone are gone from the tree (REMOVED
73, incl. the 31 `DriveResult*` auxiliaries; `git grep driveU` on the
shop-window surfaces hits only sentences saying it was deleted); every
surviving partial-correctness export's referent is the shipped driver's
own per-thread loop `drive_nonmemory_steps_aux2_lemFuel` (generated
Driver.lean:346) through `runOne` (the `ND` eliminator, Step.lean:1385) —
`DriverSafeCtl` names no package loop, discharge or scheduler, its
non-semantics constants are exactly the thread builder `ctlThread` and the
two registration ties `LabeledProcs`/`CtlTied` (all three hypotheses, all
three C4-vintage or the C4 shape); the killed arm is literally
`NDkilled CerbND.fuelExhaustedKill`, anchored by the semantics' own
`CerbND.drive_nonmemory_steps_aux2_lemFuel_zero` (Plants B/B′ show a
different constant fails at the `_zero`-derived sites); the program-done
arm is the loop's `NDactive (fmapAddBy defaultCompare 0 [Step_done2 v] acc)`
at a thread `ctlThread th₀ (ofVal (.pure v)) ρfin ⟨[], pfin, ℓfin⟩` —
exactly what `step_ctx_done` (arena `ofVal (.pure v)`, `stack0 =
Stack_empty`) produces and what the pinned, textually-unchanged
`driver2_done` consumes into `prepare_exit`; `prod_run_safe_procs`'s
conclusion is `CerbND.runND (CerbND.drive_lemFuel fuel …)
(initial_driver_state …).1 = [(st, [], dst')]` with the two-arm
disjunction, `drive_lemFuel` the semantics repo's own mirror pinned by
`CerbND.drive_wrapper_defeq : drive = drive_lemFuel CerbFuel.driverFuel :=
rfl` (CerbND.lean:467); the pinned C2 statements `loop_step_frag` and
`loop_step_frag_same` are byte-identical in source and are one-line
instances of the primed forms; the census holds exactly (3017 → 2971,
ADDED 27 / REMOVED 73 / CHANGED 26 / UNCHANGED 2918, the CHANGED set =
the 26 restated statements the record lists); the nine production
statements and `driver2_done`/`finalize_done`/`drive_after_setup`/
`drive_after_setup_with`/`wpt_driver_cps`/`wpt_driver_done`/
`diverge_total_unprovable` are byte-identical in source; the HEAD
snapshot is byte-identical to the committed post file; all 14 new pins
are trio-exact and `runND_killed` has no axioms (so it is correctly
unpinned and sweep-bounded — the sweep line "every theorem bounded by the
trio (3396 swept)" covers it); all six plants went loud and every revert
came back green at 373; the DECISIONS gate tail matches the auditor's run
line for line (modulo the `info: …Audit.lean:567:0:` prefix the register
strips, as the C3/C4 entries did); PROVISIONAL survives outside dated
records in exactly one file, `CLAUDE.md:101`, which is the standing rule
text "…are labelled PROVISIONAL on every surface." — a rule, not a label
(confirmed).

Deductions from A: a code quote in the walkthrough was truncated mid-token
by the rewrite (R-1); the "ONE CONTENT LOSS" framing understates what the
deletions removed (R-2); four small record/prose inaccuracies (H-1..H-5).

## Findings, ranked

### R-1 (Required, docs) — WALKTHROUGH §1.1 quotes a truncated `project_triple_pure`

Evidence: `docs/WALKTHROUGH.md:116-133` — the ```` ```lean ```` block opens
with `theorem project_triple_pure {GF : BundledGFunctors} [SpikeGpreS GF]`
and its LAST line is, verbatim,

```
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := by
```

followed by the closing fence. The `hwp` hypothesis is cut inside
`(hlc := .hasLC)`, and `hpost` and the conclusion `MemTriple M ctl (ev0 ::
evs) e P ψ := by` are missing. At `328be1a` the same block was complete
(lines 86-104, ending `MemTripleU M ctl (ev0 :: evs) e P ψ := by`), so the
truncation is this range's. The walkthrough's stated job is to quote the
definitions; §1.1's other five quotes (`MemTriple`, `DriverSafeCtl`,
`ctlThread`, `LabeledProcs`, `CtlTied`) are verbatim source (checked by
string containment against Adequacy.lean/DriverCollapse.lean). Premise
verified by measurement (script over the fenced blocks).

Fix: replace the block with Adequacy.lean:1605-1625 verbatim (statement
through `MemTriple M ctl (ev0 :: evs) e P ψ := by`).

### R-2 (Required, docs/record) — "ONE CONTENT LOSS" understates the deletions

Evidence. The record §1/§6 item 5, the DECISIONS F1 entry ("ONE CONTENT
LOSS — `tree_rotate_certified_total` deleted with no twin") and
`FibExhibit.lean:41-43` ("its content carried by
`fib_certified_production`") say the six other `_total` twins lost
nothing because a production statement carries their content. Measured
against the deleted statements (diff read): `fib_certified_total` was
`∀ σ₀ aids, driveU … (2·n+4) … σ₀ = .done (fib n) σ₀` — termination at the
derived bound FROM ANY INITIAL MEMORY with the FINAL STATE PINNED to the
initial one (the state-inert cone, also deleted); `list_reverse_/
dispose_list_/malloc_list_/region_loop_certified_total` were total
equations at the derived bounds `13·|ns|+7` / `12·|ns|+6` / `25·n+7` /
`7·n+3` from an ARBITRARY seeded memory next to an ARBITRARY disjoint frame
`R` (`Sat σ' (Q ∪ R)` returned); `exhibitA_total` likewise at the seeded
`σ₀`. Their production twins are cold-start (`prodMem₀`), self-contained
programs: the same *program* is covered, not the same *fact* — the
arbitrary-seeded-memory termination equations are gone. The surviving
seeded statements (`*_certified`) are partial (exhaustion admitted). For
the `procCtx` exhibits (fib, list reversal, dispose, region loop, malloc
list) a loop-level TOTAL twin over the shipped loop was available with
existing machinery (`wpt_driver_done(_alloc)` → `DriverDoneAt`, exactly as
`diverge_total_unprovable`'s proof now uses it) and was declined (§6 item
5, "a second statement of a fact already stated at the root of trust" —
which, per the above, it is not). Tree rotation is correctly singled out
as the one program with NO shipped-pipeline statement of any kind; that is
a different category from "the one content loss". The `fib_rec_certified`
restatement also traded its any-memory loop-level form for the cold-start
closed form (a deliberate, stronger-in-one-way/narrower-in-another trade,
not called out). Premise verified by measurement (statements read in the
diff; consumer machinery checked at DivergeExhibit.lean:184-216).

Fix (docs-only; the Lean is fine as is): (a) in the record §1/§6 item 5
and in a DECISIONS erratum entry (append-only), state the loss class
accurately: "the six seeded/any-memory TOTAL equations at the derived
bounds are deleted; their cold-start production twins cover the programs,
not the arbitrary-memory termination facts; the partial seeded forms
survive; tree rotation alone has no shipped-pipeline statement"; (b)
reword `FibExhibit.lean:41-43` ("its value content is carried by …; the
any-memory termination equation and the state pin are not restated"); (c)
optionally name the mover (the `DriverDoneAt` twins at `procCtx`, in the
`prodCtx` hygiene slice the record already names). Restating the totals is
NOT required for this merge.

### H-1 (record accuracy) — DECISIONS "28 commits past the pin"

Evidence: `docs/DECISIONS.md:1643` "CERBERUS-LEAN MOVED (mainline
de2fbf1, 28 commits past the pin f95ef8d …)". Measured in the read-only
semantics repo: `git rev-list --count f95ef8d..de2fbf1` = 34;
`--first-parent` = 34; `--no-merges` = 34 (the range is linear, no
merges). `de2fbf1` IS on `mdd/cerberus-lean` (`git branch --contains`).
Everything else in that entry checks against the cited docs: the Z1
manifest §1/§2/§4 (killM arms re-mirrored, `copyAllocId` real, device
ranges, `casePtrval` gains `[Inhabited α]`, `IvMaxAlignment` 16 → 8 with
heap addresses shifting, CerbFS refusals; `CerbFuel.*`,
`drive`/`drive_lemFuel`/`fuelExhaustedKill` UNCHANGED, no `.lem` changed);
the pin-bump manifest §0-§3 (LemLib 045dcb0 → 3c88f0d, `Pset`/`Pmap`/
`Fmap` inductive AVL ports, `fmapElements` ascending under the captured
comparator, `lemListFoldr` no longer reduces by `dsimp`/`rfl` — rewrite
through `LemLibTheorems.lemListFoldr_eq`, 55 types get OCaml-rank `Ord`);
the dynamic-addrs investigation §0 (Core-level claim CONFIRMED on both
oracles and Lean; the C-flavoured `malloc(0)`-then-`free` consequence does
NOT reproduce from C; Lean a faithful mirror; MIRROR + TRAY draft 19; R4
written, not decided / DEFERRED [USER 2026-09-03] per the Z1 manifest).
Fix: an erratum line in DECISIONS (34, not 28), or state what the 28
counted.

### H-2 (record accuracy) — the §9 hygiene sentence is wrong both ways

Evidence: `docs/2026-09-03_f1-notes.md` §9: "`outcomesU_done`/
`outcomesU_remove_annot` (Soundness) … are consumerless after the slice;
`outcomesU_of_step` is consumed by Round.lean only". Measured (grep over
`CerberusHeapLang/`, comment lines excluded): `outcomesU_remove_annot` IS
consumed — `Soundness.lean:5194 exact outcomesU_remove_annot M aid ds v (ev0
:: evs) ctl _`, inside `theorem outcomesU_of_step`; `outcomesU_of_step` has
NO code consumer anywhere (Round.lean's only mention is the header comment
at :47; API.lean:85 and Potential.lean:9 are prose). `outcomesU_done`,
`spikeCtx_wf`, `procCtx_wf`, `progA_wpt`, `ctlThread_current_loc` are
consumerless as stated. Fix: correct the sentence; the hygiene target is
the whole `outcomesU_of_step` device (statement over `outcomesU`), which
the API.lean row already classifies as a Round.lean-classification device.

### H-3 (grumpy-professor) — `LoopOutcome` duplicates `DriverSafeCtl`'s conclusion verbatim

Evidence: `Adequacy.lean` — `def DriverSafeCtl` (lines ~1005-1027) and
`private def LoopOutcome` (lines ~1040-1055) carry the same 15-line
two-arm disjunction, differing only by indentation and the
binder-vs-parameter status of `dst acc fl`. Plant B (a different kill
constant in `DriverSafeCtl` only) failed at the seam between the two
copies (`Adequacy.lean:1314:2: Type mismatch … drive_safe_aux …`), not at
the semantics anchor (`loop_zero_exhausts`), which is where Plant B′ (the
same change in `prod_run_safe_procs`'s statement) failed. Not a defect —
the kernel keeps them in step — but one predicate for "the loop's outcome
at one driver state, accumulator and fuel" would carry the induction and
appear once. Suggest: make the outcome predicate the public readout
vocabulary (it is exactly what the walkthrough §2 prints) and define
`DriverSafeCtl` as the ∀-closure over it, or leave as is and document the
duplication as deliberate.

### H-4 (pre-existing prose) — ARCHITECTURE §2 "premises of `cerberusRound_classify` only"

Evidence: `ARCHITECTURE.md:50-52` "(`SeqWF` and the empty-stack control
`ctl.κ = []` are premises of `cerberusRound_classify` only, for its
`value_done` arm)". Measured: `SeqWF` is also a premise of `shipped_done`
(Round.lean:1660) and `outcomesU_done` (Soundness.lean:4588); `ctl.κ = []`
(`hκ`) is a premise of every adequacy export (`engine_adequacy`, the four
projections, `semantic_*`). The sentence is unchanged in this range (no
`SeqWF` in the ARCHITECTURE diff); it is in the paragraph F1 rewrote
around. Fix: "…are not premises of the certification `engine_step_matchU`
(they are premises of `cerberusRound_classify`'s `value_done` arm and of
the adequacy exports' entry control)".

### H-5 (prose) — the R-4 reconciliation says "the same set"

Evidence: `ARCHITECTURE.md:321-323` "'Closed shipped-driver statement'
means exactly these eight (the DECISIONS register's 'nine production
statements' count the generic pipeline theorem `prod_run_eqJ` as well —
the same set)". Eight ≠ nine; the intended reading is "the same eight,
the register also counting `prod_run_eqJ`". Fix: say that.

### Notes (not findings; graded per the brief)

- N-1. The FUEL SCOPE presentation is honest. Re-measured on the pin
  (verbatim, generated Driver.lean): `def drive_nonmemory_steps_aux2 : …
  := drive_nonmemory_steps_aux2_lemFuel 100000000` (:351);
  `new_drive_core_threads` calls `((drive_nonmemory_steps_aux2
  _lemReader_tagDefs)  fmapEmpty  /- NEXT -/ tids)` (:357) — the WRAPPER,
  so the loop budget is fixed at `10^8` regardless of `driver2_lemFuel`'s
  fuel; `driver2_lemFuel (Nat.succ lemFuel)` (:381-384) consumes one unit
  per round and passes `lemFuel` only to the recursive `driver2_lemFuel
  lemFuel` inside `process_core_step2`, whose `Step_done2 cval` arm does
  `nd_update (… prepare_exit …)` and does NOT recurse. Hence a fragment run
  is exactly ONE `driver2` round and `prod_run_safe_procs` at every
  `fuel ≥ 1` is the statement about the shipped `drive`; at `fuel = 0` the
  setup runs and `driver2_lemFuel 0` kills. The worker's reading is
  confirmed. The caveat is disclosed on ARCHITECTURE §6 (MEASURED
  paragraph), README "Closed programs on the shipped pipeline", WALKTHROUGH
  §1.3 and the ProdEntry.lean header; the surfaces that say "at every
  `drive_lemFuel` fuel" without it (README:22, API.lean:54, the
  FibRecExhibit header/docstring) are literally true and one paragraph
  from the caveat. No reword required; an optional one-clause pointer
  ("the fuel bounds the outer `driver2` rounds — ProdEntry header") on
  API.lean:54 would remove the last chance of misreading. `fib_rec_certified`
  "for every `n ≥ 0`, no budget bound" is honest partial correctness: for
  `n ≥ 34` (DERIVED from the C4 audit's `fibRounds 34 = 110729571 > 10^8`)
  the Active arm is vacuous and the theorem says the run is the exhaustion
  kill or Active-with-`fib n`, which is what the driver does.
- N-2. An EXISTENTIAL generalization of the killed arm (`∃ r, … NDkilled
  r`) would not fail any gate (a weaker statement; the proofs still
  elaborate): only the signature-snapshot speedbump and a reader would
  catch it. The tree has the exact constant (measured by `#print
  DriverSafeCtl`), so this is a process note per the brief, not a finding.
- N-3. `hjmp` (jump-only tie): soundness is the kernel's — the 600-line
  `loop_step_frag_same'` proof changed at exactly one line (`rw [hlb] at
  hl` → `obtain ⟨p, hproc, hQd⟩ := hjmp l params cont hl`, the jump arm)
  and elaborates trio-exact, so every non-jump arm of the shipped round is
  proved independent of `current_proc_opt`; the mirror reads `ctl.proc`
  only in `Step.run` (`lookupLabel (M.labelsAt ctl.proc) l`) and pushes it
  in `Step.call`, and `CtlTied.jump` closes the `none` case by `labelsAt
  none = fmapEmpty` (`rfl`). At the `spikeCtx` profile no jump can fire in
  the mirror, so the straight-line exhibits' `DriverSafeCtl` statements
  are non-vacuous facts about a thread state the pipeline never produces
  (disclosed on the new README register row, ARCHITECTURE §6 (ii),
  WALKTHROUGH §1.3).
- N-4. `htd`/`hex` (empty tag definitions/extern) on the projections and
  `semantic_*`: a narrowing relative to the deleted `driveU` lane's `∀ M`,
  matching the shipped round's `fmapEmpty` statement and the production
  driver's `drive fmapEmpty false …`; every client discharges both by
  `rfl`; the README register already states "the demos state footprints at
  `fmapEmpty`". `hwf : SeqWF` dropped: a strict generalization (every
  consumer passed `⟨rfl⟩`). `hcl : th₀.current_loc = M.currentLoc` is the
  PCALL `push_exec_loc` tie already present in the C4 lane; both profiles
  satisfy it by `rfl` (probed: `(spikeThread progA).current_loc =
  spikeCtx.currentLoc := rfl` and the `prodThread`/`prodCtx` instance).
- N-5. Plants C and D fail with `maximum recursion depth has been reached`
  (Lean trying to unify the numerals `10^8` and `10^8 + 1`) — loud, and
  exactly the error class the DriverCollapse header names for budget
  numerals; the guard is the Lean elaborator, not a package check.
- N-6. The DECISIONS gate quote strips `info: CerberusHeapLang/Audit.lean:567:0: `
  from the three sweep lines (the worker's §8 keeps it). Same convention
  as the C3/C4 entries; content identical line for line.

## What was measured (by the brief's items)

### 1. Referents of the restated exports

`#print CerberusHeapLang.DriverSafeCtl` (verbatim, reflowed by Lean):
hypotheses `dst.core_state0.thread_states = [(0, none, ctlThread th₀ e ρ
ctl)]`, `dst.layout_state = σ`, `dst.core_extern = fmapEmpty`,
`dst.core_file = M₀.file`, `LabeledProcs M₀ dst.core_run_state0.labeled`,
`CtlTied M₀ dst.core_run_state0.labeled ctl`; conclusion `(∃ dst', runOne
(drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst = (NDkilled
CerbND.fuelExhaustedKill, dst')) ∨ ∃ v σfin ρfin pfin ℓfin rs' tr ctr, ψ v
σfin ∧ runOne (…) dst = (NDactive (fmapAddBy defaultCompare 0 [Step_done2 v]
acc), { … thread_states := [(0, none, ctlThread th₀ (ofVal (SpikeVal.pure v))
ρfin { κ := [], proc := pfin, execLoc := ℓfin })] …, core_run_state0 := rs',
layout_state := σfin, …, trace := tr, …, dr_step_counter := ctr })`.
Non-semantics constants: `runOne` (the `ND` eliminator, Step.lean:1385,
accepted at C2/C4 for `DriverDoneCtl`), `ctlThread` (thread builder,
moved verbatim from ProdLoop.lean), `LabeledProcs` (moved verbatim),
`CtlTied` (new; a registration tie of the same shape as `LabeledProcs`),
`ofVal`/`SpikeVal.pure` (the value readout). Nothing mirror- or
collapse-shaped; nothing `driveU`-shaped under a new name (the only loop
in any statement is the generated `drive_nonmemory_steps_aux2_lemFuel`).
`MemTriple`/`MemTriple_alloc`/`SemTriple`: `∀ R, P ##ₘ R → ∀ σ, Sat/LaunchCoh
… → ∀ th₀, th₀.current_loc = M.currentLoc → DriverSafeCtl …` (`#print`).
`prod_run_safe_procs` (`#check`): conclusion `CerbND.runND (CerbND.drive_lemFuel
fuel fmapEmpty false (prodFileWith procs e) args) (initial_driver_state sup
(prodFileWith procs e) fs).fst = [(st, [], dst')] ∧ (st = Killed dst'
CerbND.fuelExhaustedKill ∨ ∃ dres, st = Active dres ∧ ψ … ∧ dres.dres_blocked
= false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = "")` — package
vocabulary only in the hypotheses (`prodCtx`/`prodRS`/`prodThread`/
`prodCtl`/`prodMem₀`/`prodFileWith`, the C4 builders) and `DriverSafeCtl`/
`LabeledProcs`, which the client `fib_rec_certified` discharges
(`engine_adequacy` at `prodMem₀`, `frCtx_labeledProcs`). `engine_adequacy`
(`#check`): the C2-era premises with `hwf` gone and `htd`/`hex`/`hcl`
added; conclusion `DriverSafeCtl M th₀ e₀ (ev00 :: evs0) ctl σ₀ ψ`.
`#print axioms` on all 14 new pins, `engine_adequacy`, `fib_rec_certified`,
`project_triple_pure`, `semantic_frame`, `call_smoke_engine`,
`exhibitA_engine`, `diverge_total_unprovable`, `drive_after_setup_with`:
`[propext, Classical.choice, Quot.sound]` each; `runND_killed`: "does not
depend on any axioms".

### 2. `DriverSafeCtl`'s two arms, and the closed `∀ fuel`

Killed arm: `loop_zero_exhausts` is `rw [CerbND.drive_nonmemory_steps_aux2_lemFuel_zero]; rfl`
against `theorem drive_nonmemory_steps_aux2_lemFuel_zero … = ND (fun st =>
(NDkilled fuelExhaustedKill, st)) := rfl` (CerbND.lean:322-326); the
generated fuel-0 arm is `| 0 => (fun _ => ND (fun st => (NDkilled (Error0
CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg), st)))` (Driver.lean:347)
and `def fuelExhaustedKill {err : Type} : kill_reason err :=` … (CerbND.lean:80).
Fuel exactly 1 at a done configuration: the `Nat.succ lemFuel` arm records
`[Step_done2 v]` (`find_can_advance` → `none`) and recurses at `lemFuel = 0`
on `[]`, whose fuel-0 arm kills BEFORE inspecting the list — so the drain
needs one more unit and PROGRAM-DONE needs fuel ≥ 2 (`loop_step_done` at
`succ (succ fl)`, `loop_step_done_exhaust` at `succ 0`): the total lane's
`k + 2` is exact for the drain, as the record says. Program-done arm: ties
to the driver's own done state — see the Verdict paragraph; `driver2_done`
(pinned, byte-identical) consumes exactly that record shape into
`prepare_exit`, and `finalize_done` reads the value off it. Closed form:
N-1 above; `runND_killed` mirrors `runNDFuel`'s `| (NDkilled reason, st')
=> [(Killed st' reason, [], st')]` (CerbND.lean:117-118) at `runND =
runNDFuel CerbFuel.driverFuel` (`driverFuel_succ` unfolds one unit).

### 3. Deletions and the coverage claims

REMOVED 73 (DERIVED; list in §Census). Load-bearing content gone without a
twin: R-2 (the six seeded/any-memory total equations) beyond the disclosed
`tree_rotate_certified_total`. ARCHITECTURE §7's ledger and the
capability manifest carry no row the deletions falsify: the manifest
(regenerated by the gate, "no drift") lists rule → client-module rows only;
no `_total`/`launch_smoke`/`certified_registration`/`driveU`/`PROVISIONAL`
string in `docs/CAPABILITY_MANIFEST.md`. The Audit.lean pin list: 13 names
removed, 14 added (each present in the post snapshot and in the list —
checked by name), `loop_step_frag_same'`/`loop_step_frag'` pinned (the
record's "the pinned `loop_step_frag_same`/`loop_step_frag` are their
instances" is consistent: both remain pinned too). `git diff --stat` of the
Audit.lean pin set: 373 distinct `` ``CerberusHeapLang.* `` names (DERIVED
grep) = the gate's 373.

### 4. `hwf` dropped, `htd`/`hex` added; census; snapshot

N-4 above. Census re-derived by script (entry = kind + name + printed
type) from the two committed snapshot files: pre 3017, post 2971; ADDED
27, REMOVED 73, CHANGED 26, UNCHANGED 2918 — the three name lists are
IDENTICAL to the record §4's (every name checked). The nine production
statements (`exhibitA_prod`, `prod_run_eqJ`, `fib_certified_production`,
`counter_loop_certified_production`, `list_reverse_certified_production`,
`dispose_list_certified_production`, `region_loop_certified_production`,
`malloc_list_certified_production`, `fib_rec_certified_production`) and
`prod_run_eqJ_procs`: source text (statement through `:=`) at `328be1a`
vs `2bbfd70` IDENTICAL (10/15/15/19/19/21/18/22/14/17 lines); likewise
`loop_step_frag` (31 lines), `loop_step_frag_same` (24), `driver2_done`
(12), `finalize_done` (13), `drive_after_setup` (7), `drive_after_setup_with`
(8; its proof is now the one-line `driverFuel` instance),
`wpt_driver_cps` (18), `wpt_driver_done` (22), `diverge_total_unprovable`
(11). Every `wps_*`/`wpt_*` rule and every collapse is absent from the
CHANGED list. Snapshot regenerated at HEAD (`lake env lean
scripts/signature_snapshot.lean`, 13.3 s): 29041 lines, `cmp` against
`docs/2026-09-03_f1-signatures-post.txt` BYTE-IDENTICAL.

### 5. `CtlTied` / `loop_step_frag'`

N-3 above. The two pinned C2 statements are textually unchanged and are
`loop_step_frag_same' … (fun _ _ _ _ => ⟨p, hproc, by rw [hlb]; exact hQd⟩) …`
resp. `loop_step_frag' … (fun _ _ _ _ => ⟨p, by rw [hproc, hp], by rw [hlb];
exact hQd⟩) …`. `drive_safe_aux` carries `CtlTied` through PCALL (callee
tie from `LabeledProcs` at `hfl`, the pushed frame's tie from `htied.1`)
and RETURN (the popped procedure's tie from `htied.2` at the frame, the
rest from `htied.2`), with `rs'.labeled = dst.core_run_state0.labeled` from
the round lemma — read in the diff, kernel-checked.

### 6. Docs

PROVISIONAL: `git grep -l PROVISIONAL` outside dated records and
DECISIONS → 1 file, `CLAUDE.md:101` (the rule sentence). `driveU` on
shop-window surfaces: 30 hits, every one a sentence saying it was deleted
(README ×5, ARCHITECTURE ×3, WALKTHROUGH ×3, API ×1, headers ×11, Audit
×6, DivergeExhibit ×1). ARCHITECTURE as a core document: §1/§2/§4/§5/§6/§7
read in full; accurate on the lanes, the fuel arms, the MEASURED caveat,
decision points (i)/(ii) of §6 and §7 Goal 1's "does NOT include"; H-4/H-5
are the two prose slips found; no stale history in the normative sections
beyond the dated "since the fuel-lane restatement" pointers. R-4 phrasing
reconciled (H-5's wording aside). The "one content loss": R-2.

### 7. Plants (verbatim; every build `scripts/capped ~/.elan/bin/lake build`, `CERB_MEM_MAX=40G`; `git status --short` after every revert = `?? .audit-scratch/` only)

- **Plant A** — `loopOutcome_step`'s proof body (private, in
  `DriverSafeCtl`'s cone) replaced by `sorry`. Loud at the trust base:
  ```
  warning: CerberusHeapLang/Adequacy.lean:1041:16: declaration uses `sorry`
  error: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang export pin FAILED: CerberusHeapLang.exhibitA_engine depends on axioms [Classical.choice,
   Quot.sound,
   propext,
   sorryAx], expected EXACTLY [Classical.choice, Quot.sound, propext]
  error: Lean exited with code 1
  Some required targets logged failures:
  - CerberusHeapLang.Audit
  error: build failed
  EXIT=1
  ```
  Revert: `export pins: 373 trio-exact` / `Build completed successfully (456 jobs).` / `EXIT=0`.
- **Plant B** — `DriverSafeCtl`'s killed arm `NDkilled CerbND.fuelExhaustedKill`
  → `NDkilled (kill_reason.Error0 CerbFuel.fuelExhaustedLoc "plant")`
  (statement only; `LoopOutcome` untouched). Loud:
  ```
  error: CerberusHeapLang/Adequacy.lean:1314:2: Type mismatch
    drive_safe_aux htd hex hPf hcl e₀ (ev00 :: evs0) ctl dst.layout_state ψ hNS hRES fl e₀ (ev00 :: evs0) ctl dst acc
  error: CerberusHeapLang/Adequacy.lean:1383:2: Type mismatch
  error: Lean exited with code 1
  Some required targets logged failures:
  - CerberusHeapLang.Adequacy
  error: build failed
  EXIT=1
  ```
  (the `engine_adequacy`/`engine_adequacy_alloc` closing `exact`s; see
  H-3 for why the failure lands here). Revert: 373 / `Build completed
  successfully (456 jobs).` / `EXIT=0`. (A first application of this plant
  aborted at the edit script's own occurrence-count assertion — `count=1`,
  the two copies differ in indentation — and made no change; re-applied
  with the corrected count.)
- **Plant B′** — the same constant change in `prod_run_safe_procs`'s
  STATEMENT (`st = nd_status.Killed dst' CerbND.fuelExhaustedKill`). Loud
  at both `Or.inl rfl` sites, i.e. at the semantics anchor
  (`driver2_lemFuel_zero` / the loop's kill reason):
  ```
  error: CerberusHeapLang/ProdEntry.lean:794:13: Application type mismatch: The argument
    rfl
  has type
    ?m.103 = ?m.103
  but is expected to have type
  error: CerberusHeapLang/ProdEntry.lean:803:15: Application type mismatch: The argument
    rfl
  has type
    ?m.246 = ?m.246
  error: Lean exited with code 1
  Some required targets logged failures:
  - CerberusHeapLang.ProdEntry
  error: build failed
  EXIT=1
  ```
  Revert: 373 / `Build completed successfully (456 jobs).` / `EXIT=0`.
- **Plant C** — `drive_after_setup_with`'s proof `drive_after_setup_with_lemFuel
  CerbFuel.driverFuel …` → `(CerbFuel.driverFuel + 1)` (breaking the
  `drive_wrapper_defeq` use). Loud:
  ```
  error: CerberusHeapLang/ProdEntry.lean:693:0: maximum recursion depth has been reached
  use `set_option maxRecDepth <num>` to increase limit
  use `set_option diagnostics true` to get diagnostic information
  error: CerberusHeapLang/ProdEntry.lean:716:8: (kernel) unknown constant 'CerberusHeapLang.drive_after_setup_with'
  error: Lean exited with code 1
  Some required targets logged failures:
  - CerberusHeapLang.ProdEntry
  error: build failed
  EXIT=1
  ```
  Revert: 373 / `Build completed successfully (456 jobs).` / `EXIT=0`.
- **Plant D** — `prod_run_safe_procs`'s instantiation of `hsafe` at
  `CerbFuel.driverFuel` → `(CerbFuel.driverFuel + 1)` (is the loop budget
  the proof feeds `driver2_killed`/`driver2_done` really the shipped
  `10^8`?). Loud:
  ```
  error: CerberusHeapLang/ProdEntry.lean:801:29: maximum recursion depth has been reached
  use `set_option maxRecDepth <num>` to increase limit
  use `set_option diagnostics true` to get diagnostic information
  error: CerberusHeapLang/ProdEntry.lean:808:14: maximum recursion depth has been reached
  use `set_option maxRecDepth <num>` to increase limit
  use `set_option diagnostics true` to get diagnostic information
  error: Lean exited with code 1
  Some required targets logged failures:
  - CerberusHeapLang.ProdEntry
  error: build failed
  EXIT=1
  ```
  Revert: 373 / `Build completed successfully (456 jobs).` / `EXIT=0`.

Not planted (judged by reading instead): a `κfin` existential in the
done arm — `driver2_done` requires `stack0 = Stack_empty` through
`step_ctx_done`'s `hstack`, so a general stack would fail at
`prod_run_safe_procs`'s `driver2_done … rfl`.

### 8. Records and the gate

`CERB_MEM_MAX=40G ./scripts/test_unit.sh` from the audit copy root
(the primed `.lake` made the build a cache replay; `time` line verbatim:
`./scripts/test_unit.sh  7.60s user 0.81s system 101% cpu 8.323 total`),
verbatim verdict lines (log lines 1-3, 3072-3084;
the three sweep lines carry the `info:` prefix in the log):

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang export pins: 373 trio-exact
info: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (3396 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:567:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (5161 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (456 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
EXIT=0
```

(`EXIT=0` is the auditor's `echo "EXIT=$?"` after the runner.) Compared
with the DECISIONS F1 entry's quote: identical line for line after the
register's prefix strip (N-6); counts 373 / 3396 / 5161 / 456 identical.
`grep -ci uncapped` = 0, `grep -c "uses sorry"` = 0 over the log. Package
linter warnings (DERIVED from the log): 62 — Potential 50, Round 3,
EnvLaws 2, Heap 2, Rules 2, ProdLoopExhibit 1 (`:738 ra`, file untouched
in the range), StructExhibit 1 (`:190 w`, blame `2f15f98b 2026-09-01`),
TreeRotExhibit 1 (`:1154 sbty`, blame `4e86c081 2026-09-01`) — zero new
warnings; the record's 66 → 62 is consistent (four removed with deleted
code). DECISIONS: the last eight entries are in event order, all dated
2026-09-03; the F1 entry's names, counts (3017 → 2971, 27/73/26, 372 →
373, "1 files") and gate tail check against the tree; the
"cerberus-lean moved" entry's manifest claims check against the cited
docs except the commit count (H-1). The record's cited engine lines
re-read on the pin: Driver.lean:346 (`def  drive_nonmemory_steps_aux2_lemFuel`),
:351 (the `100000000` wrapper), :355-357 (`new_drive_core_threads` … the
wrapper call), :381-384 (`driver2_lemFuel`), :530 (`current_proc_opt :=
(some  main_sym)`); CerbND.lean:322-326, :328-332, :396, :467.

### 9. Grumpy-professor read of the restated Lean

Adequacy.lean: the partial lane now reads as one induction
(`drive_safe_aux`) over one round lemma with three value/annot helpers;
clear, and the header's four-layer summary matches the code. Dead code
left behind: `spikeCtx_wf`/`procCtx_wf` (Step.lean:3381/3383),
`outcomesU_done` (Soundness.lean:4588), `progA_wpt` (Exhibit.lean),
`ctlThread_current_loc` (a `@[simp]` lemma with no consumer) — all
consumerless by grep; `outcomesU_of_step` (the whole device) is
consumerless as well (H-2). Over-elaboration: H-3's duplicated conclusion.
TotalAdequacy.lean is now a 90-line readout-vocabulary module with a
HISTORY paragraph — fine, though a module whose only content is
`readoutPost` and three plumbing lemmas could live in ProdLoop.lean (not
required). DriverCollapse.lean: the four exhaustion/kill lemmas are short
and each is one unfolding of the generated code. ProdEntry.lean: the
fuel-generic setup collapse is the C4 proof with `drive` → `drive_lemFuel
fuel`, and the `driverFuel` instance is the one-liner it should be (H-2 of
the C4 audit, done). Exhibits: mechanical `(… th₀ rfl).mono ?_` rewrites;
nothing to fault.

## Census (DERIVED; pre = `docs/2026-09-03_c4-signatures-post.txt`, post = `docs/2026-09-03_f1-signatures-post.txt`)

pre 3017, post 2971; ADDED 27 = `CtlTied CtlTied.entry CtlTied.jump
CtlTied.noproc DriverSafeCtl DriverSafeCtl.mono MemTriple MemTriple_alloc
MemTriple_alloc_of_MemTriple ProvenTriple SemTriple SemTriple_iff_Mem
call_smoke_engine dg_loop_exhausts drive_after_setup_with_killed
drive_after_setup_with_lemFuel driver2_killed engine_adequacy
engine_adequacy_alloc loop_step_done_exhaust loop_step_frag'
loop_step_frag_same' loop_zero_exhausts prod_run_safe_procs runND_killed
semantic_frame semantic_triple_sound`; REMOVED 73 = the 31 `DriveResult*`
entries + `DriveDoneAt DriveOk Frag.stateInert_step MemTripleU
MemTripleU_alloc MemTripleU_alloc_of_MemTripleU ProvenTripleU SemTripleU
SemTripleU_iff_Mem StateInertLabels alloc_create_launch_smoke
call_smoke_driveU counter_loop_certified_registration dg_driveU_more
dispose_list_certified_total driveU driveU_succ driveU_value_pure
drive_classifyU drive_classifyU_aux engine_adequacyU engine_adequacyU_alloc
exhibitA_total fibBody_stateInert fibProg_stateInert fib_certified_total
free_launch_smoke kill_launch_smoke list_reverse_certified_total
malloc_list_certified_total outcomesU_of_call outcomesU_of_ret
region_loop_certified_total semantic_frameU semantic_triple_soundU
stateInert stateInert.eq_def stepOutcomes stepOutcomes_thread
tree_rotate_certified_total wpt_drive_aux wpt_engine_boundU
wpt_engine_boundU_alloc`; CHANGED 26 = `array_sum_certified case_certified
counter_loop_certified counter_loop_certified_irrelevant_binding
exhibitA_engine exhibitA_semantic exhibitB_engine exhibitB_semantic
exhibitC_engine exhibitC_semantic fib_certified fib_rec_certified
list_reverse_certified list_reverse_demo project_triple
project_triple_alloc project_triple_pure project_triple_pure_alloc provenA
provenB provenC struct_create_store_adequacy
struct_create_store_adequacy_prodMem₀ struct_update_certified
tree_rotate_certified wseq_certified`; UNCHANGED 2918.

## What was NOT checked

- The 600-line body of `loop_step_frag_same'` beyond its one changed line,
  and `loop_step_frag'`'s body beyond the diff hunks (soundness rests on
  the kernel; the C2 audit read the originals).
- The C4-era `drive_after_setup_with_lemFuel` prefix chain internals
  (`runOne_bind_active (by rfl)` steps) — the statement's `driverFuel`
  instance is byte-identical to the pinned C4 theorem; only the diff was
  read.
- No engine execution, no `fibRounds` re-measurement (the C4 audit's
  numbers are used as DERIVED inputs in N-1).
- README and WALKTHROUGH were read by grep and in the sections the brief
  names (the claim, the partial lane, "Closed programs", the exhibits
  table, the divergence register, the trust diagram; WALKTHROUGH §1.1-§1.3)
  plus a script check of every fenced quote's verbatim status — not
  sentence by sentence in full.
- The internal claims of the three cerberus-lean docs (only the DECISIONS
  entry's relay of them was checked); `refinedc/dev`; anything outside the
  range.
- The other 32 fenced `lean` blocks in WALKTHROUGH (38 in all) beyond the
  six §1.1/§2 definitions checked for verbatim status.
