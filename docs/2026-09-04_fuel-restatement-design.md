# The fuel restatement (slice F2) — consumer-side design note

Status: DESIGN, for operator discussion before any brief. Author: the
orchestrator [AGENT], 2026-09-04. Trigger: the lem-lean/cerberus-lean
fuel-parameter arc (`worktrees/lem-lean-arc/fuel-parameter/doc/lean-backend/
2026-09-03_fuel-parameter-design.md` R1, record `2026-09-04_fuel-parameter-record.md`;
our consumer review `docs/2026-09-04_review-of-fuel-parameter-design.md`).
Rulings: [USER 2026-09-03] fuel is a defect of the semantics, fixed
upstream as a quantifiable position; [USER 2026-09-04] the demo's feature
set is closed — F2 is one of the three pin-blocked slices (DECISIONS
"THE DEMO'S SCOPE, RESTATED"). Measurements below are `grep` tallies on
main `0534f9a` (DERIVED).

## 1. What arrives from upstream (as designed; verify at the pin)

- `class LemFuel where fuel : Nat` (LemLib). Every fuel'd generated
  function `f` becomes `def f [LemFuel] : T := f_lemFuel LemFuel.fuel`;
  every definition that transitively reaches one takes `[LemFuel]`
  (370 in the cerberus dry run). Call sites are textually unchanged.
- Entry points: `drive`, `runND`, `driver2`, `drive_nonmemory_steps_aux2`,
  `nd_bind`, the pexpr evaluators (`step_eval_pexpr`, `eval_pexpr_aux2`,
  `full_eval_pexpr`) — all `[LemFuel]`. `@f ⟨n⟩ = f_lemFuel n` by `rfl`.
- DELETED: `CerbFuel.driverFuel`, `CerbND.ndDefaultFuel`, LemLib's
  `lemDefaultFuel`, the nine fixed-budget `rfl` wrappers
  (`drive_wrapper_defeq` restated as `@drive ⟨n⟩ = drive_lemFuel n`), the
  numeric `declare {lean} fuel val f = N` form. KEPT: `fuelExhaustedKill`,
  `CerbFuel.fuelExhaustedLoc`, the `_zero` lemmas (now GENERATED for all 67
  fuel'd functions). The CLI's `--fuel N` (default 10^8) is the only
  numeral left, in the binary.
- Every fuel'd call starts from the FULL ambient (not the caller's
  remaining counter) — decisive for us (§3).
- NOT arriving: fuel monotonicity (their record §5); the absorbing-or-
  absent classification of exhaustion on the execution path is our
  review's requirement §2 — its status at the pin is the F2 brief's
  first measurement (§5, risk 1).

## 2. Our inventory (DERIVED, main 0534f9a)

Fuel constants in statements/proofs — `lemDefaultFuel` 29 files / ~440
occurrences (Round 133, Soundness 112, DriverCollapse 38, Adequacy 31,
EvalClass 16, MallocListExhibit 16, ProdLoopExhibit 17, ProdLoop 14,
FibRecExhibit 13, ListRevExhibit 11, TreeRotExhibit 11, DisposeExhibit 10,
the rest ≤ 6); `CerbFuel.driverFuel` 13 files / 58 occurrences (ProdEntry
18, DriverCollapse 13, Round 5, ProdLoopExhibit 4, FibRecExhibit 4,
Adequacy 3, EvenOddExhibit 3, …).

Statement-level sites (the ones whose TEXT changes):
- the static potential premises `hpot : pot e ≤ lemDefaultFuel`,
  `hQpot : … pot cont ≤ lemDefaultFuel` on every adequacy theorem
  (`project_triple`, `project_triple_pure`, the engine adequacies,
  `FragProcs`'s body bound; ARCHITECTURE §4 "the static fuel premise");
- the closed statements' budget premise `hfl : k + 2 ≤ CerbFuel.driverFuel`
  (`prod_run_eqJ` ProdEntry.lean:407, `prod_run_eqJ_procs` :723) and the
  nine production statements' `hfuel : <rounds n> ≤ CerbFuel.driverFuel`
  (ProdLoopExhibit.lean:77/:623, RegionLoopExhibit.lean:636,
  MallocListExhibit.lean:1656, FibRecExhibit.lean:866, EvenOddExhibit.lean:723,
  + exhibitA/dispose/list_reverse through `hfl`);
- the closed PARTIAL forms `prod_run_safe_procs … (fuel : Nat)`
  (ProdEntry.lean:768–775) and the exhibits' `*_certified` closed forms
  over `drive_lemFuel fuel` (outer fuel only — KOI A2).
Loop-level statements `DriverDoneCtl`/`DriverSafeCtl` (ProdLoop.lean:456–
464, Adequacy.lean:932) already quantify the INNER loop's fuel `fl` at the
worker level (`drive_nonmemory_steps_aux2_lemFuel fl`, `k + 2 ≤ fl`):
their TEXT does not change.

Binder footprint: every definition of ours that mentions an engine
function reaching fuel gains `[LemFuel]` — the mirror `Step` (74 sites),
`Round` (353), `Soundness` (192), `Heap` (85), `Rules` (72), `Wps`/`Wpt`
(57/52), `DriverCollapse` (188), `ProdEntry` (60), `Adequacy` (18),
`EvalClass` (24), `Audit` (19), every exhibit. Expect the census of F2 to
be CHANGED ≈ the whole snapshot (a binder added to nearly every public
statement), REMOVED = the shipped-constant wrappers we restate as
corollaries, ADDED = the corollaries.

## 3. Target statement shapes

Thread level (the Reynolds/O'Hearn triple's semantics, ARCHITECTURE §4):
```
theorem project_triple_pure [LemFuel] … (hpot : pot e ≤ LemFuel.fuel)
  (hQpot : ∀ l params cont, lookupLabel … = some (params, cont) → pot cont ≤ LemFuel.fuel) …
```
— one hypothesis variable where two constants were. Because every
fuel'd call starts from the full ambient, the PER-EXPRESSION potential
bound is exactly right: `pot e` bounds the evaluator's depth at each
evaluation independently; no sum over the run is needed (our review §1.2).

Loop level: unchanged text (`DriverDoneCtl`/`DriverSafeCtl` over the
worker at explicit `fl`); their consumers instantiate `fl := LemFuel.fuel`.

Closed total (the nine production statements), the pattern:
```
theorem fib_rec_certified_production [LemFuel] (hn : 0 ≤ n)
    (hpot … as today, now ≤ LemFuel.fuel)               -- if the statement carries one
    (hfuel : fibRounds n.toNat + 4 ≤ LemFuel.fuel) (fs) (args) :
    ∃ dres dst', CerbND.runND (drive fmapEmpty false (prodFileWith …) args)
        ((initial_driver_state sup (prodFileWith …) fs).1) = [(Active dres, [], dst')] ∧ …
```
with `drive`/`runND` reading the ambient. One ambient bounds both loops
and the evaluators; the outer loop needs ≥ 1 round, implied by `k + 2 ≤
fuel`. The SHIPPED corollary, per statement:
```
theorem fib_rec_certified_production_shipped (hn) (hn33 : n.toNat ≤ 33) … :
    letI : LemFuel := ⟨100000000⟩; ∃ dres dst', … := fib_rec_certified_production hn (by …) …
```
— the numeral appears ONLY in the corollary that claims to be about the
shipped binary, discharged by `omega`/the closed form (`fibRounds_closed`),
never by `decide` on 10^8 (heartbeat hazard).

Closed partial (`prod_run_safe_procs`, the exhibits' `*_certified`):
```
theorem prod_run_safe_procs [LemFuel] … :
    ∃ st dst', runND (drive …) … = [(st, [], dst')] ∧
      (st = Killed dst' fuelExhaustedKill ∨ (∃ dres, st = Active dres ∧ post dres))
```
— now genuinely over BOTH loops' fuel (KOI A2 closes) — PROVIDED the
evaluators' exhaustion is a kill, not a default (§5 risk 1). If at the pin
an evaluator's `_zero` sentinel is an opaque/default payload, the honest
form is `∀ [LemFuel], pot e ≤ LemFuel.fuel → …` (exhaustion below the
static potential is excluded by hypothesis; above it only the loops can
exhaust, and they kill). State which form landed, in the record and in
ARCHITECTURE §4.

Docs: ARCHITECTURE §4 states the outcome-list reading as the meaning
(KOI B5) and the two-loop/one-ambient picture; the "static fuel premise"
paragraph becomes "the potential premise against the quantified fuel".

## 4. Slice plan (one change at a time)

Prerequisite: the re-pin to a cerberus-lean pin that carries the fuel
half (their sequencing: after Z2's fix phase; the LemLib representation
re-pin lands FIRST as its own slice per the scout plan — if both arrive in
one pin, still two slices: representation first, fuel second, each with
its census).

F2 commits: (1) mechanical binder propagation — every module compiles
with `[LemFuel]` where the pin forces it, constants replaced by
`LemFuel.fuel`, proofs re-cut where `rfl` at a numeral was used (expect
the `drive_wrapper_defeq` consumers and `drive_after_setup*`); FAST gate.
(2) The statement restatement proper: premises to `≤ LemFuel.fuel`, the
closed forms as §3, the shipped corollaries, `_zero` lemmas consumed from
the pin (delete any hand-written duplicates); pins re-measured trio-exact
(the instance binder is a Prop-free structure, so no axiom change
expected); FAST gate. (3) Docs (ARCHITECTURE §3/§4/§6, README trust
paragraph, WALKTHROUGH, CLAIMS kinds) + snapshot + record; FULL gate.
Gate addition: a speedbump grep — no `instance : LemFuel` in the package
outside a `letI` inside a `*_shipped` corollary (the same hazard their
gate guards).

Census discipline: pre = the re-pin's post snapshot; post `…_f2-signatures-post.txt`;
classify CHANGED into "binder only" (mechanical, normalizer-verified like
C3's census) vs "premise text changed" (the `≤ LemFuel.fuel` sites, listed)
vs "shape changed" (the closed partial forms). Range audit; merge ask.

Size: M–L, mostly mechanical; 2–3 worker-days if risk 1 is clear.

## 5. Risks and their measurements (the F2 brief's first hour)

1. **Exhaustion on the execution path** (our review §2): at the pin,
   classify every fuel'd function reachable from `drive` as (A) data-
   measure structural / (B) absorbing typed exhaustion / (C) unreachable.
   If any (D) "opaque default" remains on the path, the closed partial
   forms take the `pot e ≤ LemFuel.fuel` hypothesis (§3) and KOI A2 stays
   open with the reason; write the request.
2. **Instance-argument hygiene**: two instance binders in most statements
   (`[SpikeGS …]` and `[LemFuel]`); `letI` vs section `variable [LemFuel]`
   — use explicit binders in statements, never a file-level `instance`.
3. **`rfl` at closed fuels**: `(⟨n⟩ : LemFuel).fuel = n` reduces by iota;
   `@drive ⟨n⟩` unfolds to `drive_lemFuel n` by `rfl` (their wrapper
   equation); collect_saves/registration `rfl`s are independent of fuel.
   Nothing here needs `decide` on large numerals.
4. **Perf**: none expected from the binder (their §7); our build cost is
   dominated by Round/Soundness re-elaboration — one full rebuild.
5. **Coupling with the shared-library question** (Lane C item 6): if the
   coupling layer is extracted, F2 lands in the library first and the demo
   consumes it — sequence F2 before or after the extraction, not across it.

## 6. Provenance

[AGENT] (orchestrator): the inventory, the shapes, the plan, the risks.
[USER 2026-09-03/04]: the rulings cited. Nothing built; for discussion.
