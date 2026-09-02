# Consumer review of the cerberus-lean FUEL arc design note (R2, Option C)

Reviewed: `worktrees/cerberus-lean-arc/fuel/lean_frontend/docs/2026-09-02_fuel-arc-design.md`
at `ae9a8784f`, against our request
`docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`.
Reviewer: refined-cerberus orchestrator, for the cerberus-heaplang consumer.
Verdict: **ACCEPT with three consumer requirements and one wording
suggestion.** Answers to the note's three open consumer questions are in §3.

## 1. What the design gives us, checked against the request

- Every ND-typed fueled worker's fuel-zero arm becomes the plain value
  `NDkilled (Error0 CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg)`
  with no opaque wrapper around the monadic value, and `_zero` lemmas
  hold by `rfl` at the generated signatures. That is exactly request item
  1 (a kernel-recognisable outcome) and item 2 (loudness moved to the
  harness classification). The note corrects our count (nine workers,
  not six — the three memory-model workers lifted by `liftND`) and our
  `'err` type (`driver_error`); both corrections are right.
- The kill propagates unchanged through `nd_bind` and `liftAction`, so a
  worker exhausting beneath the quantified one surfaces as the SAME
  value: one left disjunct covers every fuel in a run. This is what makes
  the ∀-fuel induction close.
- No shared `.lem` type changes; the OCaml text is untouched and the
  fork-drift gate is the byte-identity proof. Under the operator's
  ordering rule (trust surface stable, "obviously right" w.r.t. upstream)
  this is the right call over Option B, and we withdraw our request's
  suggestion of a new `kill_reason` constructor.

## 2. The soundness argument — one suggestion on how to state it

The note argues unforgeability from "a forged `error(…)` yields a
SYNTACTICALLY DIFFERENT term" and concedes the kernel cannot prove the
sentinel unequal to a genuine `Error0` kill. Both true; but the stronger
and exact justification is PARAMETRICITY IN THE OPAQUE: `fuelExhaustedLoc`
is an `opaque` with no equations, so every theorem proved about runs is
uniform in its interpretation. A proved theorem of the shape
"every outcome is `Killed _ fuelExhaustedKill` or good" therefore holds
under the reading in which `fuelExhaustedLoc` is a location no model
term denotes — which is precisely the intended meaning — and for a
program that genuinely kills (forged message or not) the left disjunct
is unprovable (the opaque cannot be shown equal to a model-produced
location) and the right one false, so the theorem is unprovable: no
false theorem. We recommend the VALIDATION.md paragraph say this
("every proof is uniform in the opaque atom; the sentinel is a fresh
location for every provable statement") rather than the syntactic
phrasing, and record that no distinctness lemma is needed BECAUSE of
this, not despite it. We confirm our induction consumes no distinctness
fact (§3(ii)).

## 3. Answers to the note's open consumer questions

(i) **Q3, the runner leaf — ACK.** Our theorems are stated over `runND`;
the runner's own fuel (`ndDefaultFuel`, moving to `driverFuel`) must
exhaust to the same kill or the ∀-fuel statement is vacuous past that
depth. Landing it after `prune/relsem` is fine; we have no statement
against the `[]` leaf.

(ii) **The opaque-atom design — ACK**, including that no distinctness-
from-genuine-`Error` lemma ships. Our induction: fuel-zero arm → left
disjunct by the `_zero` lemma; `Nat.succ` arm → one engine round
(`loop_step_frag`-style) → postcondition or the inductive hypothesis;
an exhausted worker beneath → the same kill → left disjunct. No
distinctness, no decidability, no `DecidableEq` needed.

(iii) **The exemplar's `post` shape.** `∃ r, o.1 = Active r ∧ post r o.2.2`
matches how we read the final state (`o.2.2 : driver_state`, of which
we project `layout_state` and read the value with `finalize`). But see
requirement R1 below: our statements are over `drive`, not `driver2`.

## 4. Consumer requirements (before we can delete `driveU`)

- **R1 — a fuel-parametric `drive`.** Our production statements are over
  the shipped `runND (drive tds conc file args) dst₀`, which returns
  `driver_result` through `finalize`; `drive` calls `driver2` through the
  FIXED wrapper, so the fuel is not a parameter at the level we state.
  We need `drive_lemFuel (fuel) …` (or `drive_at`) with
  `drive = drive_lemFuel CerbFuel.driverFuel` by `rfl`, so the ∀-fuel
  theorem is over the shipped pipeline end to end (setup, driver loop,
  `finalize`), not over `driver2` plus our own call to `finalize`. If
  `drive` is emitted non-recursively from lem, a `{lean}`-scoped fuel
  parameterisation of the wrapper it calls is enough; the exemplar (§6)
  should be stated over `drive_lemFuel`.
- **R2 — `_zero` lemmas and wrapper `rfl`s shipped in a hand-written
  seam we can import** (`CerbND`, as proposed) and pinned by a gate on
  their side (a renamed generated binder would break them; a red build
  there is better than a red build here).
- **R3 — the budget change (10^8) recorded as a consumer-visible side
  condition**: our `k + 2 ≤ lemDefaultFuel` premises and any
  `driver2 = driver2_lemFuel lemDefaultFuel` `rfl` become `driverFuel`
  at our re-pin. Weaker, hence fine; we only ask that `driverFuel` be
  the citable name (it is) and that the wrapper `rfl`s be among the
  shipped lemmas (they are, §1.2).

## 5. Other points

- `liftAction`'s fuel-zero arm discarding a genuine kill it was lifting
  and reporting exhaustion instead: acceptable (conservative — a run that
  exhausts is not claimed to be anything else).
- Pure-return workers keep the panicking sentinel (`hack` among them,
  which `finalize` uses): acceptable for us — `finalize` runs at fixed
  budget on a terminal state and our statements evaluate it on concrete
  states; but we note it is the one remaining opaque leaf inside a
  shipped-pipeline export's evaluation, and a `finalize` that never
  panics on a terminal state would close it.
- The `sorry` closure with the real `CerbMem.stringFromMemValue` printer
  (not the placeholder stub) plus a comment-stripped `sorry`-token source
  scan: right choice; it answers our "Also observed" item fully.
- The erratum to the C1 records (vacuous apply-condition measurement):
  noted; it does not affect us.

## 6. What we will do when it lands

Re-pin; delete `driveU` and every PROVISIONAL label; restate the
partial-correctness exports as
`∀ fuel, ∀ o ∈ runND (drive_lemFuel fuel fmapEmpty false file args) dst₀,
 (∃ st, o.1 = Killed st CerbND.fuelExhaustedKill) ∨ (∃ r, o.1 = Active r ∧ post r o.2.2)`
with `dst₀ := (initial_driver_state sup file fs).1`; keep the total-lane
equations as they are with `driverFuel` in the side condition. That
closes the first of the demo's three acceptance goals (DECISIONS.md,
[USER 2026-09-02]).

## 7. Post-review note from the cerberus-lean team (relayed 2026-09-02) — accepted

> `drive` runs the driver loop twice (once for globals via `driver_globals`,
> once for `main`), and `drive_lemFuel fuel` threads the parameter into the
> main call only, leaving globals at the fixed budget — which keeps setup
> fuel-independent for their induction; globals exhaustion still yields the
> same kill. A second mirror fuelling both is recorded as available.

Consumer position: the single-parameter form is the one we want. Our
∀-fuel induction is over the main loop; a fuel-independent setup phase is
exactly what keeps the initial driver state (`dst₀`, after globals) a
fixed term in the statement. A globals-phase exhaustion at the fixed
budget is the same kill and falls under the left disjunct, so the
theorem's shape is unchanged; that it is then indistinguishable from a
main-phase exhaustion is acceptable (both are exhaustion, neither is a
claim about the program). Our present files have no globals; when
compiled Core with globals arrives, globals initialisation is a
terminating computation whose facts belong to the total lane at the
fixed budget, so no second fuel parameter is foreseen. No change
requested.
