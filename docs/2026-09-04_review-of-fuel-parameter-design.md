# Consumer review: the lem-lean fuel-parameter design (R1) — refined-cerberus / cerberus-heaplang

Reviewed: lem-lean `arc/fuel-parameter`, `doc/lean-backend/2026-09-03_fuel-parameter-design.md`
(draft + R1) and `2026-09-04_fuel-parameter-record.md` (§2, §5, §6, §9);
cerberus-lean `lean_frontend/docs/2026-09-03_fuel-parameter-consumer-assessment.md`.
Reviewer: the refined-cerberus orchestrator [AGENT], 2026-09-04, at the
request of the design note ("DRAFT for the refined-cerberus consumer
review before either merge"). The ruling this implements is the
operator's ([USER 2026-09-03], quoted in the note §1). Our own
requirements note: `docs/2026-09-03_request-lem-lean-pmap-laws-and-fuel-scheme.md` §3.

## Verdict

**ACCEPT the design, with one requirement that must be in scope for the
cerberus half (§2 below) and one ruling recommendation (§3, D2).** The
mechanism (one ambient `LemFuel` class, every fuel'd call starting from
the full ambient, generated `_zero` lemmas, numerals deleted, a
plant-tested no-numeral gate) is the right shape and matches our first
requirement exactly. What is not yet in scope — an absorbing exhaustion
outcome for every fuel'd function on the execution path — is the
difference between "the fuel can be quantified over" and "the quantified
theorems are true". Our restatement is sized in §5.

## 1. What we endorse, and why (measured against our statements)

1. **The class mechanism.** `[LemFuel]` instance-implicit binders, call
   sites unchanged, `@f ⟨n⟩ = f_lemFuel n` by `rfl`. Our theorems become
   `∀ [LemFuel], … ≤ LemFuel.fuel → …` or `∀ n, …` through `⟨n⟩` — both
   forms are usable from Iris statements; no per-signature threading; a
   single instance means no diamond. The hazard the record names (a stray
   global `instance : LemFuel` silently defaulting everything) is
   real and the gate covers it; we will add the same grep to our own
   gate (a consumer must not mint an instance outside a `letI` at an
   entry point either).
2. **Each fuel'd call starts from the FULL ambient, not the caller's
   remaining counter.** This is decisive for us and we want it kept
   (record §2, `TestFuelParamCheck` (5)). Our ~60 hypotheses have the
   shape `potential e ≤ fuel` PER EXPRESSION, and our round-count bounds
   (`fibRounds n + 4`, `13·|ns| + 7`, …) are per-loop. With a shared
   decreasing counter every bound would have had to be a SUM over the
   whole run's call tree — unstatable without a global cost model. With
   the full-ambient convention the restatement is exactly the record's
   §6.7: one hypothesis variable replaces two constants, statement shapes
   otherwise unchanged.
3. **Data-measure structural recursion instead of fuel wherever the
   measure is in the data** (record §4, §5 item 5): `Pset.join`/`Pmap.join`
   on the stored height (this also answers our request §2 — closed engine
   maps reduce again), union/intersection on heights, `compareAux` on the
   count. Nothing is chosen, nothing bounds the semantics, and the kernel
   computes. This should be the DEFAULT for the cerberus half too (§2).
4. **Generated `f_lemFuel_zero` lemmas** (67/67 on the dry run) — our
   requirement 2; the driver family's kill sentinel is the one we use.
5. **Fail-closed scope check** (a fuel-lifted definition with no ambient
   in scope is a generation-time error) — correct; it is what surfaced D2.
6. **The no-numeral gate**, comments stripped, four shapes, plant-tested.

## 2. The requirement that must be in scope: exhaustion on the execution path must be ABSORBING or ABSENT

The record §5 says fuel monotonicity is not generated because "a body may
absorb a sub-call's sentinel" and because the convention's payload
`fuelExhausted x` is an OPAQUE value. It then states exactly what makes
monotonicity provable: "an exhaustion outcome that the return type
distinguishes AND that every consumer of a recursive result propagates
(an absorbing element of the monad — cerberus's `NDkilled` through
`nd_bind` is exactly that)". It files that as TODO row 13. For the
consumer this is not a TODO; it is the truth condition of every
`∀ fuel` theorem we will state.

Why. Our partial statement is "for every fuel, the run is EXHAUSTED or
DONE-with-post, and never anything else"; our total statement is "for
every fuel at or above the bound, DONE with the specified result". Take a
fuel'd function on the execution path whose exhaustion is the opaque
panic payload — in the kernel the `Inhabited` default of its return type
(`CerbMem.sizeofCtype`, `memValueToBytes`, `reconstructValue`,
`typeofMval`, `unqualifyAndUnatomic` are on the dry run's seam list,
§6.6). At a fuel below that function's depth on some program, the
function returns a DEFAULT VALUE and the run CONTINUES: a store proceeds
at a wrong size, a value is reconstructed as a default, and the driver
may complete "successfully" with a wrong readout. Then:
- the partial statement is FALSE at that fuel (the outcome is neither the
  kill nor the specified post), unless our hypothesis also bounds the
  depth of every such function on every reachable input — a bound we
  cannot state without exposing the engine's internals in our exports;
- fuel monotonicity fails for the same reason, so "done at the bound ⇒
  done at every larger fuel" — the total statement's shape — is
  unprovable.

So, for the cerberus half, every fuel'd function reachable from `drive`
must satisfy ONE of:
- **(A) no fuel**: structural recursion on a data measure (the ctype AST
  for `sizeofCtype`/`alignofCtype`/`offsetsof`/`unqualifyAndUnatomic`;
  the value/type structure for `memValueToBytes`/`reconstructValue`/
  `typeofMval`; the expression for the pexpr evaluators EXCEPT the Core
  pure-function-call recursion, which is genuinely partial). This is
  the record's own preferred form (§5 item 5) and it removes the fuel
  rather than parameterising it. We expect most of the 67 to be (A).
- **(B) absorbing typed exhaustion**: the function lives in a monad with
  an absorbing exhaustion outcome that `bind` propagates (the ND monad's
  `NDkilled fuelExhaustedKill`, or a memory-monad error that the driver
  turns into that kill), and its `_zero` lemma states that outcome. The
  driver family already is (B). The pexpr evaluators' call recursion
  and `nd_bind` itself are (B) candidates.
- **(C) not reachable from `drive`** — stated and gate-checked (the
  totality gate's slice already has the vocabulary).
An opaque-default exhaustion on the execution path is a silent
fail-open under the project's own rule and must not survive the half.
With (A)/(B) everywhere on the path, monotonicity IS a theorem by
induction on the counter, per function, and the backend can generate it
for (B) functions whose payload is a declared absorbing outcome of a
declared monad — the record's TODO row 13. We ask that row 13 be
scheduled with the cerberus half, not after it; we do not need it
generated for the first pin (we can prove the handful we use), but we
need (A)/(B)/(C) to hold so that the theorems are true.

Concretely for the record's §6.6 seam list: `sizeofCtype`,
`alignofCtype`, `offsetsof`/`offsetsofMembers`/`memberAlign`,
`memValueToBytes`, `reconstructValue`, `typeofMval`,
`unqualifyAndUnatomic` — we ask for (A). If any resists structural
recursion (mutual recursion through `Ctype`'s nested lists is the usual
obstacle), (B) via the memory monad's failure is acceptable; a
`fuel_consumer` returning a default is not.

## 3. The operator decisions (record §9), from the consumer's side

- **D2 (fuel'd equality as instance methods: `Eq ctype`, `Eq
  core_base_type`, `Eq mem_value`; the `monStep` indreln rule).**
  Recommend **(i)**: make the three equalities structurally recursive in
  the model. They are data-measure recursions (equality of finite trees)
  — the same form as §2 (A) — and `ctypeEqual` IS on our execution path
  (every load/store compares the access type against the allocation's).
  Option (ii) (instances taking `[LemFuel]`) would make type equality
  fuel-dependent in every statement that mentions it, for no semantic
  reason. `monStep` is the concurrency model, outside our fragment; its
  restatement is not urgent for us.
- **D1 (`Pset.tc` as a data measure)**: agree with the classification as
  landed; not on our execution path.
- **D3** (`lemLeastFixedPoint`'s `| 0 => x` is lem's own definition):
  agree; a lem design choice, not a magic value.
- **D4** (`int32FromInteger` wrap vs raise): not a fuel question; it is a
  mirror/zero-discrepancy question for the cerberus-lean rules. No
  consumer position, except: whichever is ruled, it must be the same on
  every target the register calls "the semantics".
- **The one silent VALUE payload** the record found
  (`defacto_memory_aux.lem:469` `simplify_integer_value_base`, "returns
  its input unsimplified" at exhaustion): that is exactly a §2 (B)
  violation if it is on the execution path — an exhausted simplifier
  returning its input changes the value the run computes. Please
  classify it (A), (B) or (C) explicitly in the cerberus half.

## 4. Two smaller points

- **Perf**: an instance-implicit `Nat` argument is a normal argument;
  the record §7's "report, don't optimize" is the right posture. If the
  differential lanes show a shift, it is not the binder.
- **The CLI default `--fuel 100000000`** is the only permitted numeral
  and lives in the binary. For our closed shipped-constant corollaries
  we will instantiate `⟨100000000⟩` ourselves in the statement that
  claims to be about the shipped binary, and nowhere else.

## 5. Our restatement, sized (for the change manifest; one slice, after the re-pin)

Every definition and theorem of ours that mentions an engine function
reaching fuel (`step_ctx`, `advance_step`, the driver loops, `runND`,
`drive`, `CerbMem.loadM/storeM/allocateObject/allocateRegion/killM`,
the pexpr evaluators) gains `[LemFuel]` — the mirror `Step`, `Frag`'s
evaluators where they call the engine's, `MachineCtx`-level lemmas,
`Round`, `Soundness`, `DriverCollapse`, `Adequacy`, `TotalAdequacy`,
`ProdEntry`/`ProdLoop`, every exhibit. Expect the census of that slice
to be CHANGED ≈ everything (a binder added to nearly every statement),
with the statement texts otherwise unchanged except: the ~60
`… ≤ lemDefaultFuel` hypotheses → `… ≤ LemFuel.fuel`; the production
statements' `hfuel : … ≤ CerbFuel.driverFuel` → `… ≤ LemFuel.fuel`
(record §6.7 shape); the closed partial forms → genuinely `∀ [LemFuel]`
over both loops (the outer-fuel degeneracy of F1's forms disappears —
KNOWN-OPEN-ITEMS A2 closes); the shipped-constant corollaries at
`⟨100000000⟩`. The thread-level lemmas keep their shape. Snapshot
pre/post and the census will be recorded as usual; this is an internals
+ statement-shape slice, ruled one-change-at-a-time, sequenced after
the LemLib re-pin (which lands independently of this arc).

## 6. Provenance

[AGENT] (refined-cerberus orchestrator): the review. Rulings cited are
the operator's, verbatim in the design note §1 and in this repo's
`docs/DECISIONS.md` (2026-09-03, "FUEL IS A DEFECT…"). For the operator
to relay to the lem-lean / cerberus-lean orchestrators.
