# Response to the cerberus-lean concurrency branch: the S1 interface (2026-09-04)

Reviewer: refined-cerberus / cerberus-heaplang orchestrator [AGENT], at the
request `lean_frontend/docs/2026-09-04_concurrency-S1-interface-review-request.md`
(charter D5/§8, [USER 2026-09-04] "handle carefully"). Our side's facts are
cited to main `596a8ff`; rulings quoted are the operator's, verbatim in our
`docs/DECISIONS.md`. Nothing here designs their semantics; it says whether
the proposed SHAPE serves the theorems we state over it. For the operator
to relay.

## 0. Summary

Accept the interface as drafted (Q1), with: distinguished error
constructors (Q2, yes), the syntactic F_SC predicate shipped total and
`rfl`-evaluable (Q3, yes, scope below), the SC-instance labelling (Q4,
yes) PLUS the one-tree agreement lemma (Q4, please prove it — it is the
theorem that transfers our single-thread adequacy to `CM_sc`), and a
STAGED re-pin (Q5). Two consumer facts they should have: what our
statements look like today (§1), and how a live scheduler changes them
(§4).

## 1. What we state today, so the delta is visible

Nine closed shipped-driver statements of the shape
`CerbND.runND (drive fmapEmpty false file args) ((initial_driver_state sup file fs).1) = [(Active dres, [], dst')] ∧ …`
(ARCHITECTURE §2.5, table); a closed partial form
`∃ st dst', runND (drive …) … = [(st, [], dst')] ∧ (st = Killed dst' fuelExhaustedKill ∨ …)`
(`prod_run_safe_procs`); and thread-level statements over the
single-thread loop `drive_nonmemory_steps_aux2_lemFuel fl` at every `fl`
(`DriverSafeCtl`/`DriverDoneCtl`), which are the Reynolds/O'Hearn
triple's semantics by ruling ([USER 2026-09-03]: "the outer loop is the
'scheduler' loop and the inner loop is the 'single threaded' loop … the
scheduler is degenerate, we never see schedule changes"). Two properties
of these statements matter for S1: (i) they are SINGLETON outcome
equations (the sequential driver is deterministic); (ii) they exclude
failure by CONSTRUCTOR — the killed arm is exactly the kernel-transparent
`fuelExhaustedKill`, never a string.

## 2. Q1 — names and shape: accept; explicit argument

No objection to `concurrency_model` / `CM_sequential` / `CM_sc`, nor to
the position (the bool's). EXPLICIT is right for us: a statement reads
`drive fmapEmpty CM_sequential file args` and `cases model` works; a
reader-lifted parameter would put the selector in the ambient like
`tagDefs`, where our statements would have to pin it with an instance or
an equation (we already carry `htd : M.tagDefs = fmapEmpty` at every
adequacy theorem for exactly that reason — KOI B4). Please keep the type a
payload-free inductive (kernel-transparent, decidable equality by
`deriving`), and keep the `false → CM_sequential` rewrite the ONLY
statement-text change of S1 for a sequential consumer (we will census it:
expected CHANGED = every statement naming `drive`, by that one token).

## 3. Q2 — outcome classes: yes, distinguished constructors

Our theorems exclude failures by constructor (§1(ii)); a string-carrying
`DErr_concurrency s` can only be excluded by matching the whole
constructor with an arbitrary `s`, which is fine for "never reached" but
useless for "reached exactly when". Please add `DErr_model_refused`
(spawn under `CM_sequential`; out-of-fragment under `CM_sc`) and
`DErr_model_inconsistent` (the bridge-check violation), each with a
payload that is data (the offending action / the first offending order),
not free text — so a theorem can say "the run's only non-done outcome is
`Killed (Other (DErr_model_refused a))` for the `a` the program contains".
The `driver_error` change costs us nothing today (no statement of ours
names a `DErr_*` constructor — measured: 0 hits in `cerberus-heaplang/`),
and it is the right time to do it. Same request as for fuel: make the
refusal outcome a kernel-transparent value (an `Error0`-style term with
a `_zero`/`_eq` lemma), never a `panic!` (the `Inhabited` default reading
— our ARCHITECTURE §3 "The `panic!` arms").

## 4. Q3 — `sc_fragment_ok`: yes, ship it; scope and form

Yes. Form: total, STRUCTURAL recursion over the Core file (a data
measure — no fuel, per the fuel ruling), so that `sc_fragment_ok file =
true` closes by `rfl`/`decide` on a closed file; plus an `_iff` lemma to
a Prop stating the scope, so a theorem can carry either. Scope we want
excluded (i.e. `false`): any atomic order other than `Seq_cst`; any
`Fence`/Linux op; `Ewait`; anything whose Phase-0 semantics is not the
SC interleaving over the concrete memory. INCLUDE `Epar` (spawn is what
`CM_sc` is for). Please have it read only the file (not the run state),
so the refusal is a property of the program as you say, and please state
in the manifest that its cone is axiom-free/trio-only and panic-free.
For our logic the DRF-SC split you describe is exactly right: (a) is a
`decide`-able premise; (b) race-freedom is our logic's job — a
separation logic proves it by ownership, which is the point.

## 5. Q4 — labelling, and the agreement lemma we need

Yes to the labelling: every rule/adequacy result over `CM_sc` carries
`sc_fragment_ok file = true` (or the Prop) as a premise and is named the
SC instance; adequacy over the selector where it can be. The semantics-
side fact that helps most, please prove it inside one tree:

  **Agreement on `Epar`-free programs**: for every file with no `Epar`
  (a syntactic predicate you can also ship), every `fuel ≥ some bound`
  (or under the fuel-parametric scheme, for the same ambient),
  `runND (drive tds CM_sequential file args) st = runND (drive tds CM_sc file args) st`
  — or the weaker "same outcome list up to the trace field" if the
  scheduler rounds leave a footprint in the state.

Why we need it and not just the labelling: under `CM_sc` memory actions
become non-advanceable, so the scheduler round performs them and the
outer loop turns one round per memory action; our thread-level lemmas
are stated over the INNER loop and know nothing of that. The agreement
lemma is the bridge that lets every single-thread certificate we have
(and every one the emitted-Core arc E produces) be read under `CM_sc`
for free — and it is the precise statement of "the scheduler is
degenerate for single-threaded programs". Note the fuel interaction: the
outer fuel does WORK under `CM_sc` (one round per memory action), so the
lemma's fuel side condition is real; under the fuel-parametric scheme
(one ambient) it is "for every ambient ≥ the run's need", which is
exactly the monotonic form our F2 slice states.

For the recorded non-parametric point (read values at issue): agreed
that any `CM_sc` rule using "a load returns the current heap value" is an
SC-instance rule. Our own heap coupling (points-to over the concrete
memory) IS that SC instance; we will keep the memory-value coupling behind
an interface in the shared coupling library we are designing (Lane C item
6), so a deferred-read instance replaces one layer, not the logic.

## 6. Q5 — re-pin timing: staged

Staged, please: S1's signature change as its own announced change (one
token per statement, a small forced-semantics-change slice with its own
census and range audit on our side), then the rest of Phase 0. Our re-pin
queue is already LemLib representation → the fuel half → S1; if S1's
signature rides the same pin as the fuel half, we still take it as a
separate slice (one change at a time). We do not want one large pin: each
re-pin is one audit range.

For §2.3's "step-identical to today's `false`": the three evidence forms
are what we expect; the FOURTH form is ours — at the re-pin, the demo's
FULL gate (402 pinned exports trio-exact, the nine production proofs
re-elaborated unchanged, the boundary and manifest speedbumps) is the
regression suite ([USER 2026-09-04]: "the demo as regression suite"), and
the census must show CHANGED = the one token. Please list in the S1
change manifest the `process_core_step2`/`advance_step` arms that gain
the new kill (file:line), since our round classification
(`frag_round_complete`, `ShippedRefusal`; `Round.lean`) re-proves against
them.

## 7. Two things we are not asking for, stated so they are not inferred

Nothing about Phase 1–2. And no change to the single-thread loop's
shape: our thread-level statements and the emitted-Core arc depend on
`drive_nonmemory_steps_aux2` staying the single-thread executor with the
current step-list discipline (last component first, first advanceable —
measured in `docs/2026-09-04_emitted-core-dialect-design.md` §B).

## 8. Provenance

[AGENT] (refined-cerberus orchestrator): the answers. [USER 2026-09-03/04]:
the rulings quoted. Docs-only; nothing built.
