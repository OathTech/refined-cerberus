# Whole-file corpus charter: independent pre-launch review

Verdict: **PASS with Notes**. No substantive logical or coverage gap found
in the proposed scope, and no required launch fix. This is a charter and
source-inspection review, not verification of the future implementation.

[AGENT 2026-09-08], fresh adversarial reviewer. Brief:
`docs/AUDIT-BRIEF.md`; register read: `docs/KNOWN-OPEN-ITEMS.md`, including
A7, B6–7, B19–20 and C19–20. Working practices: `AGENTS.md`.
The operator authorized autonomous execution of the expanded t5/t6/t4
cohort, a final adversarial subagent review, and a pause for external
review. No merge, push or tag is authorized by this review.

Reviewed the parent's uncommitted
`docs/2026-09-08_whole-file-corpus-charter.md` in
`worktrees/demo-whole-file-corpus`, SHA-256
`bee8e034bb948f5b4039c579a8c5a9f9818f8c6a1fb5cb707a9b09a805bf9d2f`.
Source baseline: main `4bc0a98a686dffc2377d4980108080f04cc8efad`.
Read the expanded proposal and its original t5 scout in
`worktrees/scout-next-whole-file-slice`, plus the retained t4/t6 JSON
reports. This review ran no Lean, Lake, builds or frontend executions;
the parent owns the heavy lane. The review report alone is committed in
the separate `worker-whole-corpus-charter` worktree created from main by
`scripts/new-worktree.sh`.

## Findings against the promised result

**The scope is coherent and its boundary is explicit.** It completes the
master plan's V1-1b route for the three already-supported C programs,
retaining t1. Shared integer load/conversion/assignment support is a real
prerequisite, not merely common tooling: the old `Examples/EmittedInt`
helpers fix the unannotated `intTy`, operand spellings and `StdE3` library,
while the captured programs preserve their actual annotations and linked
library. The charter requires multiple actual consumers of the generalized
support and excludes an unrelated arbitrary-library framework. The exact
captured stdlib adapter remains `EmittedStdCore.HasIntLibrary`; its
`hasIntLibrary_of_stdlib_data_eq` transfer is already available. General
evaluation and memory premises may make the client rules reusable without
claiming arbitrary library implementations satisfy that adapter.

**The narrowly permitted proof-rule change has a concrete derivation
site.** I read `wpt_neg_bound` in `Wpt.lean`: its constructor-identity
extern premise occurs only in the proof of the final fresh-binder read,
after `update_env_tuple_wild_sym`. `EnvLaws.evalPexpr_sym_of_compare`
establishes the required evaluation from comparison equality and a
`SymFrame` lookup. The new frame is `envAdd ... ev0`, so its frame property
must be supplied from the existing preservation fact. The original theorem
can remain a specialization of the weaker-premise theorem. This does not
require changing the judgment, negative-action mirror or driver protocol.
The charter allows precisely this change and its integration surfaces;
it does not repeat the earlier impossible fence of freezing all of Wpt.
This is source evidence for feasibility, not an elaborated new proof.

**The three program obligations have not been reduced to terminal
computations.** T5 needs its conditional and assignment proof; t6 requires
its five registered continuations and dispatch; t4 requires its four
continuations, invariant and decreasing budget. I checked the existing
`CorpusT4Exhibit.t4Budget` and its successor identity, and the uses of that
identity in the loop derivation. They provide a concrete existing proof
architecture, not permission to copy the old budget onto a different body.
The charter requires exact body equality, full syntactic fragment
membership, separate evaluator-depth bounds, exact collector proofs and
new public total derivations. Any genuinely new uncovered form triggers
the stated decision point. B7's disclosed residual is not silently waived.

**The theorem referent and fuel quantification are correct targets.**
`EmittedT1Exhibit.certified_production` already states the singleton Active
equation directly over genuine `drive` and `initial_driver_state`; its
capture-transfer twin retains data/supply equality and all three original
comparator-check premises. The charter requires the same complete-file
route for the new programs, at exact captured supplies and every ambient
execution fuel above justified sufficient bounds. The scout's fuel1000
observations are explicitly not proofs of those bounds. The old numeric
wrapper floors and their remaining V1-4a work are disclosed rather than
claimed closed. Nothing in this charter requires an unproved frontend
fuel-independence theorem: the all-fuel claim concerns execution of the
retained complete data term.

**The capture claim has an appropriate bounded evidence obligation.**
The retained t4/t6 reports record independent structural comparison,
quotation/supply equality and the original captured comparator checks as
true, with supplies 92/51 and Active values 10/20 respectively. T4 also
records one loop-attributes entry. These remain executable observations;
the charter separately requires complete retained fields, proof-relevant
body equality and the actual comparison checks in the new theorem route.
Fresh Cabs and original-instance comparisons are required for all four
fixtures. The t4/t6 scout reports have empty negative-check results;
the charter correctly makes intended main/supply perturbation results
future acceptance work instead of claiming they already passed.
OCaml provenance reporting remains in scope.

**The implementation fence closes over the necessary integration.**
It includes the shared support, program modules, narrowly amended derived
rule, actual-file entry helpers, API, Audit, Shipped, tools and claim
surfaces. The unchanged-existing-signature census protects retained
wrappers while permitting new exports. Frozen semantics, mirror/judgment
definitions, heap coupling and driver protocol are stated, with an
explicit escalation point rather than silent extension. Full capped
verification, exact axiom sets, independent final range review and the
external-review pause are unambiguous.

## Notes for implementation and the final reviewer

N1 — Preserve the generality of the existing complete-file route:
quantify arbitrary filesystem state and argument list in the three new
driver and capture-transfer statements, as t1 does. Required result 4
could say this explicitly. This is a small acceptance clarification, not
evidence of an existing logical hole; no new theorem has been written.

N2 — Keep the two kinds of generality distinct on public surfaces. The
shared load/store rules can accept general evaluated operands and memory
premises; the present integer-library adapter still concerns the specific
captured std.core declarations. Its equal library-data transfer across
four files does not prove arbitrary-library correspondence. The current
charter/proposal disclose this correctly; preserve that wording at exit.

N3 — When reporting the final all-fuel results, identify the frontend
capture observation separately from the execution-fuel theorem. A fixed
quoted data term can have an all-sufficient-execution-fuels certificate
without asserting that every frontend invocation at every fuel produces
that term. The current charter has the right distinction; the final
claim documents should retain it.

The final review must inspect actual proof terms and integrations. This
pre-launch PASS does not discharge the new body/collector/freshness/budget
proofs, all-four comparison runs, exact axiom pins, old-signature census
or the final adversarial review. Option (a), all-ten corpus coverage,
FreshAbove/cost cleanup, the general derived while rule, calls, seq_rmw,
tag tables and the other already-owned master-plan work remain outside
this landing; none is a new blocker discovered here.
