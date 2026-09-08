# Whole-file certificates for the supported C corpus

Status: COMPLETE ON FEATURE BRANCH; full baseline/final verification and
fresh adversarial final review passed. Paused for external review.
[AGENT 2026-09-08]. This charter makes the user's autonomous execution
request concrete; it does not authorize a merge or push.

## Authorization and baseline

[USER], verbatim:
> Go ahead and put together a charter for this work, and set it as a goal. As before, work independently with no human interaction unless needed for decision-making. Work on a worktree, branching off main. Make sure to follow the practices established in this repo. At the end, run a review using an adversarially-briefed subagent. Once you have a reviewed merge candidate covering all the work, pause for external review

Accepted scope is the proposed full V1-1b cohort: t5_ifelse, t6_switch,
t4_while, with generic emitted integer support and the landed t1 route
retained. Proposal/evidence: `scout-next-whole-file-slice` at `2f180e8`,
`docs/2026-09-08_whole-file-corpus-proposal.md` and its companion scout.
Main baseline `4bc0a98a686dffc2377d4980108080f04cc8efad`; branch
`demo-whole-file-corpus`, worktree `worktrees/demo-whole-file-corpus`.

Semantics pin `89f7e688530c6910884518811d645e4e892e4507`, Lean4.32.2,
LemLib and Iris pins stay fixed. The worktree's pinned workspace and
package cache were copied from the verified primary checkout, then checked
before use. Full baseline gate and signature snapshot precede proof edits.

## Required results

1. Shared emitted integer load, conversion, arithmetic and assignment
   support that retains actual annotations/types/symbols and consumes
   evaluation, memory and captured-library lookup premises. It must have
   multiple real consumers across the corpus. Extend/extract existing t1
   support where useful; no unrelated abstract framework.
2. A narrowly generalized derived negative-assignment rule allowing
   comparison equality through extern resolution. `wpt_neg_bound`'s only
   use of constructor identity is the final fresh-binder read; use
   `evalPexpr_sym_of_compare` there. Preserve the old public statement as
   a specialization. No change to judgment definitions or semantics.
3. Complete retained file data and actual-body shape proofs for t5/t6/t4;
   syntactic fragment membership and separate evaluator-depth bounds;
   exact save-collector and continuation proofs (t5 one, t6 five, t4 four);
   public total derivations, including t4's invariant and decreasing budget.
4. Direct genuine-driver certificates for the complete files at their
   captured frontend supplies (scout:47/51/92), every ambient fuel above
   justified sufficient bounds, arbitrary filesystem state and arguments,
   with singleton Active returns1/20/10,
   unblocked and empty trace/stdout/stderr. Capture-transfer theorems retain
   data/supply equality and the original comparator checks explicitly;
   shipped corollaries advertise these new certificates. Preserve every
   existing public signature and retain old wrappers as labelled regressions.
5. Reuse/consolidate whole-file speedbumps across t1/t5/t6/t4: fresh Cabs,
   complete structural data independently of quotation, exact supply,
   original comparator checks on the compared instance, and targeted main/
   supply perturbations. Preserve OCaml provenance reporting. Update
   API/audit/classification/claim/corpus/plan surfaces consistently.
6. Full capped verification, exact axiom cones, unchanged-existing-signature
   census, and a fresh adversarially briefed full-range review with all
   substantive in-scope findings resolved. Stop at a committed candidate
   for external review. No merge, push or tag.

The result closes V1-1's four-program migration at option (b): quoted
complete output of the pinned Lean frontend consuming OCaml Cabs, linked
and converted, with executable comparison. It does not prove the frontend
correct in the kernel, identify its file with OCaml printed Core, or finish
the demo's remaining semantic/rule-quality arc. New frontend-supply values
are captured data, not arbitrary floors; new sufficient budgets must be
justified by proof composition, not inferred from a fuel1000 probe.

## Implementation fence

Allowed: new shared emitted support module(s); new
`Examples/EmittedT{4,5,6}Data`, `Examples/EmittedT{4,5,6}` and
`EmittedT{4,5,6}Exhibit`; `EnvLaws`, `EmittedStdCore`, `Examples/EmittedInt`,
`EmittedT1Exhibit` and `IntRules` for required generic derived facts;
`Wpt` (and partial twin in `Wps` if useful) only for the narrowly named
assignment-premise generalization, preserving old statements. Existing
corpus modules may be small specializations of shared support without
changing contracts. `EmittedFile`/`EmittedMapChecks`/`ProdEntry`/`ProdLoop`
may gain small required generic lemmas while preserving existing APIs;
no driver protocol change. Integration: root/API/Audit/Shipped, module
classification/manifest, tools/fixtures, claim documents, master-plan and
requests/KOI progress, append-only DECISIONS, this charter and evidence.

Frozen: dependency pins/provider sources, Step/Round/Soundness/Fragment
judgment and mirror definitions, Heap/coupling/Language, scheduler and
driver protocol. No C calls, seq_rmw, tags/globals, kill logic, package
extraction, broad FreshAbove/cost restatement, wrapper retirement or all-ten
corpus expansion. Existing `600` wrapper sites remain unless separately
authorized later; the new certificates use exact captured supplies and
local non-collision obligations.

A real need to change frozen semantics or judgments, or an unprovable
promised export, is a decision point to report. Routine in-fence proof,
module-placement and review fixes are authorized without another check-in.
New helpers belong in support, not positive clients. Preserve exact
annotations and complete file fields; a convenient transcription is a
proof device only after its equality to the captured body is established.

## Work and review process

- Internal green checkpoints: common support, t5, t6, t4, full integration
  and review. Independent bounded workers may prepare distinct program
  modules in their own worktrees. Parent assigns file ownership, controls
  the heavy lane and independently verifies integration.
- Every Lean/Lake command uses `scripts/capped`, normally40G. Heavy builds
  are serial across workers. No native proof reduction, new axioms/sorries,
  or heartbeat/recursion-limit campaign. A pass approaching an hour is a
  stop-and-report event; a committed park record ends that slice.
- Full baseline gate and snapshot; intermediate fast gates/targeted capped
  module checks; full final gate and final signature snapshot/census. Pin
  actual exact axiom sets, without manufacturing trio dependencies.
  Verify all four actual instances and intended negative results, not
  merely an elaboration failure. Recorded observations are not proofs.
- All writes remain in refined-cerberus. Ignored logs/scratch are ephemeral;
  commit useful excerpts and label derived counts. Commit green work promptly.
  Run citation checks on changed claim documents.
- Fresh pre-launch charter review and final independent full-range review,
  both briefed with `docs/AUDIT-BRIEF.md` and KNOWN-OPEN-ITEMS. Final review
  is adversarial about logical/coverage gaps, theorem referents, actual
  externs/comparators, fresh-symbol obligations, budgets/loops, old API
  preservation and claim honesty, proportionate about tooling hardening.
- Final state: clean, reviewed, green feature branch covering all required
  programs, with evidence and unresolved external boundaries explicit.
  Pause for the user's external review; never merge autonomously.

## Pre-launch review disposition

The fresh [review](2026-09-08_review-whole-file-corpus-charter.md), adopted
from `bf88f83`, is PASS with Notes and no launch blocker. N1 is explicit in
required result4: arbitrary filesystem and arguments, including transfer
twins. N2/N3 remain acceptance distinctions: generic evaluated-operand rules
versus captured-library contracts; fixed frontend capture versus all-fuel
execution. Baseline full gate is green and the 5,569-declaration snapshot
is byte-identical to t1's final surface. Source implementation may start.

## Completion and external-review handoff

All six required results are delivered. The implementation record retains
the full verification evidence and exact signature census: 512 additions,
zero existing changes or removals. T1/T5/T6/T4 now have complete-file,
capture-transfer and shipped certificates; generic support has multiple
actual consumers. The frozen semantics and dependency pins are unchanged.

The fresh [final adversarial review](2026-09-08_review-whole-file-corpus.md)
returned PASS with one documentation Note, N1. Correction `208194d`
distinguishes T5/T4's source-pointer bound from T6's sufficient label/driver
bound; the reviewer confirmed it without requiring a theorem change.
The reviewer independently passed the full gate, fresh audit, exact
signature comparison and fresh elaboration of the shared support and all
six new body/exhibit modules.

The complete, reviewed candidate remains on `demo-whole-file-corpus`.
Main stays at `4bc0a98`. Execution stops here for external review, with
option (a), the six unsupported C programs and the remaining master-plan
work explicitly open. No merge, push or tag is authorized or performed.
