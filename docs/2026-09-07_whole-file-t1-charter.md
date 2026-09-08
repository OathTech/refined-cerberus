# Reusable whole-file adequacy, with t1 acceptance

Status: COMPLETE on the feature branch, 2026-09-08, under the user's
2026-09-07 authorization to execute the reviewed proposal autonomously
on a feature worktree. No merge or push is
authorized. The user explicitly requires sign-off before merging to main.
This charter makes the accepted scope concrete; its pre-launch review is
recorded beside it. Standing review brief: [AUDIT-BRIEF.md](AUDIT-BRIEF.md).

## Authorization and baseline

[USER, working session 2026-09-07]: "Great, can you set this up as a goal
and execute on it in a worktree. Make sure to follow the working practices
from the repo docs. While working on the feature branch, you do not need
to check in with the user, but do not merge to the main branch without
user signoff."

Accepted proposal: [next-slice review](2026-09-07_next-demo-slice-review.md),
commit `969281f`, including the user's clarification that generic machinery
is part of the deliverable. Main baseline: `7040406`; feature branch:
`demo-whole-file-t1`; worktree: `worktrees/demo-whole-file-t1`.
Read-only proof reference: G2 `520654f..5bfe992`, independently rebuilt and
checked in `worktrees/review-g2-source` during the proposal review.

Pin stays `89f7e688530c6910884518811d645e4e892e4507`, Lean 4.32.2, and
the existing LemLib/Iris dependency pins. The workspace was copied from
the verified G2 review workspace; the package cache from `codex-refinement`
(same Lean source as current main). Verify the workspace and run a full
capped baseline gate before taking a signature snapshot or editing Lean.

The proposal's R-4 disposition is adopted for this slice: the file producer
is the pinned Lean frontend consuming OCaml Cabs, then linking and converting
the complete file. The comparison with OCaml's printed Core is not assumed.
The existing option-(b) executable comparison boundary remains explicit;
option (a), the elaborator in the theorem, remains a future target. The
older synthetic t1 proof is retained as a labelled regression, as proposed.

## Required results

1. Generic engine-file capture and reconstruction, preserving all eleven
   fields, optional map trees, and separately parameterized comparators.
   Kernel reconstruction and finite comparator-check correctness theorems.
2. Generic driver delivery/startup/closed execution support retaining the
   supplied file and runtime extern map. Existing empty-extern/library-file
   interfaces specialize these results and keep their previous contracts.
   The generic capture, map-check, and driver modules do not depend on t1's
   data or result. The separate `EmittedStdCore` adapter uses the captured
   library declarations from t1's data and is reusable for other files with
   that same library data and passing lookup checks; it is not part of the
   fixture-independent machinery.
3. The actual complete-file t1 total certificate, with the G2 conclusion:
   a singleton active result of the genuine `runND (drive ...)` at every
   execution fuel at least 50, returning `lint 4`, unblocked, with empty
   stdout/stderr. It uses the captured frontend supply 36 and the original
   comparator-check hypotheses. Keep the transfer theorem to an arbitrary
   original file under explicit capture equality/supply/check premises.
4. A reusable capture/comparison tool, a fresh C-to-Cabs t1 input check,
   independent structural equality on captured data alongside quotation
   equality, and passing concrete comparator checks. The full gate runs
   this as a speedbump. A retained-main-field perturbation and a supply
   perturbation must be rejected; these are executable checks, not proofs.
5. The whole-file theorem is the advertised t1 certificate and has a
   shipped-fuel corollary. A7 is accurately partial: t1 option (b) delivered;
   other corpus files and option (a) remain open. Source, claims, audit pins,
   corpus metadata, API, and reviewer-facing documents agree.

The data comparison must preserve tree heights/shape and annotations;
existing Fmap binding-list equality is insufficient. Inspect leaf instances;
Float, if encountered, compares bits consistently with the quoter. Keep
tool-only derivation/instances outside the logic library. Correctness of
the IO frontend/quoter is not asserted by `restore_capture` or by the gate.
Record the loader/quoter and the kernel `mkAuxLemma` device in ARCHITECTURE.
The existing generated `ctype` equality ignores annotations, and enclosing
instances may already contain that dictionary. Independently derive the
constructor dependency closure before its parents, or use a separate
structural class; a local override of the leaf alone is insufficient.

## Implementation fence and sequence

Phase A: re-cut the G2 proof machinery and t1 consumer onto current main.
Files: new `EmittedFile`, `EmittedMapChecks`, `EmittedStdCore`,
`EmittedT1Exhibit`, `Examples/EmittedT1`, `Examples/EmittedT1Data`; existing
`EnvLaws`, `DriverCollapse`, `ProdLoop`, `ProdEntry`; root/API/Audit and
module classification/manifest as required. Reuse only G2, not G3/G4.
Resolve the measured apply conflicts preserving current main's repairs.
In particular preserve R2: public fragment/launcher/round interfaces use
syntactic `Frag` and explicit `evalDepth` hypotheses. Internal `*_fuel`
proof devices may use `FragFuel`; do not export or pin those as the new
public interfaces. Construct t1's membership without a fuel premise.
Run the fast gate and commit the green proof slice promptly.

Phase B: the capture/comparison/gate and advertised certificate integration.
Files: G2's loader/quoter/inspector scripts and wrapper, new tool-local
structural comparison support and a whole-file speedbump wrapper;
`scripts/test_unit.sh`; `Shipped.lean`; `Examples/CorpusE0.lean` corpus
certificate metadata only; API/Audit/classification/manifest where forced.
Fixtures: `docs/corpus-a7/t1.cabs.json`, concise provenance/usage records.
Existing `t1_shipped` may be restated to the complete-file certificate;
retain its old wrapper contract under `t1_wrapper_shipped` if restated.
Commit green intermediate slices with `--fast`; full gate at phase exit.

Phase C: claim surfaces, independent full-range review, and handoff.
Files: package/root README, ARCHITECTURE, CLAIMS, FUEL, WALKTHROUGH,
CAPABILITY_MANIFEST; repository master plan/requests register and
KNOWN-OPEN-ITEMS updates for this slice only; append-only DECISIONS;
this charter, the pre-launch/range reviews, one implementation record,
baseline/final signature snapshots and concise validation evidence.
Fix substantive review findings within this fence and repeat affected checks.

Frozen: `Step`, `Wps`, `Wpt`, `Soundness`, `Heap`, `Rules`, the Iris language
and coupling, other program proofs, all dependency pins and provider source.
No semantics re-pin, C-call/scheduler/seq_rmw work, t4/t5/t6 migration,
kill logic, procedure indices, extraction, or broad supply/fuel restatement.
The captured 36 and existing sufficient 50 are disclosed, not renamed into
claims of derivation. Startup restrictions remain empty globals/tag tables,
parameterless main, one TU, no libc, one sequential thread.

## Verification and process

- All Lean/build invocations use `scripts/capped`; memory cap 40G,
  heavy lanes serial. Scratch and logs remain inside this worktree's
  ignored Lake state; `TMPDIR` points inside the worktree. No writes to
  sibling repositories, no native proof reduction, no new axioms/sorries,
  no heartbeat/recursion-limit campaign.
- Take the baseline signature snapshot after a green full baseline gate.
  At completion classify the final diff: reusable additions, preserved
  old specializations, and the explicitly changed shipped t1 contract.
  Investigate every other existing-statement change; preserve old contracts.
- Pin the new public proof interfaces and consumer results at their actual
  exact axiom cones. Maintain the exhaustive audit. Do not manufacture trio
  dependencies for an axiom-free reconstruction proof.
- Existing clients and the old wrapper regression must still build. The
  concrete fresh frontend instance must pass all three checks, the independent
  data comparison, quotation comparison, and supply comparison. Negative
  tests must fail for the intended comparison, not merely an elaboration error.
- Before final handoff run the full capped gate and signature/axiom review.
  Record verbatim verdict tails, label derived counts, run the citation
  speedbump on edited claim documents, and independently review the complete
  range against this charter and AUDIT-BRIEF. Worker-claimed green is
  independently re-verified by the orchestrator.
- Charter and final core-document reviews use fresh reviewers as required
  by AGENTS.md. Bounded worker tasks may use separate worktrees with explicit
  ownership; the orchestrator controls heavy-build scheduling and integration.
- A required change to frozen semantics/judgments, unprovable promised
  statement, or a proof/build pass approaching an hour is a stop-and-report
  point. Preserve useful work on a parked branch if necessary. Routine
  in-fence adjustments and review fixes proceed under the user's autonomous
  execution authorization. A committed park record ends that slice.

Done means a committed, reviewed, green feature branch, with the remaining
frontend/excluded-fragment boundaries explicit. Merge and push require the
user's separate sign-off and are not part of autonomous execution.

## Pre-launch review disposition (2026-09-08)

[AGENT orchestrator] The [independent review](2026-09-08_review-whole-file-t1-charter.md)
is PASS for launch. C1 is applied: the fixture-independent capture/map/driver
machinery is distinguished from the captured-library adapter. N1 and N2 are
explicit requirements above (structural equality's dependency closure;
current main's R2 fragment/depth split). Baseline FULL gate exited 0;
selected audit lines and the final verdict tail, verbatim:

```text
info: CerberusHeapLang/Audit.lean:1123:0: CerberusHeapLang export pins: 906 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1123:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6479 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1123:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9679 constants of every kind swept, internal details included — count informational, environment-dependent)
ok:   CorpusT4Exhibit — 0 internals mentions
ok:   Examples.PartialClients — 0 internals mentions
BOUNDARY: 30 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

The baseline signature snapshot is
`cerberus-heaplang/docs/2026-09-08_whole-file-baseline.txt`, taken after
that gate. Source implementation starts after this disposition.


## Completion (2026-09-08)

All required results are implemented and committed on `demo-whole-file-t1`.
The [implementation record](2026-09-08_whole-file-t1-implementation.md)
contains adoption details, reusable versus captured-library interfaces,
parent verification, the strict unchanged-existing-signature census, and
remaining frontend/corpus limits. The [fresh full-range review](2026-09-08_review-whole-file-t1-range.md)
is PASS; its final confirmation at `a39efb0` closes all three documentation
Notes. The parent regenerated the manifest and passed the full capped gate
after those corrections; [verbatim validation](2026-09-08_whole-file-t1-validation.txt).
Main remains `7040406`, unmerged. A merge or push still needs the user's
explicit sign-off; completing this charter grants neither.
