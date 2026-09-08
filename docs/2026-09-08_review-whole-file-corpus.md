# Fresh adversarial review: complete-file corpus

**Verdict: PASS.** No substantive logical or coverage gap found in the
whole V1-1b range. One documentation Note was corrected during review;
there are no outstanding review fixes. This is a reviewed candidate for
external review, not merge, push or tag authorization.

[AGENT 2026-09-08] Independent final reviewer, briefed to try to falsify the
claims in the [charter](2026-09-08_whole-file-corpus-charter.md), using the
mandatory [audit grading](AUDIT-BRIEF.md) and [known-item register](KNOWN-OPEN-ITEMS.md).
Read repository and container practices and the implementation record.
This review covers the entire implementation,
not just the last checkpoint or the documentation correction.

## Reviewed range and isolation

- Main baseline: `4bc0a98a686dffc2377d4980108080f04cc8efad`.
- Initial feature candidate: `bc2b147`; dedicated review HEAD `b5fad959`.
  Independently verified identical tracked tree:
  `637f37c709a1284241cce474f270a36377e91dad`.
- Final feature candidate: `208194dd9be0fbc9f7cc3e9c15f5f5fba1cffdb5`,
  the documentation correction for N1. Inspected its complete diff and
  adopted it as review commit `e89881d`. Both trees then equalled
  `96de2a6db739cf5674345e30129f543aeed9bacf` before this report.
- All execution and scratch were confined to
  `worktrees/review-whole-file-corpus`. Sibling trees were read-only.
  The parent granted the serial heavy lane; all Lean/Lake commands ran
  from this worktree's `cerberus-heaplang`, through `../scripts/capped`,
  with `CERB_MEM_MAX=40G` and worktree-local `TMPDIR`.

The semantics/toolchain/dependency pins and frozen
Step/Round/Soundness/Fragment/Heap/Lang/Wps/ProdEntry/ProdLoop files have
no diff against baseline. The only core-rule modification is
`wpt_neg_bound_compare` and preservation of the old specialization in Wpt.
No native proof reduction, admission, axiom addition, or heartbeat/recursion
limit increase was found in the new proof modules.

## Finding and disposition

**N1 — Note, corrected: T6's supply premise was described incorrectly.**
The initial `../cerberus-heaplang/ARCHITECTURE.md:524` and
`../docs/2026-09-08_whole-file-corpus-implementation.md:157` said all three
new body proofs used `22 < M.runState.sym_supply`. T6 instead uses
`51 ≤ M.runState.sym_supply` in `EmittedT6Exhibit.lean:341` and `:393`,
and `51 ≤ sup` in `:684`. Its `mainBody_wpt` (`:533`) has no supply
premise: it transfers to the label specification before the assignment.

This did not invalidate the promised execution at captured supply 51,
nor reveal a vacuous rule or missing program coverage. The narrower
helper premise is sufficient for the same two source-pointer
non-collisions. Under the standing grading this is a factual documentation
Note, not a new general-supply obligation. Commit `208194d` now distinguishes
T5/T4's 22< from T6's sufficient 51≤ and its label-based proof. I inspected
the correction; it changes no theorem contract. N1 is closed.

## Logical and coverage checks

**Whole files and theorem referents.** Each new `Data` term retains all
eleven file fields and exact optional map trees, including the full linked
stdlib and implementation data. `EmittedFile.lean:66`/`:71`/`:81` capture
data, capture the original eight comparators, and restore the file;
`:94`/`:106` prove reconstruction. The new main bodies are projections
from those retained function trees, not the old CorpusE0 bodies. Their
exact annotated shape equalities are `EmittedT5.lean:282`,
`EmittedT6.lean:271`, and `EmittedT4.lean:317`.

The new production statements are at `EmittedT5Exhibit.lean:688`,
`EmittedT6Exhibit.lean:719`, and `EmittedT4Exhibit.lean:1666`. Each states
an equation over genuine `drive`, `initial_driver_state`, and
`CerbND.runND`, with arbitrary `fs` and `args`, singleton Active output,
the advertised value, unblocked status, and empty trace/stdout/stderr.
Each `_of_capture_eq` twin retains complete data equality, exact supply
equality, and checks on the original file's captured comparators. The
three new Shipped forms (`Shipped.lean:332`, `:354`, `:376`) instantiate
execution fuel only. No synthetic driver or execution transcription
replaces the exported engine run.

I traced these statements through `prod_run_eqJ_file`
(`ProdEntry.lean:950`), its genuine startup theorem (`:771`), and
`wpt_driver_done_alloc_extern` (`ProdLoop.lean:551`) to the actual
per-thread driver equation in `DriverDoneAtExtern` (`:63`). The clients
supply the allocation-aware public total derivation and label contracts;
body/continuation `Frag` and evaluator-depth hypotheses are separately
discharged. No circular delivery premise remains at the final exports.

**Original comparators, externs and nonvacuity.** Each main-lookup check
uses its captured function tree. The stdlib equality and
`HasIntLibrary` derivation connect all three programs to the captured
library under its lookup checks. Each label-union check controls the
actual union's comparison decisions before the reference collector
equality is used. The fold and collected contexts remain intact.
The runtime extern is the real singleton main self-binding, with a
proved equality to `create_extern_symmap`, not an empty replacement:
`EmittedT5.lean:88`, `EmittedT6.lean:87`,
`EmittedT4.lean:89`.

The fresh executable comparisons passed on all four actual frontend
instances, including the comparator checks on the very instance compared
to retained data. Thus these are not merely assumed checks with no
observed satisfying instance. These executable facts are not Lean proofs
of the original frontend's data/supply equality premises.

**Collectors and control.** T5's sole return continuation is exactly
`mainBody_saves`/`returnQ` (`EmittedT5Exhibit.lean:306`/`:303`). T6's
`Q_eq` (`EmittedT6Exhibit.lean:54`) retains all five case1/case2/default/
break/return continuations and suffix contexts. T4's `Q_eq`
(`EmittedT4Exhibit.lean:39`) retains all four continue/while/return/break
continuations. Lookup inversions establish fragment/depth coverage for
every registered continuation, including unreachable jump targets.
The concrete reference-collector and Q equalities use ordinary
kernel-checked reflexivity terms submitted by synchronous `mkAuxLemma`;
the device does not manufacture a success equation by native evaluation.

The selected execution proofs cover the actual constant programs:
T5 initializes x=3, takes the true branch, assigns 1 and cleans up;
T6 initializes x=2/r=0, dispatches to case2, assigns 20, jumps to break,
cleans up, and returns. T6 does not claim executions through case1 or
default; their syntax and actual registered continuations remain covered.

**T4 invariant, races and termination.** `SourceFrame`
(`EmittedT4Exhibit.lean:431`) preserves the two source-pointer lookups;
`:814` proves preservation under generated symbols above 22. The two-load
`s+i` proof (`:695`) follows the real unsequenced evaluation and retains
both exact read footprints; its completion uses `do_race_loadFootprint`.
The assignments use the exclusion-aware negative-store rule, not erased
or sequentialized read/write effects. Both owned cells are killed before
the jump to the real return continuation (`:1172`); dead emitted cleanup
is retained in the syntax.

The invariant (`:1147`) owns i=n and s=sum(n), with n≤5 and the recurrence
`sum(n+1)=sum(n)+n` (`:1109`). The actual short-circuit guard agrees with
n<5 on these invariant states (`:1123`). The budget
`159*(5-n)+98` (`:1140`) decreases by 159 per back edge; the body proves
the next label precondition at the smaller budget (`:1279`). The n=5
exit is proved separately (`:1325`), including saves, load, cleanup and
return. `blockSpecsT_main` (`:1383`) validates reachable jumps; `wpt_main`
(`:1462`) composes two allocations/initializations with loop entry.

| Program | Captured supply | Public total budget | Sufficient execution fuel |
|---|---:|---:|---:|
| t1 | 36 | 48 | 50 |
| t5 | 47 | 88 = 17+55+16 | 90 |
| t6 | 51 | 78 = 20+58 | 80 |
| t4 | 92 | 915 = 20+895 | 917 |

These are composition bounds, with explicit weakening where used, not
minimality claims. The exports quantify every sufficiently large ambient
execution fuel; they do not rely on the inspector's fuel 1000 observation.

**Shared support and preserved interfaces.**
`EmittedIntSupport.wpt_boundLoad` (`EmittedIntSupport.lean:73`) is
parameterized by annotations, cell type, memory order, fraction,
evaluated pointer lookup, loaded value, memory trap premise and exact
footprint. `wpt_intAssign` (`:114`) keeps evaluated operands and signed
range/storability premises. Actual T5/T6/T4 consume both interfaces;
multiple programs consume the literal-right unseq rule (`:143`). T1
retains its public types while consuming the shared symbol/type facts.
The existing intrinsic conversion/addition lemmas (`IntRules.lean:205`,
`:215`) have real T1/T4 consumers (`EmittedT1Exhibit.lean:256`,
`EmittedT4Exhibit.lean:626`), distinct from the captured-library adapter.

In `Wpt.lean:4860`, the extern-identity requirement is weakened only to
comparison equality. The sole affected operation is the final lookup of
the fresh binder (`:4960`); all assignment, exclusion, memory and budget
premises remain. `wpt_neg_bound` (`:4967`) restores the exact original
public contract by specialization. The unchanged-signature comparison
also covers all old wrapper and shipped statements.

## Independent execution evidence

All commands below completed successfully in the review worktree. The
full gate used primed dependency/package caches; it was not a cold rebuild
of the semantics or Iris. I additionally elaborated the seven new
support/body/proof sources directly, without using their cached source
build results, and freshly elaborated Audit.

```bash
# Worktree root; the script enters the package before every Lean/Lake call.
CERB_MEM_MAX=40G TMPDIR="$PWD/.tmp" scripts/test_unit.sh
# Package directory; same cap and worktree-local temporary directory.
CERB_MEM_MAX=40G TMPDIR="$PWD/../.tmp" ../scripts/capped "$HOME/.elan/bin/lake" env lean CerberusHeapLang/Audit.lean
CERB_MEM_MAX=40G TMPDIR="$PWD/../.tmp" ../scripts/capped "$HOME/.elan/bin/lake" env lean scripts/signature_snapshot.lean
```

The direct source-elaboration lane ran the same capped `lake env lean`
command serially for `EmittedIntSupport`, `Examples/EmittedT5`,
`Examples/EmittedT6`, `Examples/EmittedT4`, and the three corresponding
Exhibit modules. All seven exited 0 with no Lean warnings/errors.
The cohort checker separately compiled each retained Data source for its
fresh comparison. No limit was raised.

Selected **verbatim** fresh audit output:

```text
CerberusHeapLang export pins: 991 trio-exact, 7 propext-exact, 7 axiom-free-exact
CerberusHeapLang axiom sweep: every theorem bounded by the trio (7356 swept, internal details included — count informational, environment-dependent)
CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (11097 constants of every kind swept, internal details included — count informational, environment-dependent)
```

The full gate ended with `ALL GATES GREEN`. For each of t1/t5/t6/t4 it
regenerated Cabs, compared complete structural data independently of
quotation, checked exact supply and original comparators, rejected the
intended main/supply perturbations, and observed the advertised singleton
outcome. The compared OCaml artifact reported SHA-256
`7d1778bba8defb85233c4be211ab9cbe4b32dae13cf4afc9de79fae3c9302cd4`,
version `git-cn-pin-720-g9a7f7ad31`, matching the fixture record. The pinned
workspace checks also reported all 37 handwritten seams identical.

The fresh signature snapshot is byte-identical to the committed final
snapshot. An independent Python comparison of exact declaration blocks
derived **5,569 baseline / 6,081 final; 512 added / 0 removed / 0 changed**.
The existing 18 old `600` code premises remain; the three additional
textual occurrences are explanatory comments. There are 17 shipped
theorem declarations. Full-range `git diff --check` passed.

Ephemeral logs are in `.lake/review-whole-corpus/` of this review worktree;
this report records the useful results. The only post-verification change
to the candidate is N1's inspected two-document correction.

## Limits and remaining boundaries

The reviewed claim is option (b) for the four supported programs. The
frontend, native digest seam, quoter and executable comparisons remain an
explicit external connection to C; the kernel proves reconstruction and
execution of the retained files. Capture/comparison fuel is fixed 50 for
t1 and 1000 for T5/T6/T4, separately from universally quantified execution
fuel. I found no claim that these observations prove frontend correctness
or equality with OCaml printed Core.

The generated payloads were checked by fresh complete structural and
quotation comparisons, kernel-checked main projections, and field/shape
inspection; they were not manually audited line by line. The unchanged
semantics, Iris and full historical proof base were not re-audited from
scratch. The existing external OCaml build is unpinned and was identified
by its observed hash/version, not rebuilt. No arbitrary frontend-fuel,
arbitrary-library, out-of-range implementation-call, global/tag, scheduler,
or six-unsupported-program theorem was inferred. The old wrapper/file
boundary, old 600/fuel-cost restatement and other known items remain owned
by their existing records. No new hardening machinery is required by this
review.

The prepared status-only closure diff for the charter, implementation
record and master plan was also read before report completion. It accurately
records this verdict, N1's disposition, and the pause for external review;
it does not alter the verified implementation or expand its claims.
