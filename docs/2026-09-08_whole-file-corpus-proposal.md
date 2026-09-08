# Complete the whole-file migration for the supported C corpus

Status: PROPOSAL, [AGENT 2026-09-08], following the operator's question:
"Could we make this into a bigger coherent piece, eg. covering all our
remaining demo programs that we want to cover?" This expands the
[t5-first recommendation](2026-09-08_next-whole-file-slice-scout.md) into
one proposed V1-1b landing. No implementation charter is activated and no
merge is authorized. Baseline: main `4bc0a98`.

## Place in the overall arc

The master plan's four criteria are classical separation reasoning, a
faithful Iris foundation, adequacy over cerberus-lean, and genuine emitted
programs. The landed t1 slice establishes the reusable whole-file route
for the fourth criterion. Its capture/reconstruction, comparator checks
and actual-extern driver adequacy are available; the remaining three
already-certified C corpus entries still advertise synthetic wrapper files.

Recommended next outcome: **all four already-certified C corpus entries
(t1, t4, t5, t6) have complete-file certificates through a common emitted
integer support layer**. This completes the master plan's V1-1b migration
and its V1-1 program set at the accepted option-(b) executable frontend
boundary. It does not establish frontend correctness in the kernel or
finish the whole demo plan. Synthetic examples retain their separate role.

The following Phase-I work still includes seq_rmw (V1-2), freshness/cost
interface cleanup, symbolic integer storability and rule hygiene (V1-4),
kill adequacy (V1-5), and the expert exit review (V1-6). Calls belong to
V2-4 in the proposed ordering, but the recorded v1 disposition still waits
for E6; an earlier call-free v1a tag remains a proposed operator decision.

## Why all three migrations form one change

| Program | Existing proof to port | Contribution to the common route |
|---|---|---|
| t5_ifelse | Conditional, assignment, one return continuation | Establish annotation/type/operand-parametric integer support and assignment under actual extern lookup |
| t6_switch | Five registered continuations; case dispatch, break, return | Exercise the same integer support with a finite multi-label specification |
| t4_while | Four registered continuations; short-circuit guard, two assignments, loop invariant and decreasing budget | Exercise arithmetic, exact load footprints and total loop reasoning with the actual file |

The existing clients directly share `Examples.EmittedInt` load/store
lemmas. Those helpers hardcode the old type/symbol shapes and, for stores,
the three-function `StdE3` library. The new captured files need the same
generalization. T4 is the largest proof port, with its invariant and
budget rather than just another terminal computation; its legacy budget
is `t4Budget n = 159 * (5 - n) + 98` (CorpusT4Exhibit, declaration
`t4Budget`). Existing proof architecture is evidence of feasibility, not a
proof that the newly captured bodies satisfy the same derivations or costs.

The t5 scout identified one concrete proof-core amendment: `wpt_neg_bound`
requires constructor identity of every externally resolved symbol, while
the actual self-binding map supports comparison equality. Its sole use is
the final fresh-binder lookup. Generalize that derived rule narrowly using
`evalPexpr_sym_of_compare`, retaining the old theorem as a specialization.
The underlying judgments, mirror, soundness and semantics need no change
indicated by the inspected shapes. Any contrary finding is a scope review,
not permission to add new semantic features silently.

## Fresh feasibility checks

The parent generated fresh OCaml Cabs and ran the pinned Lean frontend,
linker and converter for t4 and t6 on 2026-09-08. The existing generic
inspector exported each complete file and independently compared data,
quotation, supply and the three comparator checks on the compared instance.
Both inspector runs exited 0. Complete JSON reports are retained in
`docs/evidence/2026-09-08_whole-file-expansion/`.

| Program | Captured frontend supply | Initialization's returned next supply | Sole observed Active value, fuel1000 |
|---|---:|---:|---|
| t5 (previous parent-run evidence) | 47 | 48 | Specified(1) |
| t6 (fresh) | 51 | 52 | Specified(20) |
| t4 (fresh) | 92 | 93 | Specified(10) |

All observations are unblocked with empty trace/stdout/stderr. These are
executions and comparisons, not new program correctness theorems. Fuel1000
is a probe setting, not a proposed theorem floor. Negative comparisons
were not run on t4/t6 in this scout; they remain acceptance work.

T4 and t6 each have empty globals/tags, parameterless normal main, 110
stdlib entries, six implementation entries and eleven funs/extern/funinfo
entries. Their entire stdlib AND implementation quotation blocks are
byte-identical to t1's. T4 additionally retains one loop-attributes entry.
`EmittedStdCore.hasIntLibrary_of_stdlib_data_eq` is the existing theorem
for transferring the captured integer-library contract; equality for the
new terms must still be established in the kernel during implementation.

DERIVED constructor inspection of the generated funs fields found four
`Esave` nodes for t4 and five for t6, matching the legacy continuation
counts, and no `Eccall` node. This does not replace exact-body `Frag` proofs.
The inspector's old `uncoveredKinds` diagnostic still labels expression
case/if nodes uncovered; it is not the authoritative fragment predicate.

Reproduction: run from the scout worktree root, first producing Cabs with
the read-only OCaml driver as in `scripts/check-emitted-t1.sh`, preserving
the relative `docs/corpus-e0/t4_while.c` / `t6_switch.c` source paths. Then
invoke `scripts/inspect-emitted-file.sh CABS REPORT 1000 DATA NAMESPACE`.
The actual runs used the already-primed `demo-whole-file-t1` worktree's
inspector, with outputs in the scout root's ignored
`.lake/whole-file-expansion-evidence/`; the scout itself had no pinned
workspace, and its initial `--check` correctly stopped before any Lean
run. Logs/data scratch are ephemeral; committed reports and this record
are the durable evidence. The inspector source is identical to main.

Oracle SHA-256:
`7d1778bba8defb85233c4be211ab9cbe4b32dae13cf4afc9de79fae3c9302cd4`.
Identity/prerequisites: main's `docs/corpus-a7/README.md`; no sibling edit.
The report data hashes identify the exact generated terms inspected.

## Implementation and acceptance boundary

One feature branch and one final range review/landing, with internal green
checkpoints in this order:

1. Shared emitted integer support: comparator-based variable lookup and
   assignment, actual annotations/types, library-contract-based conversions,
   loads, arithmetic and stores. Extract reusable t1 facts where appropriate;
   ordinary evaluation/memory premises keep generic rules independent of a
   particular fixture. Keep this outside positive-client modules.
2. Complete-file t5; then t6's collector/dispatch proof; then t4's
   collector/invariant/budget proof. Preserve old public signatures as
   regressions. Establish exact body/label membership, separate evaluator
   bounds, local symbol non-collision from actual captured supplies, and
   sufficient budgets justified by rule composition.
3. Complete-file actual-driver, capture-transfer and shipped corollaries
   for all three. Advertise this route for all four C corpus entries.
   Consolidate the small comparison runner over the four fixtures, update
   claim/A7/API/plan records and audit pins, and run the full capped gate,
   old-signature census and independent full-range review.

Acceptance is four complete-file certificates, shared support actually
consumed across programs, and fresh-data/comparator/supply checks with
targeted negative comparisons for the new fixtures. The final statements
run the genuine driver with each complete file and its captured supply;
the option-(b) boundary stays explicit. Do not substitute a run at one
large fuel for an all-sufficient-fuels theorem.

Keep the semantics/Lem/Iris pins, judgment definitions, Step/Round and
soundness fixed. Permit the narrowly justified derived-rule generalization
and supporting client lemmas. Do not fold in a scheduler re-pin, calls,
seq_rmw, tags/globals, the global FreshAbove/cost campaign or wrapper
retirement. In particular, retained wrappers leave their old `600` sites
in the historical census; this migration alone does not close V1-4a.

## What covering all ten programs would add

| Remaining corpus group | Required work in the master plan |
|---|---|
| t2, t3, t10 | C-call/return and scheduler adequacy (V2-4); t2 also uses i++/seq_rmw, and t3 needs PtrValidForDeref (V1-2/V2-6) |
| t9 factorial | Recursive call under unseq and outcome-list adequacy (V2-4/V2-5) |
| t7 struct | Actual nonempty tag tables and struct access (V2-3) |
| t8 array | Emitted array/dereference shapes (V2-6) |

These dependencies are visible in the C sources, `pendingCorpus`, and
master-plan §4.2; this proposal does not assert the provider-side unlocks
have already been adopted. All ten can be an umbrella arc, with separate
semantic landings. The next coherent landing recommended here is the full
V1-1b cohort, which closes one specific remaining boundary for every
already-supported C corpus program.
