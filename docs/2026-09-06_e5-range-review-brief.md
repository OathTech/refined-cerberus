# E5 full range review brief — 2026-09-06

Status: **DRAFT scope and dispatch proposal — user approval pending**.
[AGENT] Prepared after the t4 full gate. No reviewer has been dispatched
and this document is not a review result or a merge request.

## Candidate and proposed scale

Review **`8eeaf92..f60cdcf4779c48c8e04aeb6a539db3e05bb54365`** in
refined-cerberus. The candidate is on `dialect-e5`, worktree
`worktrees/dialect-e1`. Main remains parked at `c2ebeb7`. The semantics
pin is `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`, Lean 4.32.2 and
LemLib `045dcb0`; the range changes no dependency pins.

Proposed scale: **one fresh independent reviewer of the full E5 range**,
with a written findings report and explicit disposition of the partial
API question below. This covers E5's original protocol work, the resumed
rule/axiom fixes, all three emitted clients and the subsequent shared
helpers. It is not restricted to the latest t4 delta. Later substantive
slices and the charter's final fresh architecture review remain separate.

The range contains 19 commits and 71 changed files (git measurements).
Most inserted lines are the two historical signature snapshots. Use those
as diagnostic evidence where needed; assess live definitions and theorem
statements at the candidate. Do not infer correctness or coverage from
snapshot size, exact-pin counts or successful compilation alone.

Read [AUDIT-BRIEF.md](AUDIT-BRIEF.md),
[KNOWN-OPEN-ITEMS.md](KNOWN-OPEN-ITEMS.md), the later E5 rulings in
[DECISIONS.md](DECISIONS.md), and the
[active charter](2026-09-05_demo-completion-charter.md) first. Apply the
standing distinction between substantive logical/coverage findings and
optional hardening suggestions. Known gaps are not new findings unless
the record understates them or their promised mover has been missed.

## Questions the review must answer

1. **Protocol and engine agreement.** Trace the negative-store rewrite,
   exclusion id and fresh-symbol draws, excluded-store evaluation and
   discharge, nested annotation/race handling, and non-value case
   scrutinees through Step, Round, Soundness and DriverCollapse. Check
   fragment closure and classified refusals against the actual pinned
   engine. The `bound` congruence was unsound without a negative-free,
   within-fuel premise; verify the correction at every public face and
   downstream use, including the enclosing full-expression protocol.
2. **Judgments and state assumptions.** Review both Wps and Wpt, the
   supply lower bound and live control writes, call/return transport and
   adequacy. In particular, inspect seeded `procCtx`'s normalization of
   both supplies to zero against its public statements; production
   contexts retain their explicit initial supplies. An unchanged theorem
   text does not establish that a definition change preserves its meaning.
   Check the API fuel premise and static potential bounds as well.
3. **Public clients and whole emitted terms.** Review t5/t6/t4 ASTs,
   whole-term membership, engine label collection, parameter binding,
   public derivations and production equations. t5 returns 1 at budget
   88; t6 returns 20 at 78; t4 returns 10 at 915. All require initial
   supply at least 600. For t4, check the owned-cell invariant, arithmetic
   bounds, exact load footprints, RHS annotation lifetime, back-edge
   decrease, short-circuit exit, both kills and return. Distinguish
   sufficient proof budgets from minimal execution counts. Check all
   retained branches and dead cleanup, including registered continuations
   to which the concrete program never jumps.
4. **Shared rules and maintainability.** Review the shared emitted integer
   load/store helpers, annotated strong symbol binding, exact-footprint
   load faces and pure-left unsequenced helper. In the last helper the
   effectful right operand runs first; the left pointer is evaluated in
   its resulting frame. Check that factoring preserves existing t1/t5/t6
   claims and keeps engine-specific proof internals below the client API.
   Identify substantive readability/duplication issues for the charter's
   cleanup, without requiring duplicate client proofs merely for counts.
5. **Claims and trust accounting.** Check changed axiom pins and the
   sub-trio census, coverage witnesses, module classification, generated
   manifest and CLAIMS/README/ARCHITECTURE. Distinguish mirror coverage,
   public rule existence and actual partial/total consumers. Inspect the
   seven rows below and the scope of the production referent. The full
   emitted-file/library criterion A7 is explicitly open; the skeleton
   comparison does not establish semantic leaf identity or full-file
   equality. No M1 approval here may imply that A7 or the charter is done.

## Partial API/coverage disposition proposed for review

The seven `RULE-PARTIAL-UNDEMONSTRATED` variant rows cover these public
partial faces (the negative-round face serves two variants):

| Variants | Partial face | Current evidence |
|---|---|---|
| Exact whole-cell read footprint | `wps_load_footprint` | Proved; the total twin is used by the emitted load helper and t4's two-load addition. |
| Strong symbol binding at an annotated head | `wps_seq_sym_annot` | Proved; the total twin is used by t4's truth-conversion protocol. |
| Canonical/evaluating negative store (two rows) | `wps_neg_round`, with the derived `wps_neg_bound` interface | Proved; total faces are used by all three E5 clients. |
| Canonical excluded store | `wps_excluded_store` | Proved; total face used by the assignment derivations. |
| Evaluating excluded store | `wps_excluded_store_eval` | Proved; total face used by the assignment derivations. |
| Non-value expression-case scrutinee | `wps_case_eval` | Proved; total face used by the E5 clients. |

[AGENT proposal, not ratified] Retain these proved partial API faces and
retain the manifest's explicit undemonstrated classification. The corpus
requires total derivations for these terminating programs; deriving a
second almost-identical corpus proof would not by itself improve the
exemplar. Document the partial faces as proved but not demonstrated by
a partial client, without advertising coverage at that stratum.

The charter permits this **only through an explicit reviewed API/coverage
disposition**, as an alternative to useful partial clients. The reviewer
must assess whether this is an adequate exemplar and API decision, or
identify a meaningful partial client whose absence exposes a substantive
usability or coverage gap. Inspect the partial proofs themselves;
consumption of the total twin is not a substitute for that inspection.
Do not promote a manifest row or mark this question resolved merely by
accepting this brief. Any required client or documentation fix is work
remaining before M1 closes.

## Evidence and review output

The candidate's FULL gate is green. The exact commands and selected
verbatim output are in
[the t4 completion record](../cerberus-heaplang/docs/2026-09-06_e5-t4-loop.md).
It has 896 exact pins, exhaustive theorem/constant sweeps, zero red
manifest rows and zero boundary violations. The four corpus skeletons and
all applicable plants pass. The citation report has a disclosed manual
queue; assess cited claims from the source rather than treating that
report as semantic evidence.

Also read the linked t5 resume, t6, t4 condition/addition/body and original
E5 records. Use the public statements at the candidate as the referent;
historical notes remain point-in-time records.

Return a fresh full-range assessment, findings with severity and exact
source references, their effect on the declared claims, and concrete
remedies. State the disposition of seeded supply normalization, the
partial API question and whether E5 is acceptable within its disclosed
file boundary. Identify unreviewed areas explicitly. Do not rewrite
source or ratify the charter. Findings will be checked, fixed and
revalidated before any completion or merge claim.

Every Lean command remains capped and uses the package cwd/toolchain.
Heavy builds are serial; coordinate any fresh build with the primary
agent. The existing one-hour proof/build stop-and-report rule applies.
No merge, push, dependency update or sibling-repository write is part of
this review proposal.
