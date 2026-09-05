# Demo completion charter — 2026-09-05

Status: **DRAFT for adoption by the user's explicit goal command**.
The two goals and continuation through E5 and beyond are already
user-authorized. The completion criteria and execution plan below are
[AGENT] proposals implementing that scope; this document does not start
a goal, grant merge/push permission, or claim any milestone complete.

## Objective and scope

[USER]: "our intended near-term stop-state is that our 'demo'
Reynolds/O'Hearn logic is (1) good, clean, well-defined in every way, a
good demo exemplar, and (2) it works on real emitted core produced by
cerberus."

Deliver a reviewed, fully validated, merge-ready version of
`cerberus-heaplang` satisfying both goals. Work belongs to
**refined-cerberus**. Sibling repositories are dependencies and read-only
references; required upstream changes are recorded as concrete requests.

The product is classical sequential separation logic over a precisely
declared fragment of genuine Cerberus Core. Its adequacy results must
refer to the shipped cerberus-lean semantics. Raw emitted Core is the
program referent; a privately simplified or sequentialised replacement
does not discharge an emitted-program acceptance item.

RefinedC, richer invariant masks, general function-pointer logic,
concurrent C, external calls, and coverage of all Core are outside this
charter. Direct emitted C calls and their scheduler protocol are inside
it. The struct example t7 remains deferred to the existing tag-definition
work; t8's array support is part of the agreed emitted corpus. Preserve
authored examples as regressions until equivalent emitted examples cover
their claims. Coupling-library extraction and RefinedC follow this demo.

## Starting point

At drafting, local main is `c2ebeb7` with E1–E4. Active work is branch
`dialect-e5`, worktree `worktrees/dialect-e1`, at `1d04dd7`; it is clean
and unmerged. The semantics pin is `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`
and Lean is 4.32.2. These are baseline facts, not pins to retain forever.

- Generic driver adequacy, operational-mirror completeness for the
  declared fragment, and memory well-formedness preservation are
  established under the documented assumptions. Mirror completeness and
  availability of public proof rules are separate claims.
- t1 has emitted-term membership, public logic proofs and a production
  theorem returning `Specified(4)`. t5 now has whole-term membership, a
  public total proof and a production theorem returning `Specified(1)`;
  its initial symbol supply is explicitly bounded below by 600.
- The full gate passed at the t5 checkpoint, with 779 exact classical-trio
  pins and the exhaustive axiom sweeps. Counts are evidence of the audit
  discipline, not a measure of semantic coverage or completion.
- E5 acceptance and its complete range review remain open. Both emitted
  certificates still use a constructed file with a three-function
  standard-library fragment and an empty implementation map (KOI A7).

The [E5 resume record](../cerberus-heaplang/docs/2026-09-05_e5-resume.md)
owns the detailed baseline and gate evidence. The historical handoff and
old dependency scout estimates are not current forecasts.

## Completion criteria

All five criteria must be satisfied for technical completion. Track their
evidence in the milestone records and final acceptance report.

### 1. Coherent logic and theorem assumptions

- Preserve the three foundational results as the fragment grows. Rules,
  mirror steps, memory invariants and adequacy must agree with the engine.
  Retain the kernel-only proof policy and declared axiom boundary.
- State the supported fragment and residual cases precisely. Unsupported
  cases remain visibly unsupported; adding fragment membership alone
  does not establish a public rule or a program proof.
- Give fuel, freshness, initial-state, file, tag and external-environment
  assumptions one consistent account across definitions, exports and
  documentation. Review E5's seeded supply normalization explicitly.
- Partial correctness must state which outcomes it permits and how fuel
  exhaustion is classified. Total correctness must establish successful
  termination with sufficient budgets. A singleton equation is used only
  where justified; multiple outcomes must all satisfy the stated result.

### 2. Emitted corpus certified through public rules

The acceptance set is **t1–t6, t8–t10**, retaining t7's existing deferral.
Each required example must have a reproducible emitted fixture, membership
for the whole retained term, a public-rule derivation, and an adequacy
result over the shipped execution path. Keep both branches, cleanup and
other emitted structure even when the concrete run does not visit them.

Use total proofs for the terminating deterministic examples and the
appropriate all-outcomes theorem for t9. Specify result values, failure
classification and any claimed execution-state properties. Record oracle
measurements with their actual version separately from proved facts.
Revalidate t1 and t5 after changes to the pin, file or adequacy machinery.

Every public rule advertised as demonstrated needs an actual client at
the advertised partial/total level. Resolve the E5 partial-face gap with
useful clients or an explicit, reviewed API/coverage disposition; do not
invent duplicate examples merely to improve a count.

### 3. Faithful emitted-file and library connection

Close KOI A7 for the acceptance corpus. The production certificates must
apply to the actual emitted file and the library/implementation behavior
it uses. The present three-function wrapper and skeleton comparison alone
do not meet this criterion: the recorded out-of-range conversion already
distinguishes that wrapper from the full pipeline file.

The pipeline's whole file remains the preferred theorem referent.
The existing [USER] ruling also permits a hand-transcribed term with an
executable equality check at a clearly declared boundary. Accordingly,
either certify the full emitted file directly or certify a faithful full
file transcription with that check. A smaller file can qualify through a
proved preservation bridge to the actual file for the certified programs.
Preserve the distinctions between these forms in all claims.

The comparison must account for semantic content, including literals,
types, symbol bindings, annotations, procedures and relevant file/library
maps. Any renaming or other transformation needs an explicit justification;
constructor skeleton agreement alone is insufficient. Record generation
commands, input artifacts and exact dependency versions so the comparison
can be reproduced. An executable check remains a test, not a theorem.

This criterion does not require proving the C parser or compiler correct.
The boundary between C input, emitted Core and the theorem's object must
be explicit. If the file connection cannot be completed, record it as an
unmet criterion; do not silently redefine the goal to accept the wrapper.

### 4. A readable, maintainable exemplar

Present a short, reproducible path from an emitted program to its public
logic proof and production theorem. Explain the Reynolds/O'Hearn rules,
memory model, supported fragment and assumptions in terms a new reader
can follow. Keep engine-specific proof plumbing below the client API
where it can be hidden without obscuring a necessary premise.

Resolve the relevant duplication and unused-helper queue, stale coverage
claims and citation drift. Review remaining known items individually:
close those required by this charter, and give the others accurate scope
and disposition. Avoid both an open-ended cleanup campaign and using
"known issue" status to excuse an unmet completion criterion.

### 5. Verified and reviewed candidate

The final candidate must pass the repository's full gate on its recorded
pins, with current coverage, transcription and boundary reports. Review
the full E5 range and subsequent substantive slices, then obtain a fresh
full architecture review under [AUDIT-BRIEF.md](AUDIT-BRIEF.md). Resolve
substantive in-scope findings and verify fixes before claiming completion.
A self-review or green build does not stand in for the fresh review.

Produce a final acceptance report mapping these five criteria and each
required corpus example to concrete evidence, naming residual limitations,
candidate commit, pins, validation commands and review records. Technical
completion means that report supports a merge-ready candidate. Actual
merge, version tagging and push retain their separate release decisions.

## Execution sequence and checkpoints

| Milestone | Work and exit evidence | Initial status |
|---|---|---|
| M1 — finish E5 | t6_switch and t4_while public proofs and production results; assignment protocol and whole-term membership; range review from `8eeaf92` through the completed E5 candidate, including supply normalization. | t5 checkpoint complete; E5 open. |
| M2 — dependency and fuel update | Fresh scout against landed upstream work; deliberate compatible re-pin; repair and restate affected proofs, fuel claims and failure classifications; full regression evidence. Record actual breakage instead of inheriting the old scout's estimate. | Open; perform before extending scheduler adequacy. |
| M3 — E6 | Complete `seq_rmw` for t2 and the queued operand/dereference/`Elet` requirements where needed; prove emitted `Eccall` scheduler rounds and adequacy; certify t2, t3, t10 and t8. Preserve authored-call regression coverage. | Open. |
| M4 — E7 | Cover t9's alternative scheduler paths, including deferred actions; prove the result for every outcome and non-emptiness with the stated fuel conditions. Account for all executions rather than selecting one successful branch. | Open; follows E6. |
| M5 — file integration and exemplar cleanup | Discharge criteria 3 and 4; re-certify the acceptance examples on the final file/library setup and reconcile all public claims. | Open; investigate the file seam during M2 and integrate it during E6, not only after E7. |
| M6 — final acceptance | Full verification, fresh review, finding fixes and the criterion-by-criterion acceptance report. | Open. |

Small changes to this sequence are ordinary implementation decisions when
they preserve scope and reduce rework. Record the reason. Scope reductions,
weaker trust boundaries or replacing a required example need an explicit
user decision. A dependency limitation warrants a measured request, not a
private substitute semantics. Do other independent authorized work while
such a request is pending.

## Long-cycle working agreement

- Work autonomously on feature branches in refined-cerberus. Commit
  coherent validated slices and continue to the next milestone. Routine
  checkpoints are not park records. Preserve user changes and keep main
  parked until the existing merge process authorizes movement.
- Use the fast tier for intermediate proof changes and the full tier at
  claim points and after material integration. Every Lean build goes
  through `scripts/capped`; select the package toolchain by running from
  `cerberus-heaplang/`. Heavy lanes run serially. Follow the existing
  stop-and-report rule for a proof/build pass approaching an hour.
- Maintain concise progress updates and durable resume records: current
  branch/head, pins, completed criterion, actual verification, open
  question or failure, and next concrete action. Do not repeat expensive
  checks without a change or unresolved concern that warrants them.
- Follow existing review and permission rules in [CLAUDE.md](../CLAUDE.md).
  Prepare concrete review briefs and validated candidates before an
  approval step. Pre-merge audit scope and scale, each merge and each
  push retain their existing user sign-offs. This charter grants no new
  permission to dispatch reviewers, modify sibling repositories or send
  messages externally.
- If a required decision or external change prevents a milestone,
  document the exact evidence and needed action; continue other useful
  authorized work. Report the goal as unfinished while any required
  criterion, review or finding fix remains. Elapsed time and exhausted
  budget are not completion evidence.

## Adoption and navigation

Suggested goal text:

> Complete the refined-cerberus demo according to
> docs/2026-09-05_demo-completion-charter.md, through a reviewed, fully
> validated, merge-ready candidate. Work autonomously within its scope,
> keep the charter's progress and evidence current, and respect the
> existing review, merge and push approval boundaries.

After explicit adoption, record the [USER] instruction in
[DECISIONS.md](DECISIONS.md), update this document's status and maintain
the milestone states. Adoption does not erase the baseline or rewrite
historical records. A goal command can provide its own execution budget;
this charter sets no duration or token allowance.

Source documents: [dialect design](2026-09-04_emitted-core-dialect-design.md)
§C.5–C.10 and the later rulings in DECISIONS;
[known open items](KNOWN-OPEN-ITEMS.md);
[architecture](../cerberus-heaplang/ARCHITECTURE.md), especially §6–§7;
and the E5 resume record linked above. The register's later user rulings
govern over older plans. This charter tracks completion; the architecture
remains the normative account of what the current implementation proves.
