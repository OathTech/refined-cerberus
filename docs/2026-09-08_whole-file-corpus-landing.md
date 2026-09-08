# Whole-file corpus — landing review disposition and verification

Status: LANDED on main by fast-forward; full feature and primary gates
passed, review follow-ups recorded, completed worktrees cleaned up. [AGENT 2026-09-08].

The independent [landing review](2026-09-08_review-whole-file-corpus-landing.md)
of main `4bc0a98` through candidate `00db603` returned **PASS, A−**, with
no required pre-merge fix and no Critical, High or Medium finding. The
review is committed unchanged. The earlier [implementation record](2026-09-08_whole-file-corpus-implementation.md)
and [internal adversarial review](2026-09-08_review-whole-file-corpus.md)
retain the proof, comparison, exact axiom-cone and signature evidence.

[USER], verbatim in the working session:
> Review landed in docs, can you address any findings, and land it on main

This authorizes the review follow-ups and landing. It supersedes the
initial handoff's pending merge authorization. The external pre-merge
review has been supplied and accepted through this instruction; no new
permission question is required. No push is authorized.

## Review disposition

- **F1/F2 addressed in the master plan and known-item register.** The
  fourteen new numeral supply-floor premises are explicitly included in
  G1.1 and V1-4a, alongside the eighteen old `600` premises. T6 should use
  its captured `frontendSupply` in the bound; T5/T4 should derive the bound
  from the source-symbol numbers. G1.9 and V1-4a also explicitly retain the
  complete-file exports' 50/90/80/917 fuel bounds in the named-cost work.
  KOI B19 records the expanded class. The review grades the current
  statements as sound, discharged and nonblocking; this landing preserves
  their signatures. No numeral-floor cleanup is claimed to have occurred.
- **F3 addressed by the branch register and completed worktree cleanup.**
  All ten named auxiliary refs are now explicitly superseded in master
  plan §2. The earlier three t1 worker refs were already registered and
  their worktrees removed at the t1 landing; the new entry adds the four
  corpus workers, final reviewer, scout and completed t1 feature ref.
  The refs remain as provenance. Their seven clean, completed worktrees
  were removed normally after landing; unrelated worktrees were excluded.
- **F4 considered and deferred.** Printing a shared preamble once is an
  optional log/readability change, with no correctness or coverage gap.
  The external review measured a 78-second full gate and 165 repeated /
  33 distinct demo warning lines. Keep the independently reviewed runner
  intact for this landing; consolidation may accompany later tooling
  hygiene. No extra check or caching mechanism is introduced.
- **F5 acknowledged.** The positive finding confirms the narrow
  comparison-premise generalization and unchanged previous signatures.

The parent independently recounted premise declarations, excluding
occurrences inside proofs. DERIVED: T5 2 + T6 3 + T4 9 = 14 new sites;
18 old + 14 new = 32 total numeral supply-floor premise sites. The source
has not changed since `00db603`:

| Module | Premise | Theorems |
|---|---|---|
| EmittedT5Exhibit | `22 < …` | `mainBody_wpt`, `mainBody_driver_done` |
| EmittedT6Exhibit | `51 ≤ …` | `wpt_case2`, `blockSpecs_valid`, `mainBody_driver_done` |
| EmittedT4Exhibit | `22 < …` | `wpt_assignS`, `wpt_assignI`, `wpt_body`, `wpt_loopStep`, `wpt_whileCont`, `blockSpecsT_main`, `wpt_whileEntry`, `wpt_main`, `mainBody_driver_done` |

The complete-file `certified_production` statements use the exact captured
supplies and discharge these helper obligations; their root-of-trust
statements have no new supply-floor premise. The capture-transfer twins
retain their exact captured-supply equality. This bookkeeping does not
broaden the four-program option-(b) result.

## Verification and landing

All edits for this follow-up are made in `worktrees/demo-whole-file-corpus`.
No Lean source, test script, dependency pin or sibling repository changes.
The full feature gate, primary fast-forward and full primary gate are
recorded below with their actual outcomes. Ignored logs live in
each checkout's root `.lake/whole-file-corpus-landing-evidence/`; useful
excerpts here are the durable evidence.

The pinned-workspace check passed before the feature gate, including the
sync stamp and all 37 hand-written seams at pin
`89f7e688530c6910884518811d645e4e892e4507`. Static `git diff --check`
passed; the diff from `00db603` contains only documentation. No new
file:line citations were introduced. The citation speedbump ran on the
seven affected documents: the sole NOFILE row is the pre-existing
append-only DECISIONS historical reference to line101 of CLAUDE.md; KOI's two
old declaration suggestions and pinned-source rows also predate this
landing. They were inspected and left as historical records, rather than
reported as a newly empty citation queue.

### Feature gate

From the feature worktree root:

```bash
CERB_MEM_MAX=40G TMPDIR="$PWD/.tmp" scripts/test_unit.sh \
  > .lake/whole-file-corpus-landing-evidence/feature-gate.log 2>&1
```

Exit0. Selected verbatim output (intervening build diagnostics omitted):

```text
ok: no banned proof-method references
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (77 files scanned, comments stripped)
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang export pins: 991 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (7356 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (11097 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: capability manifest regenerated, no drift
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
whole-file corpus: OCaml oracle SHA-256: 7d1778bba8defb85233c4be211ab9cbe4b32dae13cf4afc9de79fae3c9302cd4
whole-file corpus: OCaml oracle version: git-cn-pin-720-g9a7f7ad31
ok: whole-file t1 — fresh Cabs matches retained fixture
ok: whole-file t1 — metadata, all three comparator checks and singleton return 4 checked
ok: whole-file t1 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t5 — fresh Cabs matches retained fixture
ok: whole-file t5 — metadata, all three comparator checks and singleton return 1 checked
ok: whole-file t5 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t6 — fresh Cabs matches retained fixture
ok: whole-file t6 — metadata, all three comparator checks and singleton return 20 checked
ok: whole-file t6 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t4 — fresh Cabs matches retained fixture
ok: whole-file t4 — metadata, all three comparator checks and singleton return 10 checked
ok: whole-file t4 — independent structural data, quotation, supply and negative checks passed
ok: complete-file corpus comparison and negative checks
ok: import direction — 19 core modules, none imports an exhibit/example/production module
BOUNDARY: 44 modules checked, 0 internals mention(s) in total, exit=0
ALL GATES GREEN
```

DERIVED: 165 demo warning occurrences / 33 distinct, unchanged baseline;
zero UNCAPPED reports. All four fresh Cabs, structural/quotation/supply,
original-comparator and main/supply negative checks passed. No tracked
change was produced by the gate. The source/API signatures remain those
independently reviewed at `00db603`; landing changes only documentation,
so the committed 5,569 → 6,081 census remains 512 added / 0 removed /
0 changed without regenerating an identical snapshot.

### Primary landing and verification

The primary checkout was clean at main `4bc0a98`. Its pin/stamp and all
37 hand-written seams passed the pinned-workspace check. The authorized
`git merge --ff-only demo-whole-file-corpus` advanced main to `2f6f2ab`,
including the unchanged external review and the dispositions above.

The same full-gate command ran from the primary root, with its output in
`.lake/whole-file-corpus-landing-evidence/main-gate.log`; exit0. The primary
rebuilt the affected library modules, then ran every full-gate speedbump.
Selected verbatim output:

```text
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang export pins: 991 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (7356 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1233:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (11097 constants of every kind swept, internal details included — count informational, environment-dependent)
ok: capability manifest regenerated, no drift
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
whole-file corpus: OCaml oracle SHA-256: 7d1778bba8defb85233c4be211ab9cbe4b32dae13cf4afc9de79fae3c9302cd4
whole-file corpus: OCaml oracle version: git-cn-pin-720-g9a7f7ad31
ok: whole-file t1 — fresh Cabs matches retained fixture
ok: whole-file t1 — metadata, all three comparator checks and singleton return 4 checked
ok: whole-file t1 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t5 — fresh Cabs matches retained fixture
ok: whole-file t5 — metadata, all three comparator checks and singleton return 1 checked
ok: whole-file t5 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t6 — fresh Cabs matches retained fixture
ok: whole-file t6 — metadata, all three comparator checks and singleton return 20 checked
ok: whole-file t6 — independent structural data, quotation, supply and negative checks passed
ok: whole-file t4 — fresh Cabs matches retained fixture
ok: whole-file t4 — metadata, all three comparator checks and singleton return 10 checked
ok: whole-file t4 — independent structural data, quotation, supply and negative checks passed
ok: complete-file corpus comparison and negative checks
ok: import direction — 19 core modules, none imports an exhibit/example/production module
BOUNDARY: 44 modules checked, 0 internals mention(s) in total, exit=0
ALL GATES GREEN
```

DERIVED: 165 demo warning occurrences / 33 distinct, the existing baseline;
0 UNCAPPED reports. All four complete-file comparisons and targeted
negatives passed. No tracked change resulted from the primary gate.
No merge commit, push or tag was made; no provider source or pin changed.
The closing record commit is authored in the feature worktree and then
fast-forwarded onto main under the same landing authorization. It changes
only documentation; source and gate scripts remain those verified at
`2f6f2ab`.

### Completed worktree cleanup

After the fast-forward, each of these seven worktrees again had an empty
`git status --porcelain=v1`; normal `git worktree remove` succeeded for
all seven, without force:

- `worker-whole-corpus-charter` at `bf88f83`
- `worker-whole-corpus-t4` at `2584247`
- `worker-whole-corpus-t5` at `5f2c045`
- `worker-whole-corpus-t6` at `eaf2e15`
- `review-whole-file-corpus` at `33c5577`
- `scout-next-whole-file-slice` at `2f180e8`
- `demo-whole-file-t1` at `4bc0a98`

Their refs remain at the registered heads. The three older t1 worker
worktrees were already absent, as recorded in that slice's landing note.
The current corpus feature worktree remains available for the closing
record and all unrelated worktrees were retained. Useful worker/reviewer
results were already committed; their ignored scratch logs were ephemeral.
