# Branch survey and landability assessment — 2026-09-07

Orchestrator [AGENT], at the operator's request: "find all branches, figure
out what's on each of them, and make an assessment of what could be landed
(perhaps with some work). The agent-built branches are messy and a bit off
target so treat them skeptically." Method: `git for-each-ref` survey against
main c2ebeb7; the orchestrator's own FULL gate on both agent-built heads
(verbatim tails below); two fresh Fable-class skeptical auditors on fixed
detached copies, each with a landability brief (reports:
`docs/2026-09-07_landability-dialect-e5-extension.md`,
`docs/2026-09-07_landability-demo-repin.md`). Nothing merged, nothing
deleted; these are recommendations for the operator.

## 1. The survey (26 local branches; remote `origin/main` = 04059dc, behind local main)

| Class | Branches | Disposition |
|---|---|---|
| Fully merged into main (ahead 0) | audit-response-3/4, calls-c1, design-kill-calls, design-refinedc, draft/rules-of-engagement, fragment-closure, fuel-design-review, heaplang-alloc-arc, kill-free-k0/k1/k2, main-share, mirror-completeness, parametric-spike, refinedc/dev, repin-fuel, demo-fuel-t1 (= main, empty) | Labels on history; deletable at the operator's call (records live in main's dated docs). |
| Unmerged records, superseded or parked by ruling | lane-b-seed (3; parked unmerged by [USER] ruling), repin-scout (1) and repin-scout2 (1; both superseded by the actual re-pin on demo-repin), charter-aims-amendment (4 commits from 2026-08-30: a charter rev 3 + a compositionality critique that never landed anywhere and predate the semantics-first split) | Keep lane-b-seed; the scouts and charter-aims-amendment are archive material: delete or leave, no landing. |
| The other agent's work | `dialect-e5` at cb46e4c (14 commits past the orchestrator's park f433820); `demo-repin` = `parked/demo-expansion-2026-09-07` at a41292d (44 more) | Assessed below. |

## 2. `dialect-e5` extension (f433820..cb46e4c) — E5 completed

Orchestrator FULL gate at cb46e4c: 896 pins trio-exact, manifest no drift
(77 rows / 0 red), corpus skeleton ok, import direction 18 core modules,
`BOUNDARY: 29 modules checked, 0`, `ALL GATES GREEN`, warnings 48.

Auditor verdicts: t5 LANDABLE AS-IS; t6 LANDABLE AS-IS; t4 LANDABLE WITH
WORK (KOI state line; 324 units of undisclosed budget slack — 915 vs
PROGRAM-DONE at 593 — to KOI B6; layering smells); the charter docs
LANDABLE WITH WORK on PROVENANCE (their DECISIONS draft calls the
actual-file closure and the re-pin "already authorized" — neither was
ruled; they are [AGENT] scope adopted through the operator's goal command;
a `[USER, paraphrase]` permission needs verbatim or an [AGENT] reading);
the review brief and the dependency/fuel note LANDABLE AS-IS (every
factual claim verified against the sibling repos), with one operator
decision: its "target the current clean head" contradicts KOI A6's [USER]
"waits for the next pin". Nothing OFF-TARGET or REJECT. All three
certifications verified: verbatim transcriptions (leaf-by-leaf), kernel
`Frag`, oracle agreement (t5 → 1, t6 → 20, t4 → 10), the ONLY pre-existing
statement text change in the range is `load_atomic` (strengthened, reason
recorded). Process fact: the range worked past a committed park record;
the operator has since said the agent was authorised — to be recorded
verbatim with the landing.

Required before a merge ask (ranked): (1) provenance retractions in the
charter/DECISIONS text; (2) a candidate-head census snapshot (auditor's
own: slice-1 post → HEAD 372/2/18); (3) record truth (KOI state line, the
600 supply floor "sufficient not necessary", B6 slack rows, §2.5 cites);
(4) two unruled decisions carried forward for the operator: the seeded-
supply normalisation (E5 §S2.5) and the re-pin target; (5) the full E5
range audit 8eeaf92..HEAD owed by the park's own rule (this assessment
covers f433820..cb46e4c only). Size: S–M, docs and one snapshot.

## 3. `demo-repin` (cb46e4c..a41292d) — re-pin + actual file + E6/E7 + seq_rmw

Orchestrator FULL gate at a41292d (dependency check at the new pin
89f7e68: 37 seams byte-identical): 958 pins trio-exact + 7 "axiom-free-
exact" (a new pin class that keeps exactness), manifest no drift, corpus
skeleton ok (t1/t4/t5/t6), import direction 18, `BOUNDARY: 33 modules
checked, 0`, `ALL GATES GREEN`, warnings 2.

Auditor verdicts, by group:
- **G1 the re-pin** (8 commits + docs; the LemLib representation AND the
  fuel-parametric semantics arrive together in cerberus-lean 89f7e68 — not
  separable after the fact): LANDABLE WITH WORK (M) as ONE forced slice.
  Done right: `SymMap = Fmap.WF symCmpK` via upstream `LemLibPmapLaws`;
  `killM_killed_inv` 3 → 7 rows; ZERO fuel numerals or retired constants
  in code; closed partial forms genuinely over `drive` at the ambient (KOI
  A2 closes). Deviations to weigh: the `pot`/`hQpot` premises DELETED and
  the operand bound moved INTO a fuel-relative `Frag [LemFuel]` with a
  `2 ≤ LemFuel.fuel` floor (differs from `2026-09-04_fuel-restatement-design.md`
  §3); no shipped-constant corollaries; the fuel review's §2 question —
  eight reachable ambient opaque-exhaustion rows at this pin — answered
  nowhere in FUEL.md/ARCHITECTURE; an UNPLANNED third forced class
  (allocator/memory contracts at the new pin: negative-size alloc,
  retained bytes, requested address → new public-rule premises); NO census
  for a surface of 860 added / 35 removed / 1599 changed (565 binder-only,
  1034 real); 13 red-frontier docs commits, 17 progress records, 17 axiom
  listings in `docs/evidence/`, 34 dangling `.tmp/` citations.
- **G2 the actual emitted file in t1** (`restore cmp data`, a 42 841-line
  term machine-quoted from the pinned Lean frontend, checked by executable
  `toExpr` round-trip): LANDABLE WITH WORK (M). This is the operator's
  ratified option (b) mechanised over the WHOLE file — sound, honest, not
  option (a). Fixes: the round-trip check as a gate speedbump (on demand
  today; 9.6 s); an independent `BEq` beside `toExpr`; KOI A7's "option (a)
  remains the named target" was quietly dropped — restore or rule; name the
  `mkAuxLemma` kernel-certificate device; decide the retained wrapper.
- **G3 E6/E7 scheduler / raw C calls** (15 commits): SPLIT — PARK. The
  referent is right (every statement over `driver2_lemFuel`,
  `process_core_step2`, `find_can_advance`, `step_ctx`; closed forms
  outcome-list shaped; nothing hand-written replaces the scheduler). But:
  no corpus program with a call certified (oracle t2 → 3, t3 → 4, t10 → 1;
  no theorems); `Step`/`wps`/`wpt`/`Frag` changed shape under the frozen
  spec with no census; the candidate `Frag e true` is admitted NOT closed
  under `Step` (kernel counterexample); 32 of 192 new pins carry package
  devices in their statements (against the 2026-09-03 pin discipline); the
  agent reordered E7 before E6 by its own decision — a design question for
  the operator.
- **G4 seq_rmw** (4 commits): SPLIT — land after a re-cut onto G1+G2
  without G3 (M). Engine arms located, mirror matches, rules sound at cost
  8, PROVISIONAL-labelled; it is E5's own missing item; the
  `negFree → boundFree` public-premise change needs a census.
- **G5 the committed failing WIP patch** in `docs/`: REJECT (branch it);
  the pause record is fine.
- **G6 DECISIONS/KOI/README**: LANDABLE WITH WORK (editorial): README
  accurate at HEAD; the branch's DECISIONS is a 1 795-line [AGENT] build
  log (collapse to ≤ 5 entries surfacing the five agent-called
  dispositions); KOI B8 row malformed, §E stale, A7 target dropped.
  Provenance honest — no [USER] mis-tagging found.

Landing order recommended: G1 → G2 → G4 (re-cut) → park G3 → the patch off
main → G6 edits with each landing; each its own snapshot/census, record,
range audit and merge ask. Report §9 enumerates fixes F1–F9.

## 4. Orchestrator's overall assessment

- **Landable, in this order**: (i) the E5 completion (t5/t6/t4) — S–M of
  docs work + the owed E5 range audit; (ii) the re-pin — M, one forced
  slice, with the fragment-fuel deviation and the exhaustion paragraph
  written up and the census taken; (iii) the actual-file statement — M;
  (iv) seq_rmw re-cut — M. Together they would put the demo at: E5
  complete, the pins current (fuel-parametric semantics in), the t1
  statement over the pipeline's actual file. That is most of the road to
  the v1 tag.
- **Park**: the E6/E7 scheduler work (sound referent, unfinished, spec
  drift without census, pin-discipline violations, E7-before-E6 unruled).
- **Reject**: the failing patch in `docs/`.
- **Process**: green gates on both heads are a strong baseline and the
  provenance is honest; the "messy" is real — build-log DECISIONS, evidence
  dumps, red-frontier commits — and is editorial, not trust-bearing. Two
  rulings the operator owes before any of it lands: the re-pin target (KOI
  A6) and the E5 supplies normalisation (§S2.5); one to settle for G3: E6
  absorbing multiple offers.
