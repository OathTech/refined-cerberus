# The allocation arc (P0-P7)

[USER 2026-09-01]: the independent skeptical re-audit
(docs/2026-09-01_cerberus-heaplang-skeptical-re-audit.md) is ADOPTED
IN FULL as this arc's charter — its P0-P7 remediation plan, merge
sequence, and final acceptance checklist are the normative text (this
file is the house-practice wrapper, not a restatement). Verified by
the orchestrator before adoption: R-01 (cursorOwn never granted by
any launcher; no cursorHeap_alloc exists; the create rule is
stranded), R-02 (11 operational-trace markers in positive production
exhibits), R-10 (Wps.lean header contradicts its own file). The
2026-09-01 foundational re-audit is STRUCK as the acceptance record
(it validated names, not proof flow — the same blind spot as the
manifest gate, R-04's root cause).

House wrapper:
- Phases P0-P7 run as slices on this branch, long-cycle per the
  [USER] authorization pattern (check-in at arc end or blocker);
  gates ALL GREEN per commit; frozen-corpus/signature discipline at
  every restructuring slice; substantive coherent commits.
- The audit's "Definition of done" per phase + its merge-sequence
  "must prove before merge" column are the slice acceptance
  criteria; its final acceptance checklist + a fresh DEPENDENCY-
  TRACING re-audit (the lesson: the re-auditor must trace proof
  cones, not names) gate the arc close.
- P1.1's allocation-failure policy choice (abstract finite
  allocation-capacity resource) is adopted as recommended — its
  design record lands with P1's first slice, operator-visible.
- The audit's RefinedC-migration contract table is carried into the
  arc summary as the port-readiness statement.

## The R-01..R-11 closure table (P0 item 5)

[AGENT 2026-09-01, P0]: one row per audit finding. OWNER is the
phase of this arc that closes it; INTENDED NAMES are the audit's
theorem/gate names (conceptual shapes — P1's design record may
adjust spellings, operator-visible); the CLOSURE TEST is the audit's
acceptance test VERBATIM-in-substance — "theorem exists" is never a
closure test (the R-04 lesson). STATUS moves only with the evidence
named in the test, updated per-slice in this table.

| Finding | Owner | Intended theorem/gate names | Closure test (the audit's acceptance test) | Status |
|---|---|---|---|---|
| R-01 — Critical: the allocation rule is unreachable from adequacy | P1 (P1.1–P1.4) | `AllocReq`, `advanceCursor`, `PlanFits`, `allocCap`, `LaunchCoh`, `launchResources`, `wps_create_cursor_internal` (the current exact rule, renamed internal), public `wps_create` (existential pointer, cursor-free statement), `wpt_create`, allocation-aware variants of `spike_step_adequacy` / `wpt_engine_boundU/J` / `wpt_strongly_normalizing` | Deleting either the public create rule or the allocator launch initialization must BREAK a headline self-contained allocation theorem; no public create theorem statement contains `AllocCursor`, `lastAddress`, `nextAllocId`, `freshBase` (or `cursorOwn`); the P1.4 local tests (plan-order consumption, empty/insufficient plan unprovable, nonzero-guard deletion breaks the internal proof) | OPEN (P0 delivered the honest claims: create marked local-only everywhere) |
| R-02 — Critical: allocating examples bypass the separation logic | P2 | Whole-program `wpt` proofs for `progAProd`, the counter production program (one-request plan) and the reversal production instance (two-request plan); an adequacy theorem for the struct client (`allocCap`-premised, not `cursorOwn`); deletion of the positive-exhibit `Step.sseq_*`/`Step.create`/`engineSteps_*`/`driverDone_step` proof bodies | The complete create/store/load theorem AND at least one allocating loop production theorem must FAIL if `wpt_create` is removed; positive example proof declarations have NO direct operational-semantic dependencies (`Step.*`, `engineSteps_*`, `driveJ_step`, `driverDone_step`) | OPEN (P0 delivered the honest labels: the three exports marked MIXED on every claims surface) |
| R-03 — High: the Cerberus relation is a bespoke one-sided projection | P3 (P3.2; merge-sequence row 7) | `CerberusRound M` (the engine-round relation named independently of examples); per-`Frag`-row two-sided theorem `Step M c c' ↔ CerberusRound M c c'` or the exhaustive sum classification (successful-next arm = `Step`, other arms disjoint from `NotStuck`) | The manifest derives its supported relation cases from an exhaustive theorem; a PLANTED engine/mirror mismatch fails the build | OPEN |
| R-04 — High: the capability gate validates declarations, not use | P3 (P3.1); P0 owns the honest-labeling sub-item | Staged manifest fields (syntax / relational rule / public rule / partial / total / production consumer) with transitive constant-dependency-cone checks; the LAYER-CUT check (every positive-exhibit → operational-constructor path crosses an approved public rule/adequacy declaration); the four planted negative tests | Plant 1: a consumer name kept but its proof replaced by a direct trace — gate 4 must FAIL. Plant 2: a local `wps` theorem listed as adequacy consumer — FAIL. Plant 3: `wpt_create` removed — total and aggregate statuses turn RED. Plant 4: a new `Frag` constructor without rule/consumer — generation FAILS (already fail-closed today) | OPEN; P0 sub-item CLOSED: FULL-ROW renamed CORE-DRIVE-ROW, lanes reported separately, the name-vs-proof-flow caveat generated into the manifest |
| R-05 — Medium: statement/loop framing is not a reusable rule | P4 (P4.2) | `frameLs`/`frameLsT`, `blockSpecs_frame`/`blockSpecsT_frame`, `wps_frame_labels`/`wpt_frame_labels`, derived whole-loop frame rules | Framed list/tree theorems are DERIVED from unframed bodies by the generic rule; `RF` is removed from the core list/tree invariant definitions | OPEN |
| R-06 — Medium: advertised split/fractional features have no client | P4 (P4.1) | A struct/tree client obtaining disjoint typed field views via `pointsToView_split`, updating through them, rejoining via `pointsToView_join`; a read-only client at a proper fraction preserving it | Every advertised split/fractional feature has a compiling consumer, or the capability claim is REMOVED; the dependency-aware manifest (P3) enforces the decision | OPEN |
| R-07 — Medium: non-production scaffolding and example constants in production modules | P5 (merge-sequence row 8) | `StmtProbe` moved to an archival/test target not imported by `CerberusHeapLang`; `intTy`/5-6-7 constants and canned exhibit proofs moved out of `Rules.lean`/`Wps.lean`; an import/dependency-direction gate | The main library import graph excludes `StmtProbe`; the dependency direction semantics → logic → adequacy → clients is mechanically acyclic (gate) | OPEN |
| R-08 — Medium: the counter loop pins an accidental env-map representation | P4 (P4.3) | `LoopExhibit` ported from `IsXFrame` to `SymFrame`; a test configuration with an irrelevant binding in the same frame | No `Fmap`-shape pin remains in `LoopExhibit`; the irrelevant-binding test passes (the proof cannot regress to exact-map equality) | OPEN |
| R-09 — Medium: `SemTriple` less general than its prose | P4 (P4.3) | Either `SemTriple` generalized over a well-formed `MachineCtx` + entry environment, or the fixed-profile scope stated on every describing surface | No claims surface describes `SemTriple` as covering every configuration; the fixed `spikeThread`/`spikeCtx` profile is stated wherever the triple is explained | OPEN (P0 sub-item: the fixed-profile qualifier added to the `SemTriple` docstring and walkthrough §3.2) |
| R-10 — Medium: documentation contradictory, overstates closure | P0 (this slice) for the enumerated stale claims; P6 for the full documentation closure | This commit (claims surfaces trued); P6: the theorem-labelled trust diagram + the generated scope ledger distinguishing local rule / launchable / partial / total / production consumer per construct | P0 sub-test: every stale statement the audit enumerated is gone (Wps.lean "NO wps_create" header; README per-byte-split and production-loop-pending rows; Ecase "local rule only" + retired `DecompJ.step_factor`/`engine_step_matchJ` names; Soundness.lean:3557-3575 "Ecase stays OUT" comment; the undisclosed handwritten allocation prefixes), create is downgraded and the three exports are labeled MIXED on every surface, and the struck records are annotated. P6 test: no stale-name/status search hits; a new reader gets the accurate end-to-end trust story from the headline documents alone | P0 SUB-ITEMS CLOSED (this commit); FULL CLOSURE OPEN (P6, after P1–P5) |
| R-11 — Low (known): `runEffectful` production boundary | P7 | Upstream retirement + pin bump; the exact-cone and banned-axiom sweeps re-run | Production theorem cones return to the classical trio; the boundary list entry is deleted with no restatement | OPEN (held boundary, documented; do not expand while P1–P3 are in flight) |
