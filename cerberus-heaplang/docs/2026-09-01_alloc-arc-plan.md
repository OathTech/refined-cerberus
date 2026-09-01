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
