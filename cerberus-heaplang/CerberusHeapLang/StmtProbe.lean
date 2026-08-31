/-
CerberusHeapLang.StmtProbe — the S0 jump-kernel probe (two-phase arc
plan, docs/2026-08-31_two-phase-arc-plan.md; report:
docs/2026-08-31_s0-probe-report.md).

TOY-ONLY by charter: no engine imports, no boundary axioms; the
probe demonstrates the statement-stratified WP architecture (label
map + per-label preconditions + jump-aware sequencing + Löb-tied
elimination) that phase 1 migrates the demo onto. Verdict: GO —
recorded in the probe report.
-/
import CerberusHeapLang.StmtProbe.Toy
import CerberusHeapLang.StmtProbe.Wps
import CerberusHeapLang.StmtProbe.Demo
