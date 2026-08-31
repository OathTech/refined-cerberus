/-
CerberusHeapLang.StmtProbe — a self-contained TOY-LANGUAGE design
probe for the statement-stratified WP (label map + per-label
preconditions + jump-aware sequencing + Löb-tied elimination), the
architecture Wps.lean realizes on the real Core fragment.

TOY-ONLY by charter: no engine imports, no boundary axioms, no
bearing on the exported claims — kept as the design record it is
(report: docs/2026-08-31_s0-probe-report.md). Skippable on a first
reading.
-/
import CerberusHeapLang.StmtProbe.Toy
import CerberusHeapLang.StmtProbe.Wps
import CerberusHeapLang.StmtProbe.Demo
