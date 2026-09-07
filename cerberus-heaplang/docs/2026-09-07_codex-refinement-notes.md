# Codex refinement notes — 2026-09-07

Charter: `docs/2026-09-07_codex-charter-total-refines-partial.md`.
Worktree: `worktrees/codex-refinement`; branch: `codex/total-refines-partial`.
Activation main: `6df8982` (the Lean tree of `2e18821`).

## T1 — LabelSpecT.forget and wps_of_wpt

Deliverable commit: `a0b728c`.

Added declarations: `CerberusHeapLang.LabelSpecT.forget` and
`CerberusHeapLang.wps_of_wpt`, immediately before the namespace's final
`end` in `Wpt.lean`. Added the single `wps_of_wpt` pin in `trioExports`.

[AGENT] The proof follows charter §4 directly: strong induction on `k`,
with `e` and `ρ` generalized; value, jump, impossible empty-table call,
zero-budget step, and successor step cases. The step case eliminates
`List Empty` observations, introduces the later, drops the credit, and
uses the induction hypothesis. No private helpers were needed, and no
partial RULE lemma is used. Both declaration texts match §3 verbatim
apart from the permitted docstrings and the added proof.

The required FULL baseline gate ran before the baseline snapshot.
Commands used the charter's environment: `CERB_PROJ` set to this worktree,
`GIT_CONFIG_GLOBAL=/dev/null`, `TMPDIR` set to this worktree's
`cerberus-heaplang/.lake`, and `CERB_MEM_MAX=40G`. All Lean/Lake invocations
went through `scripts/capped`; no uncapped warning or cgroup error occurred.
With both environment variables set, the wrapper skips sourcing `env.sh`
and emits no environment banner.

[AGENT] The first gate's login shell reported the following after the gate
had succeeded (outside the gate log):

```text
/usr/bin/bash: line 7: /home/dev/.bash_logout: Permission denied
```

[AGENT] Applied the `nono-sandbox` skill to this OS sandbox boundary;
subsequent commands use non-login shells and do not request that file.
No permission/profile change was needed or made.

Baseline gate tail, verbatim (`^==|^ok:|^info: CerberusHeapLang|^Build completed|^BOUNDARY|^ALL GATES`):

```text
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 1b: fuel-numeral grep (scripts/fuel_numeral_check.sh; a numeral outside a *_shipped corollary is red) ==
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (61 files scanned, comments stripped)
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1121:0: CerberusHeapLang export pins: 904 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1121:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6476 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1121:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9675 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (484 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 19 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ok:   Exhibit — 0 internals mentions
ok:   LoopExhibit — 0 internals mentions
ok:   FibExhibit — 0 internals mentions
ok:   ArrayExhibit — 0 internals mentions
ok:   ListRevExhibit — 0 internals mentions
ok:   TreeRotExhibit — 0 internals mentions
ok:   CaseExhibit — 0 internals mentions
ok:   WseqExhibit — 0 internals mentions
ok:   StructExhibit — 0 internals mentions
ok:   AllocExhibit — 0 internals mentions
ok:   DisposeExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
ok:   MallocListExhibit — 0 internals mentions
ok:   FibRecExhibit — 0 internals mentions
ok:   TwoLabelExhibit — 0 internals mentions
ok:   EvenOddExhibit — 0 internals mentions
ok:   EmittedAExhibit — 0 internals mentions
ok:   EmittedBExhibit — 0 internals mentions
ok:   EmittedCExhibit — 0 internals mentions
ok:   CorpusT1Exhibit — 0 internals mentions
ok:   CorpusT5Exhibit — 0 internals mentions
ok:   CorpusT6Exhibit — 0 internals mentions
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
ok:   Examples.CorpusE5 — 0 internals mentions
ok:   Examples.EmittedInt — 0 internals mentions
ok:   CorpusT4Exhibit — 0 internals mentions
ok:   Examples.PartialClients — 0 internals mentions
BOUNDARY: 30 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

Shell-reported baseline status and wall time (these are the agent's
`$?`/`SECONDS` reporting, not lines printed by the gate):

```text
GATE-EXIT=0
WALL-SECONDS=17
```

DERIVED baseline package warning count: 33, matching
`^warning: CerberusHeapLang[/.]`.

The first proof build succeeded (shell-reported wall time: 6 seconds).
The following FULL build gate succeeded before the out-of-tree checks
(shell-reported wall time: 46 seconds). The check file was
`cerberus-heaplang/.lake/scratch/codex-refinement-T1-check.lean`, importing
`CerberusHeapLang.Wpt` and opening `Iris Iris.ProgramLogic CerberusHeapLang`.
It ran through `../scripts/capped ~/.elan/bin/lake env lean` from the
package and was deleted before the final gate. Commands:

```lean
#check @LabelSpecT.forget
#check @wps_of_wpt
#print axioms CerberusHeapLang.wps_of_wpt
```

Output, verbatim:

```text
@LabelSpecT.forget : {GF : BundledGFunctors} → LabelSpecT GF → LabelSpec GF
@wps_of_wpt : ∀ [inst : LemFuel] {hlc : HasLC} {GF : BundledGFunctors} [inst_1 : SpikeGS hlc GF] {M : MachineCtx}
  {p : Option sym} {Ls : LabelSpecT GF} (k : Nat) (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr) (ρ : EnvStack),
  wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ wps M p Ls.forget emptyProcSpec Ψ e ρ
'CerberusHeapLang.wps_of_wpt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both snapshots were generated from `cerberus-heaplang/` using
`CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/signature_snapshot.lean`:
`docs/2026-09-07_codex-refinement-baseline.txt` after the baseline gate and
`docs/2026-09-07_codex-refinement-T1-post.txt` after the T1 build gate.
`diff -u` output, verbatim (exit 1 means the expected additions):

```diff
--- docs/2026-09-07_codex-refinement-baseline.txt	2026-09-07 20:26:28.428148482 +0000
+++ docs/2026-09-07_codex-refinement-T1-post.txt	2026-09-07 20:29:31.160415521 +0000
@@ -9644,6 +9644,9 @@
 def CerberusHeapLang.LabelSpecT :
 Iris.BundledGFunctors → Type
 ----
+def CerberusHeapLang.LabelSpecT.forget :
+{GF : Iris.BundledGFunctors} → CerberusHeapLang.LabelSpecT GF → CerberusHeapLang.LabelSpec GF
+----
 def CerberusHeapLang.LabeledAt :
 core_run_state → sym → CerberusHeapLang.LabelMap → Prop
 ----
@@ -47926,6 +47929,15 @@
         CerberusHeapLang.callRedex? e = none →
           (P ∗ ∀ w, Q w -∗ Ψ w ρ) ⊢ CerberusHeapLang.wps M p Ls Θ Ψ e ρ
 ----
+theorem CerberusHeapLang.wps_of_wpt :
+∀ [inst : LemFuel] {hlc : Iris.HasLC} {GF : Iris.BundledGFunctors}
+  [inst_1 : CerberusHeapLang.SpikeGS hlc GF] {M : CerberusHeapLang.MachineCtx} {p : Option sym}
+  {Ls : CerberusHeapLang.LabelSpecT GF} (k : Nat)
+  (Ψ : CerberusHeapLang.SpikeVal → CerberusHeapLang.EnvStack → Iris.IProp GF)
+  (e : CerberusHeapLang.CoreExpr) (ρ : CerberusHeapLang.EnvStack),
+  CerberusHeapLang.wpt M p Ls CerberusHeapLang.emptyProcSpecT k Ψ e ρ ⊢
+    CerberusHeapLang.wps M p Ls.forget CerberusHeapLang.emptyProcSpec Ψ e ρ
+----
 theorem CerberusHeapLang.wps_pure :
 ∀ [inst : LemFuel] {hlc : Iris.HasLC} {GF : Iris.BundledGFunctors}
   [inst_1 : CerberusHeapLang.SpikeGS hlc GF] {M : CerberusHeapLang.MachineCtx} {p : Option sym}
```

DERIVED census classification: ADDED exactly the two declarations listed
above; REMOVED 0; CHANGED 0. Compared every shared declaration block for
exact equality. DERIVED source diff: `Wpt.lean` 68 added lines, 0 removed;
`Audit.lean` 1 added line, 0 removed. The pin occurs exactly once.

[AGENT] To run the required `git rebase main` before the build gates with
uncommitted additions, used the command-local setting
`git -c rebase.autoStash=true rebase main`. Both runs reported the branch
up to date and restored their autostashes successfully. No main changes
or conflicts occurred. The final gate ran after the scratch file was
removed; no Lean source changed after that gate.

Final FULL gate tail, verbatim:

```text
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 1b: fuel-numeral grep (scripts/fuel_numeral_check.sh; a numeral outside a *_shipped corollary is red) ==
ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant (61 files scanned, comments stripped)
== gate 2: capped build, cerberus-heaplang (elaborates its axiom audit) ==
info: CerberusHeapLang/Audit.lean:1122:0: CerberusHeapLang export pins: 905 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1122:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6478 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1122:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9678 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (484 jobs).
ok: cerberus-heaplang build green
== speedbump: rule-use and classification manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: corpus skeleton (hand-transcribed emitted Core vs docs/corpus-e0; scripts/corpus_skeleton.lean) ==
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — 19 core modules, none imports an exhibit/example/production module
== speedbump: client boundary (positive clients mention no logic internals; scripts/boundary_check.sh) ==
ok:   Exhibit — 0 internals mentions
ok:   LoopExhibit — 0 internals mentions
ok:   FibExhibit — 0 internals mentions
ok:   ArrayExhibit — 0 internals mentions
ok:   ListRevExhibit — 0 internals mentions
ok:   TreeRotExhibit — 0 internals mentions
ok:   CaseExhibit — 0 internals mentions
ok:   WseqExhibit — 0 internals mentions
ok:   StructExhibit — 0 internals mentions
ok:   AllocExhibit — 0 internals mentions
ok:   DisposeExhibit — 0 internals mentions
ok:   RegionLoopExhibit — 0 internals mentions
ok:   MallocListExhibit — 0 internals mentions
ok:   FibRecExhibit — 0 internals mentions
ok:   TwoLabelExhibit — 0 internals mentions
ok:   EvenOddExhibit — 0 internals mentions
ok:   EmittedAExhibit — 0 internals mentions
ok:   EmittedBExhibit — 0 internals mentions
ok:   EmittedCExhibit — 0 internals mentions
ok:   CorpusT1Exhibit — 0 internals mentions
ok:   CorpusT5Exhibit — 0 internals mentions
ok:   CorpusT6Exhibit — 0 internals mentions
ok:   Examples.CallSmoke — 0 internals mentions
ok:   Examples.ReadinessSmoke — 0 internals mentions
ok:   Examples.Layout — 0 internals mentions
ok:   Examples.CorpusE0 — 0 internals mentions
ok:   Examples.CorpusE5 — 0 internals mentions
ok:   Examples.EmittedInt — 0 internals mentions
ok:   CorpusT4Exhibit — 0 internals mentions
ok:   Examples.PartialClients — 0 internals mentions
BOUNDARY: 30 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

Shell-reported status and wall time (agent reporting, not gate output):

```text
GATE-EXIT=0
WALL-SECONDS=17
```

DERIVED final package warning count: 33, using the charter's regex.
The manifest reported no drift and was not changed. T1 is complete on a
green FULL gate; its deliverable commit precedes any T2 work.
