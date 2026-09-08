# Complete-file t5 worker record

[AGENT 2026-09-08]. Parent charter:
`docs/2026-09-08_whole-file-corpus-charter.md`. Worktree
`worktrees/worker-whole-corpus-t5`, created from `demo-whole-file-corpus`
at `f6045fd` through the primary `scripts/new-worktree.sh`. Shared support
commit `abbfbd6` is adopted as `ccefa15`; parent owns its integration.

## Captured file and body checkpoint

`Examples/EmittedT5Data.lean` is the complete existing tool quotation from
the verified t1 slice's reusable t5 experiment, with only its namespace
changed from `CerberusHeapLang.CaptureReuseT5` to
`CerberusHeapLang.CorpusA7.T5`. The parent will independently run the fresh
Cabs/quotation/comparator speedbump at integration. No generator or
semantics source was modified here.

`Examples/EmittedT5.lean` projects main from that data, proves exact body
equality including annotations, procedure metadata and save initializer,
and proves syntactic membership for both if branches, unspecified cases,
and dead cleanup. Its independent evaluator-depth bound is 40. The
complete reference collector's main lookup is kernel checked; original
comparators remain guarded by their finite checks. Captured library data
equals the t1 captured library, enabling the existing actual-library
contract without a truncated-file assumption.

Captured frontend supply is 47. The returned supply after driver
initialization is 48; the initial run state's `sym_supply` itself is 47,
as `initial_core_run_state` draws the current supply into that field.
Source cell numbers are 21 and 22, return label 24, and temporaries 25–46.

All Lean commands use package cwd and `scripts/capped`, `CERB_MEM_MAX=40G`.
Verbatim successful lines from the targeted build log (root-relative,
ignored and ephemeral `.lake/t5-worker-evidence/proof-build.log`):

```text
✔ [454/455] Built CerberusHeapLang.Examples.EmittedT5 (4.5s)
```

The first body equality check caught a missing pointer annotation on the
negative store; `assignmentPtr` now retains
`Astd "§6.5.16#3, sentence 1"`. The complete-body equality then passed.
The public proof module remains in progress at this checkpoint and is
not included in this checkpoint commit. The full parent gate and final
adversarial review remain required before claiming the charter complete.

Cache refresh attempted to overwrite existing read-only package Git
objects, reporting permission denials. Those unnecessary writes were
not retried. The existing dependency checkout and copied build artifacts
were used; the build trace identifies Lean 4.32.2. No provider source or
dependency pin changed.

## Public-rule and driver checkpoint

`EmittedT5Exhibit.lean` now derives the complete retained body through
public total rules. It consumes `EmittedIntSupport.wpt_boundLoad`,
`wpt_intAssign`, `wpt_unseq_value_right`, comparator-based symbol lookup,
and the annotated integer memory lemmas. Its callee evaluation facts use
`EmittedStdCore.HasIntLibrary`, never the old three-function `StdE3` file
identity. Shared followup `2913ddf` is adopted as `1429ff0`.

The sufficient total budget is 88: 17 for allocation/initialization, 55
for the conditional and assignment, and 16 for return. Actual value-form
literals use the generic unsequenced-value rule; explicit budget weakening
retains spare units. No minimality claim is made. The body requires only
`22 < M.runState.sym_supply`, protecting the two source cell bindings
against the assignment's fresh temporary. The complete-file certificate
discharges this at captured supply 47. It quantifies every ambient fuel
at least 90 (88 plus the driver margin), filesystem state and argument
list, and states the genuine `CerbND.runND (_root_.drive ...)` singleton
Active outcome returning `lint 1`, unblocked, with empty trace/stdout/stderr.
The capture-transfer twin retains complete data equality, supply equality
and all three original comparator checks.

No old public declaration was edited by this worker. Parent root/API,
Audit/Shipped integration, fresh complete-file comparisons, the full gate,
and the independent adversarial range review remain parent-owned.

Verbatim final targeted build and fast-gate excerpts:

```text
✔ [455/455] Built CerberusHeapLang.EmittedT5Exhibit (10s)
Build completed successfully (455 jobs).
info: CerberusHeapLang/Audit.lean:1161:0: CerberusHeapLang export pins: 925 trio-exact, 7 propext-exact, 7 axiom-free-exact
Build completed successfully (491 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

A separate capped Lean import printed exact axiom cones for the final
source. These are measured sets, not inferred upper bounds. All selected
facts have exactly the classical trio; none was forced to depend on an
extra axiom to match a desired category. Verbatim output:

```text
'CerberusHeapLang.CorpusA7.T5.mainBody_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.mainBody_frag' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.mainBody_evalDepth' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.reference_main_labels' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.mainBody_saves' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.returnQ_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.returnQ_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.returnSpec_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.wpt_t5Load' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.wpt_t5Gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.wpt_t5Cond' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.wpt_t5AssignBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.wpt_t5Return' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.wpt_t5If' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.mainBody_wpt' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.mainBody_driver_done' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.certified_production' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T5.certified_production_of_capture_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
