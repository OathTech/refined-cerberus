# Complete-file t6 worker

Status: worker implementation complete; targeted proof checks and the fast gate
are green. Parent integration/full verification and adversarial range review
remain outstanding. Worktree `worker-whole-corpus-t6`, branched from active
`demo-whole-file-corpus` at `f6045fd`; shared support adopted from `abbfbd6`
(worker cherry-pick `afb2e01`), with shared helper followup `2913ddf`
(worker cherry-pick `ca4ed6b`). This record does not authorize a merge or push.

The assigned scope is the complete-file t6 consumer under
[the active charter](2026-09-08_whole-file-corpus-charter.md). The worker owns
only `Examples/EmittedT6Data`, `Examples/EmittedT6`, `EmittedT6Exhibit`, and
this record. Root/API/Audit/Shipped/tooling integration and adversarial range
review belong to the parent. All sibling repositories and dependency pins
remain unchanged. Heavy lanes are scheduled by the parent and all builds
run through `scripts/capped` at 40G, from the package directory.

## Captured file and body

The data module copies the scout's entire quoted frontend file, changing
only its namespace to `CerberusHeapLang.CorpusA7.T6`. The captured frontend
supply is 51; the inspector's fuel1000 observation was preparation evidence,
not the proposed certificate's justification. The parent's final speedbump
will regenerate and compare the actual Cabs/data/supply/comparator paths.
The quoted stdlib equals t1's captured stdlib in the kernel, so the existing
captured-library contract transfers without replacing the remaining file
fields or assuming global comparator equality.

The actual body has symbols x21/r22, return30, break32, case1=40, case2=39,
default41, and return temporary50. Its exact shape preserves annotated
integer types, source locations, save argument passing modes, negative-store
operand annotations and sequence grouping. All syntactic alternatives and
cleanup are covered by `mainBody_frag`; the separate evaluator bound is 40.

The new grouping matters: case1's continuation retains the annotated
case-block sequence, while case2/default reside in its right suffix. All
three retain the actual surrounding switch, cleanup and return-save
contexts. Those contexts are proved against the semantics' collector;
comparison with the older wrapper is not their authority.

## Validation

`scripts/setup-cerberus-dep.sh --check` passed at the fixed semantics pin
`89f7e688530c6910884518811d645e4e892e4507`, with 37 handwritten seams
byte-identical. Initial cache priming preceded the parent's accidental 4.33
invocation; later copy-over of identical LemLib Git objects reported their
read-only mode, so no dependency object was modified to work around it.
The actual proof commands run with the package's Lean 4.32.2 toolchain.

The first targeted capped build passed and produced no warning in the new
shape/data modules:

```
✔ [423/427] Built CerberusHeapLang.Examples.EmittedT6Data (4.3s)
✔ [424/427] Built CerberusHeapLang.Wpt (6.3s)
✔ [425/427] Built CerberusHeapLang.IntRules (2.4s)
✔ [426/427] Built CerberusHeapLang.EmittedStdCore (35s)
✔ [427/427] Built CerberusHeapLang.Examples.EmittedT6 (5.4s)
Build completed successfully (427 jobs).
```

The data and body work was committed as `fc3aac0`. Ignored logs and the
Python quote-compaction diagnostic live under the worktree-root
`.lake/t6-worker-scratch/`; they are ephemeral and are not proof artifacts.

## Complete consumer and budget

`EmittedT6Exhibit` proves all five registered continuations and their exact
collector tree, including each continuation's fragment membership and
separate evaluator depth. Its finite label specification admits case2,
break and return with budgets 43, 18, 2; case1/default remain syntactically
covered. The public total proof's 78 units compose allocation/initialization 20
and dispatch 58. Case2 uses assignment 24 and the 19-unit jump to break;
break uses two unit deliveries and return 16. Return uses bound-load 7,
two kills of 3 each, and the 3-unit jump to the 2-unit return continuation.
The assignment consumes the shared evaluated-operand integer rule and the
new value-right unseq rule; the latter's 5-unit proof is weakened to 7,
so these are justified sufficient budgets, not a claim of minimality.

The exported `certified_production` quantifies the ambient LemFuel instance
with `80 ≤ LemFuel.fuel`, and runs the genuine `drive` at the captured
`frontendSupply` 51 with arbitrary filesystem state and arguments. It
concludes a singleton Active `Specified(20)`, no trace, unblocked and empty
stdout/stderr. The capture-transfer twin retains complete-data and supply
equality plus the three original comparator checks. Fresh assignment-binder
noncollision follows locally from x/r numbers 21/22 and supply 51; no 600 floor
or old wrapper certificate is used.

Final targeted verification:

```
✔ [455/455] Built CerberusHeapLang.EmittedT6Exhibit (8.0s)
Build completed successfully (455 jobs).
```

No warning was emitted for the new T6 modules. The worker fast gate also
passed (existing integration root, before parent adds T6's new pins):

```
info: CerberusHeapLang/Audit.lean:1161:0: CerberusHeapLang export pins: 925 trio-exact, 7 propext-exact, 7 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1161:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6830 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1161:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (10277 constants of every kind swept, internal details included — count informational, environment-dependent)
✔ [490/491] Built CerberusHeapLang (803ms)
Build completed successfully (491 jobs).
ok: cerberus-heaplang build green
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

A separate capped import of the new exhibit printed its exact axiom cones:

```
'CerberusHeapLang.CorpusA7.T6.mainBody_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T6.mainBody_frag' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T6.Q_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T6.Q_frag' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T6.mainBody_wpt' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T6.blockSpecs_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T6.certified_production' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.CorpusA7.T6.certified_production_of_capture_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

This readout is preparatory evidence for the parent's exact new audit pins.
The parent must independently verify the integrated full gate, fresh four-file
comparisons, unchanged-existing-signature census and final adversarial review.
The worker did not change root/API/Audit/Shipped integration files beyond
cherry-picking the parent's own shared commits, and did not merge or push.
