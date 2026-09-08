# Actual-file t4 worker record

Status: IMPLEMENTED; parent integration and final review pending,
[AGENT 2026-09-08]. Scope and working practices are
`docs/2026-09-08_whole-file-corpus-charter.md` and `AGENTS.md`.
Worker owns only the new T4 data, shape, exhibit modules and this record.
No source in a sibling repository is modified. Heavy builds are serialized
by the parent; all Lean/Lake checks use `scripts/capped` at 40G.

Created `worker-whole-corpus-t4` from `demo-whole-file-corpus` at f6045fd
via `scripts/new-worktree.sh`; copied the verified primary pinned workspace
and package cache. `setup-cerberus-dep.sh --check` passed, including all
37 handwritten seams. Shared support abbfbd6 was cherry-picked as 6c4d5a6.

The initial retained data is the scout's complete T4 quotation with only
its namespace changed to `CerberusHeapLang.CorpusA7.T4`. The parent will
perform the final fresh complete-data and original-comparator comparison.
Supply92 is captured frontend data; the initializer's returned next93 is
separate from its run-state supply. The complete term retains both cell
annotations, all four label annotations and passing modes, cleanup and the
loop-attributes field.

The first green checkpoint establishes the exact entire body equality
`mainBody_shape`, whole-file main lookup, actual extern self-binding and
comparison equality, and genuine main-label registration under the
original finite comparator checks. It does not yet prove syntactic
membership, exact four-continuation contents, the public total loop
proof or production/capture-transfer theorems.

Verification, 2026-09-08, package cwd:

```
CERB_MEM_MAX=40G ../scripts/capped "$HOME/.elan/bin/lake" build CerberusHeapLang.Examples.EmittedT4
✔ [454/454] Built CerberusHeapLang.Examples.EmittedT4 (4.2s)
Build completed successfully (454 jobs).
```

Caller observed exit0. First feedback found an unqualified `SaveInit`
name; qualifying the existing type as `CorpusE0.SaveInit` resolved it.
Ignored logs and compacted inspection text in the worktree root's
`.lake/t4-worker-scratch/` are ephemeral; this record preserves the useful
result. No limit raises, native proof evaluation, sorries or axioms added.

Second green checkpoint: the actual body's syntactic `mainBody_frag` and
separate `mainBody_evalDepth ≤ 40`; exact `Q_eq` for all four retained
continuations, their membership and depth40; typed load clients consuming
`EmittedIntSupport.wpt_boundLoad`; actual-library comparison/truth
conversion derivations preserving load footprints, with the shared
`wpt_unseq_value_right` rule for the actual PEval literals. Shared followup
2913ddf was cherry-picked as 6a46f73. The final feedback used the existing
`update_env_tuple2_mixed` and `evalPexpr_reannot0` facts, avoiding an import
of synthetic proof clients and preserving actual pure annotations.

```
CERB_MEM_MAX=40G ../scripts/capped "$HOME/.elan/bin/lake" build CerberusHeapLang.EmittedT4Exhibit
✔ [455/455] Built CerberusHeapLang.EmittedT4Exhibit (5.0s)
Build completed successfully (455 jobs).
```

Caller observed exit0; no new worker warnings. The main total/invariant
proof and driver certificates are still pending. The expected freshness
premise is `22 < M.runState.sym_supply`: only the live source pointers21/22
are preserved by the assignment postconditions, not stale temporary
bindings; the final file still starts at its exact captured supply92.

Third green checkpoint proves the combined short-circuit guard, both
arithmetic right-hand sides with their exact actual read footprints, both
negative assignments through the shared typed rule, pointer-save rebinding,
and the full loop body. The invariant owns i=n and s=sum(0..n-1), n≤5;
`loopBudget n = 159*(5-n)+98` decreases on each continuing iteration.
`blockSpecsT_main` proves the reachable while and return entries; all four
registered continuations remain covered by the syntactic membership proof.
The final case performs both annotated cell kills and jumps to the actual
return continuation. The only supply hypothesis is22<, for live i/s.

```
CERB_MEM_MAX=40G ../scripts/capped "$HOME/.elan/bin/lake" build CerberusHeapLang.EmittedT4Exhibit
✔ [455/455] Built CerberusHeapLang.EmittedT4Exhibit (13s)
Build completed successfully (455 jobs).
```

Caller observed exit0, no new worker warnings. Routine feedback fixed a
thin `psym_eval` spelling bridge, transparent annotated-type abbreviations,
and explicit local SymFrame projections. No judgment, mirror, semantics,
rule limit or external premise change was needed. Allocation/initialization
of the full main and the genuine-driver wrapper remain pending.


The final implementation completes the full main allocation/initialization
and the genuine driver and capture-transfer wrappers. The public
`wpt_main` consumes allocation headroom and has total budget915;
`certified_production` and `certified_production_of_capture_eq` quantify
`[LemFuel]` with a sufficient lower bound917. These are upper bounds from
the compositional total proof, not a tight step-count claim. The production
statement starts at captured supply92 and covers arbitrary filesystem and
argument inputs, singleton active return10, no block, empty trace/stdout/
stderr. The original-file transfer retains full capture-data equality,
supply equality and original library/main/label comparator checks. It does
not assert correctness of the IO frontend or replace these premises with
its executable comparison.

The loop proof keeps the exact source types, allocation prefixes, save
passing modes, all four registered continuation contexts and syntactic
coverage of the complete body. Only the while and return labels require
reachable total specifications for this source program; the continue and
break continuation bodies are still independently covered by `Q_frag` and
`Q_depth`. Heap ownership, decreasing iteration budget and signed integer
range facts supply the loop's total correctness. Generic typed load,
assignment and value-right unsequenced machinery come from
`EmittedIntSupport`; source-specific comparison/truth and arithmetic
adapters retain the actual emitted annotations and library calls.

Final targeted check, caller observed exit0 and no new T4 warnings:

```
CERB_MEM_MAX=40G ../scripts/capped "$HOME/.elan/bin/lake" build CerberusHeapLang.EmittedT4Exhibit
✔ [455/455] Built CerberusHeapLang.EmittedT4Exhibit (20s)
Build completed successfully (455 jobs).
```

A separate capped `lake env lean` probe printed the exact axiom set
`[propext, Classical.choice, Quot.sound]` for each of `mainBody_shape`,
`mainBody_frag`, `Q_eq`, `Q_depth`, `blockSpecsT_main`, `wpt_main`,
`certified_production` and `certified_production_of_capture_eq`; exit0.
The parent owns permanent Audit/API/classification integration, a fresh
complete-file comparison and independent final gate/review. The worker
did not modify any shared integration surface, sibling repo, semantic
judgment or frozen evaluator, and added no admitted proof or limit raise.

Intermediate fast gate also passed, caller observed exit0:

```
CERB_MEM_MAX=40G scripts/test_unit.sh --fast
CerberusHeapLang export pins: 925 trio-exact, 7 propext-exact, 7 axiom-free-exact
Build completed successfully (491 jobs).
FAST-GATE GREEN (gates 1-2 only — not a claim-point result; say fast-gate in the commit)
```

These pins cover the branch's existing root imports; the new T4 module was
checked by the separate targeted build and axiom probe above. The parent
will add permanent exact pins and run the independently integrated gate.
