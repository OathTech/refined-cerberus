# Actual-file t4 worker record

Status: IN PROGRESS, [AGENT 2026-09-08]. Scope and working practices are
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
