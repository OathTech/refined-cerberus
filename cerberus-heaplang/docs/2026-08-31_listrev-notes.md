# List-reverse arc, phase A — slice notes

Worker record for the three phase-A commits (arc plan
`docs/2026-08-31_listrev-shopwindow-arc-plan.md`; [USER] mandate:
"this would make the case this is truly the reynolds/ohearn logic").
Quoted outputs verbatim; derived tallies labeled derived.

## What was built (commit by commit)

### Commit 1 — NULL + the pointer test + the operand-eval kit

The ENGINE's null/pointer-test design, found and mirrored (never
invented):

- **The null encoding.** `nullPtrval ty = PV Prov_none (PVnull ty)`
  (CerbMem.lean:843). A stored null serializes to eight ZERO bytes at
  `Prov_none` with no copy offsets (repr, CerbMem.lean:581-585 =
  impl_mem.ml:1165-1167); a pointer-typed load of zero bytes
  reconstructs `PV Prov_none (PVnull pointee)` — the POINTEE OF THE
  LOAD's type, not the stored one (abst's `some 0` arm,
  CerbMem.lean:688-692 = impl_mem.ml:1005-1019). The exhibit
  therefore pins ONE pointee type (`nodeTy`) for every next-field
  operation, and the nil case of `isList` ties to exactly that
  decode.
- **The null test IS the engine's `PtrEq` memop.** Core's `Ememop
  PtrEq [p₁, p₂]`: one_step0's MEMOP arm at value operands
  (Core_reduction.lean:353) → `Step_memop_request2 th_st.current_loc
  PtrEq cvals tid (is_unseq_with_ccall ctx) (fun cval => wrap_expr
  (mk_pure_e (mk_value_pe cval)))` (step_ctx, Core_reduction.lean:484
  — the continuation REBUILDS the context around a BARE pure value,
  no Eannot residue, unlike load/store) → the sequential driver's
  discharge `liftMem (CerbMem.eqPtrval loc ptr_val1 ptr_val2)` then
  `mk_th_st (if is_eq then Vtrue else Vfalse)`
  (perform_memop_request2, Driver.lean:288; driver21's arm,
  Driver.lean:377). `eqPtrval` (CerbMem.lean:1731 = impl_mem.ml:
  1830-1881 arm-for-arm) answers the fragment's shapes PURELY:
  null/null → true, concrete-vs-null (either order) → false — all
  single-layer state-verbatim `applyMemM` facts, `rfl`
  (Heap.lean `eqPtrval_null_null` / `eqPtrval_cell_null` /
  `eqPtrval_null_cell`). `eqPtrval` DISCARDS its loc argument, so
  the mirror rule pins `default` and the certification bridges by
  `rfl` (`eqPtrval_loc_irrel`).
- **Fail-closed non-coverage (WF stated, never absorbed):** the
  differing-provenance concrete/concrete arm is a REAL ND fork
  (`msum`, CerbMem.lean:1753) — not single-layer — and the
  function-pointer arms read state; both are ABSENCE of a mirror
  step (`applyMemM = none` / no dischargeStep arm → fail-closed).
  Only `PtrEq` is mirrored; PtrNe/Lt/… are mechanical extensions.
- **The kit the program shape forced** (findings, all IN-PATTERN
  S4-style extensions, none a missing-RULE-CLASS problem):
  1. `Step.memop_eval` — the Ememop operand-evaluation step
     (one_step0's `EVAL "Ememop"` over `stExceptUndef_mapM
     eval_pexpr1 pes`; step_ctx's `eval_pexpr1` is ONE full
     iteration of the evaluator tower — `eval_pexpr20` + the Sum
     readout — which on the certified operand grammar delivers the
     `mk_value_pe` form in one application, so ONE engine step
     evaluates both operands; bridged by `eval1_bridge` /
     `mapM_eval1_bridge`, the `foldM_args_bridge` pattern).
  2. `Step.store_eval` — store ACTION_EVAL (step_action's Store0
     `_,_,_` arm; the loop-carried interior store's operands are
     never syntactic values). The `Store0 … PEconstrained`
     failwithI pre-arm is excluded by the evaluator-premise grammar.
  3. `Step.sseq_sym_pure` — the plain-symbol binder beta
     (`update_env_aux`'s `CaseBase (some sym,_)` arm,
     Core_aux.lean:861): the memop result must be BOUND to be
     branched on (`lets b = memop(…) in if b then … else …` — the
     elaborator's own idiom). RECORDED DIVERGENCE (deliberate,
     fail-closed sub-relation): the `{A}v` LETS-ANNOT variant at
     this pattern is NOT mirrored — the only fragment producer of
     sym-binder-bound values is the memop protocol, which delivers
     bare values; the annot variant is a mechanical extension
     (Step.lean header, the rule's docstring).
  Each with: wps rules (`wps_memop_eval`/`wps_memop_ptreq`/
  `wps_store_eval`/`wps_seq_sym`), certification against step_ctx
  (`step_ctx_memop` + the new `dischargeStep` memop arm +
  `stepDischarge_memop_eval`/`stepDischarge_store_eval`/
  `step_ctx_beta_sym_pure`), cone membership (`FragJ.sseq_sym`/
  `memop_vals`/`memop_op`/`store_op` + `RedexJ`/`DecompJ`
  extensions), and `engine_step_matchJ` coverage.

### Commit 2 — nodes + isList + THE EXHIBIT

- **The node** ([USER] one-allocation-array ruling, extended):
  `nodeTy = long[2]` — ONE allocation, value at offset 0, next at
  offset 8 (`sizeof(long) = targetPtrSize = 8`, LP64). Intra-node
  field access is `array_shift(cur, long, 1)` — arithmetic WITHIN
  the allocation (`arrayShiftPtrval` preserves provenance);
  inter-node traversal is by LOADED pointers, each reconstructed
  with ITS OWN provenance (`splitBytesProv` — the pointer-load
  shared-provenance policy).
- **The byte round trips**, proved against the engine's own
  serializer/deserializer: `reconstruct_ptrImg_null` (`rfl`) and
  `reconstruct_ptrImg_cell` (8-byte little-endian arithmetic,
  discharged by omega over div/mod — kernel-only; machine-address WF
  `0 < a < 2^64` is the honest premise: the addresses
  `allocateObject` mints).
- **Interior STORE machinery** (new — the array exhibit only read):
  `storeM_interior_nodePtr`, `Coh.store_interior` (the byte-splice
  `spliceBytes` + pointwise `getElem?` lemmas; untouched cells by
  pairwise disjointness ⊇ the sub-range), and the wps small axioms
  `wps_load_interior_node` / `wps_store_interior_node`.
- **`isList`** — plain structural recursion on the mathematical
  list; nil = the null encoding; cons ∃-binds the next pointer with
  the node's cell ∗ the tail; value/next decode facts and address
  WF carried per node as pure conjuncts.
- **`list_reverse_certified`** — the classic three-pointer loop,
  invariant `isList prev reversed ∗ isList cur rest` +
  `xs = reversed.reverse ++ rest`, proof TEXTBOOK-COMPOSITIONAL:
  `blockSpecs_intro`, then per construct: `wps_seq_sym` +
  `wps_memop_eval` + `wps_memop_ptreq` (the null test),
  `wps_if_true/false`, `wps_seq_spec` + `wps_load_eval` +
  `wps_load_interior_node` (n := cur->next), `wps_seq` +
  `wps_store_eval` + `wps_store_interior_node` (cur->next := prev),
  `wps_run` (the jump re-establishes the invariant at
  `(v :: reversed, rest)` — `(v :: revd).reverse = revd.reverse ++
  [v]` is the whole list-algebra content). NO monolithic unfolding
  anywhere. Collapse by `wps_sound`, export by `engine_adequacyJ`;
  conclusion (engine vocabulary): driveJ never kills, never
  derails, and any delivered value is a POINTER whose FINAL-heap
  chain is `xs.reverse` (`ChainAt` — per-node `CellCoh` + decode
  facts about the final `MemState`).
- **The concrete demonstration** `list_reverse_demo`: a seeded
  3-node list [1,2,3] (engine-serialized byte images; every decode
  fact `rfl`), delivered chain [3,2,1].

### Commit 3 — records + claims surfaces (this commit)

- This slice record; the pre/post signature snapshots
  (`docs/2026-08-31_listrev-signatures-{pre,post}.txt`).
- README.md claims surface: list-reverse moved from registered
  stretch to the exhibit table; certified-fragment scope updated
  (plain-symbol-binder patterns, `Store0` operand-eval, the `PtrEq`
  memop + its operand-eval step); divergence register rows
  (sym-binder LETS-ANNOT, memop family coverage); verify-me `#print`
  list + observed output re-run verbatim; sweep tallies.
- ListRevExhibit.lean module header corrected to state the
  total-export RESIDUAL honestly (comment-only change).

## Signature diff vs the S4 snapshot (derived, from
`docs/2026-08-31_listrev-signatures-pre.txt` →
`…-post.txt`; pre verified byte-identical to
`docs/2026-08-31_phase2-s4-signatures-post.txt`)

- REMOVED: 0.
- CHANGED: 19 — of which 18 are AUTO-GENERATED eliminators
  (`rec`/`casesOn`/`recOn`/`below.*` of the four deliberately
  extended inductives `Step`, `RedexJ`, `DecompJ`, `FragJ` — pure
  artifacts of new constructors), and exactly ONE human-written
  statement: `Step.sseq_inv`, which gains the sym-binder beta as a
  7th disjunct (an inversion COMPLETION forced by the new rule; all
  prior consumers re-prove with a one-line refutation arm —
  pattern-clash `symPat_ne_base`/`symPat_ne_spec`).
- ADDED: 180 declarations (the kit + the exhibit).
- Every other pre-existing exported statement is verbatim.

## Findings / residuals (registered)

1. **Sym-binder LETS-ANNOT unmirrored** — deliberate fail-closed
   sub-relation (see commit 1 above); mechanical extension named.
2. **Memop coverage = `PtrEq` only**; the family (PtrNe/Lt/…) and
   the ND-fork arm are fail-closed absences; extensions mechanical
   (dischargeStep arm + rule + axiom per memop).
3. **TOTAL EXPORT (variant → unconditional driveJ bound) NOT
   DELIVERED** — best-effort, explicitly non-gating in the arc plan.
   Why the fib pattern does not transfer directly: fib's total lane
   is state-free (each `driveJ_step` fires from pure evaluator
   facts), while every list-reverse iteration's steps depend on
   `applyMemM` success at the CURRENT σ — the drive induction must
   thread a pure heap invariant (ChainAt-style CellCoh facts +
   pairwise disjointness, updated across each interior store)
   through the 11-steps-per-iteration chain. That is a pure
   drive-invariant lane (~the wps proof replayed at the pure level);
   named as the residual's mover. The per-iteration step count is
   fixed and known (11 = memop-eval, memop, sym-beta, if,
   load-eval, load, spec-beta, store-eval, store, wildcard-annot
   beta, jump; entry 1, exit 5), so the bound would be
   `11·|xs| + 6`.
4. **`dischargeStep` gained a memop arm** — a boundary-definition
   change to Soundness.lean's driver projection, mirrored from
   driver21's `Step_memop_request2` arm (Driver.lean:377) +
   `perform_memop_request2` (Driver.lean:288); unmirrored
   memops/operand shapes discharge to `offFragment` (fail-closed).
   Phase-1 lanes unaffected (FragP produces no memops; all phase-1
   per-rule equations pin exact outcomes).
5. **Instance seam noted during the build** (no action): `∪` on
   `SpikeHeapF` resolves to Std's ExtTreeMap instance, NOT
   iris-lean's `PartialMap` instance — term-level
   `Iris.Std.PartialMap.union` + the `get?_union'` bridge in
   ListRevExhibit.lean is the working spelling.

## Gates

All green at each commit (`scripts/test_unit.sh`: grep ban + both
package builds with in-build audits). Sweep movement (derived):
643 → 671 → 755 theorems within the declared boundary; banned-axiom
sweep 1319 → 1372 → 1499 constants, clean. New pins (Audit.lean,
verbatim expectation):

```
'CerberusHeapLang.list_reverse_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
```
