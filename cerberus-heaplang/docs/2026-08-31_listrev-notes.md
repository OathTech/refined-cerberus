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

---

# Phase B — the shop window (pedagogy pass; this worker's record)

Docs/headers/instrument only — ZERO proof-content changes, ZERO
renames. Mechanical verification of that claim: the signature
snapshot regenerated after all edits is BYTE-IDENTICAL to the
committed phase-A post snapshot
(`docs/2026-08-31_listrev-signatures-post.txt`; diff -q clean,
2026-08-31). Sweep tallies unchanged: 755 theorems / 1499 constants
/ 434 jobs.

## What was produced / moved

1. **`docs/WALKTHROUGH.md`** (new): the naive-PL-reader tour —
   §1 what Cerberus/Core/the engine are (no project history
   assumed); §2 the list-reverse program construct by construct
   (pretty form + the real `lrBody` term); §3 what a triple means
   (wp_store walked; `SemTriple`'s quantifier structure: any
   configuration satisfying P, arbitrary rest returned verbatim,
   engine execution; the headline statement skeleton); §4 the trust
   story in three tiers (kernel-checked cones / explicit hypotheses
   / the specification idiom) incl. the mirror-is-interior
   invariant (a bad mirror can only make theorems unprovable, never
   false) and the driveJ-vs-production-lane asymmetry; §5 READING
   THE THEOREMS ([USER 2026-08-31] addendum, mid-phase): verbatim
   statements + identifier-by-identifier bin tables
   (ENGINE / SPEC IDIOM / HYPOTHESES) + idiom definitions inline
   for `fib_certified_total`, `list_reverse_certified`,
   `exhibitA_prod`, + the statement-surface census output pasted
   verbatim; §6 check-it-yourself (commands RUN, output pasted);
   §7 module reading order.
2. **README recast**: Reynolds/O'Hearn claim made explicit and
   backed immediately by the exhibit table (small axioms → frame →
   disjoint stores → counter loop → fib incl. total → array →
   LIST-REVERSE → production rows), each row
   claim/hypotheses/lane/cone; drive-vs-production lane defined at
   first use; walkthrough linked at top; all honesty artifacts kept
   (trust story, scope of claims verbatim in substance, divergence
   register with references normalized to dated doc PATHS, verify-me
   block re-run); chronicle-flavored text (phase/arc/slice labels)
   removed from the front doc.
3. **`scripts/statement_census.lean`** (new, [USER 2026-08-31]
   addendum deliverable): read-only #eval instrument; for each of
   the 10 pinned exported theorems, collects the constants of the
   STATEMENT (type only, proofs not inspected) and bins by module
   root (CerberusHeapLang = idiom / Iris / Init‑Lean‑Std‑Batteries‑Qq
   = core / everything else = the CerberusLean dependency = engine).
   NOT wired as an audit check (frozen expected partitions + plant
   tests judged non-trivial mid-phase; registered as future gate in
   the script header and Audit.lean header). Run twice (before and
   after the header pass) — outputs identical.
4. **Module headers** rewritten to orient a stranger (all 18
   modules): "spike artifact N" / phase‑S1‑S4 / "Extension D
   obligation" openers replaced by content descriptions; bare
   references ("recon §", "slice notes", "probe report", "the
   report") normalized to dated doc paths; Dnn finding labels KEPT
   in DriverCollapse/ProdEntry with a one-line legend pointing at
   `docs/2026-08-30_spike-sliceB-notes.md`; the stale hardcoded
   engine pin in Step.lean's header (8fb380c9c) replaced by a
   pointer to `../scripts/semantics-pin.env` (the pin's single
   source of truth); Lang.lean's "RETIRED instance" note recast as
   "deliberately ABSENT" (the instance does not exist in code);
   Exhibit header now lists exhibit (c). No declaration renamed, no
   file renamed.

## Findings (census, honest observations — reported not papered)

- The Iris-exported theorems carry the universally quantified
  ghost-functor binder (`Iris.BundledGFunctors` + `SpikeGpreS`) in
  their statement surface; satisfiability witness `SpikeGF`. The
  engine-only exports (`fib_certified_total`, `exhibitA_prod`)
  surface ZERO Iris constants.
- `counter_loop_certified_production`'s statement surfaces
  iris-lean's finite-map library (`Iris.Std.PartialMap.singleton`,
  `Std.ExtTreeMap.instPartialMapCompare`) — footprint-map DATA
  vocabulary, not program-logic machinery; listed in WALKTHROUGH
  §5.4. No other machinery constant surfaces in any pinned
  statement.

## Commands run (verbatim outputs pasted where quoted)

- `./scripts/test_unit.sh` — baseline before edits AND after all
  edits: `ALL GATES GREEN` both times (post-edit tail quoted in
  README; the audit info-line position moved 362→366 with the
  header edit, quoted tails updated to the observed output).
- `lake env lean scripts/signature_snapshot.lean` → diff vs
  committed post snapshot: identical (above).
- `lake env lean scripts/statement_census.lean` — output pasted
  into WALKTHROUGH §5 verbatim.
- The verify-me `#print axioms` block — re-run this checkout;
  output identical to the quoted README block.

Rename table: EMPTY (no renames).

---

# Phase C — the naive-reader review, the prediction-diff, the fixes (this worker's record)

The [USER]-mandated fresh-eyes instrument (arc plan phase C) ran:
an auditor roleplaying a PL-literate separation logician with zero
Cerberus/lem/project knowledge, reading only what the front docs
point to and running every documented command. Full review:
`docs/2026-08-31_naive-reader-review.md` (repository root),
committed with this slice.

## The verdict, quoted verbatim (review §5)

> **Would I believe the Reynolds/O'Hearn-over-real-C claim after
> this session? Yes, with one precisely locatable reservation —
> and the docs themselves taught me where to put it.**

and its closing assessment:

> Nothing I checked — ten axiom cones, three census partitions,
> five line citations, one engine-source divergence claim, two
> full statement reads — came back other than exactly as
> documented, and that track record is itself evidence. This is
> the rare artifact whose documentation *under*-promises relative
> to what spot-checking finds.

Tally (review §2, verbatim): "2 READER-MAJOR, 8 READER-MINOR,
6 NOTE."

## Prediction-diff (the instrument's value demonstrated)

The phase-B close carried a prediction of five reader stumbles
([AGENT orchestrator] record, transmitted in the phase-C work
order; the five-item list itself was not committed — a process gap
noted here, not repaired retroactively). Per that record: **both
READER-MAJORs were unpredicted** —

1. MAJOR-1: the one axiom (`runEffectful`) discussed at length in
   three documents but its *statement* printed in none; the
   register chain terminates at a file:line inside a vendored
   `.lake` dependency.
2. MAJOR-2: the "differentially validated" claim asserted with no
   reachable record — the only pointer a jargon-laden pin file
   that names a commit, not what the validation covers.

The committed phase-B record's own known-frictions list (Dnn
labels deliberately kept with a legend; the ghost-functor-binder
and PartialMap statement surfacings, pre-disclosed in WALKTHROUGH
§5.4) landed exactly as predicted-grade friction or better: MINOR
finding 7, and positive NOTEs 13 and the §5.4 disclosures. The
asymmetry is the instrument's demonstrated value: everything the
author-side eye saw coming came back as friction, while the two
items it missed are precisely what a stranger ranked as blocking.
The author-side eye, primed by the register chains
(README → `Audit.lean` header → LemLib.lean:54;
README → `semantics-pin.env`), could not see that the chains'
endpoints are unreadable from outside the project.

## Fix list (this commit), by review finding number

- **Findings 1 + 2 (both MAJORs) — the single best change**: a
  self-contained "What you are asked to take on faith" subsection
  in the README's trust story: (a) `runEffectful` printed VERBATIM
  (confirmed against the vendored source,
  `.lake/packages/LemLib/lean-lib/LemLib.lean:54`) with its
  two-sentence story (effect-erasure seam; statements-only entry
  via the initial state's symbol-supply seam, which the certified
  fragment provably never reads; declared temporal, upstream
  retirement in flight, vanishes at a pin bump); (b) what the
  differential validation actually covers, summarized from the
  engine's own record with its real numbers (106/106 minimal,
  213/213 CN, 16/16 libxml2-URI byte-identical, 1,669 csmith at a
  classified baseline, ~2,000 harness-family executions,
  2,186-file CI sweep with zero mismatches among 1,316 comparable;
  sampling-not-proof and oracle-on-the-boundary stated), with the
  IN-PACKAGE path `../.cerberus-ws/lean_frontend/VALIDATION.md`
  named as the record. Walkthrough §1 and §4 link the subsection;
  the divergence-register runEffectful row and the README intro
  now point at it.
- **Findings 3 + 9 (MINOR)**: column legend line at the exhibit
  table head — Lane (drive/driveJ/production), trio, in-budget
  fuel, interior — each term one clause, full treatments still
  where they were.
- **Finding 4 (MINOR)**: `aids` documented front-facing — one
  sentence in the README's lanes paragraph (the action-id supply,
  the ∀-quantified oracle for the driver's fresh action-id draws,
  irrelevant on this deterministic fragment) + reading-table
  coverage in WALKTHROUGH §5.1 and a new `nsteps`/`aids` row in
  §5.2.
- **Finding 5 (MINOR)**: the `hfuel`/`hfuel2` pair explained in
  the §5.2 reading table: nested budget facts, one per drive entry
  point — whole program `esize` 6, jump-re-entered loop body
  `esize` 5, hence the +1 slack; `hfuel2` a trivial consequence of
  `hfuel`, interim scaffolding retired by the registered
  total-export lane.
- **Finding 6 (MINOR) + NOTE 15**: WALKTHROUGH §6 gains
  build-experience notes — the expected
  `capped: WARNING — … running UNCAPPED` sandbox warning and why
  it has no bearing on the verification claim, the expected
  `unusedVariables` linter noise from `generated/*`, the
  warm-vs-cold duration expectation (sub-second replay vs minutes
  to tens of minutes from scratch; honestly labeled: no pinned
  cold timing recorded), and the setup script's offline/idempotent
  behavior. A compact pointer line added to the README's build
  section.
- **NOTE 16**: the σ₀-returned-unchanged one-liner added to §5.1
  (the fib program provably touches no memory).

Skipped, with reasons (the reviewer praised the concision; bloat
was the named risk):

- **Finding 7 (MINOR, internal shorthand D26/R2/D14)**: the Dnn
  labels were KEPT deliberately in phase B with a legend; the
  reviewer confirms every row's content survives without them.
  Rewriting the register would churn a record whose entries' homes
  are authoritative.
- **Finding 8 (MINOR, house-flavored phrases)**: each is decodable
  from context per the review itself; a phrase-by-phrase rewrite
  pass risks the bloat and would touch claim-bearing sentences for
  style only.
- **Finding 10 (MINOR, out-of-package sends)**: the two sends that
  carry trust weight (axiom declaration, validation record) are
  exactly the MAJOR fixes above; the remaining sends land on the
  object of study (the engine's generated source) or the build
  scripts, and are irreducible for a package that certifies an
  external engine.
- **NOTE 14 (authorship), NOTEs 11/12/13 (positives)**: no action
  needed.

## Verification (this checkout, after all edits)

Docs-only slice — zero proof content touched; the only non-doc
file in the commit is the review record itself. Gates re-run:
`./scripts/test_unit.sh` ALL GATES GREEN (output quoted in the
commit message context below). The README verify-me `#print
axioms` block and the WALKTHROUGH §6 three-theorem block re-run
this checkout: outputs identical to the quoted blocks (re-pasted
in this record's phase-C run log below).

### Phase-C run log (verbatim, 2026-08-31, this checkout)

`./scripts/test_unit.sh` tail:

```
ℹ [432/434] Replayed CerberusHeapLang.Audit
info: CerberusHeapLang/Audit.lean:366:0: CerberusHeapLang axiom sweep: 755 theorems within the declared boundary (40 in the production-entry boundary modules, trio + runEffectful; all others trio-exact)
info: CerberusHeapLang/Audit.lean:366:0: CerberusHeapLang banned-axiom sweep: 1499 constants of every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (434 jobs).
ok: cerberus-heaplang build green (axiom sweep + pins passed in-build)
ALL GATES GREEN
```

The README verify-me heredoc, re-run:

```
'CerberusHeapLang.semantic_triple_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.engine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.array_sum_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.list_reverse_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
'CerberusHeapLang.counter_loop_certified_production' depends on axioms: [propext,
 runEffectful,
 Classical.choice,
 Quot.sound]
```

The WALKTHROUGH §6 three-theorem block, re-run:

```
'CerberusHeapLang.list_reverse_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.fib_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
```

Both match the documents' quoted blocks character-for-character
(the two production-entry cones carrying `runEffectful`, everything
else trio-exact). The axiom's verbatim statement in the new README
subsection was confirmed by grep against the vendored source:
`.lake/packages/LemLib/lean-lib/LemLib.lean:54` reads exactly
`axiom runEffectful {α : Type} : (Unit → BaseIO α) → α`. The
validation-summary numbers were read from
`../.cerberus-ws/lean_frontend/VALIDATION.md` at the pinned
workspace (its §2 lane table and §5 scope statement).
