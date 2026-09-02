# Foundations Phase 4 — flagship specifications at full strength (design record + oracle + exit criteria)

Worker slice record, foundations arc Phase 4 (arc plan
`docs/2026-08-31_foundations-arc-plan.md` §Phase 4; audit F-06 and
the Phase-4 remediation list + exit criterion,
`docs/2026-08-31_cerberus-heaplang-foundational-audit.md`: "the
public theorem literally states same-footprint, in-place reversal
plus termination and frame preservation").
Commits: `8f0508c` (1/3, identity indexing + flagship restatement +
the readout tidy), `4e86c08` (2/3, the second client), this commit
(3/3, oracle + records). Gates: `scripts/test_unit.sh` ALL GREEN at every
commit.

## 1. Identity-indexed predicates (audit item 1)

[AGENT] design decisions, with reasoning:

- **The node list is `List (Int × Int)` — allocation id × value.**
  `isList`/`ChainAt`/`SeedChain` recurse on it; the head pointer's
  provenance id IS the head node's listed id (pinned, not
  existential). The metadata heap (Phase 2) is the natural
  authority: the allocation id is exactly the exclusivity anchor
  `metaOwn` polices, so identity claims cost nothing new in the
  Iris proofs — the same `cellOwn` at the same key.
- **PAIRING id with value, rather than carrying two parallel
  lists**: in-place reversal moves next fields only, so the honest
  statement is that the (id, value) PAIRING is preserved while the
  chain order reverses — `SeedChain Q p' ns.reverse` says each
  node still carries its own value, which two independently
  permuted lists would not.
- **`SeedChain.footprint`** (new, pure): a seeded chain's map is
  defined at EXACTLY `ns.map (·.1)`. This is what makes
  "same footprint" a stated conjunct on the actual maps rather
  than prose: `∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome`
  follows from the two seeds plus `k ∈ (ns.reverse).map (·.1) ↔ k ∈
  ns.map (·.1)` — the reversal permutation.

## 2. The flagship restatement (audit items 2-4; THE SANCTIONED
STATEMENT CHANGES of this phase, itemized old → new)

Every changed statement (the oracle's complete list, §5) is in the
list-reverse family; nothing else moved.

- `list_reverse_certified` — OLD: partial, seeded chain only,
  conclusion `∃ p', v = ptrVal p' ∧ ChainAt σ' p' xs.reverse`
  (values-only chain "exists in the final memory" — audit F-06's
  finding verbatim). NEW: the seeded chain `m₀` is quantified NEXT
  TO an arbitrary disjoint frame footprint `R` (`m₀ ##ₘ R`,
  `Sat σ₀ (m₀ ∪ R)` — the `SemTriple` rest-quantifier shape at the
  driveJ lane), and the done-case concludes
  `∃ p' Q, v = ptrVal p' ∧ SeedChain Q p' ns.reverse ∧
  (∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome) ∧ Q ##ₘ R ∧
  Sat σ' (Q ∪ R)` — in-place + same-footprint + frame verbatim.
  GF binder DROPPED (SpikeGF-concrete).
- `list_reverse_certified_total` — OLD: unconditional
  `.done (ptrVal p') σ'` at `13·|xs|+7` with `ChainAt` only. NEW:
  same seed+frame hypotheses, same full conclusion as the partial
  form, still unconditional at the derived bound `13·|ns|+7` — the
  exit criterion's four properties (same-footprint, in-place,
  frame, termination) in ONE public statement. GF-free as before.
- `list_reverse_terminates` — hypotheses aligned (seed + frame,
  `Sat` over the union); conclusion unchanged (strong
  normalization). GF binder dropped.
- `list_reverse_demo` — instantiated at `[(1,1),(2,2),(3,3)]`,
  frame quantified, new conclusion + the demoted `ChainAt` readout
  conjunct (via `seedChain_chainAt`). GF binder dropped.
- Predicates re-indexed (spec idiom, not theorems): `isList`,
  `ChainAt`, `SeedChain` + their intro/equation lemmas and the
  interior derivation (`lrLs`/`lrLsT`/`lrPost` gain the frame
  conjunct `RF`; `lr_body_wps`/`lr_body_wpt` thread it).
- RETIRED (2 declarations deleted): `isList_readout` and
  `lrPost_to_readout` — the interior readouts that opened the state
  interpretation per-exhibit; replaced by `isList_to_cells` +
  `lrPost_readout` through the core `cells_readout` (§4). The old
  values-only conclusion form is not kept as a corollary: it is
  strictly subsumed, and the id-indexed `ChainAt` remains as
  demoted corollary vocabulary (`seedChain_chainAt`, consumed by
  the demo) with a one-line note at the definition.

**The frame-export mechanism** (audit: "the internal proofs already
own it; the readout discards it"): the frame proposition rides THE
LOOP INVARIANT (`lrLs ns RF` / `lrLsT ns RF` gain `∗ RF`), because
`wps_frame` deliberately releases frames at back edges — the label
invariant is the only thing that crosses a jump. At the launch, RF
is instantiated to the big-sep of the quantified footprint `R`
(`lrCellFrame R`), and the readout re-materializes the
postcondition's `isList` as a cell map Q (`isList_to_cells`, with
all disjointness FORCED by ownership validity —
`bigSepM_own_disjoint`), then lands the pure conclusion through the
core `cells_readout` exactly as `SemTriple`'s proof does. The
statements are therefore the jump-lane analog of `SemTriple`'s
∀R-quantifier, which is where the semantic frame was already
exported for straight-line programs.

## 3. The second client — tree rotation (audit item 6, the
accident-detector)

`TreeRotExhibit.lean`: binary-tree right rotation,
`node x vx (node y vy a b) c → node y vy a (node x vx b c)`.
- STRUCTURALLY DIFFERENT on every axis the list fixed: one
  allocation per node but THREE fields (`long[3]`, value/left/right
  at 0/8/16 — a third layout), BRANCHING recursion in
  `isTree`/`SeedTree` (two sub-structures per node, two disjoint
  sub-maps + a three-way disjointness spine), a straight-line
  program (no labels — the frame rides plain ∗, no invariant), and
  a conclusion whose id-list transformation is a PERMUTATION that
  is NOT a reversal (`rotate_ids_mem`) — a list accident that did
  not become a logic law.
- **ZERO CORE-LOGIC EDITS** (the fresh-client discipline, replayed
  at Phase 4): the commit diff touches only the new module, the
  lib-root import, and the Audit pins. Every memory rule is a
  one-line client instance of the generic
  `wps/wpt_load_cell_at`/`wps/wpt_store_cell_at`; the pointer-image
  byte algebra is REUSED from the list exhibit (pointer
  serialization is layout-independent); the splice algebra consumes
  the core `spliceBytes_slice_above` law — present since Phase 2,
  first exercised here (the two-field list node never had a field
  above a spliced range). No stop-and-report condition arose; no
  missing law was found.
- Exports at the flagship shape: `tree_rotate_certified` (partial,
  drive lane) and `tree_rotate_certified_total` (unconditional at
  the constant straight-line budget 19 = 1 x-bind + 4+4 loads +
  4+4 stores + 2 exit), both with seed + frame + footprint-equality
  conjunct, both SpikeGF-concrete, both trio-pinned in Audit.
  Satisfiability witness: `trDemo_seed` (2-node concrete tree,
  decode facts `rfl`).
- One authoring note: the program binds the root pointer to a
  symbol first (`lets x = pure(px) in …`) so both store operands
  are symbols — the operand-evaluation mirror steps
  (`Step.store_eval`) take non-value pexprs, which is the honest
  ACTION_EVAL shape; a literal-operand store would be a different
  (canonical-redex) route, not a missing law.

## 4. Concrete wrappers + the phase-2 readout tidy (audit item 5;
F-06 tail; the census footnote)

- **No ghost-functor binder on any flagship**: all four list
  exports, both tree exports, and the demo are stated without
  `{GF : BundledGFunctors} [SpikeGpreS GF]` — proofs instantiate
  `SpikeGF` internally (the pattern `fib_certified_total`
  established). The census (§5.4 of the walkthrough, re-run)
  confirms: the IRIS bin of `list_reverse_certified` no longer
  contains the binder; what remains is iris-lean's finite-map
  LIBRARY vocabulary (`get?`/`union`/`##ₘ` + the `ExtTreeMap`
  instance) — the type of footprint maps, reported not hidden.
  Registered follow-on (not Phase-4 scope, statements untouched):
  `counter_loop_certified`/`fib_certified`/`array_sum_certified`
  still carry the binder; `semantic_triple_sound` keeps it
  load-bearingly (its hypothesis is an Iris judgment).
- **The phase-2 residual CLOSES** (2026-09-01 phase-2 notes §6.1:
  "centralizing the remaining open/close pattern into one core
  readout combinator is a Phase-4 tidy"): `stateInterp_readout`
  (Rules.lean) is the one place the state interpretation is
  opened/closed for exhibit readouts; `arr_wp_readout`,
  `cell_readout`, `struct_wp_readout` consume it, and the listrev/
  tree readouts go through the core `cells_readout`. grep: no
  `stateInterp_iff`/`fupd_mask_intro_discard` open remains in any
  exhibit readout lemma (the remaining exhibit-side
  `fupd_mask_intro_discard` uses are the state-independent pure
  readouts in Fib/Case/Wseq, which never opened the interp — noted,
  out of the residual's scope).
- Core ADDITIONS this phase (no core statement changed):
  `stateInterp_readout` (Rules.lean), `Sat.union_left`
  (Adequacy.lean).

## 5. The oracle (frozen-corpus regression)

Snapshots: `docs/2026-09-01_phase3-signatures-post.txt (byte-identical to the former 2026-09-01_phase4-signatures-pre.txt, deduplicated 2026-09-02)` (= the
phase-3 post, 16998 lines) /
`docs/2026-09-01_phase4-signatures-post.txt` (17860 lines). Derived
tally (labeled as derived; the snapshots are the record, compared
per-declaration): 2 DELETED, 22 CHANGED, 124 ADDED.

- DELETED (2): `isList_readout`, `lrPost_to_readout` (§2 — interior
  readouts replaced by the cells route).
- CHANGED (22) — ALL in the sanctioned list-reverse family:
  the four exports `list_reverse_certified`,
  `list_reverse_certified_total`, `list_reverse_demo`,
  `list_reverse_terminates`; the spec predicates `isList`,
  `ChainAt`, `SeedChain` (+ `isList_cons`, `isList_cons_intro`,
  `isList_shape`, `seedChain_isList`, `demo_seed`); the interior
  derivation (`lrPost`, `lrLs`, `lrLsT`, `lr_body_wps`,
  `lr_body_wpt`, `lr_blockSpecs`, `lr_blockSpecsT`, `lr_wps`,
  `lr_wpt`, `lr_wp_readout`). NOTHING outside the family changed —
  in particular the whole fib/array/struct/loop/production surface
  and every core module statement is verbatim.
- ADDED (124): the TreeRotExhibit module (~100), the new listrev
  lemmas (`SeedChain.footprint`, `seedChain_chainAt`,
  `isList_to_cells`, `lrPost_readout`, `lrCellFrame`,
  `get?_union_right`, `demoNs`, …), the core combinator
  `stateInterp_readout`, and `Sat.union_left`.
- Axiom cones: every flagship pinned EXACTLY the trio in-build
  (Audit.lean, including the two new tree pins); sweep tail now
  "1067 theorems BOUNDED … 1995 constants" (quoted in README/
  walkthrough).

## 6. Audit Phase-4 items and the exit criterion, checked

1. **"Carry node identities/footprint through isList and
   ChainAt."** — DONE (§1; pinned ids, not existential).
2. **"Prove final node IDs are exactly a permutation of the initial
   IDs."** — DONE, in the strongest form: the final id list IS
   `(ns.map ·.1).reverse` (`SeedChain Q p' ns.reverse`), plus the
   footprint-equality conjunct on the maps; for the tree the
   rotation permutation is `rotate_ids_mem`.
3. **"State and prove preservation of an arbitrary disjoint
   frame."** — DONE (`R` quantified, returned verbatim in
   `Sat σ' (Q ∪ R)`; mechanism §2).
4. **"Add a total step or total-WP theorem for reversal."** — was
   pre-paid by Phase 3; RESTATED to the full conclusion
   (`list_reverse_certified_total`), still unconditional.
5. **"Export a concrete engine-only wrapper using SpikeGF."** —
   DONE, stronger: the flagships themselves are SpikeGF-concrete
   (§4), no separate wrapper indirection.
6. **"Add a second, structurally different client."** — DONE
   (§3), zero core edits.

**Exit criterion** ("the public theorem literally states
same-footprint, in-place reversal plus termination and frame
preservation"): `list_reverse_certified_total` states, in one
public theorem: the unconditional `.done` equation (termination
with the derived bound), `SeedChain Q p' ns.reverse` (in-place: same
allocations, own values, reversed relinking), the literal
footprint-equality conjunct (same footprint), and `Q ##ₘ R ∧
Sat σ' (Q ∪ R)` for the quantified disjoint `R` (frame
preservation). MET.

## 7. Registered follow-ons (honest, named)

- The pre-Phase-4 loop exports (`counter_loop_certified`,
  `fib_certified`, `array_sum_certified`) still carry the
  ghost-functor binder; de-GF-ing them is mechanical (the
  `fib_certified_total` pattern) but is a statement change and was
  not in this phase's sanctioned set.
- `array_sum_certified`/`counter_loop_certified` do not state
  frames; their conclusions remain single-cell readouts. The
  flagship shape is available to them at the same cost as the tree
  client if ever wanted.
- The census's registered future gate (freeze expected partitions
  in-build) remains open; this phase only re-ran the instrument and
  updated the pasted output.
- `hfuel2` on the partial flagship remains the interim in-budget
  scaffolding it was (phase-3 note carried forward); the total form
  has no fuel hypotheses.

## 8. Operational findings

- `rw` with a closed pattern rewrites ALL occurrences at once: in
  the tree demo's disjointness proofs a single `get?_empty` rewrite
  discharges every `get? ∅ k` occurrence — chained duplicates fail
  with "pattern not found" (three sites hit during the slice).
- Inside `iapply`, premise terms elaborated with unassigned ψ/Φ
  metavariables make `istart` fail ("does not support creating
  mvars"); passing the combinator via term-level `exact
  stateInterp_readout (fun … => by …)` under a known expected type
  elaborates cleanly (the `by` block is delayed until the outer
  unification has pinned the implicits).
- The `Vobject (OVpointer q)` vs `ptrVal q` spelling matters to
  unification at rule application sites: after `update_env_spec`
  binds `Vobject ov`, a `show … from rfl` rewrite to the `ptrVal`
  spelling (the lr pattern) is needed before store rules whose
  operand facts are stated with `ptrVal`.
