# Foundations Phase 2 — the generic memory layer (design record + oracle + exit criteria)

Worker slice record, foundations arc Phase 2 (arc plan
`docs/2026-08-31_foundations-arc-plan.md`; audit F-04/F-10 and the
Phase-2 remediation list,
`docs/2026-08-31_cerberus-heaplang-foundational-audit.md`).
Commits: `3335859` (1/3, the ownership split), `2f15f98` (2/3, the
fresh client + create consumed), this commit (3/3, oracle+records).
Gates: `scripts/test_unit.sh` ALL GREEN at every commit.

## 1. The ownership split (the view model)

The Phase-1 carrier was allocation-rooted: one ghost cell per
allocation id holding `(base, type, bytes)`; whole-cell rules only,
interior access by per-layout example rules (the F-04 defect). The
Heap.lean header had pre-registered the growth step verbatim:
"split into a per-byte heap + a per-allocation metadata heap". This
phase executes exactly that split, donor-shaped (Caesium's
`heap : gmap addr byte` + `allocs : gmap alloc_id allocation`;
RefinedC `theories/caesium/ghost_state.v` — `heap_mapsto` +
`loc_in_bounds`/`alloc_alive` — is the normative reference):

- **Byte heap** `Int ↦ AbsByte` — the ghost fragment of the engine's
  own `bytemap`, keyed by absolute address. Range ownership
  (`bytesOwn a dq bs`) is a recursive ∗ of per-byte cells, so
  subrange split/join is REAL separating conjunction
  (`bytesOwn_append` — split at any list decomposition, both
  directions).
- **Metadata heap** `Int ↦ MetaCell (base, type)` — the
  provenance/metadata AUTHORITY. `loadM`/`storeM` success is decided
  by the allocation table (liveness, bounds, writability, atomic
  member — CerbMem.lean:1586-1696), so byte content alone can never
  entail access success; the metadata cell carries exactly those
  facts (`MetaCoh`) and is the per-allocation exclusivity anchor
  (`metaOwn_ne` replaces the old whole-cell `pointsTo_ne` in the
  footprint-disjointness lemma). Metadata is FRACTIONAL
  (`metaOwn_fractional`, classical fractional permissions — Boyland);
  views take a fraction, and view split/join does explicit fraction
  arithmetic (`pointsToView_split`/`pointsToView_join`).
- **THE VIEW** `pointsToView id a aty off dqm dqb vty bs` =
  metadata knowledge (fraction `dqm`) ∗ in-bounds + footprint-length
  facts ∗ the range's bytes (fraction `dqb`). The typed subrange
  split law: a view whose footprint decomposes as two type
  footprints splits into the two adjacent subviews (meta fraction
  split, byte range split); join is the exact converse.
- **The maximal view**: `cellOwn i dq c` = view at offset 0 with
  view type = allocation type, both fractions `dq`, PLUS the
  image's decode-inertness (`decIndep`) as a pure payload
  (`cellOwn_view` is the two-way bridge). `pointsToCell` keeps its
  statement shape over `cellOwn`; the ↦c notation and every
  consuming statement are unchanged.
- **Coupling** `CohG σ mm mb mk`: byte cells = the bytemap readout
  (`byteAt`); metadata cells = `MetaCoh` + PAIRWISE RANGE
  DISJOINTNESS (`metas_disj` — footprint disjointness at readout now
  comes from the metadata authority, not from byte-level
  confrontation, which also keeps zero-sized cells sound); cursor
  cell (below). `Coh`/`CellCoh`/`SpikeCell` survive UNTOUCHED as the
  pure footprint vocabulary of the exported face (`Sat`, `SemTriple`,
  every `*_certified` statement is byte-identical).

Inertness relocation: the old carrier stored per-cell side-table
inertness inside the coupling (`CellCoh.dec_indep` via `Coh`). Bytes
are typeless, so the invariant cannot carry it; it rides instead as
(a) the pure `decIndep` payload of `pointsToCell`/`cellOwn`
(producers: `StorableAt.stored_dec` at stores, seed facts at launch,
`hinert` at create), and (b) explicit decode premises on the generic
rules — which is exactly the audit's requested parameterization.

## 2. The generic typed-subrange rules (F-04 retired)

Certified ONCE against the engine's interior behavior:

- memM stratum: `loadM_at` / `storeM_at` (Heap.lean) — any accessed
  type and offset; premises = metadata backing (`MetaCoh`), bounds,
  the byte-range readout, decode (load) / the `StorableAt`-shaped
  serialization facts (store), the `loadTrapV` trap exclusion. These
  generalize `loadM_success`/`storeM_success` (kept, statement-frozen,
  as the whole-cell instances) and subsume the deleted
  `loadM_interior_int`/`loadM_interior_nodePtr`/`storeM_interior_nodePtr`.
- WPS stratum: `wps_load_at` / `wps_store_at` — the VIEW rules. A
  view store REPLACES the view's byte image wholesale (the store
  footprint IS the view's extent): no splice appears in the generic
  statement.
- Derived whole-cell interior forms: `wps_load_cell_at` /
  `wps_store_cell_at` — split the maximal view at the accessed
  subrange, run the generic rule, rejoin. The store's recomposition
  is LITERALLY `spliceBytes` by definition (take-prefix ++ image ++
  drop-suffix), which is where the listrev slice's splice lemmas
  went: generalized into core (`spliceBytes_slice_below/_self/_above`,
  `readBytesFrom_write_interior`, `Coh.store_interior`), not
  duplicated.

Client instances (each a one-line term, no interp opening, no memM
seam): `wps_arr_elem_load` (ArrayExhibit — int element at 4·i),
`wps_load_node_field`/`wps_store_node_field` (ListRevExhibit —
node* field at offset 8), `wps_struct_x_store`/`wps_struct_y_store`
(StructExhibit — int fields at offsets 0/8).

## 3. The allocator resource (D26 retired) — design reasoning

D26's finding: `allocateObject` kills ("out of memory",
CerbMem.lean:1479) when `alignDown((lastAddress − size).toNat,
align) == 0` — a condition no cell footprint constrains, so
`wp_create`'s reducibility obligation was undischargeable and
exhibits dodged by hoisting creates into cold-start prefixes.

Design: the cursor is a ONE-CELL ghost heap holding exactly the two
MemState fields the allocator reads and writes
(`AllocCursor = (lastAddress, nextAllocId)`). Rationale:

- The engine's allocator is a DETERMINISTIC DOWNWARD CURSOR — the
  fresh base is a closed form of owned state (`freshBase`), so the
  right resource is exclusive knowledge of the cursor, not a
  fancier allocation capability. (Donor comparison: Caesium's
  allocator is nondeterministic, so RefinedC's `alloc_new_blocks`
  quantifies the fresh block; here determinism lets the rule NAME
  the fresh pointer — `cellPtr nid (freshBase la align size)` — and
  the consumer computes with it.)
- **The OOM arm is handled by the resource's design, not assumed
  away**: `wps_create`'s `hnz : freshBase la alignN (sizeof ty) ≠ 0`
  is a PURE guard computed on owned cursor state — the exact mirror
  of the engine's kill test. A client with a concrete (or
  sufficiently bounded) cursor discharges it by arithmetic; no
  NotStuck assumption enters.
- CURSOR-CONDITIONAL coupling: `CohG`'s allocator-health facts
  (fresh ids unallocated and not dead; every ghost-tracked
  byte/metadata address ≥ lastAddress; metadata ids < nextAllocId)
  are all conditional on cursor-cell PRESENCE. Consequence:
  cursor-free launches (every pre-existing exhibit) owe nothing
  new — the frozen corpus re-proves without new hypotheses — while
  a cursor-owning launch owes exactly the facts `wps_create`'s
  soundness needs. The cursor-owning ADEQUACY LAUNCH VARIANT is the
  registered follow-on (named mover: a `spikeGhost_init`-style
  lemma emitting `cursorOwn` from initial-state health hypotheses);
  the wps-level consumer (`struct_create_store_wps`) demonstrates
  consumption today, and the production lane's cold-start create
  discharge (`exhibitA_prod`) is unchanged.
- Ghost steps of the rule: cursor update, metadata `genHeap_alloc`
  (freshness from `cur_meta_lt`), byte-range `genHeap_alloc_big`
  (freshness because the fresh range ends at or below the old
  cursor and all tracked bytes sit at or above it), `CohG.create`
  re-establishes the coupling with the advanced cursor.
- METADATA LIFETIME (named mover, also in the Heap.lean header):
  kill/free is outside the fragment, so metadata never dies. When
  kill joins the fragment the metadata heap gains the donor's
  alloc_alive/freeable split (fractional liveness + deallocation
  permission), and `wps_create` should then also emit the freeable
  token.

`wps_create` is the logic rule of record (the statement stratum is
the package's operative layer post-S1b); a base-WP `wp_create`
corollary through the `wps_sound` collapse at the label-free profile
is mechanical and deliberately not added (no consumer; the collapse
loses the tuple-pinned post shape the WP-level small axioms use).

## 4. The fresh-client test (audit acceptance test 2) — PASSED

`StructExhibit.lean`: layout `{int x @ 0; int y @ 8}` in one
16-byte `int[4]` allocation — a THIRD distinct layout (4-byte
fields, non-adjacent offsets, padding gap). The two-field update
program is certified end-to-end (`struct_update_certified`: drive
never kills/derails; any completed run reads back both field
images). **Zero core-logic edits**: commit `2f15f98` touches no
core module beyond import registration and the manifest generator's
create row — verifiable from `git show --stat 2f15f98` (files:
StructExhibit.lean NEW, CerberusHeapLang.lean + Audit.lean imports
and pins, README.md, scripts/capability_manifest.lean,
docs/CAPABILITY_MANIFEST.md). Layout-swap evidence for the audit's
criterion 2: three different layouts (array elements, node fields,
struct fields) now consume the SAME two generic rules with only
offsets/sizes/decode facts changing.

Also in the module: `struct_create_store_wps` — the allocation
consumer (create a fresh struct from cursor ownership alone,
initialize its x field through the generic subrange store; no
cold-start hoisting).

## 5. The oracle (frozen-corpus regression)

Snapshots: `docs/2026-09-01_phase2-signatures-pre.txt` (14499 lines,
at S1c close) / `docs/2026-09-01_phase2-signatures-post.txt` (16051
lines). Derived tally (labeled as derived; the snapshots are the
record): 8 deleted, 32 changed, 172 added declarations.

DELETED (8) — exactly the F-04 evidence list plus the carrier
fields: `loadM_interior_int`, `wps_load_interior`,
`loadM_interior_nodePtr`, `storeM_interior_nodePtr`,
`wps_load_interior_node`, `wps_store_interior_node` (the six
retired interior rules/seams); `SpikeGS.heap`,
`SpikeGpreS.heap_pre` (the old single-heap fields, replaced by the
three-heap fields).

CHANGED (32) — all inside the sanctioned plumbing class:
- 10 auto-generated structure plumbing items for the re-fielded
  `SpikeGS`/`SpikeGpreS` (mk/rec/casesOn/…);
- 3 unfolding lemmas whose right-hand sides ARE the restructured
  internals: `stateInterp_eq`, `stateInterp_iff`,
  `pointsToCell_iff`;
- 19 Iris-INTERIOR statements where the raw ghost `pointsTo i (.own
  1) c` big-sep/interp spelling became the `cellOwn` composite (or
  the interp argument changed shape): `spike_step_adequacy`,
  `engine_adequacyU`, `engine_adequacyJ`, `spike_engine_adequacy`,
  `bigSepM_own_disjoint`, `cells_readout`, `isList_readout` (now
  against the coupling components), `isList_cons`,
  `isList_cons_intro`, `seedChain_isList`, `arr_body_wps`,
  `arr_wps`, `arr_wp_readout`, `bigSepA_ptx`, `bigSepB_pts`,
  `bigSep_ptx_P`, `ptx_to_cells`, `ptx_to_cells_P`, `cells_to_mC`.

NOT changed (the frozen face): every engine-facing exported
statement — `Sat`, `SemTriple`, `ProvenTriple` (type),
`semantic_triple_sound`, `semantic_frame`, `Coh`, `CellCoh`,
`SeedChain`, `ChainAt`, `isList` (type), and ALL `*_certified` /
`*_engine` / `*_prod` theorems; the small-axiom statements
`wp_store`, `wp_load`, `wps_store`, `wps_load`, `exhibit`,
`exhibitC_triple`, `wps_exhibit_*`.

ADDED (172): the split carrier (heaps, wrappers, `CohG` + its
preservation lemmas, `MetaCell`/`AllocCursor`/`MetaCoh`), the view
stratum and its laws, the generic rules and their derived whole-cell
forms, the allocator seam (`freshBase`, `allocateObject_success`,
`wps_create`, `createExpr`), the launch/readout machinery
(`MetaByteOf`, `spikeCells_alloc`, `cellsOwn_facts/extract`,
`cellOwn_cellCoh`), the moved-in byte/serialization algebra, and the
StructExhibit module.

## 6. Audit Phase-2 exit criteria, checked against the tree

1. **"No example module defines a new WP/WPS lifting rule."** — The
   six example-local/interior lifting rules are DELETED; every
   exhibit memory rule is a term-level client instance (grep: no
   `wps_unfold`/`wp_lift_atomic_step` outside Rules/Wps). Residual
   note (honest, registered): exhibit READOUT lemmas
   (`arr_wp_readout`, `cell_readout`, `lr_wp_readout`,
   `struct_wp_readout`) still open the state interpretation
   READ-ONLY to consume the adequacy interface — through the core
   extraction lemma `cellOwn_cellCoh`, never a ghost update or a
   step presentation. Centralizing the remaining open/close pattern
   into one core readout combinator is a Phase-4 tidy, not a rule.
2. **"Array and list proofs survive replacement of their concrete
   layout by another layout satisfying the same generic view
   interface."** — Demonstrated constructively: three layouts
   (array 4·i elements, node 8-offset pointer fields, struct 0/8
   int fields) consume the same `wps_load_cell_at`/
   `wps_store_cell_at` with only layout parameters changing; the
   listrev textbook proof body was UNCHANGED under the rule swap
   (only the rule names and the cellOwn spelling moved).
3. **"A fresh struct example can be verified without editing core
   logic."** — `struct_update_certified`, commit `2f15f98`, zero
   core edits (see §4).

Arc-plan Phase-2 items: 1 (split + laws + agreement through the
coupling + maximal-view re-expression) DONE; 2 (generic in-bounds
typed load + full-ownership store, serialization/decode/compat/
side-table premises, replacing every interior rule) DONE; 3
(allocator-cursor resource, sound `wps_create`, D26 retired) DONE —
with the cursor-owning adequacy-launch variant registered as the
named follow-on; 4 (examples as clients, discharge facts moved out)
DONE.

## 7. Operational findings

- **omega anomaly (recorded verbatim as observed)**: in
  `CohG.create`-adjacent proof contexts, `omega` repeatedly failed
  on trivially-true Int goals (e.g. `base ≤ k` from
  `base + ↑(sizeof ty) ≤ k` with `0 < sizeof ty` in context), with
  the printed counterexample constraint set INCONSISTENT with the
  negated goal — i.e. the goal was seemingly not incorporated.
  `Int.le_trans`/`Int.lt_of_lt_of_le`-style explicit terms discharge
  the same goals instantly and are used at those sites (marked with
  a NOTE comment in Heap.lean). Not minimized; a candidate toolchain
  bug worth a small repro when convenient.
- The three ghost heaps share the key type `Int`; none is registered
  as a bare `genHeapGS` instance (outParam collisions) — all access
  goes through named wrappers with pinned instances, and the GenHeap
  operations are wrapped once (`byteHeap_*`, `metaHeap_*`,
  `cursorHeap_*`) with `letI`-pinned instances.
- `rw` inside the Iris proof mode rewrites the WHOLE entailment
  (spatial context included); the splice-recomposition proofs
  therefore transport along equalities with Lean-level `have hEnt`
  entailments instead of in-goal rewriting where hypotheses share
  subterms with the rewrite pattern.
