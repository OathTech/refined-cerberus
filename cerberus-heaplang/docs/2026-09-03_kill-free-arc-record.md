# The kill/free arc, K0–K4 — the record (2026-09-03)

Branch `kill-free-k2` (a linear history; every hash below is on it —
`git log --oneline 78084a7..` from the charter's DECISIONS entry). Charter: DECISIONS
2026-09-02 "[USER] THE KILL/FREE ARC INCLUDES DYNAMIC ALLOCATION" ("for
real Reynolds/O'Hearn I think we need both") over the design note
`docs/2026-09-02_kill-free-design-spike.md` (`bdf8729`) and the
2026-09-03 "[USER] OVERNIGHT AUTONOMY" ruling (capacity included as
K2.5; the re-pin after K4; the fuel-lane restatement after calls; no
merges overnight; every slice gated twice and range-audited). Pinned
semantics throughout: cerberus-lean `ddcfc919972a31bc43a0454e6b2e76a19e6c4594`.
Provenance: [USER] and [AGENT] as in DECISIONS.md; audit verdicts are the
auditors' own words from the cited records. Derived tallies are labelled.

## The slices

**K0 — the global memory well-formedness invariant (acceptance goal 3).**
`89cd906` (record `docs/2026-09-03_k0-notes.md`; DECISIONS `e520b4f`).
`MemWF σ` — nine components, each cited to the engine's writers in
`CerbMem.lean` — placed in `CohG` (under cursor presence) and in
`LaunchCoh` (unconditional); five footprint-relative launch facts retired;
`create_fresh_global`; `prodMem₀_memWF`; preservation for `loadM`/`storeM`/
`allocateObject`; the `allocateRegion`/`killM` obligations stated for K3
without stubs. Two design-note premises FALSE by measurement: (a) the
engine admits zero-size regions (`allocateRegion`: `sizeN.toNat`, no `max
1`), so the invariant carries `size_nonneg`, not the note's `size_pos`;
(b) `killM` never touches `dynamicAddrs` — the only writer is
`allocateRegion`'s prepend — so "every dynamic address is a live base" is
NOT an engine invariant; the component is `dyn_lo`/`dyn_disj`. Pins 159 →
165. Range audit `b374671` (`docs/2026-09-03_k0-audit.md`): PASS after one
correction — M-1 the record's "meaning strengthens" for the alloc-lane
exports (a stronger `LaunchCoh` HYPOTHESIS makes them weaker claims about
arbitrary initial states; nothing reachable from `prodMem₀` lost;
corrected); N-1 (load-bearing for K3) `free` of a created object can
SUCCEED after a zero-size `malloc` at the same base, so only `dynamic =
true → base ∈ dynamicAddrs` is preserved and K3's `free` must read the
flag from the metadata cell. Upstream note filed: `9f0c20b`
(`../docs/2026-09-03_upstream-note-dynamic-addrs.md`).

**K1 — the metadata cell.** `32179e9`, `29f475f` (record
`docs/2026-09-03_k1-notes.md`; DECISIONS `a0a02fe`). `MetaCell` gains
`alive`, `readonly`, `dynamic : Bool` and `ty : Option ctype` (regions
untyped), each field cited to its engine writer; `MetaCoh`: live → record
present agreeing on base/size/type/writability; dead → dead-listed and
erased; dynamic → base ∈ `dynamicAddrs` (the one direction the engine
preserves). New bundles `regionOwn`/`regionView`, `readonlyCell` (+
`load_atomic_readonly`; the store refusal `storeM_readonly_kills` is an
engine fact), `deadObj`/`deadRegion`; `cur_meta_lo` returns as a `CohG`
field. 0 public statements changed. Pins 165 → 185. Range audit `2f06c10`
(`docs/2026-09-03_k1-audit.md`): PASS — coupling sound and complete
against every engine writer; the producer-less bundles proved non-vacuous
by constructed states; carried M-1 (`∈` vs `contains` vocabulary — bridge
lemmas landed at K2), N-2 (`Frag.store` admits the locking store; the
rules fix `lk = false`), N-3 (`alloc_global` wording).

**K2 — THE DISPOSE RULE (the static kill).** `9ea5d71`, `46ed41f` (record
`docs/2026-09-03_k2-notes.md`; DECISIONS `f69314c`). `Step.kill`/`kill_eval`
mirror `step_action`'s Kill arm verbatim (bare `Vunit` continuation;
generic in the kind — the engine discards the `Static0 ty` payload);
`Frag.kill`/`kill_op` static only; `kill_atomic`/`wps_kill`/`wpt_kill` (+
`_emp` textbook forms, `_eval` operand forms) at `pointsToCell … (.own 1)`
with post `deadObj`; `MemWF.killM` PROVED for both arms; completeness rows
with the exact kill reasons (UB179a, UB179b, the non-UB `Free_out_of_bound`);
the K1-audit items done. Pins 185 → 205. Range audit `73c41a9`
(`docs/2026-09-03_k2-audit.md`, on a fixed copy at `46ed41f` so K2.5 could
start): PASS — M-1 the WALKTHROUGH repeated the falsified "created base
never in `dynamicAddrs`" premise, M-2 three sites still called
`MemWF.killM` open (both fixed at K2.5), N-2 the engine-ACCEPTED static
kill of a dynamic region is mirrored but has no rule (K3 to decide).

**K2.5 — THE SPLITTABLE ALLOCATION BUDGET.** `77c5277`, `5bfa4f9`, `f0b4b67`
(record `docs/2026-09-03_k2.5-notes.md`; DECISIONS `c4aed3f`). `allocBudget n`
on iris-lean's later-credit camera (`Auth Credit`, a fresh ghost name);
`allocBudget (a + b) ⊣⊢ allocBudget a ∗ allocBudget b`; the coupling
inequality `B ≤ headroom lastAddress` inside `stateInterp`; the engine
bound `allocCost tds ty al = sizeof ty + max al 1 − 1`; `create_atomic`/
`wps_create`/`wpt_create` restated over the budget, the plan forms
derivable; `allocCap`/`PlanFits` pruned. Honest classification: at the
RULE level strictly more general; at the LAUNCH level plan ⇏ budget, the
covered initial states shrink by ≤ align−1 bytes per allocation — the
price of the ∗-splittable shape, irrelevant at the cold-start headroom
`2^48 − 9`. This CLOSES the professor's second-review residual
"allocation capacity is still not a ∗-resource" (`docs/2026-09-02_professor-review-2.md`,
its one delivery item); K4's region loop is its first loop client. Pins
205 → 221. Range audit `f7bf520` (`docs/2026-09-03_k2.5-audit.md`): PASS —
fresh ghost name, laws re-proved over the library's lemmas, coupling
preserved and initialised in both lanes, engine bound tight for size > 0;
M-1 `wpt_create` not pinned (the record's claim false — pinned at K3);
M-2 the budget header's size-0 claim false at `lastAddress ≤ 0` (a K3
obligation — closed by `la_pos`).

**K3 — DYNAMIC ALLOCATION AND FREE (acceptance goal 3 closed).** `752eb18`,
`af309f4`, `0453ec1`, `b77d9a7` (record `docs/2026-09-03_k3-notes.md`;
DECISIONS `1b45a17`). `Step.alloc`/`alloc_eval` mirror `step_action`'s
Alloc0 arm (two integer operands; bare pointer continuation); the dynamic
kill is the EXISTING `Step.kill` — `Frag.kill`/`kill_op`'s static-only
restriction LIFTED (a strict generalization, the one deliberate CHANGED
statement class); `MemWF.allocateRegion` PROVED — every stated obligation
of the invariant is a theorem; `MemWF.la_pos : 0 < lastAddress` added (the
K2.5 audit's M-2). Rules: `alloc_atomic`/`wps_alloc`/`wpt_alloc` (+ `_eval`)
over `allocBudget (regionCost al sz)` → `regionOwn` of unspecified bytes
with `0 < a ∧ a + size ≤ 2^64`, premise `0 < regionCost` (the zero-cost
shape `sizeN ≤ 0 ∧ alignN ≤ 1` outside, classified); `free_atomic`/
`wps_free`/`wpt_free` (+ `_emp`) at `regionOwn (.own 1)` → `deadRegion`,
the dynamic check spent from the METADATA CELL (`killM_success_dynamic`),
never from `dynamicAddrs`. Completeness: alloc's only refusal is the OOM
kill; `free(NULL)` is a no-op STEP; UB179a/UB179b/`Free_out_of_bound`
enumerated. The N-2 decision: the static kill of a region has NO rule by
design, with three companions (`free` of a created object, `free(NULL)`,
the zero-cost `alloc`) — on every surface. Pins 221 → 248. Range audit
`ad0cf41` (`docs/2026-09-03_k3-audit.md`; DECISIONS `100eb83`): PASS, no
High — M-1 a stale Heap header sentence, N-1 three forward-tense comments,
N-2 the zero-cost shape is `size ≤ 0 ∧ align ≤ 1` (negative sizes collapse
to size 0), N-4 cold-start address wording; `la_pos` confirmed an engine
invariant; OOM the only alloc failure; `free(NULL)` a mirrored no-op step.
All four items applied at K4 (below).

**K4 — THE EXHIBITS and the documentation closure.** `ed3a9fe` (1/3),
`daa9b5c` (2/3) and the 3/3 commit (this record travels with 3/3; record
`docs/2026-09-03_k4-notes.md`). DisposeExhibit.lean: dispose-a-list over
ListRevExhibit's created nodes — `dl_wps` (`{isList head ns} dispose {ret
unit. deadNodes ns}`), `dl_wps_emp` (the textbook `{isList head ns}
dispose {emp}`), `dl_wpt` at the DERIVED budget `12·|ns| + 6`, the framed
forms, `dispose_list_certified_total` (the `driveU` equation, PROVISIONAL:
every node id in `deadAllocations` with its record erased, the frame
returned verbatim) and `dispose_list_certified_production` (the shipped
pipeline on the two-node build-and-dispose file: EXACTLY ONE Active
execution delivering `Vunit`, two DISTINCT allocation ids dead and
erased — the proof witnesses them as the two created nodes; the statement
names no node [erratum per the K4 range audit's M-2, applied at K5; the
original sentence read "the two engine-picked ids"]) — the build prefix
restated generically in its continuation
(`lrProdPrefix_wpt`). RegionLoopExhibit.lean: `n` regions from one linear
budget — `rl_wps`/`rl_wpt` (`{allocBudget (n.toNat · regionCost al sz)}
rl(n) {emp}`, the budget as the LOOP INVARIANT split per iteration, total
at `7·n.toNat + 3`), `region_loop_certified_total` (under `LaunchCoh`,
PROVISIONAL) and `region_loop_certified_production`. Pins 248 → 269; the
manifest 22 constructors, 23 rule rows, 0 red, 15 exhibit modules —
every kill/free/alloc law with an exhibit consumer. THE FINDING: the
chartered malloc'd LINKED list is not statable — no load/store rule over
`regionOwn`/`regionView` exists (every access rule is over the object
bundles; a coercion is unsupported by the coupling by design; the memM
seams `loadM_live`/`storeM_live` already hold at any metadata cell, so
the remedy is a rule addition) — recorded on every surface, nothing
weakened; the region loop is landed as the `alloc`/`free` exhibit and
named as a substitute. The K3-audit items M-1/N-1/N-2/N-4 applied. The
snapshot: ADDED 136 / REMOVED 0 / CHANGED 0. FULL gate at 3/3 (the K4
record §10). Range audit: to be dispatched by the orchestrator over
`100eb83..<3/3>`.

## The design note, measured (what the arc corrected in `2026-09-02_kill-free-design-spike.md`)

1. §3's `size_pos` → `size_nonneg`: zero-size regions are admitted
   (K0, measured at `allocateRegion` :1538).
2. §0/§3's "every dynamic address is the base of a live allocation" is
   false: `killM` never cleans `dynamicAddrs` (K0); the invariant carries
   `dyn_lo`/`dyn_disj`, the coupling is one-directional, and `free`'s
   premise comes from the metadata cell (the K0 audit's N-1). Filed
   upstream (`9f0c20b`).
3. §4's eval mirrors "general in the values" → the operand-evaluation
   steps pin the result shapes (pointer for kill, integers for alloc);
   the other shapes are the ILLTYPED-at-distance-one rounds, classified
   (K2, K3).
4. §5's smoke readout `σ'.deadAllocations = [1]` is not derivable through
   the public rules — the honest readout is the per-id `contains`/erased
   pair at the existential id (K2); the K4 exhibits state it per node.
5. §5's `kill_launch_smoke` at drive length 4 → 5 (the operand-evaluation
   round; K2).
6. §1/§6's slicing (K3 = the kill RULES, K4 = DisposeExhibit) was reshaped
   by the [USER] inclusion of dynamic allocation and the capacity ruling:
   K2 = the static kill's rules, K2.5 = the budget, K3 = alloc/free, K4 =
   two exhibits.
7. §1's alloc sketch `∃ p, ⌜w = ptr p⌝ ∗ …` → the pointer is `cellPtr id
   a` with `id a` existential and the bounds `0 < a ∧ a + size ≤ 2^64`
   (K3 §4(a)/(b)); `regionCost` prices the RAW size (`allocateRegion`
   does not pad to `max 1`).
8. §6's size estimate (55–75 declarations, 1500–2200 lines, 4–5 slices)
   vs. the arc: six slices (K2.5 added), pins 159 → 269 (+110), snapshot
   entries at K4 2540 (K3 post 2404; the per-slice deltas are in the
   slice records).
9. §5's consumer shape: the exit is the unit value and the post carries
   `deadNodes ns` (the textbook `emp` derived); the note's `c·|ns| + d`
   is `12·|ns| + 6` (K4).
10. NOT anticipated by the note: `MemWF.la_pos` (the K2.5 audit's M-2 —
    the cursor is positive; needed to price size-0 regions), the K2-audit
    N-2 decision (static kill of a region: no rule), and the K4 finding
    (region loads/stores have no rule).

## Carried from the K3 range audit (applied at K4, commit `ed3a9fe`)

M-1 Heap header (every `MemWF` obligation is a theorem); N-1 three
forward-tense comments (Heap `loadM_live`, the K1-bundle header, Wps
`wps_kill`); N-2 the zero-cost shape `sizeN ≤ 0 ∧ alignN ≤ 1`
(`alloc_atomic` docstring, README companion (ii)); N-4 cold-start cursor
wording (`0xFFFFFFFFFFFF` is CerbMem's default, `prodMem₀` sits at
`errnoAddr = 0xFFFFFFFFFFF8`; Heap ×3, ARCHITECTURE, WALKTHROUGH, a dated
erratum in the K3 record).

## What remains (named, with movers)

- **The fuel-lane restatement (acceptance goal 1) — PROVISIONAL stays on
  every `driveU` export** (`MemTripleU`, the projections,
  `wpt_engine_boundU(_alloc)`, and the exhibits' `driveU` rows including
  K4's `dispose_list_certified_total`/`region_loop_certified_total`). The
  semantics-side fix landed upstream (cerberus-lean `f95ef8d9c`); the
  [USER 2026-09-03] sequence is the RE-PIN after K4 (cheap; the scout
  found zero renames and four errors of one cause), the calls arc, then
  the restatement once on the final configuration.
- **The residuals**: `hbsz` inside `Frag.case_value` (carried, provable
  by a fuel-indexed induction over `subst_sym_expr`); `eval_uncovered`
  and `run_surplus` (`OpenRound`; movers named in ARCHITECTURE §7).
- **Region access rules (the K4 finding) — CLOSED at K5 (2026-09-03,
  record `docs/2026-09-03_k5-notes.md`)**: `regionLoadAt_atomic`/
  `regionStoreAt_atomic` over the typed region view `typedRegionView`,
  through `loadM_live`/`storeM_live` at `regionCell`; faces at both
  strata (typed view and whole-region forms); manifest rows for
  `Frag.load`/`Frag.store`; THE MALLOC'D LINKED LIST exhibit
  (MallocListExhibit.lean: `ml_wps`/`ml_wpt`, `malloc_list_certified_total`
  PROVISIONAL, `malloc_list_certified_production`). Pins 269 → 294. K5.1
  (the K5 range audit's M-1, record `docs/2026-09-03_k5.1-notes.md`): the
  four statements STRENGTHENED to `n.toNat` DISTINCT dead ids
  (`ids.Nodup`) via the new public `regionOwn_ne`/`regionOwn_deadRegion_ne`;
  pins 294 → 296.
- **Two `save` labels in one program (the K5 audit's N-1)**: the malloc'd
  list is ONE label with two phases because the two-label form needs a
  two-entry label-map lookup law (`lookupLabel` at `fmapAddBy … (fmapAddBy
  … fmapEmpty)`; EnvLaws has only the singleton `fmapLookupBy_addBy_empty`).
  Mover: an EnvLaws slice with the two-entry (or general) lookup law.
- **The cursor heap as a device**: since K2.5 no client owns the
  allocator cursor (`cursorOwn`'s exclusive fragment lives inside
  `budgetInterp`), so the cursor ghost heap (`cursorGS`/`cursorInterp`)
  is a proof device that could be folded into the budget interpretation
  as a plain existential — an internals simplification, trust surface
  unchanged.
- **API hygiene — DONE at K5**: public `deadObj_readout`/`deadRegion_readout`
  (Adequacy.lean; the K4 audit's N-1), with `deadObj_dead`/`deadRegion_dead`
  reclassified in API.lean as the public consequence faces (a list of dead
  ids is read off one state through them under `stateInterp_readout`).
- **Upstream**: the `dynamicAddrs` under-reporting of UB179a (`9f0c20b`,
  the tray note) — an operator network window.
