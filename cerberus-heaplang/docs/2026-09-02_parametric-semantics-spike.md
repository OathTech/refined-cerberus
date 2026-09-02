# Parametric-semantics design spike (read-only) — 2026-09-02

> **STATUS: EXPERIMENT — DEFERRED, POSSIBLY PERMANENTLY.** [USER
> 2026-09-02] ruling after reading the recommendation below: the
> interfaces are NOT adopted. Reason (operator): "abstractions should do
> some work for us. There's nothing especially wrong about proving the
> proof rules correct wrt the semantics directly, it just means that the
> proof discipline is a bit harder to enforce." Assessment agreed: with
> exactly one instance the interface relocates the same proofs behind a
> class (zero proof economy), the donor itself proves memory rules by
> inversion (§0.2), and the enforcement gap is small enough for a report
> line, not an architecture. This document is a DESIGN RECORD, not a
> plan; nothing in the tree implements it. Kept: the inventory script
> `scripts/parametric_inventory.lean` as an on-demand instrument (its
> "rule proofs naming memory-record fields / env-map representation"
> counts are the candidate speedbump line). Re-open triggers, both
> currently absent: (1) a SECOND instance — the logic needed over another
> Cerberus memory model; (2) a type layer that needs an abstract memory
> CONTRACT rather than the raw rules. Ruling recorded in
> `docs/DECISIONS.md`.

Branch `parametric-spike` @ `3ea128d` (alloc arc P3.5 close; OLD semantics
pin, no `TagDefs` parameter — the inventory baseline). No `.lean` in the
package was modified; the measurement script is
`scripts/parametric_inventory.lean` (257 lines — over the ≲150 asked for;
the surplus is the second table and the layout-definition sweep).

**The question ([USER 2026-09-02], verbatim):** "I also wonder if there's
some design work we could do to make the logic parametric in its
underlying semantics, i.e forbid 'semantics hacking' by quantifying over
what the semantics actually provides. This is a kind of parametricity
property (analogous to 'theorems for free')."

**Framing under test (orchestrator, not assumed):** the Iris
language-mixin pattern — a class of laws, WP theory proved once over any
instance — with two classes, CONTROL (evaluation-context mixin + the
save/run label protocol) and MEMORY (abstract memory model for
load/store/create/pointer-equality), each with exactly ONE instance proven
from cerberus-lean, rule soundness proved in modules importing only the
interfaces.

**Constraints folded in during the spike:** [USER 2026-09-02] "change one
thing at once" — the refactor is INTERNALS-ONLY under a frozen public
spec (§6); the re-pin in flight makes the tag-definition environment an
explicit leading `TagDefs` argument on the memory functions (§2.4).

## 0. Summary of findings

1. **Measured (§1):** of 76 rule theorems in Rules/Wps/Wpt, 44 unfold the
   `Step` relation by definition in their own proof (constructor or
   `casesOn`), 0 use it only through `Step.*` lemmas, 14 are clean (pure
   logic over other rules). 17 rules touch CohG/cursor/GenHeap internals
   directly; 24 name generated engine DEFINITIONS in the proof that do not
   occur in their statement; 28 touch the env-map operations
   (`update_env`/`update_env_aux`/`bindArgs`) directly. The eight worst
   are the memory rules (`*_create_cursor_internal`, `wp_store`/`wps_store`,
   `*_store_at`, `*_load_at`): `wp_store` names all 14 `CerbMem.MemState`
   field projections and `MemState.mk` in its proof.
2. **The donor does NOT do what the framing assumes at the memory level.**
   RefinedC's `wp_deref` (lifting.v:222) inverts the concrete step relation
   (`inv_expr_step`, `DerefS`) and uses concrete-heap lemmas
   (`heap_at_inj_val`, `heap_upd_heap_at_id`, `heap_read_na`); the
   Caesium mixin `c_lang_mixin : EctxiLanguageMixin …` (lang.v:714) supplies
   only the evaluation-context/bind machinery. Iris-style parametricity is
   control-only in the donor; memory rules unfold the semantics there too.
3. **Control at Iris-mixin granularity is a poor fit here (§2.1):** the
   Esseq frame is not an evaluation context (`Erun` discards it —
   `Lang.lean` header, `Step.sseq_inv`'s jump disjunct), so the mixin
   would be a bespoke "ectx-with-jump-exception"; the generic part is ~9
   laws and buys de-duplication of three proof triples (sequencing,
   annotation), while a construct-covering control interface is ~32 laws
   over 24 `Step` constructors — a mirror of the mirror (width creep).
4. **Memory is the payoff (§2.2):** every law the memory rules need is
   ALREADY a lemma in Heap.lean (`storeM_success` :309, `loadM_success`
   :336, `loadM_at` :818, `storeM_at` :864, `allocateObject_success` :964,
   `eqPtrval_*` :159-167, `readBytesFrom_writeBytesTo_*` :221/235,
   `writeBytesTo_*` :208-217, `byteAt_*` :1035/1043). An abstract
   memory interface (5 observers, 4 actions, 7 laws) is a repackaging of
   those lemmas plus an opaque state type; the payoff is that
   `MemState.mk`, the 14 fields, `freshBase`, `writeBytesTo` become
   unnameable in rule proofs by construction, and the `TagDefs` re-pin
   lands in one place.
5. **Recommendation (§5):** memory interface yes (after the re-pin and P4,
   spec frozen, ~3 modules); env-map interface as the cheap second piece
   (kills the R-08 class by construction); control mixin no — defer, keep
   the per-construct rules proved against `Step` as Iris/RefinedC do.

## 1. Inventory (measured)

Method (`scripts/parametric_inventory.lean`, run on the built environment
at `3ea128d`, 12 s): for each seed theorem, the constants of the proof
VALUE minus those of the TYPE are the "proof-only direct" set
(what the proof commits to beyond its statement); "transitive" closes
that set through package THEOREMS only (package definitions and all
engine/Iris/Lean constants are leaves — so reaching `Step` does not count
as reaching `CerbMem.storeM` through constructor types). Columns:
`StepDef` = the `Step` inductive/constructors/`casesOn`; `StepLem` =
theorems in the `Step.` namespace (inversions, canonical instances);
`Env` = map OPERATIONS (`fmapAddBy`/`fmapLookupBy`, `Std.TreeMap*`,
`update_env*`, `bindArgs`/`bindSaveParams`, EnvLaws) — bare `Fmap`/
`EnvStack` types are statement vocabulary and not counted; `Ghost` =
`CohG`/cursor/`*Interp`/`*Heap_*`/`stateInterp_iff`/`pointsTo*_iff`/
`bytesOwn`; `Judg` = `wps.pre`/`wpt.pre` unfolded by definition; `Engine
defs` = generated cerberus-lean/LemLib definitions/lemmas (types,
constructors and auto-generated `injEq`/`match_*` excluded); `Layout` =
the re-pin's `TagDefs` set (`sizeofCtype`, `memValueToBytes`,
`reconstructValue`, `loadM`, `storeM`, `allocateObject`, `alignofIval`,
`arrayShiftPtrval`, `isAtomicMemberAccess`). `d` = direct, `t` =
transitive count (or y/n).

Reading note on the transitive columns: every `cases` on a `Step`
hypothesis produces a `Step.casesOn` whose minor premises name
`storeM`/`loadM`/`allocateObject`, so "Layout t = 3" on a pure-control rule
(e.g. `wps_if_true`) is the inversion lemma's proof, not a layout
dependence. The DIRECT columns are the ones that answer the question.

#### Rule theorems (Rules/Wps/Wpt): 76 seeds (measured)
##### Rules

| theorem | StepDef d/t | StepLem d | Env d/t | Ghost d/t | Judg d | Engine defs, proof-only direct | Eng defs t | Layout d / t |
|---|---|---|---|---|---|---|---|---|
| `spike_wp_wand` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `triple_conseq` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `triple_frame` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `triple_seq` | 0/y | 0 | 0/8 | 0/0 | 0 | 1: fmapEmpty | 24 | - / 3 |
| `wp_annot` | 3/y | 2 | 1/3 | 0/0 | 0 | 1: instInhabitedMemState | 19 | - / 3 |
| `wp_annot_reindex` | 3/y | 1 | 1/3 | 0/0 | 0 | - | 18 | - / 3 |
| `wp_env_invariant_stable` | 1/y | 0 | 0/3 | 0/0 | 0 | - | 16 | - / 3 |
| `wp_load` | 1/y | 2 | 1/6 | 12/18 | 0 | 4: loadM, readBytesFrom … | 39 | loadM, sizeofCtype / 5 |
| `wp_ofVal` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wp_sseq` | 4/y | 3 | 2/8 | 0/0 | 0 | 3: instInhabitedMemState, pattern … | 23 | - / 3 |
| `wp_store` | 1/y | 2 | 3/15 | 15/34 | 0 | 18: MemState.allocations, MemState.bytemap … | 53 | sizeofCtype, storeM / 6 |
##### Wps

| theorem | StepDef d/t | StepLem d | Env d/t | Ghost d/t | Judg d | Engine defs, proof-only direct | Eng defs t | Layout d / t |
|---|---|---|---|---|---|---|---|---|
| `blockSpecs_intro` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wps_annot` | 3/y | 2 | 1/3 | 0/0 | 3 | - | 18 | - / 3 |
| `wps_annot_reindex` | 3/y | 1 | 1/3 | 0/0 | 3 | - | 18 | - / 3 |
| `wps_case_value` | 2/y | 1 | 0/3 | 0/0 | 3 | - | 16 | - / 3 |
| `wps_create` | 0/y | 0 | 0/13 | 12/52 | 0 | - | 46 | - / 5 |
| `wps_create_cursor_internal` | 1/y | 2 | 4/13 | 21/38 | 3 | 18: Address, MemState.allocations … | 46 | allocateObject / 5 |
| `wps_frame` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wps_if_false` | 2/y | 1 | 0/3 | 0/0 | 3 | - | 16 | - / 3 |
| `wps_if_true` | 2/y | 1 | 0/3 | 0/0 | 3 | - | 16 | - / 3 |
| `wps_load` | 1/y | 2 | 1/6 | 12/18 | 3 | 4: loadM, readBytesFrom … | 39 | loadM, sizeofCtype / 5 |
| `wps_load_at` | 1/y | 2 | 1/6 | 12/18 | 3 | 5: MemState.funptrmap, MemState.lastUsedUnionMembers … | 38 | loadM, sizeofCtype / 5 |
| `wps_load_cell_at` | 0/y | 0 | 0/6 | 5/22 | 0 | - | 39 | - / 5 |
| `wps_load_eval` | 2/y | 1 | 0/3 | 0/0 | 1 | - | 16 | - / 3 |
| `wps_memop_eval` | 2/y | 1 | 0/3 | 0/0 | 1 | - | 16 | - / 3 |
| `wps_memop_ptreq` | 2/y | 1 | 0/3 | 0/0 | 1 | 1: valueFromPexpr | 16 | - / 3 |
| `wps_ofVal` | 0/n | 0 | 0/0 | 0/0 | 3 | - | 0 | - / 0 |
| `wps_pure` | 2/y | 1 | 0/3 | 0/0 | 3 | - | 17 | - / 3 |
| `wps_run` | 0/n | 0 | 0/0 | 0/0 | 3 | - | 0 | - / 0 |
| `wps_save` | 2/y | 1 | 1/3 | 0/0 | 3 | 2: mk_sym_pat, update_env | 17 | - / 3 |
| `wps_seq` | 4/y | 3 | 2/8 | 0/0 | 3 | 2: pattern, update_env | 22 | - / 3 |
| `wps_seq_spec` | 4/y | 3 | 2/8 | 0/0 | 3 | 4: Lem_Map.instMapKeyTypeOfSetType, instSetTypeSym_1 … | 22 | - / 3 |
| `wps_seq_sym` | 3/y | 3 | 2/8 | 0/0 | 3 | 4: Lem_Map.instMapKeyTypeOfSetType, instSetTypeSym_1 … | 22 | - / 3 |
| `wps_sound` | 1/y | 2 | 1/3 | 0/0 | 3 | - | 18 | - / 3 |
| `wps_store` | 1/y | 2 | 3/15 | 15/34 | 3 | 18: MemState.allocations, MemState.bytemap … | 53 | sizeofCtype, storeM / 6 |
| `wps_store_at` | 1/y | 2 | 3/15 | 14/33 | 3 | 16: MemState.allocations, MemState.bytemap … | 52 | storeM / 6 |
| `wps_store_cell_at` | 0/y | 0 | 0/15 | 5/37 | 0 | - | 52 | - / 6 |
| `wps_store_eval` | 2/y | 1 | 0/3 | 0/0 | 1 | - | 16 | - / 3 |
| `wps_unfold` | 0/n | 0 | 0/0 | 0/0 | 1 | - | 0 | - / 0 |
| `wps_value_inv` | 0/n | 0 | 0/0 | 0/0 | 3 | - | 0 | - / 0 |
| `wps_wand` | 0/n | 0 | 0/0 | 0/0 | 3 | - | 0 | - / 0 |
| `wps_wseq` | 4/y | 3 | 1/8 | 0/0 | 3 | 1: pattern | 22 | - / 3 |
##### Wpt

| theorem | StepDef d/t | StepLem d | Env d/t | Ghost d/t | Judg d | Engine defs, proof-only direct | Eng defs t | Layout d / t |
|---|---|---|---|---|---|---|---|---|
| `blockSpecsT_intro` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `blockSpecsT_mono` | 0/n | 0 | 1/1 | 0/0 | 0 | - | 0 | - / 0 |
| `wpt_annot` | 3/y | 2 | 1/3 | 0/0 | 0 | - | 18 | - / 3 |
| `wpt_annot_reindex` | 3/y | 1 | 1/3 | 0/0 | 0 | - | 18 | - / 3 |
| `wpt_create` | 0/y | 0 | 0/13 | 12/52 | 0 | - | 46 | - / 5 |
| `wpt_create_cursor_internal` | 1/y | 2 | 4/13 | 21/38 | 0 | 18: Address, MemState.allocations … | 46 | allocateObject / 5 |
| `wpt_det_step` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wpt_if_false` | 2/y | 1 | 0/3 | 0/0 | 0 | - | 16 | - / 3 |
| `wpt_if_true` | 2/y | 1 | 0/3 | 0/0 | 0 | - | 16 | - / 3 |
| `wpt_jump_eq` | 0/n | 0 | 0/0 | 0/0 | 3 | - | 0 | - / 0 |
| `wpt_jump_frame_sseq` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 1 | - / 0 |
| `wpt_load_at` | 1/y | 2 | 1/6 | 12/18 | 0 | 5: MemState.funptrmap, MemState.lastUsedUnionMembers … | 38 | loadM, sizeofCtype / 5 |
| `wpt_load_cell_at` | 0/y | 0 | 0/6 | 5/22 | 0 | - | 39 | - / 5 |
| `wpt_load_eval` | 2/y | 1 | 0/3 | 0/0 | 0 | - | 16 | - / 3 |
| `wpt_memop_eval` | 2/y | 1 | 0/3 | 0/0 | 0 | - | 16 | - / 3 |
| `wpt_memop_ptreq` | 2/y | 1 | 0/3 | 0/0 | 0 | 1: valueFromPexpr | 16 | - / 3 |
| `wpt_mono` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wpt_mono_Ls` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wpt_mono_k` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wpt_ofVal` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wpt_pure` | 2/y | 1 | 0/3 | 0/0 | 0 | - | 17 | - / 3 |
| `wpt_run` | 0/n | 0 | 0/0 | 0/0 | 0 | - | 0 | - / 0 |
| `wpt_save` | 2/y | 1 | 0/3 | 0/0 | 0 | - | 16 | - / 3 |
| `wpt_seq` | 4/y | 3 | 2/8 | 0/0 | 0 | 2: pattern, update_env | 22 | - / 3 |
| `wpt_seq_spec` | 4/y | 3 | 2/8 | 0/0 | 0 | 4: Lem_Map.instMapKeyTypeOfSetType, instSetTypeSym_1 … | 22 | - / 3 |
| `wpt_seq_sym` | 3/y | 3 | 2/8 | 0/0 | 0 | 4: Lem_Map.instMapKeyTypeOfSetType, instSetTypeSym_1 … | 22 | - / 3 |
| `wpt_sound` | 1/y | 2 | 1/3 | 0/0 | 0 | - | 18 | - / 3 |
| `wpt_step_eq` | 0/n | 0 | 0/0 | 0/0 | 3 | - | 0 | - / 0 |
| `wpt_store_at` | 1/y | 2 | 3/15 | 14/33 | 0 | 16: MemState.allocations, MemState.bytemap … | 52 | storeM / 6 |
| `wpt_store_cell` | 0/y | 0 | 0/15 | 4/38 | 0 | 1: sizeofCtype | 52 | sizeofCtype / 6 |
| `wpt_store_cell_at` | 0/y | 0 | 0/15 | 5/37 | 0 | - | 52 | - / 6 |
| `wpt_store_eval` | 2/y | 1 | 0/3 | 0/0 | 0 | - | 16 | - / 3 |
| `wpt_val_eq` | 0/n | 0 | 0/0 | 0/0 | 3 | - | 0 | - / 0 |
| `wpt_zero_step_eq` | 0/n | 0 | 0/0 | 0/0 | 3 | - | 0 | - / 0 |
#### Aggregate over the 76 rule theorems (measured)
- Step relation unfolded by definition in the rule's OWN proof (StepDef direct > 0): 44
- Step used only through `Step.*` lemmas directly (StepLem direct > 0, StepDef direct = 0): 0
- Step reachable transitively (any): 52
- Env/Fmap representation: direct > 0: 28; transitive > 0: 53
- Ghost/cursor/CohG internals: direct > 0: 17; transitive > 0: 17
- Judgment unfolded (`wps.pre`/`wpt.pre` direct): 30
- Generated engine DEFINITIONS in the proof only (not in the statement), direct: 24; transitive (through package lemmas) > 0: 53
- Engine TYPES/constructors exposed in the proof only (judgment binders etc.), direct > 0: 54
- Layout-dependent memory functions (TagDefs re-parameterization set): named DIRECTLY in the proof only: 11; in the transitive cone (dominated by `cases` on `Step`, whose constructor premises name storeM/loadM/allocateObject): 52
- CLEAN (no direct use of any category; pure logic over other rules): 14: `spike_wp_wand`, `triple_conseq`, `triple_frame`, `wp_ofVal`, `blockSpecs_intro`, `wps_frame`, `blockSpecsT_intro`, `wpt_det_step`, `wpt_jump_frame_sseq`, `wpt_mono`, `wpt_mono_Ls`, `wpt_mono_k`, `wpt_ofVal`, `wpt_run`
- WORST (engine-direct + ghost-direct + StepDef-direct): `wpt_create_cursor_internal` (18+21+1), `wps_create_cursor_internal` (18+21+1), `wps_store` (18+15+1), `wp_store` (18+15+1), `wps_store_at` (16+14+1), `wpt_store_at` (16+14+1), `wps_load_at` (5+12+1), `wpt_load_at` (5+12+1)
#### Soundness / Round / Adequacy / TotalAdequacy exports (22, measured)

| theorem | StepDef d/t | StepLem d | Env d/t | Ghost d/t | Judg d | Engine defs, proof-only direct | Eng defs t | Layout d / t |
|---|---|---|---|---|---|---|---|---|
| `engine_complete` | 4/y | 6 | 0/7 | 0/0 | 0 | 17: CerbLocation.isLibraryLocation, CerbLocation.stringFromLocation … | 115 | allocateObject, loadM, storeM / 3 |
| `engine_step_matchU` | 25/y | 16 | 3/8 | 0/0 | 0 | 30: CerbLocation.instInhabitedLoc, CerbLocation.isLibraryLocation … | 207 | allocateObject, loadM, storeM / 5 |
| `Decomp.step_factor` | 1/y | 3 | 2/3 | 0/0 | 0 | 4: get_ctx_lemFuel, is_irreducible … | 20 | - / 3 |
| `stepDischarge_run` | 0/n | 0 | 3/5 | 0/0 | 0 | 84: CerbLocation.isLibraryLocation, CerbLocation.stringFromLocation … | 183 | - / 2 |
| `Frag.step` | 25/y | 15 | 3/3 | 0/0 | 0 | 18: CerbLocation.instInhabitedLoc, CerbLocation.isLibraryLocation … | 18 | allocateObject, loadM, storeM / 3 |
| `Frag.decomp` | 0/n | 0 | 0/0 | 0/0 | 0 | 10: CerbLocation.isLibraryLocation, expr … | 12 | - / 0 |
| `cerberusRound_classify` | 1/y | 0 | 0/8 | 0/0 | 0 | - | 207 | - / 5 |
| `step_iff_cerberusRound` | 0/y | 1 | 0/8 | 0/0 | 0 | - | 207 | - / 5 |
| `spike_step_adequacy` | 0/n | 0 | 1/5 | 8/25 | 0 | - | 16 | - / 1 |
| `spike_step_adequacy_alloc` | 0/n | 0 | 1/5 | 6/42 | 0 | - | 16 | - / 1 |
| `launchResources` | 0/n | 0 | 2/5 | 10/42 | 0 | 2: MemState.lastAddress, MemState.nextAllocId | 16 | - / 1 |
| `engine_adequacyU` | 1/y | 0 | 0/17 | 0/25 | 0 | - | 221 | - / 6 |
| `engine_adequacyJ` | 0/y | 0 | 0/17 | 0/25 | 0 | - | 221 | - / 6 |
| `spike_engine_adequacy` | 0/y | 0 | 0/17 | 0/25 | 0 | 1: fmapEmpty | 221 | - / 6 |
| `semantic_triple_sound` | 0/y | 0 | 2/17 | 0/35 | 0 | 1: lemDefaultFuel | 221 | - / 6 |
| `semantic_frame` | 0/y | 0 | 1/17 | 0/35 | 0 | - | 221 | - / 6 |
| `driveJ_step` | 0/y | 0 | 0/8 | 0/0 | 0 | - | 207 | - / 5 |
| `wpt_engine_boundU` | 0/y | 0 | 1/17 | 9/26 | 0 | - | 221 | - / 6 |
| `wpt_engine_boundJ` | 0/y | 0 | 0/17 | 0/26 | 0 | - | 221 | - / 6 |
| `wpt_engine_boundU_alloc` | 0/y | 0 | 1/17 | 5/42 | 0 | - | 221 | - / 6 |
| `wpt_strongly_normalizing` | 0/y | 0 | 1/8 | 8/25 | 0 | - | 34 | - / 4 |
| `Frag.pot_step_bound` | 25/y | 15 | 3/3 | 0/0 | 0 | 18: CerbLocation.instInhabitedLoc, CerbLocation.isLibraryLocation … | 19 | allocateObject, loadM, storeM / 3 |
#### Layout-dependent package DEFINITIONS (measured)

`TOTAL layout-dependent definitions: 35` (verbatim script line; the per-definition list is the last section of the script output — omitted here for length).

Derived from the layout list: the 35 lines collapse to 18 distinct
user-level definitions once `rec`/`casesOn`/`recOn`/`mk`/`below`
companions are folded — 3 coupling structures (`CellCoh`, `MetaCoh`,
`StorableAt`), 3 `Step` constructors (`store`/`load`/`create`), 9 Heap/
Soundness/Step functions (`advanceCursor`, `cellOwn`, `cellsDisjoint`,
`decIndep`, `decodeCell`, `dischargeStep`, `evalArrayShift`,
`metaDisjoint`, `pointsToView`), 3 example constants in Rules.lean
(`fiveBytes`/`sixBytes`/`sevenBytes` — P5's "example constants out of
Rules" item). These 18 are exactly what the re-pin re-parameterizes.

### 1.1 What six representative proofs actually need from `Step`

Read, not inferred from the table.

- **`wp_store` (Rules.lean:176).** Needs (a) EXISTENCE of the store step
  given the memory action succeeds — `Step.store_canonical hmv hrun`
  (Step.lean:1236), fed by `storeM_success` (Heap.lean:309: on a
  `CellCoh` cell with a `StorableAt` value, `storeM` returns
  `(FP W addr (sizeofCtype ty), writeBytesTo σ addr bytes)`); (b)
  DETERMINISM/INVERSION — `hstep.store_inv` (Step.lean:1366): every step
  from the store redex is THE store step, successor pinned to
  `Expr [] (Eannot [DA_pos [] fp] (mk_value_e Vunit))`, env verbatim, state
  `writeBytesTo …`; (c) the ghost side: `stateInterp_iff`,
  `pointsToCell_iff`, `bytesOwn_get/read/update`, `CohG.storeRange`
  (Heap.lean:1923). The `primStep = Step` identification is by `rfl`
  (`⟨Step.store_canonical …, rfl, rfl⟩` — Lang.lean:43's `primStep` is
  unfolded definitionally, not through `primStep_eq`). The engine leakage
  (18 engine definitions, all 14 `MemState` projections + `MemState.mk` +
  `writeBytesTo` + `readBytesFrom` + `sizeofCtype`) enters through the
  destructuring of `hout`/`hmem'` and `CohG.storeRange`'s statement, not
  through anything the RULE needs: the rule needs exactly one two-sided
  law, "store-redex steps iff `storeM` succeeds, to this successor".
- **`wp_load` (Rules.lean:284) / `wps_load_at` (Wps.lean:1744).** Same
  shape with `loadM_success`/`loadM_at`: existence via
  `Step.load_canonical`, uniqueness via `Step.load_inv`, state unchanged,
  value `valueFromMemValue (decodeCell …)`/`mv`. `wps_load_at` additionally
  names `MemState.funptrmap`/`lastUsedUnionMembers` (the decode side
  tables) — the `reconstructValue lum fpm` premise `hdec` is the visible
  face of the ambient-table problem the re-pin fixes.
- **`wps_create_cursor_internal` (Wps.lean:2222) → `wps_create`
  (Wps.lean:2395).** The internal rule is the worst offender (80
  non-package direct constants): existence via `Step.create_canonical` +
  `allocateObject_success` (Heap.lean:964), which pins `allocateObject`'s
  result to `cellPtr nid (freshBase lastAddress align size)` and the new
  state to an explicit `MemState.mk` with all fields; uniqueness via
  `Step.create_inv`; ghost via `CohG.create`, `byteHeap_alloc_big`,
  `metaHeap_alloc`, `cursorHeap_update`. The PUBLIC `wps_create` has
  StepDef 0 / engine 0 / ghost 12 — it is `allocCap`'s unfolding plus
  cursor arithmetic (`advanceCursor_some_inv`, `freshBase_pos/_lt_two64`)
  around the internal rule. So `allocCap` (Heap.lean:1656) hides the
  cursor from CLIENTS; the rule proof is still cursor arithmetic — the
  existing partial instance of the pattern is one level below where the
  interface would sit.
- **`wps_seq` (Wps.lean:579).** Needs the FACTOR law of the Esseq frame,
  `Step.sseq_inv` (Step.lean:1500): a step of `Esseq pat e1 e2` is (i) a
  framed step of `e1` under `jumpRedex? e1 = none`, (ii) a beta at a value
  `e1` (pure/annot; spec/sym patterns excluded by `specPat_ne_base`/
  `symPat_ne_base`), or (iii) a jump; plus LIFTING (`Step.sseq_ctx`), the
  betas as constructors (`Step.sseq_pure`/`sseq_annot`), `Step.val_elim`
  (values are stuck), `Step.env_cons` (env stays cons-shaped), and
  `jumpRedex?_sseq` (redex search commutes with the frame). Those are
  precisely `fill`, `step_by_val`, `fill_val`, `val_stuck` of Iris's
  `EctxLanguage` (EctxLanguage.lean:40/150) PLUS the jump exception.
  `wps_seq_spec`/`wps_seq_sym` add the binder betas and reach into the env
  representation (`update_env_aux`, `Lem_Map.instMapKeyTypeOfSetType` —
  Env d = 2) to compute the bound frame.
- **`wps_if_true` (Wps.lean:865).** Existence `Step.if_true hg`
  (constructor, direct) + uniqueness `hs.if_inv` (the only step from `Eif`
  is the guard-determined branch): a "local deterministic tau with a pure
  premise" — the shape of every local rule (`save`, `case_value`,
  `pure_eval`, `*_eval`). Nothing about memory or env representation
  (Env d = 0), yet StepDef d = 2 (constructor + `casesOn`).
- **`wps_run` (Wps.lean:226) and the frame lemmas.** `wps_run` is
  definitional on the judgment's jump clause (Judg 3, Step 0).
  `triple_frame` (Rules.lean:846), `wps_frame` (Wps.lean:289),
  `blockSpecs_intro`, `wpt_mono*` are CLEAN — pure BI over the judgment.
  `semantic_frame` (Adequacy.lean:1255) is clean at the direct level but
  reaches 221 engine definitions transitively through
  `semantic_triple_sound` → `spike_engine_adequacy` → the drive loop — as
  it must: it is the engine-facing statement.

Reading of the exports table: `Frag.step`/`engine_step_matchU`/
`Frag.pot_step_bound` are the certification (StepDef d = 25 — all 24
constructors + `casesOn`); `stepDischarge_run` is the engine-unfolding
boundary (84 engine definitions direct). Those are SUPPOSED to unfold
both sides; they are the instance proof in any parametric design.

## 2. The interface draft (signatures in the note, not in the tree)

### 2.1 CONTROL — an ectx mixin with the jump exception

The engine has its own context grammar (`context`, Core_run_aux.lean:
~110-120: `CTX | Cunseq | Cwseq | Csseq | Cannot | Cbound`, 6 ctors;
`apply_ctx`/`get_ctx`), of which the package's `Decomp` (Soundness.lean:
570) covers `Csseq` (at 3 pattern shapes), `Cwseq`, `Cannot` (6 ctors),
and `Redex` (Soundness.lean:504) has 18 ctors for `Frag`'s 18 constructs.

```lean
/-- What the statement judgments use of the control structure. `E` is the
    expression type, `R` the runtime env, `S` the state, `V` values,
    `Lbl` the label-context, `M` the machine context. -/
class CoreControl (E R S V Lbl M : Type) where
  step   : M → E × R × S → E × R × S → Prop
  toVal  : E → Option V
  ofVal  : V → E
  fillSeq  : pattern → E → E → E              -- Esseq pat □ e2 (and Ewseq, Eannot ds □)
  jumpRedex? : E → Option (sym × List pexpr)
  labels : M → Lbl
  bind   : List (sym × core_base_type) → List value → R → R
  /- C1 values stuck            -/ val_stuck   : step M (ofVal v, ρ, σ) c' → False
  /- C2 partial bijection       -/ toVal_ofVal : toVal (ofVal v) = some v ; ofVal_of_toVal
  /- C3 frame lifting           -/ fill_step   : jumpRedex? e1 = none → step M (e1,ρ,σ) (e1',ρ',σ') →
                                                 step M (fillSeq p e1 e2, ρ, σ) (fillSeq p e1' e2, ρ', σ')
  /- C4 factor (three-way)      -/ fill_inv    : step M (fillSeq p e1 e2, ρ, σ) c' →
                                                 (framed …) ∨ (toVal e1 = some w ∧ beta …) ∨ (jumpRedex? e1 = some …)
  /- C5 betas, one per binder   -/ beta_wild / beta_annot / beta_spec / beta_sym : step … (e2, bind …, σ)
  /- C6 redex search vs frame   -/ jump_fill   : toVal e1 = none → jumpRedex? (fillSeq p e1 e2) = jumpRedex? e1
  /- C7 jump fires              -/ jump_step   : jumpRedex? e = some (l,pes) → lookup (labels M) l = some (ps,cont) →
                                                 eval ρ pes = some vs → step M (e, ρ, σ) (cont, bind ps vs ρ, σ)
  /- C8 jump inversion          -/ jump_inv    : jumpRedex? e = some _ → step M (e,ρ,σ) c' → c' = (that jump)
  /- C9 env shape preserved     -/ env_cons    : step M (e, ev0::evs, σ) (e', ρ', σ') → ∃ ev0' evs', ρ' = ev0'::evs'
```

Instance obligations from `Step` — all ALREADY lemmas: C1 `Step.val_elim`
(Step.lean:1340); C2 `toVal_ofVal`/`ofVal_of_toVal` (:244/:247); C3 the
constructor `Step.sseq_ctx` (and `wseq_ctx`, `annot_ctx`); C4
`Step.sseq_inv` (:1500), `Step.wseq_inv` (:1549), `Step.annot_inv`
(:1575); C5 the seven beta constructors; C6 `jumpRedex?_sseq` (:502),
`jumpRedex?_wseq` (:515), `jumpRedex?_annot*` (:519-529); C7 `Step.run`;
C8 `Step.jump_inv` (:1441); C9 `Step.env_cons` (:1330). New lemmas: 0.
Repeated per frame (Esseq, Ewseq, Eannot — the annotation frame has the
extra `annotRooted` guard and the merge tau): ×3 for C3/C4/C6.

Width check. Generic laws: 9 (×3 frames for three of them → ~15 law
instances). What they cover: `wp_sseq` (Rules.lean:702-840, 138 lines),
`wps_seq` (579-730, 151), `wpt_seq` (928-1077, 149), the three
`*_annot`/`*_annot_reindex` triples (wp 441-686, wps 306-579, wpt
602-901), `wps_wseq`, the `*_sound` collapses — i.e. the ~10 STRUCTURAL
rules, currently proved three times each (base WP / wps / wpt), would be
proved once over the class. What they do NOT cover: the 8 local taus
(`if_true/false`, `save`, `case_value`, `pure_eval`, `load_eval`,
`store_eval`, `memop_eval`) and the 4 memory actions — 12 constructs whose
rules need per-construct "fires + is the only step" pairs. Adding those to
the interface gives 9 + 12×2 = 33 laws for 24 constructors (~1.4 laws per
constructor): the interface restates `Step` by its inversion lemmas — the
mirror of the mirror. Iris-mixin granularity means STOPPING at C1-C9 and
proving the 12 local/action rules against the instance (HeapLang's
`inv_base_step`, RefinedC's `inv_expr_step` — the donor does exactly
this).

The save/run label protocol FITS the mixin only as the C6-C8 exception:
`Erun` is a redex that REPLACES the whole expression, so `fill_inv` has a
third disjunct that no ectx language has, `Language.Context` is
unavailable (Lang.lean header), and `wps`'s jump clause (Wps.lean:131) is
the judgment-level image of C7. Nothing about the label-context WP itself
needs the mixin — `wps_run`, `blockSpecs_intro`, `wps_sound`'s jump case
are definitional/Löb over the judgment — but `wps_sound` (Wps.lean:2510)
consumes C7/C8 at the actual jump step. Fit: adequate, bespoke: this is
not an instance of `Iris.ProgramLogic.EctxLanguage` (EctxLanguage.lean:
150 — `step_by_val`/`base_ctx_step_val` are falsified by the jump), so
none of iris-lean's `EctxLifting` is reusable; the class would be
package-local. That is the strain: the control mixin buys de-duplication
of ~1,100 lines of structural proofs (derived: the six ranges above) at
the price of a bespoke 9-law class with no upstream theory behind it.

### 2.2 MEMORY — an abstract memory model for the fragment's actions

```lean
/-- The memory interface: an opaque state with five observers, four
    actions as partial functions (the shape of `applyMemM (storeM …)`,
    Step.lean:778), the layout functions, all under an explicit tag
    environment `Δ`. -/
class MemModel (Mem : Type) (Δ : TagDefs) where
  -- observers (everything `CohG`, Heap.lean:1386, reads today)
  byteAt    : Mem → Int → AbsByte                     -- Heap.lean:1002
  allocMeta : Mem → Int → Option Allocation           -- σ.allocations.get?
  isDead    : Mem → Int → Bool                        -- σ.deadAllocations.contains
  nextId    : Mem → Int                               -- σ.nextAllocId
  lastAddr  : Mem → Int                               -- σ.lastAddress
  -- layout (the re-pin's TagDefs set)
  sizeof : ctype → Nat ; encode : MemValue → List AbsByte ; decode : Int → ctype → List AbsByte → MemValue
  -- actions
  store  : Loc → ctype → Bool → PointerValue → MemValue → Mem → Option (Footprint × Mem)
  load   : Loc → ctype → PointerValue → Mem → Option ((Footprint × MemValue) × Mem)
  create : prefix0 → IntegerValue → ctype → Mem → Option (PointerValue × Mem)
  ptrEq  : PointerValue → PointerValue → Mem → Option (Bool × Mem)
  /- M1 store on an owned cell -/ store_spec : CellCoh σ id ⟨a,ty,bs⟩ → StorableAt ty mv →
        store loc ty lk (cellPtr id a) mv σ = some (FP W a (sizeof ty), σ') ∧
        (∀ k, byteAt σ' k = if a ≤ k < a + |bs| then (encode mv)[k-a] else byteAt σ k) ∧
        allocMeta σ' = allocMeta σ ∧ isDead σ' = isDead σ ∧ nextId σ' = nextId σ ∧ lastAddr σ' = lastAddr σ
  /- M2 load on an owned cell  -/ load_spec  : CellCoh σ id ⟨a,ty,bs⟩ → ¬trap → load loc ty (cellPtr id a) σ = some ((FP R a (sizeof ty), decode a ty bs), σ)
  /- M2' typed subrange load   -/ load_at_spec (the `loadM_at` shape, Heap.lean:818) ; store_at_spec (:864)
  /- M3 create                 -/ create_spec : 0 < sizeof ty → freshBase (lastAddr σ) al (sizeof ty) ≠ 0 →
        create pref (IV _ al) ty σ = some (cellPtr (nextId σ) (freshBase …), σ') ∧ observers of σ' pinned
  /- M4 pointer equality       -/ ptrEq_cell_null / null_null / null_cell (the three provenance-free cases)
  /- M5 locality               -/ (subsumed by M1's byteAt equation)
  /- M6 interior write         -/ store_at_spec's byte equation at offset (the `spliceBytes` law, Heap.lean:503)
```

Instance obligations from `CerbMem.MemState` — status: M1 =
`storeM_success` (Heap.lean:309) + `writeBytesTo_allocations/
deadAllocations/…` (:208-217) + `writeBytesTo_lastAddress/nextAllocId`
(:1049/1053) + `byteAt_writeBytesTo_in/out` (:1035/1043): ALL EXIST; M2 =
`loadM_success` (:336): exists; M2' = `loadM_at`/`storeM_at`
(:818/:864): exist; M3 = `allocateObject_success` (:964) + the
`freshBase_*` bounds (:916-950): exist; M4 = `eqPtrval_*` (:159-167):
exist; M6 = `readBytesFrom_write_interior` (:503) +
`spliceBytes_slice_*` (:552-579): exist. New lemmas: the observer
re-statements are one-line `rfl`/`simp` wrappers (est. 8-10 small
lemmas). What is genuinely NEW is the opaque `Mem`: today
`abbrev Mem := CerbMem.MemState` (Step.lean:157) and `CohG` (Heap.lean:
1386) reads `σ.lastAddress`, `σ.nextAllocId`, `σ.deadAllocations.contains`,
`σ.allocations.get?`, `byteAt σ` — exactly the five observers, so `CohG`
restates verbatim over the class. `MetaCoh`/`CellCoh`/`StorableAt` (the
3 coupling structures) restate over `allocMeta`/`byteAt`/`sizeof`/
`encode`/`decode`.

Width check: 5 observers + 4 actions + 3 layout functions + 7 laws (M1,
M2, M2'×2, M3, M4×3 counted as one family, M6) for 4 memory constructs
(store/load/create/ptreq) and 17 memory-touching rules. This is
OPERATION-level parametricity — the interface is the actions' contracts,
not a mirror of `MemState`'s 14 fields. The width-creep risk is the
observer set: if a future rule needs `funptrmap`/`lastUsedUnionMembers`
(the decode side tables — `wps_load_at` names them today, via the
`reconstructValue lum fpm` premise) the observers grow toward the record.
The re-pin's `TagDefs` argument removes that particular pressure (§2.4).

### 2.3 ENV — the third, small piece the inventory argues for

28 rules touch the env-map operations directly, all through
`update_env`/`update_env_aux`/`bindArgs`/`bindSaveParams` to compute the
bound frame after a beta or jump. `EnvLaws.lean` already IS this
interface in lemma form: `SymFrame` (:261), `envAdd_lookup` (:280),
`update_env_sym/spec` (:339/:330), `lookup_env_head` (:350). A
`class EnvModel (R : Type)` with `lookup : R → sym → Option value`,
`add : sym → value → R → R`, `bindPat`, and the laws `lookup_add_same`,
`lookup_add_other`, `bind_wild_id`, `bind_spec`, `bind_sym` (5 laws,
all existing lemmas) makes `Fmap.mk`/`Std.TreeMap` unnameable in rules —
the R-08 class (LoopExhibit pinning an exact `Fmap` shape) becomes
impossible to write, not merely audited away. Instance obligations:
existing (`treeMap_get?_insert_empty` :50, `envAdd_lookup` :280).

### 2.4 The tag environment (`TagDefs`) — placement

The re-pin makes `Δ : TagDefs` an explicit leading argument of
`sizeofCtype`, `memValueToBytes`, `reconstructValue`, `loadM`, `storeM`,
`allocateObject`, `alignofIval`, `arrayShiftPtrval`,
`isAtomicMemberAccess`. Measured: 18 distinct package definitions (above)
and 11 rules (direct) name members of that set today; `Step.store`'s
`hmv` premise already takes `M.tagDefs` (Step.lean:833), so the pattern
"rules generic in `M` supply `M.tagDefs`" exists for one function.

Placement in the draft: `Δ` is a PARAMETER OF THE INSTANCE, i.e. of the
`MemModel` class (`class MemModel (Mem) (Δ : TagDefs)`) with every action
and layout function stated relative to it, and `MachineCtx.tagDefs`
(Step.lean:326) is the value the rules pass. Natural, for two reasons:
(i) it is exactly Caesium's global environment position in RefinedC
(program-wide constant of the language instance); (ii) the state
interpretation (`SpikeState`, Heap.lean:1408) has no room for a
per-configuration `Δ` — Iris's `StateInterp` is fixed per instance — so
`Δ` MUST be a section-level constant of the Heap/Rules development, which
is what "parameter of the instance" means operationally. The strain:
heap predicates whose footprint depends on layout (`pointsToView`,
`cellOwn`, `CellCoh`, `MetaCoh`, `StorableAt`, `decIndep`, `decodeCell`,
`advanceCursor`) gain a `Δ` index — a statement-surface change to the
public rules (an extra explicit or instance argument). That change is
FORCED BY THE RE-PIN regardless of this design, which is why the re-pin
must land first (§4): the parametric refactor then adds NO further
surface change. `fmapEmpty` is never baked in: `spikeCtx.tagDefs =
fmapEmpty` (Step.lean:1879) stays a client-profile equation.

## 3. The parametricity claim, precisely

What "theorems for free" buys here. A rule proved in a module that
imports `MemModel`/`EnvModel` (and, if adopted, `CoreControl`) but not
`Step.lean`/`Heap.lean`/the generated modules is a theorem
`∀ inst, laws inst → rule inst`. By construction its proof term cannot
contain `CerbMem.MemState.mk`, any of the 14 field projections,
`writeBytesTo`, `freshBase`, `Fmap.mk`, `Std.TreeMap.*`, or a `Step`
constructor — the constants are not in scope and `Mem`/`R` are opaque
types. Classes of mistake made impossible: (a) R-08 — pinning an
accidental representation (an exact `Fmap` shape, an address computed by
the allocator's arithmetic) in a rule or invariant; (b) the "cursor in the
statement" class of R-01 (a rule whose precondition names allocator
state); (c) silent dependence on a memory-record field the rule has no
business reading (`wps_load_at`'s `funptrmap`); (d) the re-pin class —
an ambient-vs-explicit `TagDefs` change becomes a one-place instance
edit instead of 18 definitions + 11 rules. Also a free ADEQUACY-SIDE
check: a law that Cerberus does not satisfy is UNPROVABLE at the instance
(the instance is proven from `Step`/`CerbMem`, never postulated), so an
over-strong interface fails closed at instance time.

What it does NOT buy. (1) A law that is TRUE of Cerberus but not what the
prose claims is still a bug — the trust moves from "did the rule proof
peek at the semantics?" to "is the law set the semantics the docs
describe?" — the F-09 idiom-faithfulness caveat, unchanged in kind,
now concentrated on ~20 law statements instead of ~76 proofs (a
concentration, which is the gain; not an elimination). (2) Coverage:
laws exist for the constructs in `Frag`; a construct without a law is
unprovable, not unsound — fail-open for coverage exactly as today
(capability manifest still needed). (3) It does not make the interface a
second semantics AS LONG AS every instance is a theorem: the danger
pattern is an `axiom`/`sorry`/`opaque` instance or a law "for
convenience" not derivable from `Step` — the existing banned-methods grep
and `Audit.lean` cone sweep catch the first; the second is caught by the
requirement that the instance module import `Step`/`CerbMem` and prove,
never declare. (4) The engine-facing statements (`SemTriple`,
`driveJ`, `CerberusRound`, the production equations) are and must remain
CONCRETE — parametricity is for the rules, the adequacy spine is the
instance's; nothing in the trust architecture ([USER 2026-08-29]: the
engine is the only trusted semantics) changes. (5) It does not by itself
remove a single line of `Soundness.lean` (143 theorems, 4,945 lines):
the certification IS the instance proof.

Where the trust goes, in one line: from 76 rule proofs that may or may
not unfold the semantics, to ~20 laws that are proved of it — the same
axiom cone (trio), a smaller reading surface.

## 4. Relation to the plan

**P5 (layering + `API.lean` + import gate + readiness smoke test).** The
interface modules ARE the API: `API.lean`'s export list becomes "the
classes and the rules stated over them"; the import gate (P5 item 4:
"clients may not depend directly on internal attachment modules") becomes
a BUILD-STRUCTURAL fact — a rule module that does not import `Heap.lean`
cannot use `CohG` — instead of a script, which is the speedbump doctrine
([USER 2026-09-02]) realized by construction rather than by checker; the
readiness smoke test (P5 item 5, a two-field-object predicate deriving its
rules "solely from the raw API") is precisely a client of `MemModel`.
P5's "move `intTy`/5/6/7 out of Rules/Wps" is the 3 layout-dependent
example constants above. So P5 is ABSORBED, not replaced: same
definition-of-done, achieved by module structure. Only P5 item 1
(`StmtProbe` out of the import graph) is independent — and already done
at P3.5.

**P4 (raw-API closure).** P4.2 frame transformations (`blockSpecs_frame`,
`wps_frame_labels`, `wpt_frame_labels`) are pure logic over the judgments
(the CLEAN category) — orthogonal, do first. P4.1 (three allocation
facts: bytes / persistent metadata / liveness) DECIDES the observer set of
`MemModel` (`allocMeta` persistent view, `byteAt`) — it must precede the
interface freeze or the interface is re-cut. P4.3 (R-08 `IsXFrame` →
`SymFrame`; `SemTriple` over `MachineCtx`) is the manual version of what
`EnvModel` gives by construction; doing P4.3 first is still right (spec
work on the concrete tree), the interface then makes regression
impossible. P4 "Soundness.lean reshaped by frame transformations": not
touched by this design — Soundness stays the instance proof.

**Sequencing (respecting [USER 2026-09-02]):** re-pin (`TagDefs`
threading, in flight) → P4 spec additions → FREEZE (`signature_snapshot`
pre) → parametric refactor, three internals-only slices: (S1) `MemModel`
+ instance + the 17 memory rules re-proved over it; (S2) `EnvModel` +
instance + the 28 env-touching rules; (S3, optional, deferred) the
control mixin → later, separately: RefinedC-shaped work (type records,
Caesium-shaped interfaces) — NOT in this arc.

**Cost (ESTIMATES, units: modules touched / theorems restated / new
lemmas).** S1 memory: 4 modules (new `Interfaces/Mem.lean`, Heap, Rules,
Wps+Wpt) / 17 rule theorems re-proved (the `Ghost d > 0` set) + 3
coupling structures restated / ~10 wrapper lemmas; Adequacy's
`launchResources`/`LaunchCoh` restate over observers (2 theorems). S2
env: 2 modules (new `Interfaces/Env.lean`, EnvLaws absorbed) / 28 rule
proofs touched, mostly mechanical (`update_env_*` → `bind_*` laws) / ~5
lemmas. S3 control (if ever): 3 modules / ~10 structural rules collapsed
from 3 copies to 1 (≈ −1,100 lines, derived) / ~15 law instances, 0 new
lemmas, but a bespoke class with no iris-lean theory. Soundness.lean: 0
in all slices. Public statements changed: 0 by design (§6).

## 5. Recommendation

Adopt the MEMORY interface (S1) and the ENV interface (S2) as one
internals-only arc after the re-pin and P4, spec frozen; do NOT adopt the
control mixin now. Trade-offs named: S1 costs a re-proof of the 17
memory rules and an opaque-state discipline for `CohG`, and buys the
by-construction exclusion of representation pins in every future rule
plus a one-place `TagDefs`; S2 is cheap and closes R-08 structurally;
the control mixin buys ~1,100 lines of de-duplication but requires a
bespoke ectx-with-jump class that iris-lean's `EctxLifting` cannot
serve, and a construct-covering version would be a mirror of the mirror
(33 laws / 24 constructors) — the donor itself proves memory rules by
inversion, so no design debt is incurred by leaving the local rules
proved against `Step`.

Top 3 risks. (R1) Observer creep: the memory interface grows toward
`MemState`'s record (decode side tables, allocation prefixes) and
becomes a second presentation of the memory model — mitigation: the
observer set is fixed at P4.1's three facts, and any new observer needs
a rule that provably needs it. (R2) Typeclass friction in iris-lean
(three GenHeaps sharing a key type already need named wrappers,
Heap.lean:1336-1366; Iris's ` || ` notation clash surfaced even in the
measurement script) inflates S1 into a grind with no capability gain —
mitigation: time-box S1 at one slice, stop-and-report at the tripwire.
(R3) Spec drift under the refactor: a "small statement tidy" while
re-proving breaks the frozen-spec invariant — mitigation: §6's identical
pre/post snapshot is the acceptance test, and public rules stay
instance-level wrappers.

## 6. One change at a time — the single change and its invariance check

The single change: rule PROOFS are re-established over interface classes
whose only instances are theorems about `Step`/`CerbMem.MemState`; rule
STATEMENTS do not change. Mechanism: generic rules
`MemModel.wps_store [MemModel Mem Δ] …` live in the interface modules;
the public `CerberusHeapLang.wps_store` (Wps.lean:1538) becomes
`:= MemModel.wps_store (inst := cerberusMem)` with its CURRENT statement,
so `scripts/signature_snapshot.lean` (kind + pretty-printed type of every
non-internal constant) prints identically before and after — the
committed pre snapshot is taken after P4 closes, the post snapshot at
the arc close, and `diff` is the acceptance test. Public statements the
draft would force to change: NONE, on this design — the only surface
change in the neighbourhood is the `Δ` index forced by the re-pin, which
lands BEFORE the freeze and is not attributable to the refactor. Audit
export list (`Audit.lean:83-127`): unchanged names, unchanged cones (the
instance is trio-only). A public statement that DOES change during the
arc is a strike against the design and stops the slice.
