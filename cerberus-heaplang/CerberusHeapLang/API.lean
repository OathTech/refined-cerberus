/-
CerberusHeapLang.API — THE PUBLIC SURFACE of the logic, as one import.

A client of the logic — an exhibit today, a type interpretation
tomorrow — imports THIS module and nothing below it:

    import CerberusHeapLang.API

and works inside `namespace CerberusHeapLang` (or `open`s it): every
public name below already lives in that namespace, so no `export`
re-declarations are needed. `Examples/ReadinessSmoke.lean` is the
worked client built this way.

WHAT THIS MODULE IS, HONESTLY. Lean 4 imports are transitive and have
no export control: importing this module makes every constant of
every module below it visible, internals included. The public/
internal line is therefore DOCUMENTED here (the table), not enforced
by the language. It is measured, not gated: the client-module section
of `scripts/parametric_inventory.lean` (an on-demand instrument)
counts a module's direct references to the ghost maps / `CohG` /
cursor, the `Step` inductive and its lemmas, the judgment unfoldings
and the plan model — zero is the expected reading for every client.
A client that needs an INTERNAL name is a finding about this surface:
the remedy is a new PUBLIC lemma (as `cellOwn_readout` was added when
three clients opened the state interpretation), never an exposure of
the internal.

THE IMPORT DIRECTION this module sits in (semantics → heap → rules →
adequacy → clients) is checked by a grep in `scripts/test_unit.sh`:
no semantics/heap/rule/adequacy module — this one included — imports
an `*Exhibit`, `Examples.*` or `Prod*` module.

THE ONE DOCUMENTED EXCEPTION to the line (2026-09-02 audit, M-2):
`CohG`, `metaInterp` and `byteInterp` — internal — appear in the
PREMISES of public statements: `project_triple`'s post,
`project_triple_pure`'s and `project_triple_pure_alloc`'s `hpost`,
`cellOwn_readout` and the `*_consequence` lemmas. The rule: a client
discharges these only through the public `*_consequence` lemmas
(`pure_`/`sep_`/`or_`/`exists_consequence`, `cellOwn_consequence`,
`pointsToCell_consequence`, `cellsOwn_consequence`,
`cells_consequence`), never by opening `CohG` or the interpretations.
The pure memory view those lemmas deliver — `CellCoh`, `Coh`/`Sat` —
is PUBLIC: it is the vocabulary of the boring post.

PROVISIONAL ([USER 2026-09-02], DECISIONS.md; Adequacy.lean header):
every adequacy export below that is stated over `driveU` rather than
the shipped driver — `MemTripleU`, `MemTripleU_alloc`, `SemTripleU`,
`project_triple`, `project_triple_pure`, `project_triple_alloc`,
`project_triple_pure_alloc`, `semantic_triple_soundU`,
`semantic_frameU`, `engine_adequacyU`, `engine_adequacyU_alloc`,
`wpt_engine_boundU`, `wpt_engine_boundU_alloc`, `SemTripleU_iff_Mem`,
`MemTripleU_alloc_of_MemTripleU` — is PROVISIONAL, in
exactly this sense: a sound fact about `driveU`, this package's loop
around the engine's `step_ctx`; not yet the root-of-trust statement,
which is over the shipped driver and awaits the cerberus-lean
fuel-exhaustion outcome
(docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md,
repository root); restated with no other change when it lands. The
root-of-trust exports are the total-lane production statements
(`exhibitA_prod`, `*_certified_production`, `prod_run_eqJ`), which
live in the production layer this module does not import.

## The surface (PUBLIC — import and use freely)

| Family | Names (module) |
|---|---|
| Program vocabulary | `CoreExpr`, `EnvStack`, `SpikeVal` (`.pure`/`.annot`, `mergeInto`), `ofVal`, `MachineCtx` (`.tagDefs`, `.extern`, `.labels`, `.SeqWF`), `spikeCtx`, `spikeEnv`, `symPat`, `storeOpRedex` (Step); `storeExpr`, `loadExpr`, `sseqExpr`, `addrOf`, `loadedVal` (Rules); `createExpr` (Rules); `Frag` — fragment membership, the adequacy premise (Soundness) |
| Pointer/location assertions | `cellPtr`, `SpikeCell`, `pointsToCell` (`pv ↦c[tds]{dq} ty ; bs`), `pointsToView` (typed sub-range view), `cellOwn` (whole-allocation bundle at a ghost id), `allocMeta` (persistent allocation knowledge), `locInBounds`, `allocBudget` (the ∗-splittable allocation capacity, K2.5) with its cost function `allocCost` and the plan-shaped reading `planCost`/`AllocReq` (Heap); the K1 bundles `regionOwn`/`regionView` (an untyped live dynamic region / its sub-range view), the K5 TYPED REGION VIEW `typedRegionView` (a region sub-range read at a type — what the region access rules are stated over), `readonlyCell` (the read-only points-to), `deadObj`/`deadRegion` (persistent knowledge of a kill) (Heap) |
| Assertion laws | `pointsToCell_cellOwn_iff`, `cellOwn_view`, `pointsToView_split`, `pointsToView_join`, `pointsToView_fractional`, `pointsToView_agree`, `pointsToView_persist`, `pointsToView_locInBounds`, `cellOwn_fractional`, `pointsToCell_fractional`, `pointsToCell_agree`, `pointsToCell_combine`, `allocMeta_persistent`, `allocMeta_agree`, `locInBounds_persistent`, the K1 laws `regionOwn_view`, `regionView_split`, `regionView_join`, `regionOwn_fractional`, `regionOwn_agree`, the K5.1 distinctness laws `regionOwn_ne`/`regionOwn_deadRegion_ne` (`metaOwn_ne` at the region bundles: a fully owned live region is a different id from any other region ownership and from any dead region; two dead regions carry no such law — dead-id distinctness is carried by a client's invariant from when they were live, as `mlLs` does), the K5 typed-region laws `typedRegionView_regionView` (the typed view IS the untyped view at a type-length image), `typedRegionView_split`/`typedRegionView_join` (a region as a struct of typed fields), `regionOwn_carve`/`regionOwn_uncarve` (a typed subrange out of / back into whole-region ownership, metadata whole), `readonlyCell_fractional`, `readonlyCell_agree`, `readonlyCell_pointsToCell_false`, `deadObj_persistent`, `deadRegion_persistent`, `deadObj_agree`, `deadObj_allocMeta_false`, `pointsToCell_deadObj_false`, `cellPtr_inj`, `cellPtr_arrayShift` (provenance-preserving shift), the budget laws `allocBudget_split` (THE split law `allocBudget (a + b) ⊣⊢ allocBudget a ∗ allocBudget b`), `allocBudget_weaken`, `allocBudget_le` (Heap) |
| Side-condition vocabulary (appears in rule statements) | `StorableAt`, `StorableView` (its four-field face for the typed-subrange stores; `StorableAt.toView`), `decIndep`, `atomicTy`, `loadTrapV`, `cellLoadTrap`, `undefByte`, `spliceBytes` with `spliceBytes_length`/`_getElem?`/`_slice_below`/`_slice_self`/`_slice_above` (Heap) |
| The pure memory view (the boring post's vocabulary) | `CellCoh` (one cell: live, writable, in bounds, exactly those bytes, decode-inert), `Coh` = `Sat` (a footprint of pairwise-disjoint such cells), `SpikeCell`, `CellMap`, `readBytesFrom`, `cellsDisjoint` (Heap, Adequacy) — what the `*_consequence` lemmas deliver about the final memory and what `MemTripleU`'s launch premise demands of the initial one |
| Environment laws | `SymFrame`, `symFrame_empty`, `SymFrame.add`, `envAdd`, `envAdd_lookup`, `symCmpK`, `update_env_sym`, `update_env_spec`, `lookup_env_head` (EnvLaws); the extern indirection `resolveExtern`, `evalPexpr_sym_of_resolve`, `resolveExtern_id_of_empty` (Step) |
| The small axioms, proved once | `AtomicStep` (the mask-generic one-step-to-value specification) and the six atomic specifications `store_atomic`, `load_atomic`, `storeAt_atomic`, `loadAt_atomic`, `create_atomic`, `load_atomic_readonly` (K1: the load over a `readonlyCell`; no store counterpart — `storeM_readonly_kills`, Heap, is the engine's refusal), `kill_atomic` (K2: THE DISPOSE RULE — the static kill consumes `pointsToCell … (.own 1)` and delivers the bare unit with at most `deadObj`; `killExpr`), `alloc_atomic`/`free_atomic` (K3), `regionLoadAt_atomic`/`regionStoreAt_atomic` (K5: THE REGION ACCESS RULES — typed load/store through a region pointer over `typedRegionView`, proved through the generic live-cell seams at `regionCell`; the engine checks no type at an untyped allocation, Heap.lean "The typed region view"); the lifting lemmas `wp_of_atomic` (Rules), `wps_of_atomic` (Wps), `wpt_of_atomic` (Wpt) — every memory rule of every judgment is a corollary; `deliveryCost`, `createExpr` (Rules) |
| Base stratum (raw WP) | `wp_store`, `wp_load` — the small axioms at iris-lean's WP, generic in the machine context and the environment (corollaries of the atomic specifications); frame and consequence there are iris-lean's `wp_frame_r`/`wp_mono` (`spike_wp_wand` = `wp_wand`); `stateInterp_readout` (Rules). No raw-WP sequencing rule exists (false at a populated label map — Rules.lean header): sequencing is stated at `wps`/`wpt` |
| Statement judgment (partial) | `wps`, `LabelSpec`, `blockSpecs`, `frameLs`; PROCEDURES (calls arc C3): `ProcSpec` (the specification table: per symbol and argument values, a pre and a post on the delivered value), `emptyProcSpec`, `procSpecs` (every declared body meets its entry, at every caller tail), `procSpecs_intro` (one body proof per procedure, assuming the table — no Löb), `procSpecs_empty`, the call rule `wps_call` (in context) / `wps_call_root` (the `Eproc` redex), `SameTail` (the env-stack shape the collapse hands to a continuation); structural: `wps_ofVal`, `wps_wand`, `wps_fupd`, `wps_mono_Ls`, `wps_frame`, `wps_frame_labels`, `wps_annot`, `wps_annot_reindex`; control: `wps_seq`, `wps_seq_spec`, `wps_seq_sym`, `wps_if` (verdict inside the logic; `wps_if_true`, `wps_if_false` derived), `wps_save` (evaluated initializers; `wps_save_vals`, `wps_save_eval`), `wps_run`, `wps_pure`, `wps_case_value`, `wps_wseq`, `wps_load_eval`, `wps_store_eval`, `wps_kill_eval`, `wps_memop_eval`, `wps_memop_ptreq`; memory: `wps_store`, `wps_load`, `wps_store_plain`, `wps_load_plain`, `wps_load_at`, `wps_store_at`, `wps_load_cell_at`, `wps_store_cell_at`, `wps_load_region_at`, `wps_store_region_at` (K5: through a typed region view), `wps_load_regionOwn_at`, `wps_store_regionOwn_at` (K5: interior access through whole-region ownership, the image spliced), `wps_create`, `wps_alloc`, `wps_free`, `wps_free_emp` (K3), `wps_kill` (K2: the dead-cell form), `wps_kill_emp` (the textbook `{p ↦ -} kill(p) {emp}`); loops: `blockSpecs_intro`, `blockSpecs_frame`, `blockSpecs_mono`; collapse: `wps_sound_cps` (the CPS collapse over the ambient control — the one Löb), `wps_sound`/`wps_sound_frame` (the entry control, with the table), `wps_sound_empty`/`wps_sound_frame_empty` (the empty table: the pre-C3 statements) (Wps) |
| Statement judgment (total) | `wpt`, `LabelSpecT`, `blockSpecsT`, `frameLsT`, `saveEntryCost`, `AnnotInsensitive`; PROCEDURES (C3): `ProcSpecT` (budget-indexed table), `emptyProcSpecT`, `procSpecsT`, `procSpecsT_intro`, `procSpecsT_empty`, `wpt_call`/`wpt_call_root` (with the budget split `1 + m + k' ≤ k`); `wpt_ofVal`, `wpt_mono`, `wpt_mono_k`, `wpt_mono_Ls`, `wpt_fupd`, `wpt_frame`, `wpt_frame_labels`, `wpt_annot`, `wpt_annot_reindex`, `wpt_seq`, `wpt_seq_spec`, `wpt_seq_sym`, `wpt_wseq`, `wpt_if` (`wpt_if_true`, `wpt_if_false` derived), `wpt_save` (`wpt_save_vals`, `wpt_save_eval`), `wpt_run`, `wpt_pure`, `wpt_case_value`, `wpt_load_eval`, `wpt_store_eval`, `wpt_kill_eval`, `wpt_memop_eval`, `wpt_memop_ptreq`, `wpt_store`, `wpt_load`, `wpt_store_plain`, `wpt_load_plain`, `wpt_load_at`, `wpt_store_at`, `wpt_load_cell_at`, `wpt_store_cell_at`, `wpt_load_region_at`, `wpt_store_region_at`, `wpt_load_regionOwn_at`, `wpt_store_regionOwn_at` (K5, budget `3 ≤ k`), `wpt_create`, `wpt_alloc`, `wpt_free`, `wpt_free_emp` (K3), `wpt_kill`, `wpt_kill_emp` (K2, budget `2 ≤ k`), `blockSpecsT_mono`, `blockSpecsT_frame`, `wpt_sound_cps` (strong induction on the budget), `wpt_sound`, `wpt_sound_empty` (Wpt) |
| The static fuel bound | `pot` (the step-monotone size potential), `Frag.esize_le_pot`, `Frag.pot_le_two`, `Frag.pot_step_bound` — the two static premises `pot e ≤ lemDefaultFuel` / `pot cont ≤ lemDefaultFuel` every adequacy theorem carries in place of a run-length-coupled bound (Potential) |
| Adequacy (partial) — PROVISIONAL, over `driveU` (header) | THE HEADLINE OF THE PARTIAL LANE: `MemTripleU` (the boring triple — memory splits as P ⊎ R, the engine's drive at ANY length never kills or derails, every delivered `(v, σ')` satisfies a pure `ψ R v σ'`; frame built in) and `project_triple_pure` (any Iris triple whose framed post pure-entails ψ under the coupling → `MemTripleU`; conclusion Iris-free); `project_triple` (the strongest-post form beneath it: post = every pure consequence of the Iris post at the final memory) and the pure-consequence lemmas that discharge the obligation — `pure_consequence`, `sep_consequence`, `or_consequence`, `exists_consequence`, `cellOwn_consequence`, `pointsToCell_consequence`, `cellsOwn_consequence`, `cells_consequence`; THE ALLOCATING TWINS: `MemTripleU_alloc` (launched under `LaunchCoh` with an allocation budget `B`), `project_triple_pure_alloc`, `project_triple_alloc`, `MemTripleU_alloc_of_MemTripleU`; the cells-shaped instance `SemTripleU`, `ProvenTripleU`, `SemTripleU_iff_Mem`, `semantic_triple_soundU`, `semantic_frameU`; `Sat`, `CellMap`; THE ONE DRIVE `driveU`, `DriveResult`; the launches `spike_step_adequacy`, `spike_step_adequacy_alloc`, `engine_adequacyU`, `engine_adequacyU_alloc`; the profiles' vacuous label premises `spikeCtx_labels_none`, `spikeCtx_labels_frag`, `spikeCtx_labels_pot`; launch vocabulary `LaunchCoh` (its `budget` field `B ≤ headroom lastAddress` is the budget-fits-the-cold-start-memory obligation, stated over the engine's `lastAddress`), `launchResources`, `headroom`; the public readouts `cellOwn_readout`, `deadObj_readout`, `deadRegion_readout` (K5, the K4 audit's N-1: a dead cell/region reads its kill effect — id in `deadAllocations`, record erased — off the final state; the destructive single-allocation faces), and the CONSEQUENCE faces `deadObj_dead`/`deadRegion_dead` (the same facts under the coupling tokens `CohG`/`metaInterp`, for a client reading MANY dead ids off one state under `stateInterp_readout` — the documented exception, as `cellOwn_consequence`) (Adequacy, Heap) |
| Adequacy (total) — PROVISIONAL, over `driveU` (header) | `wpt_engine_boundU`, `wpt_engine_boundU_alloc`, `readoutPost`, `DriveDoneAt` (TotalAdequacy). The root-of-trust total statements over the shipped driver (`exhibitA_prod`, `*_certified_production`, `prod_run_eqJ`) are in the production layer, not imported here |

## Below the line (INTERNAL — visible, not part of the surface)

| Family | Names | Why internal |
|---|---|---|
| The coupling invariant and the ghost carrier | `CohG` (with its `wf` field and the derived `CohG.cur_*` facts), the global memory well-formedness invariant `MemWF` and its lemmas (`MemWF.*`, `allocDisjoint`, `freshBase_add_le_nat`; the exported faces are `create_fresh_global`, `prodMem₀_memWF` and the preservation theorems `MemWF.loadM`/`MemWF.storeM`/`MemWF.allocateObject`/`MemWF.create`/`MemWF.killM` (K2, both arms) and the explicit-shape `MemWF.kill`, pinned in Audit.lean), the K2 kill seams `killM_success` (the engine's active arm at a live cell), `killM_killed_inv` (Round: the three refusal rows), `MetaCoh.kill_other`, `CohG.kill`, `metaHeap_update`, `allocations_erase_get?`, the `∈`/`contains` bridge for LemLib's `BEq Int` (`mem_contains_int`, `contains_cons_int`, `contains_cons_ne_int`, `int_beq_eq_true`; K1 audit M-1), `SpikeGS`'s fields, `byteOwn`, `metaOwn`, `cursorOwn`, `bytesOwn`, `byteInterp`/`metaInterp`/`cursorInterp`, the budget authority `budgetAuth` with `budgetInterp` (the coupling inequality conjunct) and its laws `budgetAuth_bound`/`budgetAuth_consume`/`budgetAuth_grant`/`budgetInit`/`budgetAuth_of_init`/`budgetInterp_zero`/`budgetInterp_intro`, `BudgetGS`, `SpikeState`, `stateInterp_eq`, `byteHeap_*`, `metaHeap_*`, `cursorHeap_*`, `bytesOwn_get`/`_read`/`_update`, `metaOwn_ne`, `bigSepM_own_disjoint`, `cellsOwn_*`, `cells_readout`, `genHeap_valid_big`, `MetaCell` (with `objCell`/`regionCell`), `metaOf`, `MetaCoh`/`LiveCoh` (`MetaCoh.of_fields`), `atomicTyOpt`, `cellOwn_cellCoh`, and the coupling readouts `pointsToCell_live`, `readonlyCell_readonly`, `regionOwn_facts` (Heap, Adequacy); `deadObj_dead`/`deadRegion_dead` are PUBLIC consequence faces since K5 (above) | The state interpretation is the logic's implementation. Its client-facing consequences are exported: the readouts, the pure-consequence lemmas and the pure memory view `CellCoh`/`Sat` above. `CohG`, `metaInterp`, `byteInterp` appear in the premises of the projection theorems and the readout/consequence lemmas — the one documented exception (header) — as opaque tokens a client never opens: the obligation is discharged only through the `*_consequence` lemmas |
| The allocator cursor and the engine bound behind the budget | `AllocCursor` (the cursor cell; its fragment lives in the state interpretation since K2.5), `freshBase`, `cursorOwn`, the pure engine bounds `freshBase_ne_zero_of_cost`/`headroom_freshBase`, `create_atomic` (the budget-premised atomic step the public rules lift), `CohG.create`, `allocateObject_success` (Heap, Rules) | `allocBudget` is the capacity face; the cursor is how the heap implements it. Clients receive `allocBudget B` from the allocation-aware launchers (`launchResources` under `LaunchCoh … B`) and never mint it: `budgetAuth_grant` is the launchers' lemma |
| The engine transition and its certification | `Step` and every `Step.*` lemma, `Decomp`, `jumpRedex?`, `toVal`, `primStep`, the `Language` instance's facts (Lang); all of Soundness except `Frag` (`engine_step_matchU`, …); all of Round (`CerberusRound`, `cerberusRound_classify`, `step_iff_cerberusRound`) | They certify the rules against the engine. A client reasoning through them bypasses the logic |
| The `driveU` lane's proof devices | the hand-written discharge `dischargeStep`/`outcomesU`/`stepOutcomes` and the lemmas stated over them — `stepDischarge_*` (Soundness), `outcomesU_of_step`, `outcomesU_of_call`, `outcomesU_of_ret`, `drive_classifyU`, `drive_classifyU_aux` (Adequacy) | Proof devices (the trust rule of 2026-09-02): their statements' referent is a package definition, not the engine, so they are not exports — UNPINNED in Audit.lean since the 2026-09-03 standards-audit response, bounded by the exhaustive sweep. A client consumes the adequacy exports above, never these |
| Judgment unfoldings | `wps.pre`, `wps_unfold`, `wpt.pre`, `wpt_unfold`, `wpt_val_eq`, `wpt_jump_eq`, `wpt_call_eq`, `wpt_step_eq`, `wpt_zero_step_eq`, `wpt_empty_call_false`, `wpt_det_step`, `wpt_drive_aux`; the collapses' return devices `wp_ret`/`wp_ret_annot`/`twp_ret`/`twp_ret_annot` (the RETURN and REMOVE-ANNOT rounds at the raw WP/TWP) | The judgments are used through their rules |
| memM lemmas and byte-map algebra | `storeM_success`, `loadM_success`, `loadM_live`, `storeM_live`, `loadM_at`, `storeM_at`, `storeM_readonly_kills`, `storeM_readonly_none`, `applyMemM_eq_ndProj`, `writeBytesTo_*`, `readBytesFrom_*`, `byteAt_*`, `MetaByteOf`, `spikeCells_alloc`, `intToBytes_*`, `bytesToInt_*` (Heap, Adequacy) | Engine-memory facts consumed by the rule proofs and the launch |

## Not imported here at all

`DriverCollapse`, `ProdLoop`, `ProdEntry` (the production-export
layer: itself a client of adequacy, imported directly by the
production exhibits), every `*Exhibit`, `Examples.*`, and `Audit`.
-/
import CerberusHeapLang.Heap
import CerberusHeapLang.EnvLaws
import CerberusHeapLang.Rules
import CerberusHeapLang.Wps
import CerberusHeapLang.Wpt
import CerberusHeapLang.Potential
import CerberusHeapLang.Adequacy
import CerberusHeapLang.TotalAdequacy
