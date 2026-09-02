/-
CerberusHeapLang.API — THE PUBLIC SURFACE of the logic, as one import.

Alloc arc P5 (2026-09-01 skeptical re-audit, charter P5 item 3; R-07).
A client of the logic — an exhibit today, a type interpretation
tomorrow — imports THIS module and nothing below it:

    import CerberusHeapLang.API

and works inside `namespace CerberusHeapLang` (or `open`s it): every
public name below already lives in that namespace, so no `export`
re-declarations are needed. The readiness smoke test
(`CerberusHeapLang.Examples.ReadinessSmoke`) is the first consumer
built this way.

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
the remedy is a new PUBLIC lemma here-below (as `cellOwn_readout` was added at
P4.1 when three clients opened the state interpretation), never an
exposure of the internal.

THE IMPORT DIRECTION this module sits in (semantics → heap → rules →
adequacy → clients) is a grep speedbump in `scripts/test_unit.sh`: no
semantics/heap/rule/adequacy module — this one included — imports an
`*Exhibit`, `Examples.*` or `Prod*` module.

## The surface (PUBLIC — import and use freely)

| Family | Names (module) |
|---|---|
| Program vocabulary | `CoreExpr`, `EnvStack`, `SpikeVal` (`.pure`/`.annot`, `mergeInto`), `ofVal`, `MachineCtx` (`.tagDefs`, `.extern`, `.labels`, `.SeqWF`), `spikeCtx`, `spikeEnv`, `symPat`, `storeOpRedex` (Step); `storeExpr`, `loadExpr`, `sseqExpr`, `addrOf`, `loadedVal` (Rules); `createExpr` (Wps); `Frag` — fragment membership, the adequacy premise (Soundness) |
| Pointer/location assertions | `cellPtr`, `SpikeCell`, `pointsToCell` (`pv ↦c[tds]{dq} ty ; bs`), `pointsToView` (typed sub-range view), `cellOwn` (whole-allocation bundle at a ghost id), `allocMeta` (persistent allocation knowledge), `locInBounds`, `allocCap` (abstract allocation capacity), `AllocReq` (Heap) |
| Assertion laws | `pointsToCell_cellOwn_iff`, `cellOwn_view`, `pointsToView_split`, `pointsToView_join`, `pointsToView_fractional`, `pointsToView_agree`, `pointsToView_persist`, `pointsToView_locInBounds`, `cellOwn_fractional`, `pointsToCell_fractional`, `pointsToCell_agree`, `pointsToCell_combine`, `allocMeta_persistent`, `allocMeta_agree`, `locInBounds_persistent`, `cellPtr_inj`, `cellPtr_arrayShift` (provenance-preserving shift), `allocCap_intro`, `allocCap_weaken` (Heap) |
| Side-condition vocabulary (appears in rule statements) | `StorableAt`, `StorableView` (its four-field face for the typed-subrange stores; `StorableAt.toView`), `decIndep`, `atomicTy`, `loadTrapV`, `cellLoadTrap`, `undefByte`, `spliceBytes` with `spliceBytes_length`/`_getElem?`/`_slice_below`/`_slice_self`/`_slice_above` (Heap) |
| Environment seam | `SymFrame`, `symFrame_empty`, `SymFrame.add`, `envAdd`, `envAdd_lookup`, `symCmpK`, `update_env_sym`, `update_env_spec`, `lookup_env_head` (EnvLaws); the extern seam `resolveExtern`, `evalPexpr_sym_of_resolve`, `resolveExtern_id_of_empty` (Step) |
| Base stratum (raw WP) | `wp_store`, `wp_load` — the small axioms at iris-lean's WP, generic in the machine context and the environment; frame and consequence there are iris-lean's `wp_frame_r`/`wp_mono` (`spike_wp_wand` = `wp_wand`); `stateInterp_readout` (Rules). No raw-WP sequencing rule exists (false at a populated label map — Rules.lean header): sequencing is stated at `wps`/`wpt` |
| Statement judgment (partial) | `wps`, `LabelSpec`, `blockSpecs`, `frameLs`; structural: `wps_ofVal`, `wps_wand`, `wps_fupd`, `wps_mono_Ls`, `wps_frame`, `wps_frame_labels`, `wps_annot`, `wps_annot_reindex`; control: `wps_seq`, `wps_seq_spec`, `wps_seq_sym`, `wps_if` (verdict inside the logic; `wps_if_true`, `wps_if_false` derived), `wps_save` (evaluated initializers; `wps_save_vals`, `wps_save_eval`), `wps_run`, `wps_pure`, `wps_case_value`, `wps_wseq`, `wps_load_eval`, `wps_store_eval`, `wps_memop_eval`, `wps_memop_ptreq`; memory: `wps_store`, `wps_load`, `wps_store_plain`, `wps_load_plain`, `wps_load_at`, `wps_store_at`, `wps_load_cell_at`, `wps_store_cell_at`, `wps_create`; loops: `blockSpecs_intro`, `blockSpecs_frame`, `blockSpecs_mono`; collapse: `wps_sound`, `wps_sound_frame` (Wps) |
| Statement judgment (total) | `wpt`, `LabelSpecT`, `blockSpecsT`, `frameLsT`, `saveEntryCost`, `AnnotInsensitive`; `wpt_ofVal`, `wpt_mono`, `wpt_mono_k`, `wpt_mono_Ls`, `wpt_fupd`, `wpt_frame`, `wpt_frame_labels`, `wpt_annot`, `wpt_annot_reindex`, `wpt_seq`, `wpt_seq_spec`, `wpt_seq_sym`, `wpt_wseq`, `wpt_if` (`wpt_if_true`, `wpt_if_false` derived), `wpt_save` (`wpt_save_vals`, `wpt_save_eval`), `wpt_run`, `wpt_pure`, `wpt_case_value`, `wpt_load_eval`, `wpt_store_eval`, `wpt_memop_eval`, `wpt_memop_ptreq`, `wpt_store`, `wpt_load`, `wpt_store_plain`, `wpt_load_plain`, `wpt_load_at`, `wpt_store_at`, `wpt_load_cell_at`, `wpt_store_cell_at`, `wpt_create`, `blockSpecsT_mono`, `blockSpecsT_frame`, `wpt_sound` (Wpt) |
| The static fuel bound | `pot` (the step-monotone size potential), `Frag.esize_le_pot`, `Frag.pot_le_two`, `Frag.pot_step_bound` — the two static premises `pot e ≤ lemDefaultFuel` / `pot cont ≤ lemDefaultFuel` every adequacy theorem carries in place of a run-length-coupled bound (Potential) |
| Adequacy (partial) | THE HEADLINE: `MemTripleU` (the boring triple — memory splits as P ⊎ R, the engine's drive at ANY length never kills or derails, every delivered `(v, σ')` satisfies a pure `ψ R v σ'`; frame built in) and `project_triple_pure` (any Iris triple whose framed post pure-entails ψ under the coupling → `MemTripleU`; conclusion Iris-free); `project_triple` (the strongest-post form beneath it: post = every pure consequence of the Iris post at the final memory) and the pure-consequence lemmas that discharge the obligation — `pure_consequence`, `sep_consequence`, `or_consequence`, `exists_consequence`, `cellOwn_consequence`, `pointsToCell_consequence`, `cellsOwn_consequence`, `cells_consequence`; THE ALLOCATING TWINS (P6.1): `MemTripleU_alloc` (launched under `LaunchCoh` with a request plan), `project_triple_pure_alloc`, `project_triple_alloc`, `MemTripleU_alloc_of_MemTripleU`; the cells-shaped instance `SemTripleU`, `ProvenTripleU`, `SemTripleU_iff_Mem`, `semantic_triple_soundU`, `semantic_frameU`; `Sat`, `CellMap`; THE ONE DRIVE `driveU`, `DriveResult`; the launches `spike_step_adequacy`, `spike_step_adequacy_alloc`, `engine_adequacyU`, `engine_adequacyU_alloc`; the profiles' vacuous label premises `spikeCtx_labels_none`, `spikeCtx_labels_frag`, `spikeCtx_labels_pot`; launch vocabulary `LaunchCoh`, `launchResources`, `PlanFits` (the plan-fits-the-cold-start-memory obligation, stated over the engine's `lastAddress`/`nextAllocId`); the public readout `cellOwn_readout` (Adequacy) |
| Adequacy (total) | `wpt_engine_boundU`, `wpt_engine_boundU_alloc`, `readoutPost`, `DriveDoneAt` (TotalAdequacy) |

## Below the line (INTERNAL — visible, not part of the surface)

| Family | Names | Why internal |
|---|---|---|
| The coupling invariant and the ghost carrier | `CohG`, `SpikeGS`'s fields, `byteOwn`, `metaOwn`, `cursorOwn`, `bytesOwn`, `byteInterp`/`metaInterp`/`cursorInterp`, `SpikeState`, `stateInterp_eq`, `byteHeap_*`, `metaHeap_*`, `cursorHeap_*`, `bytesOwn_get`/`_read`/`_update`, `metaOwn_ne`, `bigSepM_own_disjoint`, `cellsOwn_*`, `cells_readout`, `genHeap_valid_big`, `MetaCell`, `metaOf`, `MetaCoh`, `CellCoh`, `Coh`, `cellOwn_cellCoh` (Heap, Adequacy) | The state interpretation is the logic's implementation. Its client-facing consequences are exported: the readouts and the pure-consequence lemmas above. `CohG`, `metaInterp`, `byteInterp` appear in ONE public statement — the pure-consequence obligation in `project_triple`'s post — as opaque tokens a client never opens: the obligation is discharged by the `*_consequence` lemmas |
| The allocator cursor | `AllocCursor` (as a resource), `advanceCursor`, `freshBase`, `cursorOwn`, `wps_create_cursor_internal`, `wpt_create_cursor_internal`, `CohG.create`, `allocateObject_success` (Heap, Wps, Wpt) | `allocCap` is the abstract capacity face (alloc arc P1); the cursor is how the heap implements it |
| The engine transition and its certification | `Step` and every `Step.*` lemma, `Decomp`, `jumpRedex?`, `toVal`, `primStep`, the `Language` instance's facts (Lang); all of Soundness except `Frag` (`stepDischarge_*`, `engine_step_matchU`, …); all of Round (`CerberusRound`, `cerberusRound_classify`, `step_iff_cerberusRound`) | They certify the rules against the engine. A client reasoning through them bypasses the logic (the R-02 failure mode) |
| Judgment unfoldings | `wps.pre`, `wps_unfold`, `wpt.pre`, `wpt_val_eq`, `wpt_jump_eq`, `wpt_step_eq`, `wpt_zero_step_eq`, `wpt_det_step`, `wpt_drive_aux` | The judgments are used through their rules |
| memM seams and byte-map algebra | `storeM_success`, `loadM_success`, `loadM_at`, `storeM_at`, `writeBytesTo_*`, `readBytesFrom_*`, `byteAt_*`, `MetaByteOf`, `spikeCells_alloc`, `intToBytes_*`, `bytesToInt_*` (Heap, Adequacy) | Engine-memory facts consumed by the rule proofs and the launch |

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
