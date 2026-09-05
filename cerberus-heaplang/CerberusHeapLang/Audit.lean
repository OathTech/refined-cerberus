/-
CerberusHeapLang.Audit — the in-build axiom gate of this package.
Last import of the lib root, so `lake build` elaborates it; a failure
here is a red build. Part of the trust base ([USER 2026-09-02]: the
build + this sweep + the banned-methods grep; everything else is a
speedbump).

Three checks, in order:
1. EXACT PINS over the public exports (`trioExports`): each export
   must exist, be a theorem, and its transitive axiom set must EQUAL
   the classical trio. Growth OR shrinkage is a build failure until
   the list is re-baselined in the same commit with the reason.
2. THE EXHAUSTIVE SWEEP: every theorem of every `CerberusHeapLang.*`
   module (module-of-origin, so top-level names cannot dodge),
   INTERNAL DETAILS INCLUDED (private names, proof and match
   auxiliaries, equation lemmas — `Name.isInternalDetail` is NOT
   consulted), is BOUNDED by the trio — no module is allowed anything
   else.
3. THE BANNED-AXIOM SWEEP over EVERY constant kind of our modules,
   internal details included: `sorryAx` / `ofReduceBool` /
   `ofReduceNat` anywhere in any cone (defs included, referenced by a
   theorem or not) fails the build.

THE SCOPE IS EXACT (2026-09-02 detailed audit, L-1): until
2026-09-02 both sweeps skipped `n.isInternalDetail`, so a private
`theorem … := by sorry` unused by any pinned export passed the build
while the emitted text said "every theorem" — measured by a planted
private sorry in a leaf module (green under the old sweeps, red under
these; transcript in
cerberus-heaplang/docs/2026-09-02_audit-response-3-notes.md). The
skips are removed; the counts the build prints are the whole package.
The run costs the same (1.8 s wall, before and after). THE TWO TOTALS
ARE INFORMATIONAL, NOT A BASELINE (2026-09-02 re-review, N-3): they
include auxiliary declarations (equation lemmas, match splitters) that
a module realizes on demand for DEPENDENCY definitions whenever the
imported environment lacks them, so they vary with the semantics
workspace's build state at the same pin — measured 2249/3536 against
the pin's CerbMem.lean and 2210/3474 against a workspace re-primed
from a later cerberus-lean commit, the 62-constant delta being
`CerbMem.*` splitters/equation lemmas realized inside ListRevExhibit
(cerberus-heaplang/docs/2026-09-02_audit-response-4-notes.md). The
verdicts are the check; the numbers are a census of the run.

THE TRUST BASE IS THE CLASSICAL TRIO, EXACTLY, OVER EVERY EXPORT.
There is no declared boundary axiom. The former temporal boundary
(`runEffectful`, the lem runtime's effect-erasure axiom, which entered
the production-entry theorems through their statements — the shipped
`initial_driver_state` drew `sym_supply` through it) was RETIRED on
the semantics side by the cerberus-lean effect-retirement arc and left
this repo at the 2026-09-02 re-pin to cerberus-lean
`ddcfc919972a31bc43a0454e6b2e76a19e6c4594` (LemLib `045dcb0`, zero
axioms; record: cerberus-heaplang/docs/2026-09-02_repin-notes.md).
The production entry is now the pure, supply-threaded
`initial_driver_state (sup : Nat) file fs : driver_state × Nat`
(Driver.lean:446; `initial_core_run_state`, Core_run_aux.lean:406,
seeds `sym_supply` from `sup`), and the production-entry theorems
quantify over the supply; E5 assignment clients additionally expose a
lower bound on that initial supply. The nine
former boundary exports sit in `trioExports` like everything else.
Re-pinned 2026-09-03 to cerberus-lean `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`
(the fuel arc: the drive cone's fuel exhaustion is the kernel-transparent
kill `CerbND.fuelExhaustedKill`, its budget the citable
`CerbFuel.driverFuel = 10^8`; record:
cerberus-heaplang/docs/2026-09-03_repin-fuel-notes.md): no name moved, the
pin list below: 296 after K5.1 (the re-pin itself moved no pin), and the production statements' side
conditions read `k + 2 ≤ CerbFuel.driverFuel`.

CALLS ARC C1 (2026-09-03, cerberus-heaplang/docs/2026-09-03_c1-notes.md):
the configuration grew — `Config := CoreExpr × EnvStack × Ctl × Mem`,
the thread's control (call stack, current procedure, execution
location) is live state, `MachineCtx` lost `stack`/`proc`/`execLoc`
and `M.thread e ρ` became `M.thread e ρ ctl`. An internals refactor
under the frozen public spec: no name moved, the pin list below is
unchanged (296); the changed statements change SHAPE only (the
configuration type; `old = new` at the canonical embedding
`ctl = ⟨[], M.proc, M.execLoc⟩`), and the production statements
(`*_certified_production`, `prod_run_eqJ`) are textually unchanged.

CALLS ARC C2 (2026-09-03, cerberus-heaplang/docs/2026-09-03_c2-notes.md):
the procedure call and the return as MIRROR STEPS (`Step.call`, `Step.ret`,
`Step.ret_annot`), their engine certification (`engine_step_matchU` now at a
FREE successor control) and completeness rows (`complete_call`,
`complete_ret`); no logic rule (C3). The judgments `wps`/`wpt` gained the
guard "`⌜False⌝` at a call redex" (the C1 collapses are otherwise false
once the mirror calls — the record's §3); the `driveU` adequacy exports
gained the procedure well-formedness premise `MachineCtx.FragProcs`
(vacuous at both profiles, `spikeCtx_fragProcs`/`procCtx_fragProcs`); the
production round `loop_step_frag` is restated at the LIVE control (the C1
range audit's M-1). 20 pins added: 296 → 316.

STANDARDS-AUDIT RESPONSE (2026-09-03,
cerberus-heaplang/docs/2026-09-03_standards-audit-response.md): four
PROOF DEVICES UNPINNED — `stepDischarge_run` (its statement mentions the
hand-written discharge `dischargeStep`), `outcomesU_of_call` and
`outcomesU_of_ret` (mention `outcomesU`), `drive_classifyU_aux`
(mentions `driveU`). The pin list is THE PUBLIC EXPORTS; a lemma whose
statement's referent is a package-defined device is a proof device, not
an export (the trust rule of 2026-09-02), so it lives in proofs and is
bounded by the exhaustive sweep (check 2) like every other internal
theorem. No statement or proof changed. 316 → 312.

FUEL-LANE RESTATEMENT (2026-09-03, cerberus-heaplang/docs/2026-09-03_f1-notes.md):
the package loop `driveU` and every export over it are DELETED (13 pins
removed: `exhibitA_total`, `wpt_engine_boundU`, `wpt_engine_boundU_alloc`,
`fib_certified_total`, `list_reverse_certified_total`,
`tree_rotate_certified_total`, `counter_loop_certified_registration`,
`alloc_create_launch_smoke`, `kill_launch_smoke`, `free_launch_smoke`,
`dispose_list_certified_total`, `region_loop_certified_total`,
`malloc_list_certified_total`); the partial lane is restated over the
SHIPPED driver's per-thread loop (`DriverSafeCtl`, `engine_adequacy`,
`MemTriple`/`SemTriple`, the projections — the `U` suffix dropped from
every renamed pin) and its closed form over `CerbND.drive_lemFuel`
(`prod_run_safe_procs`, `fib_rec_certified`); `call_smoke_driveU` →
`call_smoke_engine`; 14 pins added (list end). 372 → 373.

DIALECT ARC E3 (2026-09-05, cerberus-heaplang/docs/2026-09-05_e3-notes.md):
the impl arithmetic constructors, the std.core unfolding through the FILE
OBJECT (`evalPexpr` reads `M.file`; `stdlibE3`, the transcribed fragment,
checked against the pinned std.core source by the corpus speedbump), the
first C integer rules (`wps_c_add`/`wpt_c_add`, `wps_conv_loaded_int`/
`wpt_conv_loaded_int`), exhibit C (`exhibitC_prod_e3`: `x + 1` in the
emitted shape on the library-carrying file `prodFileLib`), the negative
exhibit (`overflow_driver2_killed`: the UB036 kill at INT_MAX over the
genuine driver's round) and t1's `main` in the cone modulo its `unseq`
(`CorpusE0.t1MainWith_frag`, `CorpusE0.t1_unseq_not_frag`). 80 pins
added (list end): 508 → 588. Left UNPINNED with sub-trio cones (the
2026-09-02 convention): the `rfl`/`decide` facts `peDepth_*Body`,
`stdBudget_*`, `isPePure_*Body`, `int_min_eq`/`int_max_eq`, `mk_iop_*_ival`,
`mk_call_catch_add_in_range`/`_overflow`, `evalCatch_add_*`, `peDepth_cAddPe`,
`progCE3_atAdd_decomp`, `CorpusE0.t1Main_eq_with` (no axioms),
`CorpusE0.t1_convLoadedInt_covered`, `CorpusE0.t1_case_covered`,
`CorpusE0.t1_uncovered_exactly_unseq`, `isPePure_peStrip`, `peDepth_peStrip`,
`peStrip_root`, `stdBudget_le`, `get_ctx_call` (`[propext]` or
`[Quot.sound, propext]`; measured, e3-notes §9).

DIALECT ARC E4 (2026-09-05, cerberus-heaplang/docs/2026-09-05_e4-notes.md):
`Eunseq` mirrored (`Step.unseq_ctx`/`Step.unseq_vals`, `Frag.unseq`), the
certification restated in HEAD form (the engine's step list at a reducible
`unseq` has one entry per reducible component; the shipped loop takes the
head), the rule faces `wps_unseq_focus`/`wps_unseq_vals` (+ `wpt_`) and the
annotated tuple binder `wps_wseq_tuple_annot`/`wpt_wseq_tuple_annot`, and
THE MILESTONE: t1's `main` transcribed verbatim is in `Frag`
(`CorpusE0.t1Main_frag`) and certified end to end over the shipped driver
(`t1_certified_production`, CorpusT1Exhibit.lean). 1 pin REMOVED
(`CorpusE0.t1_unseq_not_frag` — false since `Frag.unseq`), 62 added (list
end): 588 → 650; the E4 range audit R-1 (docs/2026-09-05_audit-e4-range.md §3.6)
measured two more trio-exact theorems unpinned — the MirrorCoverage rounds
`unseq_focus_round`/`unseq_vals_round` — and they are pinned: 652 (the E4
split is 64 trio-exact / 91 sub-trio, not 62/93). Left UNPINNED with sub-trio cones (measured, e4-notes §8):
the `rfl`/`decide`/`simp` facts of Step/Soundness/Potential/EvalClass at the
new constructors (`valsOnly_*`, `ccallFree*`, `isValE_*`, `is_irreducible_*`,
`esizeList_*`, `potList_*`, `pot_unseq`, `esize_unseq`, `focus_exists`/
`focus_unique`, `map_ofValA_inj`, `jumpRedex?_unseq*`, `callRedex?_unseq*`,
`redexAnnots_unseq*`, `*U?_focus`/`_vals`, `callRedexU?_none_of_jumpRedexU?_some`,
`apply_ctx_unseq`, `has_ccall_lemFuel_succ_*`, `ccallFree_has_ccall`,
`ccallFreeList_has_ccall`, `get_ctx_unseq_*`, `get_ctx_annot_unseq`,
`one_step_unseq_aux_collect`, `cons_of_head?`, `Decomp.ccallFree_plug`,
`Decomp.esize_le`, `Decomp.get_ctx_single`, `all_irreducible_eq_valsOnly`,
`length_le_esizeList`, `esize_le_esizeList_of_mem`, `toVal_unseq_node`,
`toVal_none_of_isValE_false`, `operandsOfU_focus`, `CorpusE0.t1_uncovered_none`,
`t1Main_pot`, `t1_four_loadTrap`, `t1CasePe_eq`, `createInt_eq`, `killInt_eq`,
`act_store_eq`, `act_load_eq`).

DIALECT ARC E5, slice 1 of 2 (2026-09-05, cerberus-heaplang/docs/2026-09-05_e5-notes.md):
the NEGATIVE-ACTION PROTOCOL mirrored (`Step.neg_bound` — the engine's Neg arm
at `BOUND_NO_SSEQ`: exclusion id and fresh symbol drawn from the run state,
`negRewrite`; `Step.excluded_store`/`excluded_store_eval`; `Step.case_eval`),
the run state's two supplies as WRITERS on `Ctl.sup` (`Ctl.draw`, the tie
threaded through `loop_step_frag*`, `DriverSafeCtl`/`DriverDoneCtl`/
`DriverDoneAt`, `prodCtl sup`), the classification re-established at every
new root (`complete_neg_act`/`_excluded_store(_op)`/`_case_op`/`_nd`), `pot`
made additive, and `wps_bound`/`wpt_bound` restated for negative-free bodies
within the fuel (`negFree`, `Step.negFree_preserved`, `Step.pot_le`,
`esize_le_pot`). 60 pins added (list end): 652 → 712. No corpus program
certifies yet (the neg-round rule faces are slice 2). Left UNPINNED with
sub-trio cones (measured, e5-notes §8): the `rfl`/`simp`/`decide` facts at the
new constructors and searches — `negRedex?_*`/`negRedexU?_*` (every simp
lemma, the frame `_none` lemmas, `negRedex?_apply_ctx_eq`, the exclusivity
lemmas `*_none_of_negRedex?_some`, `negRedex?_none_of_negFree`),
`callRedex?_apply_ctx_eq`/`callRedexU?_apply_ctx_eq`, `Decomp.negRedex?_*`,
`Redex.negRedex?_some_inv`, `Decomp.get_ctx_rebuild_excluded`,
`Decomp.rebuild_not_irreducible_excl`, `get_ctx_excluded`/`get_ctx_nd`/
`get_ctx_annot_excluded`, the `break_*_frame` lemmas, `Ctl.draw_*`/
`Ctl.toStack_draw`, `negFree*`/`negFreeList_*`/`negFreeAlts_*` (all but the
three `_subst*` and `Step.negFree_preserved`), `ccallFreeAlts_*`/
`ccallFree_apply_ctx_*`/`ccallFree_negRewrite`/`*_map_aux`/`*_of_all`,
`esize_le_pot`/`esizeList_le_potList`/`esizeAlts_le_potAlts(_of)`,
`esize_le_esizeAlts_of_mem`, `potAlts_*`/`pot_le_potAlts_of_mem`/
`potAlts_map_subst_le`/`potList_map_le`, `pot_apply_ctx_plug`/`_excl`,
`pot_negRewrite_le`, `pot_pure_le_two`, `pot_neg`/`pot_excluded`/`pot_let`/
`pot_nd`/`pot_action_pos`, `negRewrite_eq`, `has_ccall_lemFuel_succ_case`/
`_let`/`_nd`, `and_true_intro`, `toVal_none_of_negRedex?_some`,
`jumpRedex?_excluded`/`callRedex?_excluded`, and the equation lemmas
`*.eq_def` the `unfold`s generated.

P3.5 ([USER 2026-09-02], docs/2026-09-02_p3.5-notes.md): the 65
`#guard_msgs in #print axioms` blocks + prose collapsed to the export
list below (62 names at P3.5, the same exact assertion each; the list
grows with every spec-addition slice — the build prints the current
count); the F-07 statement-borne origin discipline was cut; the
StmtProbe pins went with the deleted probe.

Nothing is declared after the sweep (a later constant would dodge
it), and this module stays the lib root's last import.
-/
import Lean
import CerberusHeapLang.Rules
import CerberusHeapLang.Wps
import CerberusHeapLang.Wpt
import CerberusHeapLang.TotalAdequacy
import CerberusHeapLang.Exhibit
import CerberusHeapLang.ProdExhibit
import CerberusHeapLang.ProdLoopExhibit
import CerberusHeapLang.LoopExhibit
import CerberusHeapLang.FibExhibit
import CerberusHeapLang.DivergeExhibit
import CerberusHeapLang.ArrayExhibit
import CerberusHeapLang.ListRevExhibit
import CerberusHeapLang.TreeRotExhibit
import CerberusHeapLang.CaseExhibit
import CerberusHeapLang.WseqExhibit
import CerberusHeapLang.StructExhibit
import CerberusHeapLang.AllocExhibit
import CerberusHeapLang.DisposeExhibit
import CerberusHeapLang.RegionLoopExhibit
import CerberusHeapLang.MallocListExhibit
import CerberusHeapLang.FibRecExhibit
import CerberusHeapLang.TwoLabelExhibit
import CerberusHeapLang.EvenOddExhibit
import CerberusHeapLang.EmittedAExhibit
import CerberusHeapLang.EmittedBExhibit
import CerberusHeapLang.EmittedCExhibit
import CerberusHeapLang.CorpusT1Exhibit
import CerberusHeapLang.CorpusT5Exhibit
import CerberusHeapLang.OverflowExhibit
import CerberusHeapLang.Examples.CorpusE0
import CerberusHeapLang.Examples.CorpusE5
import CerberusHeapLang.Examples.ReadinessSmoke
import CerberusHeapLang.Examples.MirrorCoverage
import CerberusHeapLang.Examples.CallSmoke
import CerberusHeapLang.Round

namespace CerberusHeapLang.Audit

open Lean

/-- The classical trio — the only axioms allowed anywhere. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- THE PUBLIC EXPORTS pinned EXACTLY to the trio (in landing order;
    the README's exhibits table and trust diagram, and WALKTHROUGH §6,
    name these). -/
def trioExports : List Name := [
  -- the two exhibit shapes at the statement stratum (QA-2: the raw-WP
  -- twins `exhibit`/`exhibitC_triple` retired), the engine-facing spine
  ``CerberusHeapLang.wps_exhibit_store_frame, ``CerberusHeapLang.wps_exhibit_seq_stores,
  ``CerberusHeapLang.exhibitA_engine, ``CerberusHeapLang.exhibitB_engine,
  ``CerberusHeapLang.exhibitA_semantic, ``CerberusHeapLang.exhibitB_semantic,
  ``CerberusHeapLang.exhibitC_semantic,
  ``CerberusHeapLang.exhibitC_engine,
  -- the jump layer + the unified relation
  ``CerberusHeapLang.Decomp.step_factor,
  ``CerberusHeapLang.engine_step_matchU,
  ``CerberusHeapLang.engine_adequacy, ``CerberusHeapLang.counter_loop_certified,
  -- the statement-stratified WP (partial) and its rules
  ``CerberusHeapLang.wps_sound, ``CerberusHeapLang.wps_seq, ``CerberusHeapLang.wps_store,
  ``CerberusHeapLang.wps_create, ``CerberusHeapLang.wps_load_at, ``CerberusHeapLang.wps_store_at,
  -- the total layer
  ``CerberusHeapLang.wpt_sound, ``CerberusHeapLang.wpt_store,
  -- the collapse layer (trio-exact: no shipped-state statement)
  ``CerberusHeapLang.driver2_done,
  ``CerberusHeapLang.finalize_done, ``CerberusHeapLang.loop_step_frag,
  ``CerberusHeapLang.wpt_driver_done,
  -- the exhibits
  ``CerberusHeapLang.fib_certified,
  ``CerberusHeapLang.array_sum_certified,
  ``CerberusHeapLang.struct_update_certified, ``CerberusHeapLang.struct_create_store_wps,
  ``CerberusHeapLang.list_reverse_certified, ``CerberusHeapLang.list_reverse_demo,
  ``CerberusHeapLang.tree_rotate_certified,
  ``CerberusHeapLang.diverge_total_unprovable,
  ``CerberusHeapLang.case_certified, ``CerberusHeapLang.wseq_certified,
  -- the shipped engine round and its classification (Round.lean; the
  -- 2026-09-02 mirror-completeness slice restated the round over the
  -- shipped driver's loop body — `dischargeStep`/`outcomesU` are proof
  -- devices, unpinned)
  ``CerberusHeapLang.cerberusRound_classify, ``CerberusHeapLang.step_iff_cerberusRound,
  ``CerberusHeapLang.cerberusRound_refused_store, ``CerberusHeapLang.cerberusRound_refused_load,
  ``CerberusHeapLang.cerberusRound_refused_create, ``CerberusHeapLang.cerberusRound_refused_case,
  -- mirror completeness on the fragment (2026-09-02, commit 2 of the
  -- slice): the assembled theorem and one classification lemma per
  -- redex root of `Frag`
  ``CerberusHeapLang.frag_round_complete,
  ``CerberusHeapLang.complete_store, ``CerberusHeapLang.complete_load,
  ``CerberusHeapLang.complete_create, ``CerberusHeapLang.complete_beta_pure,
  ``CerberusHeapLang.complete_beta_annot, ``CerberusHeapLang.complete_wbeta_pure,
  ``CerberusHeapLang.complete_wbeta_annot, ``CerberusHeapLang.complete_merge,
  ``CerberusHeapLang.complete_case, ``CerberusHeapLang.complete_beta_spec,
  ``CerberusHeapLang.complete_beta_sym, ``CerberusHeapLang.complete_if,
  ``CerberusHeapLang.complete_run, ``CerberusHeapLang.complete_run_noproc,
  ``CerberusHeapLang.complete_save, ``CerberusHeapLang.complete_pure_sym,
  ``CerberusHeapLang.complete_load_op, ``CerberusHeapLang.complete_memop_op,
  ``CerberusHeapLang.complete_store_op, ``CerberusHeapLang.complete_memop_vals,
  -- fragment closure (2026-09-02/03): the closure facts of the narrowed
  -- binder head, the ILLTYPED-at-distance-one equations at the rebuilt
  -- action, the no-current-procedure panic shape, the classifier's value
  -- face, the KILL bridge level by level, the eight KILL step equations
  -- and the driver's with-runstate kill
  -- (`Decomp.get_ctx_rebuild_action` has a SUB-trio cone —
  -- [Quot.sound, propext] — so it cannot sit in an EXACT-trio pin list;
  -- the exhaustive sweep bounds it. `BareHead.step` was pinned here until
  -- E1 (2026-09-05) retired `BareHead` — the LETS-ANNOT beta is mirrored
  -- and `Frag.sseq_sym` admits any fragment head — so the pin is REMOVED,
  -- recorded in cerberus-heaplang/docs/2026-09-04_e1-notes.md.)
  ``CerberusHeapLang.step_ctx_load_illtyped', ``CerberusHeapLang.step_ctx_store_illtyped',
  ``CerberusHeapLang.step_ctx_run_noproc,
  ``CerberusHeapLang.evalClass_val_iff, ``CerberusHeapLang.evalClassList_vals_iff,
  ``CerberusHeapLang.step_eval_bridge_kill, ``CerberusHeapLang.aux2_bridge_kill,
  ``CerberusHeapLang.full_eval_bridge_kill, ``CerberusHeapLang.eval1_bridge_kill,
  ``CerberusHeapLang.step_ctx_if_kill, ``CerberusHeapLang.step_ctx_run_kill,
  ``CerberusHeapLang.step_ctx_save_eval_kill, ``CerberusHeapLang.step_ctx_pure_sym_kill,
  ``CerberusHeapLang.step_ctx_load_eval_kill, ``CerberusHeapLang.step_ctx_store_eval_kill2,
  ``CerberusHeapLang.step_ctx_store_eval_kill3, ``CerberusHeapLang.step_ctx_memop_eval_kill,
  ``CerberusHeapLang.advance_withrs_killed_eval, ``CerberusHeapLang.advance_withrs_killed_tau,
  -- the production-entry exports (formerly the runEffectful boundary;
  -- trio-exact since the 2026-09-02 retirement re-pin — header)
  ``CerberusHeapLang.exhibitA_prod, ``CerberusHeapLang.fib_labeledAt_production,
  ``CerberusHeapLang.prod_run_eqJ,
  ``CerberusHeapLang.fib_certified_production,
  ``CerberusHeapLang.counter_loop_certified_production,
  ``CerberusHeapLang.list_reverse_certified_production,
  -- alloc arc P4.1: the raw separation-logic API closure — the three
  -- allocation facts' laws and their clients (R-06)
  ``CerberusHeapLang.pointsToCell_fractional, ``CerberusHeapLang.pointsToCell_combine,
  ``CerberusHeapLang.pointsToView_fractional, ``CerberusHeapLang.pointsToView_agree,
  ``CerberusHeapLang.pointsToView_persist, ``CerberusHeapLang.pointsToView_locInBounds,
  ``CerberusHeapLang.cellPtr_arrayShift, ``CerberusHeapLang.wps_fupd,
  ``CerberusHeapLang.cellOwn_readout,
  ``CerberusHeapLang.struct_wps_views, ``CerberusHeapLang.struct_x_read_shared_wps,
  ``CerberusHeapLang.cell_read_shared_wps, ``CerberusHeapLang.struct_x_read_persist_wps,
  -- alloc arc P4.2: statement-level framing at both strata (R-05) and
  -- the list/tree arbitrary-frame theorems DERIVED from unframed bodies
  -- (the tree's partial-stratum twin went through `wps_sound_frame` in
  -- `tr_wp_readout` and was retired at QA-2)
  ``CerberusHeapLang.wps_frame_labels, ``CerberusHeapLang.blockSpecs_frame,
  ``CerberusHeapLang.wps_sound_frame, ``CerberusHeapLang.wpt_frame_labels,
  ``CerberusHeapLang.blockSpecsT_frame, ``CerberusHeapLang.wpt_frame,
  ``CerberusHeapLang.lr_wps_frame, ``CerberusHeapLang.lr_wpt_frame,
  ``CerberusHeapLang.tree_rotate_wpt_frame,
  -- alloc arc P4.3: the semantic triple at any machine context (R-09) and
  -- the counter loop's irrelevant-binding test at the engine (R-08)
  ``CerberusHeapLang.semantic_triple_sound, ``CerberusHeapLang.semantic_frame,
  ``CerberusHeapLang.counter_loop_certified_irrelevant_binding,
  -- alloc arc P5: the readiness smoke test (R-07 / charter item 5) — a
  -- two-field object predicate and its load/store/allocate rules derived
  -- from the public API alone (Examples/ReadinessSmoke.lean)
  ``CerberusHeapLang.ReadinessSmoke.twoField_of_cell,
  ``CerberusHeapLang.ReadinessSmoke.twoField_load_x,
  ``CerberusHeapLang.ReadinessSmoke.twoField_load_y,
  ``CerberusHeapLang.ReadinessSmoke.twoField_store_x,
  ``CerberusHeapLang.ReadinessSmoke.twoField_store_y,
  ``CerberusHeapLang.ReadinessSmoke.twoField_create,
  -- the PROJECTION ([USER 2026-09-02], DECISIONS "no boring logic; a
  -- projection theorem only"): any Iris triple projects to the boring
  -- memory-post triple; the pure-consequence lemmas discharge its post.
  -- Professor review 1 (required fix 2): the HEADLINE is the pure form
  -- `project_triple_pure` (+ `_alloc`) — a boring `MemTriple` for a
  -- pure ψ, no Iris in the conclusion; `project_triple` is the
  -- strongest-post form beneath it
  ``CerberusHeapLang.project_triple_pure, ``CerberusHeapLang.project_triple_pure_alloc,
  ``CerberusHeapLang.project_triple, ``CerberusHeapLang.SemTriple_iff_Mem,
  ``CerberusHeapLang.pure_consequence, ``CerberusHeapLang.sep_consequence,
  ``CerberusHeapLang.or_consequence, ``CerberusHeapLang.exists_consequence,
  ``CerberusHeapLang.cellOwn_consequence, ``CerberusHeapLang.pointsToCell_consequence,
  ``CerberusHeapLang.cellsOwn_consequence, ``CerberusHeapLang.cells_consequence,
  -- P6.1 (fresh-eyes review H-1): the ALLOCATING projection — an Iris
  -- triple whose pre is footprint cells ∗ `allocBudget B` (K2.5; formerly
  -- the plan `allocCap reqs`) projects to `MemTripleU_alloc` (launch
  -- premise `LaunchCoh`); `MemTriple` implies it at every budget
  ``CerberusHeapLang.project_triple_alloc,
  ``CerberusHeapLang.MemTriple_alloc_of_MemTriple,
  -- QA-1 (2026-09-02 quality audit, H-1/M-3): the generalized block-entry
  -- rules (save at evaluated initializers) and the six stratum twins
  ``CerberusHeapLang.wps_save, ``CerberusHeapLang.wpt_save,
  ``CerberusHeapLang.wpt_load, ``CerberusHeapLang.wpt_case_value,
  ``CerberusHeapLang.wpt_wseq, ``CerberusHeapLang.wpt_fupd,
  ``CerberusHeapLang.wps_mono_Ls, ``CerberusHeapLang.blockSpecs_mono,
  -- QA-1 (M-4): the one conditional rule with the verdict inside the logic,
  -- and the plain-value forms of the whole-cell small axioms
  ``CerberusHeapLang.wps_if, ``CerberusHeapLang.wpt_if,
  ``CerberusHeapLang.wps_store_plain, ``CerberusHeapLang.wps_load_plain,
  ``CerberusHeapLang.wpt_store_plain, ``CerberusHeapLang.wpt_load_plain,
  -- QA-2: the four exhibits the README's table lists that had no pin
  -- (the allocating projection's engine instance and the three local
  -- allocation consumers)
  ``CerberusHeapLang.struct_create_store_adequacy,
  ``CerberusHeapLang.struct_create_store_adequacy_prodMem₀,
  ``CerberusHeapLang.alloc_two_creates_wps, ``CerberusHeapLang.alloc_create_wpt,
  -- kill/free arc K0 (2026-09-03): the global memory well-formedness
  -- invariant `MemWF` (acceptance goal 3) — global freshness of create,
  -- the cold-start instance, and preservation by the three memory
  -- operations of the fragment
  ``CerberusHeapLang.create_fresh_global, ``CerberusHeapLang.prodMem₀_memWF,
  ``CerberusHeapLang.MemWF.loadM, ``CerberusHeapLang.MemWF.storeM,
  ``CerberusHeapLang.MemWF.allocateObject, ``CerberusHeapLang.MemWF.create,
  -- kill/free arc K1: the extended metadata cell — the generic live-cell
  -- seams, the read-only store refusal (engine fact) and load rule, the
  -- region and dead-cell bundles' laws and coupling readouts
  ``CerberusHeapLang.loadM_live, ``CerberusHeapLang.storeM_live,
  ``CerberusHeapLang.storeM_readonly_kills, ``CerberusHeapLang.storeM_readonly_none,
  ``CerberusHeapLang.load_atomic_readonly, ``CerberusHeapLang.readonlyCell_fractional,
  ``CerberusHeapLang.readonlyCell_agree, ``CerberusHeapLang.readonlyCell_pointsToCell_false,
  ``CerberusHeapLang.readonlyCell_readonly, ``CerberusHeapLang.pointsToCell_live,
  ``CerberusHeapLang.regionView_split, ``CerberusHeapLang.regionView_join,
  ``CerberusHeapLang.regionOwn_view, ``CerberusHeapLang.regionOwn_fractional,
  ``CerberusHeapLang.regionOwn_agree, ``CerberusHeapLang.regionOwn_facts,
  ``CerberusHeapLang.deadObj_agree, ``CerberusHeapLang.deadObj_allocMeta_false,
  ``CerberusHeapLang.pointsToCell_deadObj_false, ``CerberusHeapLang.deadObj_dead,
  -- kill/free arc K2 (2026-09-03): THE DISPOSE RULE (static kill) — the
  -- atomic spec and its wps/wpt faces (dead-cell and textbook forms),
  -- the operand-evaluation forms, the engine seam `killM_success`, the
  -- refusal rows, `MemWF` preservation by `killM` (K0's obligation) and
  -- the coupling preservation `CohG.kill`; the completeness pair and the
  -- refusal instance; the ILLTYPED-at-distance-one and KILL step
  -- equations at the kill operand; the two smoke consumers. (The
  -- `∈`/`contains` bridge lemmas of K1 audit M-1 — `mem_contains_int`,
  -- `contains_cons_int`, `contains_cons_ne_int`, `int_beq_eq_true` —
  -- have SUB-trio cones, [propext, Quot.sound], measured, so they
  -- cannot sit in an EXACT-trio pin list; the exhaustive sweep bounds
  -- them, and `MemWF.kill`/`CohG.kill` consume them.)
  ``CerberusHeapLang.kill_atomic, ``CerberusHeapLang.wps_kill, ``CerberusHeapLang.wps_kill_emp,
  ``CerberusHeapLang.wps_kill_eval, ``CerberusHeapLang.wpt_kill, ``CerberusHeapLang.wpt_kill_emp,
  ``CerberusHeapLang.wpt_kill_eval, ``CerberusHeapLang.killM_success,
  ``CerberusHeapLang.killM_killed_inv, ``CerberusHeapLang.MemWF.kill, ``CerberusHeapLang.MemWF.killM,
  ``CerberusHeapLang.CohG.kill, ``CerberusHeapLang.MetaCoh.kill_other,
  ``CerberusHeapLang.cerberusRound_refused_kill, ``CerberusHeapLang.complete_kill,
  ``CerberusHeapLang.complete_kill_op, ``CerberusHeapLang.step_ctx_kill_illtyped',
  ``CerberusHeapLang.step_ctx_kill_eval_kill,
  ``CerberusHeapLang.alloc_create_kill_wps,
  -- kill/free arc K2.5: THE SPLITTABLE ALLOCATION BUDGET — the ghost
  -- algebra's laws (split/weaken/bound/consume/grant), the state-
  -- interpretation conjunct's two introduction forms, the budget-premised
  -- atomic create (its public faces `wps_create`/`wpt_create` are pinned
  -- above; restated over the budget), the plan-shaped readings, the
  -- launcher and the three cold-start budget fits. NOT pinned (sub-trio
  -- cones `[propext, Quot.sound]`, bounded by the exhaustive sweep): the
  -- pure engine bounds `freshBase_ne_zero_of_cost`/`headroom_freshBase`.
  ``CerberusHeapLang.allocBudget_split, ``CerberusHeapLang.allocBudget_weaken,
  ``CerberusHeapLang.allocBudget_le, ``CerberusHeapLang.budgetAuth_bound,
  ``CerberusHeapLang.budgetAuth_consume, ``CerberusHeapLang.budgetAuth_grant,
  ``CerberusHeapLang.budgetInterp_zero, ``CerberusHeapLang.budgetInterp_intro,
  ``CerberusHeapLang.allocCost_pos, ``CerberusHeapLang.create_atomic,
  ``CerberusHeapLang.wps_create_of_plan, ``CerberusHeapLang.wpt_create_of_plan,
  ``CerberusHeapLang.launchResources, ``CerberusHeapLang.prod_one_int_budget_fits,
  ``CerberusHeapLang.struct_budget_fits, ``CerberusHeapLang.lr_two_node_budget_fits,
  -- K2.5 range audit M-1 (done at K3): the public TOTAL allocation rule was
  -- never pinned (the K2.5 record said it was) — pinned here
  ``CerberusHeapLang.wpt_create,
  -- kill/free arc K3 (2026-09-03): DYNAMIC ALLOCATION AND FREE — the two
  -- atomic specs (`alloc_atomic` over the budget at the region cost,
  -- `free_atomic` over `regionOwn`) and their wps/wpt faces (dead-region
  -- and textbook forms, the alloc operand-evaluation forms; the free
  -- operand form is the kind-generic `wps_kill_eval`/`wpt_kill_eval`), the
  -- engine seams (`allocateRegion_success`, `killM_success_dynamic` — the
  -- :1573 dynamic check through `mem_contains_int`), `MemWF.allocateRegion`
  -- (K0's last stated obligation; acceptance goal 3 closed), the coupling
  -- preservation `CohG.alloc`, the dead-region readout, the completeness
  -- pair and the refusal instance (the OOM row `allocateRegion_killed_inv`),
  -- the ILLTYPED-at-distance-one and the two KILL step equations at the
  -- alloc operands, the cold-start region fit, the two smoke consumers.
  -- NOT pinned (SUB-trio cones `[propext, Quot.sound]`, measured by
  -- `#print axioms`; bounded by the exhaustive sweep, the K2/K2.5
  -- precedent): the pure bounds `freshBase_ne_zero_of_cost'`/
  -- `headroom_freshBase'`/`freshBase_pos_nat`/`regionCost_pos`
  -- (`regionCost_eq` has no axioms at all).
  ``CerberusHeapLang.alloc_atomic, ``CerberusHeapLang.free_atomic,
  ``CerberusHeapLang.wps_alloc, ``CerberusHeapLang.wps_alloc_eval,
  ``CerberusHeapLang.wps_free, ``CerberusHeapLang.wps_free_emp,
  ``CerberusHeapLang.wpt_alloc, ``CerberusHeapLang.wpt_alloc_eval,
  ``CerberusHeapLang.wpt_free, ``CerberusHeapLang.wpt_free_emp,
  ``CerberusHeapLang.allocateRegion_success, ``CerberusHeapLang.killM_success_dynamic,
  ``CerberusHeapLang.MemWF.allocateRegion, ``CerberusHeapLang.CohG.alloc,
  ``CerberusHeapLang.MetaCoh.of_fields_dyn, ``CerberusHeapLang.deadRegion_dead,
  ``CerberusHeapLang.prod_region_budget_fits,
  ``CerberusHeapLang.cerberusRound_refused_alloc, ``CerberusHeapLang.complete_alloc,
  ``CerberusHeapLang.complete_alloc_op, ``CerberusHeapLang.allocateRegion_killed_inv,
  ``CerberusHeapLang.step_ctx_alloc_illtyped', ``CerberusHeapLang.step_ctx_alloc_eval_kill1,
  ``CerberusHeapLang.step_ctx_alloc_eval_kill2,
  ``CerberusHeapLang.alloc_free_wps,
  -- kill/free arc K4 (2026-09-03): THE EXHIBITS — dispose-a-list over
  -- created nodes (DisposeExhibit.lean): the statement judgments at both
  -- strata (dead-list and textbook forms; framed forms), the block
  -- specifications, the readout and the PRODUCTION statement over the
  -- shipped pipeline; the generic build-prefix lemma the production reuses
  -- and its registration tie. (The `driveU` total equation was deleted in
  -- the fuel-lane restatement, 2026-09-03.)
  ``CerberusHeapLang.dl_wps, ``CerberusHeapLang.dl_wps_emp, ``CerberusHeapLang.dl_wps_frame,
  ``CerberusHeapLang.dl_blockSpecs, ``CerberusHeapLang.dl_wpt, ``CerberusHeapLang.dl_wpt_frame,
  ``CerberusHeapLang.dl_blockSpecsT, ``CerberusHeapLang.dlPost_readout,
  ``CerberusHeapLang.lrProdPrefix_wpt, ``CerberusHeapLang.dlProd_wpt,
  ``CerberusHeapLang.dlProd_blockSpecsT, ``CerberusHeapLang.dlProd_labeledAt,
  ``CerberusHeapLang.dispose_list_certified_production,
  -- K4, the second exhibit — n regions from one linear budget
  -- (RegionLoopExhibit.lean): the budget as a loop invariant split per
  -- iteration (`allocBudget_split`), spent by `wps_alloc`/`wpt_alloc`,
  -- the regions returned by `wps_free_emp`/`wpt_free_emp`; both strata,
  -- the block specifications and the PRODUCTION statement. (At K4 the malloc'd
  -- LINKED list was not statable — no load/store rule over `regionOwn`;
  -- K5 added the region access rules and the list is pinned below,
  -- `malloc_list_certified_production`.)
  ``CerberusHeapLang.rl_wps, ``CerberusHeapLang.rl_wpt,
  ``CerberusHeapLang.rl_blockSpecs, ``CerberusHeapLang.rl_blockSpecsT,
  ``CerberusHeapLang.rl_labeledAt,
  ``CerberusHeapLang.region_loop_certified_production,
  -- kill/free arc K5 (2026-09-03): THE REGION ACCESS RULES — the typed
  -- region view's laws (the untyped-view bridge, typed split/join, the
  -- carve/uncarve of whole-region ownership), the two atomic specs
  -- `regionLoadAt_atomic`/`regionStoreAt_atomic` (over `loadM_live`/
  -- `storeM_live` at `regionCell`), their wps/wpt faces over the typed
  -- view and over `regionOwn`; the public dead readouts (K4 audit N-1);
  -- and THE MALLOC'D LINKED LIST exhibit (MallocListExhibit.lean): both
  -- strata, the block specifications, the readout, the registration tie
  -- and the PRODUCTION statement. (`typedRegionView_iff` is `.rfl`; measured trio, unpinned
  -- as the other `_iff`s.)
  ``CerberusHeapLang.typedRegionView_regionView, ``CerberusHeapLang.typedRegionView_split,
  ``CerberusHeapLang.typedRegionView_join, ``CerberusHeapLang.regionOwn_carve,
  ``CerberusHeapLang.regionOwn_uncarve,
  ``CerberusHeapLang.regionLoadAt_atomic, ``CerberusHeapLang.regionStoreAt_atomic,
  ``CerberusHeapLang.wps_load_region_at, ``CerberusHeapLang.wps_store_region_at,
  ``CerberusHeapLang.wps_load_regionOwn_at, ``CerberusHeapLang.wps_store_regionOwn_at,
  ``CerberusHeapLang.wpt_load_region_at, ``CerberusHeapLang.wpt_store_region_at,
  ``CerberusHeapLang.wpt_load_regionOwn_at, ``CerberusHeapLang.wpt_store_regionOwn_at,
  ``CerberusHeapLang.deadObj_readout, ``CerberusHeapLang.deadRegion_readout,
  ``CerberusHeapLang.ml_wps, ``CerberusHeapLang.ml_wpt,
  ``CerberusHeapLang.ml_blockSpecs, ``CerberusHeapLang.ml_blockSpecsT,
  ``CerberusHeapLang.mlPost_readout,
  ``CerberusHeapLang.ml_labeledAt, ``CerberusHeapLang.malloc_list_certified_production,
  -- kill/free arc K5.1 (2026-09-03, the K5 range audit's M-1): REGION
  -- DISTINCTNESS — `metaOwn_ne` at the region bundles, public: a fully
  -- owned live region beside any region ownership / beside a dead region
  -- is a different id (what carries `ids.Nodup` through the malloc'd
  -- list's invariant and into its four strengthened statements).
  ``CerberusHeapLang.regionOwn_ne, ``CerberusHeapLang.regionOwn_deadRegion_ne,
  -- calls arc C2 (2026-09-03): THE PROCEDURE CALL AND RETURN AS MIRROR
  -- STEPS — the control-writing case analysis (`Step.ctl_cases`), the call
  -- inversion, the engine bridges (the PCALL round succeeding, its two
  -- `call_proc` kills and the argument kill; the RETURN round), `call_proc`
  -- in the mirror's terms, the completeness rows (`complete_call`,
  -- `complete_ret`), the live-control driver round (`loop_step_frag` is
  -- pinned above; its control-preserving core `loop_step_frag_same` and
  -- the any-task-kind tau round), the adequacy lane through calls
  -- (the plug lemma, the profiles' vacuous procedure premise), the total
  -- judgment's guard, and the two-procedure smoke rounds (MirrorCoverage).
  -- (`Decomp.callRedex?_inv`/`callRedex?_some`/`pot_plug_call_le` and
  -- `callRedex?_none_of_jumpRedex?_some` have SUB-trio cones — unpinnable
  -- here, bounded by the sweep. The lane's PROOF DEVICES
  -- `drive_classifyU_aux`, `outcomesU_of_call`, `outcomesU_of_ret` were
  -- pinned here by C2 and UNPINNED by the standards-audit response, with
  -- `stepDischarge_run` — see the header; bounded by the sweep.)
  ``CerberusHeapLang.Step.ctl_cases, ``CerberusHeapLang.Step.call_inv,
  ``CerberusHeapLang.step_ctx_call_ws, ``CerberusHeapLang.step_ctx_call_unknown,
  ``CerberusHeapLang.step_ctx_call_arity, ``CerberusHeapLang.step_ctx_call_kill_args,
  ``CerberusHeapLang.step_ctx_ret, ``CerberusHeapLang.call_proc_eq,
  ``CerberusHeapLang.complete_call, ``CerberusHeapLang.complete_ret,
  ``CerberusHeapLang.loop_step_frag_same, ``CerberusHeapLang.loop_step_tau_tsk,
  ``CerberusHeapLang.Decomp.frag_plug_call,
  ``CerberusHeapLang.spikeCtx_fragProcs, ``CerberusHeapLang.wpt_call_eq,
  ``CerberusHeapLang.smoke_call_round, ``CerberusHeapLang.smoke_ret_round,
  -- calls arc C3 (2026-09-03): PROCEDURE SPECIFICATIONS AND THE CALL RULE —
  -- the env-stack facts the CPS collapse threads (`SameTail` across a
  -- control-preserving step, the env-depth invariant, the two return
  -- inversions), the call rule at both strata (in context and at the root
  -- redex), the procedure rule's introduction and the empty table, the
  -- return devices at the raw WP/TWP, THE CPS COLLAPSES (the one Löb;
  -- the budget induction) and their entry-control/empty-table faces, the
  -- total judgment's empty-table call fact, and the two-procedure SMOKE
  -- (Examples/CallSmoke): `f`'s body once at every caller tail, the
  -- table discharged by `procSpecs_intro`, `main` by the call rule, the
  -- collapse WITH the table, the partial lane over the shipped loop with
  -- `FragProcs` at two procedures (`call_smoke_engine`), and the total twins.
  ``CerberusHeapLang.Step.sameTail, ``CerberusHeapLang.Step.env_depth,
  ``CerberusHeapLang.Step.ret_inv, ``CerberusHeapLang.Step.ret_annot_inv,
  ``CerberusHeapLang.wps_call, ``CerberusHeapLang.wps_call_root,
  ``CerberusHeapLang.procSpecs_intro, ``CerberusHeapLang.procSpecs_empty,
  ``CerberusHeapLang.wp_ret, ``CerberusHeapLang.wp_ret_annot,
  ``CerberusHeapLang.wps_sound_cps, ``CerberusHeapLang.wps_sound_empty,
  ``CerberusHeapLang.wps_sound_frame_empty,
  ``CerberusHeapLang.wpt_call, ``CerberusHeapLang.wpt_call_root,
  ``CerberusHeapLang.wpt_empty_call_false,
  ``CerberusHeapLang.procSpecsT_intro, ``CerberusHeapLang.procSpecsT_empty,
  ``CerberusHeapLang.twp_ret, ``CerberusHeapLang.twp_ret_annot,
  ``CerberusHeapLang.wpt_sound_cps, ``CerberusHeapLang.wpt_sound_empty,
  ``CerberusHeapLang.csF_body_wps, ``CerberusHeapLang.csCtx_procSpecs,
  ``CerberusHeapLang.csMain_wps, ``CerberusHeapLang.cs_wp_readout,
  ``CerberusHeapLang.call_smoke_engine,
  ``CerberusHeapLang.csF_body_wpt, ``CerberusHeapLang.csCtx_procSpecsT,
  ``CerberusHeapLang.csMain_wpt, ``CerberusHeapLang.cs_twp_readout,
  ``CerberusHeapLang.csCtx_fragProcs,
  -- calls arc C4 (2026-09-03): RECURSIVE FIB ON THE SHIPPED PIPELINE — the
  -- β-generic symbol-map lookup law (EnvLaws; the smoke's law moved), the
  -- plain-symbol binder's call head (formerly `BareHead.decomp_call_root`,
  -- retired at E1 with `BareHead`), THE
  -- TOTAL DRIVER LANE THROUGH CALLS (the live-control delivery fact's
  -- value/annot/step rounds, the CPS driver induction `wpt_driver_cps`, its
  -- launcher `wpt_driver_done_procs`, the whole-file registration tie), the
  -- N-procedure production entry (`prodFile_eq_with`, `prodFileWith_lookup_main`,
  -- `prodThread_eq_ctlThread`, `drive_after_setup_with`, `prod_run_eqJ_procs`),
  -- and the exhibit: the file's lookups, its registration computed
  -- (`collect_new_fr`) and its whole-file registration
  -- tie, `FragProcs` at two procedures, `fib`'s body ONCE under each table
  -- (Hoare's rule for recursive procedures — no Löb in the client), `main`
  -- by the call rule, the partial closed statement `fib_rec_certified`
  -- (restated over `drive_lemFuel` in the fuel-lane restatement) and THE
  -- EIGHTH ROOT-OF-TRUST STATEMENT `fib_rec_certified_production`.
  -- (`fibRounds_closed` — `[propext, Quot.sound]` — has a SUB-trio cone:
  -- unpinnable here, bounded by the sweep.)
  ``CerberusHeapLang.symAdd_lookup, ``CerberusHeapLang.symAdd_lookup_two,
  ``CerberusHeapLang.procEnv_single,
  ``CerberusHeapLang.LabeledProcs.of_fibers, ``CerberusHeapLang.driverDoneCtl_value,
  ``CerberusHeapLang.driverDoneCtl_annot, ``CerberusHeapLang.driverDoneCtl_step,
  ``CerberusHeapLang.wpt_driver_cps, ``CerberusHeapLang.wpt_driver_done_procs,
  ``CerberusHeapLang.prodFile_eq_with, ``CerberusHeapLang.prodFileWith_lookup_main,
  ``CerberusHeapLang.prodThread_eq_ctlThread, ``CerberusHeapLang.drive_after_setup_with,
  ``CerberusHeapLang.prod_run_eqJ_procs,
  ``CerberusHeapLang.frFile_lookup_fib, ``CerberusHeapLang.frFile_lookup_inv,
  ``CerberusHeapLang.collect_new_fr,
  ``CerberusHeapLang.frCtx_labeledProcs, ``CerberusHeapLang.frCtx_fragProcs,
  ``CerberusHeapLang.frBody_wps, ``CerberusHeapLang.frCtx_procSpecs,
  ``CerberusHeapLang.frMain_wps, ``CerberusHeapLang.fr_wp_readout,
  ``CerberusHeapLang.fib_rec_certified,
  ``CerberusHeapLang.frBody_wpt, ``CerberusHeapLang.frCtx_procSpecsT,
  ``CerberusHeapLang.frMain_wpt, ``CerberusHeapLang.fib_rec_certified_production,
  -- THE FUEL-LANE RESTATEMENT (2026-09-03, docs/2026-09-03_f1-notes.md):
  -- the package loop `driveU` and its lane are DELETED; the partial lane is
  -- over the SHIPPED driver's per-thread loop at every fuel. New exports:
  -- the two round lemmas at a jump-only procedure tie (the pinned
  -- `loop_step_frag_same`/`loop_step_frag` are their instances), the
  -- control tie `CtlTied`'s three laws, the exhaustion rounds and the
  -- killed pipeline arms, the partial adequacy `engine_adequacy(_alloc)`
  -- into `DriverSafeCtl` with its monotonicity, the fuel-generic setup
  -- collapses and THE CLOSED PARTIAL PIPELINE `prod_run_safe_procs` over
  -- `CerbND.drive_lemFuel fuel`, and the negative test's engine fact
  -- `dg_loop_exhausts`. (`runND_killed` has NO axioms — measured — so it
  -- cannot sit in an EXACT-trio pin list; the exhaustive sweep bounds it.
  -- The restated exhibits keep their pins above under their names.)
  ``CerberusHeapLang.loop_step_frag_same', ``CerberusHeapLang.loop_step_frag',
  ``CerberusHeapLang.CtlTied.noproc, ``CerberusHeapLang.CtlTied.entry,
  ``CerberusHeapLang.CtlTied.jump,
  ``CerberusHeapLang.loop_zero_exhausts, ``CerberusHeapLang.loop_step_done_exhaust,
  ``CerberusHeapLang.driver2_killed,
  ``CerberusHeapLang.engine_adequacy_alloc, ``CerberusHeapLang.DriverSafeCtl.mono,
  ``CerberusHeapLang.drive_after_setup_with_lemFuel,
  ``CerberusHeapLang.drive_after_setup_with_killed,
  ``CerberusHeapLang.prod_run_safe_procs,
  ``CerberusHeapLang.dg_loop_exhausts,
  -- THE READOUT LAYER SEALED (2026-09-04, the Reynolds/O'Hearn audit's
  -- Finding 2, Lean part; docs/2026-09-04_ar5-readout-notes.md): the
  -- dead-token consequence faces and the `[∗list]` fold — the two
  -- exhibits' local helpers over `CohG`/`metaInterp` (`deadObj_dead_keep`,
  -- `deadNodes_dead`, `deadRegions_dead`) deleted, `DeadAt` public
  -- (Adequacy.lean). Each measured trio-exact by `#print axioms` before
  -- pinning (the notes, §5).
  ``CerberusHeapLang.deadObj_consequence, ``CerberusHeapLang.deadRegion_consequence,
  ``CerberusHeapLang.bigSepL_consequence,
  -- HYGIENE SLICE H1b (2026-09-04, docs/2026-09-04_h1-notes.md): the coverage
  -- exhibits. The total twins of the case and weak-sequencing consumers
  -- (`wpt_case_value`/`wpt_wseq` gain their consumers; the two
  -- RULE-TOTAL-UNDEMONSTRATED rows become RULE); TWO `save` LABELS in one
  -- procedure body (TwoLabelExhibit.lean: the label-dependent specification,
  -- both bodies, both block specifications, the entry, the engine fact
  -- `two_label_certified` at `procCtx`, and the total twins at budget
  -- `5 * n₁ + 5 * n₂ + 5`); MUTUAL RECURSION (EvenOddExhibit.lean: `even`/`odd`
  -- under the symbol-dependent table on the THREE-procedure file, the closed
  -- partial form `even_odd_certified` and THE NINTH ROOT-OF-TRUST STATEMENT
  -- `even_odd_certified_production`). Each measured trio-exact by the build.
  ``CerberusHeapLang.caseProg_wpt, ``CerberusHeapLang.wseqProg_wpt,
  ``CerberusHeapLang.tl_body2_wps, ``CerberusHeapLang.tl_body1_wps,
  ``CerberusHeapLang.tl_blockSpecs, ``CerberusHeapLang.tl_wps,
  ``CerberusHeapLang.tl_wp_readout, ``CerberusHeapLang.two_label_certified,
  ``CerberusHeapLang.tl_body2_wpt, ``CerberusHeapLang.tl_body1_wpt,
  ``CerberusHeapLang.tl_blockSpecsT, ``CerberusHeapLang.tl_wpt,
  ``CerberusHeapLang.tl_wpt_readout,
  ``CerberusHeapLang.eoCtx_labeledProcs, ``CerberusHeapLang.eoCtx_fragProcs,
  ``CerberusHeapLang.eoEvenBody_wps, ``CerberusHeapLang.eoOddBody_wps,
  ``CerberusHeapLang.eoCtx_procSpecs, ``CerberusHeapLang.eoMain_wps,
  ``CerberusHeapLang.eo_wp_readout, ``CerberusHeapLang.even_odd_certified,
  ``CerberusHeapLang.eoEvenBody_wpt, ``CerberusHeapLang.eoOddBody_wpt,
  ``CerberusHeapLang.eoCtx_procSpecsT, ``CerberusHeapLang.eoMain_wpt,
  ``CerberusHeapLang.even_odd_certified_production,
  -- dialect arc E1 (2026-09-05, docs/2026-09-04_e1-notes.md): annotations
  -- live on every node (the location update on the control), the `bound`
  -- frame and REMOVE-BOUND, the create ACTION_EVAL at `Ivalignof`, the
  -- LETS-ANNOT beta at the plain-symbol binder; the rules at both strata;
  -- the completeness rows; the acceptance exhibit (exhibit A in the emitted
  -- shape, both strata and the production entry) and the mirror witnesses
  ``CerberusHeapLang.wps_bound, ``CerberusHeapLang.wpt_bound,
  ``CerberusHeapLang.wpt_jump_frame_bound,
  ``CerberusHeapLang.wps_create_eval, ``CerberusHeapLang.wpt_create_eval,
  ``CerberusHeapLang.step_ctx_bound_pure, ``CerberusHeapLang.step_ctx_bound_annot,
  ``CerberusHeapLang.stepDischarge_create_eval, ``CerberusHeapLang.step_ctx_beta_sym_annot,
  ``CerberusHeapLang.complete_bound_pure, ``CerberusHeapLang.complete_bound_annot,
  ``CerberusHeapLang.complete_create_op,
  ``CerberusHeapLang.MachineCtx.locUpdTh_thread,
  ``CerberusHeapLang.Step.bound_inv, ``CerberusHeapLang.Step.create_op_inv,
  ``CerberusHeapLang.progAE1_frag, ``CerberusHeapLang.progAE1_wps,
  ``CerberusHeapLang.progAE1_wpt, ``CerberusHeapLang.exhibitA_prod_e1,
  ``CerberusHeapLang.loc_update_nonlib, ``CerberusHeapLang.store_located_step,
  -- E1 range audit N-3 (docs/2026-09-05_audit-e1-range.md): the two sibling
  -- location witnesses, measured trio-exact by the auditor, pinned with the first
  ``CerberusHeapLang.loc_update_lib, ``CerberusHeapLang.loc_update_none,
  ``CerberusHeapLang.bound_annot_round, ``CerberusHeapLang.bound_pure_round,
  ``CerberusHeapLang.create_alignof_round, ``CerberusHeapLang.sseq_sym_annot_round,
  -- E2 (2026-09-05, cerberus-heaplang/docs/2026-09-05_e2-notes.md): the
  -- loaded-value dialect — the acceptance exhibit at both strata and the
  -- production entry, the tuple/weak-symbol binder rules, the new
  -- completeness rows, the pattern-generic beta and raw pure-op engine
  -- equations, the success and FAILURE bridges of the pass-iterating
  -- evaluator/classifier, the list bridges, the failure twins of the kill
  -- equations, the driver-level failure kills, the tuple mismatch panic,
  -- the `step_action` ACTION_EVAL equations, the evaluator equations at
  -- the new constructors, the case inversions and the engine-round
  -- witnesses; each measured trio-exact by the build
  ``CerberusHeapLang.progBE2_frag, ``CerberusHeapLang.progBE2_wps,
  ``CerberusHeapLang.progBE2_wpt, ``CerberusHeapLang.exhibitB_prod_e2,
  ``CerberusHeapLang.wps_seq_tuple, ``CerberusHeapLang.wpt_seq_tuple,
  ``CerberusHeapLang.wps_wseq_tuple, ``CerberusHeapLang.wpt_wseq_tuple,
  ``CerberusHeapLang.wps_wseq_sym, ``CerberusHeapLang.wpt_wseq_sym,
  ``CerberusHeapLang.complete_pure_op, ``CerberusHeapLang.complete_beta_tuple,
  ``CerberusHeapLang.complete_wbeta_tuple, ``CerberusHeapLang.complete_wbeta_sym,
  ``CerberusHeapLang.step_ctx_pure_op_raw, ``CerberusHeapLang.step_ctx_sseq_val_pure,
  ``CerberusHeapLang.step_ctx_sseq_val_annot, ``CerberusHeapLang.step_ctx_wseq_val_pure,
  ``CerberusHeapLang.step_ctx_wseq_val_annot,
  ``CerberusHeapLang.step_eval_bridge, ``CerberusHeapLang.aux2_bridge,
  ``CerberusHeapLang.full_eval_bridge, ``CerberusHeapLang.eval1_bridge,
  ``CerberusHeapLang.evalPexpr_step,
  ``CerberusHeapLang.stepPexprRaw_eval_joint, ``CerberusHeapLang.evalPexpr_shape,
  ``CerberusHeapLang.stepFail_bridge, ``CerberusHeapLang.step_eval_bridge_undef,
  ``CerberusHeapLang.classIter_bridge, ``CerberusHeapLang.aux2_bridge_fail,
  ``CerberusHeapLang.full_eval_bridge_fail, ``CerberusHeapLang.full_eval_bridge_undef,
  ``CerberusHeapLang.eval1_bridge_fail, ``CerberusHeapLang.evalClass_of_none,
  ``CerberusHeapLang.evalClassFold_vals_iff, ``CerberusHeapLang.stExpect_mapM_class,
  ``CerberusHeapLang.mapM_eval1_fail, ``CerberusHeapLang.mapM_save_fail,
  ``CerberusHeapLang.foldM_args_fail, ``CerberusHeapLang.mapM_full_eval_fail,
  ``CerberusHeapLang.mapM_eval1_kill, ``CerberusHeapLang.mapM_save_kill,
  ``CerberusHeapLang.foldM_args_kill,
  ``CerberusHeapLang.step_ctx_if_fail, ``CerberusHeapLang.step_ctx_run_fail,
  ``CerberusHeapLang.step_ctx_save_eval_fail, ``CerberusHeapLang.step_ctx_pure_op_fail,
  ``CerberusHeapLang.step_ctx_load_eval_fail, ``CerberusHeapLang.step_ctx_kill_eval_fail,
  ``CerberusHeapLang.step_ctx_store_eval_fail2, ``CerberusHeapLang.step_ctx_store_eval_fail3,
  ``CerberusHeapLang.step_ctx_alloc_eval_fail1, ``CerberusHeapLang.step_ctx_alloc_eval_fail2,
  ``CerberusHeapLang.step_ctx_create_eval_fail1, ``CerberusHeapLang.step_ctx_create_eval_fail2,
  ``CerberusHeapLang.step_ctx_memop_eval_fail, ``CerberusHeapLang.step_ctx_call_fail_args,
  ``CerberusHeapLang.advance_withrs_failed_eval, ``CerberusHeapLang.advance_withrs_failed_tau,
  ``CerberusHeapLang.runOne_liftCore_run_fail,
  ``CerberusHeapLang.update_env_aux_tuple_mismatch, ``CerberusHeapLang.Frag.pure_sym,
  ``CerberusHeapLang.Frag.sseq_inv_any, ``CerberusHeapLang.Frag.wseq_inv_any,
  ``CerberusHeapLang.step_action_store_eval, ``CerberusHeapLang.step_action_load_eval,
  ``CerberusHeapLang.step_action_create_eval, ``CerberusHeapLang.step_action_alloc_eval,
  ``CerberusHeapLang.step_action_kill_eval,
  ``CerberusHeapLang.evalPexpr_case, ``CerberusHeapLang.evalPexpr_ctor,
  ``CerberusHeapLang.evalPexpr_not, ``CerberusHeapLang.evalPexpr_if,
  ``CerberusHeapLang.Step.case_inv, ``CerberusHeapLang.Step.case_value_inv,
  ``CerberusHeapLang.Step.case_op_inv,
  ``CerberusHeapLang.pure_specified_round, ``CerberusHeapLang.wseq_tuple_pure_round,
  ``CerberusHeapLang.sseq_tuple_pure_round, ``CerberusHeapLang.wseq_sym_pure_round,
  -- E2 range audit R-2 (docs/2026-09-05_audit-e2-range.md): the `Unspecified`
  -- store's byte image IS the fresh cell's `undefByte`s — stated as a theorem
  -- (`rfl`), measured trio-exact, pinned. Its companion `unspec_paddingByte`
  -- (`paddingByte = undefByte`) has NO axioms at all and is therefore unpinned.
  ``CerberusHeapLang.unspec_bytes,
  -- dialect arc E3 (2026-09-05, cerberus-heaplang/docs/2026-09-05_e3-notes.md §9)
  ``CerberusHeapLang.stdlibE3_symMap, ``CerberusHeapLang.stdlibE3_lookup_isRepr,
  ``CerberusHeapLang.stdlibE3_lookup_convInt, ``CerberusHeapLang.stdlibE3_lookup_convLoadedInt,
  ``CerberusHeapLang.lookupFun_isRepr, ``CerberusHeapLang.lookupFun_convInt,
  ``CerberusHeapLang.lookupFun_convLoadedInt, ``CerberusHeapLang.mk_conv_int_int_in_range,
  ``CerberusHeapLang.evalConvInt_int, ``CerberusHeapLang.callBody_isRepr,
  ``CerberusHeapLang.callBody_convInt, ``CerberusHeapLang.callBody_convLoadedInt,
  ``CerberusHeapLang.evalPexpr_conv_int_int, ``CerberusHeapLang.evalPexpr_catch_add_int,
  ``CerberusHeapLang.evalCtor_ivmin_int, ``CerberusHeapLang.evalCtor_ivmax_int,
  ``CerberusHeapLang.evalPexpr_isRepr_int, ``CerberusHeapLang.evalPexpr_convInt_call_int,
  ``CerberusHeapLang.evalPexpr_convLoadedInt_spec,
  ``CerberusHeapLang.evalPexpr_convLoadedInt_unspec, ``CerberusHeapLang.evalPexpr_cAdd,
  ``CerberusHeapLang.stepFail_cAddBranch_overflow, ``CerberusHeapLang.evalPexpr_cAdd_overflow,
  ``CerberusHeapLang.evalClass_cAdd_overflow, ``CerberusHeapLang.wps_c_add,
  ``CerberusHeapLang.wpt_c_add, ``CerberusHeapLang.wps_conv_loaded_int,
  ``CerberusHeapLang.wpt_conv_loaded_int, ``CerberusHeapLang.progCE3_frag,
  ``CerberusHeapLang.progCE3_blockSpecs, ``CerberusHeapLang.progCE3_wps,
  ``CerberusHeapLang.convLoadedInt_pure_wps, ``CerberusHeapLang.convLoadedInt_pure_wpt,
  ``CerberusHeapLang.progCE3_blockSpecsT, ``CerberusHeapLang.progCE3_wpt,
  ``CerberusHeapLang.collect_new_progCE3, ``CerberusHeapLang.progCE3_labeledAt,
  ``CerberusHeapLang.stdlibE3_no_main, ``CerberusHeapLang.exhibitC_prod_e3,
  ``CerberusHeapLang.three_encodes, ``CerberusHeapLang.three_storable,
  ``CerberusHeapLang.cAdd_select_31, ``CerberusHeapLang.convLoadedIntC_eval,
  ``CerberusHeapLang.cAdd_select_max1, ``CerberusHeapLang.overflow_evalClass,
  ``CerberusHeapLang.overflow_step_ctx, ``CerberusHeapLang.overflow_driver2_killed,
  ``CerberusHeapLang.overflow_driver2_killed_frame, ``CerberusHeapLang.prodCtx_labels,
  ``CerberusHeapLang.prodCtx_extern, ``CerberusHeapLang.prodFileWith_eq_lib,
  ``CerberusHeapLang.prodFileLib_stdlib, ``CerberusHeapLang.prodFileLib_lookup_main,
  ``CerberusHeapLang.prodRSLib_labeled, ``CerberusHeapLang.drive_after_setup_lib_lemFuel,
  ``CerberusHeapLang.drive_after_setup_lib_killed, ``CerberusHeapLang.drive_after_setup_lib,
  ``CerberusHeapLang.prod_run_eqJ_lib, ``CerberusHeapLang.prod_run_eqJ_lib1,
  ``CerberusHeapLang.prod_run_safe_lib, ``CerberusHeapLang.CorpusE0.t1MainWith_frag,
  ``CerberusHeapLang.cAdd_pure_round,
  ``CerberusHeapLang.store_conv_loaded_int_round,
  ``CerberusHeapLang.loop_step_withrs_eval_killed,
  ``CerberusHeapLang.call_function_exception_of_callOut,
  ``CerberusHeapLang.call_function_of_callBody, ``CerberusHeapLang.evalPexpr_call,
  ``CerberusHeapLang.evalPexpr_catch, ``CerberusHeapLang.evalPexpr_conv_int,
  ``CerberusHeapLang.evalPexpr_is_unsigned, ``CerberusHeapLang.evalPexpr_wrapI,
  ``CerberusHeapLang.evalPexpr_peStrip, ``CerberusHeapLang.procCtxF_labels,
  ``CerberusHeapLang.stepFail_call, ``CerberusHeapLang.stepFail_catch,
  ``CerberusHeapLang.stepFail_conv_int, ``CerberusHeapLang.stepFail_is_unsigned,
  ``CerberusHeapLang.stepFail_wrapI, ``CerberusHeapLang.stepPexprRaw_peStrip,
  -- dialect arc E4 (2026-09-05, cerberus-heaplang/docs/2026-09-05_e4-notes.md
  -- §8): the unseq mirror's inversions and preservation, the head-form
  -- step-list facts, the completion classification, the unseq rule faces
  -- and the annotated tuple binder, t1's membership, and the acceptance
  -- exhibit (CorpusT1Exhibit) down to its frame lemmas — every new theorem
  -- measured trio-exact by the build is pinned (E3 left its exhibit's frame
  -- lemmas unpinned; E4 pins exhaustively, [AGENT], e4-notes §8)
  ``CerberusHeapLang.Step.unseq_inv, ``CerberusHeapLang.Step.callOf_of_call_unseq,
  ``CerberusHeapLang.Step.ccallFree_preserved, ``CerberusHeapLang.step_ctx_length,
  ``CerberusHeapLang.step_ctx_singleton_of_root, ``CerberusHeapLang.step_ctx_unseq_vals,
  ``CerberusHeapLang.step_ctx_unseq_race, ``CerberusHeapLang.complete_unseq_vals,
  ``CerberusHeapLang.fupd_wps, ``CerberusHeapLang.fupd_wpt_nonval,
  ``CerberusHeapLang.wpt_jump_frame_unseq, ``CerberusHeapLang.wps_unseq_focus,
  ``CerberusHeapLang.wpt_unseq_focus, ``CerberusHeapLang.wps_unseq_vals,
  ``CerberusHeapLang.wpt_unseq_vals, ``CerberusHeapLang.wps_wseq_tuple_annot,
  ``CerberusHeapLang.wpt_wseq_tuple_annot, ``CerberusHeapLang.CorpusE0.t1_unseq_frag,
  ``CerberusHeapLang.CorpusE0.t1Main_frag, ``CerberusHeapLang.collect_new_t1Main,
  ``CerberusHeapLang.prod_two_int_budget_fits, ``CerberusHeapLang.specInt_eval,
  ``CerberusHeapLang.t1ConvLoadedInt_eval, ``CerberusHeapLang.t1LsT_readout,
  ``CerberusHeapLang.t1Main_labeledAt, ``CerberusHeapLang.t1RetQ_bindArgs,
  ``CerberusHeapLang.t1RetQ_inv, ``CerberusHeapLang.t1RetQ_lookup,
  ``CerberusHeapLang.t1_blockSpecs, ``CerberusHeapLang.t1_blockSpecsT,
  ``CerberusHeapLang.t1_cAdd_select_31, ``CerberusHeapLang.t1_certified_production,
  ``CerberusHeapLang.t1_four_encodes, ``CerberusHeapLang.t1_four_fromMemValue,
  ``CerberusHeapLang.t1_four_reconstruct, ``CerberusHeapLang.t1_four_storable,
  ``CerberusHeapLang.t1_wps, ``CerberusHeapLang.t1_wpt,
  ``CerberusHeapLang.t1fr508_lookup_a508, ``CerberusHeapLang.t1fr508_lookup_x,
  ``CerberusHeapLang.t1fr508_sf, ``CerberusHeapLang.t1fr509_lookup_a509,
  ``CerberusHeapLang.t1fr509_lookup_y, ``CerberusHeapLang.t1fr509_sf,
  ``CerberusHeapLang.t1fr515_lookup_a515, ``CerberusHeapLang.t1fr515_sf,
  ``CerberusHeapLang.t1fr516_lookup_a516, ``CerberusHeapLang.t1fr516_sf,
  ``CerberusHeapLang.t1fr517_lookup_a517, ``CerberusHeapLang.t1fr517_lookup_x,
  ``CerberusHeapLang.t1fr517_lookup_y, ``CerberusHeapLang.t1fr517_sf,
  ``CerberusHeapLang.t1fr518_lookup, ``CerberusHeapLang.t1frB_lookup_a510,
  ``CerberusHeapLang.t1frB_lookup_a511, ``CerberusHeapLang.t1frB_sf,
  ``CerberusHeapLang.t1frX_lookup_x, ``CerberusHeapLang.t1frX_sf,
  ``CerberusHeapLang.t1frY_lookup_x, ``CerberusHeapLang.t1frY_lookup_y,
  ``CerberusHeapLang.t1frY_sf, ``CerberusHeapLang.t1sym_eval,
  -- E4 range audit R-1 (2026-09-05, docs/2026-09-05_audit-e4-range.md §3.6): the two
  -- MirrorCoverage `unseq` rounds, measured trio-exact and missed by the E4 pass (650 → 652)
  ``CerberusHeapLang.unseq_focus_round, ``CerberusHeapLang.unseq_vals_round,
  -- dialect arc E5 (1/2) (2026-09-05, cerberus-heaplang/docs/2026-09-05_e5-notes.md §8): every
  -- new theorem measured trio-exact by `collectAxioms` over the 184 new theorems (60 exactly the
  -- trio, 124 sub-trio — listed unpinned in the E5 paragraph above), exhaustively (R-1 convention)
  ``CerberusHeapLang.advance_withrs_tau_rs, ``CerberusHeapLang.case_hbsz_of_branches,
  ``CerberusHeapLang.ccallFree_subst, ``CerberusHeapLang.ccallFree_subst_fold,
  ``CerberusHeapLang.ccallFree_subst_lemFuel, ``CerberusHeapLang.complete_case_op,
  ``CerberusHeapLang.complete_excluded_store, ``CerberusHeapLang.complete_excluded_store_op,
  ``CerberusHeapLang.complete_nd, ``CerberusHeapLang.complete_neg_act,
  ``CerberusHeapLang.Decomp.lift_neg, ``CerberusHeapLang.Decomp.lift_neg',
  ``CerberusHeapLang.esize_subst, ``CerberusHeapLang.esize_subst_fold,
  ``CerberusHeapLang.esize_subst_lemFuel, ``CerberusHeapLang.eval1_bridge_gen,
  ``CerberusHeapLang.Frag.annot_inv, ``CerberusHeapLang.Frag.bound_inv,
  ``CerberusHeapLang.Frag.ccallFree, ``CerberusHeapLang.Frag.excluded_of_neg,
  ``CerberusHeapLang.Frag.negRewrite_frag, ``CerberusHeapLang.Frag.of_negRedex,
  ``CerberusHeapLang.Frag.replug, ``CerberusHeapLang.Frag.unseq_inv,
  ``CerberusHeapLang.loop_step_withrs_tau_rs, ``CerberusHeapLang.nd_fork,
  ``CerberusHeapLang.negFree_subst, ``CerberusHeapLang.negFree_subst_fold,
  ``CerberusHeapLang.negFree_subst_lemFuel, ``CerberusHeapLang.pot_subst,
  ``CerberusHeapLang.pot_subst_fold, ``CerberusHeapLang.pot_subst_lemFuel,
  ``CerberusHeapLang.runOne_pick_cons2, ``CerberusHeapLang.select_case_some,
  ``CerberusHeapLang.Step.ctl_frame_of_κ, ``CerberusHeapLang.step_ctx_case_eval_fail,
  ``CerberusHeapLang.step_ctx_case_eval_shape, ``CerberusHeapLang.step_ctx_case_eval_ws,
  ``CerberusHeapLang.step_ctx_excluded_store, ``CerberusHeapLang.step_ctx_excluded_store_eval_fail2,
  ``CerberusHeapLang.step_ctx_excluded_store_eval_fail3, ``CerberusHeapLang.step_ctx_excluded_store_eval_shape,
  ``CerberusHeapLang.step_ctx_excluded_store_eval_ws, ``CerberusHeapLang.step_ctx_excluded_store_eval_ws',
  ``CerberusHeapLang.step_ctx_excluded_store_illtyped, ``CerberusHeapLang.step_ctx_excluded_store_illtyped',
  ``CerberusHeapLang.step_ctx_nd, ``CerberusHeapLang.step_ctx_neg,
  ``CerberusHeapLang.step_ctx_neg_nobound, ``CerberusHeapLang.Step.excluded_store_canonical,
  ``CerberusHeapLang.Step.excluded_store_inv, ``CerberusHeapLang.Step.excluded_store_op_inv,
  ``CerberusHeapLang.Step.nd_root_elim, ``CerberusHeapLang.Step.negFree_preserved,
  ``CerberusHeapLang.Step.neg_root_elim, ``CerberusHeapLang.Step.pot_le,
  ``CerberusHeapLang.subst_alts_shape, ``CerberusHeapLang.substFold_cons,
  ``CerberusHeapLang.substFold_nil, ``CerberusHeapLang.wps_bound_aux,
  -- E5 resume, t5 fragment checkpoint: all 14 new named theorems measured;
  -- these 12 are trio-exact. peDepthList_map_eq / peDepthAlts_map_eq use
  -- propext only and remain covered by the exhaustive bounded sweep.
  ``CerberusHeapLang.PePure.subst_lemFuel, ``CerberusHeapLang.PePure.subst,
  ``CerberusHeapLang.Frag.of_pePure, ``CerberusHeapLang.subst_sym_expr_pure,
  ``CerberusHeapLang.substFold_pure, ``CerberusHeapLang.Frag.substFold_pure,
  ``CerberusHeapLang.CorpusE0.t5Load_frag, ``CerberusHeapLang.CorpusE0.t5Gt_frag,
  ``CerberusHeapLang.CorpusE0.t5Cond_frag, ``CerberusHeapLang.CorpusE0.t5Bool_frag,
  ``CerberusHeapLang.CorpusE0.t5AssignBlock_frag, ``CerberusHeapLang.CorpusE0.t5Main_frag,
  -- E5 second slice and t5: snapshot-difference measurement of every new
  -- non-internal theorem (86 total: 67 trio-exact, 19 sub-trio). Twelve
  -- were pinned at the fragment checkpoint; these are the remaining 55.
  ``CerberusHeapLang.Step.sup_sym_le, ``CerberusHeapLang.case_eval_round,
  ``CerberusHeapLang.collect_new_t5Main, ``CerberusHeapLang.excluded_store_atomic,
  ``CerberusHeapLang.excluded_store_eval_round, ``CerberusHeapLang.excluded_store_round,
  ``CerberusHeapLang.neg_bound_round, ``CerberusHeapLang.procCtxF_runState_labeled,
  ``CerberusHeapLang.procCtxF_sym_supply, ``CerberusHeapLang.procCtx_runState_labeled,
  ``CerberusHeapLang.procCtx_sym_supply, ``CerberusHeapLang.symOrd_ne_eq_of_num_ne,
  ``CerberusHeapLang.symOrd_self, ``CerberusHeapLang.t5BoolBranch_eval,
  ``CerberusHeapLang.t5Bool_select, ``CerberusHeapLang.t5CmpBranch_eval,
  ``CerberusHeapLang.t5CondPe_eval, ``CerberusHeapLang.t5Cond_select,
  ``CerberusHeapLang.t5Gt_select, ``CerberusHeapLang.t5Int_encodes,
  ``CerberusHeapLang.t5Int_storable, ``CerberusHeapLang.t5LsT_readout,
  ``CerberusHeapLang.t5Main_labeledAt, ``CerberusHeapLang.t5RetQ_bindArgs,
  ``CerberusHeapLang.t5RetQ_inv, ``CerberusHeapLang.t5RetQ_lookup,
  ``CerberusHeapLang.t5Tuple_eval, ``CerberusHeapLang.t5_blockSpecsT,
  ``CerberusHeapLang.t5_certified_production, ``CerberusHeapLang.t5_wpt,
  ``CerberusHeapLang.t5fr529_lookup, ``CerberusHeapLang.update_env_tuple2_mixed,
  ``CerberusHeapLang.update_env_tuple_wild_sym, ``CerberusHeapLang.wps_bound_wseq_tuple,
  ``CerberusHeapLang.wps_bound_wseq_tuple_aux, ``CerberusHeapLang.wps_case_eval,
  ``CerberusHeapLang.wps_excluded_store, ``CerberusHeapLang.wps_excluded_store_eval,
  ``CerberusHeapLang.wps_neg_bound, ``CerberusHeapLang.wps_neg_round,
  ``CerberusHeapLang.wpt_bound_wseq_tuple, ``CerberusHeapLang.wpt_case_eval,
  ``CerberusHeapLang.wpt_excluded_store, ``CerberusHeapLang.wpt_excluded_store_eval,
  ``CerberusHeapLang.wpt_neg_bound, ``CerberusHeapLang.wpt_neg_round,
  ``CerberusHeapLang.wpt_t5AssignBlock, ``CerberusHeapLang.wpt_t5Bool,
  ``CerberusHeapLang.wpt_t5Cond, ``CerberusHeapLang.wpt_t5Gt,
  ``CerberusHeapLang.wpt_t5If, ``CerberusHeapLang.wpt_t5Load,
  ``CerberusHeapLang.wpt_t5Return, ``CerberusHeapLang.wpt_unseq_pure_right,
  ``subst_sym_pexpr_lemFuel.eq_def,
  -- E5 t6 whole-term membership checkpoint: all eleven measured trio-exact.
  ``CerberusHeapLang.CorpusE0.t6Load_frag,
  ``CerberusHeapLang.CorpusE0.t6AssignStmt_frag,
  ``CerberusHeapLang.CorpusE0.t6Run_frag,
  ``CerberusHeapLang.CorpusE0.t6Save_frag,
  ``CerberusHeapLang.CorpusE0.t6Cases_frag,
  ``CerberusHeapLang.CorpusE0.t6Dispatch_frag,
  ``CerberusHeapLang.CorpusE0.t6SpecifiedBranch_frag,
  ``CerberusHeapLang.CorpusE0.t6Switch_select,
  ``CerberusHeapLang.CorpusE0.t6Switch_frag,
  ``CerberusHeapLang.CorpusE0.t6Return_frag,
  ``CerberusHeapLang.CorpusE0.t6Main_frag]

def sortedNames (ns : Array Name) : Array String :=
  (ns.map (·.toString)).qsort (· < ·)

#eval show CoreM Unit from do
  let env ← getEnv
  -- 1. EXACT PINS over the public exports.
  let pin (expected : List Name) (n : Name) : CoreM Unit := do
    let some (.thmInfo _) := env.find? n
      | throwError "CerberusHeapLang export pin FAILED: {n} is missing or not a theorem \
          (renamed/removed export — re-baseline the export list, same commit, with the reason)"
    let axs := sortedNames (← collectAxioms n)
    let exp := sortedNames expected.toArray
    unless axs == exp do
      throwError "CerberusHeapLang export pin FAILED: {n} depends on axioms {axs}, \
        expected EXACTLY {exp}"
  for n in trioExports do pin allowedAxioms n
  logInfo s!"CerberusHeapLang export pins: {trioExports.length} trio-exact"
  -- 2. THE EXHAUSTIVE SWEEP (theorems, bounded by the trio, every module).
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map (fun m => m.getRoot == `CerberusHeapLang)
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut swept := 0
  for n in names do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => true  -- the file being elaborated
    unless ours do continue
    let some (.thmInfo _) := env.find? n | continue
    for a in (← collectAxioms n) do
      unless allowedAxioms.contains a do
        throwError "CerberusHeapLang axiom sweep FAILED: theorem {n} carries axiom {a}, \
          outside the classical trio {allowedAxioms}. Either the proof is wrong (sorry / a \
          non-kernel method) or a trust decision is being made implicitly — the trust base \
          is the trio, exactly; any change happens in Audit.lean, same commit, with provenance."
    swept := swept + 1
  logInfo s!"CerberusHeapLang axiom sweep: every theorem bounded by the trio ({swept} swept, \
    internal details included — count informational, environment-dependent)"
  -- 3. THE BANNED-AXIOM SWEEP over every constant kind.
  let banned : List Name := [``sorryAx, ``ofReduceBool, ``ofReduceNat]
  let mut checked := 0
  for n in names do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => true
    unless ours do continue
    for a in (← collectAxioms n) do
      if banned.contains a then
        throwError "CerberusHeapLang banned-axiom sweep FAILED: constant {n} carries banned \
          axiom {a}. sorryAx / ofReduceBool / ofReduceNat are never in any boundary, for ANY \
          constant kind — a def-level hole is still a hole; remove it."
    checked := checked + 1
  logInfo s!"CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all \
    cones ({checked} constants of every kind swept, internal details included — count \
    informational, environment-dependent)"

end CerberusHeapLang.Audit
