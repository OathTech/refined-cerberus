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
quantify over the supply — the fragment never reads it. The nine
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
import CerberusHeapLang.Examples.ReadinessSmoke
import CerberusHeapLang.Examples.MirrorCoverage
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
  ``CerberusHeapLang.exhibitC_engine, ``CerberusHeapLang.exhibitA_total,
  -- the jump layer + the unified relation
  ``CerberusHeapLang.Decomp.step_factor,
  ``CerberusHeapLang.engine_step_matchU,
  ``CerberusHeapLang.engine_adequacyU, ``CerberusHeapLang.counter_loop_certified,
  -- the statement-stratified WP (partial) and its rules
  ``CerberusHeapLang.wps_sound, ``CerberusHeapLang.wps_seq, ``CerberusHeapLang.wps_store,
  ``CerberusHeapLang.wps_create, ``CerberusHeapLang.wps_load_at, ``CerberusHeapLang.wps_store_at,
  -- the total layer
  ``CerberusHeapLang.wpt_sound, ``CerberusHeapLang.wpt_engine_boundU,
  ``CerberusHeapLang.wpt_engine_boundU_alloc, ``CerberusHeapLang.wpt_store,
  -- the collapse layer (trio-exact: no shipped-state statement)
  ``CerberusHeapLang.driver2_done,
  ``CerberusHeapLang.finalize_done, ``CerberusHeapLang.loop_step_frag,
  ``CerberusHeapLang.wpt_driver_done,
  -- the exhibits
  ``CerberusHeapLang.fib_certified, ``CerberusHeapLang.fib_certified_total,
  ``CerberusHeapLang.array_sum_certified,
  ``CerberusHeapLang.struct_update_certified, ``CerberusHeapLang.struct_create_store_wps,
  ``CerberusHeapLang.list_reverse_certified, ``CerberusHeapLang.list_reverse_demo,
  ``CerberusHeapLang.list_reverse_certified_total,
  ``CerberusHeapLang.tree_rotate_certified, ``CerberusHeapLang.tree_rotate_certified_total,
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
  -- (`BareHead.not_annot` and `Decomp.get_ctx_rebuild_action` have
  -- SUB-trio cones — [propext] / [Quot.sound, propext] — so they cannot
  -- sit in an EXACT-trio pin list; the exhaustive sweep bounds them)
  ``CerberusHeapLang.BareHead.step,
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
  ``CerberusHeapLang.counter_loop_certified_registration, ``CerberusHeapLang.prod_run_eqJ,
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
  ``CerberusHeapLang.semantic_triple_soundU, ``CerberusHeapLang.semantic_frameU,
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
  -- `project_triple_pure` (+ `_alloc`) — a boring `MemTripleU` for a
  -- pure ψ, no Iris in the conclusion; `project_triple` is the
  -- strongest-post form beneath it
  ``CerberusHeapLang.project_triple_pure, ``CerberusHeapLang.project_triple_pure_alloc,
  ``CerberusHeapLang.project_triple, ``CerberusHeapLang.SemTripleU_iff_Mem,
  ``CerberusHeapLang.pure_consequence, ``CerberusHeapLang.sep_consequence,
  ``CerberusHeapLang.or_consequence, ``CerberusHeapLang.exists_consequence,
  ``CerberusHeapLang.cellOwn_consequence, ``CerberusHeapLang.pointsToCell_consequence,
  ``CerberusHeapLang.cellsOwn_consequence, ``CerberusHeapLang.cells_consequence,
  -- P6.1 (fresh-eyes review H-1): the ALLOCATING projection — an Iris
  -- triple whose pre is footprint cells ∗ `allocBudget B` (K2.5; formerly
  -- the plan `allocCap reqs`) projects to `MemTripleU_alloc` (launch
  -- premise `LaunchCoh`); `MemTripleU` implies it at every budget
  ``CerberusHeapLang.project_triple_alloc,
  ``CerberusHeapLang.MemTripleU_alloc_of_MemTripleU,
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
  ``CerberusHeapLang.alloc_create_launch_smoke,
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
  ``CerberusHeapLang.alloc_create_kill_wps, ``CerberusHeapLang.kill_launch_smoke,
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
  ``CerberusHeapLang.alloc_free_wps, ``CerberusHeapLang.free_launch_smoke,
  -- kill/free arc K4 (2026-09-03): THE EXHIBITS — dispose-a-list over
  -- created nodes (DisposeExhibit.lean): the statement judgments at both
  -- strata (dead-list and textbook forms; framed forms), the block
  -- specifications, the readout, the `driveU` total equation (PROVISIONAL)
  -- and the PRODUCTION statement over the shipped pipeline; the generic
  -- build-prefix lemma the production reuses and its registration tie.
  ``CerberusHeapLang.dl_wps, ``CerberusHeapLang.dl_wps_emp, ``CerberusHeapLang.dl_wps_frame,
  ``CerberusHeapLang.dl_blockSpecs, ``CerberusHeapLang.dl_wpt, ``CerberusHeapLang.dl_wpt_frame,
  ``CerberusHeapLang.dl_blockSpecsT, ``CerberusHeapLang.dlPost_readout,
  ``CerberusHeapLang.dispose_list_certified_total,
  ``CerberusHeapLang.lrProdPrefix_wpt, ``CerberusHeapLang.dlProd_wpt,
  ``CerberusHeapLang.dlProd_blockSpecsT, ``CerberusHeapLang.dlProd_labeledAt,
  ``CerberusHeapLang.dispose_list_certified_production,
  -- K4, the second exhibit — n regions from one linear budget
  -- (RegionLoopExhibit.lean): the budget as a loop invariant split per
  -- iteration (`allocBudget_split`), spent by `wps_alloc`/`wpt_alloc`,
  -- the regions returned by `wps_free_emp`/`wpt_free_emp`; both strata,
  -- the block specifications, the `driveU` total equation (PROVISIONAL)
  -- under `LaunchCoh`, and the PRODUCTION statement. (At K4 the malloc'd
  -- LINKED list was not statable — no load/store rule over `regionOwn`;
  -- K5 added the region access rules and the list is pinned below,
  -- `malloc_list_certified_production`.)
  ``CerberusHeapLang.rl_wps, ``CerberusHeapLang.rl_wpt,
  ``CerberusHeapLang.rl_blockSpecs, ``CerberusHeapLang.rl_blockSpecsT,
  ``CerberusHeapLang.region_loop_certified_total, ``CerberusHeapLang.rl_labeledAt,
  ``CerberusHeapLang.region_loop_certified_production,
  -- kill/free arc K5 (2026-09-03): THE REGION ACCESS RULES — the typed
  -- region view's laws (the untyped-view bridge, typed split/join, the
  -- carve/uncarve of whole-region ownership), the two atomic specs
  -- `regionLoadAt_atomic`/`regionStoreAt_atomic` (over `loadM_live`/
  -- `storeM_live` at `regionCell`), their wps/wpt faces over the typed
  -- view and over `regionOwn`; the public dead readouts (K4 audit N-1);
  -- and THE MALLOC'D LINKED LIST exhibit (MallocListExhibit.lean): both
  -- strata, the block specifications, the readout, the `driveU` total
  -- equation (PROVISIONAL), the registration tie and the PRODUCTION
  -- statement. (`typedRegionView_iff` is `.rfl`; measured trio, unpinned
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
  ``CerberusHeapLang.mlPost_readout, ``CerberusHeapLang.malloc_list_certified_total,
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
  ``CerberusHeapLang.smoke_call_round, ``CerberusHeapLang.smoke_ret_round]

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
