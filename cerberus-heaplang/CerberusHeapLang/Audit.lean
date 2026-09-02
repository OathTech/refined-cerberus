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
   module (module-of-origin, so top-level names cannot dodge) is
   BOUNDED by the trio — no module is allowed anything else.
3. THE BANNED-AXIOM SWEEP over EVERY constant kind of our modules:
   `sorryAx` / `ofReduceBool` / `ofReduceNat` anywhere in any cone
   (defs included, referenced by a theorem or not) fails the build.

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
import CerberusHeapLang.Examples.ReadinessSmoke
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
  ``CerberusHeapLang.stepDischarge_run, ``CerberusHeapLang.Decomp.step_factor,
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
  -- the engine-facing one-round relation (Round.lean)
  ``CerberusHeapLang.cerberusRound_classify, ``CerberusHeapLang.step_iff_cerberusRound,
  ``CerberusHeapLang.engine_complete_loadU, ``CerberusHeapLang.engine_complete_createU,
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
  -- triple whose pre is footprint cells ∗ `allocCap reqs` projects to
  -- `MemTripleU_alloc` (launch premise `LaunchCoh`); `MemTripleU`
  -- implies it at every plan
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
  ``CerberusHeapLang.alloc_create_launch_smoke]

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
    if n.isInternalDetail then continue
    for a in (← collectAxioms n) do
      unless allowedAxioms.contains a do
        throwError "CerberusHeapLang axiom sweep FAILED: theorem {n} carries axiom {a}, \
          outside the classical trio {allowedAxioms}. Either the proof is wrong (sorry / a \
          non-kernel method) or a trust decision is being made implicitly — the trust base \
          is the trio, exactly; any change happens in Audit.lean, same commit, with provenance."
    swept := swept + 1
  logInfo s!"CerberusHeapLang axiom sweep: {swept} theorems bounded by the trio"
  -- 3. THE BANNED-AXIOM SWEEP over every constant kind.
  let banned : List Name := [``sorryAx, ``ofReduceBool, ``ofReduceNat]
  let mut checked := 0
  for n in names do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => true
    unless ours do continue
    if n.isInternalDetail then continue
    for a in (← collectAxioms n) do
      if banned.contains a then
        throwError "CerberusHeapLang banned-axiom sweep FAILED: constant {n} carries banned \
          axiom {a}. sorryAx / ofReduceBool / ofReduceNat are never in any boundary, for ANY \
          constant kind — a def-level hole is still a hole; remove it."
    checked := checked + 1
  logInfo s!"CerberusHeapLang banned-axiom sweep: {checked} constants of every kind checked; \
    sorryAx/ofReduceBool/ofReduceNat absent from all cones"

end CerberusHeapLang.Audit
