/-
CerberusHeapLang.Audit — the in-build axiom gate of this package.
Last import of the lib root, so `lake build` elaborates it; a failure
here is a red build. Part of the trust base ([USER 2026-09-02]: the
build + this sweep + the banned-methods grep; everything else is a
speedbump).

Three checks, in order:
1. EXACT PINS over the public exports (`trioExports`,
   `boundaryExports`): each export must exist, be a theorem, and its
   transitive axiom set must EQUAL the expected set — the classical
   trio, or trio + `runEffectful` for the production-entry
   statements. Growth OR shrinkage is a build failure until the list
   is re-baselined in the same commit with the reason.
2. THE EXHAUSTIVE SWEEP: every theorem of every `CerberusHeapLang.*`
   module (module-of-origin, so top-level names cannot dodge) is
   BOUNDED by the trio, except theorems of the three production-entry
   modules (`boundaryModules`), bounded by trio + `runEffectful`.
3. THE BANNED-AXIOM SWEEP over EVERY constant kind of our modules:
   `sorryAx` / `ofReduceBool` / `ofReduceNat` anywhere in any cone
   (defs included, referenced by a theorem or not) fails the build.

THE DECLARED BOUNDARY: `runEffectful` (LemLib.lean:54), the semantics
repo's one residual axiom — TEMPORAL, mover: the cerberus-lean /
lem-lean register (its mainline retirement is the next slice's
re-pin; then the boundary here shrinks to the trio). It enters the
production-entry theorems through their STATEMENTS: they quantify
over the shipped `initial_driver_state` (Driver.lean:435), whose
`initial_core_run_state` (Core_run_aux.lean:395) draws sym_supply
through `runEffectful (CerberusFresh.freshIntIO ())`; the theorems
hold for every value of the seam (the fragment never reads it).

P3.5 ([USER 2026-09-02], docs/2026-09-02_p3.5-notes.md): the 65
`#guard_msgs in #print axioms` blocks + prose collapsed to the two
export lists below (62 names, same exact assertion each); the F-07
statement-borne origin discipline was cut (separable from the
boundary allowance; vestigial once the re-pin lands); the StmtProbe
pins went with the deleted probe.

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
import CerberusHeapLang.Round

namespace CerberusHeapLang.Audit

open Lean

/-- The classical trio — the only axioms allowed anywhere. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Trio + the declared temporal boundary axiom (header). -/
def boundaryAxioms : List Name :=
  allowedAxioms ++ [``runEffectful]

/-- EXACTLY the modules whose theorems quantify over the shipped
    `initial_driver_state`; everything else is held to the trio. -/
def boundaryModules : List Name :=
  [`CerberusHeapLang.ProdEntry, `CerberusHeapLang.ProdExhibit,
   `CerberusHeapLang.ProdLoopExhibit]

/-- THE PUBLIC EXPORTS pinned EXACTLY to the trio (in landing order;
    the README table and WALKTHROUGH §7 name these). -/
def trioExports : List Name := [
  -- spike: the base logic exhibit, the engine-facing spine
  ``CerberusHeapLang.exhibit, ``CerberusHeapLang.engine_complete,
  ``CerberusHeapLang.spike_engine_adequacy,
  ``CerberusHeapLang.semantic_triple_sound, ``CerberusHeapLang.semantic_frame,
  ``CerberusHeapLang.exhibitA_engine, ``CerberusHeapLang.exhibitB_engine,
  ``CerberusHeapLang.exhibitA_semantic, ``CerberusHeapLang.exhibitB_semantic,
  ``CerberusHeapLang.exhibitC_triple, ``CerberusHeapLang.exhibitC_semantic,
  ``CerberusHeapLang.exhibitC_engine, ``CerberusHeapLang.exhibitA_total,
  -- the jump layer + the unified relation
  ``CerberusHeapLang.stepDischarge_run, ``CerberusHeapLang.Decomp.step_factor,
  ``CerberusHeapLang.engine_step_matchU, ``CerberusHeapLang.engine_adequacyJ,
  ``CerberusHeapLang.engine_adequacyU, ``CerberusHeapLang.counter_loop_certified,
  -- the statement-stratified WP (partial) and its rules
  ``CerberusHeapLang.wps_sound, ``CerberusHeapLang.wps_seq, ``CerberusHeapLang.wps_store,
  ``CerberusHeapLang.wps_create, ``CerberusHeapLang.wps_load_at, ``CerberusHeapLang.wps_store_at,
  -- the total layer
  ``CerberusHeapLang.wpt_sound, ``CerberusHeapLang.wpt_engine_boundJ,
  ``CerberusHeapLang.wpt_strongly_normalizing, ``CerberusHeapLang.wpt_store_cell,
  -- the collapse layer (trio-exact: no shipped-state statement)
  ``CerberusHeapLang.prod_loop_done, ``CerberusHeapLang.driver2_done,
  ``CerberusHeapLang.finalize_done, ``CerberusHeapLang.loop_step_frag,
  ``CerberusHeapLang.wpt_driver_done,
  -- the exhibits
  ``CerberusHeapLang.fib_certified, ``CerberusHeapLang.fib_certified_total,
  ``CerberusHeapLang.fib_terminates, ``CerberusHeapLang.array_sum_certified,
  ``CerberusHeapLang.struct_update_certified, ``CerberusHeapLang.struct_create_store_wps,
  ``CerberusHeapLang.list_reverse_certified, ``CerberusHeapLang.list_reverse_demo,
  ``CerberusHeapLang.list_reverse_certified_total, ``CerberusHeapLang.list_reverse_terminates,
  ``CerberusHeapLang.tree_rotate_certified, ``CerberusHeapLang.tree_rotate_certified_total,
  ``CerberusHeapLang.diverge_total_unprovable,
  ``CerberusHeapLang.case_certified, ``CerberusHeapLang.wseq_certified,
  -- the engine-facing one-round relation (Round.lean)
  ``CerberusHeapLang.cerberusRound_classify, ``CerberusHeapLang.step_iff_cerberusRound,
  ``CerberusHeapLang.engine_complete_loadU, ``CerberusHeapLang.engine_complete_createU]

/-- THE PRODUCTION-ENTRY EXPORTS pinned EXACTLY to trio + `runEffectful`
    (statement-borne, header). -/
def boundaryExports : List Name := [
  ``CerberusHeapLang.prod_run_eq, ``CerberusHeapLang.sem_triple_prod,
  ``CerberusHeapLang.exhibitA_prod, ``CerberusHeapLang.fib_labeledAt_production,
  ``CerberusHeapLang.counter_loop_certified_registration, ``CerberusHeapLang.prod_run_eqJ,
  ``CerberusHeapLang.fib_certified_production,
  ``CerberusHeapLang.counter_loop_certified_production,
  ``CerberusHeapLang.list_reverse_certified_production]

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
  for n in boundaryExports do pin boundaryAxioms n
  logInfo s!"CerberusHeapLang export pins: {trioExports.length} trio-exact + \
    {boundaryExports.length} trio+runEffectful-exact"
  -- 2. THE EXHAUSTIVE SWEEP (theorems, bounded per module).
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map (fun m => m.getRoot == `CerberusHeapLang)
  let isBoundary : Array Bool := mods.map (fun m => boundaryModules.contains m)
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut swept := 0
  let mut boundarySwept := 0
  for n in names do
    let (ours, boundary) := match env.getModuleIdxFor? n with
      | some idx => (isOurs[idx.toNat]!, isBoundary[idx.toNat]!)
      | none => (true, false)  -- the file being elaborated: trio-only
    unless ours do continue
    let some (.thmInfo _) := env.find? n | continue
    if n.isInternalDetail then continue
    let allowed := if boundary then boundaryAxioms else allowedAxioms
    for a in (← collectAxioms n) do
      unless allowed.contains a do
        throwError "CerberusHeapLang axiom sweep FAILED: theorem {n} carries axiom {a}, \
          outside the declared boundary {allowed}. Either the proof is wrong (sorry / a \
          non-kernel method) or a boundary decision is being made implicitly — boundary \
          changes happen in Audit.lean, same commit, with provenance."
    swept := swept + 1
    if boundary then boundarySwept := boundarySwept + 1
  logInfo s!"CerberusHeapLang axiom sweep: {swept} theorems bounded by the trio \
    ({boundarySwept} in the production-entry modules by trio + runEffectful)"
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
