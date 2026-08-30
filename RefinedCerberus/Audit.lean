/-
RefinedCerberus.Audit — the in-build axiom-cone gate (arc-0).

Pattern: the predecessor repo's in-build audit (cerberus-lean park
branch, relsem/RelSem/Audit.lean), itself from golean's
proofs/Audit.lean. This file is a member of the RefinedCerberus lib
and is its LAST import, so `lake build` elaborates it and an edit
that weakens the epistemic position fails the build.

Checks (minimal arc-0 set, per the blessed rules §5 —
grow only for load-bearing trust properties):

1. EXHAUSTIVE SWEEP: every theorem in a module whose name root is
   `RefinedCerberus` (module-of-origin, not namespace — a namespace
   filter lets top-level declarations dodge) must have its
   TRANSITIVE axiom cone inside the declared boundary. `sorryAx`,
   `ofReduceBool`, `ofReduceNat` are never in the boundary.
2. CURATED PINS: exact axiom sets of load-bearing theorems via
   `#guard_msgs in #print axioms` — growth is a build failure until
   deliberately re-baselined in the same commit with the reason.

THE DECLARED BOUNDARY: the classical trio, plus — for EXACTLY the
two production-entry modules (Spike.ProdEntry / Spike.ProdExhibit) —
the one declared boundary axiom `runEffectful` (LemLib.lean:54).
Boundary entry provenance (Extension D, 2026-08-30):
- TEMPORAL, with a named mover: `runEffectful` is the semantics
  repo's one residual axiom (cerberus-lean lean_frontend/TODO.md —
  "the residual is runEffectful (LemLib, temporal — its deletion is
  ...)"; DESIGN.md §the axiom story). Its removal is owned by the
  cerberus-lean/lem-lean register, not here; when it lands, the
  boundary list here shrinks back to the trio with no statement
  change on our side.
- WHY it enters: the production-entry theorems quantify over the
  SHIPPED initial state, `initial_driver_state` (Driver.lean:435),
  whose `initial_core_run_state` (Core_run_aux.lean:395) draws
  sym_supply through `runEffectful (CerberusFresh.freshIntIO ())`.
  The axiom enters through the STATEMENT (the constant's definition
  cone), not through any proof step; the theorems hold for every
  value of the seam (the fragment never reads sym_supply — the D14
  partition). Every other module — including the whole
  DriverCollapse layer — remains trio-exact, pinned below.

The sweep is LAST in the file by design: a constant declared after
it would dodge it, so nothing is declared below it, and this module
stays the last import of the lib root.
-/
import Lean
import RefinedCerberus.Smoke
import RefinedCerberus.SemanticsSmoke
import RefinedCerberus.Spike.Rules
import RefinedCerberus.Spike.Exhibit
import RefinedCerberus.Spike.ProdExhibit

namespace RefinedCerberus.Audit

open Lean

/-- The declared axiom boundary. Classical trio only (no project
    axioms exist; see header before adding anything). -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The production-entry boundary: trio + the declared temporal
    boundary axiom (provenance + mover in the header). -/
def boundaryAxioms : List Name :=
  allowedAxioms ++ [``runEffectful]

/-- EXACTLY the modules whose theorems quantify over the shipped
    `initial_driver_state` and may therefore carry `runEffectful`
    (in their statements). Everything else is held to the trio. -/
def boundaryModules : List Name :=
  [`RefinedCerberus.Spike.ProdEntry, `RefinedCerberus.Spike.ProdExhibit]

/-! ## Curated pins -/

-- Re-baselined at first build (arc-0): the BI proof-mode smoke
-- lemma's cone is EMPTY — strictly stronger than the trio bound.
/-- info: 'RefinedCerberus.smoke' does not depend on any axioms -/
#guard_msgs in #print axioms RefinedCerberus.smoke

-- Spike slice A (2026-08-30): the acceptance exhibit — {x ↦ - ∗ y ↦ a}
-- store(x,7) {x ↦ 7 ∗ y ↦ a} via FRAME on the store small axiom —
-- carries exactly the classical trio (through iris-lean). Proved over
-- Step; engine certification of Step is slice B (artifact 4).
/--
info: 'RefinedCerberus.Spike.exhibit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.exhibit

-- Spike slice B (2026-08-30): the engine-facing spine, exact trio each.
-- engine_complete = artifact 4 (Step certified against step_ctx +
-- the Driver.lean:273 discharge, per-construct); spike_engine_adequacy
-- = the engine-only adequacy statement; the exhibits are the
-- operator's package re-concluded at the engine level, incl. the
-- recon probe as a theorem (exhibitA_terminates).
/--
info: 'RefinedCerberus.Spike.engine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.engine_complete

/--
info: 'RefinedCerberus.Spike.spike_engine_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.spike_engine_adequacy

/--
info: 'RefinedCerberus.Spike.exhibitA_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.exhibitA_engine

/--
info: 'RefinedCerberus.Spike.exhibitB_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.exhibitB_engine

/--
info: 'RefinedCerberus.Spike.exhibitA_terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.exhibitA_terminates

-- The exported semantic face ([USER 2026-08-30] final form): the
-- configuration-level triple soundness + the semantic frame rule.
/--
info: 'RefinedCerberus.Spike.semantic_triple_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.semantic_triple_sound

/--
info: 'RefinedCerberus.Spike.semantic_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.semantic_frame

-- Spike exhibit C (2026-08-30, [USER] task): disjoint sequential
-- stores — `lets _ = store(x,5) in store(y,6)` gives non-conflicting
-- updates. exhibitC_triple is derived PURELY COMPOSITIONALLY (the
-- store small axiom framed per leg + triple_seq; no
-- Step/storeM/state_interp unfolding); exhibitC_semantic exports it
-- over every splitting engine configuration (arbitrary rest verbatim);
-- exhibitC_engine instantiates at the allocateObject-seeded two-cell
-- state. Sweep count re-baselined 196 → 209 in this commit: the 13
-- new exhibit-C theorems (values/encodings ×4, the triple, fragC,
-- footprint plumbing ×4, provenC, the semantic export, the engine
-- instance), each cone exactly the trio.
/--
info: 'RefinedCerberus.Spike.exhibitC_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.exhibitC_triple

/--
info: 'RefinedCerberus.Spike.exhibitC_semantic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.exhibitC_semantic

/--
info: 'RefinedCerberus.Spike.exhibitC_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.exhibitC_engine

-- Extension D (2026-08-30): the production-entry theorems. The
-- COLLAPSE layer (DriverCollapse — the scheduler/ND/readout
-- equations against the driver's own round functions) is TRIO-EXACT;
-- the ENTRY theorems (ProdEntry/ProdExhibit — statements quantify
-- over the shipped `initial_driver_state`) carry exactly
-- trio + runEffectful, the declared temporal boundary (header:
-- provenance + mover — the semantics repo's register owns it).
/--
info: 'RefinedCerberus.Spike.prod_loop_done' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.prod_loop_done

/--
info: 'RefinedCerberus.Spike.driver2_done' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.driver2_done

/--
info: 'RefinedCerberus.Spike.finalize_done' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.finalize_done

/--
info: 'RefinedCerberus.Spike.prod_run_eq' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.prod_run_eq

/--
info: 'RefinedCerberus.Spike.sem_triple_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.sem_triple_prod

/--
info: 'RefinedCerberus.Spike.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms RefinedCerberus.Spike.exhibitA_prod

/-! ## The exhaustive sweep (LAST — nothing declared below) -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map (fun m => m.getRoot == `RefinedCerberus)
  let isBoundary : Array Bool := mods.map (fun m => boundaryModules.contains m)
  let names : Array Name := env.constants.fold
    (fun acc n _ => acc.push n) #[]
  let mut swept := 0
  let mut boundarySwept := 0
  for n in names do
    let (ours, boundary) := match env.getModuleIdxFor? n with
      | some idx => (isOurs[idx.toNat]!, isBoundary[idx.toNat]!)
      | none => (true, false)  -- the file being elaborated: trio-only
    unless ours do continue
    unless env.find? n matches some (.thmInfo _) do continue
    if n.isInternalDetail then continue
    let allowed := if boundary then boundaryAxioms else allowedAxioms
    let axs ← collectAxioms n
    for a in axs do
      unless allowed.contains a do
        throwError "RefinedCerberus axiom sweep FAILED: theorem {n} \
          carries axiom {a}, outside the declared boundary \
          {allowed}. Either the proof is wrong (sorry / a \
          non-kernel method) or a boundary decision is being made \
          implicitly — boundary changes happen in Audit.lean, same \
          commit, with provenance."
    swept := swept + 1
    if boundary then boundarySwept := boundarySwept + 1
  logInfo s!"RefinedCerberus axiom sweep: {swept} theorems within the \
    declared boundary ({boundarySwept} in the production-entry \
    boundary modules, trio + runEffectful; all others trio-exact)"

end RefinedCerberus.Audit
