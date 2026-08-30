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

THE DECLARED BOUNDARY: the classical trio only. There are no
project axioms; adding one requires a boundary-list entry here with
provenance (permanent-immovable or temporal-with-mover), per the
no-internal-trust-gaps discipline.

The sweep is LAST in the file by design: a constant declared after
it would dodge it, so nothing is declared below it, and this module
stays the last import of the lib root.
-/
import Lean
import RefinedCerberus.Smoke
import RefinedCerberus.SemanticsSmoke
import RefinedCerberus.Spike.Rules
import RefinedCerberus.Spike.Exhibit

namespace RefinedCerberus.Audit

open Lean

/-- The declared axiom boundary. Classical trio only (no project
    axioms exist; see header before adding anything). -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

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

/-! ## The exhaustive sweep (LAST — nothing declared below) -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map (fun m => m.getRoot == `RefinedCerberus)
  let names : Array Name := env.constants.fold
    (fun acc n _ => acc.push n) #[]
  let mut swept := 0
  for n in names do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => true  -- the file being elaborated
    unless ours do continue
    unless env.find? n matches some (.thmInfo _) do continue
    if n.isInternalDetail then continue
    let axs ← collectAxioms n
    for a in axs do
      unless allowedAxioms.contains a do
        throwError "RefinedCerberus axiom sweep FAILED: theorem {n} \
          carries axiom {a}, outside the declared boundary \
          {allowedAxioms}. Either the proof is wrong (sorry / a \
          non-kernel method) or a boundary decision is being made \
          implicitly — boundary changes happen in Audit.lean, same \
          commit, with provenance."
    swept := swept + 1
  logInfo s!"RefinedCerberus axiom sweep: {swept} theorems, all cones \
    within the classical trio"

end RefinedCerberus.Audit
