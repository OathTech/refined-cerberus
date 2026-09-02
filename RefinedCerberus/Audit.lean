/-
RefinedCerberus.Audit — the in-build axiom-cone gate (arc-0; slimmed
back to the pre-spike shape at the 2026-08-31 restructure — the
spike now lives in `cerberus-heaplang/` as a standalone demo
development with ITS OWN audit; this root package is the future
RefinedC port's home and carries NO boundary axioms).

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
3. BANNED-AXIOM SWEEP OVER EVERY CONSTANT KIND (added at the
   2026-08-31 merge audit, finding 3): trio-bounding stays
   theorems-only (check 1), but `sorryAx`/`ofReduceBool`/
   `ofReduceNat` anywhere in the cone of ANY of our constants —
   defs included, referenced by a theorem or not — fails the build.
   Closes the def-level-sorry hole (a hole in a bare definitional
   artifact used to ride a green build).

THE DECLARED BOUNDARY: the classical trio only. There are no
project axioms; adding one requires a boundary-list entry here with
provenance (permanent-immovable or temporal-with-mover), per the
no-internal-trust-gaps discipline. (The demo package's former
temporal boundary axiom was retired upstream at the 2026-09-02
re-pin; cerberus-heaplang's Audit.lean is trio-only too — see
cerberus-heaplang/docs/2026-09-02_repin-notes.md.)

The sweep is LAST in the file by design: a constant declared after
it would dodge it, so nothing is declared below it, and this module
stays the last import of the lib root.
-/
import Lean
import RefinedCerberus.Smoke
import RefinedCerberus.SemanticsSmoke

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

-- The semantics-pin smoke (arc-0; pinned at the 2026-08-31
-- restructure): the cerberus-lean dependency resolves. The rfl
-- lemma's cone is [propext] — it enters through the STATEMENT
-- (`CerbMem.overlapping`'s definition cone), within the trio bound.
/-- info: 'RefinedCerberus.semantics_smoke' depends on axioms: [propext] -/
#guard_msgs in #print axioms RefinedCerberus.semantics_smoke

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
  -- Pass 2 (header check 3): the banned-axiom check for EVERY
  -- constant kind of our modules — not just theorems. A `sorry` (or
  -- ofReduce*) in a bare def referenced by no theorem escaped pass 1
  -- (2026-08-31 merge-audit finding 3); it fails the build here.
  let banned : List Name := [``sorryAx, ``ofReduceBool, ``ofReduceNat]
  let mut checked := 0
  for n in names do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => true  -- the file being elaborated
    unless ours do continue
    if n.isInternalDetail then continue
    let axs ← collectAxioms n
    for a in axs do
      if banned.contains a then
        throwError "RefinedCerberus banned-axiom sweep FAILED: constant {n} \
          carries banned axiom {a}. sorryAx / ofReduceBool / \
          ofReduceNat are never in any boundary, for ANY constant \
          kind — a def-level hole is still a hole; remove it (there \
          is no register route for these)."
    checked := checked + 1
  logInfo s!"RefinedCerberus banned-axiom sweep: {checked} constants of \
    every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from \
    all cones"

end RefinedCerberus.Audit
