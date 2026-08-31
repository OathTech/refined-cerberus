/-
CerberusHeapLang.Audit — the in-build axiom-cone gate for this
package (the repository ROOT package's audit carries no boundary —
the boundary lives ONLY here, with the demo it serves).

This file is a member of the CerberusHeapLang lib and is its LAST
import, so `lake build` elaborates it and an edit that weakens the
epistemic position fails the build.

Checks (minimal set by rule — gates grow only for load-bearing
trust properties):

1. EXHAUSTIVE SWEEP: every theorem in a module whose name root is
   `CerberusHeapLang` (module-of-origin, not namespace — a namespace
   filter lets top-level declarations dodge) must have its
   TRANSITIVE axiom cone inside the declared boundary. `sorryAx`,
   `ofReduceBool`, `ofReduceNat` are never in the boundary.
   NB (2026-08-31 audit, F-07): this sweep is an UPPER-BOUND check
   (containment in the allowed list), not an equality check — a
   boundary-module theorem is allowed `runEffectful` whether or not
   its own cone uses it. EXACT cones are established only by the
   curated pins (check 2). Public wording everywhere:
   "exhaustively bounded; headline cones exactly pinned".
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

THE DECLARED BOUNDARY: the classical trio, plus — for EXACTLY the
two production-entry modules (ProdEntry / ProdExhibit) —
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
  DriverCollapse layer — is BOUNDED by the trio (sweep, check 1);
  the headline theorems' cones are exactly pinned below (check 2).

[USER 2026-08-31]: upstream retirement of runEffectful is planned on
the cerberus-lean/lem side — this boundary is expected to vanish at
a future pin bump; cleanup is mechanical (boundary deletion + pin
re-baseline to trio), no restatement.

The sweep is LAST in the file by design: a constant declared after
it would dodge it, so nothing is declared below it, and this module
stays the last import of the lib root.

Adjacent instruments:
- scripts/statement_census.lean (NOT a gate): reports the
  statement-surface constant partition of the pinned theorems
  (engine / spec-idiom / Iris / core — docs/WALKTHROUGH.md §5).
  Freezing its expected partitions as an in-build check 4 (with the
  plant tests the other checks get) is registered as a future gate;
  today it is run manually.
- scripts/capability_manifest.lean (A GATE, via
  scripts/test_unit.sh gate 4, Phase 0 of the foundations arc):
  generates docs/CAPABILITY_MANIFEST.md, the authoritative
  per-construct scope statement; the gate re-runs it and fails on
  drift against the committed output, and ties the README's
  certified-scope enumeration to the manifest's adequacy-exportable
  set (grep-level for Phase 0; the Phase-1 upgrade is a fully
  mechanical cone-derived table).
-/
import Lean
import CerberusHeapLang.Rules
import CerberusHeapLang.Wps
import CerberusHeapLang.Exhibit
import CerberusHeapLang.ProdExhibit
import CerberusHeapLang.LoopExhibit
import CerberusHeapLang.FibExhibit
import CerberusHeapLang.ArrayExhibit
import CerberusHeapLang.ListRevExhibit
import CerberusHeapLang.StmtProbe
import CerberusHeapLang.Phase1Probe

namespace CerberusHeapLang.Audit

open Lean

/-- The declared axiom boundary. Classical trio only (no project
    axioms exist; see header before adding anything). -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The production-entry boundary: trio + the declared temporal
    boundary axiom (provenance + mover + planned upstream
    retirement in the header). -/
def boundaryAxioms : List Name :=
  allowedAxioms ++ [``runEffectful]

/-- EXACTLY the modules whose theorems quantify over the shipped
    `initial_driver_state` and may therefore carry `runEffectful`
    (in their statements). Everything else is held to the trio. -/
def boundaryModules : List Name :=
  [`CerberusHeapLang.ProdEntry, `CerberusHeapLang.ProdExhibit]

/-! ## Curated pins -/

-- Spike slice A (2026-08-30): the acceptance exhibit — {x ↦ - ∗ y ↦ a}
-- store(x,7) {x ↦ 7 ∗ y ↦ a} via FRAME on the store small axiom —
-- carries exactly the classical trio (through iris-lean). Proved over
-- Step; engine certification of Step is slice B (artifact 4).
/--
info: 'CerberusHeapLang.exhibit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.exhibit

-- Spike slice B (2026-08-30): the engine-facing spine, exact trio each.
-- engine_complete = artifact 4 (Step certified against step_ctx +
-- the Driver.lean:273 discharge, per-construct); spike_engine_adequacy
-- = the engine-only adequacy statement; the exhibits are the
-- operator's package re-concluded at the engine level, incl. the
-- recon probe as a theorem (exhibitA_terminates).
/--
info: 'CerberusHeapLang.engine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.engine_complete

/--
info: 'CerberusHeapLang.spike_engine_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.spike_engine_adequacy

-- Phase-2 S3 (2026-08-31): the jump layer's headline cones, exact
-- trio each — the context-discard certification (stepDischarge_run),
-- the factor theorem with the jump disjunct, the step-match
-- completeness at the jump profile, the Löb-tied collapse with
-- blockSpecs, and THE END-TO-END CERTIFIED LOOP (driveJ conclusion,
-- engine vocabulary only).
/--
info: 'CerberusHeapLang.stepDischarge_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.stepDischarge_run

/--
info: 'CerberusHeapLang.DecompJ.step_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.DecompJ.step_factor

/--
info: 'CerberusHeapLang.engine_step_matchJ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.engine_step_matchJ

/--
info: 'CerberusHeapLang.wps_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wps_sound

/--
info: 'CerberusHeapLang.engine_adequacyJ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.engine_adequacyJ

/--
info: 'CerberusHeapLang.counter_loop_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.counter_loop_certified

/--
info: 'CerberusHeapLang.exhibitA_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.exhibitA_engine

/--
info: 'CerberusHeapLang.exhibitB_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.exhibitB_engine

/--
info: 'CerberusHeapLang.exhibitA_terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.exhibitA_terminates

-- The exported semantic face ([USER 2026-08-30] final form): the
-- configuration-level triple soundness + the semantic frame rule.
/--
info: 'CerberusHeapLang.semantic_triple_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.semantic_triple_sound

/--
info: 'CerberusHeapLang.semantic_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.semantic_frame

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
info: 'CerberusHeapLang.exhibitC_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.exhibitC_triple

/--
info: 'CerberusHeapLang.exhibitC_semantic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.exhibitC_semantic

/--
info: 'CerberusHeapLang.exhibitC_engine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.exhibitC_engine

-- Extension D (2026-08-30): the production-entry theorems. The
-- COLLAPSE layer (DriverCollapse — the scheduler/ND/readout
-- equations against the driver's own round functions) is TRIO-EXACT;
-- the ENTRY theorems (ProdEntry/ProdExhibit — statements quantify
-- over the shipped `initial_driver_state`) carry exactly
-- trio + runEffectful, the declared temporal boundary (header:
-- provenance + mover — the semantics repo's register owns it).
/--
info: 'CerberusHeapLang.prod_loop_done' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.prod_loop_done

/--
info: 'CerberusHeapLang.driver2_done' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.driver2_done

/--
info: 'CerberusHeapLang.finalize_done' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.finalize_done

/--
info: 'CerberusHeapLang.prod_run_eq' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.prod_run_eq

/--
info: 'CerberusHeapLang.sem_triple_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.sem_triple_prod

/--
info: 'CerberusHeapLang.exhibitA_prod' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.exhibitA_prod

-- S0 jump-kernel probe (2026-08-31, arc plan §Phase 1): the
-- statement-stratified WP over the TOY (StmtProbe — no engine
-- imports, no boundary). Pinned: the jump-aware sequencing lemma
-- (the readiness R1 obligation), the Löb-tied elimination into the
-- base WP (the donor wps_block_rec analog), and the toy-loop
-- demonstration (back-edge + per-label invariant + live env).
-- Each cone exactly the trio.
/--
info: 'CerberusHeapLang.StmtProbe.wps_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.StmtProbe.wps_seq

/--
info: 'CerberusHeapLang.StmtProbe.wps_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.StmtProbe.wps_sound

/--
info: 'CerberusHeapLang.StmtProbe.demo_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.StmtProbe.demo_loop

-- Phase-1 S2 (2026-08-31, two-phase arc plan): the statement-
-- stratified WP over the REAL fragment (Wps.lean) — the label-context
-- judgment as a package-local guarded fixpoint (public iris-lean
-- Banach API; jump clause deliberately absent, S3's — module header).
-- Pinned: the sequencing rule (the jump-aware statement shape over
-- Core), the collapse into the base WP (the sole adequacy interface),
-- and the store small axiom at the stratum. Each cone exactly the
-- trio.
/--
info: 'CerberusHeapLang.wps_seq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wps_seq

/--
info: 'CerberusHeapLang.wps_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wps_sound

/--
info: 'CerberusHeapLang.wps_store' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wps_store

-- Phase-2 S4 (2026-08-31): ACCEPTANCE EXHIBIT 1 — fib end-to-end
-- (the iterative two-accumulator loop through blockSpecs_intro with
-- the data-dependent invariant a = fib i ∧ b = fib (i+1), the S4
-- PURE exit, the env-map seam's SymFrame invariant; driveJ
-- conclusion, engine vocabulary only; delivered value = the
-- Lean-side fibSpec). Cone exactly the trio.
/--
info: 'CerberusHeapLang.fib_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.fib_certified

-- Phase-2 S4 (2026-08-31): ACCEPTANCE EXHIBIT 2 — array-sum
-- end-to-end (real pointer arithmetic via the certified
-- PEarray_shift arm, the ACTION_EVAL load at a symbol operand, the
-- interior-load axiom over the seeded array allocation, the
-- Specified-binder unwrap, the index-partitioned invariant;
-- conclusion: value = vs.sum AND the array preserved). Cone exactly
-- the trio.
/--
info: 'CerberusHeapLang.array_sum_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.array_sum_certified

-- Phase-2 S4 (2026-08-31): the OPERATIONAL ENGINE THEOREM for fib
-- (reclassified per the 2026-08-31 audit, F-02): unconditional at
-- the drive lane — the concrete step bound 2n+4 discharges every
-- fuel hypothesis; driveJ DELIVERS fib n. Proved by direct
-- operational induction, NOT by the logic (no total WP exists yet —
-- Phase 3); and the PRODUCTION REGISTRATION TIE (LabeledAt derived
-- from collect_labeled_continuations_NEW at the shipped initial run
-- state — the boundary statement carries the declared temporal
-- seam) with the counter loop re-exported at the derived tie.
/--
info: 'CerberusHeapLang.fib_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.fib_certified_total

/--
info: 'CerberusHeapLang.fib_labeledAt_production' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.fib_labeledAt_production

/--
info: 'CerberusHeapLang.counter_loop_certified_production' depends on axioms: [propext,
 runEffectful,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.counter_loop_certified_production

-- List-reverse arc phase A (2026-08-31): THE CANONICAL EXHIBIT —
-- in-place list reversal over one-allocation two-field nodes, the
-- honest null encoding + the engine's own PtrEq memop as the null
-- test, interior next-field loads AND stores by in-allocation
-- arithmetic, `isList` by structural recursion, the textbook
-- blockSpecs_intro proof, certified through the engine lane
-- (driveJ); conclusion: never killed/stuck, any delivered value is
-- a pointer whose FINAL-heap chain is xs.reverse. Plus the concrete
-- seeded 3-node demonstration. Cones exactly the trio.
/--
info: 'CerberusHeapLang.list_reverse_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.list_reverse_certified

/--
info: 'CerberusHeapLang.list_reverse_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.list_reverse_demo

/-! ## The exhaustive sweep (LAST — nothing declared below) -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map (fun m => m.getRoot == `CerberusHeapLang)
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
        throwError "CerberusHeapLang axiom sweep FAILED: theorem {n} \
          carries axiom {a}, outside the declared boundary \
          {allowed}. Either the proof is wrong (sorry / a \
          non-kernel method) or a boundary decision is being made \
          implicitly — boundary changes happen in Audit.lean, same \
          commit, with provenance."
    swept := swept + 1
    if boundary then boundarySwept := boundarySwept + 1
  logInfo s!"CerberusHeapLang axiom sweep: {swept} theorems BOUNDED by the \
    declared upper bounds ({boundarySwept} in the production-entry \
    boundary modules, bounded by trio + runEffectful; all others \
    bounded by the trio; exact cones pinned only for the curated \
    headline list above)"
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
        throwError "CerberusHeapLang banned-axiom sweep FAILED: constant {n} \
          carries banned axiom {a}. sorryAx / ofReduceBool / \
          ofReduceNat are never in any boundary, for ANY constant \
          kind — a def-level hole is still a hole; remove it (there \
          is no register route for these)."
    checked := checked + 1
  logInfo s!"CerberusHeapLang banned-axiom sweep: {checked} constants of \
    every kind checked; sorryAx/ofReduceBool/ofReduceNat absent from \
    all cones"

end CerberusHeapLang.Audit
