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
   F-07 STRENGTHENING (Phase 5, closing the 2026-08-31 audit's
   upper-bound gap): boundary-module theorems additionally pass the
   ORIGIN DISCIPLINE — whenever `runEffectful` is in a theorem's
   cone, it must be reachable through the STATEMENT's constants
   (the shipped initial state); a proof-borne boundary axiom fails
   the build. Non-boundary theorems are trio-bounded; boundary
   theorems are therefore exact-by-construction (trio +
   runEffectful iff statement-borne). Public wording:
   "exhaustively bounded with statement-borne boundary origin;
   headline cones additionally pinned".
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
production-entry modules (ProdEntry / ProdExhibit /
ProdLoopExhibit, the statement-carrying set) —
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
STATUS (orchestrator-checked 2026-09-01, Phase 5 close): the
upstream retirement has NOT landed (lem-lean mainline LemLib.lean:54
still carries the axiom) — the Phase-5 boundary endgame therefore
takes the arc plan's documented FALLBACK: the allowance narrowed to
the minimal statement-carrying module set (the three Prod*Exhibit/
Entry modules; the whole collapse machinery is trio-only) and every
boundary cone exact via the origin discipline (check 1). The
retirement remains the registered mover.

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
import CerberusHeapLang.StmtProbe

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
    (in their statements). Everything else is held to the trio.
    Phase 5 adds ProdLoopExhibit (the production LOOP equations);
    the whole collapse machinery (DriverCollapse, ProdLoop) stays
    OUTSIDE the boundary. -/
def boundaryModules : List Name :=
  [`CerberusHeapLang.ProdEntry, `CerberusHeapLang.ProdExhibit,
   `CerberusHeapLang.ProdLoopExhibit]

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

-- Phase-2 S3 (2026-08-31; S1b: re-homed at the unified relation —
-- the factor theorem and step-match now speak the one Decomp/Frag
-- cone at any MachineCtx): the jump layer's headline cones, exact
-- trio each — the context-discard certification (stepDischarge_run),
-- the factor theorem with the jump disjunct, the step-match
-- completeness over the full cone, the Löb-tied collapse with
-- blockSpecs, and THE END-TO-END CERTIFIED LOOP (driveJ conclusion,
-- engine vocabulary only).
/--
info: 'CerberusHeapLang.stepDischarge_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.stepDischarge_run

/--
info: 'CerberusHeapLang.Decomp.step_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.Decomp.step_factor

-- S1b re-baseline (same commit, cone unification): the step-match
-- completeness is the UNIFIED `engine_step_matchU` (full cone, any
-- MachineCtx) — the J-profile theorem is subsumed (design record §8).
/--
info: 'CerberusHeapLang.engine_step_matchU' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.engine_step_matchU

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

-- fib's TOTAL equation (statement unchanged since Phase-2 S4;
-- foundations Phase 3 re-derived its PROOF as a corollary of the
-- total statement judgment through the generic measure→drive-fuel
-- simulation — the operational induction is retired, audit F-02);
-- and the PRODUCTION REGISTRATION TIE (LabeledAt derived from
-- collect_labeled_continuations_NEW at the shipped initial run
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
info: 'CerberusHeapLang.counter_loop_certified_registration' depends on axioms: [propext,
 runEffectful,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.counter_loop_certified_registration

-- Foundations Phase 5 (2026-09-01): THE LOOP PRODUCTION COLLAPSE
-- (audit F-05 closed) — the proc-carrying, populated-label scheduler
-- collapse. TRIO-EXACT: the driver step-match (one production round
-- per mirror step, jump rounds included, over the full Frag cone)
-- and the total-judgment driver simulation (the wpt_drive_aux analog
-- at the driver's own loop). The boundary carries only the SHIPPED
-- pipeline statements (ProdLoopExhibit): the generic runND equation
-- for registered-loop programs and the fib production theorem, each
-- exactly trio + runEffectful (statement-borne, as everywhere in the
-- boundary).
/--
info: 'CerberusHeapLang.loop_step_frag' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.loop_step_frag

/--
info: 'CerberusHeapLang.wpt_driver_done' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wpt_driver_done

/--
info: 'CerberusHeapLang.prod_run_eqJ' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.prod_run_eqJ

/--
info: 'CerberusHeapLang.fib_certified_production' depends on axioms: [propext, runEffectful, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.fib_certified_production

-- Phase 5 (2026-09-01, continued): the remaining loop production
-- exports — the SELF-CONTAINED counter (engine-created cell) and the
-- SELF-CONTAINED two-node list reversal (engine-built chain), each on
-- the shipped pipeline from the cold start; and the new whole-cell
-- total store rule (trio).
/--
info: 'CerberusHeapLang.wpt_store_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wpt_store_cell

/--
info: 'CerberusHeapLang.counter_loop_certified_production' depends on axioms: [propext,
 runEffectful,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.counter_loop_certified_production

/--
info: 'CerberusHeapLang.list_reverse_certified_production' depends on axioms: [propext,
 runEffectful,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.list_reverse_certified_production

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

-- Foundations Phase 2 (2026-09-01): the generic memory layer's
-- headline pins — the allocation rule (D26 retired: create through
-- the allocator-cursor resource), the generic typed-subrange rules,
-- and the FRESH-CLIENT acceptance theorem (two-field struct update,
-- end-to-end, zero core-logic edits). Cones exactly the trio.
/--
info: 'CerberusHeapLang.wps_create' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wps_create

/--
info: 'CerberusHeapLang.wps_load_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wps_load_at

/--
info: 'CerberusHeapLang.wps_store_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wps_store_at

/--
info: 'CerberusHeapLang.struct_update_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.struct_update_certified

/--
info: 'CerberusHeapLang.struct_create_store_wps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.struct_create_store_wps

-- Foundations Phase 3 (2026-09-01): THE TOTAL LAYER (audit F-02
-- remediation) — the total statement judgment's collapse into the
-- pinned Iris TotalWeakestPre (wpt_sound: TWP gains its consumer),
-- the generic measure→drive-fuel simulation at the jump profile
-- (wpt_engine_boundJ: the cost half), and Iris TotalAdequacy
-- consumed as-is over the unified relation
-- (wpt_strongly_normalizing: the logical half). Cones exactly the
-- trio.
/--
info: 'CerberusHeapLang.wpt_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wpt_sound

/--
info: 'CerberusHeapLang.wpt_engine_boundJ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wpt_engine_boundJ

/--
info: 'CerberusHeapLang.wpt_strongly_normalizing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.wpt_strongly_normalizing

-- Foundations Phase 3 (2026-09-01): THE TOTAL CLIENTS — fib's
-- logical termination (Iris TotalAdequacy consumed as-is), the
-- list-reverse TOTAL equation at the DERIVED bound 13·|xs|+7 (the
-- registered residual closes) + its termination, and THE NEGATIVE
-- TEST (the self-jump loop's total derivation is FALSE — the
-- audit's "removing the decrease makes a looping example
-- unprovable" criterion in semantic form). Cones exactly the trio.
/--
info: 'CerberusHeapLang.fib_terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.fib_terminates

/--
info: 'CerberusHeapLang.list_reverse_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.list_reverse_certified_total

/--
info: 'CerberusHeapLang.list_reverse_terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.list_reverse_terminates

-- Foundations Phase 4 (2026-09-01): THE FLAGSHIPS AT FULL STRENGTH
-- (audit F-06) — identity-indexed same-footprint in-place reversal
-- with the frame quantifier (the restated list flagships above keep
-- their names; their new statements ride the same pins) and THE
-- SECOND CLIENT: binary-tree rotation through the generic layer,
-- zero core edits, partial + unconditional-total. Cones exactly the
-- trio.
/--
info: 'CerberusHeapLang.tree_rotate_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.tree_rotate_certified

/--
info: 'CerberusHeapLang.tree_rotate_certified_total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.tree_rotate_certified_total

/--
info: 'CerberusHeapLang.diverge_total_unprovable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CerberusHeapLang.diverge_total_unprovable

/-! ## The exhaustive sweep (LAST — nothing declared below except the
sweep's own reachability helper, declared just above it) -/

open Lean in
/-- Memoized reachability of an axiom constant through
    definitions/statements (types AND bodies) — the sweep's
    origin-discipline instrument (F-07 strengthening). Cycle-guarded
    (recursors/mutual blocks): a name is pre-marked `false` while its
    dependencies are explored. -/
partial def carriesAx (env : Environment) (ax : Name) (n : Name) :
    StateM (Std.HashMap Name Bool) Bool := do
  if n == ax then
    return true
  match (← get).get? n with
  | some b => return b
  | none =>
    modify (·.insert n false)
    let some ci := env.find? n | return false
    let consts := ci.type.getUsedConstants ++
      (match ci.value? with | some v => v.getUsedConstants | none => #[])
    let mut r := false
    for c in consts do
      if ← carriesAx env ax c then
        r := true
    modify (·.insert n r)
    return r

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
  let mut boundaryStmtBorne := 0
  let mut memo : Std.HashMap Name Bool := {}
  for n in names do
    let (ours, boundary) := match env.getModuleIdxFor? n with
      | some idx => (isOurs[idx.toNat]!, isBoundary[idx.toNat]!)
      | none => (true, false)  -- the file being elaborated: trio-only
    unless ours do continue
    let some (.thmInfo ti) := env.find? n | continue
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
    -- F-07 STRENGTHENING (Phase 5): ORIGIN DISCIPLINE. In a boundary
    -- module, `runEffectful` may enter a theorem's cone ONLY through
    -- its STATEMENT (the constants of its type — the shipped initial
    -- state); a proof-borne boundary axiom is never acceptable and
    -- fails the build. Together with the upper bound this makes every
    -- boundary theorem's cone exact-by-construction: the trio, plus
    -- runEffectful exactly when the statement carries it.
    if boundary && axs.contains ``runEffectful then
      let mut stmtCarries := false
      for c in ti.type.getUsedConstants do
        unless stmtCarries do
          let (b, memo') := (carriesAx env ``runEffectful c).run memo
          memo := memo'
          if b then
            stmtCarries := true
      unless stmtCarries do
        throwError "CerberusHeapLang axiom sweep FAILED (origin \
          discipline, F-07): boundary theorem {n} carries runEffectful \
          in its cone but NOT through its statement's constants — a \
          proof-borne boundary axiom is never allowed; the boundary \
          allowance covers statement-borne entries only."
      boundaryStmtBorne := boundaryStmtBorne + 1
    swept := swept + 1
    if boundary then boundarySwept := boundarySwept + 1
  logInfo s!"CerberusHeapLang axiom sweep: {swept} theorems BOUNDED by the \
    declared upper bounds ({boundarySwept} in the production-entry \
    boundary modules, of which {boundaryStmtBorne} carry the boundary \
    axiom — each STATEMENT-BORNE, origin-checked, so every boundary \
    cone is exact-by-construction: trio + runEffectful iff the \
    statement carries it; all other theorems bounded by the trio; \
    headline cones additionally pinned above)"
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
