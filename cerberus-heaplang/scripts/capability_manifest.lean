/-
capability_manifest.lean — THE CAPABILITY MANIFEST generator
(pattern: statement_census.lean; installed by Phase 0 of the
2026-08-31 foundations arc, remediating audit findings F-01/F-09).

Generates docs/CAPABILITY_MANIFEST.md: one row per supported Core
construct, columns = mirror rule / logic (wp/wps) rule / fragment
cone membership / per-step engine match / partial-adequacy lane /
total lane / production lane / example consumer. The committed
output is THE authoritative scope statement: every claims surface
(README, walkthrough) defers to it, and scripts/test_unit.sh gate 4
fails on (a) drift between a fresh run and the committed file and
(b) any README certified-scope token outside the manifest's
ADEQUACY-EXPORTABLE set.

CHECKED vs DECLARED (Phase-0 honesty about the instrument itself):
- CHECKED (mechanical, fail-closed): every named declaration in an
  `OK ...` cell is looked up in the environment and must exist with
  the stated kind (theorem / constructor) — a deleted or renamed
  rule, cone case, match lemma, or consumer makes this script THROW
  and the gate go red. Additionally the FULL CONSTRUCTOR LISTS of
  `Step` and `Frag` are asserted equal to the expected lists below:
  ANY cone/mirror constructor added or removed fails the run until
  the manifest is regenerated and re-reviewed.
- DECLARED (documented, not yet mechanical): the ATTRIBUTIONS — that
  a listed consumer's program actually executes the construct, and
  the lane assignments. Phase 1 replaces these with a table
  generated FROM the unified capability predicate (registered
  upgrade; arc plan Phase 1 item 2).

Run (from cerberus-heaplang/; deterministic, no timestamps):
  ../scripts/capped ~/.elan/bin/lake env lean scripts/capability_manifest.lean \
    > docs/CAPABILITY_MANIFEST.md
-/
import CerberusHeapLang

open Lean Meta

namespace CapabilityManifest

/-- A manifest cell. -/
inductive Cell
  /-- CHECKED: theorems that must exist. -/
  | thms (names : List Name) (note : String := "")
  /-- CHECKED: constructors that must exist. -/
  | ctors (names : List Name) (note : String := "")
  /-- DECLARED only (documented, not name-checked). -/
  | declared (text : String)
  /-- RED: capability absent (reason printed). -/
  | red (text : String)

def Cell.isRed : Cell → Bool
  | .red _ => true
  | _ => false

structure Row where
  token : String
  construct : String
  mirror : Cell
  logic : Cell
  cone : Cell
  engineMatch : Cell
  partialLane : Cell
  totalLane : Cell
  prodLane : Cell
  consumer : Cell

/-- Row level for the claims surfaces. The CORE columns are mirror /
cone / engine-match / partial-adequacy / consumer; the logic column
is reported separately (create is adequacy-exportable with no logic
rule); total and production lanes are honest extra lanes, RED for
most rows in Phase 0. -/
def Row.coreCells (r : Row) : List Cell :=
  [r.mirror, r.cone, r.engineMatch, r.partialLane, r.consumer]

def Row.exportable (r : Row) : Bool :=
  !(r.coreCells.any Cell.isRed)

def Row.fullRow (r : Row) : Bool :=
  r.exportable && !(r.logic.isRed)

def Row.level (r : Row) : String :=
  if !r.exportable then "LOCAL RULE ONLY (RED)"
  else if r.logic.isRed then "ADEQUACY-EXPORTABLE (no logic rule)"
  else "CERTIFIED (drive lane)"

/-- The uniform Phase-0 total-lane cell (F-02). -/
def noTotal : Cell := .red "no logical total lane (Phase 3); see Notes 2"

/-- The uniform loop-construct production cell (F-05). -/
def prodRegOnly : Cell := .red "registration tie only; see Notes 3"

def pfx : String := "CerberusHeapLang."

def shortName (n : Name) : String :=
  let s := n.toString
  if s.startsWith pfx then (s.drop pfx.length).toString else s

def rows : List Row := [
  { token := "value", construct := "value delivery (Epure at PEval; Eannot values)",
    mirror := .declared "terminal — the toVal/ofVal value protocol (values do not step)",
    logic := .thms [`CerberusHeapLang.wp_ofVal, `CerberusHeapLang.wps_ofVal],
    cone := .ctors [`CerberusHeapLang.Frag.val_pure],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_done,
      `CerberusHeapLang.step_ctx_remove_annot],
    partialLane := .thms [`CerberusHeapLang.engine_complete,
      `CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
    consumer := .thms [`CerberusHeapLang.exhibitA_engine] },
  { token := "store", construct := "Eaction Store0 (value operands)",
    mirror := .ctors [`CerberusHeapLang.Step.store],
    logic := .thms [`CerberusHeapLang.wp_store, `CerberusHeapLang.wps_store],
    cone := .ctors [`CerberusHeapLang.Frag.store],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_store],
    partialLane := .thms [`CerberusHeapLang.engine_complete,
      `CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
    consumer := .thms [`CerberusHeapLang.exhibitB_engine,
      `CerberusHeapLang.counter_loop_certified,
      `CerberusHeapLang.list_reverse_certified] },
  { token := "load", construct := "Eaction Load0 (value operand)",
    mirror := .ctors [`CerberusHeapLang.Step.load],
    logic := .thms [`CerberusHeapLang.wp_load, `CerberusHeapLang.wps_load],
    cone := .ctors [`CerberusHeapLang.Frag.load],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_load],
    partialLane := .thms [`CerberusHeapLang.engine_complete,
      `CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
    consumer := .thms [`CerberusHeapLang.exhibitA_engine,
      `CerberusHeapLang.array_sum_certified] },
  { token := "create", construct := "Eaction Create0",
    mirror := .ctors [`CerberusHeapLang.Step.create],
    logic := .red "no wp_create/wps_create small axiom (registered D26: needs the allocator-cursor resource; Phase 2); see Notes 4",
    cone := .ctors [`CerberusHeapLang.Frag.create],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_create],
    partialLane := .thms [`CerberusHeapLang.engine_complete,
      `CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
    consumer := .thms [`CerberusHeapLang.exhibitA_prod]
      (note := "production exhibit only — no drive-lane-only consumer") },
  { token := "sseq-wild", construct := "Esseq, wildcard pattern",
    mirror := .ctors [`CerberusHeapLang.Step.sseq_pure,
      `CerberusHeapLang.Step.sseq_annot, `CerberusHeapLang.Step.sseq_ctx],
    logic := .thms [`CerberusHeapLang.wp_sseq, `CerberusHeapLang.wps_seq],
    cone := .ctors [`CerberusHeapLang.Frag.sseq],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_beta_pure,
      `CerberusHeapLang.step_ctx_beta_annot],
    partialLane := .thms [`CerberusHeapLang.engine_complete,
      `CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
    consumer := .thms [`CerberusHeapLang.exhibitA_engine,
      `CerberusHeapLang.exhibitC_engine] },
  { token := "sseq-spec", construct := "Esseq, Specified-binder pattern",
    mirror := .ctors [`CerberusHeapLang.Step.sseq_spec_pure,
      `CerberusHeapLang.Step.sseq_spec_annot],
    logic := .thms [`CerberusHeapLang.wps_seq_spec],
    cone := .ctors [`CerberusHeapLang.Frag.sseq_spec],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_beta_spec_pure,
      `CerberusHeapLang.step_ctx_beta_spec_annot],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.array_sum_certified,
      `CerberusHeapLang.list_reverse_certified] },
  { token := "sseq-sym", construct := "Esseq, plain-symbol-binder pattern (bare values)",
    mirror := .ctors [`CerberusHeapLang.Step.sseq_sym_pure],
    logic := .thms [`CerberusHeapLang.wps_seq_sym],
    cone := .ctors [`CerberusHeapLang.Frag.sseq_sym],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_beta_sym_pure],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.list_reverse_certified] },
  { token := "annot", construct := "Eannot residue (descent + merge)",
    mirror := .ctors [`CerberusHeapLang.Step.annot_ctx,
      `CerberusHeapLang.Step.annot_merge],
    logic := .thms [`CerberusHeapLang.wp_annot, `CerberusHeapLang.wps_annot],
    cone := .ctors [`CerberusHeapLang.Frag.annot],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_merge],
    partialLane := .thms [`CerberusHeapLang.engine_complete,
      `CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
    consumer := .thms [`CerberusHeapLang.exhibitA_engine] },
  { token := "save", construct := "Esave (block entry, value-shaped params)",
    mirror := .ctors [`CerberusHeapLang.Step.save],
    logic := .thms [`CerberusHeapLang.wps_save],
    cone := .ctors [`CerberusHeapLang.Frag.save],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_save],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.counter_loop_certified,
      `CerberusHeapLang.fib_certified] },
  { token := "if", construct := "Eif (big-step boolean guard)",
    mirror := .ctors [`CerberusHeapLang.Step.if_true,
      `CerberusHeapLang.Step.if_false],
    logic := .thms [`CerberusHeapLang.wps_if_true,
      `CerberusHeapLang.wps_if_false],
    cone := .ctors [`CerberusHeapLang.Frag.if_],
    engineMatch := .thms [`CerberusHeapLang.stepDischarge_if_true,
      `CerberusHeapLang.stepDischarge_if_false],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.counter_loop_certified,
      `CerberusHeapLang.fib_certified] },
  { token := "run", construct := "Erun (context-discarding jump)",
    mirror := .ctors [`CerberusHeapLang.Step.run],
    logic := .thms [`CerberusHeapLang.wps_run],
    cone := .ctors [`CerberusHeapLang.Frag.run],
    engineMatch := .thms [`CerberusHeapLang.stepDischarge_run],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.counter_loop_certified,
      `CerberusHeapLang.fib_certified] },
  { token := "case-value", construct := "Ecase, VALUE scrutinee",
    mirror := .ctors [`CerberusHeapLang.Step.case_value],
    logic := .thms [`CerberusHeapLang.wps_case_value],
    cone := .ctors [`CerberusHeapLang.Frag.case_value]
      (note := "S1b: joined — branch-closure + branch-size premises explicit"),
    engineMatch := .thms [`CerberusHeapLang.step_ctx_case_value,
      `CerberusHeapLang.step_ctx_case_illtyped,
      `CerberusHeapLang.engine_complete_caseU]
      (note := "TWO-SIDED at any MachineCtx"),
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ,
      `CerberusHeapLang.engine_adequacyU],
    totalLane := noTotal,
    prodLane := .red "outside every lane",
    consumer := .thms [`CerberusHeapLang.case_certified]
      (note := "the WP-lane adequacy regression — binder pattern, substitution TAU (CaseExhibit)") },
  { token := "pure-sym", construct := "Epure exit at PEsym shape",
    mirror := .ctors [`CerberusHeapLang.Step.pure_eval]
      (note := "certified at PEsym shape — Soundness stepDischarge_pure_sym"),
    logic := .thms [`CerberusHeapLang.wps_pure],
    cone := .ctors [`CerberusHeapLang.Frag.pure_sym],
    engineMatch := .thms [`CerberusHeapLang.stepDischarge_pure_sym],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.fib_certified] },
  { token := "memop-ptreq", construct := "Ememop PtrEq (value operands)",
    mirror := .ctors [`CerberusHeapLang.Step.memop_ptreq],
    logic := .thms [`CerberusHeapLang.wps_memop_ptreq],
    cone := .ctors [`CerberusHeapLang.Frag.memop_vals],
    engineMatch := .thms [`CerberusHeapLang.step_ctx_memop],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.list_reverse_certified] },
  { token := "memop-op", construct := "Ememop PtrEq, operand-evaluation step",
    mirror := .ctors [`CerberusHeapLang.Step.memop_eval],
    logic := .thms [`CerberusHeapLang.wps_memop_eval],
    cone := .ctors [`CerberusHeapLang.Frag.memop_op],
    engineMatch := .thms [`CerberusHeapLang.stepDischarge_memop_eval],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.list_reverse_certified] },
  { token := "load-op", construct := "Load0 operand-evaluation step (ACTION_EVAL)",
    mirror := .ctors [`CerberusHeapLang.Step.load_eval],
    logic := .thms [`CerberusHeapLang.wps_load_eval],
    cone := .ctors [`CerberusHeapLang.Frag.load_op],
    engineMatch := .thms [`CerberusHeapLang.stepDischarge_load_eval],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.array_sum_certified] },
  { token := "store-op", construct := "Store0 operand-evaluation step (ACTION_EVAL)",
    mirror := .ctors [`CerberusHeapLang.Step.store_eval],
    logic := .thms [`CerberusHeapLang.wps_store_eval],
    cone := .ctors [`CerberusHeapLang.Frag.store_op],
    engineMatch := .thms [`CerberusHeapLang.stepDischarge_store_eval],
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.list_reverse_certified] },
  { token := "pure-operands",
    construct := "pure operands: PEval / PEsym / integer PEop / PEarray_shift",
    mirror := .declared "premises of the if/run/pure/ACTION_EVAL rules via the certified pure evaluator (Soundness evaluator bridge); no per-construct Step rule",
    logic := .declared "enters as rule premises (guard/argument/operand evaluation)",
    cone := .declared "via the peDepth side conditions carried by Frag.if_/run/load_op/memop_op/store_op",
    engineMatch := .declared "the evaluator bridge lemmas, Soundness.lean (eval1/mapM tower)",
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    totalLane := noTotal,
    prodLane := prodRegOnly,
    consumer := .thms [`CerberusHeapLang.array_sum_certified,
      `CerberusHeapLang.fib_certified] }
]

/-- The asserted mirror constructor list (sorted). ANY change to the
`Step` inductive fails this run until the manifest is regenerated. -/
def expectedStepCtors : List Name :=
  [`CerberusHeapLang.Step.annot_ctx, `CerberusHeapLang.Step.annot_merge,
   `CerberusHeapLang.Step.case_value, `CerberusHeapLang.Step.create,
   `CerberusHeapLang.Step.if_false, `CerberusHeapLang.Step.if_true,
   `CerberusHeapLang.Step.load, `CerberusHeapLang.Step.load_eval,
   `CerberusHeapLang.Step.memop_eval, `CerberusHeapLang.Step.memop_ptreq,
   `CerberusHeapLang.Step.pure_eval, `CerberusHeapLang.Step.run,
   `CerberusHeapLang.Step.save, `CerberusHeapLang.Step.sseq_annot,
   `CerberusHeapLang.Step.sseq_ctx, `CerberusHeapLang.Step.sseq_pure,
   `CerberusHeapLang.Step.sseq_spec_annot, `CerberusHeapLang.Step.sseq_spec_pure,
   `CerberusHeapLang.Step.sseq_sym_pure, `CerberusHeapLang.Step.store,
   `CerberusHeapLang.Step.store_eval]

/-- The asserted cone constructor list (sorted). S1b: ONE unified
cone (`Frag` — the migrated `FragJ`), with value-scrutinee `Ecase`
JOINED (`Frag.case_value` — the F-01 export). Still hand-asserted
this slice; S1c derives the rows from the cone. -/
def expectedFragCtors : List Name :=
  [`CerberusHeapLang.Frag.annot, `CerberusHeapLang.Frag.case_value,
   `CerberusHeapLang.Frag.create,
   `CerberusHeapLang.Frag.if_, `CerberusHeapLang.Frag.load,
   `CerberusHeapLang.Frag.load_op, `CerberusHeapLang.Frag.memop_op,
   `CerberusHeapLang.Frag.memop_vals, `CerberusHeapLang.Frag.pure_sym,
   `CerberusHeapLang.Frag.run, `CerberusHeapLang.Frag.save,
   `CerberusHeapLang.Frag.sseq, `CerberusHeapLang.Frag.sseq_spec,
   `CerberusHeapLang.Frag.sseq_sym, `CerberusHeapLang.Frag.store,
   `CerberusHeapLang.Frag.store_op, `CerberusHeapLang.Frag.val_pure]

def checkNames (env : Environment) (kind : String) (names : List Name) :
    Except String Unit := do
  for n in names do
    match env.find? n with
    | none => throw s!"manifest FAIL: {n} not found in the environment"
    | some ci =>
      match kind, ci with
      | "theorem", .thmInfo _ => pure ()
      | "ctor", .ctorInfo _ => pure ()
      | _, _ => throw s!"manifest FAIL: {n} exists but is not a {kind}"

def Cell.render (env : Environment) : Cell → Except String String
  | .thms names note => do
    checkNames env "theorem" names
    let ns := ", ".intercalate (names.map (fun n => s!"`{shortName n}`"))
    pure s!"OK {ns}{if note == "" then "" else s!" — {note}"}"
  | .ctors names note => do
    checkNames env "ctor" names
    let ns := ", ".intercalate (names.map (fun n => s!"`{shortName n}`"))
    pure s!"OK {ns}{if note == "" then "" else s!" — {note}"}"
  | .declared text => pure s!"DECLARED — {text}"
  | .red text => pure s!"RED — {text}"

def checkCtorList (env : Environment) (ind : Name) (expected : List Name) :
    Except String Unit := do
  match env.find? ind with
  | some (.inductInfo iv) =>
    let actual :=
      ((iv.ctors.map Name.toString).toArray.qsort (fun a b => a < b)).toList
    let expectedS :=
      ((expected.map Name.toString).toArray.qsort (fun a b => a < b)).toList
    unless actual == expectedS do
      throw s!"manifest FAIL: constructor list of {ind} changed.\n\
        expected: {expectedS}\n\
        actual:   {actual}\n\
        A cone/mirror constructor was added or removed — regenerate \
        docs/CAPABILITY_MANIFEST.md deliberately (and update the \
        expected list here) or restore the constructor."
  | _ => throw s!"manifest FAIL: inductive {ind} not found"

#eval show MetaM Unit from do
  let env ← getEnv
  -- CHECKED: the full mirror and cone constructor lists.
  (match checkCtorList env `CerberusHeapLang.Step expectedStepCtors with
   | .ok () => pure ()
   | .error e => throwError e)
  (match checkCtorList env `CerberusHeapLang.Frag expectedFragCtors with
   | .ok () => pure ()
   | .error e => throwError e)
  let render (c : Cell) : MetaM String :=
    match c.render env with
    | .ok s => pure s
    | .error e => throwError e
  IO.println "# The capability manifest"
  IO.println ""
  IO.println "GENERATED by `scripts/capability_manifest.lean` — do not hand-edit;"
  IO.println "regenerate with:"
  IO.println ""
  IO.println "```bash"
  IO.println "../scripts/capped ~/.elan/bin/lake env lean scripts/capability_manifest.lean \\"
  IO.println "  > docs/CAPABILITY_MANIFEST.md"
  IO.println "```"
  IO.println ""
  IO.println "This file is THE authoritative per-construct scope statement for"
  IO.println "`cerberus-heaplang` (2026-08-31 foundations arc, Phase 0; audit"
  IO.println "findings F-01/F-09). Every claims surface defers to it: a construct"
  IO.println "may be claimed at exactly its row's level, no more. Enforcement:"
  IO.println "`scripts/test_unit.sh` gate 4 (drift + README scope tie)."
  IO.println ""
  IO.println "Column semantics — which columns are CHECKED vs DECLARED is part of"
  IO.println "the instrument's honesty and is stated in the script header: `OK`"
  IO.println "cells are name-and-kind checked in the built environment (and the"
  IO.println "full `Step`/`Frag` constructor lists are asserted verbatim, so a"
  IO.println "deleted cone case fails the gate); lane ATTRIBUTIONS and"
  IO.println "consumer-exercises-construct claims are DECLARED pending the Phase-1"
  IO.println "fully mechanical (cone-derived) upgrade."
  IO.println ""
  IO.println "| Construct | Level | Mirror (Step) | Logic (wp/wps) | Cone (Frag) | Engine match | Partial adequacy | Total lane | Production lane | Example consumer |"
  IO.println "|---|---|---|---|---|---|---|---|---|---|"
  for r in rows do
    let cells ← [r.mirror, r.logic, r.cone, r.engineMatch, r.partialLane,
      r.totalLane, r.prodLane, r.consumer].mapM render
    IO.println s!"| {r.construct} | {r.level} | {" | ".intercalate cells} |"
  IO.println ""
  IO.println "## Notes (the registered honesty items behind the RED cells)"
  IO.println ""
  IO.println "1. **`Ecase` (value scrutinee) exported in S1b**"
  IO.println "   (audit F-01 remediation): mirror rule + wps rule + cone"
  IO.println "   membership (`Frag.case_value`, branch-closure and branch-size"
  IO.println "   premises explicit over the extended `esize`) + TWO-SIDED engine"
  IO.println "   pair (`step_ctx_case_value`/`step_ctx_case_illtyped`/"
  IO.println "   `engine_complete_caseU`) + generic adequacy coverage + the"
  IO.println "   WP-lane consumer regression `case_certified` (CaseExhibit: a"
  IO.println "   BINDER-pattern case program — the substitution TAU genuinely"
  IO.println "   fires — through wps_case_value → wps_sound →"
  IO.println "   spike_engine_adequacy, engine-vocabulary conclusion)."
  IO.println "2. **The total lane is empty for every construct** (audit F-02):"
  IO.println "   the logic has no total WP / total statement judgment;"
  IO.println "   `blockSpecs_intro_variant` has no theorem-level termination"
  IO.println "   consequence and no consumer. `fib_certified_total` is an"
  IO.println "   OPERATIONAL ENGINE THEOREM (direct induction on the drive,"
  IO.println "   explicit `Step`/`driveJ_step` rewrites) — an engine"
  IO.println "   regression/termination-accounting result, NOT a logic product."
  IO.println "   Phase 3 owns the logical total lane."
  IO.println "3. **The production lane for loop constructs is RED** (audit F-05):"
  IO.println "   what exists is the REGISTRATION theorem —"
  IO.println "   `counter_loop_certified_production` concludes at `driveJ` at the"
  IO.println "   shipped initial run state with the label plumbing derived from"
  IO.println "   the shipped registration; it is NOT a `runND` production"
  IO.println "   equation. NAMING DEBT (registered): the declaration keeps its"
  IO.println "   `_production` name this phase (a rename is statement-surface"
  IO.println "   churn); docs call it the registration theorem; the rename to"
  IO.println "   `_registration` lands with Phase 5's real production theorem."
  IO.println "   Straight-line constructs reach the shipped pipeline via"
  IO.println "   `exhibitA_prod`."
  IO.println "4. **`create` has no logic rule** (registered D26): sound"
  IO.println "   `wp_create` needs the allocator-cursor resource (Phase 2). It is"
  IO.println "   adequacy-exportable (mirror + cone + match) and its only example"
  IO.println "   consumer is the production exhibit."
  IO.println "5. **Interior (sub-allocation) load/store rules are not construct"
  IO.println "   rows**: `wps_load_interior` and the exhibit-local node rules are"
  IO.println "   layout-specific extensions of the rule layer (audit F-04);"
  IO.println "   Phase 2 replaces them with generic typed-subrange rules."
  IO.println ""
  IO.println "## Machine-readable scope lines (consumed by test_unit.sh gate 4)"
  IO.println ""
  let exportable := rows.filter (·.exportable) |>.map (·.token)
  let fullRows := rows.filter (·.fullRow) |>.map (·.token)
  let localOnly := rows.filter (fun r => !r.exportable) |>.map (·.token)
  IO.println "```"
  IO.println s!"ADEQUACY-EXPORTABLE: {" ".intercalate exportable}"
  IO.println s!"FULL-ROW: {" ".intercalate fullRows}"
  IO.println s!"LOCAL-RULE-ONLY: {" ".intercalate localOnly}"
  IO.println "```"
