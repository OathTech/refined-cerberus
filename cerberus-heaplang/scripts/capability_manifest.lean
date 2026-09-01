/-
capability_manifest.lean — THE CAPABILITY MANIFEST generator
(pattern: statement_census.lean; installed by Phase 0 of the
2026-08-31 foundations arc, remediating audit findings F-01/F-09;
upgraded to the CONE-DERIVED form by Phase-1 S1c — design record §4,
the K4 mechanism demonstrated by the S1a probe).

Generates docs/CAPABILITY_MANIFEST.md: one row per supported Core
construct, columns = mirror rule / logic (wp/wps) rule / fragment
cone membership / per-step engine match / partial-adequacy lane /
total lane / production lane / example consumer. The committed
output is THE authoritative scope statement: every claims surface
(README, walkthrough) defers to it, and scripts/test_unit.sh gate 4
fails on (a) drift between a fresh run and the committed file and
(b) any README certified-scope token outside the manifest's
ADEQUACY-EXPORTABLE set.

DERIVED vs CHECKED vs DECLARED (the instrument's own honesty):
- DERIVED (S1c — environment reflection, fail-closed): THE ROW SET
  IS ENUMERATED FROM `Frag`'s constructor list read out of the built
  environment — there is no hand-written row list and no
  hand-asserted constructor list to drift. A cone constructor
  without a `rowSpec` mapping makes this script THROW (extending the
  cone without the manifest is a red run). Symmetrically, the
  `Step` mirror's coverage is derived: every `Step` constructor read
  from the environment must be claimed by EXACTLY ONE row's mirror
  cell — a new mirror rule without a manifest row, a stale claim of
  a non-Step constructor, or a double claim each throws. This is
  the audit F-03 acceptance property "coverage cannot differ without
  a failed check" in mechanical form.
- CHECKED (the Phase-0 discipline, kept): every named declaration in
  an `OK ...` cell is looked up in the environment and must exist
  with the stated kind (theorem / constructor) — a deleted or
  renamed rule, match lemma, or consumer makes this script THROW and
  the gate go red.
- DECLARED (documented, not mechanical): the ATTRIBUTIONS — that a
  listed consumer's program actually executes the construct, and the
  lane assignments. This is documented instrument granularity:
  name-and-kind plus derived coverage is the checked level; no
  registered mover.

Row order is the cone's constructor declaration order (the
enumeration is the row set), followed by the supplementary
evaluator-tower row (which owns no cone constructor — premises, not
a capability; it is barred from claiming constructors, mechanically).

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

/-- The constructor names a cell claims (empty for non-ctor cells). -/
def Cell.ctorNames : Cell → List Name
  | .ctors names _ => names
  | _ => []

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
most rows. -/
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

/-- The uniform total-lane cell (F-02; Phase 3 owns the lane). -/
def noTotal : Cell := .red "no logical total lane (Phase 3); see Notes 2"

/-- The uniform loop-construct production cell (F-05). -/
def prodRegOnly : Cell := .red "registration tie only; see Notes 3"

def pfx : String := "CerberusHeapLang."

def shortName (n : Name) : String :=
  let s := n.toString
  if s.startsWith pfx then (s.drop pfx.length).toString else s

/-- Per-cone-constructor row data. The cone cell is NOT here — it is
the enumeration key itself (filled in by the generator), so a row
cannot claim cone membership the cone does not have. -/
structure RowSpec where
  token : String
  construct : String
  mirror : Cell
  logic : Cell
  coneNote : String := ""
  engineMatch : Cell
  partialLane : Cell
  totalLane : Cell
  prodLane : Cell
  consumer : Cell

def RowSpec.toRow (spec : RowSpec) (coneCtor : Name) : Row :=
  { token := spec.token, construct := spec.construct,
    mirror := spec.mirror, logic := spec.logic,
    cone := .ctors [coneCtor] (note := spec.coneNote),
    engineMatch := spec.engineMatch, partialLane := spec.partialLane,
    totalLane := spec.totalLane, prodLane := spec.prodLane,
    consumer := spec.consumer }

/-- THE CONSTRUCTOR → ROW MAPPING. The row set itself is NOT listed
anywhere — it is enumerated from `Frag`'s constructors in the built
environment; this mapping must COVER the enumeration or the run
throws (fail-closed: the cone cannot grow past the manifest). -/
def rowSpec : Name → Option RowSpec
  | `CerberusHeapLang.Frag.val_pure => some
    { token := "value", construct := "value delivery (Epure at PEval; Eannot values)",
      mirror := .declared "terminal — the toVal/ofVal value protocol (values do not step)",
      logic := .thms [`CerberusHeapLang.wp_ofVal, `CerberusHeapLang.wps_ofVal],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_done,
        `CerberusHeapLang.step_ctx_remove_annot],
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
      consumer := .thms [`CerberusHeapLang.exhibitA_engine] }
  | `CerberusHeapLang.Frag.store => some
    { token := "store", construct := "Eaction Store0 (value operands)",
      mirror := .ctors [`CerberusHeapLang.Step.store],
      logic := .thms [`CerberusHeapLang.wp_store, `CerberusHeapLang.wps_store],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_store],
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
      consumer := .thms [`CerberusHeapLang.exhibitB_engine,
        `CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.load => some
    { token := "load", construct := "Eaction Load0 (value operand)",
      mirror := .ctors [`CerberusHeapLang.Step.load],
      logic := .thms [`CerberusHeapLang.wp_load, `CerberusHeapLang.wps_load],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_load],
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
      consumer := .thms [`CerberusHeapLang.exhibitA_engine,
        `CerberusHeapLang.array_sum_certified] }
  | `CerberusHeapLang.Frag.create => some
    { token := "create", construct := "Eaction Create0",
      mirror := .ctors [`CerberusHeapLang.Step.create],
      logic := .red "no wp_create/wps_create small axiom (registered D26: needs the allocator-cursor resource; Phase 2); see Notes 4",
      engineMatch := .thms [`CerberusHeapLang.step_ctx_create],
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
      consumer := .thms [`CerberusHeapLang.exhibitA_prod]
        (note := "production exhibit only — no drive-lane-only consumer") }
  | `CerberusHeapLang.Frag.sseq => some
    { token := "sseq-wild", construct := "Esseq, wildcard pattern",
      mirror := .ctors [`CerberusHeapLang.Step.sseq_pure,
        `CerberusHeapLang.Step.sseq_annot, `CerberusHeapLang.Step.sseq_ctx],
      logic := .thms [`CerberusHeapLang.wp_sseq, `CerberusHeapLang.wps_seq],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_beta_pure,
        `CerberusHeapLang.step_ctx_beta_annot],
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
      consumer := .thms [`CerberusHeapLang.exhibitA_engine,
        `CerberusHeapLang.exhibitC_engine] }
  | `CerberusHeapLang.Frag.annot => some
    { token := "annot", construct := "Eannot residue (descent + merge)",
      mirror := .ctors [`CerberusHeapLang.Step.annot_ctx,
        `CerberusHeapLang.Step.annot_merge],
      logic := .thms [`CerberusHeapLang.wp_annot, `CerberusHeapLang.wps_annot],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_merge],
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod],
      consumer := .thms [`CerberusHeapLang.exhibitA_engine] }
  | `CerberusHeapLang.Frag.save => some
    { token := "save", construct := "Esave (block entry, value-shaped params)",
      mirror := .ctors [`CerberusHeapLang.Step.save],
      logic := .thms [`CerberusHeapLang.wps_save],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_save],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.fib_certified] }
  | `CerberusHeapLang.Frag.if_ => some
    { token := "if", construct := "Eif (big-step boolean guard)",
      mirror := .ctors [`CerberusHeapLang.Step.if_true,
        `CerberusHeapLang.Step.if_false],
      logic := .thms [`CerberusHeapLang.wps_if_true,
        `CerberusHeapLang.wps_if_false],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_if_true,
        `CerberusHeapLang.stepDischarge_if_false],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.fib_certified] }
  | `CerberusHeapLang.Frag.run => some
    { token := "run", construct := "Erun (context-discarding jump)",
      mirror := .ctors [`CerberusHeapLang.Step.run],
      logic := .thms [`CerberusHeapLang.wps_run],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_run],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.fib_certified] }
  | `CerberusHeapLang.Frag.sseq_spec => some
    { token := "sseq-spec", construct := "Esseq, Specified-binder pattern",
      mirror := .ctors [`CerberusHeapLang.Step.sseq_spec_pure,
        `CerberusHeapLang.Step.sseq_spec_annot],
      logic := .thms [`CerberusHeapLang.wps_seq_spec],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_beta_spec_pure,
        `CerberusHeapLang.step_ctx_beta_spec_annot],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.array_sum_certified,
        `CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.pure_sym => some
    { token := "pure-sym", construct := "Epure exit at PEsym shape",
      mirror := .ctors [`CerberusHeapLang.Step.pure_eval]
        (note := "certified at PEsym shape — Soundness stepDischarge_pure_sym"),
      logic := .thms [`CerberusHeapLang.wps_pure],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_pure_sym],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.fib_certified] }
  | `CerberusHeapLang.Frag.load_op => some
    { token := "load-op", construct := "Load0 operand-evaluation step (ACTION_EVAL)",
      mirror := .ctors [`CerberusHeapLang.Step.load_eval],
      logic := .thms [`CerberusHeapLang.wps_load_eval],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_load_eval],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.array_sum_certified] }
  | `CerberusHeapLang.Frag.sseq_sym => some
    { token := "sseq-sym", construct := "Esseq, plain-symbol-binder pattern (bare values)",
      mirror := .ctors [`CerberusHeapLang.Step.sseq_sym_pure],
      logic := .thms [`CerberusHeapLang.wps_seq_sym],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_beta_sym_pure],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.memop_vals => some
    { token := "memop-ptreq", construct := "Ememop PtrEq (value operands)",
      mirror := .ctors [`CerberusHeapLang.Step.memop_ptreq],
      logic := .thms [`CerberusHeapLang.wps_memop_ptreq],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_memop],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.memop_op => some
    { token := "memop-op", construct := "Ememop PtrEq, operand-evaluation step",
      mirror := .ctors [`CerberusHeapLang.Step.memop_eval],
      logic := .thms [`CerberusHeapLang.wps_memop_eval],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_memop_eval],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.store_op => some
    { token := "store-op", construct := "Store0 operand-evaluation step (ACTION_EVAL)",
      mirror := .ctors [`CerberusHeapLang.Step.store_eval],
      logic := .thms [`CerberusHeapLang.wps_store_eval],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_store_eval],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := noTotal,
      prodLane := prodRegOnly,
      consumer := .thms [`CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.case_value => some
    { token := "case-value", construct := "Ecase, VALUE scrutinee",
      mirror := .ctors [`CerberusHeapLang.Step.case_value],
      logic := .thms [`CerberusHeapLang.wps_case_value],
      coneNote := "S1b: joined — branch-closure + branch-size premises explicit",
      engineMatch := .thms [`CerberusHeapLang.step_ctx_case_value,
        `CerberusHeapLang.step_ctx_case_illtyped,
        `CerberusHeapLang.engine_complete_caseU]
        (note := "TWO-SIDED at any MachineCtx"),
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ,
        `CerberusHeapLang.engine_adequacyU],
      totalLane := noTotal,
      prodLane := .red "outside every lane",
      consumer := .thms [`CerberusHeapLang.case_certified]
        (note := "the WP-lane adequacy regression — binder pattern, substitution TAU (CaseExhibit)") }
  | `CerberusHeapLang.Frag.wseq => some
    { token := "wseq-wild", construct := "Ewseq, wildcard pattern (weak sequencing)",
      mirror := .ctors [`CerberusHeapLang.Step.wseq_pure,
        `CerberusHeapLang.Step.wseq_annot, `CerberusHeapLang.Step.wseq_ctx]
        (note := "S1b DRIFT TEST — entered through the generic route; see Notes 6"),
      logic := .thms [`CerberusHeapLang.wps_wseq],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_wseq_pure,
        `CerberusHeapLang.step_ctx_wseq_annot],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ,
        `CerberusHeapLang.engine_adequacyU],
      totalLane := noTotal,
      prodLane := .red "outside every lane",
      consumer := .thms [`CerberusHeapLang.wseq_certified]
        (note := "the drift-test WP-lane adequacy regression (WseqExhibit)") }
  | _ => none

/-- Supplementary rows that own NO cone constructor: premises of the
cone's rules (the evaluator tower), not capabilities. Barred from
claiming any constructor (enforced mechanically below) — a row here
can never absorb a cone or mirror extension. -/
def supplementaryRows : List Row := [
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

#eval show MetaM Unit from do
  let env ← getEnv
  -- THE ENUMERATION (K4, derived): the row set IS `Frag`'s
  -- constructor list, read out of the built environment.
  let some (.inductInfo fragInfo) := env.find? `CerberusHeapLang.Frag
    | throwError "manifest FAIL: inductive CerberusHeapLang.Frag not found"
  let some (.inductInfo stepInfo) := env.find? `CerberusHeapLang.Step
    | throwError "manifest FAIL: inductive CerberusHeapLang.Step not found"
  let mut coneRows : Array Row := #[]
  for ctor in fragInfo.ctors do
    let some spec := rowSpec ctor
      | throwError "manifest FAIL: cone constructor {ctor} has NO \
          manifest row mapping — the cone was extended without the \
          manifest (fail-closed by design; add the rowSpec arm)."
    coneRows := coneRows.push (spec.toRow ctor)
  -- Supplementary rows own no constructors, by construction.
  for r in supplementaryRows do
    unless (r.mirror.ctorNames ++ r.cone.ctorNames).isEmpty do
      throwError "manifest FAIL: supplementary row '{r.token}' claims \
        constructors — supplementary rows are premises-only; give the \
        construct a cone constructor and a rowSpec arm instead."
  let rows := coneRows.toList ++ supplementaryRows
  -- DERIVED MIRROR COVERAGE: the rows' mirror claims must be exactly
  -- `Step`'s constructor list — each claim a real Step constructor,
  -- no constructor claimed twice, no constructor unclaimed.
  let mut claimed : Array Name := #[]
  for r in rows do
    for n in r.mirror.ctorNames do
      match env.find? n with
      | some (.ctorInfo ci) =>
        unless ci.induct == `CerberusHeapLang.Step do
          throwError "manifest FAIL: row '{r.token}' claims mirror \
            constructor {n}, which is a constructor of {ci.induct}, \
            not of CerberusHeapLang.Step."
      | _ =>
        throwError "manifest FAIL: row '{r.token}' claims mirror \
          constructor {n}, which is not a constructor in the \
          environment."
      if claimed.contains n then
        throwError "manifest FAIL: mirror constructor {n} is claimed \
          by more than one row — one semantic coverage point per \
          constructor (audit F-03 acceptance)."
      claimed := claimed.push n
  for c in stepInfo.ctors do
    unless claimed.contains c do
      throwError "manifest FAIL: mirror constructor {c} has NO \
        manifest row — the Step relation was extended without the \
        manifest (fail-closed by design; add it to a row's mirror \
        cell, or give the new construct its own row)."
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
  IO.println "findings F-01/F-09; cone-derived since Phase-1 S1c). Every claims"
  IO.println "surface defers to it: a construct may be claimed at exactly its"
  IO.println "row's level, no more. Enforcement: `scripts/test_unit.sh` gate 4"
  IO.println "(drift + README scope tie)."
  IO.println ""
  IO.println "Row provenance — which parts are DERIVED vs CHECKED vs DECLARED is"
  IO.println "part of the instrument's honesty and is stated in the script"
  IO.println "header: the ROW SET is DERIVED — enumerated from the `Frag` cone's"
  IO.println "constructor list read out of the built environment (rows appear in"
  IO.println "cone declaration order; a cone constructor without a row mapping"
  IO.println "fails the run), and the `Step` mirror's coverage is DERIVED the"
  IO.println "same way (every Step constructor must be claimed by exactly one"
  IO.println "row's mirror cell); `OK` cells are name-and-kind CHECKED in the"
  IO.println "built environment; lane ATTRIBUTIONS and"
  IO.println "consumer-exercises-construct claims are DECLARED (documented"
  IO.println "instrument granularity). The supplementary evaluator row (last)"
  IO.println "owns no constructor and is mechanically barred from claiming any."
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
  IO.println "6. **`Ewseq` wildcard is the S1b DRIFT TEST** (arc plan Phase 1"
  IO.println "   item 7; design record §8 item 8): a NEW non-example construct"
  IO.println "   passed through the GENERIC route — relation rules + cone/"
  IO.println "   decomposition arms + `engine_step_matchU` arms + `wps_wseq` +"
  IO.println "   the consumer regression; the Rules/Wps/Adequacy strata and the"
  IO.println "   Language instance needed ZERO changes, and this generator"
  IO.println "   FAILED CLOSED on the extended Step/Frag constructor lists until"
  IO.println "   this row landed. Ewseq at spec/sym binder patterns stays a"
  IO.println "   registered divergence (README)."
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
