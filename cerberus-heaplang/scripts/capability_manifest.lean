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
  name-and-kind plus derived coverage is the checked level. An `OK`
  cell means the NAMED DECLARATION EXISTS with the stated kind — NOT
  that its proof depends on the row's logic rule (the 2026-09-01
  skeptical re-audit's R-04: this gate validates declarations, not
  proof flow; dependency-staged certification is alloc-arc P3, the
  registered mover). Hence the machine-readable line rename
  (2026-09-01 P0, the audit's option b): the former FULL-ROW output
  is now CORE-DRIVE-ROW, with the logic / total / production lanes
  reported separately.

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
cone / engine-match / partial-adequacy / consumer; the logic, total
and production lanes are reported separately in the machine-readable
lines (2026-09-01 P0: the former FULL-ROW aggregate is renamed
CORE-DRIVE-ROW — it certifies the drive-lane core plus a logic rule
EXISTING, and says nothing about the total/production lanes or about
proof-flow dependency; re-audit R-04). -/
def Row.coreCells (r : Row) : List Cell :=
  [r.mirror, r.cone, r.engineMatch, r.partialLane, r.consumer]

def Row.exportable (r : Row) : Bool :=
  !(r.coreCells.any Cell.isRed)

/-- The former `fullRow` (renamed, 2026-09-01 P0 — re-audit R-04
option b): core drive-lane cells green AND a logic rule exists.
Deliberately NOT "full": the total and production lanes are excluded
and reported on their own lines. -/
def Row.coreDriveRow (r : Row) : Bool :=
  r.exportable && !(r.logic.isRed)

def Row.level (r : Row) : String :=
  if !r.exportable then "LOCAL RULE ONLY (RED)"
  else if r.logic.isRed then "ADEQUACY-EXPORTABLE (no logic rule)"
  else "CERTIFIED (drive lane)"

/-- Total-lane cell: the wpt rule(s) + the total-equation
    consumer(s) (Phase 3; see Notes 2). -/
def totalVia (rules consumers : List Name) : Cell :=
  .thms (rules ++ consumers)

/-- Constructs with no total rule yet (see Notes 2). -/
def noTotal (why : String) : Cell :=
  .red s!"no total rule yet ({why}); see Notes 2"

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
      totalLane := totalVia [`CerberusHeapLang.wpt_ofVal]
        [`CerberusHeapLang.fib_certified_total, `CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod,
        `CerberusHeapLang.fib_certified_production],
      consumer := .thms [`CerberusHeapLang.exhibitA_engine] }
  | `CerberusHeapLang.Frag.store => some
    { token := "store", construct := "Eaction Store0 (value operands)",
      mirror := .ctors [`CerberusHeapLang.Step.store],
      logic := .thms [`CerberusHeapLang.wp_store, `CerberusHeapLang.wps_store],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_store,
        `CerberusHeapLang.engine_complete_storeU]
        (note := "TWO-SIDED at any MachineCtx"),
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_store_at,
        `CerberusHeapLang.wpt_store_cell_at, `CerberusHeapLang.wpt_store_cell]
        [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod,
        `CerberusHeapLang.counter_loop_certified_production,
        `CerberusHeapLang.list_reverse_certified_production],
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
      totalLane := totalVia [`CerberusHeapLang.wpt_load_at,
        `CerberusHeapLang.wpt_load_cell_at] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod,
        `CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.exhibitA_engine,
        `CerberusHeapLang.array_sum_certified] }
  | `CerberusHeapLang.Frag.create => some
    { token := "create", construct := "Eaction Create0",
      mirror := .ctors [`CerberusHeapLang.Step.create],
      logic := .thms [`CerberusHeapLang.wps_create,
        `CerberusHeapLang.wps_create_cursor_internal]
        (note := "alloc arc P1: the PUBLIC wps_create takes the abstract capacity allocCap (req :: rest) and binds an existential pointer (statement cursor-free); the exact-cursor form is wps_create_cursor_internal (heap-implementation use only); OOM excluded by the plan-fit inside allocCap — see Notes 4"),
      engineMatch := .thms [`CerberusHeapLang.step_ctx_create],
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_create]
        [`CerberusHeapLang.alloc_create_launch_smoke,
         `CerberusHeapLang.progAProd_wpt,
         `CerberusHeapLang.ctrProd_wpt,
         `CerberusHeapLang.lrProd_wpt],
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod,
        `CerberusHeapLang.counter_loop_certified_production,
        `CerberusHeapLang.list_reverse_certified_production]
        (note := "ALL THREE are WHOLE-PROGRAM create-rule consumers (alloc arc P2, the R-02 conversion): each program BINDS its engine-created pointer(s), the creates cross the PUBLIC wpt_create from abstract capacity plans (progAProd_wpt / ctrProd_wpt / lrProd_wpt), and the pipeline arrows are the generic wpt_driver_done_alloc → prod_run_eqJ — zero operational proof terms in any positive exhibit (grep transcript, docs/2026-09-01_p2-notes.md)"),
      consumer := .thms [`CerberusHeapLang.alloc_create_launch_smoke,
        `CerberusHeapLang.alloc_two_creates_wps,
        `CerberusHeapLang.alloc_create_wpt,
        `CerberusHeapLang.struct_create_store_wps,
        `CerberusHeapLang.struct_create_store_adequacy]
        (note := "alloc_create_launch_smoke is the P1 engine-facing chain-closer (driveU .done at fuel 2 via wpt_create + wpt_engine_boundU_alloc from prodMem₀); alloc_two_creates_wps / alloc_create_wpt are the wps/wpt-level local consumers of the PUBLIC rules; struct_create_store_wps is a PUBLIC-rule whole-program client over allocCap (alloc arc P2 item 1 — the program binds the fresh pointer; no cursor vocabulary) with its engine-facing adequacy consumer struct_create_store_adequacy launched through spike_engine_adequacy_alloc (P2 item 2); the HEADLINE allocating exhibits are not yet consumers (R-02, P2 items 3-5)") }
  | `CerberusHeapLang.Frag.sseq => some
    { token := "sseq-wild", construct := "Esseq, wildcard pattern",
      mirror := .ctors [`CerberusHeapLang.Step.sseq_pure,
        `CerberusHeapLang.Step.sseq_annot, `CerberusHeapLang.Step.sseq_ctx],
      logic := .thms [`CerberusHeapLang.wp_sseq, `CerberusHeapLang.wps_seq],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_beta_pure,
        `CerberusHeapLang.step_ctx_beta_annot],
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_seq] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod,
        `CerberusHeapLang.counter_loop_certified_production,
        `CerberusHeapLang.list_reverse_certified_production],
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
      totalLane := totalVia [`CerberusHeapLang.wpt_annot] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.exhibitA_prod,
        `CerberusHeapLang.counter_loop_certified_production,
        `CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.exhibitA_engine] }
  | `CerberusHeapLang.Frag.save => some
    { token := "save", construct := "Esave (block entry, value-shaped params)",
      mirror := .ctors [`CerberusHeapLang.Step.save],
      logic := .thms [`CerberusHeapLang.wps_save],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_save],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_save]
        [`CerberusHeapLang.fib_certified_total, `CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.fib_certified_production,
        `CerberusHeapLang.counter_loop_certified_production,
        `CerberusHeapLang.list_reverse_certified_production],
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
      totalLane := totalVia [`CerberusHeapLang.wpt_if_true,
        `CerberusHeapLang.wpt_if_false] [`CerberusHeapLang.fib_certified_total, `CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.fib_certified_production,
        `CerberusHeapLang.counter_loop_certified_production,
        `CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.fib_certified] }
  | `CerberusHeapLang.Frag.run => some
    { token := "run", construct := "Erun (context-discarding jump)",
      mirror := .ctors [`CerberusHeapLang.Step.run],
      logic := .thms [`CerberusHeapLang.wps_run],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_run]
        (note := "ONE-SIDED — match-given-step, the direction adequacy consumes; jump refusal channels are failwithI panics = absence of a step; see Notes 7"),
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_run]
        [`CerberusHeapLang.fib_certified_total, `CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.fib_certified_production,
        `CerberusHeapLang.counter_loop_certified_production,
        `CerberusHeapLang.list_reverse_certified_production],
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
      totalLane := totalVia [`CerberusHeapLang.wpt_seq_spec] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.array_sum_certified,
        `CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.pure_sym => some
    { token := "pure-sym", construct := "Epure exit at PEsym shape",
      mirror := .ctors [`CerberusHeapLang.Step.pure_eval]
        (note := "certified at PEsym shape — Soundness stepDischarge_pure_sym"),
      logic := .thms [`CerberusHeapLang.wps_pure],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_pure_sym],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_pure]
        [`CerberusHeapLang.fib_certified_total, `CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.fib_certified_production,
        `CerberusHeapLang.counter_loop_certified_production,
        `CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.fib_certified] }
  | `CerberusHeapLang.Frag.load_op => some
    { token := "load-op", construct := "Load0 operand-evaluation step (ACTION_EVAL)",
      mirror := .ctors [`CerberusHeapLang.Step.load_eval],
      logic := .thms [`CerberusHeapLang.wps_load_eval],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_load_eval],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_load_eval] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.array_sum_certified] }
  | `CerberusHeapLang.Frag.sseq_sym => some
    { token := "sseq-sym", construct := "Esseq, plain-symbol-binder pattern (bare values)",
      mirror := .ctors [`CerberusHeapLang.Step.sseq_sym_pure],
      logic := .thms [`CerberusHeapLang.wps_seq_sym],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_beta_sym_pure],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_seq_sym] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.memop_vals => some
    { token := "memop-ptreq", construct := "Ememop PtrEq (value operands)",
      mirror := .ctors [`CerberusHeapLang.Step.memop_ptreq],
      logic := .thms [`CerberusHeapLang.wps_memop_ptreq],
      engineMatch := .thms [`CerberusHeapLang.step_ctx_memop],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_memop_ptreq] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.memop_op => some
    { token := "memop-op", construct := "Ememop PtrEq, operand-evaluation step",
      mirror := .ctors [`CerberusHeapLang.Step.memop_eval],
      logic := .thms [`CerberusHeapLang.wps_memop_eval],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_memop_eval],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_memop_eval] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.list_reverse_certified_production],
      consumer := .thms [`CerberusHeapLang.list_reverse_certified] }
  | `CerberusHeapLang.Frag.store_op => some
    { token := "store-op", construct := "Store0 operand-evaluation step (ACTION_EVAL)",
      mirror := .ctors [`CerberusHeapLang.Step.store_eval],
      logic := .thms [`CerberusHeapLang.wps_store_eval],
      engineMatch := .thms [`CerberusHeapLang.stepDischarge_store_eval],
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      totalLane := totalVia [`CerberusHeapLang.wpt_store_eval] [`CerberusHeapLang.list_reverse_certified_total],
      prodLane := .thms [`CerberusHeapLang.list_reverse_certified_production],
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
      totalLane := noTotal "no wpt case rule — mechanical analog of wps_case_value, no consumer",
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
      totalLane := noTotal "no wpt wseq rule — mechanical analog of wps_wseq, no consumer",
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
    totalLane := totalVia [] [`CerberusHeapLang.fib_certified_total,
      `CerberusHeapLang.list_reverse_certified_total],
    prodLane := .thms [`CerberusHeapLang.fib_certified_production],
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
  IO.println "instrument granularity). An `OK` cell therefore means the NAMED"
  IO.println "DECLARATION EXISTS with the stated kind — NOT that its proof"
  IO.println "depends on the row's logic rule (2026-09-01 skeptical re-audit"
  IO.println "R-04: this gate validates declarations, not proof flow;"
  IO.println "dependency-staged certification is alloc-arc P3). The"
  IO.println "supplementary evaluator row (last)"
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
  IO.println "2. **The total lane is LIVE** (foundations Phase 3; audit F-02"
  IO.println "   remediated): the total statement judgment `wpt` (Wpt.lean) has"
  IO.println "   a MANDATORY back-edge variant decrease (the jump clause's"
  IO.println "   `∃ m, 1 + m ≤ k` against variant-indexed label preconditions),"
  IO.println "   collapses into the pinned Iris TotalWeakestPre (`wpt_sound`),"
  IO.println "   and carries BOTH adequacy halves (TotalAdequacy.lean):"
  IO.println "   termination over the unified relation"
  IO.println "   (`wpt_strongly_normalizing` — `twp_total` consumed as-is) and"
  IO.println "   the generic measure→drive-fuel simulation"
  IO.println "   (`wpt_engine_boundU`/`wpt_engine_boundJ`). Consumers:"
  IO.println "   `fib_certified_total` (unconditional driveJ equation at 2·n+4,"
  IO.println "   statement unchanged, proof a corollary — zero Step"
  IO.println "   constructors) + `fib_terminates`;"
  IO.println "   `list_reverse_certified_total` (the derived bound 13·|xs|+7) +"
  IO.println "   `list_reverse_terminates`. Negative test:"
  IO.println "   `diverge_total_unprovable` (DivergeExhibit — the self-jump"
  IO.println "   loop's total derivation is FALSE). RED total cells:"
  IO.println "   Ecase/Ewseq have no wpt rule yet (mechanical analogs of"
  IO.println "   their wps rules, no consumer — registered follow-ons)."
  IO.println "   create's total rule landed in alloc arc P1 (`wpt_create`,"
  IO.println "   derived cost bound 2 = one create step + one pure-value"
  IO.println "   delivery; consumer: the launcher smoke, Notes 4)."
  IO.println "   `blockSpecs_intro_variant` is RETIRED, replaced by"
  IO.println "   `blockSpecsT` (Wpt.lean): the smaller-measure discipline is"
  IO.println "   the judgment's jump clause, never an optional hypothesis."
  IO.println "3. **The production lane is LIVE for loop constructs** (Phase 5;"
  IO.println "   audit F-05 closed): the proc-carrying, populated-label"
  IO.println "   scheduler collapse (DriverCollapse `loop_step_frag` +"
  IO.println "   ProdLoop `wpt_driver_done`) makes loop programs runnable on"
  IO.println "   the SHIPPED pipeline — `fib_certified_production`"
  IO.println "   (ProdLoopExhibit) concludes about"
  IO.println "   `CerbND.runND (Driver.drive ...) (initial_driver_state ...)`"
  IO.println "   from the cold start, no package drive/driveJ in the statement."
  IO.println "   The former misnamed theorem is RENAMED"
  IO.println "   `counter_loop_certified_registration` (the naming debt paid):"
  IO.println "   it is the driveJ-lane REGISTRATION tie, kept as a lemma."
  IO.println "   The counter loop (`counter_loop_certified_production` — a"
  IO.println "   SELF-CONTAINED program: the cell engine-created on the cold"
  IO.println "   start) and the flagship reversal's demo instance"
  IO.println "   (`list_reverse_certified_production` — the two-node chain"
  IO.println "   engine-built by creates + field stores, then reversed by the"
  IO.println "   authored loop) conclude about the same shipped composite."
  IO.println "   Straight-line constructs reach the shipped pipeline via"
  IO.println "   `exhibitA_prod` — since alloc arc P2 step 3 a WHOLE-PROGRAM"
  IO.println "   logic proof (progAProd_wpt through the PUBLIC wpt_create,"
  IO.println "   collapsed by the generic wpt_driver_done_alloc /"
  IO.println "   prod_run_eqJ). The counter and reversal production proofs"
  IO.println "   are likewise WHOLE-PROGRAM logic proofs (P2 steps 4-5,"
  IO.println "   R-02 closed): the programs BIND their engine-created"
  IO.println "   pointers, ctrProd_wpt/lrProd_wpt carry create + stores +"
  IO.println "   loop in one total judgment (the reversal consuming the"
  IO.println "   GENERIC list logic verbatim at existential engine-picked"
  IO.println "   ids, transported by wpt_mono_Ls); the total judgment"
  IO.println "   drives the loop suffixes only. fib (no heap) is the fully"
  IO.println "   logic-driven positive control."
  IO.println "4. **`create` has PUBLIC partial+total rules, LAUNCHABLE**"
  IO.println "   (alloc arc P1; the R-01 repair — rules + launch landed,"
  IO.println "   closure test pending P2's whole-program consumers): the"
  IO.println "   public `wps_create`/`wpt_create` take the abstract finite"
  IO.println "   allocation capacity `allocCap (req :: rest)` (Heap.lean —"
  IO.println "   internally the cursor fragment + a pure plan-fit; the OOM"
  IO.println "   kill arm is excluded by the plan, never assumed away) and"
  IO.println "   bind an EXISTENTIAL pointer; their statements contain no"
  IO.println "   AllocCursor/lastAddress/nextAllocId/freshBase/cursorOwn"
  IO.println "   (grep-checked, docs/2026-09-01_p1-notes.md). The exact-"
  IO.println "   cursor rules are internal (`wps_create_cursor_internal`/"
  IO.println "   `wpt_create_cursor_internal`, heap-implementation use only)."
  IO.println "   LAUNCH: the allocation-aware launchers"
  IO.println "   (`spike_step_adequacy_alloc`, `wpt_engine_boundU/J_alloc`,"
  IO.println "   `wpt_strongly_normalizing_alloc`) grant `allocCap` from"
  IO.println "   real Cerberus memory through the one `launchResources`"
  IO.println "   helper under `LaunchCoh` (cursor key 0 NONEMPTY; CohG's"
  IO.println "   allocator-health facts non-vacuous). Chain-closing"
  IO.println "   consumer: `alloc_create_launch_smoke` (AllocExhibit — a"
  IO.println "   driveU `.done` equation at fuel exactly 2 from prodMem₀)."
  IO.println "   PARTIAL-LANE WHOLE-PROGRAM CONSUMER (alloc arc P2 items"
  IO.println "   1-2): `struct_create_store_wps` is a PUBLIC-rule client"
  IO.println "   over `allocCap` (the program binds the fresh pointer;"
  IO.println "   no cursor vocabulary), exported to the engine by"
  IO.println "   `struct_create_store_adequacy` through"
  IO.println "   `spike_engine_adequacy_alloc` — deleting the public"
  IO.println "   `wps_create` breaks it (the R-01 partial-lane closure"
  IO.println "   consumer). The public rules also export the fresh"
  IO.println "   pointer's pure address bounds (0 < addrOf p < 2^64),"
  IO.println "   carried by `allocCap`'s machine-bounded hidden cursor."
  IO.println "   TOTAL-LANE WHOLE-PROGRAM CONSUMER (P2 step 3):"
  IO.println "   `progAProd_wpt`/`exhibitA_prod` — the complete"
  IO.println "   create/store/load through the PUBLIC `wpt_create` and the"
  IO.println "   allocation-aware driver collapse `wpt_driver_done_alloc`."
  IO.println "   LOOP-LANE WHOLE-PROGRAM CONSUMERS (P2 steps 4-5):"
  IO.println "   `ctrProd_wpt`/`counter_loop_certified_production` (one-"
  IO.println "   request plan) and `lrProd_wpt`/"
  IO.println "   `list_reverse_certified_production` (two-request plan,"
  IO.println "   the generic list logic consumed verbatim at existential"
  IO.println "   engine-picked ids). R-01 and R-02 are CLOSED (closure"
  IO.println "   table, docs/2026-09-01_alloc-arc-plan.md; plant"
  IO.println "   transcripts in docs/2026-09-01_p2-notes.md)."
  IO.println "5. **Interior (sub-allocation) access is GENERIC** (Phase 2,"
  IO.println "   F-04 retired): one typed-subrange load and one store rule"
  IO.println "   (`wps_load_at`/`wps_store_at` over views; whole-cell forms"
  IO.println "   `wps_load_cell_at`/`wps_store_cell_at`), certified once"
  IO.println "   against loadM/storeM. The former int-specific and node-"
  IO.println "   specific interior rules are DELETED; array element, node"
  IO.println "   field, and struct field rules are client instances inside"
  IO.println "   their exhibit modules."
  IO.println "6. **`Ewseq` wildcard is the S1b DRIFT TEST** (arc plan Phase 1"
  IO.println "   item 7; design record §8 item 8): a NEW non-example construct"
  IO.println "   passed through the GENERIC route — relation rules + cone/"
  IO.println "   decomposition arms + `engine_step_matchU` arms + `wps_wseq` +"
  IO.println "   the consumer regression; the Rules/Wps/Adequacy strata and the"
  IO.println "   Language instance needed ZERO changes, and this generator"
  IO.println "   FAILED CLOSED on the extended Step/Frag constructor lists until"
  IO.println "   this row landed. Ewseq at spec/sym binder patterns stays a"
  IO.println "   registered divergence (README)."
  IO.println "7. **Direction semantics of the engine-match column** (arc plan"
  IO.println "   Phase-1 item 3; audit-sanctioned one-sidedness): the certified"
  IO.println "   direction for EVERY row is MATCH-GIVEN-STEP — one theorem over"
  IO.println "   the whole cone at any MachineCtx, `engine_step_matchU`"
  IO.println "   (Soundness.lean): wherever the mirror steps at a cone"
  IO.println "   configuration, the engine's discharged behavior list is exactly"
  IO.println "   the matching singleton. That is the direction the WP-driven"
  IO.println "   adequacy consumes (`NotStuck` supplies the mirror step at every"
  IO.println "   reachable configuration); the refusal channels the other"
  IO.println "   direction would classify are failwithI panics, mirrored"
  IO.println "   fail-closed as absence of a step. ADDITIONALLY two-sided:"
  IO.println "   the straight-line profile as a whole (`engine_complete` — the"
  IO.println "   per-configuration classification over `StraightFrag`, its"
  IO.println "   domain being the straight-line completeness instance) and the"
  IO.println "   per-construct completeness pairs `engine_complete_storeU` /"
  IO.println "   `engine_complete_caseU` (store, case — noted on their rows)."
  IO.println "   Rows without a completeness entry are ONE-SIDED, deliberately."
  IO.println ""
  IO.println "## Machine-readable scope lines (consumed by test_unit.sh gate 4)"
  IO.println ""
  IO.println "Line semantics (2026-09-01 P0 — the skeptical re-audit's R-04,"
  IO.println "option b: the former FULL-ROW aggregate is RENAMED, lanes"
  IO.println "reported separately): CORE-DRIVE-ROW = the drive-lane core"
  IO.println "cells (mirror/cone/engine-match/partial-adequacy/consumer)"
  IO.println "green AND a logic rule EXISTS — it says nothing about the"
  IO.println "total or production lanes, about launchability, or about"
  IO.println "proof-flow dependency (lane membership is cell non-redness,"
  IO.println "name-and-kind checked, NOT dependency-traced — R-04's staged"
  IO.println "dependency certification is alloc-arc P3). The per-lane lines"
  IO.println "list the rows whose respective cell is non-red. NB `create`"
  IO.println "joined TOTAL-LANE at alloc arc P1 (`wpt_create` + the launcher"
  IO.println "smoke); its PRODUCTION-LANE membership is still the MIXED"
  IO.println "exhibits (R-02, pending P2) — see Notes 4."
  IO.println ""
  let exportable := rows.filter (·.exportable) |>.map (·.token)
  let coreDriveRows := rows.filter (·.coreDriveRow) |>.map (·.token)
  let logicRows := rows.filter (fun r => !r.logic.isRed) |>.map (·.token)
  let totalRows := rows.filter (fun r => !r.totalLane.isRed) |>.map (·.token)
  let prodRows := rows.filter (fun r => !r.prodLane.isRed) |>.map (·.token)
  let localOnly := rows.filter (fun r => !r.exportable) |>.map (·.token)
  IO.println "```"
  IO.println s!"ADEQUACY-EXPORTABLE: {" ".intercalate exportable}"
  IO.println s!"CORE-DRIVE-ROW: {" ".intercalate coreDriveRows}"
  IO.println s!"LOGIC-RULE-LANE: {" ".intercalate logicRows}"
  IO.println s!"TOTAL-LANE: {" ".intercalate totalRows}"
  IO.println s!"PRODUCTION-LANE: {" ".intercalate prodRows}"
  IO.println s!"LOCAL-RULE-ONLY: {" ".intercalate localOnly}"
  IO.println "```"
