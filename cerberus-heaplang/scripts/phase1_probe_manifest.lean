/-
phase1_probe_manifest.lean — PHASE-1 PROBE (S1a): the K4 kill-check
demonstrator — the capability manifest generated FROM the unified
cone predicate, mechanically.

Phase 0's generator (capability_manifest.lean) asserts a
hand-authored row list against hand-asserted constructor lists.
This probe shows the Phase-1 upgrade shape: the ROW SET IS
ENUMERATED FROM `FragU`'s constructors read out of the built
environment. There is no hand-written row list to drift:
- every cone constructor MUST have a row mapping — an unmapped
  constructor (someone extends the cone without extending the
  manifest) makes this script THROW (fail-closed, the audit's
  "coverage cannot differ without a failed check");
- every mapped cell is name-and-kind checked in the environment
  (the Phase-0 discipline, kept).

S1c replaces capability_manifest.lean's hand list with this
enumeration over the migrated full cone, and gate 4's committed
output becomes cone-derived. Run (from cerberus-heaplang/):
  ../scripts/capped ~/.elan/bin/lake env lean scripts/phase1_probe_manifest.lean
-/
import CerberusHeapLang

open Lean Meta

namespace Phase1ProbeManifest

/-- Per-constructor row: the linked artifacts, each name-and-kind
    checked. -/
structure RowSpec where
  construct : String
  mirror : List Name       -- StepU constructors (empty = value protocol)
  engineMatch : List Name  -- match/protocol theorems
  complete : List Name     -- completeness direction (empty = one-sided, note says why)
  note : String

/-- The constructor → row mapping. THE ROW SET ITSELF IS NOT LISTED
    HERE — it is enumerated from `FragU`; this mapping must COVER the
    enumeration or the run throws. -/
def rowSpec : Name → Option RowSpec
  | `CerberusHeapLang.FragU.val_pure => some
    { construct := "value delivery (bare)",
      mirror := [],
      engineMatch := [`CerberusHeapLang.outcomesU_done],
      complete := [`CerberusHeapLang.outcomesU_done],
      note := "two-sided under SeqWF (values do not step; PROGRAM-DONE)" }
  | `CerberusHeapLang.FragU.annot_val => some
    { construct := "value delivery (annotated)",
      mirror := [],
      engineMatch := [`CerberusHeapLang.outcomesU_remove_annot],
      complete := [`CerberusHeapLang.outcomesU_remove_annot],
      note := "two-sided (REMOVE-ANNOT tau; no context field read)" }
  | `CerberusHeapLang.FragU.store => some
    { construct := "Eaction Store0 (value operands)",
      mirror := [`CerberusHeapLang.StepU.store],
      engineMatch := [`CerberusHeapLang.engine_step_matchU],
      complete := [`CerberusHeapLang.engine_complete_storeU],
      note := "TWO-SIDED at any MachineCtx" }
  | `CerberusHeapLang.FragU.run => some
    { construct := "Erun (context-discarding jump)",
      mirror := [`CerberusHeapLang.StepU.run],
      engineMatch := [`CerberusHeapLang.engine_step_matchU],
      complete := [],
      note := "ONE-SIDED (match-given-step; refusal channels are \
        failwithI panics, excluded by NotStuck) — documented \
        direction, audit-sanctioned; extern probe restriction" }
  | `CerberusHeapLang.FragU.case_value => some
    { construct := "Ecase, VALUE scrutinee",
      mirror := [`CerberusHeapLang.StepU.case_value],
      engineMatch := [`CerberusHeapLang.engine_step_matchU],
      complete := [`CerberusHeapLang.engine_complete_caseU],
      note := "TWO-SIDED at any MachineCtx (F-01 row GREEN at probe \
        scale: cone + match + completeness + drive regression \
        `case_regression_drive`)" }
  | _ => none

def checkThm (env : Environment) (n : Name) : Except String Unit := do
  match env.find? n with
  | some (.thmInfo _) => pure ()
  | some _ => throw s!"{n} exists but is not a theorem"
  | none => throw s!"{n} does not exist"

def checkCtor (env : Environment) (n : Name) : Except String Unit := do
  match env.find? n with
  | some (.ctorInfo _) => pure ()
  | some _ => throw s!"{n} exists but is not a constructor"
  | none => throw s!"{n} does not exist"

#eval show CoreM Unit from do
  let env ← getEnv
  -- THE ENUMERATION: the row set is FragU's constructor list, read
  -- from the environment (nothing hand-asserted).
  let some (.inductInfo info) := env.find? `CerberusHeapLang.FragU
    | throwError "probe manifest FAIL: FragU not found"
  IO.println "# Phase-1 probe manifest (GENERATED FROM FragU — K4 demonstrator)"
  IO.println ""
  IO.println "| Cone constructor | Construct | Mirror (StepU) | Engine match | Completeness | Note |"
  IO.println "|---|---|---|---|---|---|"
  for ctor in info.ctors do
    let some spec := rowSpec ctor
      | throwError "probe manifest FAIL: cone constructor {ctor} has NO \
          manifest row mapping — the cone was extended without the \
          manifest (fail-closed by design; add the row)."
    for n in spec.mirror do
      if let .error e := checkCtor env n then
        throwError "probe manifest FAIL ({ctor}): {e}"
    for n in spec.engineMatch ++ spec.complete do
      if let .error e := checkThm env n then
        throwError "probe manifest FAIL ({ctor}): {e}"
    let fmt (ns : List Name) (empty : String) : String :=
      if ns.isEmpty then empty
      else String.intercalate ", " (ns.map (fun n => s!"`{n}`"))
    IO.println s!"| `{ctor}` | {spec.construct} | \
      {fmt spec.mirror "— (value protocol)"} | \
      {fmt spec.engineMatch "—"} | \
      {fmt spec.complete "ONE-SIDED (see note)"} | {spec.note} |"
  IO.println ""
  IO.println s!"Enumerated {info.ctors.length} cone constructors from the built environment."

end Phase1ProbeManifest
