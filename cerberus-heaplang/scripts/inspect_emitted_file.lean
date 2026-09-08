/-
A7 reconnaissance over the actual pinned frontend/link/convert result.
This is an executable inspection, not a proof or a full-file serializer.
All eleven file fields remain in the in-memory object used for execution.
The JSON output contains metadata counts and diagnostics only.

Run via scripts/inspect-emitted-file.sh from the repository root. The
wrapper loads the pinned CerberusFresh implementation and generated native
wrappers so the frontend uses its actual per-TU digest, not the kernel's
opaque witness. The pinned frontendTU owns desugaring/typechecking/translation;
this script supplies the same no-libc, one-TU loading/linking context as
Main.runPipeline and retains the final fresh supply.
-/
import scripts.emitted_frontend
import CerberusHeapLang.Examples.CorpusE0
import CerberusHeapLang.EmittedStdCore
import CerberusHeapLang.EmittedMapChecks
import scripts.derive_file_to_expr

set_option autoImplicit false

namespace EmittedFileInspection

open Lean
open Lem_Basic_classes

private def symbolSummary (symbol : sym) : Json :=
  let .Symbol digest number _ := symbol
  Json.mkObj [("digest", toJson digest), ("number", toJson number),
    ("printed_name", toJson (ppSymbolPretty symbol))]

private def countMap {a b : Type} (map : Fmap a b) : Json :=
  toJson (fmapElements map).length

private def mainBody (f : file core_run_annotation) : IO CerberusHeapLang.CoreExpr := do
  let some mainSym := f.main | throw (IO.userError "linked file has no main")
  let some decl := fmapLookupBy (fun (a b : sym) => ordCompare a b) mainSym f.funs
    | throw (IO.userError "main symbol is absent from linked funs")
  match decl with
  | .Proc _ _ _ _ body => return body
  | _ => throw (IO.userError "main is not a procedure body")

private def inspect [LemFuel] (f : file core_run_annotation) (supply : Nat)
    (digest : String) : IO Json := do
  let stdlibDataMatches :=
    Lean.toExpr (CerberusHeapLang.EmittedFile.mapData f.stdlib) ==
      Lean.toExpr CerberusHeapLang.CorpusA7.T1.data.stdlib
  let stdlibPathsMatch := CerberusHeapLang.EmittedStdCore.intLibraryCheck
    (CerberusHeapLang.EmittedFile.mapComparator
      CerberusHeapLang.EmittedStdCore.referenceCmp f.stdlib)
  unless stdlibDataMatches && stdlibPathsMatch do
    throw (IO.userError "emitted integer-library data/lookup-path check failed")
  let some entry := f.main | throw (IO.userError "linked file has no main")
  let mainPathMatches := CerberusHeapLang.EmittedFile.mapLookupCheck
    (CerberusHeapLang.EmittedFile.mapComparator
      CerberusHeapLang.EmittedStdCore.referenceCmp f.funs)
    CerberusHeapLang.EmittedStdCore.referenceCmp entry
    (CerberusHeapLang.EmittedFile.mapData f.funs)
  unless mainPathMatches do
    throw (IO.userError "emitted main lookup-path check failed")
  let labelUnionMatches := CerberusHeapLang.EmittedMapChecks.mapUnionCheck
    (CerberusHeapLang.EmittedFile.mapComparator
      CerberusHeapLang.EmittedStdCore.referenceCmp f.stdlib)
    (CerberusHeapLang.EmittedFile.mapComparator
      CerberusHeapLang.EmittedStdCore.referenceCmp f.funs)
    CerberusHeapLang.EmittedStdCore.referenceCmp
    (CerberusHeapLang.EmittedFile.mapData f.stdlib)
    (CerberusHeapLang.EmittedFile.mapData f.funs)
  unless labelUnionMatches do
    throw (IO.userError "emitted label-collection union check failed")
  let body ← mainBody f
  let (initial, finalSupply) := initial_driver_state supply f CerbFS.fs_initial_state
  let outcomes ← (CerberusFresh.forceIO (fun () =>
    CerbND.runND (drive f.tagDefs false f ["cmdname"]) initial) : BaseIO _)
  let mut results : List Json := []
  for (status, trace, _) in outcomes do
    match status with
    | .Active result =>
      results := results ++ [Json.mkObj [
        ("status", toJson "active"),
        ("value", toJson (batchExitValue result.dres_core_value)),
        ("blocked", toJson result.dres_blocked),
        ("stdout", toJson result.dres_stdout),
        ("stderr", toJson result.dres_stderr),
        ("trace", toJson trace)]]
    | _ => throw (IO.userError "full-file execution produced a non-active outcome")
  if results.isEmpty then throw (IO.userError "full-file execution produced no outcome")
  return Json.mkObj [
    ("format", toJson "cerberus-demo-file-inspection-v1"),
    ("scope", toJson "metadata and executable observations; not full serialization or an equality certificate"),
    ("ambient_fuel", toJson LemFuel.fuel),
    ("source_digest", toJson digest),
    ("frontend_supply", toJson supply),
    ("after_driver_initialization_supply", toJson finalSupply),
    ("integer_library", Json.mkObj [
      ("reference_namespace", toJson "CerberusHeapLang.CorpusA7.T1"),
      ("stdlib_quotation_match", toJson stdlibDataMatches),
      ("captured_comparator_paths_match", toJson stdlibPathsMatch)]),
    ("main_lookup", Json.mkObj [
      ("captured_comparator_path_match", toJson mainPathMatches)]),
    ("label_collection", Json.mkObj [
      ("captured_union_comparisons_match", toJson labelUnionMatches)]),
    ("file", Json.mkObj [
      ("main", f.main.elim Json.null symbolSummary),
      ("calling_convention", toJson (match f.calling_convention0 with
        | .Normal_callconv => "normal" | .Inner_arg_callconv => "inner-arg")),
      ("tagDefs_entries", countMap f.tagDefs),
      ("stdlib_entries", countMap f.stdlib),
      ("impl_entries", countMap f.impl0),
      ("globs_entries", toJson f.globs.length),
      ("funs_entries", countMap f.funs),
      ("extern_entries", countMap f.extern),
      ("funinfo_entries", countMap f.funinfo),
      ("loop_attributes_entries", countMap f.loop_attributes1),
      ("visible_objects_env_entries", countMap f.visible_objects_env0)]),
    -- Diagnostic only: neither derived BEq nor this one body check is
    -- asserted to establish full-file semantic equality.
    ("body_beq_retained_t1", toJson (body == CerberusHeapLang.CorpusE0.t1Main)),
    ("uncovered_body_kinds", toJson (CerberusHeapLang.CorpusE0.uncoveredKinds body)),
    ("outcomes", toJson results)]

def run : Lean.CoreM Unit := do
  let input ← requiredEnv "CERB_DEMO_CABS_INPUT"
  let output ← requiredEnv "CERB_DEMO_INSPECTION_OUTPUT"
  let runtimeDir ← requiredEnv "CERB_DEMO_RUNTIME"
  let fuelText ← requiredEnv "CERB_DEMO_FUEL"
  let some fuel := fuelText.toNat? | throwError "CERB_DEMO_FUEL must be a natural"
  let _ : LemFuel := ⟨fuel⟩
  let (actualFile, supply, digest) ← loadLinkedFile runtimeDir input
  let report ← inspect actualFile supply digest
  if let some dataOutput ← IO.getEnv "CERB_DEMO_DATA_OUTPUT" then
    let ns ← requiredEnv "CERB_DEMO_DATA_NAMESPACE"
    let term ← EmittedFileQuotation.renderData
      (CerberusHeapLang.EmittedFile.captureData actualFile)
    IO.FS.writeFile dataOutput (
      "/- Generated from the pinned frontend file. Exact data/map trees;\n" ++
      "   captured comparators remain separate parameters. Not an execution proof. -/\n" ++
      "import CerberusHeapLang.EmittedFile\n\nnamespace " ++ ns ++ "\n\n" ++
      s!"def frontendSupply : Nat := {supply}\n\n" ++
      "def data : CerberusHeapLang.EmittedFile.Data :=\n  " ++ term.replace "\n" "\n  " ++
      "\n\nend " ++ ns ++ "\n")
    IO.println s!"wrote emitted-file data: {dataOutput}"
  IO.FS.writeFile output (report.pretty ++ "\n")
  IO.println s!"wrote full-pipeline inspection: {output}"

end EmittedFileInspection

#eval EmittedFileInspection.run
