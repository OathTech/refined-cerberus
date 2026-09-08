/- The shared actual one-TU/no-libc loading path for inspection and
   generated-data comparison. Run through the capped wrapper, which loads
   the pinned native digest implementation. -/
import Main

set_option autoImplicit false

namespace EmittedFileInspection

def requiredEnv (name : String) : IO String := do
  match ← IO.getEnv name with
  | some value =>
    if value.isEmpty then throw (IO.userError s!"empty environment variable {name}")
    return value
  | none => throw (IO.userError s!"missing environment variable {name}")

private def parseLibrary (path : String) : IO CoreParser.CoreFile := do
  let content ← IO.FS.readFile path
  match CoreParser.parseLibraryFile path content with
  | .ok parsed => return parsed
  | .error message => throw (IO.userError s!"{path}: {message}")

/-- Exact one-TU, no-libc loading path used by Main.runPipeline. The
    caller consumes the full converted file and final frontend supply. -/
def loadLinkedFile [LemFuel] (runtimeDir input : String) :
    IO (file core_run_annotation × Nat × String) := do
  let text ← IO.FS.readFile input
  let (digest, tunit) ← match CabsImport.parseJson text with
    | .ok parsed => pure parsed
    | .error message => throw (IO.userError s!"{input}: {message}")
  -- A fresh driver process loads the libraries before setting any TU digest.
  let _ ← (CerberusFresh.setDigestIO "" : BaseIO Unit)
  let stdFile ← parseLibrary (runtimeDir ++ "/std.core")
  let (ailnames, stdFunMap) := loadCoreStdlib stdFile
  let implFile ← parseLibrary
    (runtimeDir ++ "/impls/gcc_4.9.0_x86_64-apple-darwin10.8.0.impl")
  let coreImpl := loadCoreImpl implFile
  let coreEvalStuff := (ailnames, stdFunMap, coreImpl)
  let _ ← (CerberusFresh.setDigestIO digest : BaseIO Unit)
  -- A misloaded native seam must fail loudly.
  let direct ← (CerberusFresh.digestIO () : BaseIO String)
  let forced ← (CerberusFresh.forceIO (fun () => CerberusFresh.digest ()) : BaseIO String)
  unless direct == digest && forced == digest do
    throw (IO.userError "pinned native digest reads do not match the Cabs digest")
  let (coreFile, supply) ←
    match ← frontendTU true 0 coreEvalStuff ailnames stdFunMap coreImpl tunit with
    | .ok translated => pure translated
    | .error code => throw (IO.userError s!"frontendTU failed with code {code}")
  let linked ← match link [coreFile] with
    | .Result linked => pure linked
    | .Exception (loc, _) =>
      throw (IO.userError s!"link failed at {CerbLocation.stringFromLocation loc}")
  return (convert_file linked, supply, digest)

end EmittedFileInspection
