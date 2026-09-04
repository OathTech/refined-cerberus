/-
parametric_inventory.lean — READ-ONLY measurement, ON DEMAND (not run by
the gate — [AGENT 2026-09-04] decision, docs/2026-09-04_ar5-manifest-notes.md
§4: the cheap text-based twin of its client-module section,
scripts/boundary_check.sh, IS a gate speedbump; this proof-term instrument
stays a measurement without a verdict, run at design points).
Born for the 2026-09-02 parametric-semantics spike
(docs/2026-09-02_parametric-semantics-spike.md, DEFERRED).

FAIL-CLOSED CONFIGURATION (ar5-manifest 2026-09-04, the external audit's
Finding 2): every export seed below MUST resolve to a declaration of the
built environment — a missing name is a HARD FAILURE (nonzero exit), never
a `(MISSING)` row; the client-module list is READ from the one authoritative
module classification scripts/module_classes.tsv (classes `positive-client`
and `declared-smoke`), which must be complete and exact (every package
module classified, every classified module present).

For each rule theorem (Rules/Wps/Wpt) and the named export seeds, split the
constants of the PROOF TERM into "statement" (in the type) and "proof-only"
(in the value, not the type), then classify DIRECT (the theorem's own value)
vs TRANSITIVE (closure through CerberusHeapLang constants only; engine/Iris/
Lean constants are leaves, never expanded) usage of:
  StepDef  — the `Step` inductive, its constructors/rec/casesOn
  StepLem  — theorems in the `Step.` namespace (inversions, canonical)
  Env      — map OPERATIONS: LemLib `fmapAddBy`/`fmapLookupBy`, `Std.TreeMap*`,
             generated `update_env*`/`lookup_env*`, package `bindArgs`/
             `bindSaveParams`/`envAdd`, EnvLaws (bare `Fmap`/`EnvStack` types
             are statement vocabulary and deliberately NOT counted)
  Ghost    — CohG/cursor/GenHeap/interp internals of Heap.lean
  Judg     — `wps.pre`/`wpt.pre` (judgment unfolded by definition)
  Engine   — generated cerberus-lean constants (+ LemLib runtime)
  Layout   — the tag-environment-dependent memory functions
             (sizeofCtype, memValueToBytes, reconstructValue, loadM,
             storeM, allocateObject, alignofIval, arrayShiftPtrval,
             isAtomicMemberAccess) — the re-pin's TagDefs parameter set.
NB: Iris redefines ` || ` (SetNotation.lean:16), hence `Bool.or`/`.any`.
Run (from cerberus-heaplang/, box free, capped):
  CERB_MEM_MAX=40G ../scripts/capped ~/.elan/bin/lake env lean scripts/parametric_inventory.lean
-/
import CerberusHeapLang

open Lean

namespace ParametricInventory

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

def isPkg (env : Environment) (n : Name) : Bool :=
  (modOf env n).getRoot == `CerberusHeapLang

def nonEngineRoots : List Name :=
  [`CerberusHeapLang, `Iris, `Init, `Lean, `Std, `Batteries, `Qq, .anonymous]

def isEngine (env : Environment) (n : Name) : Bool :=
  !(nonEngineRoots.contains (modOf env n).getRoot)

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some (.thmInfo _) => true | _ => false

def valueConsts (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo t => t.value.getUsedConstants
  | .defnInfo d => d.value.getUsedConstants
  | .opaqueInfo o => o.value.getUsedConstants
  | _ => #[]

def hasSub (n : Name) (subs : List String) : Bool :=
  let s := n.toString
  subs.any fun t => (s.splitOn t).length > 1

def stepNs : Name := `CerberusHeapLang.Step
def isStepDef (env : Environment) (n : Name) : Bool :=
  Bool.and (Bool.or (n == stepNs) (stepNs.isPrefixOf n)) (!isThm env n)
def isStepLem (env : Environment) (n : Name) : Bool :=
  Bool.and (stepNs.isPrefixOf n) (isThm env n)
def isEnv (env : Environment) (n : Name) : Bool :=
  Bool.or (hasSub n ["fmapAddBy", "fmapLookupBy", "fmapDeleteBy", "TreeMap", "update_env",
                     "lookup_env", "bindArgs", "bindSaveParams", "envAdd", "SymFrame",
                     "symOrd", "symKey"])
          (modOf env n == `CerberusHeapLang.EnvLaws)
/-- The ghost maps, the coupling invariant, the interpretations and the
    component-level (`byteOwn`/`bytesOwn`/`metaOwn`) unfoldings. NOT
    counted: `pointsToCell_cellOwn_iff` (a law between two PUBLIC
    bundles — `pointsToCell` is the ∃-packaged `cellOwn`; alloc arc P4
    refinement) and the pure allocation-PLAN model (`isPlan` below). -/
def isGhost (n : Name) : Bool :=
  Bool.and (n != `CerberusHeapLang.pointsToCell_cellOwn_iff)
    (hasSub n ["CohG", "cursorOwn", "cursorInterp", "budgetInterp", "budgetAuth",
            "cursorHeap", "byteInterp", "metaInterp", "byteHeap", "metaHeap",
            "stateInterp_eq", "stateInterp_iff", "pointsToCell_iff",
            "cellOwn_iff", "pointsToView_iff", "bytesOwn",
            "byteOwn", "metaOwn", "MetaByteOf", "LaunchCoh", "genHeapInterp", "GenHeap"])
/-- The pure allocation-budget model (K2.5: the cursor arithmetic
    `allocCost`/`headroom`/`freshBase` a launch's budget-fit fact is
    computed with) — separated from the ghost maps at P4. -/
def isPlan (n : Name) : Bool :=
  hasSub n ["AllocCursor", "allocCost", "planCost", "headroom", "freshBase"]
def judgNs : List Name := [`CerberusHeapLang.wps.pre, `CerberusHeapLang.wpt.pre]
def isJudg (n : Name) : Bool := judgNs.any fun j => Bool.or (n == j) (j.isPrefixOf n)
def layoutSubs : List String :=
  ["sizeofCtype", "memValueToBytes", "reconstructValue", "loadM", "storeM",
   "allocateObject", "alignofIval", "arrayShiftPtrval", "isAtomicMemberAccess"]
def isLayout (env : Environment) (n : Name) : Bool := Bool.and (isEngine env n) (hasSub n layoutSubs)

/-- Auto-generated companions (`injEq`, `ctorIdx`, `match_*`, `casesOn`, …) are not "definitions used". -/
def isAuto (n : Name) : Bool :=
  Bool.or n.isInternalDetail
    (hasSub n ["injEq", "ctorIdx", "match_", "casesOn", "noConfusion", "sizeOf", ".rec", "below", "brecOn", "inj"])
/-- An engine DEFINITION (function/lemma/instance), as opposed to a type or constructor. -/
def isEngineDef (env : Environment) (n : Name) : Bool :=
  Bool.and (Bool.and (isEngine env n) (!isAuto n))
    (match env.find? n with
     | some (.defnInfo _) => true | some (.opaqueInfo _) => true | some (.thmInfo _) => true
     | _ => false)

abbrev DepM := StateM (Std.HashMap Name (Array Name))

/-- type ∪ value constants of a constant, memoized. -/
def depsOf (env : Environment) (n : Name) : DepM (Array Name) := do
  if let some d := (← get).get? n then return d
  let d := match env.find? n with
    | some ci => ci.type.getUsedConstants ++ valueConsts ci
    | none => #[]
  modify (·.insert n d)
  return d

/-- Closure from seeds through package THEOREMS only (a lemma's statement
    and proof are what "using it" commits to); package DEFINITIONS and all
    engine/Iris/Lean constants are leaves, never expanded — so a rule that
    reaches `Step` does not thereby "reach" `CerbMem.storeM` through the
    constructor types. -/
partial def cone (env : Environment) (seeds : Array Name) : DepM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack := seeds
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if !(Bool.and (isPkg env c) (isThm env c)) then continue
    for d in ← depsOf env c do
      if !seen.contains d then stack := stack.push d
  return seen

structure Row where
  name : String
  stepDefD : Nat := 0
  stepDefT : Bool := false
  stepLemD : Nat := 0
  envD : Nat := 0
  envT : Nat := 0
  ghostD : Nat := 0
  ghostT : Nat := 0
  planD : Nat := 0
  judgD : Nat := 0
  engD : Array Name := #[]
  engTyD : Nat := 0
  engT : Nat := 0
  layoutD : Array String := #[]
  layoutT : Nat := 0

def short (n : Name) : String :=
  let s := n.toString
  if s.startsWith "CerberusHeapLang." then (s.drop "CerberusHeapLang.".length).toString else s

def count (xs : Array Name) (p : Name → Bool) : Nat := (xs.filter p).size

/-- Measurement of one declaration. The caller resolves the name (the
    resolution failure is the HARD FAILURE `resolve` below — the
    pre-2026-09-04 script rendered it as a `(MISSING)` row and exited 0). -/
def analyze (env : Environment) (n : Name) (ci : ConstantInfo) : DepM Row := do
  let tset : Std.HashSet Name := Std.HashSet.ofArray ci.type.getUsedConstants
  let direct := (valueConsts ci).filter (fun c => !tset.contains c)
  let direct := (Std.HashSet.ofArray direct).toArray
  let trans := (← cone env direct).toArray
  let engD := (direct.filter (isEngineDef env)).qsort (·.toString < ·.toString)
  let engTyD := count direct (fun c => Bool.and (isEngine env c) (!isEngineDef env c))
  let layoutD := ((direct.filter (fun c => Bool.and (isLayout env c) (!isAuto c))).map short).qsort (· < ·)
  let layoutT := count trans (fun c => Bool.and (isLayout env c) (!isAuto c))
  return {
    name := short n
    stepDefD := count direct (isStepDef env), stepDefT := trans.any (isStepDef env)
    stepLemD := count direct (isStepLem env)
    envD := count direct (isEnv env), envT := count trans (isEnv env)
    ghostD := count direct isGhost, ghostT := count trans isGhost
    planD := count direct isPlan
    judgD := count direct isJudg
    engD := engD, engTyD := engTyD, engT := count trans (isEngineDef env)
    layoutD := layoutD, layoutT := layoutT }

/-! ## Configuration -/

def ruleModules : List Name :=
  [`CerberusHeapLang.Rules, `CerberusHeapLang.Wps, `CerberusHeapLang.Wpt]
def rulePrefixes : List String := ["wp_", "wps_", "wpt_", "triple", "blockSpecs", "spike_wp_wand"]

/-- The named exports measured: the certification spine (Soundness/Round),
    the partial lane (Adequacy), the total lane (ProdLoop/ProdEntry).
    Refreshed at ar5-manifest 2026-09-04 to the post-F1 names
    (`engine_adequacyU(_alloc)` → `engine_adequacy(_alloc)`,
    `semantic_triple_soundU` → `semantic_triple_sound`, `semantic_frameU` →
    `semantic_frame`; `wpt_engine_boundU(_alloc)` are GONE with the package
    loop `driveU` — the total lane's theorems are `wpt_driver_done(_alloc)`,
    `wpt_driver_done_procs` and the pipeline forms). Every name is checked
    against the environment: a missing one aborts the run. -/
def exportSeeds : List Name := [
  `CerberusHeapLang.engine_step_matchU,
  `CerberusHeapLang.Decomp.step_factor, `CerberusHeapLang.stepDischarge_run,
  `CerberusHeapLang.Frag.step, `CerberusHeapLang.Frag.decomp,
  `CerberusHeapLang.cerberusRound_classify, `CerberusHeapLang.step_iff_cerberusRound,
  `CerberusHeapLang.frag_round_complete,
  `CerberusHeapLang.spike_step_adequacy, `CerberusHeapLang.spike_step_adequacy_alloc,
  `CerberusHeapLang.launchResources,
  `CerberusHeapLang.engine_adequacy, `CerberusHeapLang.engine_adequacy_alloc,
  `CerberusHeapLang.semantic_triple_sound, `CerberusHeapLang.semantic_frame,
  `CerberusHeapLang.project_triple_pure, `CerberusHeapLang.project_triple_pure_alloc,
  `CerberusHeapLang.wpt_driver_done, `CerberusHeapLang.wpt_driver_done_alloc,
  `CerberusHeapLang.wpt_driver_done_procs,
  `CerberusHeapLang.prod_run_eqJ, `CerberusHeapLang.prod_run_eqJ_procs,
  `CerberusHeapLang.prod_run_safe_procs,
  `CerberusHeapLang.Frag.pot_step_bound]

/-- The module classification (scripts/module_classes.tsv): module, class. -/
def classVocabulary : List String :=
  ["core", "production-core", "audit", "positive-client", "declared-smoke",
   "semantic-test", "engine-mirror-test", "production-wrapper", "negative-test",
   "example-support"]
def clientClasses : List String := ["positive-client", "declared-smoke"]

def trim (s : String) : String := s.trimAscii.toString

def readModuleClasses (path : System.FilePath) : IO (Array (Name × String)) := do
  let txt ← IO.FS.readFile path
  let mut rows : Array (Name × String) := #[]
  for (line, i) in (txt.splitOn "\n").zipIdx do
    if (trim line).isEmpty || line.startsWith "#" then continue
    let cells := line.splitOn "\t"
    if cells.length != 4 then
      throw <| IO.userError s!"module_classes.tsv:{i+1}: expected 4 TAB-separated cells, got {cells.length}"
    unless classVocabulary.contains cells[1]! do
      throw <| IO.userError s!"module_classes.tsv:{i+1}: class `{cells[1]!}` not in the vocabulary"
    rows := rows.push (cells[0]!.toName, cells[1]!)
  if rows.isEmpty then throw <| IO.userError "module_classes.tsv: no rows"
  return rows

def fmt (r : Row) : String :=
  let eng := if r.engD.isEmpty then "-" else
    s!"{r.engD.size}: " ++ ", ".intercalate ((r.engD.toList.take 4).map short) ++
      (if r.engD.size > 4 then ", …" else "")
  let lay := (if r.layoutD.isEmpty then "-" else ", ".intercalate r.layoutD.toList) ++ s!" / {r.layoutT}"
  s!"| `{r.name}` | {r.stepDefD}/{if r.stepDefT then "y" else "n"} | {r.stepLemD} | {r.envD}/{r.envT} | {r.ghostD}/{r.ghostT} | {r.judgD} | {eng} | {r.engTyD} | {r.engT} | {lay} |"

def header : String :=
  "| theorem | StepDef d/t | StepLem d | Env d/t | Ghost d/t | Judg d | Engine DEFS proof-only direct | Eng types d | Eng defs t | Layout d / t |\n|---|---|---|---|---|---|---|---|---|---|"

def isClean (r : Row) : Bool :=
  [r.stepDefD, r.stepLemD, r.envD, r.ghostD, r.judgD, r.engD.size].all (· == 0)

def score (r : Row) : Nat := r.engD.size + r.ghostD + r.stepDefD

end ParametricInventory

/-- FAIL-CLOSED name resolution: a configured name absent from the built
    environment aborts the run (nonzero exit). -/
def ParametricInventory.resolve (env : Environment) (what : String) (n : Name) : CoreM (Name × ConstantInfo) := do
  match env.find? n with
  | some ci => return (n, ci)
  | none => throwError "parametric_inventory FAIL: {what} `{n}` is not a declaration of the built environment (stale configuration — refresh it)"

open ParametricInventory in
#eval show CoreM Unit from do
  let env ← getEnv
  -- ---- fail-closed configuration checks, before any measurement
  let seedCis ← exportSeeds.toArray.mapM (resolve env "export seed")
  let modRows ← readModuleClasses "scripts/module_classes.tsv"
  let pkgMods : Array Name :=
    env.header.moduleNames.filter fun m => m.getRoot == `CerberusHeapLang && m != `CerberusHeapLang
  for m in pkgMods do
    unless modRows.any (·.1 == m) do
      throwError "parametric_inventory FAIL: module `{m}` is in the environment but not classified in scripts/module_classes.tsv"
  for (m, _) in modRows do
    unless pkgMods.contains m do
      throwError "parametric_inventory FAIL: module_classes.tsv lists `{m}`, which is not a module of the built package"
  let clientModules : Array Name :=
    (modRows.filter (fun r => clientClasses.contains r.2)).map (·.1)
    |>.qsort (fun a b => a.toString < b.toString)
  if clientModules.isEmpty then throwError "parametric_inventory FAIL: no client module classified"
  -- ---- the rule theorems
  let mut seeds : Array (Name × Name × ConstantInfo) := #[]   -- (module, name, info)
  for (n, ci) in env.constants.toList do
    let m := modOf env n
    unless ruleModules.contains m do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternalDetail then continue
    let last := n.components.getLast!.toString
    unless rulePrefixes.any (last.startsWith ·) do continue
    if (last.splitOn "exhibit").length > 1 then continue
    seeds := seeds.push (m, n, ci)
  let sorted := seeds.qsort fun a b =>
    if a.1 == b.1 then a.2.1.toString < b.2.1.toString else a.1.toString < b.1.toString
  let (rows, _) := (sorted.mapM (fun p => analyze env p.2.1 p.2.2)).run {}
  IO.println s!"## Rule theorems (Rules/Wps/Wpt): {rows.size} seeds (measured)\n"
  let mut curMod : Name := .anonymous
  for (p, r) in sorted.zip rows do
    if p.1 != curMod then
      curMod := p.1
      IO.println s!"\n### {short curMod}\n\n{header}"
    IO.println (fmt r)
  let tot := rows.size
  let c (f : Row → Bool) := (rows.filter f).size
  IO.println s!"\n## Aggregate over the {tot} rule theorems (measured)\n"
  IO.println s!"- Step relation unfolded by definition in the rule's OWN proof (StepDef direct > 0): {c (·.stepDefD > 0)}"
  IO.println s!"- Step used only through `Step.*` lemmas directly (StepLem direct > 0, StepDef direct = 0): {c (fun r => Bool.and (r.stepLemD > 0) (r.stepDefD == 0))}"
  IO.println s!"- Step reachable transitively (any): {c (·.stepDefT)}"
  IO.println s!"- Env/Fmap representation: direct > 0: {c (·.envD > 0)}; transitive > 0: {c (·.envT > 0)}"
  IO.println s!"- Ghost/cursor/CohG internals: direct > 0: {c (·.ghostD > 0)}; transitive > 0: {c (·.ghostT > 0)}"
  IO.println s!"- Judgment unfolded (`wps.pre`/`wpt.pre` direct): {c (·.judgD > 0)}"
  IO.println s!"- Generated engine DEFINITIONS in the proof only (not in the statement), direct: {c (·.engD.size > 0)}; transitive (through package lemmas) > 0: {c (·.engT > 0)}"
  IO.println s!"- Engine TYPES/constructors exposed in the proof only (judgment binders etc.), direct > 0: {c (·.engTyD > 0)}"
  IO.println s!"- Layout-dependent memory functions (TagDefs re-parameterization set): named DIRECTLY in the proof only: {c (·.layoutD.size > 0)}; in the transitive cone (dominated by `cases` on `Step`, whose constructor premises name storeM/loadM/allocateObject): {c (·.layoutT > 0)}"
  let clean := rows.filter isClean
  IO.println (s!"- CLEAN (no direct use of any category; pure logic over other rules): {clean.size}: " ++
    ", ".intercalate (clean.toList.map (s!"`{·.name}`")))
  let worst := (rows.qsort (fun a b => score a > score b)).toList.take 8
  IO.println (s!"- WORST (engine-direct + ghost-direct + StepDef-direct): " ++
    ", ".intercalate (worst.map fun r => s!"`{r.name}` ({r.engD.size}+{r.ghostD}+{r.stepDefD})"))
  let (erows, _) := (seedCis.mapM (fun (n, ci) => analyze env n ci)).run {}
  IO.println s!"\n## Certification / adequacy / production exports ({erows.size}, measured; every seed resolved)\n\n{header}"
  for r in erows do IO.println (fmt r)
  IO.println "\n## Layout-dependent package DEFINITIONS (non-theorem constants whose type or body directly names a TagDefs-parameterized memory function; measured)\n"
  let mut defs : Array String := #[]
  for (n, ci) in env.constants.toList do
    unless isPkg env n do continue
    if ci matches .thmInfo _ then continue
    if n.isInternalDetail then continue
    let cs := ci.type.getUsedConstants ++ valueConsts ci
    let hits := ((cs.filter (isLayout env)).map short).toList.eraseDups
    if hits.isEmpty then continue
    defs := defs.push s!"- `{short n}` ({short (modOf env n)}): {", ".intercalate hits}"
  for d in defs.qsort (· < ·) do IO.println d
  IO.println s!"\nTOTAL layout-dependent definitions: {defs.size}"
  -- CLIENT MODULES (the classes `positive-client` and `declared-smoke` of
  -- scripts/module_classes.tsv — the same set the manifest counts as
  -- consumers and boundary_check.sh checks textually): per module, the
  -- theorem count and the DIRECT offenders by category. Zero is the
  -- expected reading (alloc arc P4 definition of done); a nonzero here is
  -- a finding about the public surface (API.lean), not a gate verdict.
  IO.println "\n## Client modules: direct references per theorem (the classification's positive clients and declared smokes; measured)\n"
  for m in clientModules do
    let mut thms : Array (Name × ConstantInfo) := #[]
    for (n, ci) in env.constants.toList do
      unless modOf env n == m do continue
      unless ci matches .thmInfo _ do continue
      if n.isInternalDetail then continue
      thms := thms.push (n, ci)
    let sortedThms := thms.qsort (·.1.toString < ·.1.toString)
    let (rows, _) := (sortedThms.mapM (fun (n, ci) => analyze env n ci)).run {}
    let off (f : Row → Bool) : List String :=
      (rows.filter f).toList.map (fun r => s!"`{r.name}`")
    let ghost := off (·.ghostD > 0)
    let sdef := off (·.stepDefD > 0)
    let slem := off (·.stepLemD > 0)
    let judg := off (·.judgD > 0)
    let plan := off (·.planD > 0)
    let fmtL (l : List String) := if l.isEmpty then "0" else s!"{l.length}: " ++ ", ".intercalate l
    IO.println s!"- {short m}: {rows.size} theorems; Ghost-direct {fmtL ghost}; StepDef-direct {fmtL sdef}; StepLem-direct {fmtL slem}; Judg-direct {fmtL judg}; Plan-direct {fmtL plan}"
  IO.println s!"\nINVENTORY: {rows.size} rule theorems, {erows.size} export seeds (all resolved), {clientModules.size} client modules"
