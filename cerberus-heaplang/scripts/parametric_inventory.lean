/-
parametric_inventory.lean — READ-ONLY measurement for the 2026-09-02
parametric-semantics spike (docs/2026-09-02_parametric-semantics-spike.md).

For each rule theorem (Rules/Wps/Wpt) and the named Soundness/Round/
Adequacy/TotalAdequacy exports, split the constants of the PROOF TERM
into "statement" (in the type) and "proof-only" (in the value, not the
type), then classify DIRECT (the theorem's own value) vs TRANSITIVE
(closure through CerberusHeapLang constants only; engine/Iris/Lean
constants are leaves, never expanded) usage of:
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
  CERB_MEM_MAX=48G ../scripts/capped ~/.elan/bin/lake env lean scripts/parametric_inventory.lean
-/
import CerberusHeapLang.TotalAdequacy
import CerberusHeapLang.Round
import CerberusHeapLang.ArrayExhibit
import CerberusHeapLang.StructExhibit
import CerberusHeapLang.ListRevExhibit
import CerberusHeapLang.TreeRotExhibit
import CerberusHeapLang.LoopExhibit
import CerberusHeapLang.Examples.ReadinessSmoke

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
    (hasSub n ["CohG", "cursorOwn", "cursorInterp",
            "cursorHeap", "byteInterp", "metaInterp", "byteHeap", "metaHeap",
            "stateInterp_eq", "stateInterp_iff", "pointsToCell_iff",
            "cellOwn_iff", "pointsToView_iff", "bytesOwn",
            "byteOwn", "metaOwn", "MetaByteOf", "LaunchCoh", "genHeapInterp", "GenHeap"])
/-- The pure allocation-plan model (alloc arc P1.1: the cursor arithmetic
    `PlanFits`/`advanceCursor`/`freshBase` a launch's plan-fit fact is
    computed with) — separated from the ghost maps at P4. -/
def isPlan (n : Name) : Bool :=
  hasSub n ["AllocCursor", "advanceCursor", "PlanFits", "freshBase"]
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

def analyze (env : Environment) (n : Name) : DepM Row := do
  let some ci := env.find? n | return { name := s!"{short n} (MISSING)" }
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

def clientModules : List Name :=
  [`CerberusHeapLang.ArrayExhibit, `CerberusHeapLang.StructExhibit,
   `CerberusHeapLang.ListRevExhibit, `CerberusHeapLang.TreeRotExhibit,
   `CerberusHeapLang.LoopExhibit, `CerberusHeapLang.Examples.ReadinessSmoke]
def ruleModules : List Name :=
  [`CerberusHeapLang.Rules, `CerberusHeapLang.Wps, `CerberusHeapLang.Wpt]
def rulePrefixes : List String := ["wp_", "wps_", "wpt_", "triple", "blockSpecs", "spike_wp_wand"]

def exportSeeds : List Name := [
  `CerberusHeapLang.engine_step_matchU,
  `CerberusHeapLang.Decomp.step_factor, `CerberusHeapLang.stepDischarge_run,
  `CerberusHeapLang.Frag.step, `CerberusHeapLang.Frag.decomp,
  `CerberusHeapLang.cerberusRound_classify, `CerberusHeapLang.step_iff_cerberusRound,
  `CerberusHeapLang.frag_round_complete,
  `CerberusHeapLang.spike_step_adequacy, `CerberusHeapLang.spike_step_adequacy_alloc,
  `CerberusHeapLang.launchResources,
  `CerberusHeapLang.engine_adequacyU, `CerberusHeapLang.engine_adequacyU_alloc,
  `CerberusHeapLang.semantic_triple_soundU, `CerberusHeapLang.semantic_frameU,
  `CerberusHeapLang.project_triple_pure, `CerberusHeapLang.project_triple_pure_alloc,
  `CerberusHeapLang.wpt_engine_boundU, `CerberusHeapLang.wpt_engine_boundU_alloc,
  `CerberusHeapLang.Frag.pot_step_bound]

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

open ParametricInventory in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut seeds : Array (Name × Name) := #[]   -- (module, name)
  for (n, ci) in env.constants.toList do
    let m := modOf env n
    unless ruleModules.contains m do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternalDetail then continue
    let last := n.components.getLast!.toString
    unless rulePrefixes.any (last.startsWith ·) do continue
    if (last.splitOn "exhibit").length > 1 then continue
    seeds := seeds.push (m, n)
  let sorted := seeds.qsort fun a b =>
    if a.1 == b.1 then a.2.toString < b.2.toString else a.1.toString < b.1.toString
  let (rows, _) := (sorted.mapM (fun p => analyze env p.2)).run {}
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
  let (erows, _) := (exportSeeds.toArray.mapM (analyze env)).run {}
  IO.println s!"\n## Soundness / Round / Adequacy / TotalAdequacy exports ({erows.size}, measured)\n\n{header}"
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
  -- CLIENT MODULES (alloc arc P4 definition of done: the array, struct,
  -- list and tree clients import only the public raw-logic API — none
  -- unfolds the ghost maps / CohG / the cursor (Ghost), the engine
  -- transition (StepDef / StepLem), or the judgment (Judg)). Per module:
  -- theorem count and the DIRECT offenders by category.
  IO.println "\n## Client modules: direct references per theorem (alloc arc P4 DoD; measured)\n"
  for m in clientModules do
    let mut thms : Array Name := #[]
    for (n, ci) in env.constants.toList do
      unless modOf env n == m do continue
      unless ci matches .thmInfo _ do continue
      if n.isInternalDetail then continue
      thms := thms.push n
    let sortedThms := thms.qsort (·.toString < ·.toString)
    let (rows, _) := (sortedThms.mapM (analyze env)).run {}
    let off (f : Row → Bool) : List String :=
      (rows.filter f).toList.map (fun r => s!"`{r.name}`")
    let ghost := off (·.ghostD > 0)
    let sdef := off (·.stepDefD > 0)
    let slem := off (·.stepLemD > 0)
    let judg := off (·.judgD > 0)
    let plan := off (·.planD > 0)
    let fmtL (l : List String) := if l.isEmpty then "0" else s!"{l.length}: " ++ ", ".intercalate l
    IO.println s!"- {short m}: {rows.size} theorems; Ghost-direct {fmtL ghost}; StepDef-direct {fmtL sdef}; StepLem-direct {fmtL slem}; Judg-direct {fmtL judg}; Plan-direct {fmtL plan}"
