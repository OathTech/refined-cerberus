/-
capability_manifest.lean — THE CAPABILITY MANIFEST generator
(pattern: statement_census.lean; installed by Phase 0 of the
2026-08-31 foundations arc, remediating audit findings F-01/F-09;
upgraded to the CONE-DERIVED form by Phase-1 S1c — design record §4,
the K4 mechanism demonstrated by the S1a probe; upgraded to the
DEPENDENCY-CERTIFIED form by alloc arc P3 — the 2026-09-01 skeptical
re-audit's R-04, charter §P3.1).

Generates docs/CAPABILITY_MANIFEST.md: one row per supported Core
construct, with STAGED per-row fields — syntax constructor /
relational rule / public logical rule / partial adequacy consumers /
local consumers / total lane / production lane — each later stage's
transitive constant-dependency cone REQUIRED to contain the
preceding public abstraction. The committed output is THE
authoritative scope statement: every claims surface (README,
walkthrough) defers to it, and scripts/test_unit.sh gate 4 fails on
(a) drift between a fresh run and the committed file, (b) any README
certified-scope token outside the manifest's ADEQUACY-EXPORTABLE
set, and (c) any throw of this script — every check below is
fail-closed (a false attribution is never a legitimate state, so it
THROWS rather than rendering a red cell).

DERIVED vs CHECKED vs DEPENDENCY-CERTIFIED vs DECLARED (the
instrument's own honesty):
- DERIVED (S1c — environment reflection): THE ROW SET IS ENUMERATED
  FROM `Frag`'s constructor list read out of the built environment —
  a cone constructor without a `rowSpec` mapping makes this script
  THROW. Symmetrically the `Step` mirror's coverage: every `Step`
  constructor read from the environment must be claimed by EXACTLY
  ONE row's mirror cell (audit F-03 acceptance property). P3.2: the
  ENGINE-MATCH column is derived from the relation-coverage theorem
  `cerberusRound_classify` (Round.lean) — its statement must be
  indexed by `Frag` and conclude `RoundClass` (arms checked), and
  every row's engine equations must lie in its proof cone.
- CHECKED (Phase 0): every named declaration in a cell is looked up
  in the environment and must exist with the stated kind.
- DEPENDENCY-CERTIFIED (P3.1, the R-04 repair — the checks are
  cone computations over the built environment, all fail-closed):
  * EXECUTION WITNESS: every consumer's STATEMENT reaches the row's
    Core syntax constructor(s) through program-valued definitions
    only (a definitions-only traversal restricted to declarations
    whose type is Core syntax — expression/pexpr/action/pattern/
    file — so the witness is the PROGRAM TEXT in the theorem's
    statement, not a proof artifact; the naive transitive cone is
    vacuous here — see the P3 notes' measurement: `esize`/`Frag`
    mention every constructor). Every public logical rule likewise
    is ABOUT its construct (its statement reaches the syntax
    constructor).
  * RULE DEPENDENCY: every partial/local consumer's proof cone
    contains one of the row's partial public rules; every total
    derivation/consumer's cone contains one of the row's total
    rules; every production consumer's cone contains a rule of the
    row (total or partial) PLUS the row's `prodRequires` set (for
    create: the PUBLIC `wpt_create` AND the allocation-aware
    launcher `launchResources` — "not merely Step.create").
  * ADEQUACY DEPENDENCY: every adequacy (engine-facing partial)
    consumer's cone contains an approved PARTIAL LAUNCHER; every
    total consumer's cone an approved TOTAL LAUNCHER; every
    production consumer's cone an approved PRODUCTION LAUNCHER (the
    launcher sets are explicit below and existence-checked). A local
    rule-level theorem listed as an adequacy consumer THROWS (charter
    plant 2).
  * THE LAYER CUT (over EVERY constant of the positive-exhibit
    modules, not just the listed consumers): every dependency path
    from a positive-exhibit declaration to an OPERATIONAL name (the
    `Step` relation's namespace, the engine-round projections, the
    per-construct engine equations, the driver step lemmas) must
    cross the approved cut — the logic/adequacy layer's declarations
    (explicit module allowlist minus the operational names, plus
    the two Lang instances) — and the DIRECT-REFERENCE BAN: no
    positive-exhibit body names `Step.*`/`engineSteps_*`/
    `driveJ_step`/`driverDone_step` directly. A raw transitive ban
    on `Step.*` would be wrong (sound rules legitimately depend on
    the relation); the cut is the right shape (charter §P3.1).
  Measured NON-VACUITY (recorded in docs/2026-09-01_p3-notes.md): a
  transitive-cone test for `Step` CONSTRUCTORS or Core syntax
  constructors is VACUOUS in Lean 4 (every `cases` on `Step` names
  every constructor through `Step.casesOn`; `esize`/`Frag` mention
  every syntax constructor) and is therefore NOT used as evidence;
  the rule/launcher cone tests and the statement-rooted syntax
  witness ARE discriminating (fib's statement reaches no `Store0`;
  a local `wps` theorem reaches no launcher).
- DECLARED (documented, not mechanical): lane prose, the construct
  descriptions, and the notes.

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

/-! ## Environment reflection helpers -/

/-- The proof/definition body of a constant. NB `ConstantInfo.value?`
    returns `none` for theorems in this toolchain — the explicit
    match is load-bearing (the P3 notes record the measurement). -/
def valueOf : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

/-- Our package's constants (module-of-origin root). -/
def isOurs (env : Environment) (n : Name) : Bool :=
  (modOf env n).getRoot == `CerberusHeapLang

def pfx : String := "CerberusHeapLang."

def shortName (n : Name) : String :=
  let s := n.toString
  if s.startsWith pfx then (s.drop pfx.length).toString else s

/-- The dependency table of OUR constants, filled LAZILY and memoized:
    for a constant, the constants named by its statement (type) and
    by its body (value). `getUsedConstants` over the package's large
    proof terms is the dominant cost, so it runs at most once per
    constant, and only for constants a traversal actually expands. -/
abbrev DepM := StateM (Std.HashMap Name (Array Name × Array Name))

def depsOf (env : Environment) (n : Name) : DepM (Array Name × Array Name) := do
  match (← get).get? n with
  | some d => return d
  | none =>
    let d := match env.find? n with
      | some ci => (ci.type.getUsedConstants,
          (match valueOf ci with | some b => b.getUsedConstants | none => #[]))
      | none => (#[], #[])
    modify (·.insert n d)
    return d

def typeDeps (env : Environment) (n : Name) : DepM (Array Name) := do
  return (← depsOf env n).1
def valueDeps (env : Environment) (n : Name) : DepM (Array Name) := do
  return (← depsOf env n).2
def allDeps (env : Environment) (n : Name) : DepM (Array Name) := do
  let (t, v) ← depsOf env n
  return t ++ v

/-- The modules that carry every cone-check TARGET (public rules,
    launchers, `prodRequires`): the logic/adequacy layer. Asserted at
    run time for every target (fail-closed). -/
def targetModules : List Name :=
  [`CerberusHeapLang.Rules, `CerberusHeapLang.Wps, `CerberusHeapLang.Wpt,
   `CerberusHeapLang.Adequacy, `CerberusHeapLang.TotalAdequacy,
   `CerberusHeapLang.ProdLoop, `CerberusHeapLang.ProdEntry]

/-- Modules PRUNED by the cone traversal: none of them imports a
    target module (asserted at run time from the environment's import
    graph — fail-closed), so no dependency path through them can reach
    a target; pruning them is sound and skips the relation/engine
    certification's giant proof terms. -/
def leafModules : List Name :=
  [`CerberusHeapLang.Step, `CerberusHeapLang.Soundness, `CerberusHeapLang.Heap,
   `CerberusHeapLang.Lang, `CerberusHeapLang.StmtProbe]

/-- Transitive import closure of a module, from the environment
    header (fail-closed: an unknown module name throws). -/
def importClosure (env : Environment) (m : Name) : Except String (Std.HashSet Name) := do
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let idxOf (x : Name) : Option Nat := mods.findIdx? (· == x)
  let some _ := idxOf m | throw s!"manifest FAIL: module {m} is not in the environment"
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[m]
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    match idxOf c with
    | some i => for imp in data[i]!.imports do stack := stack.push imp.module
    | none => pure ()
  return seen

/-- THE PROOF CONE (pruned): every constant of OUR package reachable
    from `start`'s statement and body through our constants, not
    expanding through the leaf modules. Pruning at foreign constants
    is SOUND for membership questions about our own names (iris-lean /
    the semantics never reference this package — the import graph is
    acyclic); pruning at leaf modules is sound for the target modules
    by the import-closure assertion above. -/
partial def cone (env : Environment) (start : Name) (pruneLeaves : Bool := true) :
    DepM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := ← allDeps env start
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    if !isOurs env c then continue
    seen := seen.insert c
    if pruneLeaves && leafModules.contains (modOf env c) then continue
    for d in ← allDeps env c do
      if !seen.contains d then stack := stack.push d
  return seen

/-- Type heads that count as CORE SYNTAX for the execution witness:
    a definition of such a type is program text (or a program-
    building helper / the shipped file / the runtime tuple and
    thread literal wrapping a program), and is expanded by the
    statement-rooted witness traversal; nothing else is (in
    particular NOT `esize`/`pot`/the judgments/`Frag`). -/
def syntaxTypeHeads : List Name :=
  [`generic_expr, `generic_expr_, `generic_pexpr, `generic_pexpr_,
   `generic_action, `generic_action_, `generic_paction, `generic_pattern,
   `generic_memop, `generic_file, `generic_fun_map_decl, `generic_impl_decl,
   `expr, `pexpr, `pattern, `action, `paction, `CerberusHeapLang.CoreExpr,
   `CerberusHeapLang.CoreRt, `thread_state, `Prod, `List, `Option]

partial def headOfType : Expr → Option Name
  | .forallE _ _ b _ => headOfType b
  | .app f _ => headOfType f
  | .const n _ => some n
  | .mdata _ e => headOfType e
  | _ => none

/-- THE EXECUTION WITNESS: the FOREIGN (semantics-side) constants
    reached from `start`'s STATEMENT through OUR definitions of Core-
    syntax type only. A row's syntax constructor in this set means
    the program in the theorem's statement syntactically contains the
    construct. -/
partial def stmtSyntax (env : Environment) (start : Name) : DepM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut frontier : Std.HashSet Name := {}
  let mut stack : Array Name := ← typeDeps env start
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    if !isOurs env c then
      frontier := frontier.insert c
      continue
    seen := seen.insert c
    match env.find? c with
    | some (.defnInfo d) =>
      -- a compiled-pattern auxiliary (`foo.match_n`) of a reached
      -- definition carries the matched constructors in its TYPE
      let isMatchAux := match c with
        | .str _ s => s.startsWith "match_"
        | _ => false
      let syntaxTyped := match headOfType d.type with
        | some hd => syntaxTypeHeads.contains hd
        | none => false
      if [isMatchAux, syntaxTyped].any id then
        for x in ← allDeps env c do
          if !seen.contains x then stack := stack.push x
    | _ => pure ()
  return frontier

/-! ## The approved launcher sets (explicit; existence-checked) -/

/-- Partial-lane adequacy launchers: the engine-facing theorems a
    PARTIAL adequacy consumer must stand on. -/
def partialLaunchers : List Name :=
  [`CerberusHeapLang.spike_engine_adequacy, `CerberusHeapLang.spike_engine_adequacy_alloc,
   `CerberusHeapLang.spike_step_adequacy, `CerberusHeapLang.spike_step_adequacy_alloc,
   `CerberusHeapLang.engine_adequacyJ, `CerberusHeapLang.engine_adequacyU,
   `CerberusHeapLang.engine_adequacyU_alloc, `CerberusHeapLang.semantic_triple_sound]

/-- Total-lane launchers (the measure→drive-fuel simulations and
    the Iris TotalAdequacy consumers). -/
def totalLaunchers : List Name :=
  [`CerberusHeapLang.wpt_engine_boundU, `CerberusHeapLang.wpt_engine_boundJ,
   `CerberusHeapLang.wpt_engine_boundU_alloc, `CerberusHeapLang.wpt_engine_boundJ_alloc,
   `CerberusHeapLang.wpt_strongly_normalizing, `CerberusHeapLang.wpt_strongly_normalizing_alloc]

/-- Production-lane launchers (the shipped-pipeline collapses). -/
def prodLaunchers : List Name :=
  [`CerberusHeapLang.prod_run_eq, `CerberusHeapLang.prod_run_eqJ,
   `CerberusHeapLang.wpt_driver_done, `CerberusHeapLang.wpt_driver_done_alloc]

/-! ## The layer cut -/

/-- The POSITIVE-EXHIBIT modules: every constant here is subject to
    the layer cut and the direct-reference ban. DivergeExhibit (the
    NEGATIVE test) is deliberately absent — with Soundness and
    DriverCollapse it is a charter-allowed operational home. -/
def positiveExhibitModules : List Name :=
  [`CerberusHeapLang.Exhibit, `CerberusHeapLang.ProdExhibit,
   `CerberusHeapLang.ProdLoopExhibit, `CerberusHeapLang.StructExhibit,
   `CerberusHeapLang.ListRevExhibit, `CerberusHeapLang.LoopExhibit,
   `CerberusHeapLang.ArrayExhibit, `CerberusHeapLang.FibExhibit,
   `CerberusHeapLang.TreeRotExhibit, `CerberusHeapLang.CaseExhibit,
   `CerberusHeapLang.WseqExhibit, `CerberusHeapLang.AllocExhibit]

/-- THE APPROVED CROSSING SET, module part: the logic and adequacy
    layer. A dependency path from an exhibit may reach operational
    names ONLY through a declaration of one of these modules (minus
    the operational names themselves — `driveJ_step` lives in
    Adequacy and `driverDone_step` in ProdLoop and are NOT
    crossings). Deliberately ABSENT: Step/Soundness/DriverCollapse
    (operational homes), Lang (only its two instances cross — below),
    Heap (the memory model; it reaches no operational name, so it
    needs no approval — measured), StmtProbe (the toy). -/
def cutModules : List Name :=
  [`CerberusHeapLang.Rules, `CerberusHeapLang.Wps, `CerberusHeapLang.Wpt,
   `CerberusHeapLang.Adequacy, `CerberusHeapLang.TotalAdequacy,
   `CerberusHeapLang.ProdLoop, `CerberusHeapLang.ProdEntry]

/-- THE APPROVED CROSSING SET, name part: the iris-lean `Language`
    and `IrisGS` instances (Lang.lean) — the WP's DEFINITIONAL
    attachment to the relation (`primStep := Step …`); every WP
    mention reaches `Step` through them, by design. -/
def cutNames : List Name :=
  [`CerberusHeapLang.instLanguageCoreRtMemEmptyCoreRVal, `CerberusHeapLang.instIrisGS]

/-- Operational names by exact spelling (the engine-round
    projections, the driver step lemmas, the headline match/
    completeness theorems, the decomposition machinery). -/
def operationalNames : List Name :=
  [`CerberusHeapLang.engineSteps, `CerberusHeapLang.engineStepsU,
   `CerberusHeapLang.engineStepsP, `CerberusHeapLang.engineOutcomes,
   `CerberusHeapLang.engineOutcomesP, `CerberusHeapLang.outcomesU,
   `CerberusHeapLang.dischargeStep, `CerberusHeapLang.driveJ_step,
   `CerberusHeapLang.driverDone_step, `CerberusHeapLang.loop_step_frag,
   `CerberusHeapLang.engine_step_matchU, `CerberusHeapLang.engine_complete,
   `CerberusHeapLang.engine_complete_storeU, `CerberusHeapLang.engine_complete_caseU,
   `CerberusHeapLang.CerberusRound, `CerberusHeapLang.cerberusRound_classify]

/-- Operational names by shape: the whole `Step` namespace
    (constructors, recursors, inversion lemmas), the per-construct
    engine equations, the frozen-profile step corollaries, the
    discharge lemmas, `Decomp`/`Redex`. -/
def isOperational (n : Name) : Bool :=
  let s := shortName n
  [operationalNames.contains n, s.startsWith "Step.", s.startsWith "step_ctx_",
   s.startsWith "stepDischarge_", s.startsWith "engineSteps_",
   s.startsWith "dischargeStep_", s.startsWith "Decomp.", s.startsWith "Redex.",
   s.startsWith "cerberusRound_", s.startsWith "CerberusRound."].any id

/-- The direct-reference ban set (charter §P3.1 wording: `Step.*` —
    the whole relation namespace, constructors and lemmas alike —
    `engineSteps_*`, `driveJ_step`, `driverDone_step`). -/
def isDirectBanned (stepCtors : List Name) (n : Name) : Bool :=
  let s := shortName n
  [stepCtors.contains n, s.startsWith "Step.", s.startsWith "engineSteps_",
   n == `CerberusHeapLang.driveJ_step, n == `CerberusHeapLang.driverDone_step].any id

/-! ## Cells and rows -/

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

def Cell.ctorNames : Cell → List Name
  | .ctors names _ => names
  | _ => []

def Cell.thmNames : Cell → List Name
  | .thms names _ => names
  | _ => []

/-- The TOTAL lane of a row: the wpt rules, the wpt-level whole-
    program derivations (their cones must contain a total rule), and
    the engine-facing total consumers (a total rule AND a total
    launcher). -/
structure TotalLane where
  rules : List Name
  derivations : List Name := []
  consumers : List Name
  note : String := ""

/-- The PRODUCTION lane: shipped-pipeline consumers (a rule of the
    row, a production launcher, and the row's `prodRequires`). -/
structure ProdLane where
  consumers : List Name
  note : String := ""

/-- Per-cone-constructor row data. The cone cell is NOT here — it is
the enumeration key itself (filled in by the generator), so a row
cannot claim cone membership the cone does not have. -/
structure RowSpec where
  token : String
  construct : String
  /-- The Core syntax constructor(s) whose presence in a statement's
      program text witnesses the construct (ANY of them suffices; the
      note says why several). -/
  synCtors : List Name
  syntaxNote : String := ""
  mirror : Cell
  /-- The public PARTIAL logical rules (wp_/wps_ family). -/
  logic : Cell
  coneNote : String := ""
  /-- The per-construct ENGINE EQUATIONS the row's mirror rules are
      certified by (step_ctx_*/stepDischarge_*): each must lie in the
      cone of the headline classification `cerberusRound_classify`
      (P3.2 — the manifest's relation coverage is DERIVED from that
      theorem, not declared). -/
  engineEqs : List Name
  engineNote : String := ""
  /-- The row's REFUSAL classification theorem (two-sided at the
      refusal arm: mirror stuck ⇒ the engine's round is a singleton
      refusal), or `none` with the reason the row is one-sided there
      (the R-03 residual, per row). -/
  twoSided : Option Name := none
  oneSidedWhy : String := ""
  /-- The refusal arm is NOT APPLICABLE (the value row: values are
      never mirror-stuck — both engine rounds are exact value arms). -/
  refusalNA : Bool := false
  /-- The generic partial-lane adequacy theorems the row rides. -/
  partialLane : Cell
  /-- Engine-facing PARTIAL consumers (rule + partial launcher). -/
  adequacyConsumers : List Name
  adequacyNote : String := ""
  /-- Rule-level consumers: wps/wpt derivations WITHOUT an engine
      conclusion (rule dependency + witness only; never claimed as
      adequacy). -/
  localConsumers : List Name := []
  localNote : String := ""
  total : Option TotalLane
  totalRed : String := ""
  prod : Option ProdLane
  prodRed : String := ""
  /-- Extra names EVERY production consumer's cone must contain. -/
  prodRequires : List Name := []

structure Row where
  token : String
  construct : String
  synCtors : List Name
  syntaxNote : String
  mirror : Cell
  logic : Cell
  cone : Cell
  engineEqs : List Name
  engineNote : String
  twoSided : Option Name
  oneSidedWhy : String
  refusalNA : Bool
  /-- Supplementary rows: a DECLARED engine-match text instead. -/
  engineDeclared : String := ""
  partialLane : Cell
  adequacyConsumers : List Name
  adequacyNote : String
  localConsumers : List Name
  localNote : String
  total : Option TotalLane
  totalRed : String
  prod : Option ProdLane
  prodRed : String
  prodRequires : List Name
  /-- Supplementary rows own no constructor and carry no per-row
      stage checks (their names are still existence-checked). -/
  supplementary : Bool := false

def RowSpec.toRow (spec : RowSpec) (coneCtor : Name) : Row :=
  { token := spec.token, construct := spec.construct,
    synCtors := spec.synCtors, syntaxNote := spec.syntaxNote,
    mirror := spec.mirror, logic := spec.logic,
    cone := .ctors [coneCtor] (note := spec.coneNote),
    engineEqs := spec.engineEqs, engineNote := spec.engineNote,
    twoSided := spec.twoSided, oneSidedWhy := spec.oneSidedWhy,
    refusalNA := spec.refusalNA,
    partialLane := spec.partialLane,
    adequacyConsumers := spec.adequacyConsumers, adequacyNote := spec.adequacyNote,
    localConsumers := spec.localConsumers, localNote := spec.localNote,
    total := spec.total, totalRed := spec.totalRed,
    prod := spec.prod, prodRed := spec.prodRed, prodRequires := spec.prodRequires }

/-- Row level for the claims surfaces. The CORE columns are mirror /
cone / engine-match / partial-adequacy / adequacy consumers (the
latter now DEPENDENCY-CERTIFIED); the logic, total and production
lanes are reported separately in the machine-readable lines
(2026-09-01 P0: the former FULL-ROW aggregate was renamed
CORE-DRIVE-ROW; since P3 every listed lane member is dependency-
certified or the run throws). -/
def Row.coreCells (r : Row) : List Cell :=
  [r.mirror, r.cone, r.partialLane]

def Row.exportable (r : Row) : Bool :=
  !(r.coreCells.any Cell.isRed) && !r.adequacyConsumers.isEmpty

def Row.coreDriveRow (r : Row) : Bool :=
  r.exportable && !(r.logic.isRed)

def Row.level (r : Row) : String :=
  if !r.exportable then "LOCAL RULE ONLY (RED)"
  else if r.logic.isRed then "ADEQUACY-EXPORTABLE (no logic rule)"
  else "CERTIFIED (drive lane)"

/-! The Core syntax constructors (spellings checked in the environment). -/
def Esseq := `generic_expr_.Esseq
def Ewseq := `generic_expr_.Ewseq
def Esave := `generic_expr_.Esave
def Eif := `generic_expr_.Eif
def Erun := `generic_expr_.Erun
def Ecase := `generic_expr_.Ecase
def Eannot := `generic_expr_.Eannot
def Ememop := `generic_expr_.Ememop
def PEsym := `generic_pexpr_.PEsym
def PEval := `generic_pexpr_.PEval
def Create := `generic_action_.Create
def Store0 := `generic_action_.Store0
def Load0 := `generic_action_.Load0
def PtrEq := `generic_memop.PtrEq
def Cspecified := `ctor.Cspecified

/-- The three allocating production exports (whole-program create-
    rule consumers since P2). -/
def allocProds : List Name :=
  [`CerberusHeapLang.exhibitA_prod, `CerberusHeapLang.counter_loop_certified_production,
   `CerberusHeapLang.list_reverse_certified_production]

def lrTotal : List Name := [`CerberusHeapLang.list_reverse_certified_total]
def fibLrTotal : List Name :=
  [`CerberusHeapLang.fib_certified_total, `CerberusHeapLang.list_reverse_certified_total]
def loopProds : List Name :=
  [`CerberusHeapLang.fib_certified_production,
   `CerberusHeapLang.counter_loop_certified_production,
   `CerberusHeapLang.list_reverse_certified_production]

/-- THE CONSTRUCTOR → ROW MAPPING. The row set itself is NOT listed
anywhere — it is enumerated from `Frag`'s constructors in the built
environment; this mapping must COVER the enumeration or the run
throws (fail-closed: the cone cannot grow past the manifest). -/
def rowSpec : Name → Option RowSpec
  | `CerberusHeapLang.Frag.val_pure => some
    { token := "value", construct := "value delivery (Epure at PEval; Eannot values)",
      synCtors := [PEval],
      mirror := .declared "terminal — the toVal/ofVal value protocol (values do not step)",
      logic := .thms [`CerberusHeapLang.wp_ofVal, `CerberusHeapLang.wps_ofVal],
      engineEqs := [`CerberusHeapLang.step_ctx_done, `CerberusHeapLang.step_ctx_remove_annot],
      oneSidedWhy := "the value protocol: no mirror step exists at a value by design; both engine rounds (PROGRAM-DONE / REMOVE-ANNOT) are EXACT arms of the classification (value_done / value_annot) — nothing is one-sided here",
      refusalNA := true,
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.exhibitA_engine],
      total := some
        { rules := [`CerberusHeapLang.wpt_ofVal],
          consumers := `CerberusHeapLang.exhibitA_total :: fibLrTotal },
      prod := some
        { consumers := [`CerberusHeapLang.exhibitA_prod, `CerberusHeapLang.fib_certified_production] } }
  | `CerberusHeapLang.Frag.store => some
    { token := "store", construct := "Eaction Store0 (value operands)",
      synCtors := [Store0],
      mirror := .ctors [`CerberusHeapLang.Step.store],
      logic := .thms [`CerberusHeapLang.wp_store, `CerberusHeapLang.wps_store,
        `CerberusHeapLang.wps_store_at, `CerberusHeapLang.wps_store_cell_at]
        (note := "wps_store_at/wps_store_cell_at are the GENERIC typed-subrange forms (Notes 5)"),
      engineEqs := [`CerberusHeapLang.step_ctx_store],
      engineNote := "TWO-SIDED at any MachineCtx",
      twoSided := some `CerberusHeapLang.cerberusRound_refused_store,
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.exhibitB_engine,
        `CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.list_reverse_certified,
        `CerberusHeapLang.struct_create_store_adequacy],
      total := some
        { rules := [`CerberusHeapLang.wpt_store_at, `CerberusHeapLang.wpt_store_cell_at, `CerberusHeapLang.wpt_store_cell],
          consumers := `CerberusHeapLang.exhibitA_total :: lrTotal },
      prod := some
        { consumers := allocProds } }
  | `CerberusHeapLang.Frag.load => some
    { token := "load", construct := "Eaction Load0 (value operand)",
      synCtors := [Load0],
      mirror := .ctors [`CerberusHeapLang.Step.load],
      logic := .thms [`CerberusHeapLang.wp_load, `CerberusHeapLang.wps_load,
        `CerberusHeapLang.wps_load_at, `CerberusHeapLang.wps_load_cell_at]
        (note := "wps_load_at/wps_load_cell_at are the GENERIC typed-subrange forms (Notes 5)"),
      engineEqs := [`CerberusHeapLang.step_ctx_load],
      twoSided := some `CerberusHeapLang.cerberusRound_refused_load,
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.exhibitA_engine,
        `CerberusHeapLang.array_sum_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_load_at, `CerberusHeapLang.wpt_load_cell_at],
          consumers := `CerberusHeapLang.exhibitA_total :: lrTotal },
      prod := some
        { consumers := [`CerberusHeapLang.exhibitA_prod, `CerberusHeapLang.list_reverse_certified_production] } }
  | `CerberusHeapLang.Frag.create => some
    { token := "create", construct := "Eaction Create0",
      synCtors := [Create],
      mirror := .ctors [`CerberusHeapLang.Step.create],
      logic := .thms [`CerberusHeapLang.wps_create,
        `CerberusHeapLang.wps_create_cursor_internal]
        (note := "alloc arc P1: the PUBLIC wps_create takes the abstract capacity allocCap (req :: rest) and binds an existential pointer (statement cursor-free); the exact-cursor form is wps_create_cursor_internal (heap-implementation use only); OOM excluded by the plan-fit inside allocCap — see Notes 4"),
      engineEqs := [`CerberusHeapLang.step_ctx_create],
      twoSided := some `CerberusHeapLang.cerberusRound_refused_create,
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.struct_create_store_adequacy],
      adequacyNote := "the PUBLIC-rule whole-program client's engine export (alloc arc P2 item 2), launched through spike_engine_adequacy_alloc",
      localConsumers := [`CerberusHeapLang.alloc_two_creates_wps,
        `CerberusHeapLang.alloc_create_wpt, `CerberusHeapLang.struct_create_store_wps],
      localNote := "rule-level: the plan-order consumption test, the derived k=2 total budget, and the struct client's wps derivation (its engine export is the adequacy consumer)",
      total := some
        { rules := [`CerberusHeapLang.wpt_create],
          derivations := [`CerberusHeapLang.progAProd_wpt, `CerberusHeapLang.ctrProd_wpt, `CerberusHeapLang.lrProd_wpt],
          consumers := [`CerberusHeapLang.alloc_create_launch_smoke],
          note := "alloc_create_launch_smoke is the engine-facing chain-closer (driveU .done at fuel 2 via wpt_create + wpt_engine_boundU_alloc from prodMem₀); the three derivations are the P2 whole-program total judgments the production exports collapse" },
      prod := some
        { consumers := allocProds,
          note := "ALL THREE are WHOLE-PROGRAM create-rule consumers (alloc arc P2, the R-02 conversion): each program BINDS its engine-created pointer(s), the creates cross the PUBLIC wpt_create from abstract capacity plans, and the pipeline arrows are the generic wpt_driver_done_alloc → prod_run_eqJ; since P3 the cone of each is REQUIRED to contain wpt_create AND launchResources (prodRequires)" },
      prodRequires := [`CerberusHeapLang.wpt_create, `CerberusHeapLang.launchResources] }
  | `CerberusHeapLang.Frag.sseq => some
    { token := "sseq-wild", construct := "Esseq, wildcard pattern",
      synCtors := [Esseq],
      mirror := .ctors [`CerberusHeapLang.Step.sseq_pure,
        `CerberusHeapLang.Step.sseq_annot, `CerberusHeapLang.Step.sseq_ctx],
      logic := .thms [`CerberusHeapLang.wp_sseq, `CerberusHeapLang.wps_seq],
      engineEqs := [`CerberusHeapLang.step_ctx_beta_pure, `CerberusHeapLang.step_ctx_beta_annot],
      oneSidedWhy := "context row: the refusal at a nested redex propagates from the redex; the beta at a value never refuses (cons env) — the redex rows carry the two-sidedness; no context-level refusal theorem yet",
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.exhibitA_engine,
        `CerberusHeapLang.exhibitC_engine],
      total := some
        { rules := [`CerberusHeapLang.wpt_seq],
          consumers := `CerberusHeapLang.exhibitA_total :: lrTotal },
      prod := some
        { consumers := allocProds } }
  | `CerberusHeapLang.Frag.annot => some
    { token := "annot", construct := "Eannot residue (descent + merge)",
      synCtors := [Eannot, Store0, Load0],
      syntaxNote := "a RUNTIME residue, not source syntax: the engine's DA_pos annotation arises from every executed Store0/Load0 (the evaluator-case witness the charter allows), or from a literal Eannot",
      mirror := .ctors [`CerberusHeapLang.Step.annot_ctx,
        `CerberusHeapLang.Step.annot_merge],
      logic := .thms [`CerberusHeapLang.wp_annot, `CerberusHeapLang.wps_annot],
      engineEqs := [`CerberusHeapLang.step_ctx_merge],
      oneSidedWhy := "context row (descent) / pure merge: as sseq-wild",
      partialLane := .thms [`CerberusHeapLang.engine_complete,
        `CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.exhibitA_engine],
      total := some
        { rules := [`CerberusHeapLang.wpt_annot],
          consumers := `CerberusHeapLang.exhibitA_total :: lrTotal },
      prod := some
        { consumers := allocProds } }
  | `CerberusHeapLang.Frag.save => some
    { token := "save", construct := "Esave (block entry, value-shaped params)",
      synCtors := [Esave],
      mirror := .ctors [`CerberusHeapLang.Step.save],
      logic := .thms [`CerberusHeapLang.wps_save],
      engineEqs := [`CerberusHeapLang.step_ctx_save],
      oneSidedWhy := "the refusal channel is an ENGINE EVAL round on non-value params (the mirror requires value-shaped params) — a genuine one-sided gap, not a panic",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.fib_certified, `CerberusHeapLang.list_reverse_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_save],
          consumers := fibLrTotal },
      prod := some
        { consumers := [`CerberusHeapLang.fib_certified_production],
          note := "fib ONLY (P3 dependency finding, recorded in the P3 notes): the counter and reversal production programs carry their `save` as a NEVER-ENTERED registration site (the untaken sseq arm — the loop is entered by `run` against the driver-collected label), so their cones contain no wpt_save; the P2 manifest listed them here and the dependency check REMOVED them" } }
  | `CerberusHeapLang.Frag.if_ => some
    { token := "if", construct := "Eif (big-step boolean guard)",
      synCtors := [Eif],
      mirror := .ctors [`CerberusHeapLang.Step.if_true,
        `CerberusHeapLang.Step.if_false],
      logic := .thms [`CerberusHeapLang.wps_if_true,
        `CerberusHeapLang.wps_if_false],
      engineEqs := [`CerberusHeapLang.stepDischarge_if_true, `CerberusHeapLang.stepDischarge_if_false],
      oneSidedWhy := "non-boolean guard: failwithI PANIC (opaque — no kernel classification possible); guard evaluation errors: kill",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.fib_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_if_true, `CerberusHeapLang.wpt_if_false],
          consumers := fibLrTotal },
      prod := some
        { consumers := loopProds } }
  | `CerberusHeapLang.Frag.run => some
    { token := "run", construct := "Erun (context-discarding jump)",
      synCtors := [Erun],
      mirror := .ctors [`CerberusHeapLang.Step.run],
      logic := .thms [`CerberusHeapLang.wps_run],
      engineEqs := [`CerberusHeapLang.stepDischarge_run],
      engineNote := "ONE-SIDED — match-given-step, the direction adequacy consumes; jump refusal channels are failwithI panics = absence of a step; see Notes 7",
      oneSidedWhy := "jump refusal channels (unbound label, arity) are failwithI panics (opaque); argument evaluation errors: kill",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.counter_loop_certified,
        `CerberusHeapLang.fib_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_run],
          consumers := fibLrTotal },
      prod := some
        { consumers := loopProds } }
  | `CerberusHeapLang.Frag.sseq_spec => some
    { token := "sseq-spec", construct := "Esseq, Specified-binder pattern",
      synCtors := [Cspecified],
      syntaxNote := "the Specified constructor pattern (Esseq is shared with the other binder rows; the pattern constructor is the distinguishing syntax)",
      mirror := .ctors [`CerberusHeapLang.Step.sseq_spec_pure,
        `CerberusHeapLang.Step.sseq_spec_annot],
      logic := .thms [`CerberusHeapLang.wps_seq_spec],
      engineEqs := [`CerberusHeapLang.step_ctx_beta_spec_pure, `CerberusHeapLang.step_ctx_beta_spec_annot],
      oneSidedWhy := "non-Specified bound value: update_env's failwithI mismatch arm (opaque panic)",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.array_sum_certified,
        `CerberusHeapLang.list_reverse_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_seq_spec],
          consumers := lrTotal },
      prod := some
        { consumers := [`CerberusHeapLang.list_reverse_certified_production] } }
  | `CerberusHeapLang.Frag.pure_sym => some
    { token := "pure-sym", construct := "Epure exit at PEsym shape",
      synCtors := [PEsym],
      mirror := .ctors [`CerberusHeapLang.Step.pure_eval]
        (note := "certified at PEsym shape — Soundness stepDischarge_pure_sym"),
      logic := .thms [`CerberusHeapLang.wps_pure],
      engineEqs := [`CerberusHeapLang.stepDischarge_pure_sym],
      oneSidedWhy := "unbound symbol: the pure evaluator's error channel (kill) — no refusal theorem yet",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.fib_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_pure],
          consumers := fibLrTotal },
      prod := some
        { consumers := [`CerberusHeapLang.fib_certified_production, `CerberusHeapLang.list_reverse_certified_production],
          note := "the counter production exits through a bare value, not a PEsym (P3 dependency finding: no wpt_pure in its cone; removed from this lane)" } }
  | `CerberusHeapLang.Frag.load_op => some
    { token := "load-op", construct := "Load0 operand-evaluation step (ACTION_EVAL)",
      synCtors := [Load0],
      syntaxNote := "the same Load0 syntax as the value-operand row; the operand-evaluation round is distinguished by its rule (wps_load_eval), which the dependency check requires",
      mirror := .ctors [`CerberusHeapLang.Step.load_eval],
      logic := .thms [`CerberusHeapLang.wps_load_eval],
      engineEqs := [`CerberusHeapLang.stepDischarge_load_eval],
      oneSidedWhy := "operand evaluation errors: kill; PEconstrained: panic — no refusal theorem yet",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.array_sum_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_load_eval],
          consumers := lrTotal },
      prod := some
        { consumers := [`CerberusHeapLang.list_reverse_certified_production] } }
  | `CerberusHeapLang.Frag.sseq_sym => some
    { token := "sseq-sym", construct := "Esseq, plain-symbol-binder pattern (bare values)",
      synCtors := [Esseq],
      syntaxNote := "Esseq shared with the wildcard row; the binder shape is distinguished by its rule (wps_seq_sym), which the dependency check requires",
      mirror := .ctors [`CerberusHeapLang.Step.sseq_sym_pure],
      logic := .thms [`CerberusHeapLang.wps_seq_sym],
      engineEqs := [`CerberusHeapLang.step_ctx_beta_sym_pure],
      oneSidedWhy := "as sseq-spec (binder beta)",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.list_reverse_certified,
        `CerberusHeapLang.struct_create_store_adequacy],
      total := some
        { rules := [`CerberusHeapLang.wpt_seq_sym],
          consumers := lrTotal },
      prod := some
        { consumers := allocProds } }
  | `CerberusHeapLang.Frag.memop_vals => some
    { token := "memop-ptreq", construct := "Ememop PtrEq (value operands)",
      synCtors := [PtrEq],
      mirror := .ctors [`CerberusHeapLang.Step.memop_ptreq],
      logic := .thms [`CerberusHeapLang.wps_memop_ptreq],
      engineEqs := [`CerberusHeapLang.step_ctx_memop],
      oneSidedWhy := "non-pointer operands and eqPtrval's differing-provenance ND fork land in offFragment (the fork is a real msum) — no refusal theorem yet",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.list_reverse_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_memop_ptreq],
          consumers := lrTotal },
      prod := some
        { consumers := [`CerberusHeapLang.list_reverse_certified_production] } }
  | `CerberusHeapLang.Frag.memop_op => some
    { token := "memop-op", construct := "Ememop PtrEq, operand-evaluation step",
      synCtors := [Ememop],
      syntaxNote := "the operand-evaluation rule wps_memop_eval is memop-GENERIC (any Ememop; PtrEq is the only memop with a value-operand rule, the previous row), so the witness is Ememop",
      mirror := .ctors [`CerberusHeapLang.Step.memop_eval],
      logic := .thms [`CerberusHeapLang.wps_memop_eval],
      engineEqs := [`CerberusHeapLang.stepDischarge_memop_eval],
      oneSidedWhy := "as load-op",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.list_reverse_certified],
      total := some
        { rules := [`CerberusHeapLang.wpt_memop_eval],
          consumers := lrTotal },
      prod := some
        { consumers := [`CerberusHeapLang.list_reverse_certified_production] } }
  | `CerberusHeapLang.Frag.store_op => some
    { token := "store-op", construct := "Store0 operand-evaluation step (ACTION_EVAL)",
      synCtors := [Store0],
      syntaxNote := "the same Store0 syntax as the value-operand row; distinguished by its rule (wps_store_eval)",
      mirror := .ctors [`CerberusHeapLang.Step.store_eval],
      logic := .thms [`CerberusHeapLang.wps_store_eval],
      engineEqs := [`CerberusHeapLang.stepDischarge_store_eval],
      oneSidedWhy := "as load-op",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
      adequacyConsumers := [`CerberusHeapLang.list_reverse_certified,
        `CerberusHeapLang.struct_create_store_adequacy],
      total := some
        { rules := [`CerberusHeapLang.wpt_store_eval],
          consumers := lrTotal },
      prod := some
        { consumers := allocProds } }
  | `CerberusHeapLang.Frag.case_value => some
    { token := "case-value", construct := "Ecase, VALUE scrutinee",
      synCtors := [Ecase],
      mirror := .ctors [`CerberusHeapLang.Step.case_value],
      logic := .thms [`CerberusHeapLang.wps_case_value],
      coneNote := "S1b: joined — branch-closure + branch-size premises explicit",
      engineEqs := [`CerberusHeapLang.step_ctx_case_value],
      engineNote := "TWO-SIDED at any MachineCtx (the ILLTYPED no-match equation step_ctx_case_illtyped is the refusal theorem's engine equation — it feeds engine_complete_caseU, not the step arm, which is why it is not listed as a step equation: the relation-coverage check rejected it there)",
      twoSided := some `CerberusHeapLang.cerberusRound_refused_case,
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ,
        `CerberusHeapLang.engine_adequacyU],
      adequacyConsumers := [`CerberusHeapLang.case_certified],
      adequacyNote := "the WP-lane adequacy regression — binder pattern, substitution TAU (CaseExhibit)",
      total := none,
      totalRed := "no total rule yet (no wpt case rule — mechanical analog of wps_case_value, no consumer); see Notes 2",
      prod := none, prodRed := "outside every lane" }
  | `CerberusHeapLang.Frag.wseq => some
    { token := "wseq-wild", construct := "Ewseq, wildcard pattern (weak sequencing)",
      synCtors := [Ewseq],
      mirror := .ctors [`CerberusHeapLang.Step.wseq_pure,
        `CerberusHeapLang.Step.wseq_annot, `CerberusHeapLang.Step.wseq_ctx]
        (note := "S1b DRIFT TEST — entered through the generic route; see Notes 6"),
      logic := .thms [`CerberusHeapLang.wps_wseq],
      engineEqs := [`CerberusHeapLang.step_ctx_wseq_pure, `CerberusHeapLang.step_ctx_wseq_annot],
      oneSidedWhy := "as sseq-wild",
      partialLane := .thms [`CerberusHeapLang.engine_adequacyJ,
        `CerberusHeapLang.engine_adequacyU],
      adequacyConsumers := [`CerberusHeapLang.wseq_certified],
      adequacyNote := "the drift-test WP-lane adequacy regression (WseqExhibit)",
      total := none,
      totalRed := "no total rule yet (no wpt wseq rule — mechanical analog of wps_wseq, no consumer); see Notes 2",
      prod := none, prodRed := "outside every lane" }
  | _ => none

/-- Supplementary rows that own NO cone constructor: premises of the
cone's rules (the evaluator tower), not capabilities. Barred from
claiming any constructor (enforced mechanically below) — a row here
can never absorb a cone or mirror extension. Its names are
existence-checked; it carries no per-row stage (no rule of its own
to depend on — the tower enters as premises). -/
def supplementaryRows : List Row := [
  { token := "pure-operands",
    construct := "pure operands: PEval / PEsym / integer PEop / PEarray_shift",
    synCtors := [], syntaxNote := "premises, not a construct",
    mirror := .declared "premises of the if/run/pure/ACTION_EVAL rules via the certified pure evaluator (Soundness evaluator bridge); no per-construct Step rule",
    logic := .declared "enters as rule premises (guard/argument/operand evaluation)",
    cone := .declared "via the peDepth side conditions carried by Frag.if_/run/load_op/memop_op/store_op",
    engineEqs := [], engineNote := "", twoSided := none, oneSidedWhy := "", refusalNA := true,
    engineDeclared := "the evaluator bridge lemmas, Soundness.lean (eval1/mapM tower)",
    partialLane := .thms [`CerberusHeapLang.engine_adequacyJ],
    adequacyConsumers := [`CerberusHeapLang.array_sum_certified,
      `CerberusHeapLang.fib_certified],
    adequacyNote := "",
    localConsumers := [], localNote := "",
    total := some
      { rules := [],
        consumers := fibLrTotal,
        note := "no rule of its own — the tower is premises" },
    totalRed := "",
    prod := some
      { consumers := [`CerberusHeapLang.fib_certified_production] },
    prodRed := "", prodRequires := [],
    supplementary := true }
]

/-! ## Checks -/

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

def renderNames (names : List Name) : String :=
  ", ".intercalate (names.map (fun n => s!"`{shortName n}`"))

def Cell.render (env : Environment) : Cell → Except String String
  | .thms names note => do
    checkNames env "theorem" names
    pure s!"OK {renderNames names}{if note == "" then "" else s!" — {note}"}"
  | .ctors names note => do
    checkNames env "ctor" names
    pure s!"OK {renderNames names}{if note == "" then "" else s!" — {note}"}"
  | .declared text => pure s!"DECLARED — {text}"
  | .red text => pure s!"RED — {text}"

/-- Does `c` (a cone) contain ANY of `targets`? -/
def hits (c : Std.HashSet Name) (targets : List Name) : List Name :=
  targets.filter (fun t => c.contains t)

/-- Accumulating failure monad for the per-row checks: every failure
    of a row is reported (not just the first), then the run throws. -/
abbrev Check := StateT (Array String) DepM

def fail (msg : String) : Check Unit := modify (·.push msg)

/-- Lift a name/kind check into the accumulating monad. -/
def checkNamesC (env : Environment) (kind : String) (names : List Name) : Check Unit :=
  match checkNames env kind names with
  | .ok () => pure ()
  | .error msg => fail msg

/-- THE STAGED DEPENDENCY CHECKS for one row. Every failure is
    recorded with the row, the stage, the consumer and the missing
    abstraction named; the run then throws with all of them. -/
def checkRow (env : Environment) (clsCone : Std.HashSet Name) (r : Row) : Check Unit := do
  if r.supplementary then return ()
  -- syntax constructors exist and are constructors
  checkNamesC env "ctor" r.synCtors
  -- P3.2 RELATION COVERAGE, DERIVED: the row's engine equations must
  -- lie in the cone of the headline classification theorem — the
  -- manifest's relation column rests on `cerberusRound_classify`, not
  -- on a declared list; and the row's refusal theorem (if any) must be
  -- a refusal classification ABOUT this construct.
  checkNamesC env "theorem" r.engineEqs
  for eq in r.engineEqs do
    unless clsCone.contains eq do
      fail s!"manifest FAIL (row '{r.token}', RELATION COVERAGE): engine equation \
        {shortName eq} is NOT in the proof cone of cerberusRound_classify — the \
        headline coverage theorem does not rest on it (a stale or decorative \
        engine-match claim)."
  match r.twoSided with
  | some t =>
    checkNamesC env "theorem" [t]
    let syn ← stmtSyntax env t
    if (hits syn r.synCtors).isEmpty then
      fail s!"manifest FAIL (row '{r.token}', RELATION TWO-SIDED): {shortName t} is \
        not about this construct (its statement reaches none of {r.synCtors.map shortName})."
    let tdeps ← typeDeps env t
    unless tdeps.contains `CerberusHeapLang.EngineOutcome.isRefusal &&
        tdeps.contains `CerberusHeapLang.outcomesU do
      fail s!"manifest FAIL (row '{r.token}', RELATION TWO-SIDED): {shortName t} does \
        not state a refusal classification (no EngineOutcome.isRefusal / outcomesU in its statement)."
  | none =>
    if r.oneSidedWhy == "" then
      fail s!"manifest FAIL (row '{r.token}'): no refusal theorem and no recorded reason \
        (the R-03 residual must be stated per row)."
  let partialRules := r.logic.thmNames
  let totalRules := match r.total with | some t => t.rules | none => []
  let witness (who : String) (n : Name) : Check Unit := do
    let syn ← stmtSyntax env n
    if (hits syn r.synCtors).isEmpty then
      fail s!"manifest FAIL (row '{r.token}', EXECUTION WITNESS): {who} \
        {shortName n} — its statement reaches none of the row's syntax \
        constructors {r.synCtors.map shortName} through program-valued \
        definitions; the theorem is not about a program containing this \
        construct."
  let requireAny (who stage : String) (n : Name) (c : Std.HashSet Name)
      (targets : List Name) (what : String) : Check Unit := do
    if targets.isEmpty then
      fail s!"manifest FAIL (row '{r.token}', {stage}): {who} {shortName n} is \
        listed but the row declares NO {what} to depend on — an inconsistent \
        row spec (remove the consumer or declare the abstraction)."
    else if (hits c targets).isEmpty then
      fail s!"manifest FAIL (row '{r.token}', {stage}): {who} {shortName n} \
        does NOT depend on any {what} {targets.map shortName} — its proof \
        bypasses the row's public abstraction (R-04)."
  -- stage: public logical rules are ABOUT the construct
  for rule in partialRules ++ totalRules do
    witness "public rule" rule
  -- stage: adequacy (engine-facing partial) consumers
  for n in r.adequacyConsumers do
    checkNamesC env "theorem" [n]
    witness "adequacy consumer" n
    let c ← cone env n
    requireAny "adequacy consumer" "RULE DEPENDENCY" n c partialRules "partial public rule"
    requireAny "adequacy consumer" "ADEQUACY DEPENDENCY" n c partialLaunchers
      "approved partial launcher"
  -- stage: local (rule-level) consumers
  for n in r.localConsumers do
    checkNamesC env "theorem" [n]
    witness "local consumer" n
    let c ← cone env n
    requireAny "local consumer" "RULE DEPENDENCY" n c (partialRules ++ totalRules)
      "public rule of the row"
  -- stage: total lane
  match r.total with
  | some t =>
    checkNamesC env "theorem" t.rules
    for n in t.derivations do
      checkNamesC env "theorem" [n]
      witness "total derivation" n
      let c ← cone env n
      requireAny "total derivation" "RULE DEPENDENCY" n c t.rules "total rule"
    for n in t.consumers do
      checkNamesC env "theorem" [n]
      witness "total consumer" n
      let c ← cone env n
      requireAny "total consumer" "RULE DEPENDENCY" n c t.rules "total rule"
      requireAny "total consumer" "ADEQUACY DEPENDENCY" n c totalLaunchers
        "approved total launcher"
  | none =>
    if r.totalRed == "" then
      fail s!"manifest FAIL (row '{r.token}'): no total lane and no RED reason"
  -- stage: production lane
  match r.prod with
  | some p =>
    for n in p.consumers do
      checkNamesC env "theorem" [n]
      witness "production consumer" n
      let c ← cone env n
      requireAny "production consumer" "RULE DEPENDENCY" n c (totalRules ++ partialRules)
        "public rule of the row"
      requireAny "production consumer" "ADEQUACY DEPENDENCY" n c prodLaunchers
        "approved production launcher"
      for req in r.prodRequires do
        unless c.contains req do
          fail s!"manifest FAIL (row '{r.token}', PRODUCTION REQUIREMENT): \
            production consumer {shortName n} does NOT depend on the required \
            abstraction {shortName req} (the row's prodRequires)."
  | none =>
    if r.prodRed == "" then
      fail s!"manifest FAIL (row '{r.token}'): no production lane and no RED reason"

/-- THE LAYER CUT + DIRECT-REFERENCE BAN over every constant of the
    positive-exhibit modules. Returns the count checked. -/
def checkLayerCut (env : Environment) (stepCtors : List Name) : DepM (Nat × Array String) := do
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let isCut (n : Name) : Bool :=
    !isOperational n && (cutNames.contains n || cutModules.contains (modOf env n))
  let mut checked := 0
  let mut failures : Array String := #[]
  for n in names do
    if n.isInternalDetail then continue
    unless positiveExhibitModules.contains (modOf env n) do continue
    let body ← valueDeps env n
    -- direct-reference ban
    for c in body do
      if isDirectBanned stepCtors c then
        failures := failures.push s!"manifest FAIL (DIRECT-REFERENCE BAN): positive-exhibit declaration \
          {shortName n} ({modOf env n}) names the operational constant \
          {shortName c} directly in its body."
    -- layer cut: DFS from the body, stop at approved crossings, fail at
    -- any operational name, with the path reported
    let mut parent : Std.HashMap Name Name := {}
    let mut seen : Std.HashSet Name := {}
    let mut stack : Array (Name × Name) := body.map (fun c => (c, n))
    let mut reported := false
    while h : stack.size > 0 do
      let (c, p) := stack[stack.size - 1]
      stack := stack.pop
      if seen.contains c then continue
      if !isOurs env c then continue
      seen := seen.insert c
      parent := parent.insert c p
      if isOperational c then
        let mut path : List String := [shortName c]
        let mut cur := c
        let mut fuel := 64
        while fuel > 0 do
          fuel := fuel - 1
          match parent.get? cur with
          | some q => path := shortName q :: path; cur := q
          | none => fuel := 0
        unless reported do
          failures := failures.push s!"manifest FAIL (LAYER CUT): positive-exhibit declaration \
            {shortName n} ({modOf env n}) reaches the operational name \
            {shortName c} WITHOUT crossing the approved logic/adequacy layer; \
            path: {" → ".intercalate path}"
          reported := true
        continue
      if isCut c then continue
      for d in ← allDeps env c do
        if !seen.contains d then stack := stack.push (d, c)
    checked := checked + 1
  return (checked, failures)

def liftE {α : Type} (e : Except String α) : MetaM α :=
  match e with
  | .ok a => pure a
  | .error msg => throwError msg

end CapabilityManifest

open CapabilityManifest in
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
  -- THE LAUNCHER SETS exist (fail-closed: a renamed launcher is a
  -- red run, never a silently-empty requirement).
  liftE (checkNames env "theorem" (partialLaunchers ++ totalLaunchers ++ prodLaunchers))
  match env.find? `CerberusHeapLang.instLanguageCoreRtMemEmptyCoreRVal, env.find? `CerberusHeapLang.instIrisGS with
  | some _, some _ => pure ()
  | _, _ => throwError "manifest FAIL: the Lang instances named in the cut allowlist are missing"
  -- SOUNDNESS OF THE PRUNING (fail-closed): every cone-check target
  -- lives in a target module, and no leaf module imports one.
  for r in rows do
    let targets := r.logic.thmNames ++ (match r.total with | some t => t.rules | none => [])
      ++ r.prodRequires
    for t in targets do
      unless targetModules.contains (modOf env t) do
        throwError "manifest FAIL: row '{r.token}' names {t} as a rule/requirement, \
          but it lives in {modOf env t}, outside the target modules the cone \
          traversal is pruned for; extend targetModules deliberately."
  for l in partialLaunchers ++ totalLaunchers ++ prodLaunchers do
    unless targetModules.contains (modOf env l) do
      throwError "manifest FAIL: launcher {l} lives in {modOf env l}, outside the target modules."
  for m in leafModules do
    let closure ← liftE (importClosure env m)
    for t in targetModules do
      if closure.contains t then
        throwError "manifest FAIL: leaf module {m} (pruned by the cone traversal) \
          imports target module {t} — the pruning would be UNSOUND; fix leafModules."
  -- P3.2: THE HEADLINE RELATION-COVERAGE THEOREM exists, is a theorem,
  -- and is indexed by the cone (`Frag`) with the classification type
  -- (`RoundClass`) — the relation column below is derived from it.
  let clsName := `CerberusHeapLang.cerberusRound_classify
  let some (.thmInfo clsInfo) := env.find? clsName
    | throwError "manifest FAIL: the relation-coverage theorem {clsName} is missing or not a theorem"
  let clsTypeConsts := clsInfo.type.getUsedConstants
  unless clsTypeConsts.contains `CerberusHeapLang.Frag do
    throwError "manifest FAIL: {clsName} is not indexed by the cone `Frag` — its statement \
      does not quantify over Frag; the relation coverage cannot be derived from it."
  unless clsTypeConsts.contains `CerberusHeapLang.RoundClass do
    throwError "manifest FAIL: {clsName} does not conclude the RoundClass classification."
  let some (.inductInfo rcInfo) := env.find? `CerberusHeapLang.RoundClass
    | throwError "manifest FAIL: inductive CerberusHeapLang.RoundClass not found"
  let expectedArms := [`CerberusHeapLang.RoundClass.value_done, `CerberusHeapLang.RoundClass.value_annot,
    `CerberusHeapLang.RoundClass.step, `CerberusHeapLang.RoundClass.refused]
  unless rcInfo.ctors == expectedArms do
    throwError "manifest FAIL: RoundClass arms changed ({rcInfo.ctors}); the manifest's \
      relation-coverage semantics (value_done / value_annot / step / refused) must be re-read."
  -- THE LAYER CUT over the positive-exhibit modules (the R-02 bypass
  -- class), then THE STAGED DEPENDENCY CHECKS per row (the R-04 class,
  -- plus the P3.2 relation-coverage derivation) — every failure of
  -- both is reported, then the run throws. The classification cone is
  -- computed UNPRUNED (its engine equations live in Soundness).
  let ((cutChecked, cutFailures), cache) := (checkLayerCut env stepInfo.ctors).run {}
  let (clsCone, cache) := (cone env clsName (pruneLeaves := false)).run cache
  let (rowFailures, _) := ((do for r in rows do checkRow env clsCone r : Check Unit).run #[] |>.run cache) |>.map (·.2) id
  let failures := cutFailures ++ rowFailures
  unless failures.isEmpty do
    throwError "{failures.size} HARD-check failure(s) (layer cut / dependency certification):\n{"\n".intercalate failures.toList}"
  -- THE LAYER CUT over the positive-exhibit modules.
  -- CHECK-ONLY MODE (scripts/test_unit.sh --fast): every HARD check
  -- above has run (throws are fail-closed); the rendering — whose
  -- diff against the committed copy is the SPEEDBUMP drift mechanic —
  -- is skipped. Selected by the environment variable so the script
  -- stays a plain `lake env lean` target.
  if (← IO.getEnv "CAPABILITY_MANIFEST_CHECK_ONLY").isSome then
    IO.println s!"CAPABILITY MANIFEST HARD CHECKS OK: {rows.length} rows \
      (cone-derived, mirror coverage exact), staged dependency \
      certification passed for every listed consumer, layer cut + \
      direct-reference ban hold over {cutChecked} positive-exhibit \
      declarations; rendering skipped (check-only)."
    return
  let render (c : Cell) : MetaM String := liftE (c.render env)
  let names (ns : List Name) : String := renderNames ns
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
  IO.println "findings F-01/F-09; cone-derived since Phase-1 S1c; DEPENDENCY-"
  IO.println "CERTIFIED since alloc arc P3 — re-audit R-04). Every claims"
  IO.println "surface defers to it: a construct may be claimed at exactly its"
  IO.println "row's level, no more. Enforcement: `scripts/test_unit.sh` gate 4"
  IO.println "(drift + README scope tie + every check below fail-closed)."
  IO.println ""
  IO.println "Row provenance — DERIVED vs CHECKED vs DEPENDENCY-CERTIFIED vs"
  IO.println "DECLARED is stated in the script header. In brief: the ROW SET is"
  IO.println "DERIVED (enumerated from the `Frag` cone's constructor list in the"
  IO.println "built environment, in declaration order; a cone constructor without"
  IO.println "a row mapping fails the run) and the `Step` mirror coverage is"
  IO.println "DERIVED (every Step constructor claimed by exactly one row's mirror"
  IO.println "cell); `OK` cells are name-and-kind CHECKED; and EVERY CONSUMER"
  IO.println "LISTED IN A LANE IS DEPENDENCY-CERTIFIED — its statement's program"
  IO.println "text contains the row's syntax constructor (the execution witness,"
  IO.println "computed through program-valued definitions only), its proof cone"
  IO.println "contains a public rule of the row (partial rule for adequacy/local"
  IO.println "consumers, total rule for the total lane, either for production),"
  IO.println "and — for adequacy/total/production consumers — an approved"
  IO.println "launcher of that lane; production consumers additionally carry the"
  IO.println "row's required abstractions (create: `wpt_create` AND"
  IO.println "`launchResources`). A listed name failing any of these THROWS (the"
  IO.println "run is red, gate 4 is red) — an `OK` consumer therefore means its"
  IO.println "PROOF FLOWS THROUGH the row's public abstraction, not merely that a"
  IO.println "declaration of that name exists (the 2026-09-01 re-audit's R-04"
  IO.println "closed). Additionally the LAYER CUT holds over every constant of the"
  IO.println s!"positive-exhibit modules ({cutChecked} declarations checked this run):"
  IO.println "no dependency path from an exhibit reaches an operational name"
  IO.println "(`Step.*`, the engine-round projections, the per-construct engine"
  IO.println "equations, `driveJ_step`/`driverDone_step`) except through the"
  IO.println "approved logic/adequacy layer, and no exhibit body names one"
  IO.println "directly. The ENGINE-MATCH column is DERIVED (alloc arc P3.2, R-03):"
  IO.println "every row's engine equations are checked to lie in the proof cone of"
  IO.println "the headline relation-coverage theorem `cerberusRound_classify`"
  IO.println "(Round.lean — exhaustive over `Frag`), and a row is TWO-SIDED at"
  IO.println "the refusal arm only if it names a refusal-classification theorem"
  IO.println "about its construct (Notes 7). Lane prose and construct"
  IO.println "descriptions are DECLARED. The supplementary evaluator row (last)"
  IO.println "owns no constructor and is mechanically barred from claiming any."
  IO.println ""
  IO.println "| Construct | Level | Syntax witness | Mirror (Step) | Logic (partial rules) | Cone (Frag) | Engine match (relation coverage) | Partial adequacy | Adequacy consumers | Local consumers | Total lane | Production lane |"
  IO.println "|---|---|---|---|---|---|---|---|---|---|---|---|"
  for r in rows do
    let cells ← [r.mirror, r.logic, r.cone].mapM render
    let engine := if r.supplementary then s!"DECLARED — {r.engineDeclared}" else
      let eqs := s!"DERIVED {names r.engineEqs} (in the cone of `cerberusRound_classify`)"
      let two := match r.twoSided with
        | some t => s!"; TWO-SIDED at the refusal arm: `{shortName t}`"
        | none => if r.refusalNA then s!"; refusal arm N/A — {r.oneSidedWhy}"
          else s!"; ONE-SIDED at the refusal arm — {r.oneSidedWhy}"
      s!"{eqs}{if r.engineNote == "" then "" else s!" — {r.engineNote}"}{two}"
    let partialC ← render r.partialLane
    let cells := cells ++ [engine, partialC]
    let syn := if r.synCtors.isEmpty then s!"DECLARED — {r.syntaxNote}"
      else s!"OK {names r.synCtors}{if r.syntaxNote == "" then "" else s!" — {r.syntaxNote}"}"
    let adeq := s!"CERTIFIED {names r.adequacyConsumers}{if r.adequacyNote == "" then "" else s!" — {r.adequacyNote}"}"
    let loc := if r.localConsumers.isEmpty then "—"
      else s!"CERTIFIED {names r.localConsumers}{if r.localNote == "" then "" else s!" — {r.localNote}"}"
    let tot := match r.total with
      | some t =>
        let rules := if t.rules.isEmpty then "rules: (premises)" else s!"rules: {names t.rules}"
        let ders := if t.derivations.isEmpty then "" else s!"; derivations: {names t.derivations}"
        s!"CERTIFIED {rules}{ders}; consumers: {names t.consumers}{if t.note == "" then "" else s!" — {t.note}"}"
      | none => s!"RED — {r.totalRed}"
    let prod := match r.prod with
      | some p =>
        let req := if r.prodRequires.isEmpty then "" else s!" (each cone required to contain {names r.prodRequires})"
        s!"CERTIFIED {names p.consumers}{req}{if p.note == "" then "" else s!" — {p.note}"}"
      | none => s!"RED — {r.prodRed}"
    IO.println s!"| {r.construct} | {r.level} | {syn} | {" | ".intercalate cells} | {adeq} | {loc} | {tot} | {prod} |"
  IO.println ""
  IO.println "## Notes (the registered honesty items behind the RED cells and the instrument's limits)"
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
  IO.println "   `list_reverse_terminates`; `exhibitA_total` (the straight-line"
  IO.println "   create-free program at drive fuel 6 — alloc arc P2 retired its"
  IO.println "   engineSteps trace for the total route). Negative test:"
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
  IO.println "   logic-driven positive control. P3 DEPENDENCY FINDINGS (the"
  IO.println "   instrument's first catch on the live tree): the counter and"
  IO.println "   reversal productions are NOT `save`-rule consumers (their"
  IO.println "   `save` is the never-entered registration site) and the"
  IO.println "   counter is not a `pure-sym` consumer — the P2 manifest listed"
  IO.println "   them so; the dependency check removed the three attributions"
  IO.println "   (record: docs/2026-09-01_p3-notes.md)."
  IO.println "4. **`create` has PUBLIC partial+total rules, LAUNCHABLE, with"
  IO.println "   DEPENDENCY-CERTIFIED consumers** (alloc arc P1 rules+launch;"
  IO.println "   P2 whole-program consumers, R-01/R-02 closed; P3 the cone"
  IO.println "   checks): the public `wps_create`/`wpt_create` take the abstract"
  IO.println "   finite allocation capacity `allocCap (req :: rest)` (Heap.lean —"
  IO.println "   internally the cursor fragment + a pure plan-fit; the OOM kill"
  IO.println "   arm is excluded by the plan, never assumed away) and bind an"
  IO.println "   EXISTENTIAL pointer; their statements contain no"
  IO.println "   AllocCursor/lastAddress/nextAllocId/freshBase/cursorOwn"
  IO.println "   (grep-checked, docs/2026-09-01_p1-notes.md). The exact-cursor"
  IO.println "   rules are internal (`wps_create_cursor_internal`/"
  IO.println "   `wpt_create_cursor_internal`, heap-implementation use only)."
  IO.println "   LAUNCH: the allocation-aware launchers"
  IO.println "   (`spike_step_adequacy_alloc`, `wpt_engine_boundU/J_alloc`,"
  IO.println "   `wpt_strongly_normalizing_alloc`) grant `allocCap` from real"
  IO.println "   Cerberus memory through the one `launchResources` helper under"
  IO.println "   `LaunchCoh` (cursor key 0 NONEMPTY; CohG's allocator-health"
  IO.println "   facts non-vacuous). Chain-closing total consumer:"
  IO.println "   `alloc_create_launch_smoke` (a driveU `.done` equation at fuel"
  IO.println "   exactly 2 from prodMem₀). Adequacy (partial) consumer:"
  IO.println "   `struct_create_store_adequacy` through"
  IO.println "   `spike_engine_adequacy_alloc`. Local consumers:"
  IO.println "   `alloc_two_creates_wps`, `alloc_create_wpt`,"
  IO.println "   `struct_create_store_wps`. Total derivations:"
  IO.println "   `progAProd_wpt`/`ctrProd_wpt`/`lrProd_wpt`; production"
  IO.println "   consumers: the three allocating exports, each cone REQUIRED to"
  IO.println "   contain `wpt_create` and `launchResources` (the charter's \"not"
  IO.println "   merely Step.create\"). The public rules also export the fresh"
  IO.println "   pointer's pure address bounds (0 < addrOf p < 2^64), carried by"
  IO.println "   `allocCap`'s machine-bounded hidden cursor. Plant transcripts:"
  IO.println "   docs/2026-09-01_p2-notes.md (R-01/R-02) and"
  IO.println "   docs/2026-09-01_p3-notes.md (R-04)."
  IO.println "5. **Interior (sub-allocation) access is GENERIC** (Phase 2,"
  IO.println "   F-04 retired): one typed-subrange load and one store rule"
  IO.println "   (`wps_load_at`/`wps_store_at` over views; whole-cell forms"
  IO.println "   `wps_load_cell_at`/`wps_store_cell_at`), certified once"
  IO.println "   against loadM/storeM. The former int-specific and node-"
  IO.println "   specific interior rules are DELETED; array element, node"
  IO.println "   field, and struct field rules are client instances inside"
  IO.println "   their exhibit modules. The store/load rows list the generic"
  IO.println "   forms among their partial rules (a client consuming only the"
  IO.println "   subrange form is a rule consumer of the row)."
  IO.println "6. **`Ewseq` wildcard is the S1b DRIFT TEST** (arc plan Phase 1"
  IO.println "   item 7; design record §8 item 8): a NEW non-example construct"
  IO.println "   passed through the GENERIC route — relation rules + cone/"
  IO.println "   decomposition arms + `engine_step_matchU` arms + `wps_wseq` +"
  IO.println "   the consumer regression; the Rules/Wps/Adequacy strata and the"
  IO.println "   Language instance needed ZERO changes, and this generator"
  IO.println "   FAILED CLOSED on the extended Step/Frag constructor lists until"
  IO.println "   this row landed. Ewseq at spec/sym binder patterns stays a"
  IO.println "   registered divergence (README)."
  IO.println "7. **The engine-match column is DERIVED from the relation-coverage"
  IO.println "   theorem** (alloc arc P3.2; re-audit R-03 — Round.lean): the"
  IO.println "   engine-facing one-round relation is NAMED, `CerberusRound M aid`"
  IO.println "   = the graph of the discharged `step_ctx` round (the singleton"
  IO.println "   successful-next of `outcomesU`), independent of every example"
  IO.println "   and of the mirror; and `cerberusRound_classify` classifies EVERY"
  IO.println "   well-sized `Frag` configuration (SeqWF context, cons env) into"
  IO.println "   exactly one of value_done (PROGRAM-DONE, exact) / value_annot"
  IO.println "   (REMOVE-ANNOT, exact — the engine's successful-next at an"
  IO.println "   annotated value, which the mirror's value protocol does NOT"
  IO.println "   step: the reason a global iff is the wrong shape) / step (the"
  IO.println "   mirror steps, and then `Step M c c' ↔ CerberusRound M aid c c'`"
  IO.println "   for EVERY c' — `step_iff_cerberusRound`, two-sided; mirror"
  IO.println "   determinism falls out) / refused (mirror stuck at a non-value —"
  IO.println "   ¬NotStuck, the set adequacy excludes). Each row's engine"
  IO.println "   equations are CHECKED to lie in that theorem's proof cone (a"
  IO.println "   stale or decorative engine-match claim throws), so the column"
  IO.println "   is derived, not declared. THE RESIDUAL, per row: the `refused`"
  IO.println "   arm says nothing about the ENGINE at a mirror-stuck"
  IO.println "   configuration. Rows marked TWO-SIDED carry a refusal"
  IO.println "   classification theorem (`cerberusRound_refused_store/_load/"
  IO.println "   _create/_case`: mirror stuck ⇒ the engine's round is a"
  IO.println "   singleton refusal — memory kill or ILLTYPED); rows marked"
  IO.println "   ONE-SIDED state why (mostly `failwithI` PANIC channels — an"
  IO.println "   OPAQUE constant with no equations, so a kernel classification"
  IO.println "   of the panic as \"not a successful-next\" is impossible, not"
  IO.println "   merely unproved; plus the memop ND fork and save's EVAL round"
  IO.println "   on non-value params). The machine lines RELATION-REFUSAL-"
  IO.println "   TWO-SIDED / -ONE-SIDED list the split. RelSemCore disclaimer:"
  IO.println "   `CerberusRound` is NOT bridged to the semantics repo's own"
  IO.println "   RelSem spine (README, two presentations one engine); a future"
  IO.println "   type layer claiming RelSemCore must prove that bridge first."
  IO.println "8. **What the dependency certification does NOT claim** (the"
  IO.println "   instrument's own limits, measured before installation —"
  IO.println "   docs/2026-09-01_p3-notes.md): (a) it does not tie a public rule"
  IO.println "   to its `Step` constructor by cone membership — in Lean 4 every"
  IO.println "   `cases` on `Step` names every constructor (`Step.casesOn`), so"
  IO.println "   that test is vacuous; the rule↔relation tie is the rule's"
  IO.println "   statement being ABOUT the construct (checked) plus the engine"
  IO.println "   certification of the relation itself (the mirror/engine-match"
  IO.println "   columns); (b) the execution witness is SYNTACTIC (the program"
  IO.println "   text contains the constructor) — that the construct is actually"
  IO.println "   EXECUTED is witnessed by the rule dependency (a rule for a"
  IO.println "   construct that never executes is not needed by the proof: the"
  IO.println "   never-entered `save` finding in Notes 3 is exactly this"
  IO.println "   discrimination working); (c) rows sharing syntax (Store0 for"
  IO.println "   store/store-op, Load0 for load/load-op, Esseq for the binder"
  IO.println "   rows) are told apart by their rules, not their syntax."
  IO.println ""
  IO.println "## Machine-readable scope lines (consumed by test_unit.sh gate 4)"
  IO.println ""
  IO.println "Line semantics (2026-09-01 P0 renamed the former FULL-ROW aggregate"
  IO.println "CORE-DRIVE-ROW and split the lanes; P3 made every lane member"
  IO.println "dependency-certified): CORE-DRIVE-ROW = the drive-lane core cells"
  IO.println "(mirror/cone/engine-match/partial-adequacy) green, at least one"
  IO.println "DEPENDENCY-CERTIFIED adequacy consumer, AND a partial logic rule"
  IO.println "that is ABOUT the construct. TOTAL-LANE / PRODUCTION-LANE list the"
  IO.println "rows whose lane is non-red — every consumer in a listed lane has"
  IO.println "passed the rule / launcher / witness cone checks (a failing one is"
  IO.println "a red run, not a listed row). LOGIC-RULE-LANE lists rows with a"
  IO.println "partial rule. `create` joined TOTAL-LANE at alloc arc P1 and"
  IO.println "PRODUCTION-LANE at P2; P3 certifies both by dependency — Notes 4."
  IO.println ""
  let exportable := rows.filter (·.exportable) |>.map (·.token)
  let coreDriveRows := rows.filter (·.coreDriveRow) |>.map (·.token)
  let logicRows := rows.filter (fun r => !r.logic.isRed) |>.map (·.token)
  let totalRows := rows.filter (fun r => r.total.isSome) |>.map (·.token)
  let prodRows := rows.filter (fun r => r.prod.isSome) |>.map (·.token)
  let localOnly := rows.filter (fun r => !r.exportable) |>.map (·.token)
  IO.println "```"
  IO.println s!"ADEQUACY-EXPORTABLE: {" ".intercalate exportable}"
  IO.println s!"CORE-DRIVE-ROW: {" ".intercalate coreDriveRows}"
  IO.println s!"LOGIC-RULE-LANE: {" ".intercalate logicRows}"
  IO.println s!"TOTAL-LANE: {" ".intercalate totalRows}"
  IO.println s!"PRODUCTION-LANE: {" ".intercalate prodRows}"
  IO.println s!"LOCAL-RULE-ONLY: {" ".intercalate localOnly}"
  IO.println s!"DEPENDENCY-CERTIFIED: yes (staged rule/launcher/witness cone checks + layer cut over {cutChecked} positive-exhibit declarations)"
  let twoSidedRows := rows.filter (fun r => r.twoSided.isSome) |>.map (·.token)
  let oneSidedRows := rows.filter (fun r => !r.supplementary && r.twoSided.isNone && !r.refusalNA) |>.map (·.token)
  let naRows := rows.filter (fun r => !r.supplementary && r.refusalNA) |>.map (·.token)
  IO.println s!"RELATION-COVERAGE: derived from cerberusRound_classify over Frag ({coneRows.size} rows; arms value_done value_annot step refused; the step arm two-sided by step_iff_cerberusRound)"
  IO.println s!"RELATION-REFUSAL-TWO-SIDED: {" ".intercalate twoSidedRows}"
  IO.println s!"RELATION-REFUSAL-ONE-SIDED: {" ".intercalate oneSidedRows}"
  IO.println s!"RELATION-REFUSAL-NA: {" ".intercalate naRows} (values are never mirror-stuck; both value rounds exact)"
  IO.println "```"
