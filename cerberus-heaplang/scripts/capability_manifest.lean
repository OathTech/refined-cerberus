/-
capability_manifest.lean — the per-construct coverage REPORT
(a claim-point SPEEDBUMP, [USER 2026-09-02] — "speedbumps, not
adversarial gates"; P3.5 cut the 1,507-line dependency-certifying
generator down to this: docs/2026-09-02_p3.5-notes.md).

What it does, and nothing else:
1. ROWS ARE DERIVED: the row set is `Frag`'s constructor list read
   out of the built environment. A constructor with no `ruleFor`
   mapping prints a MISSING row and the run exits nonzero — the
   fragment cannot grow past this report silently.
2. ONE LINE PER CONSTRUCTOR: constructor → the logical rule theorem
   that covers it (`ruleFor` below).
3. THE ONE CHECK THAT HAS CAUGHT REAL OVERCLAIMS: the named rule
   exists, is a theorem, and lies in the proof-term dependency cone
   of at least one declaration of an exhibit module (`*Exhibit`) —
   the report says which. A rule consumed by no exhibit is a red row
   (a construct "covered" by a rule nobody's proof flows through is
   the 2026-09-01 re-audit's R-01/R-04 class of overclaim).

Output: one markdown table + one machine line. Deterministic.
Run (from cerberus-heaplang/):
  ../scripts/capped ~/.elan/bin/lake env lean scripts/capability_manifest.lean \
    > docs/CAPABILITY_MANIFEST.md
-/
import CerberusHeapLang

open Lean

namespace CapabilityManifest

/-- THE MAPPING: fragment constructor → the rule theorem(s) covering it
    (kill/free arc K3: a constructor may be covered by several
    kind-specific rules — `Frag.kill` by the static dispose `wps_kill` AND
    the dynamic `wps_free`; K5: `Frag.load`/`Frag.store` by the object rule
    AND the region rule `wps_load_region_at`/`wps_store_region_at`; every
    listed rule is checked separately). An empty list is a MISSING row. -/
def ruleFor : Name → List Name
  | `CerberusHeapLang.Frag.val_pure   => [`CerberusHeapLang.wps_ofVal]
  | `CerberusHeapLang.Frag.store      => [`CerberusHeapLang.wps_store, `CerberusHeapLang.wps_store_region_at]
  | `CerberusHeapLang.Frag.load       => [`CerberusHeapLang.wps_load_at, `CerberusHeapLang.wps_load_region_at]
  | `CerberusHeapLang.Frag.create     => [`CerberusHeapLang.wps_create]
  | `CerberusHeapLang.Frag.kill       => [`CerberusHeapLang.wps_kill, `CerberusHeapLang.wps_free]
  | `CerberusHeapLang.Frag.kill_op    => [`CerberusHeapLang.wps_kill_eval]
  | `CerberusHeapLang.Frag.alloc      => [`CerberusHeapLang.wps_alloc]
  | `CerberusHeapLang.Frag.alloc_op   => [`CerberusHeapLang.wps_alloc_eval]
  | `CerberusHeapLang.Frag.sseq       => [`CerberusHeapLang.wps_seq]
  | `CerberusHeapLang.Frag.annot      => [`CerberusHeapLang.wps_annot]
  | `CerberusHeapLang.Frag.save       => [`CerberusHeapLang.wps_save]
  | `CerberusHeapLang.Frag.if_        => [`CerberusHeapLang.wps_if_true]
  | `CerberusHeapLang.Frag.run        => [`CerberusHeapLang.wps_run]
  | `CerberusHeapLang.Frag.sseq_spec  => [`CerberusHeapLang.wps_seq_spec]
  | `CerberusHeapLang.Frag.pure_sym   => [`CerberusHeapLang.wps_pure]
  | `CerberusHeapLang.Frag.load_op    => [`CerberusHeapLang.wps_load_eval]
  | `CerberusHeapLang.Frag.sseq_sym   => [`CerberusHeapLang.wps_seq_sym]
  | `CerberusHeapLang.Frag.memop_vals => [`CerberusHeapLang.wps_memop_ptreq]
  | `CerberusHeapLang.Frag.memop_op   => [`CerberusHeapLang.wps_memop_eval]
  | `CerberusHeapLang.Frag.store_op   => [`CerberusHeapLang.wps_store_eval]
  | `CerberusHeapLang.Frag.case_value => [`CerberusHeapLang.wps_case_value]
  | `CerberusHeapLang.Frag.wseq       => [`CerberusHeapLang.wps_wseq]
  | _ => []

/-- DECLARED NO-RULE constructors: in the fragment, MIRRORED and
    CLASSIFIED, with no logical rule BY DESIGN of the current slice —
    each with the record that says so and names the slice that adds the
    rule. Printed as an explicit row (not red): the absence is stated, not
    silent. An unmapped, undeclared constructor is still MISSING and red.
    - `Frag.call` (calls arc C2, 2026-09-03): the procedure call is
      mirrored (`Step.call`/`Step.ret`), certified (`engine_step_matchU`)
      and classified (`complete_call`/`complete_ret`); the call rule and
      the specification table are C3 (docs/2026-09-03_c2-notes.md). -/
def declaredNoRule : Name → Option String
  | `CerberusHeapLang.Frag.call =>
    some "NO RULE YET (declared: calls arc C2 — mirror-level only; the call rule is C3, \
      docs/2026-09-03_c2-notes.md)"
  | _ => none

/-! ## Environment reflection -/

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

def isOurs (env : Environment) (n : Name) : Bool :=
  (modOf env n).getRoot == `CerberusHeapLang

def short (n : Name) : String :=
  let s := n.toString
  if s.startsWith "CerberusHeapLang." then (s.drop "CerberusHeapLang.".length).toString else s

/-- Statement + body constants of a constant (theorem bodies included:
    `ConstantInfo.value?` is `none` for theorems in this toolchain). -/
def usedConstants (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    (match ci with
     | .thmInfo t => t.value.getUsedConstants
     | .defnInfo d => d.value.getUsedConstants
     | .opaqueInfo o => o.value.getUsedConstants
     | _ => #[])

/-- Transitive import closure of a module (from the environment header). -/
def importClosure (env : Environment) (m : Name) : Std.HashSet Name := Id.run do
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[m]
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some i := mods.findIdx? (· == c) then
      for imp in data[i]!.imports do stack := stack.push imp.module
  return seen

/-- Memoized dependency table (one `getUsedConstants` per constant). -/
abbrev DepM := StateM (Std.HashMap Name (Array Name))

def depsOf (env : Environment) (n : Name) : DepM (Array Name) := do
  if let some d := (← get).get? n then return d
  let d := match env.find? n with | some ci => usedConstants ci | none => #[]
  modify (·.insert n d)
  return d

/-- The proof-term dependency cone of a set of seeds through OUR
    constants. A constant is expanded only if its module can reach a
    rule module at all (its import closure contains one) — a module
    that imports no rule module cannot lie on a path to a rule, so
    pruning there is sound and skips the relation/engine
    certification's large proof terms. -/
partial def cone (env : Environment) (canReach : Name → Bool) (seeds : Array Name) :
    DepM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack := seeds
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains c || !isOurs env c then continue
    seen := seen.insert c
    if !canReach (modOf env c) then continue
    for d in ← depsOf env c do
      if !seen.contains d then stack := stack.push d
  return seen

/-! ## The report -/

#eval show CoreM Unit from do
  let env ← getEnv
  let some (.inductInfo fragInfo) := env.find? `CerberusHeapLang.Frag
    | throwError "manifest FAIL: inductive CerberusHeapLang.Frag not found"
  -- the exhibit modules, from the environment, sorted for determinism
  let exhibits : Array Name :=
    (env.header.moduleNames.filter fun m =>
      m.getRoot == `CerberusHeapLang && m.toString.endsWith "Exhibit")
    |>.qsort (fun a b => a.toString < b.toString)
  if exhibits.isEmpty then throwError "manifest FAIL: no *Exhibit module in the environment"
  -- the rule modules (of the mapped rules that exist) + the pruning predicate
  let ruleMods : Std.HashSet Name := Id.run do
    let mut s : Std.HashSet Name := {}
    for ctor in fragInfo.ctors do
      for r in ruleFor ctor do
        if env.contains r then s := s.insert (modOf env r)
    return s
  let closures : Std.HashMap Name (Std.HashSet Name) := Id.run do
    let mut m : Std.HashMap Name (Std.HashSet Name) := {}
    for mod in env.header.moduleNames do
      if mod.getRoot == `CerberusHeapLang then m := m.insert mod (importClosure env mod)
    return m
  let canReach (mod : Name) : Bool :=
    match closures.get? mod with
    | some cl => ruleMods.any (fun r => cl.contains r)
    | none => true  -- unknown module: never prune (fail-closed)
  -- constants by module (our package only)
  let byModule : Std.HashMap Name (Array Name) := env.constants.fold
    (fun acc n _ =>
      if n.isInternalDetail then acc else
      let m := modOf env n
      if m.getRoot == `CerberusHeapLang then acc.insert m ((acc.getD m #[]).push n) else acc) {}
  -- one cone per exhibit module, sharing the dependency table
  let mut table : Std.HashMap Name (Array Name) := {}
  let mut cones : Array (Name × Std.HashSet Name) := #[]
  for ex in exhibits do
    let (c, table') := (cone env canReach (byModule.getD ex #[])).run table
    table := table'
    cones := cones.push (ex, c)
  -- rows
  let mut lines : Array String := #[]
  let mut red : Nat := 0
  let mut ruleRows : Nat := 0
  for ctor in fragInfo.ctors do
    match ruleFor ctor with
    | [] =>
      match declaredNoRule ctor with
      | some why =>
        lines := lines.push s!"| `{short ctor}` | {why} | — |"
      | none =>
        lines := lines.push s!"| `{short ctor}` | **MISSING** — no rule mapped (add a `ruleFor` arm) | — |"
        red := red + 1
    | rs =>
      for r in rs do
        ruleRows := ruleRows + 1
        match env.find? r with
        | some (.thmInfo _) =>
          let users := cones.filter (fun (_, c) => c.contains r) |>.map (fun (ex, _) => short ex)
          if users.isEmpty then
            lines := lines.push s!"| `{short ctor}` | `{short r}` | **RED** — consumed by no exhibit |"
            red := red + 1
          else
            lines := lines.push s!"| `{short ctor}` | `{short r}` | {", ".intercalate users.toList} |"
        | some _ =>
          lines := lines.push s!"| `{short ctor}` | `{short r}` | **RED** — exists but is not a theorem |"
          red := red + 1
        | none =>
          lines := lines.push s!"| `{short ctor}` | `{short r}` | **RED** — not in the environment |"
          red := red + 1
  IO.println "# The capability manifest"
  IO.println ""
  IO.println "GENERATED by `scripts/capability_manifest.lean` — do not hand-edit; regenerate with"
  IO.println "`../scripts/capped ~/.elan/bin/lake env lean scripts/capability_manifest.lean > docs/CAPABILITY_MANIFEST.md`"
  IO.println "(from `cerberus-heaplang/`). A claim-point SPEEDBUMP report ([USER 2026-09-02]):"
  IO.println "`scripts/test_unit.sh` regenerates it and reports drift or a red row."
  IO.println ""
  IO.println "One row per (constructor of the fragment `Frag`, covering rule) pair — the"
  IO.println "constructors are read from the built environment; an unmapped constructor"
  IO.println "is a MISSING row and a red run unless it is a DECLARED no-rule constructor"
  IO.println "(`declaredNoRule`: in the fragment, mirrored and classified, no rule by design"
  IO.println "of the current slice — the row states it); a constructor with several kind-specific"
  IO.println "rules (`Frag.kill`: the static dispose and the dynamic free) has one row per"
  IO.println "rule. The rule column names the logical rule covering the construct; the last"
  IO.println "column lists the exhibit modules whose proofs actually depend on that rule"
  IO.println "(proof-term dependency cone through this package's constants). A rule"
  IO.println "consumed by no exhibit is a red row: the construct has a rule but no client."
  IO.println ""
  IO.println "| Fragment constructor | Rule | Consumed by (exhibit modules) |"
  IO.println "|---|---|---|"
  for l in lines do IO.println l
  IO.println ""
  IO.println s!"MANIFEST: {fragInfo.ctors.length} constructors, {ruleRows} rule rows, {red} red, {exhibits.size} exhibit modules"
  if red > 0 then
    throwError "capability manifest: {red} red/MISSING row(s) — see the table above"

end CapabilityManifest
