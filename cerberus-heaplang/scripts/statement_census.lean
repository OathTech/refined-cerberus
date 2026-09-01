/-
statement_census.lean — the STATEMENT-SURFACE CENSUS (read-only
reporting instrument; pattern: signature_snapshot.lean).

For each pinned exported theorem, collect the constants occurring in
its STATEMENT (the theorem's type — proofs are not inspected) and
bin them by module of origin:

  ENGINE     — any module outside the bins below. By construction of
               this package's imports these are exactly the
               cerberus-lean semantics modules (the generated
               engine: CerbMem, Core_*, Driver, CerbND, Symbol, …)
               and their LemLib/Lem_* runtime — trusted because they
               ARE the semantics under judgment.
  SPEC IDIOM — modules rooted at `CerberusHeapLang`: this package's
               statement-level definitions (drive/driveJ, Sat/Coh,
               ChainAt/SeedChain, program terms, value injections) —
               the statement-level trust surface; each is small and
               meant to be read (docs/WALKTHROUGH.md §5).
  IRIS       — modules rooted at `Iris` (iris-lean).
  LEAN CORE  — Init/Lean/Std/Batteries/Qq or module-less builtins.

The invariant this witnesses: exported statements are ENGINE
vocabulary plus the enumerated SPEC IDIOM, nothing else — with the
one honest exception that the Iris-exported theorems carry a
universally quantified ghost-functor binder (`Iris.BundledGFunctors`
+ the package's `SpikeGpreS` hypothesis class), which the census
surfaces in the IRIS bin for exactly those theorems (satisfiability
witness: `SpikeGF`, Adequacy.lean). Any OTHER Iris/machinery
constant surfacing in an exported statement is a finding.

Run (from cerberus-heaplang/; read-only, prints to stdout):
  ../scripts/capped ~/.elan/bin/lake env lean scripts/statement_census.lean

THE CENSUS FREEZE-GATE (acceptance-suite slice, 2026-09-01 — the
formerly registered future gate, implemented): the committed
expected output is docs/STATEMENT_CENSUS.txt and
scripts/test_unit.sh gate 5 re-runs this script and fails on any
drift against it (and fail-closed on a missing/renamed pinned
theorem — the lookup throws). A statement-surface change to a
pinned export therefore requires a deliberate same-commit
re-baseline of the committed census. Plant-tested both directions
(record: docs/2026-09-01_acceptance-suite-record.md).
-/
import CerberusHeapLang

open Lean Meta

/-- The pinned exported theorems: the README verify-me list, plus
(arc-close re-audit fix L2, 2026-09-01) the three Phase-5 production
exports — the arc's headline new statements, now census-FROZEN, not
just axiom-pinned, so gate 5's statement-vocabulary protection
extends to them. -/
def pinned : List Name := [
  `CerberusHeapLang.semantic_triple_sound,
  `CerberusHeapLang.engine_complete,
  `CerberusHeapLang.counter_loop_certified,
  `CerberusHeapLang.fib_certified,
  `CerberusHeapLang.fib_certified_total,
  `CerberusHeapLang.array_sum_certified,
  `CerberusHeapLang.list_reverse_certified,
  `CerberusHeapLang.list_reverse_demo,
  `CerberusHeapLang.tree_rotate_certified,
  `CerberusHeapLang.tree_rotate_certified_total,
  `CerberusHeapLang.exhibitA_prod,
  `CerberusHeapLang.counter_loop_certified_registration,
  -- Phase-5 production exports (appended at the end so the
  -- committed census's existing blocks stay byte-identical):
  `CerberusHeapLang.fib_certified_production,
  `CerberusHeapLang.counter_loop_certified_production,
  `CerberusHeapLang.list_reverse_certified_production]

inductive Bin | engine | idiom | iris | core
deriving BEq

def Bin.label : Bin → String
  | .engine => "ENGINE"
  | .idiom => "SPEC IDIOM (CerberusHeapLang)"
  | .iris => "IRIS"
  | .core => "LEAN CORE/STD"

def coreRoots : List Name := [`Init, `Lean, `Std, `Batteries, `Qq]

#eval show MetaM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let binOf (n : Name) : Bin :=
    match env.getModuleIdxFor? n with
    | none => .core  -- module-less builtins (Quot etc.)
    | some idx =>
      let root := (mods[idx.toNat]!).getRoot
      if root == `CerberusHeapLang then .idiom
      else if root == `Iris then .iris
      else if coreRoots.contains root then .core
      else .engine
  for thm in pinned do
    let some ci := env.find? thm
      | throwError "census: pinned theorem {thm} not found (FAIL)"
    unless ci matches .thmInfo _ do
      throwError "census: {thm} is not a theorem (FAIL)"
    let used := ci.type.getUsedConstants
    let mut bins : Array (Bin × Array Name) :=
      #[(.engine, #[]), (.idiom, #[]), (.iris, #[]), (.core, #[])]
    for c in used do
      let b := binOf c
      bins := bins.map (fun (bb, arr) =>
        if bb == b && !arr.contains c then (bb, arr.push c) else (bb, arr))
    IO.println s!"== {thm} =="
    for (b, arr) in bins do
      let sorted := arr.qsort (fun a b => a.toString < b.toString)
      IO.println s!"  {b.label} ({sorted.size}):"
      for c in sorted do
        IO.println s!"    {c}"
  IO.println "census: done (statement surfaces only; proofs not inspected)"
