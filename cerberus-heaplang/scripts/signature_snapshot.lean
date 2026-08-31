/-
signature_snapshot.lean — the frozen-corpus regression instrument
(phase 1, two-phase arc plan: the acceptance gate is that every
exported statement re-proves UNCHANGED or STRENGTHENED across the
S1/S2 restratification; this script extracts every CerberusHeapLang
constant's kind and pretty-printed type to stdout, deterministically
sorted, for pre/post diffing).

Run (from cerberus-heaplang/):
  lake env lean scripts/signature_snapshot.lean > docs/<snapshot>.txt

The snapshot covers ALL constant kinds (theorems, defs, instances,
inductives — statement surface is not only theorems: the triple
DEFINITIONS are part of the frozen corpus), excluding internal
details (match auxiliaries, proof terms, etc.).
-/
import CerberusHeapLang

open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isOurs : Array Bool := mods.map (fun m => m.getRoot == `CerberusHeapLang)
  let mut entries : Array (String × String) := #[]
  for (n, ci) in env.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some idx => isOurs[idx.toNat]!
      | none => false
    unless ours do continue
    if n.isInternalDetail then continue
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "def"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec"
      | .quotInfo _ => "quot"
    let ty ← ppExpr ci.type
    entries := entries.push (n.toString, s!"{kind} {n} :\n{ty.pretty 100}")
  let sorted := entries.qsort (fun a b => a.1 < b.1)
  for (_, s) in sorted do
    IO.println s
    IO.println "----"
