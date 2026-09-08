/- Tool-local structural comparison for the complete emitted-file data.
   These instances are deliberately absent from the logic library. -/
import CerberusHeapLang.EmittedFile
import Lean

open Lean Elab Command Meta

namespace EmittedFileStructural

-- IEEE equality loses signed zero and is not reflexive on NaNs. Compare
-- every bit exposed by toBits, the same representation retained by capture.
instance : BEq Float where
  beq a b := a.toBits == b.toBits

private def resultIsSort : Expr → Bool
  | .forallE _ _ body _ => resultIsSort body
  | .sort _ => true
  | _ => false

-- Primitive equality and the polymorphic standard-container instances are
-- structural. Their element dictionaries are synthesized anew in each parent.
private def builtin (n : Name) : Bool :=
  [``Nat, ``Int, ``Bool, ``Unit, ``PUnit, ``String, ``Char, ``List,
   ``Option, ``Prod, ``Sum, ``Array, ``Except, ``Fin, ``UInt8, ``UInt16,
   ``UInt32, ``UInt64, ``USize, ``Float].contains n

/-- Re-derive every reachable constructor family in dependency order, even
when a BEq already exists. In particular, re-deriving only ctype would leave
old annotation-insensitive dictionaries embedded in enclosing Core types.
Pmap is not a builtin: all its constructor fields, including height, count.
Type abbreviations are followed, and mutual families are visited together. -/
private partial def deriveName (name : Name) : StateRefT NameSet CommandElabM Unit := do
  if (← get).contains name || builtin name then return
  modify (·.insert name)
  match (← getEnv).find? name with
  | some (.inductInfo info) =>
    for n in info.all do modify (·.insert n)
    for n in info.all do
      let ind ← getConstInfoInduct n
      for ctor in ind.ctors do
        let ci ← getConstInfoCtor ctor
        for dep in ci.type.getUsedConstants do deriveName dep
    let ids := info.all.toArray.map mkIdent
    elabCommand (← `(deriving instance BEq for $[$ids],*))
  | some (.defnInfo info) =>
    if resultIsSort info.type then
      for dep in info.value.getUsedConstants do deriveName dep
  | _ => pure ()

elab "derive_emitted_file_beq" : command => do
  let _ ← (deriveName ``CerberusHeapLang.EmittedFile.Data).run {}

derive_emitted_file_beq

/-- Executable structural comparison, independent of quotation and of the
semantics' intentional annotation-insensitive ctype equality. This is a
speedbump check, not a theorem establishing equality of arbitrary files. -/
def equal (a b : CerberusHeapLang.EmittedFile.Data) : Bool := a == b

end EmittedFileStructural
