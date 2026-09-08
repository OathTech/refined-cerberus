/- Tool-local quotation instances for the emitted-file data projection.
   None of these instances is imported by the logic library. -/
import CerberusHeapLang.EmittedFile
import Lean

open Lean Elab Command Meta

namespace EmittedFileQuotation

-- Float is primitive; its specification record contains functions and
-- proofs, not the data representation to quote. Preserve the exact bits.
instance : ToExpr Float where
  toExpr f := mkApp (mkConst ``Float.ofBits) (toExpr f.toBits)
  toTypeExpr := mkConst ``Float

private def resultIsSort : Expr → Bool
  | .forallE _ _ body _ => resultIsSort body
  | .sort _ => true
  | _ => false

private def builtin (n : Name) : Bool :=
  [``Nat, ``Int, ``Bool, ``Unit, ``PUnit, ``String, ``Char, ``List,
   ``Option, ``Prod, ``Sum, ``Array, ``Except, ``Fin, ``UInt8, ``UInt16,
   ``UInt32, ``UInt64, ``USize, ``Float].contains n

/-- Follow constructor-field types and type abbreviations, then ask
Lean's deriving handler for each mutual family. Function fields are not
given a quotation instance: an unsupported dependency is an error. -/
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
    elabCommand (← `(deriving instance Lean.ToExpr for $[$ids],*))
  | some (.defnInfo info) =>
    if resultIsSort info.type then
      for dep in info.value.getUsedConstants do deriveName dep
  | _ => pure ()

elab "derive_emitted_file_to_expr" : command => do
  let _ ← (deriveName ``CerberusHeapLang.EmittedFile.Data).run {}

end EmittedFileQuotation

derive_emitted_file_to_expr

namespace EmittedFileQuotation

private def implicitParameters : Expr → Nat → Bool
  | _, 0 => true
  | .forallE _ _ body info, n + 1 => info.isImplicit && implicitParameters body n
  | _, _ + 1 => false

/-- Constructor rendering, without diagnostic pretty-printer elision.
Only implicit constructor parameters are omitted; the generated declaration
is subsequently elaborated and compared with a fresh frontend result. -/
partial def render (e : Expr) : CoreM Format := do
  -- The standard Nat quotation uses OfNat and its canonical instance.
  -- Render that exact spelling as a numeral, keeping other instances explicit.
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    if args[0]!.isConstOf ``Nat && args[2]!.isAppOfArity ``instOfNatNat 1 &&
        args[2]!.getAppArgs[0]! == args[1]! then
      if let .lit (.natVal n) := args[1]! then return format (toString n)
  match e with
  | .const n _ => return format ("@_root_." ++ n.toString)
  | .lit (.natVal n) => return format (toString n)
  | .lit (.strVal s) => return format (reprStr s)
  | .app _ _ =>
    let mut args := e.getAppArgs
    let head ← match e.getAppFn with
      | .const n _ =>
        match ← getConstInfo n with
        | .ctorInfo ci =>
          if implicitParameters ci.type ci.numParams then
            args := args.extract ci.numParams args.size
            pure (format ("_root_." ++ n.toString))
          else pure (format ("@_root_." ++ n.toString))
        | _ => pure (format ("@_root_." ++ n.toString))
      | _ => throwError "file quotation has a non-constant application head"
    if args.isEmpty then return head
    let formatted ← args.toList.mapM render
    return Format.paren (Format.group
      (head ++ Format.nest 2 (Format.line ++ Format.joinSep formatted Format.line)))
  | _ => throwError "file quotation contains an open term or unsupported expression form"

def renderData (d : CerberusHeapLang.EmittedFile.Data) : CoreM String := do
  let quoted := toExpr d
  let args := quoted.getAppArgs
  let names := #["main", "callingConvention", "tagDefs", "stdlib", "impl", "globs",
    "funs", "extern", "funinfo", "loopAttributes", "visibleObjects"]
  unless quoted.isAppOf ``CerberusHeapLang.EmittedFile.Data.mk && args.size == names.size do
    throwError "unexpected emitted-file data constructor"
  let mut fields := []
  for name in names, arg in args do
    let value ← render arg
    fields := fields ++ [name ++ " := " ++ (value.pretty 100).replace "\n" "\n    "]
  return "{ " ++ String.intercalate ",\n  " fields ++ " }"

end EmittedFileQuotation
