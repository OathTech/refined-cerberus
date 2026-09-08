/- Focused executable regressions; no equality theorem is asserted.
   Compile scripts/derive_file_beq.lean into an ignored scripts/ search
   directory, add its parent to LEAN_PATH, then run this file under capped. -/
import scripts.derive_file_beq
import CerberusHeapLang.Examples.EmittedT1Data

namespace EmittedFileStructuralTests

open CerberusHeapLang

private def withValue (v : value) : EmittedFile.Data :=
  { CorpusA7.T1.data with impl := some (.Node .Empty default
      (.Def .BTy_unit (.Pexpr [] () (.PEval v))) .Empty 1) }

-- The type annotation is nested through ctype's mutual family, the
-- memory value, Core object/value, expression and implementation declaration.
private def nested (annots : List annot) : value :=
  .Vobject (.OVunion default default
    (.MVunspecified (.Ctype [] (.Atomic (.Ctype annots .Void0)))))

private def check (label : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"structural comparison failed: {label}")
  IO.println s!"ok: structural comparison — {label}"

#eval do
  let data := CorpusA7.T1.data
  check "t1 reflexivity" (EmittedFileStructural.equal data data)
  check "changed main" (!EmittedFileStructural.equal data { data with main := none })

  let original := nested []
  let annotated := nested [.Aloc (.other "changed annotation")]
  check "existing nested equality ignores annotation"
    (value.beq_derived original annotated)
  check "nested annotation retained through all parents"
    (!EmittedFileStructural.equal (withValue original) (withValue annotated))

  let lowTree : EmittedFile.MapData Nat (List (sym × ctype)) :=
    some (.Node .Empty 0 [] .Empty 1)
  let highTree : EmittedFile.MapData Nat (List (sym × ctype)) :=
    some (.Node .Empty 0 [] .Empty 2)
  check "map height retained" (!EmittedFileStructural.equal
    { data with visibleObjects := lowTree } { data with visibleObjects := highTree })
  check "absent and comparator-bearing empty maps differ"
    (!EmittedFileStructural.equal { data with visibleObjects := none }
      { data with visibleObjects := some .Empty })

  let floatData := fun bits => withValue (.Vobject (.OVfloating (Float.ofBits bits)))
  check "float signed zero retained" (!EmittedFileStructural.equal
    (floatData 0) (floatData 0x8000000000000000))
  check "float NaN reflexivity" (EmittedFileStructural.equal
    (floatData 0x7ff8000000000001) (floatData 0x7ff8000000000001))
  -- This runtime canonicalizes the NaN payloads supplied to ofBits, so
  -- exercise a mantissa-bit difference that survives conversion instead.
  check "float mantissa bit retained" (!EmittedFileStructural.equal
    (floatData 0x3ff0000000000000) (floatData 0x3ff0000000000001))

end EmittedFileStructuralTests
