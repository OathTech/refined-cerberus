/-
CerberusHeapLang.StdCore — THE STANDARD-LIBRARY FRAGMENT THE EMITTED DIALECT
UNFOLDS (dialect arc E3; docs/2026-09-05_e3-notes.md).

The elaborator's Core calls the Core standard library: every C
initialiser, assignment and return of an `int` passes through
`conv_loaded_int('signed int', …)` (docs/corpus-e0/t1.core), whose body
calls `conv_int`, whose body calls `is_representable_integer`
(`.cerberus-ws/runtime/libcore/std.core:5–6`, `:25–55`, `:61–67`). The
engine unfolds those calls through the FILE's `stdlib` map — the parsed
std.core the pipeline loads (`loadCoreStdlib`, Main.lean:44; `call_function`,
core_eval.lem:120–163) — and the mirror evaluator reads the same file
object (`callBody`, Step.lean). A production statement is stated over a
hand-built file (`prodFile`/`prodFileWith`/`prodFileLib`, ProdEntry.lean),
so the std.core bodies a statement's file carries are HAND-TRANSCRIBED
here from the pinned text, [USER 2026-09-04] E0 question 3 ("the pipeline's
Core enters a statement as a HAND-TRANSCRIBED TERM checked by an
EXECUTABLE EQUALITY speedbump"): the skeleton speedbump
(`scripts/corpus_skeleton.lean`, `Examples/CorpusE0.lean` `stdTable`) checks
each body below against the pinned `std.core` text, the way it checks t1's
`main` against the oracle's emitted text (the oracle cannot print std.core
itself: `--pp=core` on std.core as the input file aborts in its parser,
recorded in the E3 notes).

WHAT IS TRANSCRIBED (three `fun`s; the corpus needs no other):

```
fun is_representable_integer (n: integer, ty: ctype): boolean :=
  Ivmin(ty) <= n /\ n <= Ivmax(ty)

fun conv_int (ty: ctype, n: integer): integer :=
  if ty = '_Bool' then
    if n = 0 then 0 else 1
  else
    if is_representable_integer(n, ty) then
      n
    else
      if is_unsigned(ty) then
        wrapI(ty, n)
      else
        <Integer.conv_nonrepresentable_signed_integer>(ty, n)

fun conv_loaded_int (ty: ctype, _n: loaded integer): loaded integer :=
  case _n of
    | Specified(n:integer) =>
        Specified(conv_int(ty, n))
    | Unspecified(_: ctype) =>
        Unspecified(ty)
  end
```

NOT transcribed (pending, docs/2026-09-05_e3-notes.md §7): `wrapI`
(std.core:229–242 — a pure `let`, outside the covered grammar) and the
gcc impl's `<Integer.conv_nonrepresentable_signed_integer>` (`wrapI(ty,
n)`), both reached by `conv_int` only at a NON-representable value — never
in the corpus, whose arithmetic is in range; a run reaching them is the
classifier's `.uncovered` (fail-closed). `params_length`/`params_nth`
(the C-call protocol, E6) are recursive and have no static inlining budget.

THE BUDGETS. `stdBudget` (Step.lean) is keyed by the printed name; the
three equalities `peDepth_isReprBody`/`_convIntBody`/`_convLoadedIntBody`
(kernel-checked by `rfl`) tie each budget to the depth of the transcribed
body it bounds; the budget of a callee exceeds those of the callees its
body names (4 < 17 < 23).

SYMBOLS. Symbol identity for the engine's maps is `(digest, id)`
(`symbol_compare`, Symbol.lean:213 — the description is not compared),
so every symbol here has its own id (9001–9017); the descriptions are the
std.core names, which is what the skeleton compares and what `stdBudget`
keys on. -/
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-! ## The symbols -/

/-- `is_representable_integer` (std.core:5). -/
def isReprSym : sym := Symbol "" 9001 (SD_Id "is_representable_integer")
/-- `conv_int` (std.core:25). -/
def convIntSym : sym := Symbol "" 9002 (SD_Id "conv_int")
/-- `conv_loaded_int` (std.core:61). -/
def convLoadedIntSym : sym := Symbol "" 9003 (SD_Id "conv_loaded_int")
/-- `wrapI` (std.core:229) — named by `conv_int`'s body, NOT transcribed. -/
def wrapISym : sym := Symbol "" 9004 (SD_Id "wrapI")

/-- The parameters, one symbol each (a `Fun`'s parameters are substituted
    by symbol identity, `foldl2 subst_sym_pexpr`, core_eval.lem:156). -/
def irNSym : sym := Symbol "" 9011 (SD_Id "n")
def irTySym : sym := Symbol "" 9012 (SD_Id "ty")
def ciTySym : sym := Symbol "" 9013 (SD_Id "ty")
def ciNSym : sym := Symbol "" 9014 (SD_Id "n")
def cliTySym : sym := Symbol "" 9015 (SD_Id "ty")
def cliArgSym : sym := Symbol "" 9016 (SD_Id "_n")
def cliNSym : sym := Symbol "" 9017 (SD_Id "n")

/-! ## The bodies (std.core's text, constructor for constructor) -/

/-- The pexpr spellings used by the bodies (canonical annotations). -/
def stdSym (x : sym) : generic_pexpr Unit sym := Pexpr [] () (PEsym x)
def stdInt (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEval (Vobject (OVinteger (CerbMem.integerIval n))))
/-- `'_Bool'`. -/
def stdBoolTy : ctype := Ctype [] (.Basic (.Integer .Bool0))
def stdBoolTyPe : generic_pexpr Unit sym := Pexpr [] () (PEval (Vctype stdBoolTy))

/-- `Ivmin(ty) <= n /\ n <= Ivmax(ty)` (std.core:6). -/
def isReprBody : generic_pexpr Unit sym :=
  Pexpr [] () (PEop OpAnd
    (Pexpr [] () (PEop OpLe (Pexpr [] () (PEctor Civmin [stdSym irTySym])) (stdSym irNSym)))
    (Pexpr [] () (PEop OpLe (stdSym irNSym) (Pexpr [] () (PEctor Civmax [stdSym irTySym])))))

/-- `conv_int`'s body (std.core:33–55). -/
def convIntBody : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEop OpEq (stdSym ciTySym) stdBoolTyPe))
    (Pexpr [] () (PEif (Pexpr [] () (PEop OpEq (stdSym ciNSym) (stdInt 0))) (stdInt 0) (stdInt 1)))
    (Pexpr [] () (PEif (Pexpr [] () (PEcall (Sym isReprSym) [stdSym ciNSym, stdSym ciTySym]))
      (stdSym ciNSym)
      (Pexpr [] () (PEif (Pexpr [] () (PEis_unsigned (stdSym ciTySym)))
        (Pexpr [] () (PEcall (Sym wrapISym) [stdSym ciTySym, stdSym ciNSym]))
        (Pexpr [] () (PEcall (Impl Integer__conv_nonrepresentable_signed_integer)
          [stdSym ciTySym, stdSym ciNSym])))))))

/-- `conv_loaded_int`'s body (std.core:62–67). -/
def convLoadedIntBody : generic_pexpr Unit sym :=
  Pexpr [] () (PEcase (stdSym cliArgSym)
    [(Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some cliNSym, BTy_object OTy_integer))]),
      Pexpr [] () (PEctor Cspecified
        [Pexpr [] () (PEcall (Sym convIntSym) [stdSym cliTySym, stdSym cliNSym])])),
     (Pattern [] (CaseCtor Cunspecified [Pattern [] (CaseBase (none, BTy_ctype))]),
      Pexpr [] () (PEctor Cunspecified [stdSym cliTySym]))])

/-- The three declarations (`Fun bty params body`, Core.lean:1481). -/
def isReprParams : List (sym × core_base_type) :=
  [(irNSym, BTy_object OTy_integer), (irTySym, BTy_ctype)]
def convIntParams : List (sym × core_base_type) :=
  [(ciTySym, BTy_ctype), (ciNSym, BTy_object OTy_integer)]
def convLoadedIntParams : List (sym × core_base_type) :=
  [(cliTySym, BTy_ctype), (cliArgSym, BTy_loaded OTy_integer)]

def isReprDecl : generic_fun_map_decl Unit core_run_annotation :=
  Fun BTy_boolean isReprParams isReprBody
def convIntDecl : generic_fun_map_decl Unit core_run_annotation :=
  Fun (BTy_object OTy_integer) convIntParams convIntBody
def convLoadedIntDecl : generic_fun_map_decl Unit core_run_annotation :=
  Fun (BTy_loaded OTy_integer) convLoadedIntParams convLoadedIntBody

/-- THE FRAGMENT AS A `stdlib` MAP (the file field `call_function` reads
    first, core_eval.lem:126). -/
def stdlibE3 : generic_fun_map Unit core_run_annotation :=
  symAdd isReprSym isReprDecl (symAdd convIntSym convIntDecl
    (symAdd convLoadedIntSym convLoadedIntDecl fmapEmpty))

theorem stdlibE3_symMap : SymMap stdlibE3 :=
  ((symMap_empty.add _ _).add _ _).add _ _

/-! ## The budgets tie to the transcription (kernel-checked) -/

theorem peDepth_isReprBody : peDepth isReprBody = 4 := rfl
theorem peDepth_convIntBody : peDepth convIntBody = 17 := rfl
theorem peDepth_convLoadedIntBody : peDepth convLoadedIntBody = 23 := rfl
theorem stdBudget_isRepr : stdBudget (Sym isReprSym) = 4 := rfl
theorem stdBudget_convInt : stdBudget (Sym convIntSym) = 17 := rfl
theorem stdBudget_convLoadedInt : stdBudget (Sym convLoadedIntSym) = 23 := rfl

/-- The bodies are in the covered grammar (their calls are leaves-with-
    arguments; `wrapI` and the impl constant are covered syntactically and
    unfold to nothing). -/
theorem isPePure_isReprBody : isPePure isReprBody = true := by decide
theorem isPePure_convIntBody : isPePure convIntBody = true := by decide
theorem isPePure_convLoadedIntBody : isPePure convLoadedIntBody = true := by decide

/-! ## Files carrying the fragment -/

/-- A file whose `stdlib` IS the transcribed fragment: what the E3
    production statements name (`prodFileLib`, ProdEntry.lean). -/
def StdE3 (file : generic_file Unit core_run_annotation) : Prop := file.stdlib = stdlibE3

/-- The three lookups on the fragment map (the `symAdd` lookup law,
    EnvLaws.lean). -/
theorem stdlibE3_lookup_isRepr :
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      isReprSym stdlibE3 = some isReprDecl := by
  unfold stdlibE3
  rw [symAdd_lookup ((symMap_empty.add _ _).add _ _), if_pos (by decide +kernel)]

theorem stdlibE3_lookup_convInt :
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      convIntSym stdlibE3 = some convIntDecl := by
  unfold stdlibE3
  rw [symAdd_lookup ((symMap_empty.add _ _).add _ _), if_neg (by decide +kernel),
    symAdd_lookup (symMap_empty.add _ _), if_pos (by decide +kernel)]

theorem stdlibE3_lookup_convLoadedInt :
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2)
      convLoadedIntSym stdlibE3 = some convLoadedIntDecl := by
  unfold stdlibE3
  rw [symAdd_lookup ((symMap_empty.add _ _).add _ _), if_neg (by decide +kernel),
    symAdd_lookup (symMap_empty.add _ _), if_neg (by decide +kernel),
    symAdd_lookup symMap_empty, if_pos (by decide +kernel)]

/-- The mirror's callee lookups on such a file (`lookupFun`, Step.lean:
    `file.stdlib` first). -/
theorem lookupFun_isRepr {file : generic_file Unit core_run_annotation} (h : StdE3 file) :
    lookupFun file (Sym isReprSym) = some (isReprParams, isReprBody) := by
  unfold lookupFun; dsimp only; rw [h, stdlibE3_lookup_isRepr]; rfl

theorem lookupFun_convInt {file : generic_file Unit core_run_annotation} (h : StdE3 file) :
    lookupFun file (Sym convIntSym) = some (convIntParams, convIntBody) := by
  unfold lookupFun; dsimp only; rw [h, stdlibE3_lookup_convInt]; rfl

theorem lookupFun_convLoadedInt {file : generic_file Unit core_run_annotation} (h : StdE3 file) :
    lookupFun file (Sym convLoadedIntSym) = some (convLoadedIntParams, convLoadedIntBody) := by
  unfold lookupFun; dsimp only; rw [h, stdlibE3_lookup_convLoadedInt]; rfl

end CerberusHeapLang
