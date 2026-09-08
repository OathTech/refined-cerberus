/- The actual main body projected from the complete emitted t1 fixture.
   Shape equalities below support public proofs without changing the referent. -/
import CerberusHeapLang.EmittedStdCore
import CerberusHeapLang.EmittedMapChecks
import Core_linking
import CerberusHeapLang.Examples.CorpusE0
import Lean

set_option autoImplicit false

namespace CerberusHeapLang.CorpusA7.T1

def mainSym : sym := data.main.get (by decide)

def findMainBody : Option CoreExpr := do
  let tree ← data.funs
  let (_, decl) ← (Pmap.bindings tree).find? fun (key, _) => key == mainSym
  match decl with
  | .Proc _ _ _ _ body => some body
  | _ => none

def mainBody : CoreExpr := findMainBody.get (by decide)

/-- The complete retained file, with its original comparator parameters. -/
def restoredFile (cmp : EmittedFile.Comparators) : file core_run_annotation :=
  EmittedFile.restore cmp data

theorem restoredFile_main (cmp : EmittedFile.Comparators) :
    (restoredFile cmp).main = some mainSym := rfl

theorem restoredFile_tagDefs (cmp : EmittedFile.Comparators) :
    (restoredFile cmp).tagDefs = fmapEmpty := rfl

theorem restoredFile_globs (cmp : EmittedFile.Comparators) :
    (restoredFile cmp).globs = [] := rfl

/-- The collector unions stdlib and funs using their original stored
comparators. This check covers the actual union's comparison decisions. -/
def labelUnionCheck (cmp : EmittedFile.Comparators) : Bool :=
  EmittedMapChecks.mapUnionCheck cmp.stdlib cmp.funs EmittedStdCore.referenceCmp
    data.stdlib data.funs

/-- Transfer label collection to reference comparisons only after proving
the union data agrees. The fold and its binding-to-set conversion stay intact. -/
theorem collect_labels_eq_of_check (cmp : EmittedFile.Comparators)
    (h : labelUnionCheck cmp = true) :
    collect_labeled_continuations_NEW (restoredFile cmp) =
      collect_labeled_continuations_NEW
        (restoredFile { cmp with stdlib := EmittedStdCore.referenceCmp, funs := EmittedStdCore.referenceCmp }) := by
  unfold collect_labeled_continuations_NEW
  apply EmittedMapChecks.fold_eq_of_mapData_eq
  exact EmittedMapChecks.mapData_union_of_check cmp.stdlib cmp.funs
    EmittedStdCore.referenceCmp EmittedStdCore.referenceCmp data.stdlib data.funs h

/-- The concrete reference collector registers the actual main body's
saves. Submit a small reflexivity certificate directly to the kernel, as
`decide +kernel` does with its decision certificate: elaborator reduction
repeatedly expands the intermediate map trees. The auxiliary theorem is
checked synchronously with the ordinary limits and included in the audit.
This uses neither native evaluation nor an equation for an opaque value. -/
theorem reference_main_labels : ∀ (cmp : EmittedFile.Comparators),
    fmapLookupBy symCmpL mainSym
      (collect_labeled_continuations_NEW
        (restoredFile { cmp with stdlib := EmittedStdCore.referenceCmp, funs := EmittedStdCore.referenceCmp })) =
      some (collect_saves mainBody) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← goal.getType
    let proof ← Lean.Meta.forallTelescope target fun xs body => do
      let some (_, _, rhs) := body.eq? | throwError "expected an equality"
      Lean.Meta.mkLambdaFVars xs (← Lean.Meta.mkEqRefl rhs)
    let lemmaName ← Lean.withOptions (Lean.Elab.async.set · false) do
      Lean.Meta.mkAuxLemma [] target proof
    goal.assign (Lean.mkConst lemmaName)
    Lean.Elab.Tactic.replaceMainGoal []

/-- Main registration in the complete original file, using its checked
stored comparator and the shipped union, fold and save collection. -/
theorem main_labels_of_check (cmp : EmittedFile.Comparators)
    (h : labelUnionCheck cmp = true) :
    fmapLookupBy symCmpL mainSym (collect_labeled_continuations_NEW (restoredFile cmp)) =
      some (collect_saves mainBody) := by
  rw [collect_labels_eq_of_check cmp h, reference_main_labels]

/-- The real startup map is a singleton self-binding, not an empty map. -/
def runtimeExtern : Fmap sym sym := symAdd mainSym mainSym fmapEmpty

theorem restoredFile_extern (cmp : EmittedFile.Comparators) :
    create_extern_symmap (restoredFile cmp) = runtimeExtern := rfl

theorem runtimeExtern_compare (x : sym) :
    symCmpK (resolveExtern runtimeExtern x) x = .EQ :=
  resolveExtern_self_compare mainSym x

theorem runtimeExtern_main : resolveExtern runtimeExtern mainSym = mainSym := rfl

open CorpusE0 (psym seqE letS letW bnd act specInt)

def sourceDigest : String := match mainSym with | .Symbol digest _ _ => digest
def sourcePos (col : Nat) : CerbLocation.Pos := ⟨"docs/corpus-e0/t1.c", 1, col⟩
def loc (lo hi : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) .noCursor
def locP (lo hi cursor : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) (.pointCursor (sourcePos cursor))
def locR (lo hi clo chi : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) (.regionCursor (sourcePos clo) (sourcePos chi))

def tmp (n : Nat) : sym := .Symbol sourceDigest n .SD_None
def xSym : sym := .Symbol sourceDigest 21 (.SD_ObjectAddress "x")
def ySym : sym := .Symbol sourceDigest 22 (.SD_ObjectAddress "y")
def retSym : sym := .Symbol sourceDigest 24 (.SD_Id "ret_24")
abbrev intBty : core_base_type := BTy_loaded OTy_integer
abbrev ptrBty : core_base_type := BTy_object OTy_pointer

/-- The startup lookup checks only the path to main in the original
function tree. It does not assert whole-comparator equality. -/
def mainLookupCheck (cmp : sym → sym → LemOrdering) : Bool :=
  EmittedFile.mapLookupCheck cmp EmittedStdCore.referenceCmp mainSym data.funs

theorem referenceLookup_main :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym
      (EmittedFile.restoreMap EmittedStdCore.referenceCmp data.funs) =
      some (.Proc (locR 1 55 5 9) (some 20) intBty [] mainBody) := rfl

/-- The genuine startup lookup finds the exact parameterless main
procedure, retaining its location, identifier, result type and body. -/
theorem restoredFile_mainLookup (cmp : EmittedFile.Comparators)
    (h : mainLookupCheck cmp.funs = true) :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym (restoredFile cmp).funs =
      some (.Proc (locR 1 55 5 9) (some 20) intBty [] mainBody) :=
  (EmittedFile.restoreMap_lookup_of_check cmp.funs EmittedStdCore.referenceCmp
    EmittedStdCore.referenceCmp mainSym data.funs h).trans referenceLookup_main

/-- Transfer the lookup to an actual file when its complete data agrees
and the original function comparator passes the finite check. -/
theorem mainLookup_of_capture_eq (fallback : EmittedFile.Comparators)
    (f : file core_run_annotation) (hd : EmittedFile.captureData f = data)
    (hc : mainLookupCheck (EmittedFile.captureComparators fallback f).funs = true) :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym f.funs =
      some (.Proc (locR 1 55 5 9) (some 20) intBty [] mainBody) := by
  rw [← EmittedFile.restore_eq_of_data_eq fallback f data hd]
  exact restoredFile_mainLookup _ hc

def xTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 18 21)]
def yTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 29 32)]
def retTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 1 4)]
def tyPe (ty : ctype) : generic_pexpr Unit sym := Pexpr [] () (PEval (Vctype ty))
def convLoaded (ty : ctype) (s : sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEcall (Sym EmittedStdCore.convLoadedInt.1) [tyPe ty, psym s])
def intValueAnnot : annot := Avalue (Ainteger (.Signed .Int_))
def intLiteral (a : List annot) (n : Int) : CoreExpr :=
  Expr a (Epure (Pexpr [] () (PEval (lint n))))

def createX : CoreExpr :=
  act (locR 16 55 22 23)
    (Create (Pexpr [] () (PEctor Civalignof [tyPe xTy])) (tyPe xTy)
      (PrefSource (loc 22 23) [mainSym, xSym]))
def createY : CoreExpr :=
  act (locR 16 55 33 34)
    (Create (Pexpr [] () (PEctor Civalignof [tyPe yTy])) (tyPe yTy)
      (PrefSource (loc 33 34) [mainSym, ySym]))
def initializeX : CoreExpr :=
  letS [Aloc (loc 18 28), Astmt] (tmp 25) intBty
    (bnd (intLiteral [Aloc (loc 26 27), Aexpr, intValueAnnot] 3))
    (act (loc 18 28) (Store0 false (tyPe xTy) (psym xSym) (convLoaded xTy (tmp 25)) NA))

def loadX : CoreExpr :=
  letW [Aloc (loc 37 38), Aexpr, intValueAnnot] (tmp 32) ptrBty
    (Expr [Aloc (loc 37 38), Aexpr] (Epure (psym xSym)))
    (act (loc 37 38) (Load0 (tyPe xTy) (psym (tmp 32)) NA))
def loadY : CoreExpr :=
  letW [Aloc (loc 51 52), Aexpr, intValueAnnot] (tmp 33) ptrBty
    (Expr [Aloc (loc 51 52), Aexpr] (Epure (psym ySym)))
    (act (loc 51 52) (Load0 (tyPe yTy) (psym (tmp 33)) NA))
def one : CoreExpr := intLiteral [Aloc (loc 41 42), Aexpr, intValueAnnot] 1

def addBranch (p q : generic_pexpr Unit sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Cspecified
    [Pexpr [Astd "§6.5.6#5"] () (PEcatch_exceptional_condition (.Signed .Int_) IOpAdd
      (Pexpr [Astd "§6.5.6#4"] () (PEconv_int (.Signed .Int_) p))
      (Pexpr [Astd "§6.5.6#4"] () (PEconv_int (.Signed .Int_) q)))])
def addAlts : List (pattern × generic_pexpr Unit sym) :=
  [(Pattern [] (CaseCtor Ctuple
      [Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some (tmp 29), BTy_object OTy_integer))]),
       Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some (tmp 30), BTy_object OTy_integer))])]),
    addBranch (psym (tmp 29)) (psym (tmp 30))),
   (Pattern [] (CaseBase (none, BTy_tuple [intBty, intBty])),
    Pexpr [Astd "§6.5#5"] () (PEundef (locP 37 42 39) UB036_exceptional_condition))]
def addPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEcase (Pexpr [] () (PEctor Ctuple [psym (tmp 27), psym (tmp 28)])) addAlts)
def sum : CoreExpr :=
  bnd (Expr [Aloc (locP 37 42 39), Aexpr, intValueAnnot, Astd "§6.5.6"]
    (Ewseq (Pattern [] (CaseCtor Ctuple
      [Pattern [] (CaseBase (some (tmp 27), intBty)), Pattern [] (CaseBase (some (tmp 28), intBty))]))
      (Expr [] (Eunseq [loadX, one])) (Expr [] (Epure addPe))))
def initializeY : CoreExpr :=
  letS [Aloc (loc 29 43), Astmt] (tmp 26) intBty sum
    (act (loc 29 43) (Store0 false (tyPe yTy) (psym ySym) (convLoaded yTy (tmp 26)) NA))

def kill (atLoc : CerbLocation.Loc) (ty : ctype) (s : sym) : CoreExpr :=
  act atLoc (Kill (Static0 ty) (psym s))
def returnStmt : CoreExpr :=
  letS [Aloc (loc 44 53), Astmt] (tmp 34) intBty (bnd loadY)
    (seqE (kill (loc 44 53) xTy xSym)
      (seqE (kill (loc 44 53) yTy ySym)
        (Expr [] (Erun empty_annotation retSym [convLoaded retTy (tmp 34)]))))
def cleanup : CoreExpr :=
  seqE (kill (locR 16 55 22 23) xTy xSym)
    (seqE (kill (locR 16 55 33 34) yTy ySym) (Expr [] (Epure (Pexpr [] () (PEval Vunit)))))
def block : CoreExpr :=
  letS [Aloc (loc 16 55), Astmt] xSym ptrBty createX
    (letS [] ySym ptrBty createY
      (seqE initializeX (seqE initializeY (seqE returnStmt cleanup))))
def returnSave : CoreExpr :=
  Expr [Alabel LAreturn, Aloc (locR 1 55 5 9)]
    (Esave (retSym, intBty) [(tmp 35, ((intBty, some (retTy, By_value)), specInt 0))]
      (Expr [] (Epure (psym (tmp 35)))))

/-- This is equality to the actual retained file's body, including every
annotation, type, prefix, initializer and sequence grouping. -/
theorem mainBody_shape : mainBody = seqE block returnSave := rfl

theorem convLoaded_pePure (ty : ctype) (s : sym) : PePure (convLoaded ty s) :=
  PePure.of_isPePure rfl

theorem convLoaded_depth (ty : ctype) (s : sym) : peDepth (convLoaded ty s) = 26 := rfl

section Membership

theorem createX_frag : Frag createX :=
  .create_op rfl (.ctorTy [] Civalignof rfl [] xTy) (.val [] (Vctype xTy))

theorem createY_frag : Frag createY :=
  .create_op rfl (.ctorTy [] Civalignof rfl [] yTy) (.val [] (Vctype yTy))


theorem initializeX_frag : Frag initializeX :=
  .sseq_sym (.bound (.val_pure (lint 3)))
    (.store_op rfl (.sym [] xSym) (convLoaded_pePure _ _))

theorem loadX_frag : Frag loadX :=
  .wseq_sym (.pure_op rfl (.sym [] xSym))
    (.load_op rfl (.sym [] (tmp 32)))
theorem loadY_frag : Frag loadY :=
  .wseq_sym (.pure_op rfl (.sym [] ySym))
    (.load_op rfl (.sym [] (tmp 33)))

theorem sum_frag : Frag sum :=
  .bound (.wseq_tuple (pa := []) (ls := [([], some (tmp 27), intBty), ([], some (tmp 28), intBty)])
    (.unseq (by simp) rfl (fun e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact loadX_frag
      · rcases List.mem_singleton.mp he with rfl
        exact .val_pure (lint 1)))
    (.pure_op rfl (PePure.of_isPePure rfl)))

theorem initializeY_frag : Frag initializeY :=
  .sseq_sym sum_frag
    (.store_op rfl (.sym [] ySym) (convLoaded_pePure _ _))

theorem kill_frag (atLoc : CerbLocation.Loc) (ty : ctype) (s : sym) :
    Frag (kill atLoc ty s) :=
  .kill_op rfl (.sym [] s)

theorem returnStmt_frag : Frag returnStmt :=
  .sseq_sym (.bound loadY_frag)
    (.sseq (kill_frag _ _ _)
      (.sseq (kill_frag _ _ _)
        (.run (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact convLoaded_pePure _ _))))

theorem cleanup_frag : Frag cleanup :=
  .sseq (kill_frag _ _ _) (.sseq (kill_frag _ _ _) (.val_pure Vunit))

theorem returnSave_frag : Frag returnSave :=
  .save
    (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact CorpusE0.specInt_pePure 0)
    (.pure_op rfl (.sym [] (tmp 35)))

/-- Every node of the actual body is admitted, including the cleanup after
the return and the complete return-save metadata. -/
theorem mainBody_frag : Frag mainBody := by
  rw [mainBody_shape]
  exact .sseq
    (.sseq_sym createX_frag (.sseq_sym createY_frag
      (.sseq initializeX_frag (.sseq initializeY_frag
        (.sseq returnStmt_frag cleanup_frag)))))
    returnSave_frag

/-- The operand evaluator bound is separate from syntactic membership. -/
theorem mainBody_evalDepth : evalDepth mainBody ≤ 40 := Nat.le_of_ble_eq_true rfl

end Membership

end CerberusHeapLang.CorpusA7.T1
