/- The actual main body projected from the complete emitted t6 fixture.
   Shape equalities below support public proofs without changing the referent. -/
import CerberusHeapLang.Examples.EmittedT6Data
import CerberusHeapLang.EmittedStdCore
import CerberusHeapLang.EmittedMapChecks
import Core_linking
import CerberusHeapLang.Examples.CorpusE0
import Lean

set_option autoImplicit false

namespace CerberusHeapLang.CorpusA7.T6

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
def sourcePos (col : Nat) : CerbLocation.Pos := ⟨"docs/corpus-e0/t6_switch.c", 1, col⟩
def loc (lo hi : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) .noCursor
def locP (lo hi cursor : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) (.pointCursor (sourcePos cursor))
def locR (lo hi clo chi : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) (.regionCursor (sourcePos clo) (sourcePos chi))

def tmp (n : Nat) : sym := .Symbol sourceDigest n .SD_None
def xSym : sym := .Symbol sourceDigest 21 (.SD_ObjectAddress "x")
def rSym : sym := .Symbol sourceDigest 22 (.SD_ObjectAddress "r")
def retSym : sym := .Symbol sourceDigest 30 (.SD_Id "ret_30")
abbrev intBty : core_base_type := BTy_loaded OTy_integer
abbrev ptrBty : core_base_type := BTy_object OTy_pointer

/-- The startup lookup checks only the path to main in the original
function tree. It does not assert whole-comparator equality. -/
def mainLookupCheck (cmp : sym → sym → LemOrdering) : Bool :=
  EmittedFile.mapLookupCheck cmp EmittedStdCore.referenceCmp mainSym data.funs

theorem referenceLookup_main :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym
      (EmittedFile.restoreMap EmittedStdCore.referenceCmp data.funs) =
      some (.Proc (locR 1 136 5 9) (some 20) intBty [] mainBody) := rfl

/-- The genuine startup lookup finds the exact parameterless main
procedure, retaining its location, identifier, result type and body. -/
theorem restoredFile_mainLookup (cmp : EmittedFile.Comparators)
    (h : mainLookupCheck cmp.funs = true) :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym (restoredFile cmp).funs =
      some (.Proc (locR 1 136 5 9) (some 20) intBty [] mainBody) :=
  (EmittedFile.restoreMap_lookup_of_check cmp.funs EmittedStdCore.referenceCmp
    EmittedStdCore.referenceCmp mainSym data.funs h).trans referenceLookup_main

/-- Transfer the lookup to an actual file when its complete data agrees
and the original function comparator passes the finite check. -/
theorem mainLookup_of_capture_eq (fallback : EmittedFile.Comparators)
    (f : file core_run_annotation) (hd : EmittedFile.captureData f = data)
    (hc : mainLookupCheck (EmittedFile.captureComparators fallback f).funs = true) :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym f.funs =
      some (.Proc (locR 1 136 5 9) (some 20) intBty [] mainBody) := by
  rw [← EmittedFile.restore_eq_of_data_eq fallback f data hd]
  exact restoredFile_mainLookup _ hc

def breakSym : sym := .Symbol sourceDigest 32 (.SD_Id "break_32")
def case1Sym : sym := .Symbol sourceDigest 40 (.SD_Id "case_40")
def case2Sym : sym := .Symbol sourceDigest 39 (.SD_Id "case_39")
def defaultSym : sym := .Symbol sourceDigest 41 (.SD_Id "default_41")
def xTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 18 21)]
def rTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 29 32)]
def retTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 1 4)]
def switchTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 48 49)]
def tyPe (ty : ctype) : generic_pexpr Unit sym := Pexpr [] () (PEval (Vctype ty))
def convLoaded (ty : ctype) (s : sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEcall (Sym EmittedStdCore.convLoadedInt.1) [tyPe ty, psym s])
def convAssign (s : sym) : generic_pexpr Unit sym :=
  Pexpr [Astd "§6.5.16.1#2, conversion"] ()
    (PEcall (Sym EmittedStdCore.convLoadedInt.1) [tyPe rTy, psym s])
def ptrAssign (s : sym) : generic_pexpr Unit sym :=
  Pexpr [Astd "§6.5.16#3, sentence 1"] () (PEsym s)
def intValueAnnot : annot := Avalue (Ainteger (.Signed .Int_))
def intLiteral (a : List annot) (n : Int) : CoreExpr :=
  Expr a (Epure (Pexpr [] () (PEval (lint n))))
def pureE (pe : generic_pexpr Unit sym) : CoreExpr := Expr [] (Epure pe)
def unitE : CoreExpr := pureE (Pexpr [] () (PEval Vunit))
open CorpusE0 (wc)

def createX : CoreExpr :=
  act (locR 16 136 22 23)
    (Create (Pexpr [] () (PEctor Civalignof [tyPe xTy])) (tyPe xTy)
      (PrefSource (loc 22 23) [mainSym, xSym]))
def createR : CoreExpr :=
  act (locR 16 136 33 34)
    (Create (Pexpr [] () (PEctor Civalignof [tyPe rTy])) (tyPe rTy)
      (PrefSource (loc 33 34) [mainSym, rSym]))
def initializeX : CoreExpr :=
  letS [Aloc (loc 18 28), Astmt] (tmp 33) intBty
    (bnd (intLiteral [Aloc (loc 26 27), Aexpr, intValueAnnot] 2))
    (act (loc 18 28) (Store0 false (tyPe xTy) (psym xSym) (convLoaded xTy (tmp 33)) NA))
def initializeR : CoreExpr :=
  letS [Aloc (loc 29 39), Astmt] (tmp 34) intBty
    (bnd (intLiteral [Aloc (loc 37 38), Aexpr, intValueAnnot] 0))
    (act (loc 29 39) (Store0 false (tyPe rTy) (psym rSym) (convLoaded rTy (tmp 34)) NA))
def load (x : sym) (ty : ctype) (n lo hi : Nat) : CoreExpr :=
  letW [Aloc (loc lo hi), Aexpr, intValueAnnot] (tmp n) ptrBty
    (Expr [Aloc (loc lo hi), Aexpr] (Epure (psym x)))
    (act (loc lo hi) (Load0 (tyPe ty) (psym (tmp n)) NA))

def assignStmt (start n m : Nat) (v : Int) : CoreExpr :=
  Expr [Aloc (loc start (start + 7)), Astmt]
    (Esseq (Pattern [] (CaseBase (none, intBty)))
      (bnd (Expr [Aloc (locP start (start + 6) (start + 2)), Aexpr, intValueAnnot,
          Astd "§6.5.16#3, sentence 4"]
        (Ewseq (Pattern [] (CaseCtor Ctuple
            [Pattern [] (CaseBase (some (tmp n), ptrBty)), Pattern [] (CaseBase (some (tmp m), intBty))]))
          (Expr [Astd "§6.5.16#3, sentence 5"]
            (Eunseq [Expr [Aloc (loc start (start + 1)), Aexpr] (Epure (psym rSym)),
              intLiteral [Aloc (loc (start + 4) (start + 6)), Aexpr, intValueAnnot] v]))
          (Expr [] (Ewseq wc
            (Expr [Astd "§6.5.16.1#2, store"]
              (Eaction (Paction polarity.Neg0 (Action (locP start (start + 6) (start + 2))
                empty_annotation (Store0 false (tyPe rTy) (ptrAssign (tmp n)) (convAssign (tmp m)) NA)))))
            (pureE (convAssign (tmp m)))))))) unitE)

def ptrInits : List (sym × ((core_base_type × Option (ctype × pass_by_value_or_pointer)) ×
    generic_pexpr Unit sym)) :=
  [(xSym, ((ptrBty, some (xTy, By_pointer)), psym xSym)),
   (rSym, ((ptrBty, some (rTy, By_pointer)), psym rSym))]
def run (an : List annot) (l : sym) : CoreExpr :=
  Expr an (Erun empty_annotation l [psym xSym, psym rSym])
def save (an : List annot) (l : sym) (body : CoreExpr) : CoreExpr :=
  Expr an (Esave (l, BTy_unit) ptrInits body)
def defaultTail : CoreExpr :=
  seqE (save [Aloc (loc 99 115), Astmt, Alabel LAdefault] defaultSym (assignStmt 108 46 47 30))
    (seqE (run [Aloc (loc 116 122), Astmt] breakSym) unitE)
def case2Tail : CoreExpr :=
  seqE (save [Aloc (loc 76 91), Astmt, Alabel LAcase] case2Sym (assignStmt 84 44 45 20))
    (seqE (run [Aloc (loc 92 98), Astmt] breakSym) defaultTail)
def casesBody : CoreExpr :=
  seqE (Expr [Aloc (loc 51 124), Astmt] (Esseq wc
    (save [Aloc (loc 53 68), Astmt, Alabel LAcase] case1Sym (assignStmt 61 42 43 10))
    (seqE (run [Aloc (loc 69 75), Astmt] breakSym) case2Tail))) unitE

def dispatch : CoreExpr :=
  seqE (Expr [] (Eif (Pexpr [] () (PEop OpEq (psym (tmp 38)) (Pexpr [] () (PEval (oint 1)))))
    (run [] case1Sym) unitE))
  (seqE (Expr [] (Eif (Pexpr [] () (PEop OpEq (psym (tmp 38)) (Pexpr [] () (PEval (oint 2)))))
    (run [] case2Sym) unitE))
  (seqE (run [] defaultSym)
    (Expr [Aloc (loc 40 124), Astmt] (Esseq wc
      (run [Aloc (loc 40 124), Astmt] breakSym) casesBody))))
def specifiedBranch (pe : generic_pexpr Unit sym) : CoreExpr :=
  letS [] (tmp 38) (BTy_object OTy_integer)
    (pureE (Pexpr [Astd "§6.8.4.2#5, sentence 1"] ()
      (PEcall (Sym EmittedStdCore.convInt.1) [tyPe switchTy, pe]))) dispatch

def switchPats : List (pattern × CoreExpr) :=
  [(Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some (tmp 37), BTy_object OTy_integer))]),
    specifiedBranch (psym (tmp 37))),
   (Pattern [] (CaseCtor Cunspecified [Pattern [] (CaseBase (none, BTy_ctype))]),
    pureE (Pexpr [Astd "§6.5#5"] () (PEundef (loc 40 124) UB036_exceptional_condition)))]
def switch : CoreExpr :=
  letS [Aloc (loc 40 124), Astmt] (tmp 36) intBty (bnd (load xSym xTy 35 48 49))
    (Expr [] (Ecase (psym (tmp 36)) switchPats))
def afterSwitch : CoreExpr :=
  seqE (save [Aloc (loc 40 124), Astmt, Alabel LAswitch] breakSym
    (Expr [Aloc (loc 40 124), Astmt] (Epure (Pexpr [] () (PEval Vunit))))) unitE
def switchBlock : CoreExpr :=
  Expr [Aloc (loc 40 124), Astmt] (Esseq wc switch afterSwitch)

def kill (atLoc : CerbLocation.Loc) (ty : ctype) (s : sym) : CoreExpr :=
  act atLoc (Kill (Static0 ty) (psym s))
def returnStmt : CoreExpr :=
  letS [Aloc (loc 125 134), Astmt] (tmp 49) intBty (bnd (load rSym rTy 48 132 133))
    (seqE (kill (loc 125 134) xTy xSym)
      (seqE (kill (loc 125 134) rTy rSym)
        (Expr [] (Erun empty_annotation retSym [convLoaded retTy (tmp 49)]))))
def cleanup : CoreExpr :=
  seqE (kill (locR 16 136 22 23) xTy xSym)
    (seqE (kill (locR 16 136 33 34) rTy rSym) unitE)
def block : CoreExpr :=
  letS [Aloc (loc 16 136), Astmt] xSym ptrBty createX
    (letS [] rSym ptrBty createR
      (seqE initializeX (seqE initializeR (seqE switchBlock (seqE returnStmt cleanup)))))
def returnSave : CoreExpr :=
  Expr [Alabel LAreturn, Aloc (locR 1 136 5 9)]
    (Esave (retSym, intBty) [(tmp 50, ((intBty, some (retTy, By_value)), specInt 0))]
      (pureE (psym (tmp 50))))

/-- Exact equality includes all annotations, metadata, initializers and grouping. -/
theorem mainBody_shape : mainBody = seqE block returnSave := rfl

theorem stdlib_data_eq : data.stdlib = CorpusA7.T1.data.stdlib := rfl

theorem hasIntLibrary_restore (cmp : EmittedFile.Comparators)
    (h : EmittedStdCore.intLibraryCheck cmp.stdlib = true) :
    EmittedStdCore.HasIntLibrary (restoredFile cmp) :=
  EmittedStdCore.hasIntLibrary_of_stdlib (restoredFile cmp) cmp.stdlib
    (by change EmittedFile.restoreMap cmp.stdlib data.stdlib = _; rw [stdlib_data_eq]) h

theorem load_frag (x : sym) (ty : ctype) (n lo hi : Nat) : Frag (load x ty n lo hi) :=
  .wseq_sym (Frag.of_pePure _ (.sym _ _)) (.load_op rfl (.sym [] _))

theorem assignStmt_frag (start n m : Nat) (v : Int) : Frag (assignStmt start n m v) := by
  refine .sseq (.bound (.wseq_tuple
    (ls := [([], some (tmp n), ptrBty), ([], some (tmp m), intBty)]) ?_ ?_)) (.val_pure _)
  · refine .unseq (by simp) rfl ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Frag.of_pePure _ (.sym _ _)
    · exact .val_pure _
  · exact .wseq (.neg_store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl))
      (Frag.of_pePure _ (PePure.of_isPePure rfl))

theorem run_frag (an : List annot) (l : sym) : Frag (run an l) := by
  refine .run ?_
  intro pe hpe
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl <;> exact .sym _ _

theorem save_frag (an : List annot) (l : sym) (body : CoreExpr) (hb : Frag body) :
    Frag (save an l body) := by
  refine .save ?_ hb
  intro pe hpe
  change pe ∈ [psym xSym, psym rSym] at hpe
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl <;> exact .sym _ _

theorem defaultTail_frag : Frag defaultTail :=
  .sseq (save_frag _ _ _ (assignStmt_frag _ _ _ _)) (.sseq (run_frag _ _) (.val_pure _))
theorem case2Tail_frag : Frag case2Tail :=
  .sseq (save_frag _ _ _ (assignStmt_frag _ _ _ _)) (.sseq (run_frag _ _) defaultTail_frag)
theorem casesBody_frag : Frag casesBody :=
  .sseq (.sseq (save_frag _ _ _ (assignStmt_frag _ _ _ _))
    (.sseq (run_frag _ _) case2Tail_frag)) (.val_pure _)
theorem dispatch_frag : Frag dispatch :=
  .sseq (.if_ (PePure.of_isPePure rfl) (run_frag _ _) (.val_pure _))
    (.sseq (.if_ (PePure.of_isPePure rfl) (run_frag _ _) (.val_pure _))
      (.sseq (run_frag _ _) (.sseq (run_frag _ _) casesBody_frag)))
theorem specifiedBranch_frag (pe : generic_pexpr Unit sym)
    (hp : PePure (Pexpr [Astd "§6.8.4.2#5, sentence 1"] ()
      (PEcall (Sym EmittedStdCore.convInt.1) [tyPe switchTy, pe]))) :
    Frag (specifiedBranch pe) :=
  .sseq_sym (Frag.of_pePure _ hp) dispatch_frag

theorem switch_select (v : value) :
    select_case subst_sym_expr v switchPats =
      match v with
      | Vloaded (LVspecified o) => some (specifiedBranch (Pexpr [] () (PEval (Vobject o))))
      | Vloaded (LVunspecified _) => some (pureE
          (Pexpr [Astd "§6.5#5"] () (PEundef (loc 40 124) UB036_exceptional_condition)))
      | _ => none := by
  cases v <;> try rfl
  rename_i lv
  cases lv <;> rfl

theorem switch_frag : Frag switch := by
  refine .sseq_sym (.bound (load_frag _ _ _ _ _)) (.case_op rfl (.sym _ _) ?_ ?_ ?_)
  · intro q hq
    simp only [switchPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact specifiedBranch_frag _ (PePure.of_isPePure rfl)
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)
  · intro v e' hsel
    rw [switch_select] at hsel
    cases v <;> try cases hsel
    rename_i lv
    cases lv with
    | LVspecified o =>
      cases hsel
      exact specifiedBranch_frag _ (PePure.of_isPePure rfl)
    | LVunspecified ty =>
      cases hsel
      exact Frag.of_pePure _ (PePure.of_isPePure rfl)
  · exact case_hbsz_of_branches

theorem afterSwitch_frag : Frag afterSwitch :=
  .sseq (save_frag _ _ _ (.val_pure _)) (.val_pure _)
theorem switchBlock_frag : Frag switchBlock := .sseq switch_frag afterSwitch_frag

theorem returnStmt_frag : Frag returnStmt := by
  refine .sseq_sym (.bound (load_frag _ _ _ _ _))
    (.sseq (.kill_op rfl (.sym _ _)) (.sseq (.kill_op rfl (.sym _ _)) (.run ?_)))
  intro pe hpe
  obtain rfl := List.mem_singleton.mp hpe
  exact PePure.of_isPePure rfl

theorem cleanup_frag : Frag cleanup :=
  .sseq (.kill_op rfl (.sym _ _)) (.sseq (.kill_op rfl (.sym _ _)) (.val_pure _))
theorem block_frag : Frag block := by
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)) ?_
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)) ?_
  refine .sseq (.sseq_sym (.bound (.val_pure _))
    (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl))) ?_
  exact .sseq (.sseq_sym (.bound (.val_pure _))
    (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl)))
    (.sseq switchBlock_frag (.sseq returnStmt_frag cleanup_frag))
theorem returnSave_frag : Frag returnSave := by
  refine .save ?_ (Frag.of_pePure _ (.sym _ _))
  intro pe hpe
  obtain rfl := List.mem_singleton.mp hpe
  exact CorpusE0.specInt_pePure 0

theorem mainBody_frag : Frag mainBody := by
  rw [mainBody_shape]
  exact .sseq block_frag returnSave_frag

theorem mainBody_evalDepth : evalDepth mainBody ≤ 40 := by
  rw [mainBody_shape]
  decide +kernel

end CerberusHeapLang.CorpusA7.T6
