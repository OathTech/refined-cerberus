/- The actual main body projected from the complete emitted t4 fixture.
   Shape equalities below support public proofs without changing the referent. -/
import CerberusHeapLang.Examples.EmittedT4Data
import CerberusHeapLang.EmittedStdCore
import CerberusHeapLang.EmittedIntSupport
import CerberusHeapLang.Substitution
import CerberusHeapLang.EmittedMapChecks
import Core_linking
import CerberusHeapLang.Examples.CorpusE0
import Lean

set_option autoImplicit false

namespace CerberusHeapLang.CorpusA7.T4

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

open CorpusE0 (psym seqE letS letW bnd act specInt wc)

def sourceDigest : String := match mainSym with | .Symbol digest _ _ => digest
def sourcePos (col : Nat) : CerbLocation.Pos := ⟨"docs/corpus-e0/t4_while.c", 1, col⟩
def loc (lo hi : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) .noCursor
def locP (lo hi cursor : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) (.pointCursor (sourcePos cursor))
def locR (lo hi clo chi : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) (.regionCursor (sourcePos clo) (sourcePos chi))

def tmp (n : Nat) : sym := .Symbol sourceDigest n .SD_None
def iSym : sym := .Symbol sourceDigest 21 (.SD_ObjectAddress "i")
def sSym : sym := .Symbol sourceDigest 22 (.SD_ObjectAddress "s")
def retSym : sym := .Symbol sourceDigest 27 (.SD_Id "ret_27")
def continueSym : sym := .Symbol sourceDigest 28 (.SD_Id "continue_28")
def breakSym : sym := .Symbol sourceDigest 29 (.SD_Id "break_29")
def whileSym : sym := .Symbol sourceDigest 32 (.SD_Id "while_32")
abbrev intBty : core_base_type := BTy_loaded OTy_integer
abbrev ptrBty : core_base_type := BTy_object OTy_pointer

def mainLookupCheck (cmp : sym → sym → LemOrdering) : Bool :=
  EmittedFile.mapLookupCheck cmp EmittedStdCore.referenceCmp mainSym data.funs

theorem referenceLookup_main :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym
      (EmittedFile.restoreMap EmittedStdCore.referenceCmp data.funs) =
      some (.Proc (locR 1 100 5 9) (some 20) intBty [] mainBody) := rfl

theorem restoredFile_mainLookup (cmp : EmittedFile.Comparators)
    (h : mainLookupCheck cmp.funs = true) :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym (restoredFile cmp).funs =
      some (.Proc (locR 1 100 5 9) (some 20) intBty [] mainBody) :=
  (EmittedFile.restoreMap_lookup_of_check cmp.funs EmittedStdCore.referenceCmp
    EmittedStdCore.referenceCmp mainSym data.funs h).trans referenceLookup_main

theorem mainLookup_of_capture_eq (fallback : EmittedFile.Comparators)
    (f : file core_run_annotation) (hd : EmittedFile.captureData f = data)
    (hc : mainLookupCheck (EmittedFile.captureComparators fallback f).funs = true) :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym f.funs =
      some (.Proc (locR 1 100 5 9) (some 20) intBty [] mainBody) := by
  rw [← EmittedFile.restore_eq_of_data_eq fallback f data hd]
  exact restoredFile_mainLookup _ hc

def iTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 18 21)]
def sTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 29 32)]
def retTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 1 4)]
def tyPe (ty : ctype) : generic_pexpr Unit sym := Pexpr [] () (PEval (Vctype ty))
def intValueAnnot : annot := Avalue (Ainteger (.Signed .Int_))
def exprAnn (l : CerbLocation.Loc) : List annot := [Aloc l, Aexpr, intValueAnnot]
def literal (an : List annot) (n : Int) : CoreExpr :=
  Expr an (Epure (Pexpr [] () (PEval (lint n))))
def pureE (pe : generic_pexpr Unit sym) : CoreExpr := Expr [] (Epure pe)
def unitE : CoreExpr := pureE (Pexpr [] () (PEval Vunit))
def convLoaded (an : List annot) (ty : ctype) (s : sym) : generic_pexpr Unit sym :=
  Pexpr an () (PEcall (Sym EmittedStdCore.convLoadedInt.1) [tyPe ty, psym s])
def convInt (an : List annot) (s : sym) : generic_pexpr Unit sym :=
  Pexpr an () (PEcall (Sym EmittedStdCore.convInt.1)
    [tyPe (EmittedStdCore.sintTyAnn []), psym s])
def intTuple (n m : Nat) : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Ctuple [psym (tmp n), psym (tmp m)])
def intTuplePat (n m : Nat) : pattern :=
  Pattern [] (CaseCtor Ctuple [Pattern [] (CaseBase (some (tmp n), intBty)),
    Pattern [] (CaseBase (some (tmp m), intBty))])
def specPat (n : Nat) : pattern := Pattern [] (CaseCtor Cspecified
  [Pattern [] (CaseBase (some (tmp n), BTy_object OTy_integer))])
def specTuplePat (n m : Nat) : pattern := Pattern [] (CaseCtor Ctuple [specPat n, specPat m])
def anyTuplePat : pattern := Pattern [] (CaseBase (none, BTy_tuple [intBty, intBty]))
def unspecified (l : CerbLocation.Loc) : generic_pexpr Unit sym :=
  Pexpr [] () (PEval (Vloaded (LVunspecified (EmittedStdCore.sintTyAnn [Aloc l]))))

def load (ty : ctype) (x : sym) (n lo hi : Nat) : CoreExpr :=
  letW (exprAnn (loc lo hi)) (tmp n) ptrBty
    (Expr [Aloc (loc lo hi), Aexpr] (Epure (psym x)))
    (act (loc lo hi) (Load0 (tyPe ty) (psym (tmp n)) NA))

def ltPats (l : CerbLocation.Loc) (p q : Nat) : List (pattern × CoreExpr) :=
  [(specTuplePat p q,
    Expr [Astd "§6.5.8#6"] (Epure (Pexpr [] () (PEif
      (Pexpr [] () (PEop OpLt (convInt [Astd "§6.5.8#3"] (tmp p))
        (convInt [Astd "§6.5.8#3"] (tmp q)))) (specInt 1) (specInt 0))))),
   (anyTuplePat, pureE (unspecified l))]
def lt (ty : ctype) (x : sym) (t n m p q start : Nat) (k : Int) : CoreExpr :=
  Expr (exprAnn (locP start (start + 5) (start + 2)) ++ [Astd "§6.5.8"])
    (Ewseq (intTuplePat n m)
      (Expr [] (Eunseq [load ty x t start (start + 1),
        literal (exprAnn (loc (start + 4) (start + 5))) k]))
      (Expr [] (Ecase (intTuple n m) (ltPats (locP start (start + 5) (start + 2)) p q))))

def truthPats (l : CerbLocation.Loc) (p q : Nat) (negate : Bool) :
    List (pattern × generic_pexpr Unit sym) :=
  let test := Pexpr [] () (PEop OpEq (convInt [Astd "§6.5.9#4, sentence 1"] (tmp p))
      (convInt [Astd "§6.5.9#4, sentence 1"] (tmp q)))
  let test := if negate then Pexpr [Astd "§6.5.9#4, sentence 3"] () (PEnot test)
    else Pexpr [Astd "§6.5.9#4, sentence 3"] () (PEop OpEq
      (convInt [Astd "§6.5.9#4, sentence 1"] (tmp p))
      (convInt [Astd "§6.5.9#4, sentence 1"] (tmp q)))
  [(specTuplePat p q, Pexpr [Astd "§6.5.9#3"] () (PEif test (specInt 1) (specInt 0))),
   (anyTuplePat, unspecified l)]
def truth (l : CerbLocation.Loc) (n m p q : Nat) (negate : Bool) (e : CoreExpr) : CoreExpr :=
  Expr (exprAnn l) (Ewseq (intTuplePat n m)
    (Expr [] (Eunseq [e, literal (exprAnn l) 0]))
    (pureE (Pexpr [] () (PEcase (intTuple n m) (truthPats l p q negate)))))
def left : CoreExpr :=
  truth (locP 47 52 49) 41 42 43 44 false
    (truth (locP 47 52 49) 46 47 48 49 false
      (lt iTy iSym 51 52 53 54 55 47 5))
def right : CoreExpr :=
  truth (locP 56 61 58) 60 61 62 63 true
    (lt sTy sSym 65 66 67 68 69 56 7)
def andSpecified (pe : generic_pexpr Unit sym) : CoreExpr :=
  Expr [] (Eif (Pexpr [] () (PEop OpEq pe (Pexpr [] () (PEval (oint 0)))))
    (letS [] (tmp 59) intBty (literal (exprAnn .unknown) 0)
      (pureE (convLoaded [] (EmittedStdCore.sintTyAnn [Aloc (locP 47 61 53)]) (tmp 59))))
    (letS [] (tmp 71) intBty right
      (pureE (convLoaded [] (EmittedStdCore.sintTyAnn [Aloc (locP 47 61 53)]) (tmp 71)))))
def andPats : List (pattern × CoreExpr) :=
  [(specPat 58, andSpecified (psym (tmp 58))),
   (Pattern [] (CaseCtor Cunspecified [Pattern [] (CaseBase (none, BTy_ctype))]),
    pureE (Pexpr [] () (PEundef (locP 47 61 53) (UB_CERB004_unspecified UB_unspec_conditional))))]
def andE : CoreExpr :=
  letS (exprAnn (locP 47 61 53) ++ [Astd "6.5.13#3", Astd "6.5.13#4", Aexpr, intValueAnnot])
    (tmp 57) intBty left (Expr [] (Ecase (psym (tmp 57)) andPats))
def cond : CoreExpr := bnd (truth (locP 47 61 53) 36 37 38 39 false andE)
def boolPats : List (pattern × CoreExpr) :=
  [(specPat 35, pureE (Pexpr [] () (PEif
      (Pexpr [] () (PEnot (Pexpr [] () (PEop OpEq (psym (tmp 35))
        (Pexpr [] () (PEval (oint 1)))))))
      (Pexpr [] () (PEval Vtrue)) (Pexpr [] () (PEval Vfalse))))),
   (Pattern [] (CaseCtor Cunspecified [Pattern [] (CaseBase (none, BTy_ctype))]),
    Expr [] (End [pureE (Pexpr [] () (PEval Vtrue)), pureE (Pexpr [] () (PEval Vfalse))]))]
def boolE : CoreExpr := Expr [] (Ecase (psym (tmp 34)) boolPats)
def addBranch (p q : generic_pexpr Unit sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Cspecified
    [Pexpr [Astd "§6.5.6#5"] () (PEcatch_exceptional_condition (.Signed .Int_) IOpAdd
      (Pexpr [Astd "§6.5.6#4"] () (PEconv_int (.Signed .Int_) p))
      (Pexpr [Astd "§6.5.6#4"] () (PEconv_int (.Signed .Int_) q)))])
def addPats (l : CerbLocation.Loc) (p q : Nat) : List (pattern × generic_pexpr Unit sym) :=
  [(specTuplePat p q, addBranch (psym (tmp p)) (psym (tmp q))),
   (anyTuplePat, Pexpr [Astd "§6.5#5"] () (PEundef l UB036_exceptional_condition))]
def addE (l : CerbLocation.Loc) (n m p q : Nat) (e1 e2 : CoreExpr) : CoreExpr :=
  Expr (exprAnn l ++ [Astd "§6.5.6"]) (Ewseq (intTuplePat n m)
    (Expr [] (Eunseq [e1, e2]))
    (pureE (Pexpr [] () (PEcase (intTuple n m) (addPats l p q)))))
def addSI : CoreExpr := addE (locP 69 74 71) 73 74 75 76
  (load sTy sSym 78 69 70) (load iTy iSym 79 73 74)
def addI1 : CoreExpr := addE (locP 80 85 82) 82 83 84 85
  (load iTy iSym 87 80 81) (literal (exprAnn (loc 84 85)) 1)
def assign (ty : ctype) (x : sym) (start n m : Nat) (rhs : CoreExpr) : CoreExpr :=
  Expr [Aloc (loc start (start + 10)), Astmt]
    (Esseq (Pattern [] (CaseBase (none, intBty)))
      (bnd (Expr (exprAnn (locP start (start + 9) (start + 2)) ++ [Astd "§6.5.16#3, sentence 4"])
        (Ewseq (Pattern [] (CaseCtor Ctuple
            [Pattern [] (CaseBase (some (tmp n), ptrBty)), Pattern [] (CaseBase (some (tmp m), intBty))]))
          (Expr [Astd "§6.5.16#3, sentence 5"]
            (Eunseq [Expr [Aloc (loc start (start + 1)), Aexpr] (Epure (psym x)), rhs]))
          (Expr [] (Ewseq wc
            (Expr [Astd "§6.5.16.1#2, store"]
              (Eaction (Paction polarity.Neg0 (Action (locP start (start + 9) (start + 2))
                empty_annotation (Store0 false (tyPe ty)
                  (Pexpr [Astd "§6.5.16#3, sentence 1"] () (PEsym (tmp n)))
                  (convLoaded [Astd "§6.5.16.1#2, conversion"] ty (tmp m)) NA)))))
            (pureE (convLoaded [Astd "§6.5.16.1#2, conversion"] ty (tmp m)))))))) unitE)
def ptrInits : List CorpusE0.SaveInit :=
  [(iSym, ((ptrBty, some (iTy, .By_pointer)), psym iSym)),
   (sSym, ((ptrBty, some (sTy, .By_pointer)), psym sSym))]
def save (la : label_annot) (l : sym) (body : CoreExpr) : CoreExpr :=
  Expr [Aloc (loc 40 88), Astmt, Alabel la] (Esave (l, BTy_unit) ptrInits body)
def body : CoreExpr :=
  seqE (Expr [Aloc (loc 40 88), Astmt] (Esseq wc
    (Expr [Aloc (loc 63 88), Astmt] (Esseq wc
      (assign sTy sSym 65 72 80 addSI)
      (seqE (assign iTy iSym 76 81 88 addI1) unitE)))
    (seqE (save (.LAloop_continue 24) continueSym
      (Expr [Aloc (loc 40 88), Astmt] (Epure (Pexpr [] () (PEval Vunit))))) unitE)))
    (Expr [] (Erun empty_annotation whileSym [psym iSym, psym sSym]))
def loopTest : CoreExpr :=
  letS [] (tmp 34) intBty cond (letS [] (tmp 33) BTy_boolean boolE
    (Expr [] (Eif (psym (tmp 33)) body unitE)))
def whileE : CoreExpr := save (.LAloop 24) whileSym loopTest
def afterWhile : CoreExpr :=
  seqE (save (.LAloop_break 24) breakSym
    (Expr [Aloc (loc 40 88), Astmt] (Epure (Pexpr [] () (PEval Vunit))))) unitE

def kill (atLoc : CerbLocation.Loc) (ty : ctype) (s : sym) : CoreExpr :=
  act atLoc (Kill (Static0 ty) (psym s))
def returnStmt : CoreExpr :=
  letS [Aloc (loc 89 98), Astmt] (tmp 90) intBty (bnd (load sTy sSym 89 96 97))
    (seqE (kill (loc 89 98) iTy iSym)
      (seqE (kill (loc 89 98) sTy sSym)
        (Expr [] (Erun empty_annotation retSym [convLoaded [] retTy (tmp 90)]))))
def cleanup : CoreExpr :=
  seqE (kill (locR 16 100 22 23) iTy iSym)
    (seqE (kill (locR 16 100 33 34) sTy sSym) unitE)
def returnSave : CoreExpr :=
  Expr [Alabel .LAreturn, Aloc (locR 1 100 5 9)]
    (Esave (retSym, intBty) [(tmp 91, ((intBty, some (retTy, .By_value)), specInt 0))]
      (pureE (psym (tmp 91))))
def createI : CoreExpr := act (locR 16 100 22 23)
  (Create (Pexpr [] () (PEctor Civalignof [tyPe iTy])) (tyPe iTy)
    (PrefSource (loc 22 23) [mainSym, iSym]))
def createS : CoreExpr := act (locR 16 100 33 34)
  (Create (Pexpr [] () (PEctor Civalignof [tyPe sTy])) (tyPe sTy)
    (PrefSource (loc 33 34) [mainSym, sSym]))
def initializeI : CoreExpr :=
  letS [Aloc (loc 18 28), Astmt] (tmp 30) intBty (bnd (literal (exprAnn (loc 26 27)) 0))
    (act (loc 18 28) (Store0 false (tyPe iTy) (psym iSym) (convLoaded [] iTy (tmp 30)) NA))
def initializeS : CoreExpr :=
  letS [Aloc (loc 29 39), Astmt] (tmp 31) intBty (bnd (literal (exprAnn (loc 37 38)) 0))
    (act (loc 29 39) (Store0 false (tyPe sTy) (psym sSym) (convLoaded [] sTy (tmp 31)) NA))
def mainTerm : CoreExpr :=
  seqE (letS [Aloc (loc 16 100), Astmt] iSym ptrBty createI
    (letS [] sSym ptrBty createS
      (seqE initializeI (seqE initializeS
        (seqE (Expr [Aloc (loc 40 88), Astmt] (Esseq wc whileE afterWhile))
          (seqE returnStmt cleanup)))))) returnSave

theorem mainBody_shape : mainBody = mainTerm := rfl

theorem load_frag (ty : ctype) (x : sym) (n c1 c2 : Nat) : Frag (load ty x n c1 c2) :=
  .wseq_sym (Frag.of_pePure _ (.sym _ _))
    (.load_op rfl (.sym [] _))

theorem lt_frag (ty : ctype) (x : sym) (t n m p q start : Nat) (k : Int) :
    Frag (lt ty x t n m p q start k) := by
  refine .wseq_tuple (ls := [([], some (tmp n), intBty), ([], some (tmp m), intBty)]) ?_ ?_
  · refine .unseq (by simp) rfl ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (load_frag) _ _ _ _ _
    · exact .val_pure _
  · refine .case_op rfl (PePure.of_isPePure rfl) ?_ ?_ ?_
    · intro br hbr
      simp only [ltPats, List.mem_cons, List.not_mem_nil, or_false] at hbr
      rcases hbr with rfl | rfl <;>
        exact Frag.of_pePure _ (PePure.of_isPePure rfl)
    · intro v e' hsel
      obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
      simp only [ltPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl)
    · exact case_hbsz_of_branches

theorem truth_frag (loc : CerbLocation.Loc) (n m p q : Nat) (negate : Bool)
    (e : CoreExpr) (he : Frag e) (hc : ccallFree e = true) :
    Frag (truth loc n m p q negate e) := by
  refine .wseq_tuple (ls := [([], some (tmp n), intBty), ([], some (tmp m), intBty)]) ?_ ?_
  · refine .unseq (by simp) ?_ ?_
    · change (ccallFree e && (true && true)) = true
      rw [hc]
      rfl
    · intro e' he'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl
      · exact he
      · exact .val_pure _
  · cases negate <;> exact Frag.of_pePure _ (PePure.of_isPePure rfl)

theorem left_frag : Frag left :=
  (truth_frag) _ _ _ _ _ _ _ (truth_frag _ _ _ _ _ _ _ (lt_frag _ _ _ _ _ _ _ _ _) rfl) rfl

theorem right_frag : Frag right :=
  (truth_frag) _ _ _ _ _ _ _ (lt_frag _ _ _ _ _ _ _ _ _) rfl

theorem andSpecified_frag (pe : generic_pexpr Unit sym) (hp : PePure pe) :
    Frag (andSpecified pe) := by
  refine .if_ (.op _ _ rfl hp (.val _ _)) ?_ ?_
  · exact .sseq_sym (.val_pure _)
      (Frag.of_pePure _ (PePure.of_isPePure rfl))
  · exact .sseq_sym (right_frag)
      (Frag.of_pePure _ (PePure.of_isPePure rfl))

theorem and_select (v : value) :
    select_case subst_sym_expr v andPats =
      match v with
      | Vloaded (LVspecified o) => some (andSpecified (Pexpr [] () (PEval (Vobject o))))
      | Vloaded (LVunspecified _) => some (pureE (Pexpr [] ()
          (PEundef (locP 47 61 53) (UB_CERB004_unspecified UB_unspec_conditional))))
      | _ => none := by
  cases v <;> try rfl
  rename_i lv
  cases lv <;> rfl

theorem andE_frag : Frag andE := by
  refine .sseq_sym (left_frag) (.case_op rfl (.sym _ _) ?_ ?_ ?_)
  · intro br hbr
    simp only [andPats, List.mem_cons, List.not_mem_nil, or_false] at hbr
    rcases hbr with rfl | rfl
    · exact andSpecified_frag _ (.sym _ _)
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)
  · intro v e' hsel
    rw [and_select] at hsel
    cases v <;> try cases hsel
    rename_i lv
    cases lv with
    | LVspecified o =>
      cases hsel
      exact andSpecified_frag _ (.val _ _)
    | LVunspecified ty =>
      cases hsel
      exact Frag.of_pePure _ (PePure.of_isPePure rfl)
  · exact case_hbsz_of_branches

theorem cond_frag : Frag cond :=
  .bound (truth_frag _ _ _ _ _ _ _ (andE_frag) rfl)

theorem boolE_frag : Frag boolE := by
  refine .case_op rfl (.sym _ _) ?_ ?_ ?_
  · intro q hq
    simp only [boolPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)
    · refine .nd (by decide) ?_
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .val_pure _
  · intro v e' hsel
    obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
    simp only [boolPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl)
    · have he (bs : List (sym × value)) : substFold (Expr [] (End [pureE (Pexpr [] () (PEval Vtrue)),
          pureE (Pexpr [] () (PEval Vfalse))])) bs =
          Expr [] (End [pureE (Pexpr [] () (PEval Vtrue)),
            pureE (Pexpr [] () (PEval Vfalse))]) := by
        induction bs with
        | nil => rfl
        | cons pair rest ih =>
          rcases pair with ⟨s, v⟩
          rw [substFold_cons, ih]
          rfl
      rw [he binds]
      refine .nd (by decide) ?_
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .val_pure _
  · exact case_hbsz_of_branches

theorem addE_frag (loc : CerbLocation.Loc) (n m p q : Nat) (e1 e2 : CoreExpr)
    (h1 : Frag e1) (h2 : Frag e2) (hc1 : ccallFree e1 = true) (hc2 : ccallFree e2 = true) :
    Frag (addE loc n m p q e1 e2) := by
  refine .wseq_tuple (ls := [([], some (tmp n), intBty), ([], some (tmp m), intBty)]) ?_ ?_
  · refine .unseq (by simp) ?_ ?_
    · change (ccallFree e1 && (ccallFree e2 && true)) = true
      rw [hc1, hc2]
      rfl
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact h1
      · exact h2
  · exact Frag.of_pePure _ (PePure.of_isPePure rfl)

theorem assign_frag (ty : ctype) (x : sym) (start n m : Nat) (rhs : CoreExpr)
    (hr : Frag rhs) (hc : ccallFree rhs = true) : Frag (assign ty x start n m rhs) := by
  refine .sseq (.bound (.wseq_tuple
    (ls := [([], some (tmp n), ptrBty), ([], some (tmp m), intBty)]) ?_ ?_)) (.val_pure _)
  · refine .unseq (by simp) ?_ ?_
    · change (true && (ccallFree rhs && true)) = true
      rw [hc]
      rfl
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact Frag.of_pePure _ (.sym _ _)
      · exact hr
  · exact .wseq
      (.neg_store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl))
      (Frag.of_pePure _ (PePure.of_isPePure rfl))

theorem save_frag (la : label_annot) (l : sym) (body : CoreExpr) (hb : Frag body) : Frag (save la l body) := by
  refine .save ?_ hb
  · intro pe hpe
    change pe ∈ [psym iSym, psym sSym] at hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact .sym _ _

theorem body_frag : Frag body := by
  refine .sseq (.sseq (.sseq ?_ (.sseq ?_ (.val_pure _)))
    (.sseq (save_frag _ _ _ (.val_pure _)) (.val_pure _))) ?_
  · exact (assign_frag) _ _ _ _ _ _
      (addE_frag _ _ _ _ _ _ _ (load_frag _ _ _ _ _) (load_frag _ _ _ _ _) rfl rfl) rfl
  · exact (assign_frag) _ _ _ _ _ _
      (addE_frag _ _ _ _ _ _ _ (load_frag _ _ _ _ _)
        (.val_pure _) rfl rfl) rfl
  · refine .run ?_
    · intro pe hpe
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      rcases hpe with rfl | rfl <;> exact .sym _ _

theorem whileE_frag : Frag whileE :=
  (save_frag) _ _ _ (.sseq_sym (cond_frag) (.sseq_sym (boolE_frag)
    (.if_ (.sym _ _) (body_frag) (.val_pure _))))


theorem returnStmt_frag : Frag returnStmt := by
  refine .sseq_sym (.bound (load_frag _ _ _ _ _))
    (.sseq (.kill_op rfl (.sym _ _)) (.sseq (.kill_op rfl (.sym _ _)) (.run ?_)))
  intro pe hpe
  obtain rfl := List.mem_singleton.mp hpe
  exact PePure.of_isPePure rfl

theorem cleanup_frag : Frag cleanup :=
  .sseq (.kill_op rfl (.sym _ _)) (.sseq (.kill_op rfl (.sym _ _)) (.val_pure _))
theorem afterWhile_frag : Frag afterWhile :=
  .sseq (save_frag _ _ _ (.val_pure _)) (.val_pure _)
theorem returnSave_frag : Frag returnSave := by
  refine .save ?_ (Frag.of_pePure _ (.sym _ _))
  intro pe hpe
  obtain rfl := List.mem_singleton.mp hpe
  exact CorpusE0.specInt_pePure 0

theorem mainBody_frag : Frag mainBody := by
  rw [mainBody_shape]
  refine .sseq ?_ returnSave_frag
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)) ?_
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)) ?_
  refine .sseq (.sseq_sym (.bound (.val_pure _))
    (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl))) ?_
  exact .sseq (.sseq_sym (.bound (.val_pure _))
    (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl)))
    (.sseq (.sseq whileE_frag afterWhile_frag) (.sseq returnStmt_frag cleanup_frag))

/-- A syntactic membership witness and a separate sufficient operand depth. -/
theorem mainBody_evalDepth : evalDepth mainBody ≤ 40 := by
  rw [mainBody_shape]
  decide +kernel

end CerberusHeapLang.CorpusA7.T4
