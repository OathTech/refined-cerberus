/- The actual main body projected from the complete emitted t5 fixture.
   Shape equalities below support public proofs without changing the referent. -/
import CerberusHeapLang.EmittedStdCore
import CerberusHeapLang.Examples.EmittedT5Data
import CerberusHeapLang.Substitution
import CerberusHeapLang.EmittedMapChecks
import Core_linking
import CerberusHeapLang.Examples.CorpusE0
import Lean

set_option autoImplicit false

namespace CerberusHeapLang.CorpusA7.T5

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
def sourcePos (col : Nat) : CerbLocation.Pos := ⟨"docs/corpus-e0/t5_ifelse.c", 1, col⟩
def loc (lo hi : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) .noCursor
def locP (lo hi cursor : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) (.pointCursor (sourcePos cursor))
def locR (lo hi clo chi : Nat) : CerbLocation.Loc :=
  .region (sourcePos lo) (sourcePos hi) (.regionCursor (sourcePos clo) (sourcePos chi))

def tmp (n : Nat) : sym := .Symbol sourceDigest n .SD_None
def xSym : sym := .Symbol sourceDigest 21 (.SD_ObjectAddress "x")
def rSym : sym := .Symbol sourceDigest 22 (.SD_ObjectAddress "r")
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
      some (.Proc (locR 1 85 5 9) (some 20) intBty [] mainBody) := rfl

/-- The genuine startup lookup finds the exact parameterless main
procedure, retaining its location, identifier, result type and body. -/
theorem restoredFile_mainLookup (cmp : EmittedFile.Comparators)
    (h : mainLookupCheck cmp.funs = true) :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym (restoredFile cmp).funs =
      some (.Proc (locR 1 85 5 9) (some 20) intBty [] mainBody) :=
  (EmittedFile.restoreMap_lookup_of_check cmp.funs EmittedStdCore.referenceCmp
    EmittedStdCore.referenceCmp mainSym data.funs h).trans referenceLookup_main

/-- Transfer the lookup to an actual file when its complete data agrees
and the original function comparator passes the finite check. -/
theorem mainLookup_of_capture_eq (fallback : EmittedFile.Comparators)
    (f : file core_run_annotation) (hd : EmittedFile.captureData f = data)
    (hc : mainLookupCheck (EmittedFile.captureComparators fallback f).funs = true) :
    fmapLookupBy EmittedStdCore.referenceCmp mainSym f.funs =
      some (.Proc (locR 1 85 5 9) (some 20) intBty [] mainBody) := by
  rw [← EmittedFile.restore_eq_of_data_eq fallback f data hd]
  exact restoredFile_mainLookup _ hc

theorem stdlib_data_eq : data.stdlib = CorpusA7.T1.data.stdlib := rfl

theorem hasIntLibrary_restore (cmp : EmittedFile.Comparators)
    (h : EmittedStdCore.intLibraryCheck cmp.stdlib = true) :
    EmittedStdCore.HasIntLibrary (restoredFile cmp) :=
  EmittedStdCore.hasIntLibrary_of_stdlib _ cmp.stdlib (by rw [← stdlib_data_eq]; rfl) h

def xTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 18 21)]
def rTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 29 32)]
def retTy : ctype := EmittedStdCore.sintTyAnn [Aloc (loc 1 4)]
def conditionTy : ctype := EmittedStdCore.sintTyAnn [Aloc (locP 40 45 42)]
def tyPe (ty : ctype) : generic_pexpr Unit sym := Pexpr [] () (PEval (Vctype ty))
def convLoaded (an : List annot) (ty : ctype) (s : sym) : generic_pexpr Unit sym :=
  Pexpr an () (PEcall (Sym EmittedStdCore.convLoadedInt.1) [tyPe ty, psym s])
def convInt (an : List annot) (p : generic_pexpr Unit sym) : generic_pexpr Unit sym :=
  Pexpr an () (PEcall (Sym EmittedStdCore.convInt.1) [tyPe (EmittedStdCore.sintTyAnn []), p])
def intValueAnnot : annot := Avalue (Ainteger (.Signed .Int_))
def intPe (n : Int) : generic_pexpr Unit sym := Pexpr [] () (PEval (lint n))
def intLiteral (a : List annot) (n : Int) : CoreExpr := Expr a (Epure (intPe n))
def pure (pe : generic_pexpr Unit sym) : CoreExpr := Expr [] (Epure pe)
def unitExpr : CoreExpr := pure (Pexpr [] () (PEval Vunit))
def tuple (n m : Nat) : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Ctuple [psym (tmp n), psym (tmp m)])
def tuplePattern (n m : Nat) : pattern :=
  Pattern [] (CaseCtor Ctuple
    [Pattern [] (CaseBase (some (tmp n), intBty)), Pattern [] (CaseBase (some (tmp m), intBty))])
def specifiedPattern (n : Nat) : pattern :=
  Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some (tmp n), BTy_object OTy_integer))])
def specifiedTuplePattern (n m : Nat) : pattern :=
  Pattern [] (CaseCtor Ctuple [specifiedPattern n, specifiedPattern m])
def anyTuplePattern : pattern := Pattern [] (CaseBase (none, BTy_tuple [intBty, intBty]))
def unspecifiedPe : generic_pexpr Unit sym := Pexpr [] () (PEval (Vloaded (LVunspecified conditionTy)))

def createX : CoreExpr :=
  act (locR 16 85 22 23)
    (Create (Pexpr [] () (PEctor Civalignof [tyPe xTy])) (tyPe xTy)
      (PrefSource (loc 22 23) [mainSym, xSym]))
def createR : CoreExpr :=
  act (locR 16 85 33 34)
    (Create (Pexpr [] () (PEctor Civalignof [tyPe rTy])) (tyPe rTy)
      (PrefSource (loc 33 34) [mainSym, rSym]))
def initializeX : CoreExpr :=
  letS [Aloc (loc 18 28), Astmt] (tmp 25) intBty
    (bnd (intLiteral [Aloc (loc 26 27), Aexpr, intValueAnnot] 3))
    (act (loc 18 28) (Store0 false (tyPe xTy) (psym xSym) (convLoaded [] xTy (tmp 25)) NA))
def initializeR : CoreExpr :=
  Expr [Aloc (loc 29 35), Astmt, Astd "§6.2.4#6"]
    (Eaction (Paction polarity.Pos (Action (loc 29 35) empty_annotation
      (Store0 false (tyPe rTy) (psym rSym) (Pexpr [] () (PEval (Vloaded (LVunspecified rTy)))) NA))))
def load (ty : ctype) (x : sym) (n lo hi : Nat) : CoreExpr :=
  letW [Aloc (loc lo hi), Aexpr, intValueAnnot] (tmp n) ptrBty
    (Expr [Aloc (loc lo hi), Aexpr] (Epure (psym x)))
    (act (loc lo hi) (Load0 (tyPe ty) (psym (tmp n)) NA))

def gtBranch (p q : generic_pexpr Unit sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif
    (Pexpr [] () (PEop OpGt (convInt [Astd "§6.5.8#3"] p) (convInt [Astd "§6.5.8#3"] q)))
    (specInt 1) (specInt 0))
def gtPats : List (pattern × CoreExpr) :=
  [(specifiedTuplePattern 37 38,
      Expr [Astd "§6.5.8#6"] (Epure (gtBranch (psym (tmp 37)) (psym (tmp 38))))),
   (anyTuplePattern, pure unspecifiedPe)]
def gt : CoreExpr :=
  Expr [Aloc (locP 40 45 42), Aexpr, intValueAnnot, Astd "§6.5.8"]
    (Ewseq (tuplePattern 35 36)
      (Expr [] (Eunseq [load xTy xSym 34 40 41,
        intLiteral [Aloc (loc 44 45), Aexpr, intValueAnnot] 2]))
      (Expr [] (Ecase (tuple 35 36) gtPats)))
def condBranch (p q : generic_pexpr Unit sym) : generic_pexpr Unit sym :=
  Pexpr [Astd "§6.5.9#3"] () (PEif
    (Pexpr [Astd "§6.5.9#4, sentence 3"] () (PEop OpEq
      (convInt [Astd "§6.5.9#4, sentence 1"] p) (convInt [Astd "§6.5.9#4, sentence 1"] q)))
    (specInt 1) (specInt 0))
def condPats : List (pattern × generic_pexpr Unit sym) :=
  [(specifiedTuplePattern 31 32, condBranch (psym (tmp 31)) (psym (tmp 32))),
   (anyTuplePattern, unspecifiedPe)]
def cond : CoreExpr :=
  bnd (Expr [Aloc (locP 40 45 42), Aexpr, intValueAnnot]
    (Ewseq (tuplePattern 29 30)
      (Expr [] (Eunseq [gt, intLiteral [Aloc (locP 40 45 42), Aexpr, intValueAnnot] 0]))
      (pure (Pexpr [] () (PEcase (tuple 29 30) condPats)))))
def boolBranch (pe : generic_pexpr Unit sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (Pexpr [] () (PEnot
    (Pexpr [] () (PEop OpEq pe (Pexpr [] () (PEval (oint 1)))))))
    (Pexpr [] () (PEval Vtrue)) (Pexpr [] () (PEval Vfalse)))
def boolPats : List (pattern × CoreExpr) :=
  [(specifiedPattern 28, pure (boolBranch (psym (tmp 28)))),
   (Pattern [] (CaseCtor Cunspecified [Pattern [] (CaseBase (none, BTy_ctype))]),
      Expr [] (End [pure (Pexpr [] () (PEval Vtrue)), pure (Pexpr [] () (PEval Vfalse))]))]
def boolExpr : CoreExpr := Expr [] (Ecase (psym (tmp 27)) boolPats)

def assignmentPtr (n : Nat) : generic_pexpr Unit sym :=
  Pexpr [Astd "§6.5.16#3, sentence 1"] () (PEsym (tmp n))
def assignmentConv (m : Nat) : generic_pexpr Unit sym :=
  convLoaded [Astd "§6.5.16.1#2, conversion"] rTy (tmp m)
def assignBlock (start n m : Nat) (v : Int) : CoreExpr :=
  Expr [Aloc (loc (start - 2) (start + 8)), Astmt]
    (Esseq CorpusE0.wc
      (Expr [Aloc (loc start (start + 6)), Astmt]
        (Esseq (Pattern [] (CaseBase (none, intBty)))
          (bnd (Expr [Aloc (locP start (start + 5) (start + 2)), Aexpr, intValueAnnot,
              Astd "§6.5.16#3, sentence 4"]
            (Ewseq (Pattern [] (CaseCtor Ctuple
                [Pattern [] (CaseBase (some (tmp n), ptrBty)), Pattern [] (CaseBase (some (tmp m), intBty))]))
              (Expr [Astd "§6.5.16#3, sentence 5"]
                (Eunseq [Expr [Aloc (loc start (start + 1)), Aexpr] (Epure (psym rSym)),
                  intLiteral [Aloc (loc (start + 4) (start + 5)), Aexpr, intValueAnnot] v]))
              (Expr [] (Ewseq CorpusE0.wc
                (Expr [Astd "§6.5.16.1#2, store"]
                  (Eaction (Paction polarity.Neg0 (Action (locP start (start + 5) (start + 2))
                    empty_annotation (Store0 false (tyPe rTy) (assignmentPtr n) (assignmentConv m) NA)))))
                (pure (assignmentConv m))))))) unitExpr)) unitExpr)
def ifStmt : CoreExpr :=
  letS [Aloc (loc 36 73), Astmt] (tmp 27) intBty cond
    (letS [] (tmp 26) BTy_boolean boolExpr
      (Expr [] (Eif (psym (tmp 26)) (assignBlock 49 40 41 1) (assignBlock 65 42 43 0))))
def kill (atLoc : CerbLocation.Loc) (ty : ctype) (x : sym) : CoreExpr :=
  act atLoc (Kill (Static0 ty) (psym x))
def returnStmt : CoreExpr :=
  letS [Aloc (loc 74 83), Astmt] (tmp 45) intBty (bnd (load rTy rSym 44 81 82))
    (seqE (kill (loc 74 83) xTy xSym)
      (seqE (kill (loc 74 83) rTy rSym)
        (Expr [] (Erun empty_annotation retSym [convLoaded [] retTy (tmp 45)]))))
def cleanup : CoreExpr :=
  seqE (kill (locR 16 85 22 23) xTy xSym)
    (seqE (kill (locR 16 85 33 34) rTy rSym) unitExpr)
def block : CoreExpr :=
  letS [Aloc (loc 16 85), Astmt] xSym ptrBty createX
    (letS [] rSym ptrBty createR
      (seqE initializeX (seqE initializeR (seqE ifStmt (seqE returnStmt cleanup)))))
def returnSave : CoreExpr :=
  Expr [Alabel LAreturn, Aloc (locR 1 85 5 9)]
    (Esave (retSym, intBty) [(tmp 46, ((intBty, some (retTy, By_value)), specInt 0))]
      (pure (psym (tmp 46))))

/-- Equality to the captured body retains every annotation and initializer. -/
theorem mainBody_shape : mainBody = seqE block returnSave := rfl


theorem load_frag (ty : ctype) (x : sym) (n c1 c2 : Nat) : Frag (load ty x n c1 c2) :=
  .wseq_sym (Frag.of_pePure _ (.sym _ _))
    (.load_op rfl (.sym [] _))

theorem gt_frag : Frag gt := by
  refine .wseq_tuple (ls := [([], some (tmp 35), intBty), ([], some (tmp 36), intBty)]) ?_ ?_
  · refine .unseq (by simp) rfl ?_
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (load_frag) xTy xSym 34 40 41
    · obtain rfl := List.mem_singleton.mp he
      exact .val_pure _
  · refine .case_op rfl (PePure.of_isPePure rfl) ?_ ?_ ?_
    · intro q hq
      simp only [gtPats, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        exact Frag.of_pePure _ (PePure.of_isPePure rfl)
    · intro v e' hsel
      obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
      simp only [gtPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl)
    · exact case_hbsz_of_branches

theorem cond_frag : Frag cond := by
  refine .bound (.wseq_tuple
    (ls := [([], some (tmp 29), intBty), ([], some (tmp 30), intBty)]) ?_ ?_)
  · refine .unseq (by simp) rfl ?_
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (gt_frag)
    · obtain rfl := List.mem_singleton.mp he
      exact .val_pure _
  · exact Frag.of_pePure _ (PePure.of_isPePure rfl)

theorem boolExpr_frag : Frag boolExpr := by
  refine .case_op rfl (PePure.of_isPePure rfl) ?_ ?_ ?_
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
    · have he (bs : List (sym × value)) : substFold (Expr [] (End [pure (Pexpr [] () (PEval Vtrue)),
          pure (Pexpr [] () (PEval Vfalse))])) bs =
          Expr [] (End [pure (Pexpr [] () (PEval Vtrue)),
            pure (Pexpr [] () (PEval Vfalse))]) := by
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

theorem assignBlock_frag (start n m : Nat) (v : Int) : Frag (assignBlock start n m v) := by
  refine .sseq (.sseq (.bound (.wseq_tuple
    (ls := [([], some (tmp n), ptrBty), ([], some (tmp m), intBty)]) ?_ ?_)) (.val_pure _)) (.val_pure _)
  · refine .unseq (by simp) rfl ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Frag.of_pePure _ (.sym _ _)
    · exact .val_pure _
  · refine .wseq ?_ ?_
    · exact .neg_store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)


theorem createX_frag : Frag createX :=
  .create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
theorem createR_frag : Frag createR :=
  .create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
theorem initializeX_frag : Frag initializeX :=
  .sseq_sym (.bound (.val_pure _)) (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl))
theorem initializeR_frag : Frag initializeR :=
  .store_op rfl (.sym _ _) (PePure.of_isPePure rfl)
theorem ifStmt_frag : Frag ifStmt :=
  .sseq_sym cond_frag (.sseq_sym boolExpr_frag
    (.if_ (.sym _ _) (assignBlock_frag 49 40 41 1) (assignBlock_frag 65 42 43 0)))
theorem kill_frag (atLoc : CerbLocation.Loc) (ty : ctype) (s : sym) :
    Frag (kill atLoc ty s) := .kill_op rfl (.sym [] s)
theorem returnStmt_frag : Frag returnStmt :=
  .sseq_sym (.bound (load_frag _ _ _ _ _))
    (.sseq (kill_frag _ _ _) (.sseq (kill_frag _ _ _)
      (.run (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact PePure.of_isPePure rfl))))
theorem cleanup_frag : Frag cleanup :=
  .sseq (kill_frag _ _ _) (.sseq (kill_frag _ _ _) (.val_pure Vunit))
theorem returnSave_frag : Frag returnSave :=
  .save (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact CorpusE0.specInt_pePure 0)
    (.pure_op rfl (.sym [] (tmp 46)))
/-- Membership covers both assignment branches, unspecified cases and dead cleanup. -/
theorem mainBody_frag : Frag mainBody := by
  rw [mainBody_shape]
  exact .sseq (.sseq_sym createX_frag (.sseq_sym createR_frag
    (.sseq initializeX_frag (.sseq initializeR_frag (.sseq ifStmt_frag
      (.sseq returnStmt_frag cleanup_frag)))))) returnSave_frag
/-- The operand evaluator bound remains distinct from syntactic membership. -/
theorem mainBody_evalDepth : evalDepth mainBody ≤ 40 := Nat.le_of_ble_eq_true rfl

end CerberusHeapLang.CorpusA7.T5
