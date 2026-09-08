/- Integer-library declarations from the actual emitted-file fixture.
   Proofs use callee lookup facts, not equality with a truncated library.
   EmittedT1Exhibit consumes this support in its complete-file execution proof. -/
import CerberusHeapLang.Examples.EmittedT1Data
import CerberusHeapLang.IntRules

set_option autoImplicit false

namespace CerberusHeapLang.EmittedStdCore

open Lem_List

abbrev StdFun := sym × List (sym × core_base_type) × generic_pexpr Unit sym

/-- Read declaration data without imposing a comparator on the actual file.
The lookup hypotheses below concern the file's real comparator-backed maps. -/
def findStdFun (name : String) : Option StdFun := do
  let tree ← CorpusA7.T1.data.stdlib
  let (key, decl) ← (Pmap.bindings tree).find? fun (key, _) =>
    match key with
    | .Symbol _ _ (.SD_Id text) => text == name
    | _ => false
  match decl with
  | .Fun _ params body => some (key, params, body)
  | _ => none

def isRepr : StdFun := (findStdFun "is_representable_integer").get (by decide)
def convInt : StdFun := (findStdFun "conv_int").get (by decide)
def convLoadedInt : StdFun := (findStdFun "conv_loaded_int").get (by decide)
def wrapI : StdFun := (findStdFun "wrapI").get (by decide)
def nSym : sym := (isRepr.2.1[0]'(by decide)).1
def tySym : sym := (convInt.2.1[0]'(by decide)).1

theorem convInt_params :
    convInt.2.1 = [(tySym, BTy_ctype), (nSym, BTy_object OTy_integer)] := rfl

/-- The finite lookup obligations for the three actual library callees.
Other declarations and the implementation map remain unrestricted. -/
structure HasIntLibrary (f : file core_run_annotation) : Prop where
  isRepr : lookupFun f (Sym isRepr.1) = some isRepr.2
  convInt : lookupFun f (Sym convInt.1) = some convInt.2
  convLoadedInt : lookupFun f (Sym convLoadedInt.1) = some convLoadedInt.2

/-- A reference for finite lookup-path checks, not a replacement for the
comparator captured in the frontend's file. -/
def referenceCmp (a b : sym) : LemOrdering := Lem_Basic_classes.ordCompare a b

theorem referenceLookup_isRepr :
    fmapLookupBy referenceCmp isRepr.1
      (EmittedFile.restoreMap referenceCmp CorpusA7.T1.data.stdlib) =
      some (Fun BTy_boolean isRepr.2.1 isRepr.2.2) := rfl

theorem referenceLookup_convInt :
    fmapLookupBy referenceCmp convInt.1
      (EmittedFile.restoreMap referenceCmp CorpusA7.T1.data.stdlib) =
      some (Fun (BTy_object OTy_integer) convInt.2.1 convInt.2.2) := rfl

theorem referenceLookup_convLoadedInt :
    fmapLookupBy referenceCmp convLoadedInt.1
      (EmittedFile.restoreMap referenceCmp CorpusA7.T1.data.stdlib) =
      some (Fun (BTy_loaded OTy_integer) convLoadedInt.2.1 convLoadedInt.2.2) := rfl

/-- Exactly the three callee paths used by the conversion proofs below.
This executable premise does not compare whole comparator functions. -/
def intLibraryCheck (cmp : sym → sym → LemOrdering) : Bool :=
  EmittedFile.mapLookupCheck cmp referenceCmp isRepr.1 CorpusA7.T1.data.stdlib &&
  EmittedFile.mapLookupCheck cmp referenceCmp convInt.1 CorpusA7.T1.data.stdlib &&
  EmittedFile.mapLookupCheck cmp referenceCmp convLoadedInt.1 CorpusA7.T1.data.stdlib

theorem lookupFun_of_stdlib (f : file core_run_annotation) (fn : StdFun)
    (ty : core_base_type)
    (h : fmapLookupBy referenceCmp fn.1 f.stdlib = some (Fun ty fn.2.1 fn.2.2)) :
    lookupFun f (Sym fn.1) = some fn.2 := by
  unfold referenceCmp at h
  simp only [lookupFun, h]

/-- Passing the finite path check suffices for the actual library contract.
All other file fields remain unrestricted. -/
theorem hasIntLibrary_of_stdlib (f : file core_run_annotation)
    (cmp : sym → sym → LemOrdering)
    (hm : f.stdlib = EmittedFile.restoreMap cmp CorpusA7.T1.data.stdlib)
    (h : intLibraryCheck cmp = true) : HasIntLibrary f := by
  simp only [intLibraryCheck, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  constructor
  · apply lookupFun_of_stdlib _ isRepr BTy_boolean
    rw [hm]
    exact (EmittedFile.restoreMap_lookup_of_check cmp referenceCmp referenceCmp
      isRepr.1 CorpusA7.T1.data.stdlib h1).trans referenceLookup_isRepr
  · apply lookupFun_of_stdlib _ convInt (BTy_object OTy_integer)
    rw [hm]
    exact (EmittedFile.restoreMap_lookup_of_check cmp referenceCmp referenceCmp
      convInt.1 CorpusA7.T1.data.stdlib h2).trans referenceLookup_convInt
  · apply lookupFun_of_stdlib _ convLoadedInt (BTy_loaded OTy_integer)
    rw [hm]
    exact (EmittedFile.restoreMap_lookup_of_check cmp referenceCmp referenceCmp
      convLoadedInt.1 CorpusA7.T1.data.stdlib h3).trans referenceLookup_convLoadedInt

/-- The complete reconstructed file satisfies the contract with its own
eight comparator parameters. -/
theorem hasIntLibrary_restore (cmp : EmittedFile.Comparators)
    (h : intLibraryCheck cmp.stdlib = true) :
    HasIntLibrary (EmittedFile.restore cmp CorpusA7.T1.data) :=
  hasIntLibrary_of_stdlib _ cmp.stdlib rfl h

/-- The same recorded library can serve other emitted program files.
Only library data identity and the captured comparator's paths are needed. -/
theorem hasIntLibrary_of_stdlib_data_eq (f : file core_run_annotation)
    (hd : EmittedFile.mapData f.stdlib = CorpusA7.T1.data.stdlib)
    (hc : intLibraryCheck (EmittedFile.mapComparator referenceCmp f.stdlib) = true) :
    HasIntLibrary f := by
  apply hasIntLibrary_of_stdlib f (EmittedFile.mapComparator referenceCmp f.stdlib) _ hc
  rw [← hd, EmittedFile.restoreMap_capture]

/-- Transfer the contract to an original file when its complete data is
the fixture and its captured standard-library comparator passes the check.
Establishing the data premise for a frontend run is the declared executable
transcription boundary; this theorem does not assert frontend correctness. -/
theorem hasIntLibrary_of_capture_eq (fallback : EmittedFile.Comparators)
    (f : file core_run_annotation)
    (hd : EmittedFile.captureData f = CorpusA7.T1.data)
    (hc : intLibraryCheck (EmittedFile.captureComparators fallback f).stdlib = true) :
    HasIntLibrary f := by
  rw [← EmittedFile.restore_eq_of_data_eq fallback f CorpusA7.T1.data hd]
  exact hasIntLibrary_restore _ hc

/-- A signed C int retaining its emitted type annotations. -/
def sintTyAnn (ta : List annot) : ctype :=
  Ctype ta (.Basic (.Integer (.Signed .Int_)))

def instantiate (fn : StdFun) (values : List value) : generic_pexpr Unit sym :=
  foldl2 (fun body (param : sym × core_base_type) value =>
    subst_sym_pexpr param.1 value body) fn.2.2 fn.2.1 values

def isReprInst (n : Int) (ta : List annot := []) := instantiate isRepr [oint n, Vctype (sintTyAnn ta)]
def convIntInst (n : Int) (ta : List annot := []) := instantiate convInt [Vctype (sintTyAnn ta), oint n]
def convLoadedIntInst (ty : ctype) (v : value) :=
  instantiate convLoadedInt [Vctype ty, v]

theorem callBody_isRepr {f : file core_run_annotation} (h : HasIntLibrary f) (n : Int) (ta : List annot) :
    callBody f (Sym isRepr.1) [oint n, Vctype (sintTyAnn ta)] = some (isReprInst n ta) := by
  unfold callBody
  rw [h.isRepr]
  rfl

theorem callBody_convInt {f : file core_run_annotation} (h : HasIntLibrary f) (n : Int) (ta : List annot) :
    callBody f (Sym convInt.1) [Vctype (sintTyAnn ta), oint n] = some (convIntInst n ta) := by
  unfold callBody
  rw [h.convInt]
  rfl

theorem callBody_convLoadedInt {f : file core_run_annotation} (h : HasIntLibrary f)
    (ty : ctype) (v : value) :
    callBody f (Sym convLoadedInt.1) [Vctype ty, v] = some (convLoadedIntInst ty v) := by
  unfold callBody
  rw [h.convLoadedInt]
  rfl

theorem isRepr_budget : stdBudget (Sym isRepr.1) = 4 := rfl
theorem convInt_budget : stdBudget (Sym convInt.1) = 17 := rfl
theorem convLoadedInt_budget : stdBudget (Sym convLoadedInt.1) = 23 := rfl

theorem isReprInst_depth (n : Int) (ta : List annot) : peDepth (peStrip (isReprInst n ta)) = 4 := rfl
theorem convLoadedIntInst_depth (ty : ctype) (v : value) :
    peDepth (peStrip (convLoadedIntInst ty v)) = 23 := rfl

/-- The location attached to the parsed library's value operands. The
shape equations below tie this spelling to the recorded declarations. -/
def libraryLoc : CerbLocation.Loc :=
  .region ⟨"../.cerberus-ws/runtime/libcore/std.core", 0, 0⟩
    ⟨"../.cerberus-ws/runtime/libcore/std.core", 0, 0⟩ .noCursor
def libPe (node : generic_pexpr_ Unit sym) : generic_pexpr Unit sym :=
  Pexpr [Aloc libraryLoc] () node
def libVal (v : value) := libPe (PEval v)

def isReprEvalBody (n : Int) (ta : List annot := []) : generic_pexpr Unit sym :=
  Pexpr [] () (PEop OpAnd
    (Pexpr [] () (PEop OpLe
      (Pexpr [] () (PEctor Civmin [libVal (Vctype (sintTyAnn ta))])) (ointPe n)))
    (Pexpr [] () (PEop OpLe (ointPe n)
      (Pexpr [] () (PEctor Civmax [libVal (Vctype (sintTyAnn ta))])))))

theorem isReprInst_shape (n : Int) (ta : List annot) : peStrip (isReprInst n ta) = isReprEvalBody n ta := rfl

def convThen (n : Int) : generic_pexpr Unit sym :=
  libPe (PEif (libPe (PEop OpEq (libVal (oint n)) (libVal (oint 0))))
    (libVal (oint 0)) (libVal (oint 1)))
def convElse2 (n : Int) (ta : List annot := []) : generic_pexpr Unit sym :=
  libPe (PEif (libPe (PEis_unsigned (libVal (Vctype (sintTyAnn ta)))))
    (libPe (PEcall (Sym wrapI.1) [libVal (Vctype (sintTyAnn ta)), libVal (oint n)]))
    (libPe (PEcall (Impl Integer__conv_nonrepresentable_signed_integer)
      [libVal (Vctype (sintTyAnn ta)), libVal (oint n)])))
def convElse (n : Int) (ta : List annot := []) : generic_pexpr Unit sym :=
  libPe (PEif (libPe (PEcall (Sym isRepr.1) [libVal (oint n), libVal (Vctype (sintTyAnn ta))]))
    (libVal (oint n)) (convElse2 n ta))
def convEvalBody (n : Int) (ta : List annot := []) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif (libPe (PEop OpEq (libVal (Vctype (sintTyAnn ta))) (libVal (Vctype stdBoolTy))))
    (convThen n) (convElse n ta))

/-- The actual conversion body with its two operands exposed. Keeping the
first substitution separate avoids repeatedly unfolding the complete
fixture while reducing the second substitution. -/
def convBodyWith (tyPe nPe : generic_pexpr Unit sym) : generic_pexpr Unit sym :=
  libPe (PEif (libPe (PEop OpEq tyPe (libVal (Vctype stdBoolTy))))
    (libPe (PEif (libPe (PEop OpEq nPe (libVal (oint 0))))
      (libVal (oint 0)) (libVal (oint 1))))
    (libPe (PEif (libPe (PEcall (Sym isRepr.1) [nPe, tyPe])) nPe
      (libPe (PEif (libPe (PEis_unsigned tyPe))
        (libPe (PEcall (Sym wrapI.1) [tyPe, nPe]))
        (libPe (PEcall (Impl Integer__conv_nonrepresentable_signed_integer) [tyPe, nPe])))))))

def convIntTyped (ta : List annot) : generic_pexpr Unit sym :=
  subst_sym_pexpr tySym (Vctype (sintTyAnn ta)) convInt.2.2

theorem convIntInst_expand (n : Int) (ta : List annot) :
    convIntInst n ta = subst_sym_pexpr nSym (oint n) (convIntTyped ta) := by
  unfold convIntInst instantiate
  rw [convInt_params]
  rfl

theorem convIntTyped_shape (ta : List annot) :
    convIntTyped ta = convBodyWith (libVal (Vctype (sintTyAnn ta))) (libPe (PEsym nSym)) := rfl

theorem convIntInst_shape (n : Int) (ta : List annot) :
    peStrip (convIntInst n ta) = convEvalBody n ta := by
  rw [convIntInst_expand, convIntTyped_shape]
  rfl

theorem convIntInst_depth (n : Int) (ta : List annot) :
    peDepth (peStrip (convIntInst n ta)) = 17 := by
  rw [convIntInst_shape]
  rfl
theorem convBranches_pure (n : Int) (ta : List annot) : (isPePure (convThen n) && isPePure (convElse n ta)) = true := rfl
theorem convElse2_pure (n : Int) (ta : List annot) : isPePure (convElse2 n ta) = true := rfl

def libPat (node : generic_pattern_ sym) : pattern := Pattern [Aloc libraryLoc] node
def cliAlts (ty : ctype) : List (pattern × generic_pexpr Unit sym) :=
  [(libPat (CaseCtor Cspecified [libPat (CaseBase (some nSym, BTy_object OTy_integer))]),
    libPe (PEctor Cspecified
      [libPe (PEcall (Sym convInt.1) [libVal (Vctype ty), libPe (PEsym nSym)])])),
   (libPat (CaseCtor Cunspecified [libPat (CaseBase (none, BTy_ctype))]),
    libPe (PEctor Cunspecified [libVal (Vctype ty)]))]
def convLoadedEvalBody (ty : ctype) (v : value) : generic_pexpr Unit sym :=
  Pexpr [] () (PEcase (Pexpr [] () (PEval v)) (cliAlts ty))

theorem convLoadedIntInst_shape (ty : ctype) (v : value) :
    peStrip (convLoadedIntInst ty v) = convLoadedEvalBody ty v := rfl
theorem cliAlts_pure (ty : ctype) : isPePureAlts (cliAlts ty) = true := rfl

theorem cliAlts_select_spec (ty : ctype) (n : Int) :
    select_case subst_sym_pexpr (lint n) (cliAlts ty) =
      some (libPe (PEctor Cspecified
        [libPe (PEcall (Sym convInt.1) [libVal (Vctype ty), libVal (oint n)])])) := rfl
theorem cliAlts_select_unspec (ty ty' : ctype) :
    select_case subst_sym_pexpr (Vloaded (LVunspecified ty')) (cliAlts ty) =
      some (libPe (PEctor Cunspecified [libVal (Vctype ty)])) := rfl

theorem cliAlts_spec_depth (ty : ctype) (n : Int) :
    peDepth (reannot0 (libPe (PEctor Cspecified
      [libPe (PEcall (Sym convInt.1) [libVal (Vctype ty), libVal (oint n)])]))) ≤
      peDepthAlts (cliAlts ty) := Nat.le_of_eq rfl
theorem cliAlts_unspec_depth (ty : ctype) :
    peDepth (reannot0 (libPe (PEctor Cunspecified [libVal (Vctype ty)]))) ≤
      peDepthAlts (cliAlts ty) := by
  change (2 : Nat) ≤ 21
  decide

section Evaluation
variable [LemFuel] {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
  {f : file core_run_annotation} {ρ : EnvStack} {ta : List annot}

theorem evalCtor_ivmin_int_annot :
    evalCtor tds Civmin [Vctype (sintTyAnn ta)] =
      some (Vobject (OVinteger (CerbMem.minIval (.Signed .Int_)))) := rfl

theorem evalCtor_ivmax_int_annot :
    evalCtor tds Civmax [Vctype (sintTyAnn ta)] =
      some (Vobject (OVinteger (CerbMem.maxIval (.Signed .Int_)))) := rfl

theorem eval_isReprInst (n : Int) (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext f ρ (peStrip (isReprInst n ta)) = some Vtrue := by
  rw [isReprInst_shape]
  unfold isReprEvalBody libVal libPe
  rw [evalPexpr_op, evalPexpr_op, evalPexpr_op, evalPexpr_ctor1, evalPexpr_ctor1,
    ointPe, evalPexpr_val, evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [evalCtor_ivmin_int_annot, evalCtor_ivmax_int_annot]
  simp only [Option.bind_some]
  rw [show evalBinop OpLe (Vobject (OVinteger (CerbMem.minIval (.Signed .Int_)))) (oint n) =
      some (boolValue (decide (-2147483648 ≤ n))) from rfl,
    show evalBinop OpLe (oint n) (Vobject (OVinteger (CerbMem.maxIval (.Signed .Int_)))) =
      some (boolValue (decide (n ≤ 2147483647))) from rfl,
    boolValue_decide_true h1, boolValue_decide_true h2]
  rfl

theorem eval_isRepr_call (a : List annot) (h : HasIntLibrary f)
    {pe1 pe2 : generic_pexpr Unit sym} {n : Int}
    (hv1 : evalPexpr tds ext f ρ pe1 = some (oint n))
    (hv2 : evalPexpr tds ext f ρ pe2 = some (Vctype (sintTyAnn ta)))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext f ρ (Pexpr a () (PEcall (Sym isRepr.1) [pe1, pe2])) = some Vtrue := by
  rw [evalPexpr_call, evalPexprList_cons, hv1, evalPexprList_cons, hv2, evalPexprList_nil]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callBody_isRepr h n ta]
  simp only [Option.bind_some]
  rw [if_pos (by rw [isReprInst_depth, isRepr_budget]; exact Nat.le_refl _)]
  exact eval_isReprInst n h1 h2

theorem eval_libVal (v : value) : evalPexpr tds ext f ρ (libVal v) = some v := by
  unfold libVal libPe
  rw [evalPexpr_val]

theorem eval_convIntInst (h : HasIntLibrary f) (n : Int)
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext f ρ (peStrip (convIntInst n ta)) = some (oint n) := by
  rw [convIntInst_shape]
  unfold convEvalBody
  rw [evalPexpr_if, if_pos (convBranches_pure n ta)]
  unfold libPe
  rw [evalPexpr_op, eval_libVal, eval_libVal]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalBinop OpEq (Vctype (sintTyAnn ta)) (Vctype stdBoolTy) = some Vfalse from rfl]
  simp only [Option.bind_some]
  unfold convElse libPe
  rw [evalPexpr_if, if_pos (show (isPePure (libVal (oint n)) && isPePure (convElse2 n ta)) = true from rfl),
    eval_isRepr_call _ h (eval_libVal _) (eval_libVal _) h1 h2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact eval_libVal _

theorem eval_convInt_call (a : List annot) (h : HasIntLibrary f)
    {pe1 pe2 : generic_pexpr Unit sym} {n : Int}
    (hv1 : evalPexpr tds ext f ρ pe1 = some (Vctype (sintTyAnn ta)))
    (hv2 : evalPexpr tds ext f ρ pe2 = some (oint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext f ρ (Pexpr a () (PEcall (Sym convInt.1) [pe1, pe2])) = some (oint n) := by
  rw [evalPexpr_call, evalPexprList_cons, hv1, evalPexprList_cons, hv2, evalPexprList_nil]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callBody_convInt h n ta]
  simp only [Option.bind_some]
  rw [if_pos (by rw [convIntInst_depth, convInt_budget]; exact Nat.le_refl _)]
  exact eval_convIntInst h n h1 h2

theorem eval_convLoadedInt_spec (a : List annot) (h : HasIntLibrary f)
    {pe1 pe2 : generic_pexpr Unit sym} {n : Int}
    (hv1 : evalPexpr tds ext f ρ pe1 = some (Vctype (sintTyAnn ta)))
    (hv2 : evalPexpr tds ext f ρ pe2 = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext f ρ (Pexpr a () (PEcall (Sym convLoadedInt.1) [pe1, pe2])) =
      some (lint n) := by
  rw [evalPexpr_call, evalPexprList_cons, hv1, evalPexprList_cons, hv2, evalPexprList_nil]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callBody_convLoadedInt h (sintTyAnn ta) (lint n)]
  simp only [Option.bind_some]
  rw [if_pos (by rw [convLoadedIntInst_depth, convLoadedInt_budget]; exact Nat.le_refl _),
    convLoadedIntInst_shape]
  unfold convLoadedEvalBody
  rw [evalPexpr_case, if_pos (cliAlts_pure (sintTyAnn ta)), evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [cliAlts_select_spec]
  simp only [Option.bind_some]
  rw [if_pos (cliAlts_spec_depth _ _), evalPexpr_reannot0]
  unfold libPe
  rw [evalPexpr_ctor1, eval_convInt_call _ h (eval_libVal _) (eval_libVal _) h1 h2]
  rfl

theorem eval_convLoadedInt_unspec (a : List annot) (h : HasIntLibrary f)
    {pe1 pe2 : generic_pexpr Unit sym} {ty ty' : ctype}
    (hv1 : evalPexpr tds ext f ρ pe1 = some (Vctype ty))
    (hv2 : evalPexpr tds ext f ρ pe2 = some (Vloaded (LVunspecified ty'))) :
    evalPexpr tds ext f ρ (Pexpr a () (PEcall (Sym convLoadedInt.1) [pe1, pe2])) =
      some (Vloaded (LVunspecified ty)) := by
  rw [evalPexpr_call, evalPexprList_cons, hv1, evalPexprList_cons, hv2, evalPexprList_nil]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [callBody_convLoadedInt h ty (Vloaded (LVunspecified ty'))]
  simp only [Option.bind_some]
  rw [if_pos (by rw [convLoadedIntInst_depth, convLoadedInt_budget]; exact Nat.le_refl _),
    convLoadedIntInst_shape]
  unfold convLoadedEvalBody
  rw [evalPexpr_case, if_pos (cliAlts_pure ty), evalPexpr_val]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [cliAlts_select_unspec]
  simp only [Option.bind_some]
  rw [if_pos (cliAlts_unspec_depth _), evalPexpr_reannot0]
  unfold libPe
  rw [evalPexpr_ctor1, eval_libVal]
  rfl

end Evaluation

section Rules
open Iris Iris.BI Iris.ProgramLogic
variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
  {M : MachineCtx} {p : Option sym} {ta : List annot}

/-- Conversion through the actual emitted library, partial stratum. -/
theorem wps_conv_loaded_int [LemFuel]
    {Ls : LabelSpec GF} {Θ : ProcSpec GF} {Ψ : SpikeVal → EnvStack → IProp GF}
    (pe1 pe2 : generic_pexpr Unit sym) (ρ : EnvStack) {n : Int}
    (hstd : HasIntLibrary M.file)
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vctype (sintTyAnn ta)))
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    Ψ (.pure (lint n)) ρ ⊢
      wps M p Ls Θ Ψ
        (Expr [] (Epure (Pexpr [] () (PEcall (Sym convLoadedInt.1) [pe1, pe2])))) ρ :=
  wps_pure _ _ rfl (eval_convLoadedInt_spec [] hstd hv1 hv2 h1 h2)

/-- Conversion through the actual emitted library, total stratum. -/
theorem wpt_conv_loaded_int [LemFuel]
    {Ls : LabelSpecT GF} {Θ : ProcSpecT GF} {Ψ : SpikeVal → EnvStack → IProp GF}
    (pe1 pe2 : generic_pexpr Unit sym) (ρ : EnvStack) {n : Int} {k : Nat} (hk : 2 ≤ k)
    (hstd : HasIntLibrary M.file)
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vctype (sintTyAnn ta)))
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    Ψ (.pure (lint n)) ρ ⊢
      wpt M p Ls Θ k Ψ
        (Expr [] (Epure (Pexpr [] () (PEcall (Sym convLoadedInt.1) [pe1, pe2])))) ρ :=
  wpt_pure _ _ hk rfl (eval_convLoadedInt_spec [] hstd hv1 hv2 h1 h2)

end Rules

end CerberusHeapLang.EmittedStdCore
