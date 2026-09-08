/- Public-rule proof and complete-file production execution for actual t1.
   File quotation, supply and comparator checks remain the explicit boundary. -/
import CerberusHeapLang.Examples.EmittedT1
import CerberusHeapLang.Examples.EmittedInt
import CerberusHeapLang.ProdEntry

set_option autoImplicit false
namespace CerberusHeapLang.CorpusA7.T1
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (psym seqE letS letW bnd act)
open EmittedStdCore (sintTyAnn HasIntLibrary)
variable {GF : BundledGFunctors}

abbrev a25 : sym := tmp 25
abbrev a26 : sym := tmp 26
abbrev a27 : sym := tmp 27
abbrev a28 : sym := tmp 28
abbrev a29 : sym := tmp 29
abbrev a30 : sym := tmp 30
abbrev a32 : sym := tmp 32
abbrev a33 : sym := tmp 33
abbrev a34 : sym := tmp 34
abbrev a35 : sym := tmp 35

abbrev frX (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd xSym (Vobject (OVpointer px)) f
abbrev frY (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd ySym (Vobject (OVpointer py)) (frX px f)
abbrev fr25 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a25 (lint 3) (frY px py f)
abbrev fr32 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a32 (Vobject (OVpointer px)) (fr25 px py f)
abbrev frB (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a27 (lint 3) (envAdd a28 (lint 1) (fr32 px py f))
abbrev fr26 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a26 (lint 4) (frB px py f)
abbrev fr33 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a33 (Vobject (OVpointer py)) (fr26 px py f)
abbrev fr34 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a34 (lint 4) (fr33 px py f)

section Frames
variable {f : Fmap sym value} (hf : SymFrame f) (px py : CerbMem.PointerValue)
include hf

theorem frX_sf : SymFrame (frX px f) := hf.add _ _
theorem frY_sf : SymFrame (frY px py f) := (frX_sf hf px).add _ _
theorem fr25_sf : SymFrame (fr25 px py f) := (frY_sf hf px py).add _ _
theorem fr32_sf : SymFrame (fr32 px py f) := (fr25_sf hf px py).add _ _
theorem frB_sf : SymFrame (frB px py f) := ((fr32_sf hf px py).add _ _).add _ _
theorem fr26_sf : SymFrame (fr26 px py f) := (frB_sf hf px py).add _ _
theorem fr33_sf : SymFrame (fr33 px py f) := (fr26_sf hf px py).add _ _
theorem fr34_sf : SymFrame (fr34 px py f) := (fr33_sf hf px py).add _ _

theorem frX_lookup_x : fmapLookupBy symCmpK xSym (frX px f) = some (Vobject (OVpointer px)) := by
  unfold frX
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]
theorem frY_lookup_x : fmapLookupBy symCmpK xSym (frY px py f) = some (Vobject (OVpointer px)) := by
  unfold frY
  rw [envAdd_lookup (frX_sf hf px) symCmpK, if_neg (by decide +kernel), frX_lookup_x hf px]
theorem frY_lookup_y : fmapLookupBy symCmpK ySym (frY px py f) = some (Vobject (OVpointer py)) := by
  unfold frY
  rw [envAdd_lookup (frX_sf hf px) symCmpK, if_pos (by decide +kernel)]
theorem fr25_lookup_x : fmapLookupBy symCmpK xSym (fr25 px py f) = some (Vobject (OVpointer px)) := by
  unfold fr25
  rw [envAdd_lookup (frY_sf hf px py) symCmpK, if_neg (by decide +kernel), frY_lookup_x hf px py]
theorem fr25_lookup_a25 : fmapLookupBy symCmpK a25 (fr25 px py f) = some (lint 3) := by
  unfold fr25
  rw [envAdd_lookup (frY_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem fr32_lookup_a32 : fmapLookupBy symCmpK a32 (fr32 px py f) = some (Vobject (OVpointer px)) := by
  unfold fr32
  rw [envAdd_lookup (fr25_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem frB_lookup_a27 : fmapLookupBy symCmpK a27 (frB px py f) = some (lint 3) := by
  unfold frB
  rw [envAdd_lookup ((fr32_sf hf px py).add _ _) symCmpK, if_pos (by decide +kernel)]
theorem frB_lookup_a28 : fmapLookupBy symCmpK a28 (frB px py f) = some (lint 1) := by
  unfold frB
  rw [envAdd_lookup ((fr32_sf hf px py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (fr32_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem fr26_lookup_a26 : fmapLookupBy symCmpK a26 (fr26 px py f) = some (lint 4) := by
  unfold fr26
  rw [envAdd_lookup (frB_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem fr26_lookup_y : fmapLookupBy symCmpK ySym (fr26 px py f) = some (Vobject (OVpointer py)) := by
  unfold fr26 frB fr32 fr25
  rw [envAdd_lookup (frB_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup ((fr32_sf hf px py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (fr32_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (fr25_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frY_sf hf px py) symCmpK, if_neg (by decide +kernel), frY_lookup_y hf px py]
theorem fr33_lookup_a33 : fmapLookupBy symCmpK a33 (fr33 px py f) = some (Vobject (OVpointer py)) := by
  unfold fr33
  rw [envAdd_lookup (fr26_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem fr34_lookup_a34 : fmapLookupBy symCmpK a34 (fr34 px py f) = some (lint 4) := by
  unfold fr34
  rw [envAdd_lookup (fr33_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem fr34_lookup_x : fmapLookupBy symCmpK xSym (fr34 px py f) = some (Vobject (OVpointer px)) := by
  unfold fr34 fr33 fr26 frB fr32
  rw [envAdd_lookup (fr33_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (fr26_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (frB_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup ((fr32_sf hf px py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (fr32_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (fr25_sf hf px py) symCmpK, if_neg (by decide +kernel), fr25_lookup_x hf px py]
theorem fr34_lookup_y : fmapLookupBy symCmpK ySym (fr34 px py f) = some (Vobject (OVpointer py)) := by
  unfold fr34 fr33
  rw [envAdd_lookup (fr33_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (fr26_sf hf px py) symCmpK, if_neg (by decide +kernel), fr26_lookup_y hf px py]

end Frames

def returnQ : LabelMap :=
  fmapAddBy symCmpL retSym ([(a35, intBty)], Expr [] (Epure (psym a35))) fmapEmpty

/-- The shipped save collector returns exactly the continuation used by
the actual body's public proof, retaining the emitted grouping and metadata. -/
theorem mainBody_saves : collect_saves mainBody = returnQ := rfl

theorem returnQ_lookup :
    lookupLabel returnQ retSym = some ([(a35, intBty)], Expr [] (Epure (psym a35))) := by
  unfold lookupLabel returnQ
  rw [fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

theorem returnQ_inv {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel returnQ l = some (params, cont)) :
    params = [(a35, intBty)] ∧ cont = Expr [] (Epure (psym a35)) := by
  unfold lookupLabel returnQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem returnQ_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs [(a35, intBty)] [v] (f :: rest) = envAdd a35 v f :: rest := by
  show update_env (mk_sym_pat a35 intBty) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem fr35_lookup {f : Fmap sym value} (hf : SymFrame f) (v : value) :
    fmapLookupBy symCmpK a35 (envAdd a35 v f) = some v := by
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

def returnSpec (GF : BundledGFunctors) [SpikeGS .hasLC GF] : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜symOrd l retSym = .eq ∧ m = 2 ∧ vs = [lint 4] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝)

/-- The post: the delivered value is `Specified(4)`. -/
def resultPost : value → Mem → Prop := fun v _ => v = lint 4

theorem returnSpec_readout [LemFuel] [SpikeGS .hasLC GF] :
    ∀ w ρ', iprop(⌜w = SpikeVal.pure (lint 4)⌝) ⊢ readoutPost (GF := GF) resultPost w ρ' := by
  intro w ρ'
  iintro %hw
  iintro %σ' %ns %κs %nt -
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  subst hw
  rfl

/-- Symbol evaluation uses the engine's key equality, retaining descriptive
metadata and the actual external map. -/
theorem symbol_eval [LemFuel] {M : MachineCtx}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    {x : sym} {f : Fmap sym value} {v : value} (hf : SymFrame f)
    (rest : EnvStack) (hl : fmapLookupBy symCmpK x f = some v) :
    evalPexpr M.tagDefs M.extern M.file (f :: rest) (psym x) = some v :=
  evalPexpr_sym_of_compare M.tagDefs hf rest [] (hex x) hl

theorem returnSpec_valid [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (hQ : M.labelsAt p = returnQ) :
    ⊢ blockSpecsT (GF := GF) M p (returnSpec GF) emptyProcSpecT (readoutPost resultPost) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [hQ] at hl
  obtain ⟨rfl, rfl⟩ := returnQ_inv hl
  dsimp only [returnSpec]
  iintro %hpure
  obtain ⟨-, rfl, rfl, f, rest, hρ, hf⟩ := hpure
  cases hρ
  rw [returnQ_bindArgs]
  iapply wpt_pure (psym a35) _ (Nat.le_refl 2) rfl
    (symbol_eval hex (hf.add _ _) _ (fr35_lookup hf (lint 4)))
  iapply returnSpec_readout
  ipureintro
  rfl


/- Memory witnesses for this client; no dependency on the older wrapper
   exhibits (which also happen to store 3 and 4). -/
private def threeMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 3)
private def t1FourMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 4)
private abbrev threeBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] threeMval).2
private abbrev fourBytesT1 (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] t1FourMval).2
private theorem three_fromMemValue : (valueFromMemValue threeMval).2 = lint 3 := rfl
private theorem t1_four_fromMemValue : (valueFromMemValue t1FourMval).2 = lint 4 := rfl

theorem int_size (ta : List annot) {tds : CerbTags.TagDefsMap} :
    CerbMem.sizeofCtype tds (sintTyAnn ta) = 4 := rfl
theorem int_align [LemFuel] (ta : List annot) {tds : CerbTags.TagDefsMap} :
    CerbMem.alignofIval tds (sintTyAnn ta) = .IV .Prov_none 4 := rfl
theorem int_nonatomic (ta : List annot) : atomicTy (sintTyAnn ta) = false := rfl
theorem int_size_pos (ta : List annot) {tds : CerbTags.TagDefsMap} :
    0 < CerbMem.sizeofCtype tds (sintTyAnn ta) := by rw [int_size]; decide
theorem int_decIndep (ta : List annot) {tds : CerbTags.TagDefsMap}
    (a : Int) (bs : List CerbMem.AbsByte) : decIndep tds a (sintTyAnn ta) bs := fun _ _ => rfl

theorem int_three_storable (tds : CerbTags.TagDefsMap) (ta : List annot) :
    StorableAt tds (sintTyAnn ta) threeMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
theorem int_four_storable (tds : CerbTags.TagDefsMap) (ta : List annot) :
    StorableAt tds (sintTyAnn ta) t1FourMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
theorem int_three_encodes [LemFuel] (tds : CerbTags.TagDefsMap) (ta : List annot) :
    memValueFromValue tds (Ctype [] (unatomic_ (sintTyAnn ta))) (lint 3) = some threeMval := rfl
theorem int_four_encodes [LemFuel] (tds : CerbTags.TagDefsMap) (ta : List annot) :
    memValueFromValue tds (Ctype [] (unatomic_ (sintTyAnn ta))) (lint 4) = some t1FourMval := rfl

theorem int_three_reconstruct (ta : List annot) {tds : CerbTags.TagDefsMap}
    (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (a : Int) :
    CerbMem.reconstructValue tds lum fpm (a + ((0 : Nat) : Int)) (sintTyAnn ta)
      (((threeBytes tds).drop 0).take (CerbMem.sizeofCtype tds (sintTyAnn ta))) = threeMval := by
  rw [show a + ((0 : Nat) : Int) = a by omega]
  rfl
theorem int_four_reconstruct (ta : List annot) {tds : CerbTags.TagDefsMap}
    (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (a : Int) :
    CerbMem.reconstructValue tds lum fpm (a + ((0 : Nat) : Int)) (sintTyAnn ta)
      (((fourBytesT1 tds).drop 0).take (CerbMem.sizeofCtype tds (sintTyAnn ta))) = t1FourMval := by
  rw [show a + ((0 : Nat) : Int) = a by omega]
  rfl
theorem int_three_loadTrap (ta : List annot) : loadTrapV (sintTyAnn ta) threeMval = false := rfl
theorem int_four_loadTrap (ta : List annot) : loadTrapV (sintTyAnn ta) t1FourMval = false := rfl

section Operands
variable [LemFuel] {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
  {f : file core_run_annotation} {ρ : EnvStack}

theorem convLoaded_eval (h : HasIntLibrary f) {ta : List annot} {s : sym} {n : Int}
    (hv : evalPexpr tds ext f ρ (psym s) = some (lint n))
    (hlo : -2147483648 ≤ n) (hhi : n ≤ 2147483647) :
    evalPexpr tds ext f ρ (convLoaded (sintTyAnn ta) s) = some (lint n) :=
  EmittedStdCore.eval_convLoadedInt_spec [] h (by unfold tyPe; rw [evalPexpr_val]) hv hlo hhi

theorem alignPe_eval (ty : ctype) :
    evalPexpr tds ext f ρ (Pexpr [] () (PEctor Civalignof [tyPe ty])) =
      some (Vobject (OVinteger (CerbMem.alignofIval tds ty))) := by
  simp only [tyPe, evalPexpr_tyctor, evalTyCtor_alignof, isTyCtor]

omit [LemFuel] in
theorem add_select :
    select_case subst_sym_pexpr (Vtuple [lint 3, lint 1]) addAlts =
      some (addBranch (ointPe 3) (ointPe 1)) := rfl

theorem addBranch_eval :
    evalPexpr tds ext f ρ (addBranch (ointPe 3) (ointPe 1)) = some (lint 4) := by
  unfold addBranch
  rw [evalPexpr_ctor1,
    evalPexpr_catch_add_int [Astd "§6.5.6#5"]
      (evalPexpr_conv_int_int [Astd "§6.5.6#4"] (by rw [ointPe, evalPexpr_val]) (by decide) (by decide))
      (evalPexpr_conv_int_int [Astd "§6.5.6#4"] (by rw [ointPe, evalPexpr_val]) (by decide) (by decide))
      (by decide) (by decide)]
  rfl

theorem addPe_eval
    (hv1 : evalPexpr tds ext f ρ (psym a27) = some (lint 3))
    (hv2 : evalPexpr tds ext f ρ (psym a28) = some (lint 1)) :
    evalPexpr tds ext f ρ addPe = some (lint 4) := by
  unfold addPe
  rw [evalPexpr_case, if_pos (show isPePureAlts addAlts = true from rfl), evalPexpr_ctor2, hv1, hv2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [show evalCtor tds Ctuple [lint 3, lint 1] = some (Vtuple [lint 3, lint 1]) from rfl]
  simp only [Option.bind_some]
  rw [add_select]
  simp only [Option.bind_some]
  rw [if_pos (show peDepth (reannot0 (addBranch (ointPe 3) (ointPe 1))) ≤ peDepthAlts addAlts
    from Nat.le_refl _), evalPexpr_reannot0]
  exact addBranch_eval

end Operands


def oneA : SpikeValA := .pure [Aloc (loc 41 42), Aexpr, intValueAnnot] [] (lint 1)
theorem one_eq : one = ofValA oneA := rfl

theorem createX_eq : createX = createOpRedex [] (locR 16 55 22 23) empty_annotation
    (Pexpr [] () (PEctor Civalignof [tyPe xTy])) (tyPe xTy)
    (PrefSource (loc 22 23) [mainSym, xSym]) := rfl
theorem createY_eq : createY = createOpRedex [] (locR 16 55 33 34) empty_annotation
    (Pexpr [] () (PEctor Civalignof [tyPe yTy])) (tyPe yTy)
    (PrefSource (loc 33 34) [mainSym, ySym]) := rfl
theorem store_eq (atLoc : CerbLocation.Loc) (ty : ctype) (p v : generic_pexpr Unit sym) :
    act atLoc (Store0 false (tyPe ty) p v NA) = storeOpRedex [] atLoc empty_annotation ty p v NA := rfl
theorem load_eq (atLoc : CerbLocation.Loc) (ty : ctype) (p : generic_pexpr Unit sym) :
    act atLoc (Load0 (tyPe ty) p NA) = loadOpRedex [] atLoc empty_annotation ty p NA := rfl
theorem kill_eq (atLoc : CerbLocation.Loc) (ty : ctype) (s : sym) :
    kill atLoc ty s = killOpRedex [] atLoc empty_annotation (Static0 ty) (psym s) := rfl

/-- The actual emitted main satisfies the total logic contract. The
allocation budget retains both annotated cell types; 48 is sufficient. -/
theorem mainBody_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : HasIntLibrary M.file)
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ) (hQ : M.labelsAt p = returnQ)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs xTy 4 + allocCost M.tagDefs yTy 4)) ⊢
      wpt M p (returnSpec GF) emptyProcSpecT 48 (readoutPost resultPost) mainBody (ev0 :: evs) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapX, HcapY⟩
  rw [mainBody_shape]
  unfold seqE CorpusE0.wc
  iapply wpt_seq _ _ _ _ _ _ _ 48 0
  simp only [block, initializeX, initializeY, returnStmt, cleanup, sum,
    letS, seqE, CorpusE0.wc, bnd, createX_eq, createY_eq, kill_eq, store_eq]
  rw [show (Pattern [] (CaseBase (some xSym, ptrBty)) : pattern) = symPat [] xSym ptrBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 45
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [(tyPe xTy)])) (tyPe xTy) (PrefSource (loc 22 23) [mainSym, xSym])
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs xTy) (ty := xTy) rfl
    (alignPe_eval xTy) (evalPexpr_val _ _ _ _ _)
  rw [show CerbMem.alignofIval M.tagDefs xTy = .IV .Prov_none 4 from rfl]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 xTy (PrefSource (loc 22 23) [mainSym, xSym])
    (ev0 :: evs) (Nat.le_refl 2) (int_size_pos [Aloc (loc 18 21)]) (int_nonatomic [Aloc (loc 18 21)]) (fun a => int_decIndep [Aloc (loc 18 21)] a _)
  isplitl [HcapX]
  · iexact HcapX
  iintro %px ⟨HptX, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym xSym ptrBty]
  rw [show (Pattern [] (CaseBase (some ySym, ptrBty)) : pattern) = symPat [] ySym ptrBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 42
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [(tyPe yTy)])) (tyPe yTy) (PrefSource (loc 33 34) [mainSym, ySym])
    _ (align := CerbMem.alignofIval M.tagDefs yTy) (ty := yTy) rfl
    (alignPe_eval yTy) (evalPexpr_val _ _ _ _ _)
  rw [show CerbMem.alignofIval M.tagDefs yTy = .IV .Prov_none 4 from rfl]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 yTy (PrefSource (loc 33 34) [mainSym, ySym])
    _ (Nat.le_refl 2) (int_size_pos [Aloc (loc 29 32)]) (int_nonatomic [Aloc (loc 29 32)]) (fun a => int_decIndep [Aloc (loc 29 32)] a _)
  isplitl [HcapY]
  · iexact HcapY
  iintro %py ⟨HptY, -⟩
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym ySym ptrBty]
  iapply wpt_seq _ _ _ _ _ _ _ 7 35
  rw [show (Pattern [] (CaseBase (some a25, intBty)) : pattern) = symPat [] a25 intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 4
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  rw [show intLiteral [Aloc (loc 26 27), Aexpr, intValueAnnot] 3 =
    ofValA (.pure [Aloc (loc 26 27), Aexpr, intValueAnnot] [] (lint 3)) from rfl]
  iapply wpt_ofValA (.pure [Aloc (loc 26 27), Aexpr, intValueAnnot] [] (lint 3)) _ (by decide)
  simp only [SpikeVal.val]
  iexists (lint 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a25 intBty]
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ empty_annotation xTy (psym xSym) (convLoaded xTy a25) NA _ rfl
    (pv := px) (cv := lint 3)
    (symbol_eval hex (fr25_sf hf px py) evs (fr25_lookup_x hf px py))
    (convLoaded_eval hstd (symbol_eval hex (fr25_sf hf px py) evs (fr25_lookup_a25 hf px py)) (by decide) (by decide))
  iapply wpt_store _ _ empty_annotation xTy px (lint 3) NA threeMval
    (List.replicate (CerbMem.sizeofCtype M.tagDefs xTy) undefByte) _ (Nat.le_refl 3)
    (int_three_encodes M.tagDefs [Aloc (loc 18 21)]) (int_three_storable M.tagDefs [Aloc (loc 18 21)])
  isplitl [HptX]
  · iexact HptX
  iintro %fp1 HptX
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 19 16
  rw [show (Pattern [] (CaseBase (some a26, intBty)) : pattern) = symPat [] a26 intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 15 4
  rw [show (15 : Nat) = 14 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  rw [show (Pattern [] (CaseCtor Ctuple [Pattern [] (CaseBase (some a27, intBty)),
      Pattern [] (CaseBase (some a28, intBty))]) : pattern) =
    tuplePat [] [([], some a27, intBty), ([], some a28, intBty)] from rfl]
  iapply wpt_wseq_tuple_annot _ [] [([], some a27, intBty), ([], some a28, intBty)]
    _ _ _ _ 11 3
  rw [show ([loadX, one] : List CoreExpr) = [] ++ loadX :: [one] from rfl]
  iapply wpt_unseq_focus [] [] loadX [one] _ rfl rfl 6 5
  unfold loadX letW
  rw [load_eq]
  rw [show (Pattern [] (CaseBase (some a32, ptrBty)) : pattern) = symPat [] a32 ptrBty from rfl]
  iapply wpt_wseq_sym _ _ _ _ _ _ _ _ 2 4
  iapply wpt_pure (psym xSym) _ (Nat.le_refl 2) rfl (symbol_eval hex (fr25_sf hf px py) evs (fr25_lookup_x hf px py))
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a32 ptrBty]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ HptX
    with ⟨%idx, %adx, %hpvx, HcellX⟩
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval _ _ empty_annotation xTy (psym a32) NA _ rfl (pv := px)
    (symbol_eval hex (fr32_sf hf px py) evs (fr32_lookup_a32 hf px py))
  rw [hpvx, show (cellPtr idx adx) = cellPtr idx (adx + ((0 : Nat) : Int))
    from congrArg (cellPtr idx) (by omega)]
  iapply wpt_load_cell_at _ _ empty_annotation idx adx xTy 0 xTy NA
    (.own 1) (threeBytes M.tagDefs) _ (mv := threeMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => int_three_reconstruct [Aloc (loc 18 21)] lum fpm _) (int_three_loadTrap [Aloc (loc 18 21)])
  isplitl [HcellX]
  · iexact HcellX
  iintro %fp2 HcellX
  simp only [SpikeVal.val]
  rw [three_fromMemValue,
    show cellPtr idx (adx + ((0 : Nat) : Int)) = cellPtr idx adx from congrArg (cellPtr idx) (by omega), ← hpvx]
  iintro %wa' %hwa'
  cases wa' with
  | pure _ _ _ => cases hwa'
  | annot aA' aA2' bA' dsA' vA' =>
  obtain ⟨rfl, rfl⟩ : dsA' = [DA_pos [] fp2] ∧ vA' = lint 3 := by
    injection hwa' with h1 h2; exact ⟨h1, h2⟩
  rw [one_eq]
  rw [show ([] ++ ofValA (SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3)) ::
      [ofValA (oneA)] : List CoreExpr) =
    [SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3), oneA].map ofValA
    from rfl]
  iapply wpt_unseq_vals [] [SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3),
    oneA] _ (by decide) rfl
  iexists [lint 3, lint 1], [DA_pos [] fp2]
  isplit
  · ipureintro
    rfl
  rw [update_env_tuple2_mixed a27 a28 intBty intBty, show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_annot
  iapply wpt_pure addPe _ (Nat.le_refl 2) rfl
    (addPe_eval (symbol_eval hex (frB_sf hf px py) evs (frB_lookup_a27 hf px py))
      (symbol_eval hex (frB_sf hf px py) evs (frB_lookup_a28 hf px py)))
  simp only [SpikeVal.merge]
  iexists (lint 4)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a26 intBty]
  iapply wpt_store_eval _ _ empty_annotation yTy (psym ySym) (convLoaded yTy a26) NA _ rfl
    (pv := py) (cv := lint 4)
    (symbol_eval hex (fr26_sf hf px py) evs (fr26_lookup_y hf px py))
    (convLoaded_eval hstd (symbol_eval hex (fr26_sf hf px py) evs (fr26_lookup_a26 hf px py)) (by decide) (by decide))
  iapply wpt_store _ _ empty_annotation yTy py (lint 4) NA t1FourMval
    (List.replicate (CerbMem.sizeofCtype M.tagDefs yTy) undefByte) _ (Nat.le_refl 3)
    (int_four_encodes M.tagDefs [Aloc (loc 29 32)]) (int_four_storable M.tagDefs [Aloc (loc 29 32)])
  isplitl [HptY]
  · iexact HptY
  iintro %fp3 HptY
  simp only [SpikeVal.mergeInto]
  iapply wpt_seq _ _ _ _ _ _ _ 16 0
  rw [show (Pattern [] (CaseBase (some a34, intBty)) : pattern) = symPat [] a34 intBty from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 9
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  unfold loadY letW
  rw [load_eq]
  rw [show (Pattern [] (CaseBase (some a33, ptrBty)) : pattern) = symPat [] a33 ptrBty from rfl]
  iapply wpt_wseq_sym _ _ _ _ _ _ _ _ 2 4
  iapply wpt_pure (psym ySym) _ (Nat.le_refl 2) rfl (symbol_eval hex (fr26_sf hf px py) evs (fr26_lookup_y hf px py))
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a33 ptrBty]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ HptY
    with ⟨%idy, %ady, %hpvy, HcellY⟩
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval _ _ empty_annotation yTy (psym a33) NA _ rfl (pv := py)
    (symbol_eval hex (fr33_sf hf px py) evs (fr33_lookup_a33 hf px py))
  rw [hpvy, show (cellPtr idy ady) = cellPtr idy (ady + ((0 : Nat) : Int))
    from congrArg (cellPtr idy) (by omega)]
  iapply wpt_load_cell_at _ _ empty_annotation idy ady yTy 0 yTy NA
    (.own 1) (fourBytesT1 M.tagDefs) _ (mv := t1FourMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => int_four_reconstruct [Aloc (loc 29 32)] lum fpm _) (int_four_loadTrap [Aloc (loc 29 32)])
  isplitl [HcellY]
  · iexact HcellY
  iintro %fp4 HcellY
  simp only [SpikeVal.val]
  rw [t1_four_fromMemValue,
    show cellPtr idy (ady + ((0 : Nat) : Int)) = cellPtr idy ady from congrArg (cellPtr idy) (by omega), ← hpvy]
  iexists (lint 4)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a34 intBty]
  iapply wpt_seq _ _ _ _ _ _ _ 3 6
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ empty_annotation (Static0 xTy) (psym xSym) _ rfl (pv := px)
    (symbol_eval hex (fr34_sf hf px py) evs (fr34_lookup_x hf px py))
  rw [hpvx]
  iapply wpt_kill_emp _ _ empty_annotation (Static0 xTy) (cellPtr idx adx) xTy
    (threeBytes M.tagDefs) _ (Nat.le_refl 2) rfl
  isplitl [HcellX]
  · iapply (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mpr
    iexists idx, adx
    isplit
    · ipureintro
      rfl
    · iexact HcellX
  simp only [SpikeVal.mergeInto]
  rw [← hpvx]
  iapply wpt_seq _ _ _ _ _ _ _ 3 3
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ empty_annotation (Static0 yTy) (psym ySym) _ rfl (pv := py)
    (symbol_eval hex (fr34_sf hf px py) evs (fr34_lookup_y hf px py))
  rw [hpvy]
  iapply wpt_kill_emp _ _ empty_annotation (Static0 yTy) (cellPtr idy ady) yTy
    (fourBytesT1 M.tagDefs) _ (Nat.le_refl 2) rfl
  isplitl [HcellY]
  · iapply (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mpr
    iexists idy, ady
    isplit
    · ipureintro
      rfl
    · iexact HcellY
  simp only [SpikeVal.mergeInto]
  rw [← hpvy]
  iapply wpt_run [] empty_annotation retSym [convLoaded retTy a34] _ _ 2
    (by rw [hQ]; exact returnQ_lookup)
    (by
      have hv : evalPexpr M.tagDefs M.extern M.file (fr34 px py ev0 :: evs)
          (convLoaded retTy a34) = some (lint 4) :=
        convLoaded_eval hstd (ta := [Aloc (loc 1 4)])
          (symbol_eval hex (fr34_sf hf px py) evs (fr34_lookup_a34 hf px py)) (by decide) (by decide)
      rw [evalPexprs_cons, hv, evalPexprs_nil]
      rfl)
    (Nat.le_refl 3)
  dsimp only [returnSpec]
  ipureintro
  exact ⟨by decide +kernel, rfl, rfl, _, _, rfl, fr34_sf hf px py⟩


/-! ## Driver delivery with the actual external map

The actual file and initial run state are retained. Label registration is
derived from the checked file union and the exact save-map proof. The final
theorems compose this delivery with full startup and finalization. -/

def entryRunState (cmp : EmittedFile.Comparators) (sup : Nat) : core_run_state :=
  (initial_core_run_state sup (collect_labeled_continuations_NEW (restoredFile cmp))).1

theorem entryRunState_main (cmp : EmittedFile.Comparators) (sup : Nat)
    (h : labelUnionCheck cmp = true) :
    fmapLookupBy symCmpL mainSym (entryRunState cmp sup).labeled = some returnQ := by
  change fmapLookupBy symCmpL mainSym
    (collect_labeled_continuations_NEW (restoredFile cmp)) = some returnQ
  rw [main_labels_of_check cmp h, mainBody_saves]

def entryCtx (cmp : EmittedFile.Comparators) (sup : Nat) : MachineCtx :=
  { tagDefs := (restoredFile cmp).tagDefs, file := restoredFile cmp,
    extern := runtimeExtern, tid := 0, parent := none, errno := errnoPtr,
    runState := entryRunState cmp sup }

def entryCtl (sup : Nat) : Ctl :=
  ⟨[], some mainSym, ELoc_normal [(mainSym, CerbLocation.other "Driver.drive")],
    CerbLocation.other "Driver.drive", ⟨sup, 0⟩⟩

def entryThread : thread_state :=
  { arena := mainBody, stack0 := Stack_empty, errno := errnoPtr,
    current_loc := CerbLocation.other "Driver.drive",
    exec_loc := ELoc_normal [(mainSym, CerbLocation.other "Driver.drive")],
    env := [fmapEmpty], current_proc_opt := some mainSym }

theorem entryCtx_labels (cmp : EmittedFile.Comparators) (sup : Nat)
    (hQ : fmapLookupBy symCmpL mainSym (entryRunState cmp sup).labeled = some returnQ) :
    (entryCtx cmp sup).labelsAt (entryCtl sup).proc = returnQ := by
  change (match fmapLookupBy symCmpL (resolveExtern runtimeExtern mainSym)
      (entryRunState cmp sup).labeled with
    | some Q => Q
    | none => fmapEmpty) = returnQ
  rw [runtimeExtern_main, hQ]

theorem entry_budget_fits :
    allocCost fmapEmpty xTy 4 + allocCost fmapEmpty yTy 4 ≤
      headroom prodMem₀.lastAddress := by
  exact prod_two_int_budget_fits

/-- The actual main's per-thread driver delivery. The checked library paths
and collector union establish the file premises, including registration;
the environment map is the one produced by actual startup. -/
theorem mainBody_driver_done [LemFuel] (hfuel : 40 ≤ LemFuel.fuel)
    (cmp : EmittedFile.Comparators) (sup : Nat)
    (hstd : EmittedStdCore.intLibraryCheck cmp.stdlib = true)
    (hlabels : labelUnionCheck cmp = true) :
    DriverDoneAtExtern runtimeExtern mainSym returnQ (restoredFile cmp) entryThread
      mainBody [fmapEmpty] (CerbLocation.other "Driver.drive") ⟨sup, 0⟩
      prodMem₀ resultPost 48 := by
  have hlbl := entryCtx_labels cmp sup (entryRunState_main cmp sup hlabels)
  exact wpt_driver_done_alloc_extern (hfuel := by omega) (GF := SpikeGF)
    (M₀ := entryCtx cmp sup) (ctl := entryCtl sup) (th₀ := entryThread)
    (p := mainSym) (Q := returnQ) rfl hlbl rfl rfl rfl rfl (Nat.le_refl _)
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := returnQ_inv hl
      exact .pure_op rfl (.sym [] a35))
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := returnQ_inv hl
      change 1 ≤ LemFuel.fuel
      omega)
    (returnSpec SpikeGF) mainBody fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
    (allocCost fmapEmpty xTy 4 + allocCost fmapEmpty yTy 4) mainBody_frag (Nat.le_trans mainBody_evalDepth hfuel)
    (prodMem₀_launchCoh _ entry_budget_fits) resultPost 48
    (by
      intro inst
      rw [show (entryCtl sup).proc = some mainSym from rfl]
      iintro ⟨-, Hcap⟩
      isplitr [Hcap]
      · iapply returnSpec_valid (M := entryCtx cmp sup) (p := some mainSym) runtimeExtern_compare hlbl
      · have hw := mainBody_wpt (GF := SpikeGF) (M := entryCtx cmp sup)
          (p := some mainSym) (hfuel := by omega)
          (EmittedStdCore.hasIntLibrary_restore cmp hstd) runtimeExtern_compare hlbl
          fmapEmpty [] symFrame_empty
        rw [show (entryCtx cmp sup).tagDefs = fmapEmpty from rfl] at hw
        iapply hw $$ Hcap)

/-- Complete-file execution at the actual frontend supply. The checked
file/library premises feed the public body proof and derived registration;
startup, errno initialization, driver delivery and finalization are composed
over the shipped semantics. -/
theorem certified_production [LemFuel] (hfuel : 50 ≤ LemFuel.fuel)
    (cmp : EmittedFile.Comparators)
    (hstd : EmittedStdCore.intLibraryCheck cmp.stdlib = true)
    (hmain : mainLookupCheck cmp.funs = true)
    (hlabels : labelUnionCheck cmp = true)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive (restoredFile cmp).tagDefs false (restoredFile cmp) args)
          ((initial_driver_state frontendSupply (restoredFile cmp) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 4 ∧
      dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  refine prod_run_eqJ_file (restoredFile cmp) (restoredFile_tagDefs cmp)
    (restoredFile_globs cmp) mainSym (restoredFile_main cmp)
    (locR 1 55 5 9) (some 20) intBty mainBody (restoredFile_mainLookup cmp hmain)
    frontendSupply (Q := returnQ) ?_ resultPost 48 ?_ (by omega) fs args
  · rw [restoredFile_extern, runtimeExtern_main]
    exact entryRunState_main cmp frontendSupply hlabels
  · rw [restoredFile_extern]
    exact mainBody_driver_done (hfuel := by omega) cmp frontendSupply hstd hlabels

/-- Transfer the production equation to the original file and supply when
the retained data and the original comparator checks agree. The executable
frontend comparison tests this connection; it does not discharge these Lean
equality premises or prove correctness of the IO frontend. -/
theorem certified_production_of_capture_eq [LemFuel] (hfuel : 50 ≤ LemFuel.fuel)
    (fallback : EmittedFile.Comparators) (F : file core_run_annotation) (sup : Nat)
    (hdata : EmittedFile.captureData F = data) (hsup : sup = frontendSupply)
    (hstd : EmittedStdCore.intLibraryCheck (EmittedFile.captureComparators fallback F).stdlib = true)
    (hmain : mainLookupCheck (EmittedFile.captureComparators fallback F).funs = true)
    (hlabels : labelUnionCheck (EmittedFile.captureComparators fallback F) = true)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive F.tagDefs false F args) ((initial_driver_state sup F fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 4 ∧
      dres.dres_blocked = false ∧ dres.dres_stdout = "" ∧ dres.dres_stderr = "" := by
  subst sup
  rw [← EmittedFile.restore_eq_of_data_eq fallback F data hdata]
  exact certified_production hfuel (EmittedFile.captureComparators fallback F) hstd hmain hlabels fs args

end CerberusHeapLang.CorpusA7.T1
