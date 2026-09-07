/-
CerberusHeapLang.CorpusT1Exhibit — THE FIRST CORPUS PROGRAM, CERTIFIED END TO
END (dialect arc E4, THE FIRST MILESTONE; docs/2026-09-05_e4-notes.md §3).

`docs/corpus-e0/t1.c` is `int main(void) { int x = 3; int y = x + 1; return
y; }`. Its `main`, as the pinned pipeline elaborates it (docs/corpus-e0/t1.core,
every annotation, `bound`, `unseq`, `Specified`, the std.core calls), is the
hand-transcribed `CorpusE0.t1Main` (Examples/CorpusE0.lean). The corpus
skeleton speedbump compares constructor shape with the retained emitted
text; it does not establish full-term or full-file identity. This module
is a client of the logic on that term:
`t1_wps` (partial), `t1_wpt` (total, budget 48) and

  `t1_certified_production`: the shipped pipeline `drive` on the library-
  carrying one-procedure file `prodFileLib stdlibE3 [] t1Main` is EXACTLY
  ONE Active execution delivering `Specified(4)`

with `50 ≤ LemFuel.fuel` at the caller's single instance (public total
cost 48 plus two driver iterations). This revalidates the retained emitted
`main` transcription on the current pin. The constructed file still uses
the three-function library fragment and an empty implementation map;
closing its connection to the actual pipeline file remains A7. E1–E3's
`EmittedAExhibit`/`B`/`C` remain synthetics in the dialect's features. The
chain is the generic route `t1_wpt → wpt_driver_done_alloc →
prod_run_eqJ_lib1`. The `unseq` — the read of `x` beside `Specified(1)` — is
E4's: `wps_unseq_focus`/`wpt_unseq_focus` (the sequential driver's
last-reducible-first order: `pure(Specified(1))` first, then the load) and
`wps_unseq_vals`/`wpt_unseq_vals` (the annotated tuple `{DA_pos fp}(Specified(3),
Specified(1))`, race-free by computation — one annotated component), consumed
by the E2 tuple binder at an annotated head (`wps_wseq_tuple_annot`/`wpt_…`),
the dynamic annotation riding onto the `+` node (`wps_annot`/`wpt_annot`) and
dropped by `bound` (`wps_bound`/`wpt_bound`). The two `int` cells come from
ONE summed allocation budget (`allocBudget_split`, AllocExhibit.lean).

The oracle's own reading of t1.c (`--exec`, recorded verbatim in the E4
record): `Defined {value: "Specified(4)", stdout: "", stderr: "", blocked:
"false"}` — the theorem's readout.

A CLIENT of the logic: it reasons through the public rules only.
-/
import CerberusHeapLang.Examples.CorpusE0
import CerberusHeapLang.Examples.EmittedInt
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.IntRules
import CerberusHeapLang.AllocExhibit
import CerberusHeapLang.EmittedAExhibit
import CerberusHeapLang.EmittedCExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (t1Main t1Reg t1RegP t1RegR a508 a509 a510 a511 a512 a513 a515
  a516 a517 a518 ptrTy intCty psym specInt convLoadedInt act wc seqE letS letW bnd createInt
  killInt t1LoadX t1LoadY t1Spec3 t1Spec1 t1CasePe t1Main_frag)

variable {GF : BundledGFunctors}

/-! ## The program's pure operands -/

/-- t1's `+` node IS the E3 rule's shape at t1's symbols and location. -/
theorem t1CasePe_eq : t1CasePe = cAddPe a510 a511 a512 a513 (t1Reg 36 41) := rfl

-- `specInt_eval`, `t1ConvLoadedInt_eval`, `t1sym_eval`, `createInt_eq`,
-- `act_store_eq` and `act_load_eq` — the evaluator/redex lemmas every
-- emitted-corpus client shares — live in Examples/EmittedInt.lean since the
-- L1 landing (2026-09-07): example support must not import a client.

/-- The selected branch of t1's `+` at `(Specified(3), Specified(1))`. -/
theorem t1_cAdd_select_31 :
    select_case subst_sym_pexpr (Vtuple [lint 3, lint 1]) (cAddPats a512 a513 (t1Reg 36 41)) =
      some (cAddBranch 3 1) := rfl

/-! ## The transcription's action nodes in the rules' redex spellings (`rfl`) -/

-- (`createInt_eq`, `act_store_eq`, `act_load_eq`: Examples/EmittedInt.lean)
theorem killInt_eq (x : sym) :
    killInt x = killOpRedex [] (t1Reg 0 54) empty_annotation (Static0 intTy) (psym x) := rfl

/-! ## The value 4 at the cell (the `three*` lemmas of EmittedCExhibit at 4) -/

def t1FourMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 4)

abbrev fourBytesT1 (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] t1FourMval).2

theorem t1_four_encodes [LemFuel] :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) (lint 4) = some t1FourMval := rfl

theorem t1_four_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy t1FourMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem t1_four_reconstruct {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (a : Int) :
    CerbMem.reconstructValue tds lum fpm (a + ((0 : Nat) : Int)) intTy
      (((fourBytesT1 tds).drop 0).take (CerbMem.sizeofCtype tds intTy)) = t1FourMval := by
  rw [show a + ((0 : Nat) : Int) = a by omega]
  rfl

theorem t1_four_fromMemValue : (valueFromMemValue t1FourMval).2 = lint 4 := rfl

theorem t1_four_loadTrap : loadTrapV intTy t1FourMval = false := rfl

-- (`prod_two_int_budget_fits`, the two `int` cells' summed cold-start budget,
-- shared by every emitted client: Examples/EmittedInt.lean)

/-! ## The environment frames of the run and their lookups

The engine's env is ONE thread-global stack of frames: every `let strong`,
`let weak` — INCLUDING the `let weak a_515 = pure(x)` INSIDE the `unseq`
component — pushes a binding onto the head frame, so the frame after the
`unseq` carries `a_515` beneath the tuple binder's `a_510`, `a_511`. -/

abbrev t1frX (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd CorpusE0.xSym (Vobject (OVpointer px)) f
abbrev t1frY (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd CorpusE0.ySym (Vobject (OVpointer py)) (t1frX px f)
abbrev t1fr508 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a508 (lint 3) (t1frY px py f)
abbrev t1fr515 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a515 (Vobject (OVpointer px)) (t1fr508 px py f)
abbrev t1frB (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a510 (lint 3) (envAdd a511 (lint 1) (t1fr515 px py f))
abbrev t1fr509 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a509 (lint 4) (t1frB px py f)
abbrev t1fr516 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a516 (Vobject (OVpointer py)) (t1fr509 px py f)
abbrev t1fr517 (px py : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd a517 (lint 4) (t1fr516 px py f)

section Frames
variable {f : Fmap sym value} (hf : SymFrame f) (px py : CerbMem.PointerValue)
include hf

theorem t1frX_sf : SymFrame (t1frX px f) := hf.add _ _
theorem t1frY_sf : SymFrame (t1frY px py f) := (t1frX_sf hf px).add _ _
theorem t1fr508_sf : SymFrame (t1fr508 px py f) := (t1frY_sf hf px py).add _ _
theorem t1fr515_sf : SymFrame (t1fr515 px py f) := (t1fr508_sf hf px py).add _ _
theorem t1frB_sf : SymFrame (t1frB px py f) := ((t1fr515_sf hf px py).add _ _).add _ _
theorem t1fr509_sf : SymFrame (t1fr509 px py f) := (t1frB_sf hf px py).add _ _
theorem t1fr516_sf : SymFrame (t1fr516 px py f) := (t1fr509_sf hf px py).add _ _
theorem t1fr517_sf : SymFrame (t1fr517 px py f) := (t1fr516_sf hf px py).add _ _

theorem t1frX_lookup_x : fmapLookupBy symCmpK CorpusE0.xSym (t1frX px f) = some (Vobject (OVpointer px)) := by
  unfold t1frX
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]
theorem t1frY_lookup_x : fmapLookupBy symCmpK CorpusE0.xSym (t1frY px py f) = some (Vobject (OVpointer px)) := by
  unfold t1frY
  rw [envAdd_lookup (t1frX_sf hf px) symCmpK, if_neg (by decide +kernel), t1frX_lookup_x hf px]
theorem t1frY_lookup_y : fmapLookupBy symCmpK CorpusE0.ySym (t1frY px py f) = some (Vobject (OVpointer py)) := by
  unfold t1frY
  rw [envAdd_lookup (t1frX_sf hf px) symCmpK, if_pos (by decide +kernel)]
theorem t1fr508_lookup_x : fmapLookupBy symCmpK CorpusE0.xSym (t1fr508 px py f) = some (Vobject (OVpointer px)) := by
  unfold t1fr508
  rw [envAdd_lookup (t1frY_sf hf px py) symCmpK, if_neg (by decide +kernel), t1frY_lookup_x hf px py]
theorem t1fr508_lookup_a508 : fmapLookupBy symCmpK a508 (t1fr508 px py f) = some (lint 3) := by
  unfold t1fr508
  rw [envAdd_lookup (t1frY_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem t1fr515_lookup_a515 : fmapLookupBy symCmpK a515 (t1fr515 px py f) = some (Vobject (OVpointer px)) := by
  unfold t1fr515
  rw [envAdd_lookup (t1fr508_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem t1frB_lookup_a510 : fmapLookupBy symCmpK a510 (t1frB px py f) = some (lint 3) := by
  unfold t1frB
  rw [envAdd_lookup ((t1fr515_sf hf px py).add _ _) symCmpK, if_pos (by decide +kernel)]
theorem t1frB_lookup_a511 : fmapLookupBy symCmpK a511 (t1frB px py f) = some (lint 1) := by
  unfold t1frB
  rw [envAdd_lookup ((t1fr515_sf hf px py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1fr515_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem t1fr509_lookup_a509 : fmapLookupBy symCmpK a509 (t1fr509 px py f) = some (lint 4) := by
  unfold t1fr509
  rw [envAdd_lookup (t1frB_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem t1fr509_lookup_y : fmapLookupBy symCmpK CorpusE0.ySym (t1fr509 px py f) = some (Vobject (OVpointer py)) := by
  unfold t1fr509 t1frB t1fr515 t1fr508
  rw [envAdd_lookup (t1frB_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup ((t1fr515_sf hf px py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1fr515_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1fr508_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1frY_sf hf px py) symCmpK, if_neg (by decide +kernel), t1frY_lookup_y hf px py]
theorem t1fr516_lookup_a516 : fmapLookupBy symCmpK a516 (t1fr516 px py f) = some (Vobject (OVpointer py)) := by
  unfold t1fr516
  rw [envAdd_lookup (t1fr509_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem t1fr517_lookup_a517 : fmapLookupBy symCmpK a517 (t1fr517 px py f) = some (lint 4) := by
  unfold t1fr517
  rw [envAdd_lookup (t1fr516_sf hf px py) symCmpK, if_pos (by decide +kernel)]
theorem t1fr517_lookup_x : fmapLookupBy symCmpK CorpusE0.xSym (t1fr517 px py f) = some (Vobject (OVpointer px)) := by
  unfold t1fr517 t1fr516 t1fr509 t1frB t1fr515
  rw [envAdd_lookup (t1fr516_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1fr509_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1frB_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup ((t1fr515_sf hf px py).add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1fr515_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1fr508_sf hf px py) symCmpK, if_neg (by decide +kernel), t1fr508_lookup_x hf px py]
theorem t1fr517_lookup_y : fmapLookupBy symCmpK CorpusE0.ySym (t1fr517 px py f) = some (Vobject (OVpointer py)) := by
  unfold t1fr517 t1fr516
  rw [envAdd_lookup (t1fr516_sf hf px py) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup (t1fr509_sf hf px py) symCmpK, if_neg (by decide +kernel), t1fr509_lookup_y hf px py]

end Frames

/-! ## The label `ret_507` -/

/-- The registration of `save ret_507: loaded integer (a_518: loaded integer
    := Specified(0)) in pure(a_518)`. -/
def t1RetQ : LabelMap :=
  fmapAddBy symCmpL CorpusE0.retSym ([(a518, CorpusE0.lint)], Expr [] (Epure (psym a518))) fmapEmpty

theorem t1RetQ_lookup :
    lookupLabel t1RetQ CorpusE0.retSym = some ([(a518, CorpusE0.lint)], Expr [] (Epure (psym a518))) := by
  unfold lookupLabel t1RetQ
  rw [fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

theorem t1RetQ_inv {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t1RetQ l = some (params, cont)) :
    params = [(a518, CorpusE0.lint)] ∧ cont = Expr [] (Epure (psym a518)) := by
  unfold lookupLabel t1RetQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem t1RetQ_bindArgs (v : value) (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindArgs [(a518, CorpusE0.lint)] [v] (f :: rest) = envAdd a518 v f :: rest := by
  show update_env (mk_sym_pat a518 CorpusE0.lint) v (f :: rest) = _
  rw [update_env_cons, update_env_aux_sym]

theorem t1fr518_lookup {f : Fmap sym value} (hf : SymFrame f) (v : value) :
    fmapLookupBy symCmpK a518 (envAdd a518 v f) = some v := by
  rw [envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

/-! ## THE PARTIAL JUDGMENT -/

def t1Ls (GF : BundledGFunctors) [SpikeGS .hasLC GF] : LabelSpec GF := fun l vs ρ =>
  iprop(⌜symOrd l CorpusE0.retSym = .eq ∧ vs = [lint 4] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝)

def ψT1s (GF : BundledGFunctors) [SpikeGS .hasLC GF] : SpikeVal → EnvStack → IProp GF :=
  fun w _ => iprop(⌜w = SpikeVal.pure (lint 4)⌝)

theorem t1_blockSpecs [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t1RetQ) :
    ⊢ blockSpecs (GF := GF) M p (t1Ls GF) emptyProcSpec (ψT1s GF) := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  rw [hQ] at hl
  obtain ⟨rfl, rfl⟩ := t1RetQ_inv hl
  dsimp only [t1Ls]
  iintro %hpure
  obtain ⟨-, rfl, f, rest, hρ, hf⟩ := hpure
  cases hρ
  rw [t1RetQ_bindArgs]
  iapply wps_pure (psym a518) _ rfl (t1sym_eval hex _ (t1fr518_lookup hf (lint 4)))
  dsimp only [ψT1s]
  ipureintro
  rfl

/-- THE WHOLE PROGRAM, PARTIAL judgment. -/
theorem t1_wps [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = t1RetQ)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4)) ⊢
      wps M p (t1Ls GF) emptyProcSpec (ψT1s GF) t1Main (ev0 :: evs) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapX, HcapY⟩
  simp only [t1Main, letS, seqE, wc, bnd, createInt_eq, killInt_eq, act_store_eq]
  rw [show (Pattern [] (CaseBase (some CorpusE0.xSym, ptrTy)) : pattern) = symPat [] CorpusE0.xSym ptrTy from rfl]
  -- x := create(Ivalignof(int), int)
  iapply wps_seq_sym
  iapply wps_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty (PrefSource (t1Reg 15 54) [CorpusE0.xSym])
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wps_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t1Reg 15 54) [CorpusE0.xSym])
    (ev0 :: evs) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapX]
  · iexact HcapX
  iintro %px ⟨HptX, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym CorpusE0.xSym ptrTy]
  rw [show (Pattern [] (CaseBase (some CorpusE0.ySym, ptrTy)) : pattern) = symPat [] CorpusE0.ySym ptrTy from rfl]
  -- y := create(Ivalignof(int), int)
  iapply wps_seq_sym
  iapply wps_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty (PrefSource (t1Reg 15 54) [CorpusE0.ySym])
    _ (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wps_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t1Reg 15 54) [CorpusE0.ySym])
    _ intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapY]
  · iexact HcapY
  iintro %py ⟨HptY, -⟩
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym CorpusE0.ySym ptrTy]
  -- a_508 := bound({loc} pure(Specified(3)))
  rw [show (Pattern [] (CaseBase (some a508, CorpusE0.lint)) : pattern) = symPat [] a508 CorpusE0.lint from rfl]
  iapply wps_seq_sym
  unfold t1Spec3 bnd
  iapply wps_bound _ _ _ rfl
  iapply wps_pure (specInt 3) _ rfl (specInt_eval _ 3)
  simp only [SpikeVal.val]
  iexists (lint 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a508 CorpusE0.lint]
  -- store(int, x, conv_loaded_int(int, a_508)) ; …
  iapply wps_seq
  iapply wps_store_eval _ _ empty_annotation intTy (psym CorpusE0.xSym) (convLoadedInt a508) NA _ rfl
    (pv := px) (cv := lint 3)
    (t1sym_eval hex evs (t1fr508_lookup_x hf px py))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex evs (t1fr508_lookup_a508 hf px py)) (by decide) (by decide))
  iapply wps_store _ _ empty_annotation intTy px (lint 3) NA threeMval
    (List.replicate (CerbMem.sizeofCtype M.tagDefs intTy) undefByte) _
    three_encodes (three_storable _)
  isplitl [HptX]
  · iexact HptX
  iintro %fp1 HptX
  simp only [SpikeVal.mergeInto]
  rw [show (Pattern [] (CaseBase (some a509, CorpusE0.lint)) : pattern) = symPat [] a509 CorpusE0.lint from rfl]
  -- a_509 := bound(let weak (a_510, a_511) = unseq(let weak a_515 = pure(x) in load(int, a_515),
  --                                                 pure(Specified(1))) in pure(case …))
  iapply wps_seq_sym
  iapply wps_bound _ _ _ rfl
  rw [show (Pattern [] (CaseCtor Ctuple [Pattern [] (CaseBase (some a510, CorpusE0.lint)),
      Pattern [] (CaseBase (some a511, CorpusE0.lint))]) : pattern) =
    tuplePat [] [([], some a510, CorpusE0.lint), ([], some a511, CorpusE0.lint)] from rfl]
  iapply wps_wseq_tuple_annot _ [] [([], some a510, CorpusE0.lint), ([], some a511, CorpusE0.lint)]
  -- THE UNSEQ: the engine reduces the LAST component first — pure(Specified(1))
  rw [show ([t1LoadX, t1Spec1] : List CoreExpr) = [t1LoadX] ++ t1Spec1 :: [] from rfl]
  iapply wps_unseq_focus [] [t1LoadX] t1Spec1 [] _ rfl rfl
  unfold t1Spec1
  iapply wps_pure (specInt 1) _ rfl (specInt_eval _ 1)
  iintro %wa %hwa
  -- … then the read of x
  rw [show ([t1LoadX] ++ ofValA wa :: [] : List CoreExpr) = [] ++ t1LoadX :: [ofValA wa] from rfl]
  iapply wps_unseq_focus [] [] t1LoadX [ofValA wa] _ (by simp) (by simp)
  unfold t1LoadX letW
  rw [act_load_eq]
  rw [show (Pattern [] (CaseBase (some a515, ptrTy)) : pattern) = symPat [] a515 ptrTy from rfl]
  iapply wps_wseq_sym
  iapply wps_pure (psym CorpusE0.xSym) _ rfl (t1sym_eval hex evs (t1fr508_lookup_x hf px py))
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a515 ptrTy]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ HptX
    with ⟨%idx, %adx, %hpvx, HcellX⟩
  iapply wps_load_eval _ _ empty_annotation intTy (psym a515) NA _ rfl (pv := px)
    (t1sym_eval hex evs (t1fr515_lookup_a515 hf px py))
  rw [hpvx, show (cellPtr idx adx) = cellPtr idx (adx + ((0 : Nat) : Int))
    from congrArg (cellPtr idx) (by omega)]
  iapply wps_load_cell_at _ _ empty_annotation idx adx intTy 0 intTy NA
    (.own 1) (threeBytes M.tagDefs) _ (mv := threeMval) (by omega)
    (fun lum fpm => three_reconstruct lum fpm _) three_loadTrap
  isplitl [HcellX]
  · iexact HcellX
  iintro %fp2 HcellX
  simp only [SpikeVal.val]
  rw [three_fromMemValue,
    show cellPtr idx (adx + ((0 : Nat) : Int)) = cellPtr idx adx from congrArg (cellPtr idx) (by omega), ← hpvx]
  iintro %wa' %hwa'
  -- both components are values: the completion into the annotated tuple
  cases wa with
  | annot _ _ _ _ _ => cases hwa
  | pure aA bA vA =>
  obtain rfl : vA = lint 1 := SpikeVal.pure.inj hwa
  cases wa' with
  | pure _ _ _ => cases hwa'
  | annot aA' aA2' bA' dsA' vA' =>
  obtain ⟨rfl, rfl⟩ : dsA' = [DA_pos [] fp2] ∧ vA' = lint 3 := by
    injection hwa' with h1 h2; exact ⟨h1, h2⟩
  rw [show ([] ++ ofValA (SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3)) ::
      [ofValA (SpikeValA.pure aA bA (lint 1))] : List CoreExpr) =
    [SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3), SpikeValA.pure aA bA (lint 1)].map ofValA
    from rfl]
  iapply wps_unseq_vals [] [SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3),
    SpikeValA.pure aA bA (lint 1)] _ rfl
  -- the tuple binder at the annotated head; the annotation rides onto the `+`
  iexists [lint 3, lint 1], [DA_pos [] fp2]
  isplit
  · ipureintro
    rfl
  rw [update_env_tuple2 a510 a511 CorpusE0.lint]
  iapply wps_annot
  rw [t1CasePe_eq]
  iapply wps_c_add a510 a511 a512 a513 (t1Reg 36 41) _
    (t1sym_eval hex evs (t1frB_lookup_a510 hf px py)) (t1sym_eval hex evs (t1frB_lookup_a511 hf px py))
    t1_cAdd_select_31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [SpikeVal.merge]
  iexists (lint 4)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a509 CorpusE0.lint]
  -- store(int, y, conv_loaded_int(int, a_509)) ; …
  iapply wps_seq
  iapply wps_store_eval _ _ empty_annotation intTy (psym CorpusE0.ySym) (convLoadedInt a509) NA _ rfl
    (pv := py) (cv := lint 4)
    (t1sym_eval hex evs (t1fr509_lookup_y hf px py))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex evs (t1fr509_lookup_a509 hf px py)) (by decide) (by decide))
  iapply wps_store _ _ empty_annotation intTy py (lint 4) NA t1FourMval
    (List.replicate (CerbMem.sizeofCtype M.tagDefs intTy) undefByte) _
    t1_four_encodes (t1_four_storable _)
  isplitl [HptY]
  · iexact HptY
  iintro %fp3 HptY
  simp only [SpikeVal.mergeInto]
  rw [show (Pattern [] (CaseBase (some a517, CorpusE0.lint)) : pattern) = symPat [] a517 CorpusE0.lint from rfl]
  -- a_517 := bound(let weak a_516 = pure(y) in load(int, a_516))
  iapply wps_seq_sym
  iapply wps_bound _ _ _ rfl
  unfold t1LoadY letW
  rw [act_load_eq]
  rw [show (Pattern [] (CaseBase (some a516, ptrTy)) : pattern) = symPat [] a516 ptrTy from rfl]
  iapply wps_wseq_sym
  iapply wps_pure (psym CorpusE0.ySym) _ rfl (t1sym_eval hex evs (t1fr509_lookup_y hf px py))
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a516 ptrTy]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ HptY
    with ⟨%idy, %ady, %hpvy, HcellY⟩
  iapply wps_load_eval _ _ empty_annotation intTy (psym a516) NA _ rfl (pv := py)
    (t1sym_eval hex evs (t1fr516_lookup_a516 hf px py))
  rw [hpvy, show (cellPtr idy ady) = cellPtr idy (ady + ((0 : Nat) : Int))
    from congrArg (cellPtr idy) (by omega)]
  iapply wps_load_cell_at _ _ empty_annotation idy ady intTy 0 intTy NA
    (.own 1) (fourBytesT1 M.tagDefs) _ (mv := t1FourMval) (by omega)
    (fun lum fpm => t1_four_reconstruct lum fpm _) t1_four_loadTrap
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
  rw [update_env_sym a517 CorpusE0.lint]
  -- kill(int, x) ; kill(int, y) ; run ret_507(conv_loaded_int(int, a_517)) ; …
  iapply wps_seq
  iapply wps_kill_eval _ _ empty_annotation (Static0 intTy) (psym CorpusE0.xSym) _ rfl (pv := px)
    (t1sym_eval hex evs (t1fr517_lookup_x hf px py))
  rw [hpvx]
  iapply wps_kill_emp _ _ empty_annotation (Static0 intTy) (cellPtr idx adx) intTy
    (threeBytes M.tagDefs) _ rfl
  isplitl [HcellX]
  · iapply (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mpr
    iexists idx, adx
    isplit
    · ipureintro
      rfl
    · iexact HcellX
  simp only [SpikeVal.mergeInto]
  rw [← hpvx]
  iapply wps_seq
  iapply wps_kill_eval _ _ empty_annotation (Static0 intTy) (psym CorpusE0.ySym) _ rfl (pv := py)
    (t1sym_eval hex evs (t1fr517_lookup_y hf px py))
  rw [hpvy]
  iapply wps_kill_emp _ _ empty_annotation (Static0 intTy) (cellPtr idy ady) intTy
    (fourBytesT1 M.tagDefs) _ rfl
  isplitl [HcellY]
  · iapply (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mpr
    iexists idy, ady
    isplit
    · ipureintro
      rfl
    · iexact HcellY
  simp only [SpikeVal.mergeInto]
  rw [← hpvy]
  iapply wps_seq
  iapply wps_run [] empty_annotation CorpusE0.retSym [convLoadedInt a517] _ _
    (by rw [hQ]; exact t1RetQ_lookup)
    (by rw [evalPexprs_cons, t1ConvLoadedInt_eval hstd (t1sym_eval hex evs (t1fr517_lookup_a517 hf px py))
          (by decide) (by decide), evalPexprs_nil]; rfl)
  dsimp only [t1Ls]
  ipureintro
  exact ⟨by decide +kernel, rfl, _, _, rfl, t1fr517_sf hf px py⟩

/-! ## THE TOTAL JUDGMENT -/

def t1LsT (GF : BundledGFunctors) [SpikeGS .hasLC GF] : LabelSpecT GF := fun l m vs ρ =>
  iprop(⌜symOrd l CorpusE0.retSym = .eq ∧ m = 2 ∧ vs = [lint 4] ∧ ∃ f rest, ρ = f :: rest ∧ SymFrame f⌝)

/-- The post: the delivered value is `Specified(4)`. -/
def ψT1 : value → Mem → Prop := fun v _ => v = lint 4

theorem t1LsT_readout [LemFuel] [SpikeGS .hasLC GF] :
    ∀ w ρ', iprop(⌜w = SpikeVal.pure (lint 4)⌝) ⊢ readoutPost (GF := GF) ψT1 w ρ' := by
  intro w ρ'
  iintro %hw
  iintro %σ' %ns %κs %nt -
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  subst hw
  rfl

theorem t1_blockSpecsT [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hex : ∀ x, resolveExtern M.extern x = x)
    (hQ : M.labelsAt p = t1RetQ) :
    ⊢ blockSpecsT (GF := GF) M p (t1LsT GF) emptyProcSpecT (readoutPost ψT1) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [hQ] at hl
  obtain ⟨rfl, rfl⟩ := t1RetQ_inv hl
  dsimp only [t1LsT]
  iintro %hpure
  obtain ⟨-, rfl, rfl, f, rest, hρ, hf⟩ := hpure
  cases hρ
  rw [t1RetQ_bindArgs]
  iapply wpt_pure (psym a518) _ (Nat.le_refl 2) rfl
    (t1sym_eval hex _ (t1fr518_lookup hf (lint 4)))
  iapply t1LsT_readout
  ipureintro
  rfl

/-- THE WHOLE PROGRAM, total judgment, BUDGET 48: from the two cells' summed
    allocation budget to the readout `Specified(4)`. The budget is an UPPER
    BOUND assembled rule by rule (the E4 record §6 (ii) tabulates it: each
    rule's constant covers its round and the delivered value's cost), not
    the exact round count: the shipped inner loop delivers the value after
    40 rounds and reports PROGRAM-DONE at fuel 42 (historical measurement
    on the E4 pin, not remeasured here — the E4 range audit N-1,
    docs/2026-09-05_audit-e4-range.md §3.4), so the `k + 2` of
    `wpt_driver_done_alloc` carries 8 units of slack; nothing claims
    tightness (KOI B6). -/
theorem t1_wpt [LemFuel] (hfuel : 0 < LemFuel.fuel) [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} (hstd : StdE3 M.file)
    (hex : ∀ x, resolveExtern M.extern x = x) (hQ : M.labelsAt p = t1RetQ)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs intTy 4 + allocCost M.tagDefs intTy 4)) ⊢
      wpt M p (t1LsT GF) emptyProcSpecT 48 (readoutPost ψT1) t1Main (ev0 :: evs) := by
  iintro Hcap
  icases (allocBudget_split _ _).1 $$ Hcap with ⟨HcapX, HcapY⟩
  simp only [t1Main, letS, seqE, wc, bnd, createInt_eq, killInt_eq, act_store_eq]
  rw [show (Pattern [] (CaseBase (some CorpusE0.xSym, ptrTy)) : pattern) = symPat [] CorpusE0.xSym ptrTy from rfl]
  -- x := create(Ivalignof(int), int)
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 45
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty (PrefSource (t1Reg 15 54) [CorpusE0.xSym])
    (ev0 :: evs) (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t1Reg 15 54) [CorpusE0.xSym])
    (ev0 :: evs) (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapX]
  · iexact HcapX
  iintro %px ⟨HptX, -⟩
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym CorpusE0.xSym ptrTy]
  rw [show (Pattern [] (CaseBase (some CorpusE0.ySym, ptrTy)) : pattern) = symPat [] CorpusE0.ySym ptrTy from rfl]
  -- y := create(Ivalignof(int), int)
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 42
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_create_eval _ _ empty_annotation (Pexpr [] () (PEctor Civalignof [intCty])) intCty (PrefSource (t1Reg 15 54) [CorpusE0.ySym])
    _ (align := CerbMem.alignofIval M.tagDefs intTy) (ty := intTy) rfl
    (alignofIntPe_eval _ _) (evalPexpr_val _ _ _ _ _)
  rw [alignofIval_intTy]
  iapply wpt_create (hfuel := hfuel) (halign := by decide) (haddr := rfl) _ _ empty_annotation .Prov_none 4 intTy (PrefSource (t1Reg 15 54) [CorpusE0.ySym])
    _ (Nat.le_refl 2) intTy_size_pos intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [HcapY]
  · iexact HcapY
  iintro %py ⟨HptY, -⟩
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym CorpusE0.ySym ptrTy]
  -- a_508 := bound({loc} pure(Specified(3)))
  rw [show (Pattern [] (CaseBase (some a508, CorpusE0.lint)) : pattern) = symPat [] a508 CorpusE0.lint from rfl]
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 3 39
  rw [show (3 : Nat) = 2 + 1 from rfl]
  unfold t1Spec3 bnd
  iapply wpt_bound _ _ _ rfl
  iapply wpt_pure (specInt 3) _ (Nat.le_refl 2) rfl (specInt_eval _ 3)
  simp only [SpikeVal.val]
  iexists (lint 3)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a508 CorpusE0.lint]
  -- store(int, x, conv_loaded_int(int, a_508)) ; …
  iapply wpt_seq _ _ _ _ _ _ _ 4 35
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ empty_annotation intTy (psym CorpusE0.xSym) (convLoadedInt a508) NA _ rfl
    (pv := px) (cv := lint 3)
    (t1sym_eval hex evs (t1fr508_lookup_x hf px py))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex evs (t1fr508_lookup_a508 hf px py)) (by decide) (by decide))
  iapply wpt_store _ _ empty_annotation intTy px (lint 3) NA threeMval
    (List.replicate (CerbMem.sizeofCtype M.tagDefs intTy) undefByte) _ (Nat.le_refl 3)
    three_encodes (three_storable _)
  isplitl [HptX]
  · iexact HptX
  iintro %fp1 HptX
  simp only [SpikeVal.mergeInto]
  rw [show (Pattern [] (CaseBase (some a509, CorpusE0.lint)) : pattern) = symPat [] a509 CorpusE0.lint from rfl]
  -- a_509 := bound(let weak (a_510, a_511) = unseq(…) in pure(case …)) — 15 units:
  -- REMOVE-BOUND 1; the unseq 11 (pure 2 + [pure 2 + load_eval 1 + load 3] + completion 3);
  -- the LETW-ANNOT beta is prepaid by the annotated tuple's delivery cost; the
  -- annotation wrapper 1 + the `+` round 2
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 15 20
  rw [show (15 : Nat) = 14 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  rw [show (Pattern [] (CaseCtor Ctuple [Pattern [] (CaseBase (some a510, CorpusE0.lint)),
      Pattern [] (CaseBase (some a511, CorpusE0.lint))]) : pattern) =
    tuplePat [] [([], some a510, CorpusE0.lint), ([], some a511, CorpusE0.lint)] from rfl]
  iapply wpt_wseq_tuple_annot _ [] [([], some a510, CorpusE0.lint), ([], some a511, CorpusE0.lint)]
    _ _ _ _ 11 3
  rw [show ([t1LoadX, t1Spec1] : List CoreExpr) = [t1LoadX] ++ t1Spec1 :: [] from rfl]
  iapply wpt_unseq_focus [] [t1LoadX] t1Spec1 [] _ rfl rfl 2 9
  unfold t1Spec1
  iapply wpt_pure (specInt 1) _ (Nat.le_refl 2) rfl (specInt_eval _ 1)
  iintro %wa %hwa
  rw [show ([t1LoadX] ++ ofValA wa :: [] : List CoreExpr) = [] ++ t1LoadX :: [ofValA wa] from rfl]
  iapply wpt_unseq_focus [] [] t1LoadX [ofValA wa] _ (by simp) (by simp) 6 3
  unfold t1LoadX letW
  rw [act_load_eq]
  rw [show (Pattern [] (CaseBase (some a515, ptrTy)) : pattern) = symPat [] a515 ptrTy from rfl]
  iapply wpt_wseq_sym _ _ _ _ _ _ _ _ 2 4
  iapply wpt_pure (psym CorpusE0.xSym) _ (Nat.le_refl 2) rfl (t1sym_eval hex evs (t1fr508_lookup_x hf px py))
  iexists (Vobject (OVpointer px))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a515 ptrTy]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ HptX
    with ⟨%idx, %adx, %hpvx, HcellX⟩
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval _ _ empty_annotation intTy (psym a515) NA _ rfl (pv := px)
    (t1sym_eval hex evs (t1fr515_lookup_a515 hf px py))
  rw [hpvx, show (cellPtr idx adx) = cellPtr idx (adx + ((0 : Nat) : Int))
    from congrArg (cellPtr idx) (by omega)]
  iapply wpt_load_cell_at _ _ empty_annotation idx adx intTy 0 intTy NA
    (.own 1) (threeBytes M.tagDefs) _ (mv := threeMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => three_reconstruct lum fpm _) three_loadTrap
  isplitl [HcellX]
  · iexact HcellX
  iintro %fp2 HcellX
  simp only [SpikeVal.val]
  rw [three_fromMemValue,
    show cellPtr idx (adx + ((0 : Nat) : Int)) = cellPtr idx adx from congrArg (cellPtr idx) (by omega), ← hpvx]
  iintro %wa' %hwa'
  cases wa with
  | annot _ _ _ _ _ => cases hwa
  | pure aA bA vA =>
  obtain rfl : vA = lint 1 := SpikeVal.pure.inj hwa
  cases wa' with
  | pure _ _ _ => cases hwa'
  | annot aA' aA2' bA' dsA' vA' =>
  obtain ⟨rfl, rfl⟩ : dsA' = [DA_pos [] fp2] ∧ vA' = lint 3 := by
    injection hwa' with h1 h2; exact ⟨h1, h2⟩
  rw [show ([] ++ ofValA (SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3)) ::
      [ofValA (SpikeValA.pure aA bA (lint 1))] : List CoreExpr) =
    [SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3), SpikeValA.pure aA bA (lint 1)].map ofValA
    from rfl]
  iapply wpt_unseq_vals [] [SpikeValA.annot aA' aA2' bA' [DA_pos [] fp2] (lint 3),
    SpikeValA.pure aA bA (lint 1)] _ (Nat.le_refl 3) rfl
  iexists [lint 3, lint 1], [DA_pos [] fp2]
  isplit
  · ipureintro
    rfl
  rw [update_env_tuple2 a510 a511 CorpusE0.lint, show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_annot
  rw [t1CasePe_eq]
  iapply wpt_c_add a510 a511 a512 a513 (t1Reg 36 41) _ (Nat.le_refl 2)
    (t1sym_eval hex evs (t1frB_lookup_a510 hf px py)) (t1sym_eval hex evs (t1frB_lookup_a511 hf px py))
    t1_cAdd_select_31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [SpikeVal.merge]
  iexists (lint 4)
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a509 CorpusE0.lint]
  -- store(int, y, conv_loaded_int(int, a_509)) ; …
  iapply wpt_seq _ _ _ _ _ _ _ 4 16
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval _ _ empty_annotation intTy (psym CorpusE0.ySym) (convLoadedInt a509) NA _ rfl
    (pv := py) (cv := lint 4)
    (t1sym_eval hex evs (t1fr509_lookup_y hf px py))
    (t1ConvLoadedInt_eval hstd (t1sym_eval hex evs (t1fr509_lookup_a509 hf px py)) (by decide) (by decide))
  iapply wpt_store _ _ empty_annotation intTy py (lint 4) NA t1FourMval
    (List.replicate (CerbMem.sizeofCtype M.tagDefs intTy) undefByte) _ (Nat.le_refl 3)
    t1_four_encodes (t1_four_storable _)
  isplitl [HptY]
  · iexact HptY
  iintro %fp3 HptY
  simp only [SpikeVal.mergeInto]
  rw [show (Pattern [] (CaseBase (some a517, CorpusE0.lint)) : pattern) = symPat [] a517 CorpusE0.lint from rfl]
  -- a_517 := bound(let weak a_516 = pure(y) in load(int, a_516))
  iapply wpt_seq_sym _ _ _ _ _ _ _ _ 7 9
  rw [show (7 : Nat) = 6 + 1 from rfl]
  iapply wpt_bound _ _ _ rfl
  unfold t1LoadY letW
  rw [act_load_eq]
  rw [show (Pattern [] (CaseBase (some a516, ptrTy)) : pattern) = symPat [] a516 ptrTy from rfl]
  iapply wpt_wseq_sym _ _ _ _ _ _ _ _ 2 4
  iapply wpt_pure (psym CorpusE0.ySym) _ (Nat.le_refl 2) rfl (t1sym_eval hex evs (t1fr509_lookup_y hf px py))
  iexists (Vobject (OVpointer py))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym a516 ptrTy]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ HptY
    with ⟨%idy, %ady, %hpvy, HcellY⟩
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval _ _ empty_annotation intTy (psym a516) NA _ rfl (pv := py)
    (t1sym_eval hex evs (t1fr516_lookup_a516 hf px py))
  rw [hpvy, show (cellPtr idy ady) = cellPtr idy (ady + ((0 : Nat) : Int))
    from congrArg (cellPtr idy) (by omega)]
  iapply wpt_load_cell_at _ _ empty_annotation idy ady intTy 0 intTy NA
    (.own 1) (fourBytesT1 M.tagDefs) _ (mv := t1FourMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => t1_four_reconstruct lum fpm _) t1_four_loadTrap
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
  rw [update_env_sym a517 CorpusE0.lint]
  -- kill(int, x) ; kill(int, y) ; run ret_507(conv_loaded_int(int, a_517)) ; …
  iapply wpt_seq _ _ _ _ _ _ _ 3 6
  rw [show (3 : Nat) = 2 + 1 from rfl]
  iapply wpt_kill_eval _ _ empty_annotation (Static0 intTy) (psym CorpusE0.xSym) _ rfl (pv := px)
    (t1sym_eval hex evs (t1fr517_lookup_x hf px py))
  rw [hpvx]
  iapply wpt_kill_emp _ _ empty_annotation (Static0 intTy) (cellPtr idx adx) intTy
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
  iapply wpt_kill_eval _ _ empty_annotation (Static0 intTy) (psym CorpusE0.ySym) _ rfl (pv := py)
    (t1sym_eval hex evs (t1fr517_lookup_y hf px py))
  rw [hpvy]
  iapply wpt_kill_emp _ _ empty_annotation (Static0 intTy) (cellPtr idy ady) intTy
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
  iapply wpt_seq _ _ _ _ _ _ _ 3 0
  iapply wpt_run [] empty_annotation CorpusE0.retSym [convLoadedInt a517] _ _ 2
    (by rw [hQ]; exact t1RetQ_lookup)
    (by rw [evalPexprs_cons, t1ConvLoadedInt_eval hstd (t1sym_eval hex evs (t1fr517_lookup_a517 hf px py))
          (by decide) (by decide), evalPexprs_nil]; rfl)
    (Nat.le_refl 3)
  dsimp only [t1LsT]
  ipureintro
  exact ⟨by decide +kernel, rfl, rfl, _, _, rfl, t1fr517_sf hf px py⟩

/-! ## THE PRODUCTION ENTRY — THE MILESTONE -/

/-- The whole-file registration at the production initial run state: the
    shipped `collect_labeled_continuations_NEW` on `prodFileLib stdlibE3 []
    t1Main` registers exactly `ret_507` for `main`. -/
theorem collect_new_t1Main :
    collect_labeled_continuations_NEW (prodFileLib stdlibE3 [] t1Main) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym t1RetQ fmapEmpty := rfl

theorem t1Main_labeledAt (sup : Nat) :
    LabeledAt (prodRSLib stdlibE3 [] sup t1Main) mainSym t1RetQ := by
  unfold LabeledAt
  rw [prodRSLib_labeled, collect_new_t1Main, fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

/-- THE FIRST CORPUS PROGRAM, CERTIFIED END TO END (E4 acceptance (ii), THE
    MILESTONE): the shipped pipeline on the library-carrying one-procedure
    file wrapping `docs/corpus-e0/t1.c`'s emitted `main` — transcribed
    VERBATIM, `CorpusE0.t1Main` — is EXACTLY ONE Active execution; its result
    value is `Specified(4)` (`int x = 3; int y = x + 1; return y;`). The
    statement is `exhibitC_prod_e3`'s but for the program (the emitted one)
    and the budget; the chain is `t1_wpt → wpt_driver_done_alloc →
    prod_run_eqJ_lib1`, at the caller's ambient fuel of at least 50. The
    historical oracle `--exec` measurement on t1.c returned `Specified(4)`,
    exit code 4 (the E4 record §5); it is not a new-pin oracle measurement.
    The full-file/library connection remains A7. -/
theorem t1_certified_production [LemFuel] (hfuel : 50 ≤ LemFuel.fuel) (sup : Nat) (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFileLib stdlibE3 [] t1Main) args)
          ((initial_driver_state sup (prodFileLib stdlibE3 [] t1Main) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = lint 4 ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQe := t1Main_labeledAt sup
  have hlbl := prodCtx_labels (f := prodFileLib stdlibE3 [] t1Main) hQe
  obtain ⟨dres, dst', heq, hψ, hbl, hout, herr⟩ :=
    prod_run_eqJ_lib1 sup stdlibE3 t1Main hQe ψT1 48
      (wpt_driver_done_alloc (hfuel := by omega) (GF := SpikeGF) (ctl := prodCtl sup)
        (M₀ := prodCtx (prodFileLib stdlibE3 [] t1Main) (prodRSLib stdlibE3 [] sup t1Main))
        rfl rfl hlbl rfl rfl rfl rfl (Nat.le_refl _)
        (fun l params cont hl => by
          rw [hlbl] at hl
          obtain ⟨-, rfl⟩ := t1RetQ_inv hl
          exact .pure_op rfl (.sym [] a518))
        (fun l params cont hl => by
          rw [hlbl] at hl
          obtain ⟨-, rfl⟩ := t1RetQ_inv hl
          exact (Nat.le_trans (show evalDepth _ ≤ 1 from Nat.le_of_ble_eq_true rfl) (by omega)))
        (t1LsT SpikeGF)
        t1Main fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
        (allocCost fmapEmpty intTy 4 + allocCost fmapEmpty intTy 4) t1Main_frag (Nat.le_trans (show evalDepth _ ≤ 40 from Nat.le_of_ble_eq_true rfl) (by omega))
        (prodMem₀_launchCoh _ prod_two_int_budget_fits)
        ψT1 48
        (by
          intro inst
          iintro ⟨-, Hcap⟩
          isplitr [Hcap]
          · iapply t1_blockSpecsT (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl
          · iapply t1_wpt (hfuel := by omega) (M := prodCtx (prodFileLib stdlibE3 [] t1Main) (prodRSLib stdlibE3 [] sup t1Main))
              rfl (resolveExtern_id_of_empty (prodCtx_extern _ _)) hlbl fmapEmpty []
              symFrame_empty $$ Hcap))
      hfuel
      fs args
  exact ⟨dres, dst', heq, hψ, hbl, hout, herr⟩

end CerberusHeapLang
