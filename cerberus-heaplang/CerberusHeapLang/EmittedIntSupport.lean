/- Shared derived support for the actual emitted integer programs.
   Source annotations, cell types, symbols and evaluated operands remain
   parameters. The captured-library adapter supplies conversion premises;
   the generic load and assignment rules have no fixture premise. -/
import CerberusHeapLang.Examples.EmittedInt
import CerberusHeapLang.EmittedStdCore

set_option autoImplicit false
namespace CerberusHeapLang.EmittedIntSupport
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open EmittedStdCore (sintTyAnn HasIntLibrary)

variable {GF : BundledGFunctors}

def symPe (a : List annot) (x : sym) : generic_pexpr Unit sym :=
  Pexpr a () (PEsym x)

theorem update_sym (a : List annot) (x : sym) (bty : core_base_type)
    (v : value) (f : Fmap sym value) (rest : EnvStack) :
    update_env (symPat a x bty) v (f :: rest) = envAdd x v f :: rest := by
  rw [update_env_cons]
  rfl

/-- Evaluation uses key comparison rather than identity of descriptive
symbol metadata. The source annotation is retained in the expression. -/
theorem symbol_eval [LemFuel] {M : MachineCtx}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    {x : sym} {f : Fmap sym value} {v : value} (hf : SymFrame f)
    (rest : EnvStack) (a : List annot)
    (hl : fmapLookupBy symCmpK x f = some v) :
    evalPexpr M.tagDefs M.extern M.file (f :: rest) (symPe a x) = some v :=
  evalPexpr_sym_of_compare M.tagDefs hf rest a (hex x) hl

theorem int_size (ta : List annot) {tds : CerbTags.TagDefsMap} :
    CerbMem.sizeofCtype tds (sintTyAnn ta) = 4 := rfl
theorem int_align [LemFuel] (ta : List annot) {tds : CerbTags.TagDefsMap} :
    CerbMem.alignofIval tds (sintTyAnn ta) = .IV .Prov_none 4 := rfl
theorem int_nonatomic (ta : List annot) : atomicTy (sintTyAnn ta) = false := rfl
theorem int_size_pos (ta : List annot) {tds : CerbTags.TagDefsMap} :
    0 < CerbMem.sizeofCtype tds (sintTyAnn ta) := by rw [int_size]; decide
theorem int_decIndep (ta : List annot) {tds : CerbTags.TagDefsMap}
    (a : Int) (bs : List CerbMem.AbsByte) :
    decIndep tds a (sintTyAnn ta) bs := fun _ _ => rfl
theorem int_cellLoadTrap (ta : List annot) (tds : CerbTags.TagDefsMap)
    (a : Int) (bs : List CerbMem.AbsByte) :
    cellLoadTrap tds ⟨a, sintTyAnn ta, bs⟩ = false := rfl

/-- Annotation-preserving signed-int storability follows from the existing
range-based serializer lemma. No fixed program value is assumed. -/
theorem int_storable (tds : CerbTags.TagDefsMap) (ta : List annot) (n : Int)
    (hlo : -2147483648 ≤ n) (hhi : n ≤ 2147483647) :
    StorableAt tds (sintTyAnn ta) (emittedIntMval n) := by
  have h := emittedInt_storable tds n hlo hhi
  exact ⟨h.compat, h.fpm, h.len, h.bytes_fpm, fun _ _ _ => rfl⟩

theorem int_encodes [LemFuel] (tds : CerbTags.TagDefsMap)
    (ta : List annot) (n : Int) :
    memValueFromValue tds (Ctype [] (unatomic_ (sintTyAnn ta))) (lint n) =
      some (emittedIntMval n) := rfl

/-- The emitted pointer-temporary load, with all source annotations and
the cell type retained. -/
def boundLoad (a pa ax ap aa ar : List annot) (bty : core_base_type)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (x tmp : sym) (mo : memory_order) : CoreExpr :=
  Expr a (Ewseq (symPat pa tmp bty)
    (Expr ax (Epure (symPe ap x)))
    (loadOpRedex aa loc ann ty (symPe ar tmp) mo))

/-- A typed load through a source pointer binder, retaining the exact read
footprint. The rule is generic in cell type, annotations and memory order. -/
theorem wpt_boundLoad [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (a pa ax ap aa ar : List annot) (bty : core_base_type)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (x tmp : sym) (mo : memory_order)
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (dq : DFrac) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv ty bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv dq ty bs ∗
      (pointsToCell M.tagDefs pv dq ty bs -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pv ty)] v)
          (envAdd tmp (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (boundLoad a pa ax ap aa ar bty loc ann ty x tmp mo)
        (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold boundLoad
  iapply wpt_wseq_sym _ _ _ _ _ _ _ _ 2 4
  iapply wpt_pure (symPe ap x) _ (Nat.le_refl 2) rfl
    (symbol_eval hex hf rest ap hl)
  iexists (Vobject (OVpointer pv))
  isplit
  · ipureintro; rfl
  rw [update_sym]
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval aa loc ann ty (symPe ar tmp) mo _ rfl
    (symbol_eval hex (hf.add _ _) rest ar
      (by rw [envAdd_lookup hf, if_pos (symOrd_self _)]))
  iapply wpt_load_footprint aa loc ann ty pv mo dq bs _ (Nat.le_refl 3) htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro Hpt
  rw [hload]
  iapply HΨ $$ Hpt

/-- Signed-int assignment at already evaluated operands. The caller keeps
the exact emitted syntax and supplies evaluation facts; no library or
particular source-symbol spelling is built into the rule. -/
theorem wpt_intAssign [LemFuel] [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, symCmpK (resolveExtern M.extern x) x = .EQ)
    (an a0 a1 a2 a3 pa : List annot) (ds : List dyn_annotation)
    (bty : core_base_type) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (ta : List annot) (pp vp ret : generic_pexpr Unit sym) (mo : memory_order)
    (f : Fmap sym value) (rest : EnvStack) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte) (n : Int) (vr : value)
    (hlo : -2147483648 ≤ n) (hhi : n ≤ 2147483647)
    (hnv : valueFromPexprs [pp, vp] = none)
    (hpp : evalPexpr M.tagDefs M.extern M.file (f :: rest) pp = some (Vobject (OVpointer pv)))
    (hvp : evalPexpr M.tagDefs M.extern M.file (f :: rest) vp = some (lint n))
    (hnvr : valueFromPexpr ret = none)
    (hret : evalPexpr M.tagDefs M.extern M.file (f :: rest) ret = some vr) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) (sintTyAnn ta) bs ∗
      (∀ s : sym, ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pv (.own 1) (sintTyAnn ta) (emittedIntBytes M.tagDefs n) -∗
        Ψ (.pure vr) (envAdd s vr f :: rest))) ⊢
      wpt M p Ls Θ 16 Ψ
        (Expr an (Ebound (negAssignBody a0 a1 a2 a3 pa ds bty loc ann
          (sintTyAnn ta) pp vp ret mo))) (f :: rest) :=
  wpt_neg_bound_compare an a0 a1 a2 a3 pa ds bty loc ann (sintTyAnn ta) pp vp ret mo
    f rest hf (emittedIntMval n) bs (Nat.le_refl 16) hex hnv hpp hvp hnvr hret
    (int_encodes M.tagDefs ta n) (int_storable M.tagDefs ta n hlo hhi)

end CerberusHeapLang.EmittedIntSupport
