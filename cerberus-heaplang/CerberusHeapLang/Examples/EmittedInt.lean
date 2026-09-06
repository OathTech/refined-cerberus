/-
Shared public-rule derivations for the emitted integer expression shapes.
Locations and temporary symbols are parameters, so clients retain their
original AST while sharing the memory and environment proof plumbing.
-/
import CerberusHeapLang.CorpusT1Exhibit

set_option autoImplicit false
namespace CerberusHeapLang
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (emittedIntLoad ptrTy psym letW)

variable {GF : BundledGFunctors}

/-- Read a whole integer cell through the emitted temporary pointer
    binder. The caller retains ownership and receives the exact read footprint.
    The location and both source symbols are unrestricted parameters. -/
theorem wpt_emittedIntLoad_footprint [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (loc : CerbLocation.Loc) (x tmp : sym) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : SymFrame f) (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv intTy bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) intTy bs ∗
      (pointsToCell M.tagDefs pv (.own 1) intTy bs -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pv intTy)] v) (envAdd tmp (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (emittedIntLoad loc x tmp) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  unfold emittedIntLoad letW
  rw [show (Pattern [] (CaseBase (some tmp, ptrTy)) : pattern) = symPat [] tmp ptrTy from rfl]
  iapply wpt_wseq_sym _ _ _ _ _ _ _ _ 2 4
  iapply wpt_pure (psym x) _ (Nat.le_refl 2) rfl (t1sym_eval hex rest hl)
  iexists (Vobject (OVpointer pv))
  isplit
  · ipureintro; rfl
  rw [update_env_sym, act_load_eq]
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval _ _ _ _ _ _ _ rfl (pv := pv)
    (t1sym_eval hex rest (by rw [envAdd_lookup hf, if_pos (symOrd_self _)]))
  iapply wpt_load_footprint _ _ _ _ pv _ (.own 1) bs _ (Nat.le_refl 3) htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro Hpt
  rw [hload]
  iapply HΨ $$ Hpt

/-- Read a whole integer cell through the emitted temporary pointer
    binder. The caller retains ownership and receives the load footprint.
    The location and both source symbols are unrestricted parameters. -/
theorem wpt_emittedIntLoad [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (loc : CerbLocation.Loc) (x tmp : sym) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : SymFrame f) (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv intTy bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) intTy bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) intTy bs -∗
        Ψ (.annot [DA_pos [] fp] v) (envAdd tmp (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (emittedIntLoad loc x tmp) (f :: rest) := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_emittedIntLoad_footprint hex loc x tmp f rest hf pv bs v hl hload htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro Hpt
  iapply HΨ $$ Hpt

/-- The memory value and byte image written by an emitted signed-int assignment. -/
def emittedIntMval (n : Int) : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval n)

abbrev emittedIntBytes (tds : CerbTags.TagDefsMap) (n : Int) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] (emittedIntMval n)).2

theorem emittedInt_encodes (tds : CerbTags.TagDefsMap) (n : Int) :
    memValueFromValue tds (Ctype [] (unatomic_ intTy)) (lint n) = some (emittedIntMval n) := rfl

theorem emittedInt_storable (tds : CerbTags.TagDefsMap) (n : Int) :
    StorableAt tds intTy (emittedIntMval n) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The common integer-store protocol after an emitted assignment's
    mixed tuple binder. It preserves the RHS annotations until the
    enclosing bound removes them and exposes the fresh return binding. -/
theorem wpt_emittedIntStore [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hstd : StdE3 M.file) (hex : ∀ x, resolveExtern M.extern x = x)
    (loc : CerbLocation.Loc) (n m : sym) (ds : List dyn_annotation) (v : Int)
    (hnm : symOrd m n ≠ .eq) (hv1 : -2147483648 ≤ v) (hv2 : v ≤ 2147483647)
    (f : Fmap sym value) (rest : List (Fmap sym value)) (hf : SymFrame f)
    (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) intTy bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pv (.own 1) intTy (emittedIntBytes M.tagDefs v) -∗
        Ψ (.pure (lint v)) (envAdd s (lint v)
          (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f)) :: rest))) ⊢
      wpt M p Ls Θ 16 Ψ
        (Expr [Astd "§6.5#2"] (Ebound
          (negAssignBody [] [] [Astd "§6.5.16.1#2, store"] [] [] ds BTy_unit
            loc empty_annotation intTy (psym n) (CorpusE0.convLoadedInt m) (CorpusE0.convLoadedInt m) NA)))
        (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f) :: rest) := by
  have hlp := t1sym_eval hex rest (by
    rw [envAdd_lookup (hf.add m (lint v)), if_pos (symOrd_self n)] :
      fmapLookupBy symCmpK n (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f)) =
        some (Vobject (OVpointer pv)))
  have hlv := t1ConvLoadedInt_eval hstd (t1sym_eval hex rest (by
    rw [envAdd_lookup (hf.add m (lint v)), if_neg hnm, envAdd_lookup hf, if_pos (symOrd_self m)] :
      fmapLookupBy symCmpK m (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f)) = some (lint v))) hv1 hv2
  exact wpt_neg_bound [Astd "§6.5#2"] [] [] [Astd "§6.5.16.1#2, store"] [] [] ds BTy_unit
    loc empty_annotation intTy (psym n) (CorpusE0.convLoadedInt m) (CorpusE0.convLoadedInt m) NA
    (envAdd n (Vobject (OVpointer pv)) (envAdd m (lint v) f)) rest ((hf.add _ _).add _ _)
    (emittedIntMval v) bs (Nat.le_refl 16) hex rfl hlp hlv rfl hlv
    (emittedInt_encodes _ v) (emittedInt_storable _ v)

end CerberusHeapLang
