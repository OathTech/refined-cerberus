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
  iapply wpt_load _ _ _ _ pv _ (.own 1) bs _ (Nat.le_refl 3) htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  rw [hload]
  iapply HΨ $$ Hpt

end CerberusHeapLang
