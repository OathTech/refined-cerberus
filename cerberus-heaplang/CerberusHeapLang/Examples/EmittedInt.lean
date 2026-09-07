/-
Shared public-rule derivations for the emitted integer expression shapes.
Locations and temporary symbols are parameters, so clients retain their
original AST while sharing the memory and environment proof plumbing.

Example support (module_classes.tsv): it imports core modules and the corpus
transcriptions only — never a client. The evaluator/redex lemmas the emitted
corpus clients share (`specInt_eval`, `t1ConvLoadedInt_eval`, `t1sym_eval`,
`createInt_eq`, `act_store_eq`, `act_load_eq`, `prod_two_int_budget_fits` from
CorpusT1Exhibit; `t5CmpBranch`/`t5CmpBranch_eval`,
`t5Tuple_eval`, `t5frAssign` from CorpusT5Exhibit) were relocated here at the
L1 landing (2026-09-07) so that CorpusT1Exhibit is not imported by example
support and CorpusT5Exhibit is not imported by CorpusT4/T6Exhibit; their
names and statements are unchanged.
-/
import CerberusHeapLang.Examples.CorpusE0
import CerberusHeapLang.IntRules
import CerberusHeapLang.Wpt
import CerberusHeapLang.ProdEntry

set_option autoImplicit false
namespace CerberusHeapLang
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (emittedIntLoad ptrTy psym letW act intCty specInt convLoadedInt createInt t5a t5Tuple)

variable {GF : BundledGFunctors}

/-! ## Evaluator and redex lemmas shared by the emitted-corpus clients
(relocated from CorpusT1Exhibit / CorpusT5Exhibit; statements unchanged) -/

theorem specInt_eval {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {file : generic_file Unit core_run_annotation} (ρ : EnvStack) (n : Int) :
    evalPexpr tds ext file ρ (specInt n) = some (lint n) := by
  rw [specInt, evalPexpr_ctor1, evalPexpr_val]
  rfl

/-- `conv_loaded_int('signed int', a)` at a bound in-range `Specified(n)` (the
    E3 evaluator lemma at t1's operand spelling — `intCty` is `sintTy`'s
    literal). -/
theorem t1ConvLoadedInt_eval {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {file : generic_file Unit core_run_annotation} (hstd : StdE3 file) {ρ : EnvStack}
    {a : sym} {n : Int} (hv : evalPexpr tds ext file ρ (psym a) = some (lint n))
    (h1 : -2147483648 ≤ n) (h2 : n ≤ 2147483647) :
    evalPexpr tds ext file ρ (convLoadedInt a) = some (lint n) :=
  evalPexpr_convLoadedInt_spec [] hstd (by rw [intCty, evalPexpr_val]; rfl) hv h1 h2

/-- The symbol operand at a frame whose lookup is known (the `symC_eval` of
    EmittedCExhibit.lean at t1's spelling `psym`). -/
theorem t1sym_eval {M : MachineCtx} (hex : ∀ x, resolveExtern M.extern x = x)
    {x : sym} {f : Fmap sym value} {v : value} (evs : List (Fmap sym value))
    (hl : fmapLookupBy symCmpK x f = some v) :
    evalPexpr M.tagDefs M.extern M.file (f :: evs) (psym x) = some v := by
  rw [CorpusE0.psym, evalPexpr_sym_of_resolve _ _ _ (hex _)]
  exact lookup_env_head hl evs

/-! The transcription's action nodes in the rules' redex spellings (`rfl`). -/

theorem createInt_eq (loc : CerbLocation.Loc) (x : sym) :
    createInt loc x = createOpRedex [] loc empty_annotation
      (Pexpr [] () (PEctor Civalignof [intCty])) intCty (PrefSource loc [x]) := rfl
theorem act_store_eq (loc : CerbLocation.Loc) (pe2 pe3 : generic_pexpr Unit sym) :
    act loc (Store0 false intCty pe2 pe3 NA) = storeOpRedex [] loc empty_annotation intTy pe2 pe3 NA := rfl
theorem act_load_eq (loc : CerbLocation.Loc) (pe2 : generic_pexpr Unit sym) :
    act loc (Load0 intCty pe2 NA) = loadOpRedex [] loc empty_annotation intTy pe2 NA := rfl

/-- The two `int` cells' summed budget fits the production cold-start
    cursor's headroom (closed arithmetic). -/
theorem prod_two_int_budget_fits :
    allocCost fmapEmpty intTy 4 + allocCost fmapEmpty intTy 4 ≤ headroom prodMem₀.lastAddress := by
  rw [prodMem₀_lastAddress]
  decide

/-- The specified branch after substituting its two integer payloads. -/
def t5CmpBranch (op : binop) (x y : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEif
    (Pexpr [] () (PEop op
      (Pexpr [] () (PEcall (Sym convIntSym) [intCty, ointPe x]))
      (Pexpr [] () (PEcall (Sym convIntSym) [intCty, ointPe y]))))
    (specInt 1) (specInt 0))

theorem t5CmpBranch_eval {M : MachineCtx} (hstd : StdE3 M.file) (ρ : EnvStack)
    (op : binop) (x y : Int) (b : Bool)
    (hx1 : -2147483648 ≤ x) (hx2 : x ≤ 2147483647)
    (hy1 : -2147483648 ≤ y) (hy2 : y ≤ 2147483647)
    (hop : evalBinop op (oint x) (oint y) = some (if b then Vtrue else Vfalse)) :
    evalPexpr M.tagDefs M.extern M.file ρ (t5CmpBranch op x y) =
      some (lint (if b then 1 else 0)) := by
  unfold t5CmpBranch
  rw [evalPexpr_if, if_pos (show (isPePure (specInt 1) && isPePure (specInt 0)) = true from rfl), evalPexpr_op,
    evalPexpr_convInt_call_int [] hstd (by rw [intCty, evalPexpr_val]; rfl)
      (by rw [ointPe, evalPexpr_val]) hx1 hx2,
    evalPexpr_convInt_call_int [] hstd (by rw [intCty, evalPexpr_val]; rfl)
      (by rw [ointPe, evalPexpr_val]) hy1 hy2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hop]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_some] <;>
    exact specInt_eval ρ _

theorem t5Tuple_eval {M : MachineCtx} {ρ : EnvStack} (n m : Nat) (v w : value)
    (hn : evalPexpr M.tagDefs M.extern M.file ρ (psym (t5a n)) = some v)
    (hm : evalPexpr M.tagDefs M.extern M.file ρ (psym (t5a m)) = some w) :
    evalPexpr M.tagDefs M.extern M.file ρ (t5Tuple n m) = some (Vtuple [v, w]) := by
  rw [t5Tuple, evalPexpr_ctor2, hn, hm]
  rfl

/-- The frame after an emitted assignment's mixed tuple binder: the pointer
    temporary `a_n` and the value temporary `a_m`. -/
abbrev t5frAssign (n m : Nat) (v : Int) (pr : CerbMem.PointerValue) (f : Fmap sym value) :=
  envAdd (t5a n) (Vobject (OVpointer pr)) (envAdd (t5a m) (lint v) f)

/-! ## The shared integer load/store derivations -/

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
