/-
The emitted t4_while execution proof, in progress. This checkpoint checks
the four continuations against the engine collector and their fragment
and potential obligations. There is no production result in this module
yet; the public total loop derivation remains to be completed.
-/
import CerberusHeapLang.CorpusT5Exhibit

set_option autoImplicit false
namespace CerberusHeapLang
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Maybe Lem_List
open CorpusE0 (t4Load t4Reg t4iSym t4sSym t4RetSym t4ContinueSym t4BreakSym t4WhileSym
  t4LoopTest t4While t4AfterWhile t4Return t4Main t5a t5Unit t5Pure
  ptrTy psym seqE letS wc)

variable {GF : BundledGFunctors}

theorem wpt_t4Load [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (hex : ∀ x, resolveExtern M.extern x = x)
    (x : sym) (tmp c1 c2 : Nat) (f : Fmap sym value) (rest : List (Fmap sym value))
    (hf : SymFrame f) (pv : CerbMem.PointerValue) (bs : List CerbMem.AbsByte)
    (v : value) (hl : fmapLookupBy symCmpK x f = some (Vobject (OVpointer pv)))
    (hload : loadedVal M.tagDefs pv intTy bs = v)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) intTy bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) intTy bs -∗
        Ψ (.annot [DA_pos [] fp] v) (envAdd (t5a tmp) (Vobject (OVpointer pv)) f :: rest))) ⊢
      wpt M p Ls Θ 6 Ψ (t4Load x tmp c1 c2) (f :: rest) :=
  wpt_emittedIntLoad hex (t4Reg c1 c2) x (t5a tmp) f rest hf pv bs v hl hload htrap

/-- The suffix outside the while save belongs to each label in its body. -/
def t4LoopContext (body : CoreExpr) : CoreExpr :=
  seqE (Expr [Aloc (t4Reg 39 87), Astmt] (Esseq wc body t4AfterWhile)) t4Return

def t4WhileCont : CoreExpr := t4LoopContext t4LoopTest
def t4ContinueCont : CoreExpr := t4LoopContext
  (seqE (seqE (Expr [Aloc (t4Reg 39 87), Astmt] (Epure (Pexpr [] () (PEval Vunit)))) t5Unit)
    (Expr [] (Erun empty_annotation t4WhileSym [psym t4iSym, psym t4sSym])))
def t4BreakCont : CoreExpr :=
  seqE (seqE (Expr [Aloc (t4Reg 39 87), Astmt] (Epure (Pexpr [] () (PEval Vunit)))) t5Unit) t4Return
def t4RetCont : CoreExpr := t5Pure (psym (t5a 574))
def t4PtrParams : List (sym × core_base_type) := [(t4iSym, ptrTy), (t4sSym, ptrTy)]
def t4RetParams : List (sym × core_base_type) := [(t5a 574, CorpusE0.lint)]

def t4Q : LabelMap := collect_saves t4Main

theorem t4Q_while : lookupLabel t4Q t4WhileSym = some (t4PtrParams, t4WhileCont) := rfl
theorem t4Q_continue : lookupLabel t4Q t4ContinueSym = some (t4PtrParams, t4ContinueCont) := rfl
theorem t4Q_break : lookupLabel t4Q t4BreakSym = some (t4PtrParams, t4BreakCont) := rfl
theorem t4Q_ret : lookupLabel t4Q t4RetSym = some (t4RetParams, t4RetCont) := rfl

theorem t4Q_eq : t4Q =
    fmapAddBy symCmpL t4BreakSym (t4PtrParams, t4BreakCont)
    (fmapAddBy symCmpL t4ContinueSym (t4PtrParams, t4ContinueCont)
    (fmapAddBy symCmpL t4WhileSym (t4PtrParams, t4WhileCont)
    (fmapAddBy symCmpL t4RetSym (t4RetParams, t4RetCont) fmapEmpty))) := rfl

theorem t4Q_lookup (l : sym) : lookupLabel t4Q l =
    if symOrd l t4BreakSym = .eq then some (t4PtrParams, t4BreakCont)
    else if symOrd l t4ContinueSym = .eq then some (t4PtrParams, t4ContinueCont)
    else if symOrd l t4WhileSym = .eq then some (t4PtrParams, t4WhileCont)
    else if symOrd l t4RetSym = .eq then some (t4RetParams, t4RetCont)
    else none := by
  rw [t4Q_eq]
  unfold lookupLabel
  rw [labelAdd_lookup (((symMap_empty.addLabel _ _).addLabel _ _).addLabel _ _),
    labelAdd_lookup ((symMap_empty.addLabel _ _).addLabel _ _),
    labelAdd_lookup (symMap_empty.addLabel _ _), labelAdd_lookup symMap_empty]
  rfl

theorem t4Q_cont {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t4Q l = some (params, cont)) :
    cont ∈ [t4ContinueCont, t4WhileCont, t4BreakCont, t4RetCont] := by
  rw [t4Q_lookup] at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · split at h
        · cases h; simp
        · cases h

theorem t4LoopContext_frag (body : CoreExpr) (hb : Frag body) : Frag (t4LoopContext body) :=
  .sseq (.sseq hb (.sseq (CorpusE0.t4Save_frag _ _ (.val_pure _)) (.val_pure _))) CorpusE0.t4Return_frag

theorem t4Q_frag {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t4Q l = some (params, cont)) : Frag cont := by
  have hc := t4Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · refine t4LoopContext_frag _ (.sseq (.sseq (.val_pure _) (.val_pure _)) (.run ?_ ?_))
    · intro pe hpe
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      rcases hpe with rfl | rfl <;> exact .sym _ _
    · intro pe hpe
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      rcases hpe with rfl | rfl <;> exact peDepth_sym_le _ _
  · exact t4LoopContext_frag _ (.sseq_sym CorpusE0.t4Cond_frag (.sseq_sym CorpusE0.t4Bool_frag
      (.if_ (.sym _ _) (peDepth_sym_le _ _) CorpusE0.t4Body_frag (.val_pure _))))
  · exact .sseq (.sseq (.val_pure _) (.val_pure _)) CorpusE0.t4Return_frag
  · exact Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _)

theorem t4Q_pot {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel t4Q l = some (params, cont)) : pot cont ≤ lemDefaultFuel := by
  have hc := t4Q_cont h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl

theorem collect_new_t4Main :
    collect_labeled_continuations_NEW (prodFileLib stdlibE3 [] t4Main) =
      fmapAddBy (fun (s1 s2 : sym) => ordCompare s1 s2) mainSym t4Q fmapEmpty := rfl

theorem t4Main_labeledAt (sup : Nat) :
    LabeledAt (prodRSLib stdlibE3 [] sup t4Main) mainSym t4Q := by
  unfold LabeledAt
  rw [prodRSLib_labeled, collect_new_t4Main, fmapLookupBy_addBy_empty, if_pos (by decide +kernel)]

theorem t4Main_pot : pot t4Main ≤ lemDefaultFuel := Nat.le_of_ble_eq_true rfl

end CerberusHeapLang
