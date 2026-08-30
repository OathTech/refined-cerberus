/-
RefinedCerberus.Spike.Lang — the iris-lean `Language` instance over
the fragment's Step (recon §5.3: the Language-instance route, R3 —
inherits the full mask/fupd WP; HeapLang's instantiation is the
template, Iris/HeapLang/Instances.lean + PrimitiveLaws.lean:59-90).

- Observations: `Empty` (the fragment forks no threads and emits no
  observations; every `List Empty` is `[]`).
- Values: `SpikeVal` (Step.lean — bare or one-annot-wrapped value,
  mirroring is_irreducible).
- The one deliberate structural point: `Language.Context` holds for
  the Esseq frame (so Iris's wp_bind applies to real strong
  sequencing — the R6 test), but NOT for the Eannot frame: an
  annot-rooted body steps by the ANNOTS merge, not in context, so
  `Context.primStep_fill` fails there. The Eannot layer is handled by
  a dedicated commuting lemma in Rules.lean (wp_annot), not by bind.

SOUNDNESS STATUS: the WP is over Step; Step's certification against
the engine is Soundness.lean, and the engine-facing meaning lands
through Adequacy.lean (SemTriple / semantic_triple_sound).
-/
import RefinedCerberus.Spike.Heap

set_option autoImplicit false

namespace RefinedCerberus.Spike

open Iris Iris.ProgramLogic

/-- Every list of `Empty` observations is empty. -/
theorem List.empty_eq_nil (l : List Empty) : l = [] := by
  cases l with
  | nil => rfl
  | cons e _ => exact e.elim

instance : Language CoreExpr Mem Empty SpikeVal where
  primStep := fun p _obs q => Step (p.1, p.2) (q.1, q.2.1) ∧ q.2.2 = []
  toVal := toVal
  ofVal := ofVal
  coe_of_toVal_eq_some := ofVal_of_toVal
  toVal_coe := toVal_ofVal
  val_stuck := fun h => h.1.toVal_none

@[simp] theorem primStep_eq (e : CoreExpr) (σ : Mem) (obs : List Empty)
    (e' : CoreExpr) (σ' : Mem) (efs : List CoreExpr) :
    (PrimStep.primStep (e, σ) obs (e', σ', efs) : Prop) ↔
      (Step (e, σ) (e', σ') ∧ efs = []) := Iff.rfl

/-- Values-side sanity: `toVal` on the Language instance is the
    Step.lean `toVal`. -/
theorem language_toVal_eq (e : CoreExpr) :
    ToVal.toVal (Val := SpikeVal) e = toVal e := rfl

/-- The strong-sequencing frame is an iris-lean evaluation context:
    wp_bind for real Esseq comes from this instance (get_ctx Esseq
    arm + apply_ctx Csseq, Core_reduction.lean:375,389). -/
instance instContextSseq (a : List annot) (pat : pattern) (e2 : CoreExpr) :
    Language.Context (fun e => Expr a (Esseq pat e e2)) where
  toVal_eq_none_fill {e} _ := rfl
  primStep_fill {e σ obs e' σ' eₜ} h :=
    ⟨Step.sseq_ctx h.1, h.2⟩
  primStep_fill_inv {e σ obs Ke' σ' eₜ} hv h := by
    obtain ⟨hstep, hefs⟩ := h
    rcases hstep.sseq_inv with ⟨e1', σ'', hs, hout⟩ | ⟨_, _, v, _, rfl, _⟩ |
        ⟨_, _, _, v, _, rfl, _⟩
    · cases hout
      exact ⟨e1', rfl, hs, hefs⟩
    · rw [language_toVal_eq, toVal_ofVal] at hv; cases hv
    · rw [language_toVal_eq, toVal_ofVal] at hv; cases hv

/-! ## Determinism / reducibility facts for the pure steps

These feed `wp_lift_pure_det_step_no_fork` (Lifting.lean:171) — the
beta and merge steps are deterministic, state-independent taus. -/

/-- The Esseq wildcard beta on a bare value is a pure deterministic
    step (LETS-PURE). -/
theorem sseq_pure_det {a pa : List annot} {bty : core_base_type} {v : value}
    {e2 : CoreExpr} {σ : Mem} {obs : List Empty} {e' : CoreExpr} {σ' : Mem}
    {eₜ : List CoreExpr}
    (h : PrimStep.primStep
      (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.pure v)) e2), σ)
      obs (e', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧ e' = e2 ∧ eₜ = [] := by
  obtain ⟨hstep, hefs⟩ := h
  rcases hstep.sseq_inv with ⟨e1', σ'', hs, hout⟩ | ⟨_, _, w, hp, he, hout⟩ |
      ⟨_, _, ds, w, hp, he, hout⟩
  · exact absurd hs (fun hs => Step.val_elim hs)
  · injection hout with h1 h2
    exact ⟨List.empty_eq_nil obs, h2, h1, hefs⟩
  · -- a bare value form cannot be the annot value form
    exact absurd he (by simp [ofVal])

/-- The Esseq wildcard beta on an annot value is a pure deterministic
    step (LETS-ANNOT). -/
theorem sseq_annot_det {a pa : List annot} {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr} {σ : Mem}
    {obs : List Empty} {e' : CoreExpr} {σ' : Mem} {eₜ : List CoreExpr}
    (h : PrimStep.primStep
      (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.annot ds v)) e2), σ)
      obs (e', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧ e' = Expr [] (Eannot ds e2) ∧ eₜ = [] := by
  obtain ⟨hstep, hefs⟩ := h
  rcases hstep.sseq_inv with ⟨e1', σ'', hs, hout⟩ | ⟨_, _, w, hp, he, hout⟩ |
      ⟨_, _, ds', w, hp, he, hout⟩
  · exact absurd hs (fun hs => Step.val_elim hs)
  · exact absurd he (by simp [ofVal])
  · obtain ⟨hds, -⟩ : ds = ds' ∧ v = w := by simpa [ofVal] using he
    subst hds
    injection hout with h1 h2
    exact ⟨List.empty_eq_nil obs, h2, h1, hefs⟩

/-- The ANNOTS merge is a pure deterministic step. -/
theorem annot_merge_det {a1 a2 : List annot} {ds1 ds2 : List dyn_annotation}
    {b : CoreExpr} {σ : Mem} {obs : List Empty} {e' : CoreExpr} {σ' : Mem}
    {eₜ : List CoreExpr}
    (h : PrimStep.primStep
      (Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), σ) obs (e', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧ e' = Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b) ∧ eₜ = [] := by
  obtain ⟨hstep, hefs⟩ := h
  rcases hstep.annot_inv with ⟨hg, b', σ'', hs, hout⟩ | ⟨a2', ds2', c, hb, hout⟩
  · simp [annotRooted] at hg
  · obtain ⟨rfl, rfl, rfl⟩ : a2 = a2' ∧ ds2 = ds2' ∧ b = c := by
      simpa using hb
    injection hout with h1 h2
    exact ⟨List.empty_eq_nil obs, h2, h1, hefs⟩

/-! ## The Iris ghost-state instance -/

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- Mirror of HeapLang's IrisGS_gen instance
    (PrimitiveLaws.lean:82-88): no per-step later credits beyond the
    base one, trivial fork postcondition (nothing forks), and a
    step-count-insensitive state interpretation. -/
instance instIrisGS [SpikeGS hlc GF] : IrisGS_gen hlc CoreExpr GF where
  invGS := SpikeGS.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    letI := @SpikeGS.invGS hlc GF _
    iintro $

/-! ## Non-vacuity witness for the ghost-state prerequisites

A concrete functor list satisfying `SpikeGpreS` (mirror of HeapLangS,
PrimitiveLaws.lean:94-126, minus prophecies). The bundled `SpikeGS`
(ghost NAMES + world satisfaction) is constructed by allocation inside
the adequacy proof, exactly as HeapLang's `heap_adequacy` does — that
construction is slice B's adequacy obligation. -/

def SpikeGF : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨_root_.Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Int (Agree (DiscreteO SpikeCell)) SpikeHeapF),
          by infer_instance⟩
  | 5 => ⟨constOF (HeapView Int (Agree (DiscreteO GName)) SpikeHeapF),
          by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instSpikeGpreS_SpikeGF : SpikeGpreS SpikeGF where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6

end RefinedCerberus.Spike
