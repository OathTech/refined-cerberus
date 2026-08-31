/-
CerberusHeapLang.Lang — the iris-lean `Language` instance over
the fragment's Step (recon §5.3: the Language-instance route, R3 —
inherits the full mask/fupd WP; HeapLang's instantiation is the
template, Iris/HeapLang/Instances.lean + PrimitiveLaws.lean:59-90).

PHASE-1 S1: the language expression is the runtime TUPLE `CoreRt`
(Core expression + live env stack) and values are `CoreRVal`
(SpikeVal + final env) — the probe's componentwise `TRt`/`TRVal`
pattern (StmtProbe/Toy.lean:445-460), minus the label-map component
(S3's frozen-context restatement). `toVal`/`ofVal` act
componentwise; the partial-bijection laws lift pointwise.

- Observations: `Empty` (the fragment forks no threads and emits no
  observations; every `List Empty` is `[]`).
- The one deliberate structural point: `Language.Context` holds for
  the Esseq frame (so Iris's wp_bind applies to real strong
  sequencing), but NOT for the Eannot frame: an annot-rooted body
  steps by the ANNOTS merge, not in context, so
  `Context.primStep_fill` fails there. The Eannot layer is handled by
  a dedicated commuting lemma in Rules.lean (wp_annot), not by bind.
  S3 NOTE (restratification): the instance is TRUE for the phase-1
  (jump-free) relation and remains certified; the S3 global jump rule
  FALSIFIES it (readiness R1 — a jump of e1 and of `Esseq pat e1 e2`
  step to the SAME configuration), so S3 retires the instance. The
  stratified sequencing route (Wps.lean `wps_seq`, and `wp_sseq`'s
  factor-theorem proof in Rules.lean) does not use it.

SOUNDNESS STATUS: the WP is over Step; Step's certification against
the engine is Soundness.lean, and the engine-facing meaning lands
through Adequacy.lean (SemTriple / semantic_triple_sound).
-/
import CerberusHeapLang.Heap

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic

/-- Every list of `Empty` observations is empty. -/
theorem List.empty_eq_nil (l : List Empty) : l = [] := by
  cases l with
  | nil => rfl
  | cons e _ => exact e.elim

instance : Language CoreRt Mem Empty CoreRVal where
  primStep := fun p _obs q =>
    Step (p.1.e, p.1.ρ, p.2) (q.1.e, q.1.ρ, q.2.1) ∧ q.2.2 = []
  toVal := toValRt
  ofVal := ofValRt
  coe_of_toVal_eq_some {r v} h := by
    obtain ⟨e, ρ⟩ := r
    rw [toValRt_mk] at h
    cases he : toVal e with
    | none => rw [he] at h; cases h
    | some w =>
      rw [he] at h
      cases h
      show ofValRt ⟨w, ρ⟩ = ⟨e, ρ⟩
      rw [ofValRt_mk, ofVal_of_toVal he]
  toVal_coe v := by
    obtain ⟨w, ρ⟩ := v
    rw [ofValRt_mk, toValRt_mk, toVal_ofVal]
    rfl
  val_stuck {r σ obs r' σ' eₜ} h := by
    obtain ⟨e, ρ⟩ := r
    show toValRt ⟨e, ρ⟩ = none
    rw [toValRt_mk, Step.toVal_none h.1]
    rfl

@[simp] theorem primStep_eq (r : CoreRt) (σ : Mem) (obs : List Empty)
    (r' : CoreRt) (σ' : Mem) (efs : List CoreRt) :
    (PrimStep.primStep (r, σ) obs (r', σ', efs) : Prop) ↔
      (Step (r.e, r.ρ, σ) (r'.e, r'.ρ, σ') ∧ efs = []) := Iff.rfl

/-- Values-side sanity: `toVal` on the Language instance is the
    componentwise `toValRt`. -/
theorem language_toVal_eq (r : CoreRt) :
    ToVal.toVal (Val := CoreRVal) r = toValRt r := rfl

/-- The strong-sequencing frame is an iris-lean evaluation context:
    wp_bind for real Esseq comes from this instance (get_ctx Esseq
    arm + apply_ctx Csseq, Core_reduction.lean:375,389). TRUE for the
    phase-1 jump-free relation; RETIRED by S3 (header note). -/
instance instContextSseq (a : List annot) (pat : pattern) (e2 : CoreExpr) :
    Language.Context (fun r : CoreRt => ⟨Expr a (Esseq pat r.e e2), r.ρ⟩) where
  toVal_eq_none_fill {r} _ := rfl
  primStep_fill {r σ obs r' σ' eₜ} h :=
    ⟨Step.sseq_ctx h.1, h.2⟩
  primStep_fill_inv {r σ obs Kr' σ' eₜ} hv h := by
    obtain ⟨hstep, hefs⟩ := h
    have hv' : toVal r.e = none := by
      rw [language_toVal_eq] at hv
      obtain ⟨e, ρ⟩ := r
      rw [toValRt_mk] at hv
      cases he : toVal e with
      | none => rfl
      | some w => rw [he] at hv; cases hv
    rcases hstep.sseq_inv with ⟨e1', ρ', σ'', hs, hout⟩ |
        ⟨_, _, v, _, _, hpat, he1, _, _⟩ | ⟨_, _, _, v, _, _, hpat, he1, _, _⟩
    · obtain ⟨he, hρ, hσ⟩ :
          Kr'.e = Expr a (Esseq pat e1' e2) ∧ Kr'.ρ = ρ' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst hσ
      refine ⟨⟨e1', ρ'⟩, ?_, hs, hefs⟩
      obtain ⟨Ke, Kρ⟩ := Kr'
      simp only at he hρ
      rw [he, hρ]
    · rw [he1, toVal_ofVal] at hv'; cases hv'
    · rw [he1, toVal_ofVal] at hv'; cases hv'

/-! ## Determinism / reducibility facts for the pure steps

These feed `wp_lift_pure_det_step_no_fork` (Lifting.lean:171) — the
beta and merge steps are deterministic, state-independent taus. The
beta facts are stated at cons-shaped env stacks: the betas fire only
there (Step.lean header note 1 — the empty-env panic channel is
mirrored as absence of a step). -/

/-- The Esseq wildcard beta on a bare value is a pure deterministic
    step (LETS-PURE). -/
theorem sseq_pure_det {a pa : List annot} {bty : core_base_type} {v : value}
    {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {σ : Mem} {obs : List Empty} {r' : CoreRt} {σ' : Mem} {eₜ : List CoreRt}
    (h : PrimStep.primStep
      ((⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.pure v)) e2),
        ev0 :: evs⟩ : CoreRt), σ) obs (r', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧ r' = (⟨e2, ev0 :: evs⟩ : CoreRt) ∧ eₜ = [] := by
  obtain ⟨hstep, hefs⟩ := h
  rcases hstep.sseq_inv with ⟨e1', ρ'', σ'', hs, hout⟩ |
      ⟨_, _, w, _, _, hp, he, _, hout⟩ | ⟨_, _, ds, w, _, _, hp, he, _, hout⟩
  · exact absurd hs (fun hs => Step.val_elim hs)
  · obtain ⟨h1, h2, h3⟩ : r'.e = e2 ∧ r'.ρ = ev0 :: evs ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    refine ⟨List.empty_eq_nil obs, h3, ?_, hefs⟩
    obtain ⟨re, rρ⟩ := r'
    simp only at h1 h2
    rw [h1, h2]
  · -- a bare value form cannot be the annot value form
    exact absurd he (by simp [ofVal])

/-- The Esseq wildcard beta on an annot value is a pure deterministic
    step (LETS-ANNOT). -/
theorem sseq_annot_det {a pa : List annot} {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    {obs : List Empty} {r' : CoreRt} {σ' : Mem} {eₜ : List CoreRt}
    (h : PrimStep.primStep
      ((⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.annot ds v)) e2),
        ev0 :: evs⟩ : CoreRt), σ) obs (r', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧
      r' = (⟨Expr [] (Eannot ds e2), ev0 :: evs⟩ : CoreRt) ∧ eₜ = [] := by
  obtain ⟨hstep, hefs⟩ := h
  rcases hstep.sseq_inv with ⟨e1', ρ'', σ'', hs, hout⟩ |
      ⟨_, _, w, _, _, hp, he, _, hout⟩ | ⟨_, _, ds', w, _, _, hp, he, _, hout⟩
  · exact absurd hs (fun hs => Step.val_elim hs)
  · exact absurd he (by simp [ofVal])
  · obtain ⟨hds, -⟩ : ds = ds' ∧ v = w := by simpa [ofVal] using he
    subst hds
    obtain ⟨h1, h2, h3⟩ : r'.e = Expr [] (Eannot ds e2) ∧
        r'.ρ = ev0 :: evs ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    refine ⟨List.empty_eq_nil obs, h3, ?_, hefs⟩
    obtain ⟨re, rρ⟩ := r'
    simp only at h1 h2
    rw [h1, h2]

/-- The ANNOTS merge is a pure deterministic step (any env — the
    merge never reads it). -/
theorem annot_merge_det {a1 a2 : List annot} {ds1 ds2 : List dyn_annotation}
    {b : CoreExpr} {ρ : EnvStack} {σ : Mem} {obs : List Empty}
    {r' : CoreRt} {σ' : Mem} {eₜ : List CoreRt}
    (h : PrimStep.primStep
      ((⟨Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), ρ⟩ : CoreRt), σ)
      obs (r', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧
      r' = (⟨Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b), ρ⟩ : CoreRt) ∧ eₜ = [] := by
  obtain ⟨hstep, hefs⟩ := h
  rcases hstep.annot_inv with ⟨hg, b', ρ'', σ'', hs, hout⟩ |
      ⟨a2', ds2', c, hb, hout⟩
  · simp [annotRooted] at hg
  · obtain ⟨rfl, rfl, rfl⟩ : a2 = a2' ∧ ds2 = ds2' ∧ b = c := by
      simpa using hb
    obtain ⟨h1, h2, h3⟩ : r'.e = Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b) ∧
        r'.ρ = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    refine ⟨List.empty_eq_nil obs, h3, ?_, hefs⟩
    obtain ⟨re, rρ⟩ := r'
    simp only at h1 h2
    rw [h1, h2]

/-! ## The Iris ghost-state instance -/

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- Mirror of HeapLang's IrisGS_gen instance
    (PrimitiveLaws.lean:82-88): no per-step later credits beyond the
    base one, trivial fork postcondition (nothing forks), and a
    step-count-insensitive state interpretation. -/
instance instIrisGS [SpikeGS hlc GF] : IrisGS_gen hlc CoreRt GF where
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

end CerberusHeapLang
