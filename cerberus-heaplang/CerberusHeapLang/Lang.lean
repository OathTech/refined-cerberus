/-
CerberusHeapLang.Lang — the iris-lean `Language` instance over
the fragment's Step (recon §5.3: the Language-instance route, R3 —
inherits the full mask/fupd WP; HeapLang's instantiation is the
template, Iris/HeapLang/Instances.lean + PrimitiveLaws.lean:59-90).

PHASE-1 S1 + PHASE-2 S3: the language expression is the runtime
TUPLE `CoreRt` (Core expression + live env stack + the static
per-procedure label map) and values are `CoreRVal` — the probe's
FULL componentwise `TRt`/`TRVal` pattern (StmtProbe/Toy.lean:
445-460, label map included). `toVal`/`ofVal` act componentwise;
the partial-bijection laws lift pointwise. `primStep` runs `Step`
at the tuple's own label map and PINS the successor's map to it
(`q.1.lbl = p.1.lbl` — the probe's `q.1.fn = p.1.fn`): the engine
never writes `labeled` on the sequential path.

- Observations: `Empty` (the fragment forks no threads and emits no
  observations; every `List Empty` is `[]`).
- S3 RETIREMENT (pre-declared — phase-1 notes §2 item 1, and this
  header's own phase-1 note): the `Language.Context` instance for
  the Esseq frame (`instContextSseq`) is RETIRED. It was TRUE for
  the phase-1 jump-free relation; the S3 global jump rule FALSIFIES
  it (readiness R1 — a jump of e1 and of `Esseq pat e1 e2` step to
  the SAME configuration, so `Context.primStep_fill` fails). The
  sequencing routes in force (Wps.lean `wps_seq`; Rules.lean
  `wp_sseq`'s factor proof) never used it.

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
    Step p.1.lbl (p.1.e, p.1.ρ, p.2) (q.1.e, q.1.ρ, q.2.1) ∧
      q.1.lbl = p.1.lbl ∧ q.2.2 = []
  toVal := toValRt
  ofVal := ofValRt
  coe_of_toVal_eq_some {r v} h := by
    obtain ⟨e, ρ, Q⟩ := r
    rw [toValRt_mk] at h
    cases he : toVal e with
    | none => rw [he] at h; cases h
    | some w =>
      rw [he] at h
      cases h
      show ofValRt ⟨w, ρ, Q⟩ = ⟨e, ρ, Q⟩
      rw [ofValRt_mk, ofVal_of_toVal he]
  toVal_coe v := by
    obtain ⟨w, ρ, Q⟩ := v
    rw [ofValRt_mk, toValRt_mk, toVal_ofVal]
    rfl
  val_stuck {r σ obs r' σ' eₜ} h := by
    obtain ⟨e, ρ, Q⟩ := r
    show toValRt ⟨e, ρ, Q⟩ = none
    rw [toValRt_mk, Step.toVal_none h.1]
    rfl

@[simp] theorem primStep_eq (r : CoreRt) (σ : Mem) (obs : List Empty)
    (r' : CoreRt) (σ' : Mem) (efs : List CoreRt) :
    (PrimStep.primStep (r, σ) obs (r', σ', efs) : Prop) ↔
      (Step r.lbl (r.e, r.ρ, σ) (r'.e, r'.ρ, σ') ∧ r'.lbl = r.lbl ∧ efs = []) :=
  Iff.rfl

/-- Values-side sanity: `toVal` on the Language instance is the
    componentwise `toValRt`. -/
theorem language_toVal_eq (r : CoreRt) :
    ToVal.toVal (Val := CoreRVal) r = toValRt r := rfl

/-! RETIRED (S3, pre-declared): `instContextSseq`, the
`Language.Context` instance for the Esseq frame. The S3 global jump
rule falsifies `Context.primStep_fill` — the engine's `Erun`
discards the frame (step_ctx's Erun arm, Core_reduction.lean:484),
so a jump of `e1` and of `Esseq pat e1 e2` step to the SAME
configuration, and a step of the framed term is not always a framed
step. Statement-level fact recording the falsification direction:
`Step.sseq_inv`'s jump disjunct (Step.lean). Nothing in the
sequencing routes used the instance (header note). -/

/-! ## Determinism / reducibility facts for the pure steps

These feed `wp_lift_pure_det_step_no_fork` (Lifting.lean:171) — the
beta and merge steps are deterministic, state-independent taus. The
beta facts are stated at cons-shaped env stacks: the betas fire only
there (Step.lean header note 1 — the empty-env panic channel is
mirrored as absence of a step). -/

/-- The Esseq wildcard beta on a bare value is a pure deterministic
    step (LETS-PURE). -/
theorem sseq_pure_det {Q : LabelMap} {a pa : List annot}
    {bty : core_base_type} {v : value}
    {e2 : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {σ : Mem} {obs : List Empty} {r' : CoreRt} {σ' : Mem} {eₜ : List CoreRt}
    (h : PrimStep.primStep
      ((⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.pure v)) e2),
        ev0 :: evs, Q⟩ : CoreRt), σ) obs (r', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧ r' = (⟨e2, ev0 :: evs, Q⟩ : CoreRt) ∧ eₜ = [] := by
  obtain ⟨hstep, hlbl, hefs⟩ := h
  rcases hstep.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs, hout⟩ |
      ⟨_, _, w, _, _, hp, he, _, hout⟩ | ⟨_, _, ds, w, _, _, hp, he, _, hout⟩ |
      ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
      ⟨_, _, _, _, _, _, hpat, _, _, _⟩
  · exact absurd hs (fun hs => Step.val_elim hs)
  · obtain ⟨h1, h2, h3⟩ : r'.e = e2 ∧ r'.ρ = ev0 :: evs ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    refine ⟨List.empty_eq_nil obs, h3, ?_, hefs⟩
    obtain ⟨re, rρ, rQ⟩ := r'
    simp only at h1 h2 hlbl
    rw [h1, h2, hlbl]
  · -- a bare value form cannot be the annot value form
    exact absurd he (by simp [ofVal])
  · rw [jumpRedex?_ofVal] at hj; cases hj
  · exact (specPat_ne_base hpat).elim
  · exact (specPat_ne_base hpat).elim
  · exact (symPat_ne_base hpat).elim

/-- The Esseq wildcard beta on an annot value is a pure deterministic
    step (LETS-ANNOT). -/
theorem sseq_annot_det {Q : LabelMap} {a pa : List annot}
    {bty : core_base_type}
    {ds : List dyn_annotation} {v : value} {e2 : CoreExpr}
    {ev0 : Fmap sym value} {evs : List (Fmap sym value)} {σ : Mem}
    {obs : List Empty} {r' : CoreRt} {σ' : Mem} {eₜ : List CoreRt}
    (h : PrimStep.primStep
      ((⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty))) (ofVal (.annot ds v)) e2),
        ev0 :: evs, Q⟩ : CoreRt), σ) obs (r', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧
      r' = (⟨Expr [] (Eannot ds e2), ev0 :: evs, Q⟩ : CoreRt) ∧ eₜ = [] := by
  obtain ⟨hstep, hlbl, hefs⟩ := h
  rcases hstep.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs, hout⟩ |
      ⟨_, _, w, _, _, hp, he, _, hout⟩ | ⟨_, _, ds', w, _, _, hp, he, _, hout⟩ |
      ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
      ⟨_, _, _, _, _, _, hpat, _, _, _⟩
  · exact absurd hs (fun hs => Step.val_elim hs)
  · exact absurd he (by simp [ofVal])
  · obtain ⟨hds, -⟩ : ds = ds' ∧ v = w := by simpa [ofVal] using he
    subst hds
    obtain ⟨h1, h2, h3⟩ : r'.e = Expr [] (Eannot ds e2) ∧
        r'.ρ = ev0 :: evs ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    refine ⟨List.empty_eq_nil obs, h3, ?_, hefs⟩
    obtain ⟨re, rρ, rQ⟩ := r'
    simp only at h1 h2 hlbl
    rw [h1, h2, hlbl]
  · rw [jumpRedex?_ofVal] at hj; cases hj
  · exact (specPat_ne_base hpat).elim
  · exact (specPat_ne_base hpat).elim
  · exact (symPat_ne_base hpat).elim

/-- The ANNOTS merge is a pure deterministic step (any env — the
    merge never reads it). -/
theorem annot_merge_det {Q : LabelMap} {a1 a2 : List annot}
    {ds1 ds2 : List dyn_annotation}
    {b : CoreExpr} {ρ : EnvStack} {σ : Mem} {obs : List Empty}
    {r' : CoreRt} {σ' : Mem} {eₜ : List CoreRt}
    (h : PrimStep.primStep
      ((⟨Expr a1 (Eannot ds1 (Expr a2 (Eannot ds2 b))), ρ, Q⟩ : CoreRt), σ)
      obs (r', σ', eₜ)) :
    obs = [] ∧ σ' = σ ∧
      r' = (⟨Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b), ρ, Q⟩ : CoreRt) ∧
      eₜ = [] := by
  obtain ⟨hstep, hlbl, hefs⟩ := h
  rcases hstep.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hs, hout⟩ |
      ⟨a2', ds2', c, hb, hout⟩ |
      ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
  · simp [annotRooted] at hg
  · obtain ⟨rfl, rfl, rfl⟩ : a2 = a2' ∧ ds2 = ds2' ∧ b = c := by
      simpa using hb
    obtain ⟨h1, h2, h3⟩ : r'.e = Expr (a1 ++ a2) (Eannot (ds1 ++ ds2) b) ∧
        r'.ρ = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    refine ⟨List.empty_eq_nil obs, h3, ?_, hefs⟩
    obtain ⟨re, rρ, rQ⟩ := r'
    simp only at h1 h2 hlbl
    rw [h1, h2, hlbl]
  · simp [annotRooted] at hg

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
