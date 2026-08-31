/-
CerberusHeapLang.Wps — phase-1 S2: the STATEMENT-STRATIFIED WP over
the real Core fragment (the probe's architecture, StmtProbe/Wps.lean,
migrated off the toy — two-phase arc plan
docs/2026-08-31_two-phase-arc-plan.md; prescription: probe report
docs/2026-08-31_s0-probe-report.md §6).

THE SHAPE: the classical LABEL-CONTEXT statement logic (de Bruin
1981-style label-assumption judgments), realized as a guarded
fixpoint over the fragment's Step via iris-lean's PUBLIC Banach
machinery (`fixpoint`/`OFE.Contractive` — the same machinery `wp`
itself is built from; iris-lean untouched; adjudicated in-bounds,
docs/2026-08-31_s0-adjudication.md). `wps Q Ls Ψ e ρ` is indexed by

- `Q : LabelMap` — the STATIC label map (per-procedure registered
  continuations; the engine's `labeled_continuations`,
  Core_run_aux.lean:186-187 — Caesium `f_code`'s analog). S3 ties it
  to `core_run_state.labeled` at the current procedure by a pure
  equation (the donor's `⌜Q = rf.f_code⌝`, lifting.v:1002 —
  legitimate because nothing writes `labeled` on the positive
  sequential path).
- `Ls : LabelSpec GF` — the per-label preconditions, indexed by the
  jump-argument values (the probe's `Ls : Nat → Int → IProp`,
  list-valued for Erun's argument list).

PHASE-1 HONESTY — THE JUMP CLAUSE IS ABSENT (the sanctioned
"honest absence", arc plan / mission order): the fragment is
branch-free sequential (no Erun rule in Step, no registered-label
consultation), so `wps.pre` has TWO clauses (value / step) and the
label context RIDES uncertified. S3 (phase 2) adds the jump clause
(at the Core `jumpRedex?` over the Esseq/Eannot frames), the
`wps_run`/`blockSpecs` machinery, and the two engine-certification
lemmas (the factor theorem's jump disjunct + the jump-redex
inversion — probe report §6 S3); `wps_sound` then gains the
`blockSpecs` premise (its phase-1 statement is the jump-free
collapse, unconditional). Every OTHER statement below — the (Q, Ls)
parameters in particular — is stated so S3's clause insertion is a
definition-local delta: the rule STATEMENTS survive verbatim, their
proofs gain one case each.

WHAT MIGRATES HERE (probe §4 coverage preservation, now on the REAL
fragment): the small axioms (`wps_store`/`wps_load` — the house
`storeM_success`/`loadM_success` engine seams reused verbatim inside
the step clause), the jump-aware-SHAPED sequencing rule `wps_seq`
(its jump case arrives with S3; the phase-1 proof is the
value/annot-beta/step three-way), the annotation-commuting layer
(`wps_annot_reindex`/`wps_annot` — the R-i cost re-paid once at this
stratum), structural rules (`wps_wand`/`wps_frame`), the collapse
`wps_sound` into the base Iris WP (the sole adequacy interface), and
the two corpus exhibit shapes over an ARBITRARY label context.

NO `wps_create`: no create small axiom exists at ANY layer
(registered design finding D26, ProdEntry.lean header — a sound one
needs the allocator-cursor resource in the state interpretation,
phase 2's item). Cold-start creates ride the production entry
(prod_run_eq / sem_triple_prod) unchanged.
-/
import CerberusHeapLang.Rules

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

/-! ## The label context (riding parameters — header note) -/

/-- The static label map: the engine's per-procedure registered
    continuations (`labeled_continuations core_run_annotation`,
    Core_run_aux.lean:186 — label ↦ (parameters, sseq-extended
    body)). Populated once by `collect_labeled_continuations_NEW`
    (Core_aux.lean:843/853), never written on the sequential path. -/
abbrev LabelMap : Type := labeled_continuations core_run_annotation

/-- Per-label preconditions, indexed by the jump-argument values
    (probe `Ls`, list-valued for Erun's argument list). -/
abbrev LabelSpec (GF : BundledGFunctors) : Type :=
  sym → List value → IProp GF

/-! ## Per-constructor value-test facts (match-reduction discipline) -/

@[simp] theorem toVal_sseq_node (a : List annot) (pat : pattern)
    (e1 e2 : CoreExpr) : toVal (Expr a (Esseq pat e1 e2)) = none := rfl

@[simp] theorem toVal_action_node (a : List annot)
    (p : generic_paction core_run_annotation Unit sym) :
    toVal (Expr a (Eaction p)) = none := rfl

variable {hlc : HasLC} {GF : BundledGFunctors}

/-! ## The statement WP -/

/-- One unfolding of the statement WP. Phase 1: two clauses — value /
    step (header note: the jump clause is S3's, at the Core
    `jumpRedex?`). The step clause is the base `wp_lift_step` premise
    shape at this instance's `numLatersPerStep = 0`, minus forks
    (the fragment forks nothing — `primStep` pins `eₜ = []`). -/
def wps.pre [SpikeGS hlc GF] (Q : LabelMap) (Ls : LabelSpec GF)
    (F : (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr) (ρ : EnvStack) :
    IProp GF :=
  match toVal e with
  | some w => iprop(|={⊤}=> Ψ w ρ)
  | none =>
    iprop(∀ (σ₁ : Mem) (ns : Nat) (obs obs' : List Empty) (nt : Nat),
      stateInterp σ₁ ns (obs ++ obs') nt ={⊤,∅}=∗
      ⌜PrimStep.Reducible ((⟨e, ρ⟩ : CoreRt), σ₁)⌝ ∗
      ▷ ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
        ⌜((⟨e, ρ⟩ : CoreRt), σ₁) -<obs>-> (r, σ₂, eₜ)⌝ -∗ £ 1 ={∅,⊤}=∗
        stateInterp σ₂ (ns + 1) obs' nt ∗ F Ψ r.e r.ρ)

instance wps.pre.contractive [SpikeGS hlc GF] (Q : LabelMap)
    (Ls : LabelSpec GF) :
    OFE.Contractive (wps.pre (GF := GF) Q Ls) where
  distLater_dist := by
    intro n F F' HF Ψ e ρ
    unfold wps.pre
    cases toVal e
    case some => exact .rfl
    case none =>
      refine BI.forall_ne fun σ₁ => ?_
      refine BI.forall_ne fun ns => ?_
      refine BI.forall_ne fun obs => ?_
      refine BI.forall_ne fun obs' => ?_
      refine BI.forall_ne fun nt => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      refine OFE.Contractive.distLater_dist fun m m_n => ?_
      refine BI.forall_ne fun r => ?_
      refine BI.forall_ne fun σ₂ => ?_
      refine BI.forall_ne fun eₜ => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl ?_
      refine BIFUpdate.ne.ne ?_
      refine BI.sep_ne.ne .rfl ?_
      exact HF m m_n _ _ _

/-- The statement WP: guarded fixpoint of `wps.pre` (the same
    construction as iris-lean's own `wp`, WeakestPre.lean:118, and
    the probe's `wps`). -/
def wps [SpikeGS hlc GF] (Q : LabelMap) (Ls : LabelSpec GF) :
    (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF :=
  fixpoint (wps.pre Q Ls)

theorem wps_unfold [SpikeGS hlc GF] {Q : LabelMap} {Ls : LabelSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr} {ρ : EnvStack} :
    wps (GF := GF) Q Ls Ψ e ρ ⊣⊢ wps.pre Q Ls (wps Q Ls) Ψ e ρ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wps.pre Q Ls).toContractiveHom)).dist Ψ e ρ

variable [SpikeGS hlc GF]
variable {Q : LabelMap} {Ls : LabelSpec GF}

/-! ## Structural rules -/

/-- Value rule at the canonical value injections (the donor's Return
    channel / probe `wps_val`). -/
theorem wps_ofVal {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeVal)
    (ρ : EnvStack) :
    Ψ w ρ ⊢ wps Q Ls Ψ (ofVal w) ρ := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toVal_ofVal]
  iintro H
  imodintro
  iexact H

/-- Value-channel inversion at the canonical injections (the wps
    analog of `wp_value_fupd'`'s forward direction). -/
theorem wps_value_inv {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeVal)
    (ρ : EnvStack) :
    wps Q Ls Ψ (ofVal w) ρ ⊢ iprop(|={⊤}=> Ψ w ρ) := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toVal_ofVal]
  iintro H
  iexact H

/-- Monotonicity/consequence in the value channel (probe `wps_wand`;
    S3 note: jump exits are Ψ-independent — the label preconditions
    carry everything across a jump — so the statement survives the
    jump clause verbatim). -/
theorem wps_wand {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr)
    (ρ : EnvStack) :
    wps Q Ls Ψ₁ e ρ ⊢
      iprop((∀ w ρ', Ψ₁ w ρ' -∗ Ψ₂ w ρ') -∗ wps Q Ls Ψ₂ e ρ) := by
  iloeb as IH generalizing %e %ρ
  cases htv : toVal e with
  | some w =>
    rw [wps_unfold.to_eq, wps_unfold.to_eq]
    simp only [wps.pre, htv]
    iintro H HΨ
    imod H with H
    imodintro
    iapply HΨ $$ H
  | none =>
    rw [wps_unfold.to_eq, wps_unfold.to_eq]
    simp only [wps.pre, htv]
    iintro H HΨ %σ₁ %ns %obs %obs' %nt Hσ
    imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨$, H⟩
    imodintro
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    imod H $$ %r %σ₂ %eₜ %Hstep Hcred with ⟨$, H⟩
    imodintro
    iapply IH $$ %(r.e) %(r.ρ) H HΨ

/-- FRAME over the statement WP (derived from `wps_wand`; S3 note:
    the frame rides to the value exit; at a jump it is released —
    the label invariant is the only thing that crosses a back
    edge). -/
theorem wps_frame {Ψ : SpikeVal → EnvStack → IProp GF} {R : IProp GF}
    (e : CoreExpr) (ρ : EnvStack) :
    iprop(wps Q Ls Ψ e ρ ∗ R) ⊢
      wps Q Ls (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ := by
  iintro ⟨H, HR⟩
  iapply (wps_wand e ρ) $$ H
  iintro %w %ρ' HΨ
  isplitl [HΨ]
  · iexact HΨ
  · iexact HR

/-! ## The annotation layer at this stratum (the R-i cost, re-paid
once — the run-time Eannot residue commutes with `wps` exactly as
with the base WP; proofs mirror Rules.lean's `wp_annot_reindex` /
`wp_annot` over `wps.pre`) -/

/-- Annotation reindexing (the lockstep argument) over `wps`. -/
theorem wps_annot_reindex (a : List annot) (dsA dsB : List dyn_annotation)
    (c : CoreExpr) (ρ : EnvStack) {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (hΦ : ∀ w ρ', Ψ₁ (SpikeVal.merge dsA w) ρ' = Ψ₂ (SpikeVal.merge dsB w) ρ') :
    wps Q Ls Ψ₁ (Expr a (Eannot dsA c)) ρ ⊢
      wps Q Ls Ψ₂ (Expr a (Eannot dsB c)) ρ := by
  iloeb as IH generalizing %a %dsA %dsB %c %ρ %hΦ
  rcases toVal_annot_cases a c dsA with ⟨rfl, v, rfl, hA⟩ | hA
  · -- value on both sides
    have hB : toVal (Expr ([] : List annot) (Eannot dsB (ofVal (.pure v)))) =
        some (.annot dsB v) := rfl
    rw [wps_unfold.to_eq, wps_unfold.to_eq]
    simp only [wps.pre, hA, hB]
    iintro H
    imod H with H
    imodintro
    have h' : Ψ₁ (SpikeVal.annot dsA v) ρ = Ψ₂ (SpikeVal.annot dsB v) ρ :=
      hΦ (.pure v) ρ
    rw [← h']
    iexact H
  · -- non-value on both sides
    have hB : toVal (Expr a (Eannot dsB c)) = none := by
      rcases toVal_annot_cases a c dsB with ⟨rfl, v, rfl, _⟩ | hB
      · rw [show toVal (Expr ([] : List annot) (Eannot dsA (ofVal (.pure v)))) =
            some (.annot dsA v) from rfl] at hA
        cases hA
      · exact hB
    rw [wps_unfold.to_eq, wps_unfold.to_eq]
    simp only [wps.pre, hA, hB]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
    imodintro
    isplit
    · ipureintro
      obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
      rcases hstep.1.annot_inv with ⟨hg, c', ρ', σ'', hs, _⟩ |
          ⟨a2, ds2, c'', rfl, _⟩
      · exact ⟨[], ⟨Expr a (Eannot dsB c'), ρ'⟩, _, [],
          ⟨Step.annot_ctx hg hs, rfl⟩⟩
      · exact ⟨[], ⟨Expr (a ++ a2) (Eannot (dsB ++ ds2) c''), ρ⟩, _, [],
          ⟨Step.annot_merge, rfl⟩⟩
    · inext
      iintro %e₂ %σ₂ %eₜ %HstepB Hcred
      obtain ⟨hstepB, rfl⟩ := HstepB
      rcases hstepB.annot_inv with ⟨hg, c', ρ', σ'', hs, hout⟩ |
          ⟨a2, ds2, c'', rfl, hout⟩
      · obtain ⟨e₂e, e₂ρ⟩ := e₂
        obtain ⟨he, hρ, hσ⟩ : e₂e = Expr a (Eannot dsB c') ∧ e₂ρ = ρ' ∧
            σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst he hρ hσ
        imod H $$ %(⟨Expr a (Eannot dsA c'), e₂ρ⟩ : CoreRt) %_ %([])
          %⟨Step.annot_ctx hg hs, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %a %dsA %dsB %c' %e₂ρ %hΦ H
      · obtain ⟨e₂e, e₂ρ⟩ := e₂
        obtain ⟨he, hρ, hσ⟩ : e₂e = Expr (a ++ a2) (Eannot (dsB ++ ds2) c'') ∧
            e₂ρ = ρ ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq] using hout
        subst he
        obtain rfl : ρ = e₂ρ := hρ.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod H $$ %(⟨Expr (a ++ a2) (Eannot (dsA ++ ds2) c''), ρ⟩ : CoreRt) %_
          %([]) %⟨Step.annot_merge, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %(a ++ a2) %(dsA ++ ds2) %(dsB ++ ds2) %c'' %ρ
          %(fun w ρ' => by
            rw [← SpikeVal.merge_merge, ← SpikeVal.merge_merge]
            exact hΦ (SpikeVal.merge ds2 w) ρ') H

/-- `wps` commutes with the run-time dyn-annotation wrapper (mirror
    of `wp_annot`; the merge case exits through the reindexing
    lemma). -/
theorem wps_annot (ds : List dyn_annotation) (e : CoreExpr) (ρ : EnvStack)
    {Ψ : SpikeVal → EnvStack → IProp GF} :
    wps Q Ls (fun w ρ' => Ψ (SpikeVal.merge ds w) ρ') e ρ ⊢
      wps Q Ls Ψ (Expr ([] : List annot) (Eannot ds e)) ρ := by
  iloeb as IH generalizing %ds %e %ρ
  cases hv : toVal e with
  | some w =>
    have he := ofVal_of_toVal hv
    subst he
    cases w with
    | pure v =>
      -- the wrap is itself a value: .annot ds v
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, toVal_ofVal,
        show toVal (Expr ([] : List annot) (Eannot ds (ofVal (.pure v)))) =
          some (.annot ds v) from rfl]
      iintro H
      imod H with H
      imodintro
      rw [show (SpikeVal.annot ds v) = SpikeVal.merge ds (SpikeVal.pure v)
        from rfl]
      iexact H
    | annot ds2 v =>
      -- double annot: one deterministic ANNOTS-merge step to a value
      rw [(wps_unfold
        (e := Expr ([] : List annot) (Eannot ds (ofVal (.annot ds2 v))))).to_eq]
      simp only [wps.pre,
        show toVal (Expr ([] : List annot)
          (Eannot ds (ofVal (SpikeVal.annot ds2 v)))) = none from rfl]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _⟩, _, [], ⟨Step.annot_merge, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, rfl⟩ := Hstep
      rcases hs.annot_inv with ⟨hg, c', ρ', σ'', hs', hout⟩ |
          ⟨a2, ds2', c'', hb, hout⟩
      · exact absurd hs' (fun h => Step.val_elim (w := .annot ds2 v) h)
      · obtain ⟨rfl, rfl, rfl⟩ : ([] : List annot) = a2 ∧ ds2 = ds2' ∧
            Expr ([] : List annot) (Epure (Pexpr [] () (PEval v))) = c'' := by
          simpa [ofVal] using hb
        obtain ⟨re, rρ⟩ := r
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr ([] : List annot)
              (Eannot (ds ++ ds2)
                (Expr ([] : List annot) (Epure (Pexpr [] () (PEval v))))) ∧
            rρ = ρ ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq, ofVal] using hout
        subst hre
        obtain rfl : ρ = rρ := hrρ.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        ihave H := wps_value_inv (.annot ds2 v) ρ $$ H
        imod H with H
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · rw [show Expr ([] : List annot) (Eannot (ds ++ ds2)
              (Expr ([] : List annot) (Epure (Pexpr [] () (PEval v))))) =
            ofVal (.annot (ds ++ ds2) v) from rfl]
          iapply wps_ofVal (.annot (ds ++ ds2) v) ρ
          rw [show (SpikeVal.annot (ds ++ ds2) v) =
            SpikeVal.merge ds (SpikeVal.annot ds2 v) from rfl]
          iexact H
  | none =>
    by_cases hr : annotRooted e = true
    · -- annot-rooted body: the wrap merges; exit through reindexing
      obtain ⟨a2, ds2, c, rfl⟩ : ∃ a2 ds2 c, e = Expr a2 (Eannot ds2 c) := by
        unfold annotRooted at hr
        split at hr
        · rename_i a2 ds2 c
          exact ⟨a2, ds2, c, rfl⟩
        · cases hr
      rw [(wps_unfold
        (e := Expr ([] : List annot) (Eannot ds (Expr a2 (Eannot ds2 c))))).to_eq]
      simp only [wps.pre, toVal_annot_none hv]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _⟩, _, [], ⟨Step.annot_merge, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, rfl⟩ := Hstep
      rcases hs.annot_inv with ⟨hg, c', ρ', σ'', hs', hout⟩ |
          ⟨a2', ds2', c'', hb, hout⟩
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
      · obtain ⟨rfl, rfl, rfl⟩ : a2 = a2' ∧ ds2 = ds2' ∧ c = c'' := by
          simpa using hb
        obtain ⟨re, rρ⟩ := r
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr ([] ++ a2) (Eannot (ds ++ ds2) c) ∧
            rρ = ρ ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq] using hout
        subst hre
        obtain rfl : ρ = rρ := hrρ.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · simp only [List.nil_append]
          iapply (wps_annot_reindex
            (Ψ₁ := fun w ρ' => iprop(Ψ (SpikeVal.merge ds w) ρ'))
            a2 ds2 (ds ++ ds2) c ρ
            (fun w ρ' => congrArg (fun z => Ψ z ρ')
              (SpikeVal.merge_merge ds ds2 w))) $$ H
    · -- plain body: reduction in the Cannot frame, Löb
      have hr' : annotRooted e = false := by simpa using hr
      have hwrap : toVal (Expr ([] : List annot) (Eannot ds e)) = none :=
        toVal_annot_none hv
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, hv, hwrap]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
        exact ⟨[], ⟨Expr ([] : List annot) (Eannot ds e'.e), e'.ρ⟩, _, [],
          ⟨Step.annot_ctx hr' hstep.1, rfl⟩⟩
      · inext
        iintro %e₂ %σ₂ %eₜ %HstepW Hcred
        obtain ⟨hstepW, rfl⟩ := HstepW
        rcases hstepW.annot_inv with ⟨hg, e'', ρ', σ'', hs, hout⟩ |
            ⟨a2, ds2, c, heq, hout⟩
        · obtain ⟨e₂e, e₂ρ⟩ := e₂
          obtain ⟨he, hρ, hσ⟩ : e₂e = Expr ([] : List annot) (Eannot ds e'') ∧
              e₂ρ = ρ' ∧ σ₂ = σ'' := by
            simpa [Prod.mk.injEq] using hout
          subst he hρ hσ
          imod H $$ %(⟨e'', e₂ρ⟩ : CoreRt) %_ %([]) %⟨hs, rfl⟩ Hcred
            with ⟨$, H⟩
          imodintro
          iapply IH $$ %ds %e'' %e₂ρ H
        · exact absurd heq (by
            intro heq
            rw [heq] at hr'
            simp [annotRooted] at hr')

/-! ## THE SEQUENCING RULE (the jump-aware statement shape — probe
`wps_seq`; the phase-1 proof is the value-beta / annot-beta / step
three-way, S3 adds the jump-clause transfer as the fourth case) -/

theorem wps_seq {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps Q Ls (fun w ρ' => wps Q Ls
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wps Q Ls Ψ (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    -- e1 is finished: the beta step (LETS-PURE / LETS-ANNOT) at the
    -- cons-shaped env; the continuation comes from the premise's
    -- value channel.
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofVal w) e2))).to_eq]
    simp only [wps.pre, toVal_ofVal, toVal_sseq_node]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H with H
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases w with
      | pure v => exact ⟨[], ⟨_, _⟩, _, [], ⟨Step.sseq_pure, rfl⟩⟩
      | annot ds v => exact ⟨[], ⟨_, _⟩, _, [], ⟨Step.sseq_annot, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, rfl⟩ := Hstep
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hs', hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds, v, _, _, _, he1, _, hout⟩
    · exact absurd hs' (fun h => Step.val_elim h)
    · -- LETS-PURE: successor (e2, ρ, σ)
      obtain rfl : w = .pure v := by
        cases w with
        | pure v' => simpa [ofVal] using he1
        | annot ds' v' => exact absurd he1 (by simp [ofVal])
      obtain ⟨re, rρ⟩ := r
      obtain ⟨hre, hrρ, hσ⟩ : re = e2 ∧ rρ = ev0 :: evs ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      subst hrρ
      obtain rfl : e2 = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · rw [show (fun u ρ'' => Ψ (SpikeVal.mergeInto (SpikeVal.pure v) u) ρ'')
          = Ψ from rfl]
        iexact H
    · -- LETS-ANNOT: successor ({ds}e2, ρ, σ); exit through wps_annot
      obtain rfl : w = .annot ds v := by
        cases w with
        | pure v' => exact absurd he1 (by simp [ofVal])
        | annot ds' v' =>
          obtain ⟨h1, h2⟩ : ds' = ds ∧ v' = v := by simpa [ofVal] using he1
          rw [h1, h2]
      obtain ⟨re, rρ⟩ := r
      obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot ds e2) ∧
          rρ = ev0 :: evs ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      subst hre hrρ
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · rw [show (fun u ρ'' => Ψ (SpikeVal.mergeInto (SpikeVal.annot ds v) u) ρ'')
          = fun u ρ'' => Ψ (SpikeVal.merge ds u) ρ'' from rfl]
        iapply wps_annot ds e2 (ev0 :: evs) $$ H
  | none =>
    -- e1 steps: inversion factor + congruence lift + Löb; env
    -- invariance keeps the stack cons-shaped for the IH.
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
        e1 e2))).to_eq]
    simp only [wps.pre, htv, toVal_sseq_node]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
    imodintro
    isplit
    · ipureintro
      obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
      obtain ⟨hs', hnil'⟩ := hps
      exact ⟨obs0, ⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
          r'.e e2), r'.ρ⟩, σ', [],
        ⟨Step.sseq_ctx hs', rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, rfl⟩ := Hstep
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hs', hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩
    · obtain rfl : ρ'' = ev0 :: evs := hs'.env_invariant
      obtain ⟨re, rρ⟩ := r
      obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Esseq (Pattern pa
          (CaseBase (none, bty))) e1' e2) ∧ rρ = ev0 :: evs ∧ σ₂ = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst hre hrρ hσ
      imod H $$ %(⟨e1', ev0 :: evs⟩ : CoreRt) %σ₂ %([] : List CoreRt)
        %⟨hs', rfl⟩ Hcred with ⟨$, H⟩
      imodintro
      iapply IH $$ %e1' %ev0 %evs H
    · rw [he1, toVal_ofVal] at htv; cases htv
    · rw [he1, toVal_ofVal] at htv; cases htv

/-! ## The small axioms at the statement layer (house engine seams
`storeM_success`/`loadM_success` reused verbatim — probe §6 S2) -/

/-- Store small axiom over `wps` (full ownership, UB-excluding —
    the same preconditions as `wp_store`, Rules.lean; the env rides
    verbatim; the footprint reaches the continuation universally
    since only one is possible). -/
theorem wps_store {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue fmapEmpty (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt ty mv) :
    iprop(pointsToCell (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell pv (.own 1) ty (CerbMem.memValueToBytes [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps Q Ls Ψ (storeExpr loc ann ty pv cv mo) ρ := by
  rw [(wps_unfold (e := storeExpr loc ann ty pv cv mo)).to_eq]
  simp only [wps.pre, show toVal (storeExpr loc ann ty pv cv mo) = none from rfl]
  iintro ⟨Hpt, HΨ⟩ %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_iff σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨%m, %Hcoh, Hh⟩
  icases (pointsToCell_iff pv (.own 1) ty bs).mp $$ Hpt with ⟨%i, %addr, %Hpv, Hpt⟩
  subst Hpv
  ihave %Hget : ⌜Iris.Std.PartialMap.get? m i = some (SpikeCell.mk addr ty bs)⌝
      $$ [Hh Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hh $Hpt]
    itrivial
  have hcell : CellCoh σ₁ i ⟨addr, ty, bs⟩ := Hcoh.cells i _ Hget
  have hrun := storeM_success σ₁ i ⟨addr, ty, bs⟩ mv loc hcell hst
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _⟩, _, [], ⟨Step.store_canonical hmv hrun, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hstep, rfl⟩ := Hstep
  obtain ⟨mv', fp', σ'', hmv', hmem', hout⟩ := hstep.store_inv
  obtain rfl : mv = mv' := Option.some.inj (hmv.symm.trans hmv')
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : fp' = CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty) ∧
      σ'' = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes [] mv).2 := by
    have h := Option.some.inj hmem'.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨re, rρ⟩ := r
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty))]
        (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) ∧ rρ = ρ ∧
      σ₂ = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes [] mv).2 := by
    simpa [Prod.mk.injEq] using hout
  subst hre hσ
  obtain rfl : ρ = rρ := hrρ.symm
  imod Hclose with -
  imod (genHeap_update
      (v₂ := SpikeCell.mk addr ty (CerbMem.memValueToBytes [] mv).2))
    $$ [$Hh $Hpt] with ⟨Hh, Hpt⟩
  imodintro
  isplitl [Hh]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists (Iris.Std.PartialMap.insert m i
      (SpikeCell.mk addr ty (CerbMem.memValueToBytes [] mv).2))
    isplitr [Hh]
    · ipureintro
      exact Coh.store σ₁ m i ⟨addr, ty, bs⟩ mv Hcoh Hget hst
    · iexact Hh
  · rw [show Expr ([] : List annot) (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty))]
        (Expr [] (Epure (Pexpr [] () (PEval Vunit))))) =
      ofVal (.annot [DA_pos [] (CerbMem.Footprint.FP .W addr
        (CerbMem.sizeofCtype ty))] Vunit) from rfl]
    iapply (wps_ofVal
      (.annot [DA_pos [] (CerbMem.Footprint.FP .W addr
        (CerbMem.sizeofCtype ty))] Vunit) ρ)
    iapply HΨ
    iapply (pointsToCell_iff _ _ _ _).mpr
    iexists i, addr
    isplit
    · ipureintro; rfl
    · iexact Hpt

/-- Load small axiom over `wps` (any fraction, UB-excluding — the
    `htrap` premise excludes the _Bool trap arm as in `wp_load`). -/
theorem wps_load {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell (GF := GF) pv dq ty bs ∗
      (∀ fp, pointsToCell pv dq ty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] (loadedVal pv ty bs)) ρ)) ⊢
      wps Q Ls Ψ (loadExpr loc ann ty pv mo) ρ := by
  rw [(wps_unfold (e := loadExpr loc ann ty pv mo)).to_eq]
  simp only [wps.pre, show toVal (loadExpr loc ann ty pv mo) = none from rfl]
  iintro ⟨Hpt, HΨ⟩ %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_iff σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨%m, %Hcoh, Hh⟩
  icases (pointsToCell_iff pv dq ty bs).mp $$ Hpt with ⟨%i, %addr, %Hpv, Hpt⟩
  subst Hpv
  ihave %Hget : ⌜Iris.Std.PartialMap.get? m i = some (SpikeCell.mk addr ty bs)⌝
      $$ [Hh Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hh $Hpt]
    itrivial
  have hcell : CellCoh σ₁ i ⟨addr, ty, bs⟩ := Hcoh.cells i _ Hget
  have hrun := loadM_success σ₁ i ⟨addr, ty, bs⟩ loc hcell htrap
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _⟩, _, [], ⟨Step.load_canonical hrun, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hstep, rfl⟩ := Hstep
  obtain ⟨fp', mval', σ'', hmem', hout⟩ := hstep.load_inv
  rw [hrun] at hmem'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ :
      (fp' = CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype ty) ∧
        mval' = decodeCell ⟨addr, ty, bs⟩) ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem'.symm
    exact ⟨⟨congrArg (fun p => p.1.1) h, congrArg (fun p => p.1.2) h⟩,
      (congrArg Prod.snd h).symm⟩
  obtain ⟨re, rρ⟩ := r
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype ty))]
        (Expr [] (Epure (Pexpr [] () (PEval
          (valueFromMemValue (decodeCell ⟨addr, ty, bs⟩)).2))))) ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hh]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists m
    isplitr [Hh]
    · ipureintro
      exact Hcoh
    · iexact Hh
  · rw [show Expr ([] : List annot) (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype ty))]
        (Expr [] (Epure (Pexpr [] () (PEval
          (valueFromMemValue (decodeCell ⟨addr, ty, bs⟩)).2))))) =
      ofVal (.annot [DA_pos [] (CerbMem.Footprint.FP .R addr
        (CerbMem.sizeofCtype ty))] (loadedVal (cellPtr i addr) ty bs))
      from rfl]
    iapply (wps_ofVal
      (.annot [DA_pos [] (CerbMem.Footprint.FP .R addr
        (CerbMem.sizeofCtype ty))] (loadedVal (cellPtr i addr) ty bs)) ρ)
    iapply HΨ
    iapply (pointsToCell_iff _ _ _ _).mpr
    iexists i, addr
    isplit
    · ipureintro; rfl
    · iexact Hpt

/-! ## THE COLLAPSE into the base Iris WP (the sole adequacy
interface). Phase-1 form: UNCONDITIONAL (jump-free fragment — the
honest absence, header note); S3's form gains the `blockSpecs`
premise and the one Löb-tied jump case (the donor `wps_block_rec`
analog, probe report §2). -/

theorem wps_sound {Ψ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr)
    (ρ : EnvStack) :
    wps Q Ls Ψ e ρ ⊢
      WP (⟨e, ρ⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Ψ w.w w.ρ }} := by
  iloeb as IH generalizing %e %ρ
  cases htv : toVal e with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wps_unfold.to_eq, wp_unfold.to_eq]
    simp only [wps.pre, toVal_ofVal, wp.pre, language_toVal_eq, toValRt_mk,
      Option.map_some]
    iintro Hwps
    imod Hwps with Hwps
    imodintro
    iexact Hwps
  | none =>
    have htoval : ToVal.toVal (Val := CoreRVal) (⟨e, ρ⟩ : CoreRt) = none := by
      rw [language_toVal_eq, toValRt_mk, htv]
      rfl
    rw [wps_unfold.to_eq]
    simp only [wps.pre, htv]
    iintro Hwps
    iapply wp_lift_step htoval
    iintro %σ₁ %ns %obs %obs' %nt Hσ
    imod Hwps $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, Hwps⟩
    imodintro
    isplitr
    · ipureintro
      exact hred
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hnil⟩ := Hstep
    imod Hwps $$ %r %σ₂ %eₜ %(⟨hs, hnil⟩ :
        ((⟨e, ρ⟩ : CoreRt), σ₁) -<obs>-> (r, σ₂, eₜ)) Hcred with ⟨HSI, Hwps⟩
    imodintro
    isplitl [HSI]
    · subst hnil
      simp only [List.length_nil, Nat.add_zero]
      iexact HSI
    isplitr []
    · have hr : r = (⟨r.e, r.ρ⟩ : CoreRt) := rfl
      rw [hr]
      iapply IH $$ %(r.e) %(r.ρ) Hwps
    · subst hnil
      simp only [Algebra.BigOpL.bigOpL_nil]
      itrivial

/-! ## Coverage preservation on the REAL fragment (probe §4, now over
Core): the corpus's two exhibit shapes on the stratified layer, for
an ARBITRARY label context (Q, Ls) — jump-free code never consults
it. Compositional discipline identical to the frozen exhibits: small
axiom + FRAME + the sequencing rule; distinctness by ∗ alone. -/

/-- Corpus shape 1 (the house `exhibit`): {x ↦ - ∗ y ↦ a} store(x,7)
    {x ↦ 7 ∗ y ↦ a}, via FRAME on the store small axiom — any label
    context, any env. -/
theorem wps_exhibit_store_frame (x y : CerbMem.PointerValue)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) (ρ : EnvStack) :
    iprop(pointsToCell (GF := GF) x (.own 1) intTy bs ∗
        pointsToCell y (.own 1) ty' bs') ⊢
      wps Q Ls
        (fun _ _ => iprop(pointsToCell x (.own 1) intTy sevenBytes ∗
          pointsToCell y (.own 1) ty' bs'))
        (storeExpr loc ann intTy x sevenVal mo) ρ := by
  iintro ⟨Hx, Hy⟩
  iapply (wps_frame
    (Ψ := fun _ _ => iprop(pointsToCell (GF := GF) x (.own 1) intTy sevenBytes))
    (R := pointsToCell y (.own 1) ty' bs') _ _)
  isplitl [Hx]
  · iapply wps_store loc ann intTy x sevenVal mo sevenMval bs ρ seven_encodes
      seven_storable
    isplitl [Hx]
    · iexact Hx
    iintro %fp Hx
    rw [show sevenBytes = (CerbMem.memValueToBytes [] sevenMval).2 from rfl]
    iexact Hx
  · iexact Hy

/-- Corpus shape 2 (the house `exhibitC_triple`): two sequenced
    stores on disjoint cells, glued by the (jump-aware-shaped)
    sequencing rule — each leg the small axiom, distinctness carried
    by ∗ alone, any label context, any cons-shaped env. -/
theorem wps_exhibit_seq_stores (x y : CerbMem.PointerValue)
    (loc loc' : CerbLocation.Loc) (ann ann' : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type)
    (bsx bsy : List CerbMem.AbsByte)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    iprop(pointsToCell (GF := GF) x (.own 1) intTy bsx ∗
        pointsToCell y (.own 1) intTy bsy) ⊢
      wps Q Ls
        (fun _ _ => iprop(pointsToCell x (.own 1) intTy fiveBytes ∗
          pointsToCell y (.own 1) intTy sixBytes))
        (sseqExpr bty (storeExpr loc ann intTy x fiveVal mo)
          (storeExpr loc' ann' intTy y sixVal mo')) (ev0 :: evs) := by
  iintro ⟨Hx, Hy⟩
  rw [show sseqExpr bty (storeExpr loc ann intTy x fiveVal mo)
      (storeExpr loc' ann' intTy y sixVal mo') =
    Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
      (storeExpr loc ann intTy x fiveVal mo)
      (storeExpr loc' ann' intTy y sixVal mo')) from rfl]
  iapply wps_seq
  iapply wps_store loc ann intTy x fiveVal mo fiveMval bsx (ev0 :: evs)
    five_encodes five_storable
  isplitl [Hx]
  · iexact Hx
  iintro %fp Hx
  iapply wps_store loc' ann' intTy y sixVal mo' sixMval bsy (ev0 :: evs)
    six_encodes six_storable
  isplitl [Hy]
  · iexact Hy
  iintro %fp' Hy
  rw [show fiveBytes = (CerbMem.memValueToBytes [] fiveMval).2 from rfl,
    show sixBytes = (CerbMem.memValueToBytes [] sixMval).2 from rfl]
  isplitl [Hx]
  · iexact Hx
  · iexact Hy

end CerberusHeapLang
