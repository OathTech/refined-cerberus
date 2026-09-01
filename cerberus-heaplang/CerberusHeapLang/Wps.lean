/-
CerberusHeapLang.Wps — the STATEMENT-STRATIFIED WP: the judgment
the loop exhibits are proved in.

THE SHAPE: the classical LABEL-CONTEXT statement logic (de Bruin
1981-style label-assumption judgments, the shape RefinedC's
statement judgment also takes), realized as a guarded fixpoint over
the fragment's Step via iris-lean's PUBLIC Banach machinery
(`fixpoint`/`OFE.Contractive` — the same machinery `wp` itself is
built from; iris-lean untouched). `wps M Ls Ψ e ρ` is indexed by

- `Q : LabelMap` — the STATIC label map (per-procedure registered
  continuations; the engine's `labeled_continuations`,
  Core_run_aux.lean:186-187 — the analog of Caesium's `f_code`).
  The certification ties it to `core_run_state.labeled` at the
  current procedure by a pure equation (RefinedC's
  `⌜Q = rf.f_code⌝`, lifting.v:1002 — legitimate because nothing
  writes `labeled` on the positive sequential path).
- `Ls : LabelSpec GF` — the per-label preconditions, indexed by the
  jump-argument values (list-valued for Erun's argument list) and
  the jump-time environment.

THE JUMP CLAUSE: `wps.pre` has THREE clauses (value / jump redex /
step). The jump clause fires at the Core `jumpRedex?` (Step.lean —
the syntactic image of step_ctx's Erun context-discard over the
Esseq/Eannot frames); `Q` is the CURRENT PROCEDURE's label map
carried in the runtime tuple (`CoreRt.lbl`); the engine's two-level
`core_run_state.labeled` read through `current_proc_opt` and the
extern indirection is tied to it by the pure equation
`fmapLookupBy ord p rs.labeled = some Q` in Soundness.lean's
jump-profile certification. The clause demands: the label resolves
in `Q` (`lookupLabel`), the arguments evaluate under the CURRENT
env by the PURE evaluator (`evalPexprs` — certified against the
engine's `full_eval_pexpr'`), the env stack is cons-shaped (the
`update_env` panic exclusion), and the per-label precondition
`Ls l vs` holds — then TRACKING STOPS (the label-context logic's
discipline: a jump's postcondition is the label's business, so the
postcondition clash that would sink a bind-style rule never forms).
`wps_sound` (the collapse into the base WP, and the package's one
Löb induction) carries the `blockSpecs` premise — every registered
label's body re-establishes its precondition — and its jump case is
where the clause is CERTIFIED against the step relation
(`Step.jump_inv` / `Step.run_of_jumpRedex`).

THE CONTENTS: the small axioms at this stratum (`wps_store`/
`wps_load` — the `storeM_success`/`loadM_success` engine seams
reused verbatim inside the step clause), the jump-aware sequencing
rules (`wps_seq`, `wps_seq_spec`, `wps_seq_sym`), the
annotation-commuting layer (`wps_annot_reindex`/`wps_annot`),
structural rules (`wps_wand`/`wps_frame`), the branch/entry rules,
the per-label invariant rule `blockSpecs_intro` and the
invariant+variant rule `blockSpecs_intro_variant` (no Löb in
either — the one Löb is inside `wps_sound`), and the collapse
`wps_sound` into the base Iris WP (the sole adequacy interface).

NO `wps_create`: no create small axiom exists at ANY layer (a sound
one needs the allocator-cursor resource in the state
interpretation — registered growth step, ProdEntry.lean header).
Cold-start creates ride the production entry
(prod_run_eq / sem_triple_prod) unchanged.

Design records: docs/2026-08-31_s0-probe-report.md (the
architecture probe), docs/2026-08-31_s0-adjudication.md (the
machinery-use adjudication), the dated slice notes.
-/
import CerberusHeapLang.Rules

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

/-! ## The label context (header note; `LabelMap` itself lives in
Step.lean — Step consults it) -/

/-- Per-label preconditions, indexed by the jump-argument values AND
    the jump-time environment (probe `Ls`, list-valued for Erun's
    argument list; S3 jump-clause payload decision: env-indexed —
    classical de Bruin label assertions range over the whole state,
    and the Core env's finite-map representation makes env-BLIND
    specs unusable for data-dependent loops: the body's parameter
    lookups after the jump's `update_env` fold sit on an arbitrary
    quantified base frame, where the tree-map add/lookup laws would
    demand comparator lawfulness the digest order does not ship;
    pinning the env in `Ls` keeps every exhibit-side map operation
    at concrete keys and concrete frames — recorded finding, slice
    notes). -/
abbrev LabelSpec (GF : BundledGFunctors) : Type :=
  sym → List value → EnvStack → IProp GF

/-! ## Per-constructor value-test facts (match-reduction discipline) -/

@[simp] theorem toVal_sseq_node (a : List annot) (pat : pattern)
    (e1 e2 : CoreExpr) : toVal (Expr a (Esseq pat e1 e2)) = none := rfl

@[simp] theorem toVal_wseq_node (a : List annot) (pat : pattern)
    (e1 e2 : CoreExpr) : toVal (Expr a (Ewseq pat e1 e2)) = none := rfl

@[simp] theorem toVal_action_node (a : List annot)
    (p : generic_paction core_run_annotation Unit sym) :
    toVal (Expr a (Eaction p)) = none := rfl

@[simp] theorem toVal_memop_node (a : List annot) (mop : memop)
    (pes : List (generic_pexpr Unit sym)) :
    toVal (Expr a (Ememop mop pes)) = none := rfl

variable {hlc : HasLC} {GF : BundledGFunctors}

/-! ## The statement WP -/

/-- One unfolding of the statement WP. S3: THREE clauses — value /
    jump redex / step (header note; probe Wps.lean:154). The jump
    clause's payload: label resolution in the tuple-carried
    per-procedure map, argument evaluation by the pure evaluator at
    the CURRENT env, the cons-shaped-env WF fact, and the per-label
    precondition — all pure but `Ls`, so the clause is Ψ- and
    frame-independent (what makes sequencing a transfer). The step
    clause is the base `wp_lift_step` premise shape at this
    instance's `numLatersPerStep = 0`, minus forks (the fragment
    forks nothing — `primStep` pins `eₜ = []`). -/
def wps.pre [SpikeGS hlc GF] (M : MachineCtx) (Ls : LabelSpec GF)
    (F : (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr) (ρ : EnvStack) :
    IProp GF :=
  match toVal e with
  | some w => iprop(|={⊤}=> Ψ w ρ)
  | none =>
    match jumpRedex? e with
    | some lp =>
      iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (cont : CoreExpr)
        (vs : List value) (ev0 : Fmap sym value) (evs : List (Fmap sym value)),
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel M.labels lp.1 = some (params, cont)⌝ ∗
        ⌜evalPexprs M.extern ρ lp.2 = some vs⌝ ∗ Ls lp.1 vs ρ)
    | none =>
      iprop(∀ (σ₁ : Mem) (ns : Nat) (obs obs' : List Empty) (nt : Nat),
        stateInterp σ₁ ns (obs ++ obs') nt ={⊤,∅}=∗
        ⌜PrimStep.Reducible ((⟨e, ρ, M⟩ : CoreRt), σ₁)⌝ ∗
        ▷ ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
          ⌜((⟨e, ρ, M⟩ : CoreRt), σ₁) -<obs>-> (r, σ₂, eₜ)⌝ -∗ £ 1 ={∅,⊤}=∗
          stateInterp σ₂ (ns + 1) obs' nt ∗ F Ψ r.e r.ρ)

instance wps.pre.contractive [SpikeGS hlc GF] (M : MachineCtx)
    (Ls : LabelSpec GF) :
    OFE.Contractive (wps.pre (GF := GF) M Ls) where
  distLater_dist := by
    intro n F F' HF Ψ e ρ
    unfold wps.pre
    cases toVal e
    case some => exact .rfl
    case none =>
      cases jumpRedex? e
      case some => exact .rfl
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
def wps [SpikeGS hlc GF] (M : MachineCtx) (Ls : LabelSpec GF) :
    (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF :=
  fixpoint (wps.pre M Ls)

theorem wps_unfold [SpikeGS hlc GF] {M : MachineCtx} {Ls : LabelSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr} {ρ : EnvStack} :
    wps (GF := GF) M Ls Ψ e ρ ⊣⊢ wps.pre M Ls (wps M Ls) Ψ e ρ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wps.pre M Ls).toContractiveHom)).dist Ψ e ρ

variable [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpec GF}

/-! ## Structural rules -/

/-- Value rule at the canonical value injections (the donor's Return
    channel / probe `wps_val`). -/
theorem wps_ofVal {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeVal)
    (ρ : EnvStack) :
    Ψ w ρ ⊢ wps M Ls Ψ (ofVal w) ρ := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toVal_ofVal]
  iintro H
  imodintro
  iexact H

/-- Value-channel inversion at the canonical injections (the wps
    analog of `wp_value_fupd'`'s forward direction). -/
theorem wps_value_inv {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeVal)
    (ρ : EnvStack) :
    wps M Ls Ψ (ofVal w) ρ ⊢ iprop(|={⊤}=> Ψ w ρ) := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toVal_ofVal]
  iintro H
  iexact H

/-- THE JUMP RULE (donor `wps_goto`, lifting.v:1112, in the
    label-context shape — probe `wps_run`): a registered jump is
    verified by consulting the label's precondition at the
    argument values — nothing else. Near-definitional: the
    judgment's jump clause IS this rule. The `▷` of the donor's
    `wps_goto` is paid at the actual jump step inside `wps_sound`. -/
theorem wps_run {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (ra : core_run_annotation) (l : sym)
    (pes : List (generic_pexpr Unit sym))
    {params : List (sym × core_base_type)} {cont : CoreExpr}
    {vs : List value} (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hl : lookupLabel M.labels l = some (params, cont))
    (hvs : evalPexprs M.extern (ev0 :: evs) pes = some vs) :
    Ls l vs (ev0 :: evs) ⊢
      wps M Ls Ψ (Expr a (Erun ra l pes)) (ev0 :: evs) := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, show toVal (Expr a (Erun ra l pes)) = none from rfl,
    jumpRedex?_run]
  iintro H
  imodintro
  iexists params, cont, vs, ev0, evs
  isplit
  · ipureintro; rfl
  isplit
  · ipureintro; exact hl
  isplit
  · ipureintro; exact hvs
  iexact H

/-- Monotonicity/consequence in the value channel (probe `wps_wand`;
    S3: jump exits are Ψ-independent — the label preconditions
    carry everything across a jump — so the statement survives the
    jump clause verbatim; its case is a pass-through). -/
theorem wps_wand {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr)
    (ρ : EnvStack) :
    wps M Ls Ψ₁ e ρ ⊢
      iprop((∀ w ρ', Ψ₁ w ρ' -∗ Ψ₂ w ρ') -∗ wps M Ls Ψ₂ e ρ) := by
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
    cases hjr : jumpRedex? e with
    | some lp =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H HΨ
      iexact H
    | none =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
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
    iprop(wps M Ls Ψ e ρ ∗ R) ⊢
      wps M Ls (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ := by
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
    wps M Ls Ψ₁ (Expr a (Eannot dsA c)) ρ ⊢
      wps M Ls Ψ₂ (Expr a (Eannot dsB c)) ρ := by
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
    -- the two wraps share the jump-redex answer (`jumpRedex?` never
    -- reads the dyn-annotation payload)
    have hEq : jumpRedex? (Expr a (Eannot dsB c)) =
        jumpRedex? (Expr a (Eannot dsA c)) := by
      rw [jumpRedex?_annot, jumpRedex?_annot]
    cases hjr : jumpRedex? (Expr a (Eannot dsA c)) with
    | some lp =>
      -- S3 JUMP CASE: the two clauses are the SAME FORMULA — the
      -- jump discards the wrapper, and the clause never mentions Φ.
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, hA, hB, hjr, hEq.trans hjr]
      iintro H
      iexact H
    | none =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, hA, hB, hjr, hEq.trans hjr]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
        rcases hstep.1.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs, _⟩ |
            ⟨a2, ds2, c'', rfl, _⟩ |
            ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
        · exact ⟨[], ⟨Expr a (Eannot dsB c'), ρ', M⟩, _, [],
            ⟨Step.annot_ctx hnj hg hs, rfl, rfl⟩⟩
        · exact ⟨[], ⟨Expr (a ++ a2) (Eannot (dsB ++ ds2) c''), ρ, M⟩, _, [],
            ⟨Step.annot_merge, rfl, rfl⟩⟩
        · rw [jumpRedex?_annot_of_not_root _ _ hg, hj] at hjr; cases hjr
      · inext
        iintro %e₂ %σ₂ %eₜ %HstepB Hcred
        obtain ⟨hstepB, hlbl, rfl⟩ := HstepB
        rcases hstepB.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs, hout⟩ |
            ⟨a2, ds2, c'', rfl, hout⟩ |
            ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
        · obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
          simp only at hlbl
          obtain rfl : M = e₂M := hlbl.symm
          obtain ⟨he, hρ, hσ⟩ : e₂e = Expr a (Eannot dsB c') ∧ e₂ρ = ρ' ∧
              σ₂ = σ'' := by
            simpa [Prod.mk.injEq] using hout
          subst he hρ hσ
          imod H $$ %(⟨Expr a (Eannot dsA c'), e₂ρ, M⟩ : CoreRt) %_ %([])
            %⟨Step.annot_ctx hnj hg hs, rfl, rfl⟩ Hcred with ⟨$, H⟩
          imodintro
          iapply IH $$ %a %dsA %dsB %c' %e₂ρ %hΦ H
        · obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
          simp only at hlbl
          obtain rfl : M = e₂M := hlbl.symm
          obtain ⟨he, hρ, hσ⟩ : e₂e = Expr (a ++ a2) (Eannot (dsB ++ ds2) c'') ∧
              e₂ρ = ρ ∧ σ₂ = σ₁ := by
            simpa [Prod.mk.injEq] using hout
          subst he
          obtain rfl : ρ = e₂ρ := hρ.symm
          obtain rfl : σ₁ = σ₂ := hσ.symm
          imod H $$ %(⟨Expr (a ++ a2) (Eannot (dsA ++ ds2) c''), ρ,
              M⟩ : CoreRt) %_
            %([]) %⟨Step.annot_merge, rfl, rfl⟩ Hcred with ⟨$, H⟩
          imodintro
          iapply IH $$ %(a ++ a2) %(dsA ++ ds2) %(dsB ++ ds2) %c'' %ρ
            %(fun w ρ' => by
              rw [← SpikeVal.merge_merge, ← SpikeVal.merge_merge]
              exact hΦ (SpikeVal.merge ds2 w) ρ') H
        · rw [jumpRedex?_annot_of_not_root _ _ hg, hj] at hjr; cases hjr

/-- `wps` commutes with the run-time dyn-annotation wrapper (mirror
    of `wp_annot`; the merge case exits through the reindexing
    lemma). -/
theorem wps_annot (ds : List dyn_annotation) (e : CoreExpr) (ρ : EnvStack)
    {Ψ : SpikeVal → EnvStack → IProp GF} :
    wps M Ls (fun w ρ' => Ψ (SpikeVal.merge ds w) ρ') e ρ ⊢
      wps M Ls Ψ (Expr ([] : List annot) (Eannot ds e)) ρ := by
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
          (Eannot ds (ofVal (SpikeVal.annot ds2 v)))) = none from rfl,
        show jumpRedex? (Expr ([] : List annot)
          (Eannot ds (ofVal (SpikeVal.annot ds2 v)))) = none from rfl]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs', hout⟩ |
          ⟨a2, ds2', c'', hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
      · exact absurd hs' (fun h => Step.val_elim (w := .annot ds2 v) h)
      · obtain ⟨rfl, rfl, rfl⟩ : ([] : List annot) = a2 ∧ ds2 = ds2' ∧
            Expr ([] : List annot) (Epure (Pexpr [] () (PEval v))) = c'' := by
          simpa [ofVal] using hb
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr ([] : List annot)
              (Eannot (ds ++ ds2)
                (Expr [] (Epure (Pexpr [] () (PEval v))))) ∧
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
              (Expr [] (Epure (Pexpr [] () (PEval v))))) =
            ofVal (.annot (ds ++ ds2) v) from rfl]
          iapply wps_ofVal (.annot (ds ++ ds2) v) ρ
          rw [show (SpikeVal.annot (ds ++ ds2) v) =
            SpikeVal.merge ds (SpikeVal.annot ds2 v) from rfl]
          iexact H
      · rw [show annotRooted (ofVal (SpikeVal.annot ds2 v)) = true from rfl]
          at hg
        cases hg
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
      simp only [wps.pre, toVal_annot_none hv,
        show jumpRedex? (Expr ([] : List annot)
            (Eannot ds (Expr a2 (Eannot ds2 c)))) = none from
          jumpRedex?_annot_of_root _ _ rfl]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs', hout⟩ |
          ⟨a2', ds2', c'', hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
      · obtain ⟨rfl, rfl, rfl⟩ : a2 = a2' ∧ ds2 = ds2' ∧ c = c'' := by
          simpa using hb
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
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
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
    · -- plain body: jump-clause transfer, or reduction in the Cannot
      -- frame + Löb
      have hr' : annotRooted e = false := by simpa using hr
      have hwrap : toVal (Expr ([] : List annot) (Eannot ds e)) = none :=
        toVal_annot_none hv
      cases hjr : jumpRedex? e with
      | some lp =>
        -- S3 JUMP CASE: wrap and body share the clause formula.
        rw [wps_unfold.to_eq, wps_unfold.to_eq]
        simp only [wps.pre, hv, hwrap, hjr,
          (jumpRedex?_annot_of_not_root ([] : List annot) ds hr').trans hjr]
        iintro H
        iexact H
      | none =>
        rw [wps_unfold.to_eq, wps_unfold.to_eq]
        simp only [wps.pre, hv, hwrap, hjr,
          (jumpRedex?_annot_of_not_root ([] : List annot) ds hr').trans hjr]
        iintro H %σ₁ %ns %obs %obs' %nt Hσ
        imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
          exact ⟨[], ⟨Expr ([] : List annot) (Eannot ds e'.e), e'.ρ, M⟩, _, [],
            ⟨Step.annot_ctx hjr hr' hstep.1, rfl, rfl⟩⟩
        · inext
          iintro %e₂ %σ₂ %eₜ %HstepW Hcred
          obtain ⟨hstepW, hlbl, rfl⟩ := HstepW
          rcases hstepW.annot_inv with ⟨hg, hnj, e'', ρ', σ'', hs, hout⟩ |
              ⟨a2, ds2, c, heq, hout⟩ |
              ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩
          · obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
            simp only at hlbl
            obtain rfl : M = e₂M := hlbl.symm
            obtain ⟨he, hρ, hσ⟩ : e₂e = Expr ([] : List annot) (Eannot ds e'') ∧
                e₂ρ = ρ' ∧ σ₂ = σ'' := by
              simpa [Prod.mk.injEq] using hout
            subst he hρ hσ
            imod H $$ %(⟨e'', e₂ρ, M⟩ : CoreRt) %_ %([]) %⟨hs, rfl, rfl⟩ Hcred
              with ⟨$, H⟩
            imodintro
            iapply IH $$ %ds %e'' %e₂ρ H
          · exact absurd heq (by
              intro heq
              rw [heq] at hr'
              simp [annotRooted] at hr')
          · rw [hjr] at hj; cases hj

/-! ## THE SEQUENCING RULE (the jump-aware statement shape — probe
`wps_seq`; the phase-1 proof is the value-beta / annot-beta / step
three-way, S3 adds the jump-clause transfer as the fourth case) -/

theorem wps_seq {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M Ls (fun w ρ' => wps M Ls
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wps M Ls Ψ (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
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
    simp only [wps.pre, toVal_ofVal, toVal_sseq_node, jumpRedex?_sseq,
      jumpRedex?_ofVal]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H with H
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases w with
      | pure v => exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_pure, rfl, rfl⟩⟩
      | annot ds v => exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_annot, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds, v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, _⟩
    · exact absurd hs' (fun h => Step.val_elim h)
    · -- LETS-PURE: successor (e2, ρ, σ)
      obtain rfl : w = .pure v := by
        cases w with
        | pure v' => simpa [ofVal] using he1
        | annot ds' v' => exact absurd he1 (by simp [ofVal])
      obtain ⟨re, rρ, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
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
      obtain ⟨re, rρ, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
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
    · rw [jumpRedex?_ofVal] at hj; cases hj
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      -- S3 JUMP CASE (probe report §3 case 2): both sides' jump
      -- clauses are the SAME FORMULA — `jumpRedex? (Esseq …) =
      -- jumpRedex? e1` is the syntactic image of the engine's
      -- context-discard, and the clause never mentions Ψ or the
      -- frame. The transfer is `iexact`.
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
          e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H
      iexact H
    | none =>
      -- e1 steps: inversion factor + congruence lift + Löb; the
      -- stack stays CONS-SHAPED (`Step.env_cons` — S3's survivor of
      -- the retired env invariance) and the IH re-enters at the new
      -- head frame.
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
          e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
            r'.e e2), r'.ρ, M⟩, σ', [],
          ⟨Step.sseq_ctx hjr hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
          ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Esseq (Pattern pa
            (CaseBase (none, bty))) e1' e2) ∧ rρ = ev0' :: evs ∧
            σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, M⟩ : CoreRt) %σ₂ %([] : List CoreRt)
          %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim

/-- THE WEAK-SEQUENCING RULE at the wildcard pattern (S1b DRIFT TEST
    — the `wps_seq` clone over the Ewseq lane; same jump-aware
    four-way proof: value-beta / annot-beta / frame step / jump
    transfer). -/
theorem wps_wseq {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M Ls (fun w ρ' => wps M Ls
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wps M Ls Ψ (Expr a (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofVal w) e2))).to_eq]
    simp only [wps.pre, toVal_ofVal, toVal_wseq_node, jumpRedex?_wseq,
      jumpRedex?_ofVal]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H with H
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases w with
      | pure v => exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.wseq_pure, rfl, rfl⟩⟩
      | annot ds v => exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.wseq_annot, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds, v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩
    · exact absurd hs' (fun h => Step.val_elim h)
    · -- LETW-PURE: successor (e2, ρ, σ)
      obtain rfl : w = .pure v := by
        cases w with
        | pure v' => simpa [ofVal] using he1
        | annot ds' v' => exact absurd he1 (by simp [ofVal])
      obtain ⟨re, rρ, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
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
    · -- LETW-ANNOT: successor ({ds}e2, ρ, σ); exit through wps_annot
      obtain rfl : w = .annot ds v := by
        cases w with
        | pure v' => exact absurd he1 (by simp [ofVal])
        | annot ds' v' =>
          obtain ⟨h1, h2⟩ : ds' = ds ∧ v' = v := by simpa [ofVal] using he1
          rw [h1, h2]
      obtain ⟨re, rρ, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
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
    · rw [jumpRedex?_ofVal] at hj; cases hj
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      -- the jump clauses are the same formula through the Cwseq
      -- frame (`jumpRedex? (Ewseq …) = jumpRedex? e1`)
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
          e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr]
      iintro H
      iexact H
    | none =>
      -- e1 steps: inversion factor + congruence lift + Löb
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
          e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
            r'.e e2), r'.ρ, M⟩, σ', [],
          ⟨Step.wseq_ctx hjr hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
          ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Ewseq (Pattern pa
            (CaseBase (none, bty))) e1' e2) ∧ rρ = ev0' :: evs ∧
            σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, M⟩ : CoreRt) %σ₂ %([] : List CoreRt)
          %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [hjr] at hj; cases hj

/-! ## The branch/entry rules (S3 — the engine's measured
granularity: Eif's big-step guard via the pure-evaluator premise,
Esave's valueFromPexprs fast-path, Ecase's value-scrutinee
selection; each one deterministic engine step, certified per-rule in
Soundness.lean) -/

/-- Eif, true branch (donor `wps_if`, lifting.v:1256, at the
    engine's big-step-guard granularity; the pure evaluator premise
    is certified against `full_eval_pexpr` by the bridge). -/
theorem wps_if_true {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack)
    (hg : evalPexpr M.extern ρ g = some Vtrue) :
    wps M Ls Ψ e2 ρ ⊢ wps M Ls Ψ (Expr a (Eif g e2 e3)) ρ := by
  rw [(wps_unfold (e := Expr a (Eif g e2 e3))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Eif g e2 e3)) = none from rfl,
    show jumpRedex? (Expr a (Eif g e2 e3)) = none from rfl]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.if_true hg, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  rcases hs.if_inv with ⟨-, hout⟩ | ⟨hg', -⟩
  · obtain ⟨re, rρ, rM⟩ := r
    simp only at hlbl
    obtain rfl : M = rM := hlbl.symm
    obtain ⟨hre, hrρ, hσ⟩ : re = e2 ∧ rρ = ρ ∧ σ₂ = σ₁ := by
      simpa [Prod.mk.injEq] using hout
    obtain rfl : e2 = re := hre.symm
    subst hrρ
    obtain rfl : σ₁ = σ₂ := hσ.symm
    imod Hclose with -
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iexact H
  · rw [hg] at hg'; cases hg'

/-- Eif, false branch. -/
theorem wps_if_false {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack)
    (hg : evalPexpr M.extern ρ g = some Vfalse) :
    wps M Ls Ψ e3 ρ ⊢ wps M Ls Ψ (Expr a (Eif g e2 e3)) ρ := by
  rw [(wps_unfold (e := Expr a (Eif g e2 e3))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Eif g e2 e3)) = none from rfl,
    show jumpRedex? (Expr a (Eif g e2 e3)) = none from rfl]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.if_false hg, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  rcases hs.if_inv with ⟨hg', -⟩ | ⟨-, hout⟩
  · rw [hg] at hg'; cases hg'
  · obtain ⟨re, rρ, rM⟩ := r
    simp only at hlbl
    obtain rfl : M = rM := hlbl.symm
    obtain ⟨hre, hrρ, hσ⟩ : re = e3 ∧ rρ = ρ ∧ σ₂ = σ₁ := by
      simpa [Prod.mk.injEq] using hout
    obtain rfl : e3 = re := hre.symm
    subst hrρ
    obtain rfl : σ₁ = σ₂ := hσ.symm
    imod Hclose with -
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iexact H

/-- Esave ENTRY (one_step0's valueFromPexprs fast-path TAU): verify
    the save body at the parameter-bound env. -/
theorem wps_save {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) {cvals : List value}
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hvals : valueFromPexprs (saveParamPexprs ps) = some cvals) :
    wps M Ls Ψ body (bindSaveParams ps cvals (ev0 :: evs)) ⊢
      wps M Ls Ψ (Expr a (Esave sb ps body)) (ev0 :: evs) := by
  rw [(wps_unfold (e := Expr a (Esave sb ps body))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Esave sb ps body)) = none from rfl,
    show jumpRedex? (Expr a (Esave sb ps body)) = none from rfl]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.save hvals, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨cvals', ev0', evs', hρeq, hvals', hout⟩ := hs.save_inv
  obtain rfl : cvals = cvals' := Option.some.inj (hvals.symm.trans hvals')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = body ∧
      rρ = bindSaveParams ps cvals (ev0 :: evs) ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  obtain rfl : body = re := hre.symm
  subst hrρ
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- Ecase at a VALUE scrutinee (the engine's substitution TAU; the
    no-match ILLTYPED refusal is excluded by the selection
    premise). -/
theorem wps_case_value {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (pe : generic_pexpr Unit sym) (pats : List (pattern × CoreExpr))
    {cval : value} {e' : CoreExpr} (ρ : EnvStack)
    (hv : valueFromPexpr pe = some cval)
    (hsel : select_case subst_sym_expr cval pats = some e') :
    wps M Ls Ψ e' ρ ⊢ wps M Ls Ψ (Expr a (Ecase pe pats)) ρ := by
  rw [(wps_unfold (e := Expr a (Ecase pe pats))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Ecase pe pats)) = none from rfl,
    show jumpRedex? (Expr a (Ecase pe pats)) = none from rfl]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨e', ρ, M⟩, σ₁, [], ⟨Step.case_value hv hsel, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨cval', e'', hv', hsel', hout⟩ := hs.case_inv
  obtain rfl : cval = cval' := Option.some.inj (hv.symm.trans hv')
  obtain rfl : e' = e'' := Option.some.inj (hsel.symm.trans hsel')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = e' ∧ rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  obtain rfl : e' = re := hre.symm
  subst hrρ
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- PURE at a non-value pexpr (S4): ONE deterministic engine step
    big-step-evaluating the pure expression through the certified
    evaluator (one_step0's Epure EVAL arm; `Step.pure_eval`); the
    successor is the canonical value injection, so the rule lands in
    the postcondition directly. Stated at `[]` node annotations (the
    canonical cone — a non-canonically-annotated value successor
    would fall outside the mirror's value classification, slice
    notes §D3). -/
theorem wps_pure {Ψ : SpikeVal → EnvStack → IProp GF}
    (pe : generic_pexpr Unit sym) (ρ : EnvStack) {v : value}
    (hnv : valueFromPexpr pe = none) (hv : evalPexpr M.extern ρ pe = some v) :
    Ψ (.pure v) ρ ⊢ wps M Ls Ψ (Expr ([] : List annot) (Epure pe)) ρ := by
  rw [(wps_unfold (e := Expr ([] : List annot) (Epure pe))).to_eq]
  simp only [wps.pre, toVal_pure_none hnv, jumpRedex?_pure]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.pure_eval hnv hv, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨v', -, hv', hout⟩ := hs.pure_inv
  obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Epure (Pexpr [] () (PEval v))) ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · rw [show Expr ([] : List annot) (Epure (Pexpr [] () (PEval v))) =
      ofVal (.pure v) from rfl]
    iapply wps_ofVal (.pure v) ρ
    iexact H

/-- ACTION_EVAL for a load with an unevaluated pointer operand (S4):
    ONE deterministic engine step evaluating the operand through the
    certified evaluator to the canonical load redex, over which the
    certified load axiom then applies (`Step.load_eval`). -/
theorem wps_load_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 : generic_pexpr Unit sym) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue}
    (hnv2 : valueFromPexpr pe2 = none)
    (hv2 : evalPexpr M.extern ρ pe2 = some (Vobject (OVpointer pv))) :
    wps M Ls Ψ (loadExpr loc ann ty pv mo) ρ ⊢
      wps M Ls Ψ (loadOpRedex loc ann ty pe2 mo) ρ := by
  rw [(wps_unfold (e := loadOpRedex loc ann ty pe2 mo)).to_eq]
  simp only [wps.pre, loadOpRedex, toVal_action_node, jumpRedex?_action]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.load_eval hnv2 hv2, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', hv2', hout⟩ := hs.load_op_inv hnv2
  obtain rfl : pv = pv' := by
    simpa using Option.some.inj (hv2.symm.trans hv2')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = loadExpr loc ann ty pv mo ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq, loadExpr] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-! ## The Specified-binder sequencing rule (S4)

`lets Specified(x) = e1 in e2` — the load-result unwrapping idiom
(Step.lean `specPat`): the bound value must be a `Vloaded
(LVspecified ov)` (the premise's value channel carries the shape
fact — a mismatched shape is the engine's update_env failwithI
PANIC, excluded because the rule then provides no step and the WP's
reducibility obligation could not be met), and the continuation is
verified at the payload-bound environment. -/

theorem wps_seq_spec {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa pb : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M Ls (fun w ρ' => iprop(∃ (ov : object_value),
        ⌜w.val = Vloaded (LVspecified ov)⌝ ∗
        wps M Ls (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2
          (update_env (specPat pa pb x bty) (Vloaded (LVspecified ov)) ρ')))
      e1 (ev0 :: evs) ⊢
      wps M Ls Ψ (Expr a (Esseq (specPat pa pb x bty) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (specPat pa pb x bty)
        (ofVal w) e2))).to_eq]
    simp only [wps.pre, toVal_ofVal, toVal_sseq_node, jumpRedex?_sseq,
      jumpRedex?_ofVal]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H with ⟨%ov, %hval, Hinner⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    cases w with
    | pure v =>
      obtain rfl : v = Vloaded (LVspecified ov) := hval
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_spec_pure, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩
      · exact absurd hs' (fun h => Step.val_elim h)
      · exact (specPat_ne_base hpat.symm).elim
      · exact (specPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain rfl : ov = ov' := by simpa [ofVal] using he1
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hσ⟩ : re = e2 ∧
            rρ = update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov)) (ev0 :: evs) ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq] using hout
        subst hrρ
        obtain rfl : e2 = re := hre.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · rw [show (fun u ρ'' =>
            Ψ (SpikeVal.mergeInto (SpikeVal.pure
              (Vloaded (LVspecified ov))) u) ρ'') = Ψ from rfl]
          iexact Hinner
      · exact absurd he1 (by simp [ofVal])
      · exact (symPat_ne_spec hpat).elim
    | annot ds v =>
      obtain rfl : v = Vloaded (LVspecified ov) := hval
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_spec_annot, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩
      · exact absurd hs' (fun h => Step.val_elim h)
      · exact (specPat_ne_base hpat.symm).elim
      · exact (specPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact absurd he1 (by simp [ofVal])
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain ⟨rfl, rfl⟩ : ds = ds' ∧ ov = ov' := by
          simpa [ofVal] using he1
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot ds e2) ∧
            rρ = update_env (specPat pa pb x bty)
              (Vloaded (LVspecified ov)) (ev0 :: evs) ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrρ
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · rw [show (fun u ρ'' =>
            Ψ (SpikeVal.mergeInto (SpikeVal.annot ds
              (Vloaded (LVspecified ov))) u) ρ'') =
            (fun u ρ'' => Ψ (SpikeVal.merge ds u) ρ'') from rfl]
          iapply wps_annot ds e2 _ $$ Hinner
      · exact (symPat_ne_spec hpat).elim
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (specPat pa pb x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H
      iexact H
    | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (specPat pa pb x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Esseq (specPat pa pb x bty)
            r'.e e2), r'.ρ, M⟩, σ', [],
          ⟨Step.sseq_ctx hjr hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
          ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, he1, _, _⟩
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Esseq (specPat pa pb x bty)
            e1' e2) ∧ rρ = ev0' :: evs ∧
            σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, M⟩ : CoreRt) %σ₂ %([] : List CoreRt)
          %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [he1, toVal_ofVal] at htv; cases htv

/-! ## The plain-symbol-binder sequencing rule (list-reverse phase A)

`lets x = e1 in e2` at a bare symbol pattern — the memop result's
binding idiom (Step.lean `symPat`). The premise's value channel
carries the PURE-value shape fact (the mirror's sym-binder beta is
deliberately restricted to bare values — Step.lean, the recorded
fail-closed divergence), and the continuation is verified at the
value-bound environment. -/

theorem wps_seq_sym {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M Ls (fun w ρ' => iprop(∃ (v : value),
        ⌜w = SpikeVal.pure v⌝ ∗
        wps M Ls Ψ e2 (update_env (symPat pa x bty) v ρ')))
      e1 (ev0 :: evs) ⊢
      wps M Ls Ψ (Expr a (Esseq (symPat pa x bty) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (symPat pa x bty)
        (ofVal w) e2))).to_eq]
    simp only [wps.pre, toVal_ofVal, toVal_sseq_node, jumpRedex?_sseq,
      jumpRedex?_ofVal]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H with ⟨%v, %hval, Hinner⟩
    subst hval
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_sym_pure, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
        ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
        ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
        ⟨pa', x', bty', v', _, _, hpat, he1, _, hout⟩
    · exact absurd hs' (fun h => Step.val_elim h)
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · rw [jumpRedex?_ofVal] at hj; cases hj
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
      obtain rfl : v = v' := by simpa [ofVal] using he1
      obtain ⟨re, rρ, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      obtain ⟨hre, hrρ, hσ⟩ : re = e2 ∧
          rρ = update_env (symPat pa x bty) v (ev0 :: evs) ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      subst hrρ
      obtain rfl : e2 = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iexact Hinner
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (symPat pa x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H
      iexact H
    | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (symPat pa x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Esseq (symPat pa x bty)
            r'.e e2), r'.ρ, M⟩, σ', [],
          ⟨Step.sseq_ctx hjr hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
          ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, he1, _, _⟩
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Esseq (symPat pa x bty)
            e1' e2) ∧ rρ = ev0' :: evs ∧
            σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, M⟩ : CoreRt) %σ₂ %([] : List CoreRt)
          %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [he1, toVal_ofVal] at htv; cases htv
      · rw [he1, toVal_ofVal] at htv; cases htv

/-! ## The pointer-test memop rules (list-reverse phase A)

The null test as the ENGINE's own pointer memop, at the wps stratum:
`wps_memop_ptreq` consumes the pure single-layer `eqPtrval` verdict
(Heap.lean's `eqPtrval_null_null` / `eqPtrval_cell_null` /
`eqPtrval_null_cell` discharge `hres` at the fragment's shapes);
`wps_memop_eval` is the one-step operand evaluation into the
canonical value-operand redex (the memop analog of
`wps_load_eval`). -/

/-- The pointer-equality memop at VALUE operands: one deterministic
    engine step delivering the boolean verdict as a BARE pure value
    (no Eannot residue — the memop protocol's continuation,
    Core_reduction.lean:484). State untouched (`hres` pins the
    single-layer state-verbatim verdict — exactly the null-test
    arms). -/
theorem wps_memop_ptreq {Ψ : SpikeVal → EnvStack → IProp GF}
    (pv1 pv2 : CerbMem.PointerValue) {b : Bool} (ρ : EnvStack)
    (hres : ∀ σ : Mem, applyMemM (CerbMem.eqPtrval default pv1 pv2) σ =
      some (b, σ)) :
    Ψ (.pure (boolValue b)) ρ ⊢
      wps M Ls Ψ (memopPtrEqVals (Vobject (OVpointer pv1))
        (Vobject (OVpointer pv2))) ρ := by
  rw [(wps_unfold (e := memopPtrEqVals (Vobject (OVpointer pv1))
    (Vobject (OVpointer pv2)))).to_eq]
  simp only [wps.pre, memopPtrEqVals, memopRedex, toVal_memop_node,
    jumpRedex?_memop]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [],
      ⟨Step.memop_ptreq rfl rfl (hres σ₁), rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨b', σ'', hmem, hout⟩ := hs.memop_ptreq_inv rfl rfl
  rw [hres σ₁] at hmem
  obtain ⟨rfl, rfl⟩ : b = b' ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Epure (Pexpr [] ()
      (PEval (boolValue b)))) ∧ rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · rw [show Expr ([] : List annot) (Epure (Pexpr [] ()
        (PEval (boolValue b)))) = ofVal (.pure (boolValue b)) from rfl]
    iapply wps_ofVal (.pure (boolValue b)) ρ
    iexact H

/-- Memop-operand evaluation: ONE deterministic engine step
    big-step-evaluating both operands through the certified
    evaluator into the canonical value-operand memop redex
    (`Step.memop_eval`). -/
theorem wps_memop_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (mop : memop) (pe1 pe2 : generic_pexpr Unit sym)
    {v1 v2 : value} (ρ : EnvStack)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hv1 : evalPexpr M.extern ρ pe1 = some v1)
    (hv2 : evalPexpr M.extern ρ pe2 = some v2) :
    wps M Ls Ψ (memopRedex mop
      [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) ρ ⊢
      wps M Ls Ψ (memopRedex mop [pe1, pe2]) ρ := by
  rw [(wps_unfold (e := memopRedex mop [pe1, pe2])).to_eq]
  simp only [wps.pre, memopRedex, toVal_memop_node, jumpRedex?_memop]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.memop_eval hnv hv1 hv2, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨v1', v2', hv1', hv2', hout⟩ := hs.memop_op_inv hnv
  obtain rfl : v1 = v1' := Option.some.inj (hv1.symm.trans hv1')
  obtain rfl : v2 = v2' := Option.some.inj (hv2.symm.trans hv2')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Ememop mop
      [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- ACTION_EVAL for a store with unevaluated pointer/value operands
    (the store analog of `wps_load_eval` — the loop-carried interior
    store's entry step): ONE deterministic engine step evaluating
    the operands into the canonical store redex, over which the
    certified store axiom then applies (`Step.store_eval`). -/
theorem wps_store_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 pe3 : generic_pexpr Unit sym) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue} {cv : value}
    (hnv2 : valueFromPexpr pe2 = none)
    (hnv3 : valueFromPexpr pe3 = none)
    (hv2 : evalPexpr M.extern ρ pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr M.extern ρ pe3 = some cv) :
    wps M Ls Ψ (storeExpr loc ann ty pv cv mo) ρ ⊢
      wps M Ls Ψ (storeOpRedex loc ann ty pe2 pe3 mo) ρ := by
  rw [(wps_unfold (e := storeOpRedex loc ann ty pe2 pe3 mo)).to_eq]
  simp only [wps.pre, storeOpRedex, toVal_action_node, jumpRedex?_action]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [],
      ⟨Step.store_eval hnv2 hnv3 hv2 hv3, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', cv', hv2', hv3', -, hout⟩ := hs.store_op_inv hnv2
  obtain rfl : pv = pv' := by
    simpa using Option.some.inj (hv2.symm.trans hv2')
  obtain rfl : cv = cv' := Option.some.inj (hv3.symm.trans hv3')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = storeExpr loc ann ty pv cv mo ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq, storeExpr] using hout
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

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
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt ty mv) :
    iprop(pointsToCell (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell pv (.own 1) ty (CerbMem.memValueToBytes [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann ty pv cv mo) ρ := by
  rw [(wps_unfold (e := storeExpr loc ann ty pv cv mo)).to_eq]
  simp only [wps.pre, show toVal (storeExpr loc ann ty pv cv mo) = none from rfl,
    show jumpRedex? (storeExpr loc ann ty pv cv mo) = none from rfl]
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
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.store_canonical hmv hrun, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨mv', fp', σ'', hmv', hmem', hout⟩ := hstep.store_inv
  obtain rfl : mv = mv' := Option.some.inj (hmv.symm.trans hmv')
  rw [hrun] at hmem'
  obtain ⟨rfl, rfl⟩ : fp' = CerbMem.Footprint.FP .W addr (CerbMem.sizeofCtype ty) ∧
      σ'' = CerbMem.writeBytesTo σ₁ addr (CerbMem.memValueToBytes [] mv).2 := by
    have h := Option.some.inj hmem'.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
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
      wps M Ls Ψ (loadExpr loc ann ty pv mo) ρ := by
  rw [(wps_unfold (e := loadExpr loc ann ty pv mo)).to_eq]
  simp only [wps.pre, show toVal (loadExpr loc ann ty pv mo) = none from rfl,
    show jumpRedex? (loadExpr loc ann ty pv mo) = none from rfl]
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
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.load_canonical hrun, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨fp', mval', σ'', hmem', hout⟩ := hstep.load_inv
  rw [hrun] at hmem'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ :
      (fp' = CerbMem.Footprint.FP .R addr (CerbMem.sizeofCtype ty) ∧
        mval' = decodeCell ⟨addr, ty, bs⟩) ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem'.symm
    exact ⟨⟨congrArg (fun p => p.1.1) h, congrArg (fun p => p.1.2) h⟩,
      (congrArg Prod.snd h).symm⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
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

/-- INTERIOR int load small axiom (S4, the array exhibit): loading
    at `int` from an interior offset of an owned cell whose type is
    big enough delivers the DECODE OF THE BYTE SLICE; the cell rides
    through untouched. The decode-independence premise (`hdec`) is
    the interior analog of `CellCoh.dec_indep` — the exhibit
    discharges it per element from its seeded byte images. Stated
    over the raw ghost `pointsTo` (the cell's id and base address
    explicit — the interior pointer is `cellPtr id (a + off)`). -/
theorem wps_load_interior {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aty : ctype) (id a : Int) (off : Nat) (mo : memory_order)
    (dq : DFrac) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {mv : CerbMem.MemValue}
    (hbound : off + CerbMem.sizeofCtype intTy ≤ CerbMem.sizeofCtype aty)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue lum fpm (a + (off : Int))
      intTy ((bs.drop off).take (CerbMem.sizeofCtype intTy)) = mv) :
    iprop(pointsTo (GF := GF) id dq (SpikeCell.mk a aty bs) ∗
      (∀ fp, pointsTo id dq (SpikeCell.mk a aty bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann intTy (cellPtr id (a + (off : Int))) mo)
        ρ := by
  rw [(wps_unfold
    (e := loadExpr loc ann intTy (cellPtr id (a + (off : Int))) mo)).to_eq]
  simp only [wps.pre,
    show toVal (loadExpr loc ann intTy (cellPtr id (a + (off : Int))) mo) =
      none from rfl,
    show jumpRedex? (loadExpr loc ann intTy
      (cellPtr id (a + (off : Int))) mo) = none from rfl]
  iintro ⟨Hpt, HΨ⟩ %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_iff σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨%m, %Hcoh, Hh⟩
  ihave %Hget : ⌜Iris.Std.PartialMap.get? m id = some (SpikeCell.mk a aty bs)⌝
      $$ [Hh Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hh $Hpt]
    itrivial
  have hcell : CellCoh σ₁ id ⟨a, aty, bs⟩ := Hcoh.cells id _ Hget
  have hrun := loadM_interior_int σ₁ id ⟨a, aty, bs⟩ off loc hcell hbound
  rw [hdec σ₁.lastUsedUnionMembers σ₁.funptrmap] at hrun
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.load_canonical hrun, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hstep, hlbl, rfl⟩ := Hstep
  obtain ⟨fp', mval', σ'', hmem', hout⟩ := hstep.load_inv
  rw [hrun] at hmem'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ :
      (fp' = CerbMem.Footprint.FP .R (a + (off : Int))
        (CerbMem.sizeofCtype intTy) ∧ mv = mval') ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem'.symm
    exact ⟨⟨congrArg (fun p => p.1.1) h,
      (congrArg (fun p => p.1.2) h).symm⟩,
      (congrArg Prod.snd h).symm⟩
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr [] (Eannot
        [DA_pos [] (CerbMem.Footprint.FP .R (a + (off : Int))
          (CerbMem.sizeofCtype intTy))]
        (Expr [] (Epure (Pexpr [] () (PEval (valueFromMemValue mv).2))))) ∧
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
        [DA_pos [] (CerbMem.Footprint.FP .R (a + (off : Int))
          (CerbMem.sizeofCtype intTy))]
        (Expr [] (Epure (Pexpr [] () (PEval (valueFromMemValue mv).2))))) =
      ofVal (.annot [DA_pos [] (CerbMem.Footprint.FP .R (a + (off : Int))
        (CerbMem.sizeofCtype intTy))] ((valueFromMemValue mv).2))
      from rfl]
    iapply (wps_ofVal
      (.annot [DA_pos [] (CerbMem.Footprint.FP .R (a + (off : Int))
        (CerbMem.sizeofCtype intTy))] ((valueFromMemValue mv).2)) ρ)
    iapply HΨ
    iexact Hpt

/-! ## Block specifications, THE COLLAPSE, and the loop rules

The collapse into the base Iris WP (the sole adequacy interface).
S3 form as pre-declared: `wps_sound` gains the `blockSpecs` premise
and the one Löb-tied jump case (the donor `wps_block_rec` analog,
probe report §2 — the mutual-□ + iLöb of the donor SPLITS: the
per-label proofs, `blockSpecs_intro`, need NO Löb because the jump
clause breaks the back-edge circularity; the single Löb induction
lands here, simultaneously the stmt-WP-to-WP collapse). -/

/-- All block specifications (donor `[∗ map] wps_block`,
    lifting.v:1302/1306's premise collection, flat form —
    unregistered labels are vacuous because the lookup premise is
    unsatisfiable; probe `blockSpecs`). The jump-time env is
    quantified in cons shape (registered continuations are
    sseq-extended and closed under the registration discipline, so
    per-label proofs quantify it freely; the jump binds the
    parameters over whatever env the jump arrives in). -/
abbrev blockSpecs (M : MachineCtx) (Ls : LabelSpec GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) : IProp GF :=
  iprop(□ ∀ (l : sym) (params : List (sym × core_base_type))
    (cont : CoreExpr) (vs : List value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)),
    ⌜lookupLabel M.labels l = some (params, cont)⌝ -∗ Ls l vs (ev0 :: evs) -∗
      wps M Ls Ψ cont (bindArgs params vs (ev0 :: evs)))

/-- THE PER-LABEL INVARIANT RULE (partial correctness, the default
    loop rule): assembling the block specifications needs NO Löb and
    no mutual assumption — the back-edge circularity is broken by
    the jump clause (each body's own back edges discharge against
    `Ls` directly, via `wps_run`). This is where the label-context
    shape pays: the donor `wps_block_rec`'s mutual-□ premise is not
    needed; its Löb lives in `wps_sound`. -/
theorem blockSpecs_intro {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l params cont vs ev0 evs,
      lookupLabel M.labels l = some (params, cont) →
      Ls l vs (ev0 :: evs) ⊢ wps (GF := GF) M Ls Ψ cont
        (bindArgs params vs (ev0 :: evs))) :
    ⊢ blockSpecs M Ls Ψ := by
  unfold blockSpecs
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %hQ HLs
  iapply h l params cont vs ev0 evs hQ $$ HLs

/-- THE INVARIANT+VARIANT RULE (the well-founded derivation
    principle over the certified jump layer): prove each label body
    assuming the block specifications only for STRICTLY SMALLER
    measures — classical well-founded induction on a `Nat`-valued
    variant of the jump arguments, no Löb, no step-indexing. The
    measure's product (per-iteration step bounds → the unconditional
    production `.done` equation) is the termination-accounting
    item's slot (arc plan §Phase 2), not this rule's: here the
    variant buys the DERIVATION PRINCIPLE (bodies may consult
    smaller-measure specs as ordinary hypotheses). -/
theorem blockSpecs_intro_variant {Ψ : SpikeVal → EnvStack → IProp GF}
    (μ : sym → List value → Nat)
    (h : ∀ l params cont vs ev0 evs,
      lookupLabel M.labels l = some (params, cont) →
      (∀ l' params' cont' vs' ev0' evs',
        lookupLabel M.labels l' = some (params', cont') → μ l' vs' < μ l vs →
        Ls l' vs' (ev0' :: evs') ⊢ wps (GF := GF) M Ls Ψ cont'
          (bindArgs params' vs' (ev0' :: evs'))) →
      Ls l vs (ev0 :: evs) ⊢ wps (GF := GF) M Ls Ψ cont
        (bindArgs params vs (ev0 :: evs))) :
    ⊢ blockSpecs M Ls Ψ := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hQ => ?_
  -- strong induction on the measure, purely at the meta level
  suffices hind : ∀ (n : Nat) l params cont vs ev0 evs,
      lookupLabel M.labels l = some (params, cont) → μ l vs < n →
      Ls l vs (ev0 :: evs) ⊢ wps (GF := GF) M Ls Ψ cont
        (bindArgs params vs (ev0 :: evs)) by
    exact hind (μ l vs + 1) l params cont vs ev0 evs hQ (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro l params cont vs ev0 evs _ h0; cases h0
  | succ n ih =>
    intro l params cont vs ev0 evs hQ hlt
    refine h l params cont vs ev0 evs hQ ?_
    intro l' params' cont' vs' ev0' evs' hQ' hμ
    exact ih l' params' cont' vs' ev0' evs' hQ' (by omega)

/-- THE LÖB-TIED ELIMINATION (the donor `wps_block_rec` analog + the
    stmt-WP-to-WP collapse in one — probe `wps_sound`, now against
    the REAL engine mirror): under the block specifications, the
    statement WP entails the base Iris WP with the value-channel
    postcondition. ONE Löb induction ties every back edge: at a jump
    redex the (□) block spec turns the label precondition into the
    body's statement WP, and the induction hypothesis — a step
    later, aligned with the jump step's ▷ — turns that into the base
    WP. Partial correctness (donor parity).

    This is where the jump clause is CERTIFIED against the step
    relation: `Step.run_of_jumpRedex` (reducibility at a registered
    jump redex) and `Step.jump_inv` (every step at a jump redex is
    THE jump, successor independent of the decomposition — the
    engine's context-discard, certified in Soundness.lean against
    step_ctx's Erun arm). S3 pre-declared statement change: gains
    the `blockSpecs` premise (the phase-1 form was the jump-free
    unconditional collapse). -/
theorem wps_sound {Ψ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr)
    (ρ : EnvStack) :
    blockSpecs M Ls Ψ ⊢
      iprop(wps M Ls Ψ e ρ -∗
        WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, Ψ w.w w.ρ }}) := by
  iloeb as IH generalizing %e %ρ
  cases htv : toVal e with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wps_unfold.to_eq, wp_unfold.to_eq]
    simp only [wps.pre, toVal_ofVal, wp.pre, language_toVal_eq, toValRt_mk,
      Option.map_some]
    iintro #HB Hwps
    imod Hwps with Hwps
    imodintro
    iexact Hwps
  | none =>
    have htoval : ToVal.toVal (Val := CoreRVal) (⟨e, ρ, M⟩ : CoreRt) = none := by
      rw [language_toVal_eq, toValRt_mk, htv]
      rfl
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro #HB Hwps
      iapply wp_lift_step htoval
      iintro %σ₁ %ns %obs %obs' %nt Hσ
      imod Hwps with ⟨%params, %cont, %vs, %ev0, %evs, %hρ, %hl, %hvs, HLs⟩
      subst hρ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨cont, bindArgs params vs (ev0 :: evs), M⟩, σ₁, [],
          ⟨Step.run_of_jumpRedex hjr hl hvs, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      obtain ⟨params', cont', vs', ev0', evs', hρ', hl', hvs', hout⟩ :=
        hs.jump_inv hjr
      obtain ⟨rfl, rfl⟩ : params = params' ∧ cont = cont' := by
        rw [hl] at hl'
        exact ⟨congrArg Prod.fst (Option.some.inj hl'),
          congrArg Prod.snd (Option.some.inj hl')⟩
      obtain rfl : vs = vs' := by
        rw [hvs] at hvs'
        exact Option.some.inj hvs'
      obtain ⟨re, rρ, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      obtain ⟨hre, hrρ, hσ⟩ : re = cont ∧
          rρ = bindArgs params vs (ev0 :: evs) ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      obtain rfl : cont = re := hre.symm
      subst hrρ
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · simp only [List.length_nil, Nat.add_zero]
        iexact Hσ
      isplitr []
      · ihave Hwps' := HB $$ %l %params %cont %vs %ev0 %evs %hl HLs
        iapply IH $$ %cont %(bindArgs params vs (ev0 :: evs)) HB Hwps'
      · simp only [Algebra.BigOpL.bigOpL_nil]
        itrivial
    | none =>
      rw [wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro #HB Hwps
      iapply wp_lift_step htoval
      iintro %σ₁ %ns %obs %obs' %nt Hσ
      imod Hwps $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, Hwps⟩
      imodintro
      isplitr
      · ipureintro
        exact hred
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, hnil⟩ := Hstep
      have hr : r = (⟨r.e, r.ρ, M⟩ : CoreRt) := by
        obtain ⟨re, rρ, rM⟩ := r
        simp only at hlbl
        rw [hlbl]
      imod Hwps $$ %r %σ₂ %eₜ %(⟨hs, hlbl, hnil⟩ :
          ((⟨e, ρ, M⟩ : CoreRt), σ₁) -<obs>-> (r, σ₂, eₜ)) Hcred
        with ⟨HSI, Hwps⟩
      imodintro
      isplitl [HSI]
      · subst hnil
        simp only [List.length_nil, Nat.add_zero]
        iexact HSI
      isplitr []
      · rw [hr]
        iapply IH $$ %(r.e) %(r.ρ) HB Hwps
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
      wps M Ls
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
      wps M Ls
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
