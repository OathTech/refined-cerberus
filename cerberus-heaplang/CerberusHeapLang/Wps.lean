/-
CerberusHeapLang.Wps — the partial label-context judgment `wps`: the
judgment the loop exhibits are proved in.

THE SHAPE: the classical label-context statement logic (de Bruin
1981-style label-assumption judgments, the shape RefinedC's statement
judgment also takes), realized as a guarded fixpoint over the
fragment's `Step` via iris-lean's public Banach machinery
(`fixpoint`/`OFE.Contractive` — the same machinery `wp` itself is
built from; iris-lean untouched). `wps M Ls Ψ e ρ` is indexed by the
machine context `M` (whose derived `M.labels` is the current
procedure's static label map — Step.lean header note 3), the label
specification `Ls : LabelSpec GF` (`sym → List value → EnvStack →
IProp GF`: a precondition per registered label over the jump-argument
values and the jump-time environment), the postcondition `Ψ` over the
delivered value and the final environment, the expression, and the
live environment stack.

THE JUMP CLAUSE: `wps.pre` has three clauses (value / jump redex /
step). The jump clause fires at `jumpRedex? e` (Step.lean — the
syntactic image of `step_ctx`'s `Erun` context-discard through the
`Esseq`/`Eannot` spine) and demands: the label resolves in `M.labels`
(`lookupLabel`), the arguments evaluate under the CURRENT environment
by the pure evaluator (`evalPexprs`, certified against the engine's
`full_eval_pexpr` in Soundness.lean), the environment stack is
cons-shaped (the `update_env` panic exclusion), and the label's
precondition `Ls l vs ρ` holds — then TRACKING STOPS: a jump's
postcondition is the label's business, so the postcondition clash
that would sink a bind-style rule never forms. The collapse
`wps_sound` into iris-lean's WP carries the `blockSpecs` premise
(every registered body re-establishes its label's precondition) and
is the package's one Löb induction; its jump case is where the clause
meets the step relation (`Step.jump_inv`/`Step.run_of_jumpRedex`).

THE CONTENTS: the memory rules as corollaries of the atomic step
specifications (`wps_of_atomic`; `wps_store`/`wps_load`, the typed
sub-range forms `wps_load_at`/`wps_store_at`/`wps_load_cell_at`/
`wps_store_cell_at`, the plain-value forms `wps_store_plain`/
`wps_load_plain`); the allocation rule `wps_create` from the abstract
capacity `allocCap (req :: rest)` (Heap.lean; the exact-cursor form
`wps_create_cursor_internal` is heap-implementation vocabulary); the
sequencing rules at the three binder shapes and `Ewseq` (`wps_seq`,
`wps_seq_spec`, `wps_seq_sym`, `wps_wseq`); the conditional with the
guard's verdict as a pure premise (`wps_if`; `wps_if_true`/`_false`
derived); value-scrutinee case (`wps_case_value`); block entry and the
jump (`wps_save` at evaluated initializers, `wps_run`); operand
evaluation and the `PtrEq` memop (`wps_load_eval`, `wps_store_eval`,
`wps_memop_eval`, `wps_memop_ptreq`); the pure exit and the
annotation layer (`wps_pure`, `wps_ofVal`, `wps_annot`,
`wps_annot_reindex`); consequence (`wps_wand`, `wps_fupd`,
`wps_mono_Ls`); framing at the statement level (`wps_frame`, and
`wps_frame_labels` through the framed label context `frameLs`, which
carries a frame across every back edge); the per-label invariant rule
`blockSpecs_intro` (no Löb) with `blockSpecs_frame`/`blockSpecs_mono`;
and the collapses `wps_sound`/`wps_sound_frame` into the raw WP — the
adequacy interface (Adequacy.lean). There is deliberately no raw-WP
sequencing rule and no `Language.Context` instance: both are false
once labels are populated (Rules.lean and Lang.lean headers).
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
        ⌜evalPexprs M.tagDefs M.extern ρ lp.2 = some vs⌝ ∗ Ls lp.1 vs ρ)
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

/-- LIFTING AN ATOMIC STEP SPECIFICATION (Rules.lean `AtomicStep`) to
    the statement judgment: the one-step-to-value shape lands in the
    step clause (mask pair ⊤/∅), the later is introduced, the credit
    dropped, and the delivered value closes through `wps_ofVal`.
    Every memory rule below is this lemma applied to its small axiom's
    atomic specification (professor review 1, required fix 8). -/
theorem wps_of_atomic {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr}
    {ρ : EnvStack} {c : Nat} {P : IProp GF} {Q : SpikeVal → IProp GF}
    (h : AtomicStep M e ρ c P Q) (hnv : toVal e = none)
    (hnj : jumpRedex? e = none) :
    iprop(P ∗ (∀ w : SpikeVal, Q w -∗ Ψ w ρ)) ⊢ wps M Ls Ψ e ρ := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, hnv, hnj]
  iintro ⟨HP, HΨ⟩ %σ₁ %ns %obs %obs' %nt Hσ
  cases obs with
  | cons o _ => exact o.elim
  | nil =>
  simp only [List.nil_append]
  imod (h ⊤ ∅ Std.LawfulSet.empty_subset σ₁ ns obs' nt) $$ [$HP $Hσ]
    with ⟨%hred, Hcont⟩
  imodintro
  isplitr
  · ipureintro
    exact hred
  inext
  iintro %r %σ₂ %eₜ %Hstep -
  imod Hcont $$ %r %σ₂ %eₜ %Hstep with ⟨Hσ', %w, %hw, HQ⟩
  obtain ⟨rfl, rfl, -⟩ := hw
  imodintro
  isplitl [Hσ']
  · iexact Hσ'
  · iapply (wps_ofVal w ρ)
    iapply HΨ $$ HQ

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
    (hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some vs) :
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

/-- POSTCONDITION-MODALITY ABSORPTION (iris `wp_fupd`): a statement WP
    whose postcondition sits under a fancy update is a statement WP —
    the update is paid at the value exit (the value clause is
    fupd-headed), passes through a jump untouched (the jump clause
    is Ψ-independent), and rides through steps by Löb. This is what
    lets a client perform a GHOST update (e.g. `pointsToView_persist`)
    after an access, inside the statement logic. -/
theorem wps_fupd {Ψ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr)
    (ρ : EnvStack) :
    wps M Ls (fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) e ρ ⊢ wps M Ls Ψ e ρ := by
  iloeb as IH generalizing %e %ρ
  cases htv : toVal e with
  | some w =>
    rw [wps_unfold.to_eq, wps_unfold.to_eq]
    simp only [wps.pre, htv]
    iintro H
    imod H with H
    iexact H
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H
      iexact H
    | none =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨$, H⟩
      imodintro
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      imod H $$ %r %σ₂ %eₜ %Hstep Hcred with ⟨$, H⟩
      imodintro
      iapply IH $$ %(r.e) %(r.ρ) H

/-- MONOTONICITY IN THE LABEL CONTEXT (the `wpt_mono_Ls` twin, QA-1/M-3):
    a label context pointwise entailed by another verifies more — the
    value clause is `Ls`-independent, the jump clause consults `Ls` once,
    steps ride by Löb. -/
theorem wps_mono_Ls {Ls₁ Ls₂ : LabelSpec GF} {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l vs ρ', Ls₁ l vs ρ' ⊢ Ls₂ l vs ρ') (e : CoreExpr) (ρ : EnvStack) :
    wps M Ls₁ Ψ e ρ ⊢ wps M Ls₂ Ψ e ρ := by
  iloeb as IH generalizing %e %ρ
  cases htv : toVal e with
  | some w =>
    rw [(wps_unfold (Ls := Ls₁)).to_eq, (wps_unfold (Ls := Ls₂)).to_eq]
    simp only [wps.pre, htv]
    iintro H
    iexact H
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      rw [(wps_unfold (Ls := Ls₁)).to_eq, (wps_unfold (Ls := Ls₂)).to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H
      imod H with ⟨%params, %cont, %vs, %ev0, %evs, %h1, %h2, %h3, HLs⟩
      imodintro
      iexists params, cont, vs, ev0, evs
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      iapply h lp.1 vs ρ $$ HLs
    | none =>
      rw [(wps_unfold (Ls := Ls₁)).to_eq, (wps_unfold (Ls := Ls₂)).to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨$, H⟩
      imodintro
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      imod H $$ %r %σ₂ %eₜ %Hstep Hcred with ⟨$, H⟩
      imodintro
      iapply IH $$ %(r.e) %(r.ρ) H

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

/-! ## Statement-level framing (alloc arc P4.2 — the R-05 closure)

The frame rule of the statement logic, in Reynolds/O'Hearn form: a
frame `R` rides along the WHOLE statement — through the value exit
AND across every back edge — by framing the label context pointwise.
`wps_frame` above frames the value channel only (the frame is
dropped at a jump); with `frameLs` the frame is carried by the label
preconditions, so nothing is lost. Loop clients state their
invariants UNFRAMED and obtain the arbitrary-frame theorems from
these rules (ListRevExhibit, TreeRotExhibit). -/

/-- Framing of a label context: every label precondition gains the
    frame `R`. -/
abbrev frameLs (R : IProp GF) (Ls : LabelSpec GF) : LabelSpec GF :=
  fun l vs ρ => iprop(Ls l vs ρ ∗ R)

/-- THE STATEMENT FRAME RULE (labels included): `wps M Ls Ψ e ρ ∗ R ⊢
    wps M (frameLs R Ls) (Ψ ∗ R) e ρ`. Value exit: the frame joins the
    postcondition; jump: the frame joins the label precondition (this
    is exactly what `frameLs` is for); step: Löb. -/
theorem wps_frame_labels {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (e : CoreExpr) (ρ : EnvStack) :
    wps M Ls Ψ e ρ ⊢
      iprop(R -∗ wps M (frameLs R Ls) (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ) := by
  iloeb as IH generalizing %e %ρ
  cases htv : toVal e with
  | some w =>
    rw [wps_unfold.to_eq, wps_unfold.to_eq]
    simp only [wps.pre, htv]
    iintro H HR
    imod H with H
    imodintro
    isplitl [H]
    · iexact H
    · iexact HR
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H HR
      imod H with ⟨%params, %cont, %vs, %ev0, %evs, %h1, %h2, %h3, HLs⟩
      imodintro
      iexists params, cont, vs, ev0, evs
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [HLs]
      · iexact HLs
      · iexact HR
    | none =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H HR %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨$, H⟩
      imodintro
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      imod H $$ %r %σ₂ %eₜ %Hstep Hcred with ⟨$, H⟩
      imodintro
      iapply IH $$ %(r.e) %(r.ρ) H HR

/-! ## The annotation layer (the R-i cost): the run-time Eannot
residue commutes with `wps`. Two steps: `wps_annot_reindex` — two
wraps of the SAME body differing only in the dyn-annotation payload
step in lockstep forever (annotations never influence fragment
stepping — they are race bookkeeping), so their judgments are
interderivable whenever the postconditions agree modulo `merge`
(Löb induction over `wps.pre`); `wps_annot` — the commuting rule
itself, whose annot-rooted-body case takes the ANNOTS merge step and
exits through the reindexing lemma. The value-side input is
`toVal_annot_cases`/`toVal_annot_none` (Rules.lean). -/

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

/-- `wps` commutes with the run-time dyn-annotation wrapper: to
    verify `{A}e`, verify `e` with the postcondition translated along
    `merge` (the merge case exits through the reindexing lemma). -/
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

/-- THE CONDITIONAL RULE (donor `wps_if`, lifting.v:1256, at the
    engine's big-step-guard granularity; QA-1/Q4: the guard's verdict
    is INSIDE THE LOGIC — a pure assertion `⌜evalPexpr … g = some
    (boolValue b)⌝`, so a guard whose value is known only from Iris-level
    facts needs no meta-level case split; the pure evaluator premise is
    certified against `full_eval_pexpr` by the bridge). -/
theorem wps_if {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack) (b : Bool) :
    iprop(⌜evalPexpr M.tagDefs M.extern ρ g = some (boolValue b)⌝ ∗
      wps M Ls Ψ (bif b then e2 else e3) ρ) ⊢
      wps M Ls Ψ (Expr a (Eif g e2 e3)) ρ := by
  rw [(wps_unfold (e := Expr a (Eif g e2 e3))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Eif g e2 e3)) = none from rfl,
    show jumpRedex? (Expr a (Eif g e2 e3)) = none from rfl]
  iintro ⟨%hg, H⟩ %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases b
    · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.if_false hg, rfl, rfl⟩⟩
    · exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.if_true hg, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  have hout : re = (bif b then e2 else e3) ∧ rρ = ρ ∧ σ₂ = σ₁ := by
    rcases hs.if_inv with ⟨hg', hout⟩ | ⟨hg', hout⟩ <;> cases b <;>
      first
        | (simpa [Prod.mk.injEq] using hout)
        | (rw [hg] at hg'; simp [boolValue] at hg')
  obtain ⟨rfl, rfl, rfl⟩ := hout
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- Eif, true branch — the `b := true` instance of `wps_if` with the
    verdict at the meta level (retained as a derived corollary). -/
theorem wps_if_true {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack)
    (hg : evalPexpr M.tagDefs M.extern ρ g = some Vtrue) :
    wps M Ls Ψ e2 ρ ⊢ wps M Ls Ψ (Expr a (Eif g e2 e3)) ρ := by
  iintro H
  iapply wps_if a g e2 e3 ρ true
  isplit
  · ipureintro; exact hg
  · rw [show (bif true then e2 else e3) = e2 from rfl]
    iexact H

/-- Eif, false branch — the `b := false` instance of `wps_if`. -/
theorem wps_if_false {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack)
    (hg : evalPexpr M.tagDefs M.extern ρ g = some Vfalse) :
    wps M Ls Ψ e3 ρ ⊢ wps M Ls Ψ (Expr a (Eif g e2 e3)) ρ := by
  iintro H
  iapply wps_if a g e2 e3 ρ false
  isplit
  · ipureintro; exact hg
  · rw [show (bif false then e2 else e3) = e3 from rfl]
    iexact H

/-- Esave ENTRY at VALUE initializers (one_step0's Esave TAU arm):
    verify the save body at the parameter-bound env. The literal
    instance of `wps_save`; one engine step. -/
theorem wps_save_vals {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
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
  obtain ⟨ev0', evs', hρeq, hout⟩ := hs.save_vals_inv hvals
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

/-- Esave PARAMETER EVALUATION (QA-1/H-1; one_step0's Esave EVAL arm,
    `Step.save_eval`): when the initializers are not all values, ONE
    deterministic engine step evaluates them through the certified
    evaluator and re-forms the node with literal initializers, over
    which `wps_save_vals` then applies. -/
theorem wps_save_eval {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) {cvals : List value} (ρ : EnvStack)
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (hvals : evalPexprs M.tagDefs M.extern ρ (saveParamPexprs ps) = some cvals) :
    wps M Ls Ψ (Expr a (Esave sb (saveParamsWithValues ps cvals) body)) ρ ⊢
      wps M Ls Ψ (Expr a (Esave sb ps body)) ρ := by
  rw [(wps_unfold (e := Expr a (Esave sb ps body))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Esave sb ps body)) = none from rfl,
    show jumpRedex? (Expr a (Esave sb ps body)) = none from rfl]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.save_eval hnv hvals, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨cvals', hvals', hout⟩ := hs.save_op_inv hnv
  obtain rfl : cvals = cvals' := Option.some.inj (hvals.symm.trans hvals')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Esave sb (saveParamsWithValues ps cvals) body) ∧
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

/-- ESAVE ENTRY (the block-entry rule; QA-1/H-1 generality): the
    initializers evaluate — by the certified pure evaluator, at the
    entry env — to `cvals`, and the body is verified at the
    parameter-bound env. Covers both engine arms: literal initializers
    (the TAU arm, `wps_save_vals` — the pre-QA-1 statement, now the
    instance at `valueFromPexprs … = some cvals`) and live-variable
    initializers (`save loop(x := n, c := p)` — the EVAL arm then the
    TAU arm, `wps_save_eval` then `wps_save_vals`). -/
theorem wps_save {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) {cvals : List value}
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hvals : evalPexprs M.tagDefs M.extern (ev0 :: evs) (saveParamPexprs ps) = some cvals) :
    wps M Ls Ψ body (bindSaveParams ps cvals (ev0 :: evs)) ⊢
      wps M Ls Ψ (Expr a (Esave sb ps body)) (ev0 :: evs) := by
  cases hv : valueFromPexprs (saveParamPexprs ps) with
  | some cvals' =>
    obtain rfl : cvals = cvals' := Option.some.inj
      (hvals.symm.trans (evalPexprs_of_valueFromPexprs M.tagDefs M.extern _ hv))
    exact wps_save_vals a sb ps body ev0 evs hv
  | none =>
    refine .trans ?_ (wps_save_eval a sb ps body (ev0 :: evs) hv hvals)
    rw [← bindSaveParams_withValues ps cvals]
    exact wps_save_vals a sb _ body ev0 evs (valueFromPexprs_withValues ps cvals
      ((List.length_map ..).symm.trans (evalPexprs_length _ _ _ hvals)))

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
    (hnv : valueFromPexpr pe = none) (hv : evalPexpr M.tagDefs M.extern ρ pe = some v) :
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
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv))) :
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

/-- ACTION_EVAL for a kill's pointer operand (kill/free arc K2; the
    `wps_load_eval` twin): a `kill(kind, pe)` whose operand evaluates
    to the pointer `pv` is verified by verifying the kill at `pv`. -/
theorem wps_kill_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pe : generic_pexpr Unit sym) (ρ : EnvStack)
    {pv : CerbMem.PointerValue}
    (hnv : valueFromPexpr pe = none)
    (hv : evalPexpr M.tagDefs M.extern ρ pe = some (Vobject (OVpointer pv))) :
    wps M Ls Ψ (killExpr loc ann kind pv) ρ ⊢
      wps M Ls Ψ (killOpRedex loc ann kind pe) ρ := by
  rw [(wps_unfold (e := killOpRedex loc ann kind pe)).to_eq]
  simp only [wps.pre, killOpRedex, toVal_action_node, jumpRedex?_action]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.kill_eval hnv hv, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', hv', hout⟩ := hs.kill_op_inv hnv
  obtain rfl : pv = pv' := by
    simpa using Option.some.inj (hv.symm.trans hv')
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hσ⟩ : re = killExpr loc ann kind pv ∧
      rρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq, killExpr] using hout
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
    (hv1 : evalPexpr M.tagDefs M.extern ρ pe1 = some v1)
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some v2) :
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
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr M.tagDefs M.extern ρ pe3 = some cv) :
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
      ⟨Step.store_eval hnv hv2 hv3, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', cv', hv2', hv3', hout⟩ := hs.store_op_inv hnv
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

/-! ## The small axioms at the statement layer — corollaries of the
atomic step specifications (Rules.lean) through `wps_of_atomic`; no
engine unfolding lives in this module (professor review 1, required
fix 8: one proof per small axiom) -/

/-- Store small axiom over `wps` (full ownership, UB-excluding —
    `store_atomic` lifted; the env rides verbatim; the footprint
    reaches the continuation universally since only one is
    possible). -/
theorem wps_store {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann ty pv cv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_of_atomic (store_atomic loc ann ty pv cv mo mv bs ρ hmv hst) rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%fp, %hw, Hpt'⟩
    subst hw
    iapply HΨ $$ Hpt'

/-- Load small axiom over `wps` (any fraction, UB-excluding — the
    `htrap` premise excludes the _Bool trap arm as in `wp_load`). -/
theorem wps_load {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv dq ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv dq ty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] (loadedVal M.tagDefs pv ty bs)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann ty pv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_of_atomic (load_atomic loc ann ty pv mo dq bs ρ htrap) rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%fp, %hw, Hpt'⟩
    subst hw
    iapply HΨ $$ Hpt'

/-- THE DISPOSE RULE over `wps` (kill/free arc K2): `kill_atomic`
    lifted. The classical `{p ↦ -} kill(static ty, p) {emp}`: full
    ownership of the created object's cell is consumed; the
    continuation runs at the BARE unit value (no footprint annotation
    — the engine's continuation is `mk_value_e Vunit`, so no `_plain`
    form is needed) and is offered the persistent DEAD cell
    `deadObj` at the pointer's id and base (drop it: `wps_kill_emp`).
    `hstatic`: the kill is static — the dynamic `free` is K3. -/
theorem wps_kill {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      ((∃ (id a : Int), ⌜pv = cellPtr id a⌝ ∗ deadObj M.tagDefs id a ty) -∗
        Ψ (SpikeVal.pure Vunit) ρ)) ⊢
      wps M Ls Ψ (killExpr loc ann kind pv) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_of_atomic (kill_atomic loc ann kind pv ty bs ρ hstatic) rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%hw, Hd⟩
    subst hw
    iapply HΨ $$ Hd

/-- The textbook face: `{p ↦ -} kill(static ty, p) {emp}` — the dead
    cell dropped. -/
theorem wps_kill_emp {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗ Ψ (SpikeVal.pure Vunit) ρ) ⊢
      wps M Ls Ψ (killExpr loc ann kind pv) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_kill loc ann kind pv ty bs ρ hstatic
  isplitl [Hpt]
  · iexact Hpt
  · iintro -
    iexact HΨ

/-! ## The plain-value forms of the whole-cell small axioms (QA-1/Q12;
the total twins and `AnnotInsensitive` are in Wpt.lean — this module
does not import it, so the predicate is spelled out here) -/

/-- `wps_store` for an annotation-insensitive postcondition
    (`∀ ds v ρ', Ψ (.annot ds v) ρ' = Ψ (.pure v) ρ'`): the textbook
    `{p ↦ -} store(p, v) {p ↦ v}` — no footprint quantifier. -/
theorem wps_store_plain {Ψ : SpikeVal → EnvStack → IProp GF}
    (hΨ : ∀ (ds : List dyn_annotation) (v : value) (ρ' : EnvStack),
      Ψ (.annot ds v) ρ' = Ψ (.pure v) ρ')
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (.pure Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann ty pv cv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_store loc ann ty pv cv mo mv bs ρ hmv hst
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt'
  rw [hΨ]
  iapply HΨ $$ Hpt'

/-- `wps_load` for an annotation-insensitive postcondition. -/
theorem wps_load_plain {Ψ : SpikeVal → EnvStack → IProp GF}
    (hΨ : ∀ (ds : List dyn_annotation) (v : value) (ρ' : EnvStack),
      Ψ (.annot ds v) ρ' = Ψ (.pure v) ρ')
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv dq ty bs ∗
      (pointsToCell M.tagDefs pv dq ty bs -∗ Ψ (.pure (loadedVal M.tagDefs pv ty bs)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann ty pv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_load loc ann ty pv mo dq bs ρ htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt'
  rw [hΨ]
  iapply HΨ $$ Hpt'

/-! ## THE GENERIC TYPED-SUBRANGE RULES (Phase 2, F-04)

One load rule and one store rule for ANY typed view of any
allocation — parameterized by the accessed type, the offset, the
decode (load) and the serialization facts (store). The per-layout
interior rules of the listrev/array slices are RETIRED: array
element and node field rules are client instances of these two
(derived inside the exhibit modules). -/

/-- GENERIC TYPED SUBRANGE LOAD small axiom (any fractions,
    UB-excluding): loading a typed view delivers the fixed decode of
    its byte image; the view rides through untouched. `hdec` is the
    view's table-independent decode at the interior address; `htrap`
    excludes the _Bool trap arm at the accessed type. -/
theorem wps_load_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (mo : memory_order) (dqm dqb : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(pointsToView M.tagDefs (GF := GF) id a aty off dqm dqb vty bs ∗
      (∀ fp, pointsToView M.tagDefs id a aty off dqm dqb vty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wps_of_atomic (loadAt_atomic loc ann id a aty off vty mo dqm dqb bs ρ hdec htrap)
    rfl rfl
  isplitl [Hv]
  · iexact Hv
  · iintro %w ⟨%fp, %hw, Hv'⟩
    subst hw
    iapply HΨ $$ Hv'

/-- GENERIC FULL-OWNERSHIP TYPED SUBRANGE STORE small axiom
    (UB-excluding): storing through a typed view REPLACES the view's
    byte image wholesale (the store footprint IS the view's extent —
    no cell-level splicing in the statement; whole-cell splicing is
    the client-side decomposition into subviews). The serialization
    premises are the `StorableAt` facts at the accessed type. -/
theorem wps_store_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order) (dqm : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hst : StorableView M.tagDefs vty mv) :
    iprop(pointsToView M.tagDefs (GF := GF) id a aty off dqm (.own 1) vty bs ∗
      (∀ fp, pointsToView M.tagDefs id a aty off dqm (.own 1) vty
          (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wps_of_atomic (storeAt_atomic loc ann id a aty off vty cv mo dqm bs ρ hmv hst)
    rfl rfl
  isplitl [Hv]
  · iexact Hv
  · iintro %w ⟨%fp, %hw, Hv'⟩
    subst hw
    iapply HΨ $$ Hv'

/-! ## Whole-cell interior access (derived clients of the generic
rules: split the maximal view at the accessed subrange, run the
generic rule, rejoin — the recomposition of a store IS `spliceBytes`
by definition). Layout-independent; exhibit field/element rules are
instances of THESE. -/

/-- Interior typed load THROUGH whole-cell ownership (any accessed
    type and offset; the cell rides through untouched). Derived from
    `wps_load_at` by the subrange split/join laws. -/
theorem wps_load_cell_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hbound : off + CerbMem.sizeofCtype M.tagDefs vty ≤ CerbMem.sizeofCtype M.tagDefs aty)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(cellOwn M.tagDefs (GF := GF) id dq (SpikeCell.mk a aty bs) ∗
      (∀ fp, cellOwn M.tagDefs id dq (SpikeCell.mk a aty bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo)
        ρ := by
  iintro ⟨Hcell, HΨ⟩
  icases (cellOwn_iff M.tagDefs id dq (SpikeCell.mk a aty bs)).mp $$ Hcell
    with ⟨Hm, Hb, %Hpure⟩
  obtain ⟨hlen, hdec0⟩ := Hpure
  have hblen : bs.length = CerbMem.sizeofCtype M.tagDefs aty := hlen
  have htk : (bs.take off).length = off := by
    simp [List.length_take]
    omega
  have hmidlen : ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)).length =
      CerbMem.sizeofCtype M.tagDefs vty := by
    simp [List.length_take, List.length_drop]
    omega
  have hsplit : bs = bs.take off ++
      ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty) ++
        (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty)) := by
    rw [List.take_append_drop, List.take_append_drop]
  ihave Hb2 : bytesOwn a dq (bs.take off ++
      ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty) ++
        (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty))) $$ [Hb]
  · rw [← hsplit]
    iexact Hb
  icases (bytesOwn_append a dq _ _).1 $$ Hb2 with ⟨Hpre, Hrest⟩
  icases (bytesOwn_append _ dq _ _).1 $$ Hrest with ⟨Hmid0, Hsuf0⟩
  ihave Hmid : bytesOwn (a + (off : Int)) dq
      ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) $$ [Hmid0]
  · rw [show a + (off : Int) = a + ((bs.take off).length : Int) by rw [htk]]
    iexact Hmid0
  ihave Hsuf : bytesOwn (a + (off : Int) +
      ((CerbMem.sizeofCtype M.tagDefs vty : Nat) : Int)) dq
      ((bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty)) $$ [Hsuf0]
  · rw [show a + (off : Int) + ((CerbMem.sizeofCtype M.tagDefs vty : Nat) : Int) =
      a + ((bs.take off).length : Int) +
        (((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)).length : Int) by
        rw [htk, hmidlen]]
    iexact Hsuf0
  iapply wps_load_at loc ann id a aty off vty mo dq dq
    ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) ρ hdec htrap
  isplitl [Hm Hmid]
  · iapply (pointsToView_iff M.tagDefs _ _ _ _ _ _ _ _).mpr
    isplitl [Hm]
    · iexact Hm
    isplit
    · ipureintro
      exact ⟨hbound, hmidlen⟩
    · iexact Hmid
  iintro %fp Hview
  icases (pointsToView_iff M.tagDefs _ _ _ _ _ _ _ _).mp $$ Hview with ⟨Hm, -, Hmid⟩
  iapply HΨ
  iapply (cellOwn_iff M.tagDefs id dq (SpikeCell.mk a aty bs)).mpr
  isplitl [Hm]
  · iexact Hm
  isplitl [Hpre Hmid Hsuf]
  · have hEnt : bytesOwn (GF := GF) a dq (bs.take off ++
        ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty) ++
          (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty))) ⊢
        bytesOwn a dq bs := by
      rw [← hsplit]
    iapply hEnt
    iapply (bytesOwn_append a dq _ _).2
    isplitl [Hpre]
    · iexact Hpre
    rw [show a + ((bs.take off).length : Int) = a + (off : Int) by rw [htk]]
    iapply (bytesOwn_append _ dq _ _).2
    isplitl [Hmid]
    · iexact Hmid
    · rw [show a + (off : Int) +
        ((((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)).length : Nat) : Int) =
        a + (off : Int) + ((CerbMem.sizeofCtype M.tagDefs vty : Nat) : Int) by
          rw [hmidlen]]
      iexact Hsuf
  · ipureintro
    exact ⟨hlen, hdec0⟩

/-- Interior typed store THROUGH whole-cell ownership: the cell's
    image is SPLICED at the accessed subrange (recomposing the
    subviews around the store footprint is literally `spliceBytes`).
    `hdec'` is the spliced image's decode-inertness at the ALLOCATION
    type (the whole-cell assertion's pure payload). Derived from
    `wps_store_at`. -/
theorem wps_store_cell_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hbound : off + CerbMem.sizeofCtype M.tagDefs vty ≤ CerbMem.sizeofCtype M.tagDefs aty)
    (hst : StorableView M.tagDefs vty mv)
    (hdec' : decIndep M.tagDefs a aty
      (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs)) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a aty bs) ∗
      (∀ fp, cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a aty
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo)
        ρ := by
  iintro ⟨Hcell, HΨ⟩
  icases (cellOwn_iff M.tagDefs id (.own 1) (SpikeCell.mk a aty bs)).mp $$ Hcell
    with ⟨Hm, Hb, %Hpure⟩
  obtain ⟨hlen, hdec0⟩ := Hpure
  have hlenimg : (CerbMem.memValueToBytes M.tagDefs [] mv).2.length =
      CerbMem.sizeofCtype M.tagDefs vty := hst.len
  have hblen : bs.length = CerbMem.sizeofCtype M.tagDefs aty := hlen
  have htk : (bs.take off).length = off := by
    simp [List.length_take]
    omega
  have hmidlen : ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)).length =
      CerbMem.sizeofCtype M.tagDefs vty := by
    simp [List.length_take, List.length_drop]
    omega
  have hsplit : bs = bs.take off ++
      ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty) ++
        (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty)) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hsplice : spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs =
      bs.take off ++ ((CerbMem.memValueToBytes M.tagDefs [] mv).2 ++
        bs.drop (off + (CerbMem.memValueToBytes M.tagDefs [] mv).2.length)) := by
    unfold spliceBytes
    rw [List.append_assoc]
  have hdroplen : (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty) =
      bs.drop (off + (CerbMem.memValueToBytes M.tagDefs [] mv).2.length) := by
    rw [List.drop_drop, hst.len]
  ihave Hb2 : bytesOwn a (.own 1) (bs.take off ++
      ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty) ++
        (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty))) $$ [Hb]
  · rw [← hsplit]
    iexact Hb
  icases (bytesOwn_append a (.own 1) _ _).1 $$ Hb2 with ⟨Hpre, Hrest⟩
  icases (bytesOwn_append _ (.own 1) _ _).1 $$ Hrest with ⟨Hmid0, Hsuf0⟩
  ihave Hmid : bytesOwn (a + (off : Int)) (.own 1)
      ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) $$ [Hmid0]
  · rw [show a + (off : Int) = a + ((bs.take off).length : Int) by rw [htk]]
    iexact Hmid0
  ihave Hsuf : bytesOwn (a + (off : Int) +
      ((CerbMem.sizeofCtype M.tagDefs vty : Nat) : Int)) (.own 1)
      ((bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty)) $$ [Hsuf0]
  · rw [show a + (off : Int) + ((CerbMem.sizeofCtype M.tagDefs vty : Nat) : Int) =
      a + ((bs.take off).length : Int) +
        (((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)).length : Int) by
        rw [htk, hmidlen]]
    iexact Hsuf0
  iapply wps_store_at loc ann id a aty off vty cv mo (.own 1)
    ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) ρ hmv hst
  isplitl [Hm Hmid]
  · iapply (pointsToView_iff M.tagDefs _ _ _ _ _ _ _ _).mpr
    isplitl [Hm]
    · iexact Hm
    isplit
    · ipureintro
      exact ⟨hbound, hmidlen⟩
    · iexact Hmid
  iintro %fp Hview
  icases (pointsToView_iff M.tagDefs _ _ _ _ _ _ _ _).mp $$ Hview with ⟨Hm, -, Hmid⟩
  iapply HΨ
  iapply (cellOwn_iff M.tagDefs id (.own 1) (SpikeCell.mk a aty
    (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs))).mpr
  isplitl [Hm]
  · iexact Hm
  isplitl [Hpre Hmid Hsuf]
  · have hEnt : bytesOwn (GF := GF) a (.own 1) (bs.take off ++
        ((CerbMem.memValueToBytes M.tagDefs [] mv).2 ++
          bs.drop (off + (CerbMem.memValueToBytes M.tagDefs [] mv).2.length))) ⊢
        bytesOwn a (.own 1)
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs) := by
      rw [hsplice]
    iapply hEnt
    iapply (bytesOwn_append a (.own 1) _ _).2
    isplitl [Hpre]
    · iexact Hpre
    rw [show a + ((bs.take off).length : Int) = a + (off : Int) by rw [htk]]
    iapply (bytesOwn_append _ (.own 1) _ _).2
    isplitl [Hmid]
    · iexact Hmid
    · rw [show a + (off : Int) +
        (((CerbMem.memValueToBytes M.tagDefs [] mv).2.length : Nat) : Int) =
        a + (off : Int) + ((CerbMem.sizeofCtype M.tagDefs vty : Nat) : Int) by
          rw [hst.len]]
      rw [← hdroplen]
      iexact Hsuf
  · ipureintro
    refine ⟨?_, hdec'⟩
    show (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs).length =
      CerbMem.sizeofCtype M.tagDefs aty
    rw [spliceBytes_length _ _ _ (by omega)]
    exact hlen

/-! ## THE ALLOCATION RULES (Phase 2 internal rule; alloc arc P1.4
public rule)

Two strata (charter P1.4):

- `wps_create_cursor_internal` — the exact-cursor rule: sound
  allocation THROUGH the allocator-cursor resource. The cursor cell
  carries exactly the two MemState fields `allocateObject` reads
  (lastAddress/nextAllocId), so the fresh base address is a CLOSED
  FORM of owned state and the out-of-memory kill arm
  (`alignedAddr == 0`, CerbMem.lean:1479) becomes the PURE premise
  `hnz` — allocation failure is excluded by ownership arithmetic,
  not assumed away. HEAP-IMPLEMENTATION USE ONLY: it names
  `lastAddress`/`nextAllocId`/`freshBase`/`cursorOwn` and may be
  consumed only by this module's public rule and its total mirror
  (Wpt.lean). (The last legacy client, StructExhibit's, converted to
  the public rule at alloc arc P2 item 1.)
- `wps_create` — THE PUBLIC RULE: precondition `allocCap
  (req :: rest)`, existential/continuation-bound pointer result
  with the fresh whole-cell points-to plus `allocCap rest`. NO
  cursor vocabulary in the statement (the P1 grep test). Launchable:
  the allocation-aware launchers (Adequacy/TotalAdequacy) grant
  `allocCap` from real Cerberus memory via `launchResources`.

Donor shape: RefinedC's alloc_new_blocks/alloc_alive discipline
(theories/caesium/ghost_state.v) — there the allocator is part of
the state interpretation and the client sees an existential fresh
location (lifting.v:979-998); here the authority is a one-cell ghost
heap because the engine's allocator is a deterministic cursor, and
`allocCap` is the abstract finite-capacity face of that cursor
(no-OOM policy: docs/2026-09-01_p1-notes.md, the P1.1 design
record). -/

section CreateRule
open Iris.Std.PartialMap

/-- CREATE small axiom, EXACT-CURSOR (INTERNAL — see the section
    header): with the allocator cursor at `⟨la, nid⟩` and a nonzero
    fresh base, `create` allocates exactly
    `cellPtr nid (freshBase la alignN (sizeof ty))`, delivers the
    whole-allocation points-to at unspecified bytes, and advances
    the cursor. UB/OOM-excluding: `hnz` is the out-of-memory guard,
    `hsz`/`hatom` pin a real non-atomic object type, `hinert` is the
    unspecified image's decode-inertness at the allocated type (rfl
    for scalar and integer-array types). Clients use the PUBLIC
    `wps_create` below. `create_atomic` (Rules.lean) lifted. -/
theorem wps_create_cursor_internal {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (ty : ctype)
    (pref : prefix0) (la nid : Int) (ρ : EnvStack)
    (hsz : 0 < CerbMem.sizeofCtype M.tagDefs ty) (hatom : atomicTy ty = false)
    (hnz : freshBase la alignN (CerbMem.sizeofCtype M.tagDefs ty) ≠ 0)
    (hinert : decIndep M.tagDefs (freshBase la alignN (CerbMem.sizeofCtype M.tagDefs ty)) ty
      (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte)) :
    iprop(cursorOwn (GF := GF) ⟨la, nid⟩ ∗
      ((pointsToCell M.tagDefs (cellPtr nid (freshBase la alignN (CerbMem.sizeofCtype M.tagDefs ty)))
          (.own 1) ty (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte) ∗
        cursorOwn ⟨freshBase la alignN (CerbMem.sizeofCtype M.tagDefs ty), nid + 1⟩) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer
          (cellPtr nid (freshBase la alignN (CerbMem.sizeofCtype M.tagDefs ty)))))) ρ)) ⊢
      wps M Ls Ψ (createExpr loc ann (.IV aprov alignN) ty pref) ρ := by
  iintro ⟨Hc, HΨ⟩
  iapply wps_of_atomic (create_atomic loc ann aprov alignN ty pref la nid ρ hsz hatom hnz hinert)
    rfl rfl
  isplitl [Hc]
  · iexact Hc
  · iintro %w ⟨%hw, Hpt, Hc'⟩
    subst hw
    iapply HΨ
    isplitl [Hpt]
    · iexact Hpt
    · iexact Hc'

/-- THE PUBLIC ALLOCATION RULE (alloc arc P1.4, the charter's exact
    logical shape): capacity for `req :: rest` buys one `create` of
    `req`; the returned pointer is CONTINUATION-BOUND (its allocation
    id and address occur nowhere in the precondition), delivered with
    full whole-cell ownership at unspecified bytes and the remaining
    capacity `allocCap rest`. Side premises: `hatom` pins a
    non-atomic object type; `hinert` is the unspecified image's
    decode-inertness AT EVERY ADDRESS (rfl for scalar and
    integer-array types) — address-independent so the statement stays
    cursor-free. Positivity of `sizeof req.ty` and the no-OOM guard
    are NOT premises: they ride inside `allocCap` (the plan fits).
    The continuation ALSO receives the fresh pointer's pure
    machine-address bounds `0 < addrOf p < 2^64` (alloc arc P2 —
    the charter P1.4 "bounds knowledge" allowance, needed by the
    allocating whole-program clients, e.g. `isList`'s node-WF facts;
    kept in pure form — the persistent-metadata form of bounds
    knowledge is `pointsToView_locInBounds`, Heap.lean). The statement contains
    no `AllocCursor`/`lastAddress`/`nextAllocId`/`freshBase`/
    `cursorOwn` — the P1 grep test. -/
theorem wps_create {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (req : AllocReq) (rest : List AllocReq)
    (pref : prefix0) (ρ : EnvStack)
    (hatom : atomicTy req.ty = false)
    (hinert : ∀ a : Int, decIndep M.tagDefs a req.ty
      (List.replicate (CerbMem.sizeofCtype M.tagDefs req.ty) undefByte)) :
    iprop(allocCap M.tagDefs (GF := GF) (req :: rest) ∗
      (∀ p : CerbMem.PointerValue,
        (pointsToCell M.tagDefs p (.own 1) req.ty
            (List.replicate (CerbMem.sizeofCtype M.tagDefs req.ty) undefByte) ∗
          allocCap M.tagDefs rest ∗
          ⌜0 < addrOf p ∧ addrOf p < 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer p))) ρ)) ⊢
      wps M Ls Ψ (createExpr loc ann (.IV aprov req.align) req.ty pref) ρ := by
  unfold allocCap
  iintro ⟨⟨%c, Hc, %hfit⟩, HΨ⟩
  obtain ⟨hplan, hla⟩ := hfit
  obtain ⟨c', hadv, hrest⟩ := (PlanFits_cons_iff M.tagDefs c req rest).mp hplan
  obtain ⟨hsz, hnz, rfl⟩ := advanceCursor_some_inv M.tagDefs hadv
  iapply wps_create_cursor_internal loc ann aprov req.align req.ty pref
    c.lastAddr c.nextId ρ hsz hatom hnz (hinert _)
  isplitl [Hc]
  · iexact Hc
  iintro ⟨Hpt, Hc⟩
  iapply HΨ
  isplitl [Hpt]
  · iexact Hpt
  isplitl [Hc]
  · -- rebuild the (unfolded) capacity from the advanced cursor
    iexists ⟨freshBase c.lastAddr req.align (CerbMem.sizeofCtype M.tagDefs req.ty),
      c.nextId + 1⟩
    isplitl [Hc]
    · iexact Hc
    · ipureintro
      exact ⟨hrest, Int.le_of_lt (freshBase_lt_two64 M.tagDefs c.lastAddr req.align
        req.ty hsz hnz hla)⟩
  · ipureintro
    exact ⟨freshBase_pos M.tagDefs c.lastAddr req.align req.ty hnz,
      freshBase_lt_two64 M.tagDefs c.lastAddr req.align req.ty hsz hnz hla⟩

end CreateRule

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

/-- FRAMING THE BLOCK SPECIFICATIONS: block specifications at `Ls`
    are block specifications at the framed context, with the frame
    joining the postcondition — the per-label bodies are framed by
    `wps_frame_labels`. -/
theorem blockSpecs_frame {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF) :
    blockSpecs (GF := GF) M Ls Ψ ⊢
      blockSpecs M (frameLs R Ls) (fun w ρ' => iprop(Ψ w ρ' ∗ R)) := by
  iintro #HB
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %hQ ⟨HLs, HR⟩
  ihave HW := HB $$ %l %params %cont %vs %ev0 %evs %hQ HLs
  iapply wps_frame_labels R cont (bindArgs params vs (ev0 :: evs)) $$ HW HR

/-- Monotonicity of the block specifications in the postcondition (the
    `blockSpecsT_mono` twin, QA-1/M-3; through `wps_wand`). -/
theorem blockSpecs_mono {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ w ρ', Ψ₁ w ρ' ⊢ Ψ₂ w ρ') :
    blockSpecs (GF := GF) M Ls Ψ₁ ⊢ blockSpecs M Ls Ψ₂ := by
  iintro #HB
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %hQ HLs
  ihave HW := HB $$ %l %params %cont %vs %ev0 %evs %hQ HLs
  iapply wps_wand cont (bindArgs params vs (ev0 :: evs)) $$ HW
  iintro %w %ρ' H
  iapply h w ρ' $$ H

/-! `blockSpecs_intro_variant` (the invariant+variant-shaped lemma
that offered smaller-measure block specifications as OPTIONAL
meta-level hypotheses) is RETIRED (foundations Phase 3, audit F-02:
it had no consumer and no theorem-level termination consequence).
THE REAL TOTAL RULE is `blockSpecsT`/`blockSpecsT_intro` (Wpt.lean):
there the smaller-measure discipline is the total judgment's jump
clause — mandatory, with the collapse into Iris TotalWeakestPre
(`wpt_sound`) and the drive-fuel simulation (TotalAdequacy.lean) as
its theorem-level consequences. -/

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


/-- THE WHOLE-LOOP FRAME RULE (derived): under block specifications
    at `Ls`, a statement WP FRAMED by `R` collapses to the base WP with
    `R` in the postcondition — `R` crosses every back edge (the labels
    are framed by `blockSpecs_frame`, the judgment by
    `wps_frame_labels`, and `wps_sound` runs at the framed context). -/
theorem wps_sound_frame {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (e : CoreExpr) (ρ : EnvStack) :
    blockSpecs M Ls Ψ ⊢
      iprop(wps M Ls Ψ e ρ ∗ R -∗
        WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, Ψ w.w w.ρ ∗ R }}) := by
  iintro #HB ⟨H, HR⟩
  ihave HW := wps_frame_labels R e ρ $$ H HR
  ihave HB' := blockSpecs_frame R $$ HB
  iapply wps_sound e ρ $$ HB' HW

end CerberusHeapLang
