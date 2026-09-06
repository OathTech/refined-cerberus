/-
CerberusHeapLang.Wps — the partial label-context judgment `wps`: the
judgment the loop exhibits are proved in.

THE SHAPE: the classical label-context statement logic (de Bruin
1981-style label-assumption judgments, the shape RefinedC's statement
judgment also takes), realized as a guarded fixpoint over the
fragment's `Step` via iris-lean's public Banach machinery
(`fixpoint`/`OFE.Contractive` — the same machinery `wp` itself is
built from; iris-lean untouched). `wps M p Ls Θ Ψ e ρ` is indexed by the
machine context `M`, the CURRENT PROCEDURE `p : Option sym` (whose
derived `M.labelsAt p` is its static label map — Step.lean header note
3; calls arc C3: the judgment is procedure-indexed, not control-indexed —
RETURN does not restore `exec_loc`, so the step clause quantifies over
the call stack and execution location `(κ, ℓ)`), the label
specification `Ls : LabelSpec GF` (`sym → List value → EnvStack →
IProp GF`: a precondition per registered label over the jump-argument
values and the jump-time environment), the PROCEDURE SPECIFICATION
TABLE `Θ : ProcSpec GF` (`sym → List value → IProp GF × (value → IProp
GF)`: per procedure and argument values, a precondition and a
postcondition on the delivered value; `emptyProcSpec` recovers every
pre-C3 statement), the postcondition `Ψ` over the delivered value and
the final environment, the expression, and the live environment stack.

THE JUMP CLAUSE: `wps.pre` has four clauses (value / jump redex / call
redex / step). The jump clause fires at `jumpRedex? e` (Step.lean — the
syntactic image of `step_ctx`'s `Erun` context-discard through the
`Esseq`/`Eannot` spine) and demands: the label resolves in `M.labelsAt p`
(`lookupLabel`), the arguments evaluate under the CURRENT environment
by the pure evaluator (`evalPexprs`, certified against the engine's
`full_eval_pexpr` in Soundness.lean), the environment stack is
cons-shaped (the `update_env` panic exclusion), and the label's
precondition `Ls l vs ρ` holds — then TRACKING STOPS: a jump's
postcondition is the label's business, so the postcondition clash
that would sink a bind-style rule never forms.

THE CALL CLAUSE (calls arc C3, replacing C2's `⌜False⌝` guard) fires at
`callRedex? e = some (ctx, f, pes)` (the call redex located outside-in
with the context PCALL captures) and demands what the engine's round
needs — the procedure resolves (`lookupProc`), the arity matches, the
arguments evaluate — and the SPECIFICATION: the table's precondition
`(Θ f vs).1` now and, a step later, the CALLER'S CONTINUATION `apply_ctx
ctx (pure ret)` at the caller's own environment for every `ret` meeting
the postcondition — exactly what RETURN produces. The callee's body is
`procSpecs`' business: every declared body verified once, at every caller
tail (`lookup_env` searches all frames — `∀ ρ` is forced), assuming the
table for every procedure, itself included — Hoare's rule for recursive
procedures, `procSpecs_intro` with no Löb. The collapse `wps_sound_cps`
into iris-lean's WP — CPS over the ambient control, RefinedC's
`stmt_wp_def` shape — carries the `procSpecs` and `blockSpecs` premises
and is the package's ONE Löb induction: its jump case is where the jump
clause meets the step relation (`Step.jump_inv`/`Step.run_of_jumpRedex`),
its call case is where the one Löb and the frame stack meet — the callee
runs under the induction hypothesis, and the RETURN (`Step.ret_inv`,
`wp_ret`/`wp_ret_annot`; the caller's env restored by `SameTail`) hands
the value to the caller's continuation, again through the hypothesis.
`wps_sound` (entry control) and `wps_sound_empty` (empty table: the
pre-C3 statement verbatim) are its faces.

THE CONTENTS: the memory rules as corollaries of the atomic step
specifications (`wps_of_atomic`; `wps_store`/`wps_load`, the typed
sub-range forms `wps_load_at`/`wps_store_at`/`wps_load_cell_at`/
`wps_store_cell_at`, the plain-value forms `wps_store_plain`/
`wps_load_plain`); the allocation rule `wps_create` from the
∗-splittable budget `allocBudget (allocCost ty align)` (Heap.lean, K2.5;
`wps_create_of_plan` is its plan-shaped reading); the
sequencing rules at the three binder shapes and `Ewseq` (`wps_seq`,
`wps_seq_spec`, `wps_seq_sym`, `wps_wseq`); the conditional with the
guard's verdict as a pure premise (`wps_if`; `wps_if_true`/`_false`
derived); value-scrutinee case (`wps_case_value`); block entry and the
jump (`wps_save` at evaluated initializers, `wps_run`); operand
evaluation and the `PtrEq` memop (`wps_load_eval`, `wps_store_eval`,
`wps_memop_eval`, `wps_memop_ptreq`); the pure exit and the
annotation layer (`wps_pure`, `wps_ofVal`, `wps_annot`,
`wps_annot_reindex`); the call rule (`wps_call` in context,
`wps_call_root` at the `Eproc` redex); consequence (`wps_wand`, `wps_fupd`,
`wps_mono_Ls`); framing at the statement level (`wps_frame`, and
`wps_frame_labels` through the framed label context `frameLs`, which
carries a frame across every back edge and into every call's
continuation); the per-label invariant rule `blockSpecs_intro` (no Löb)
with `blockSpecs_frame`/`blockSpecs_mono`; the procedure rule
`procSpecs_intro` (no Löb) with `procSpecs_empty`; the return devices
`wp_ret`/`wp_ret_annot`; and the collapses `wps_sound_cps` (CPS, the one
Löb), `wps_sound`/`wps_sound_frame` (entry control) and
`wps_sound_empty`/`wps_sound_frame_empty` (empty table) into the raw WP
— the adequacy interface (Adequacy.lean). There is deliberately no raw-WP
sequencing rule and no `Language.Context` instance: both are false
once labels are populated (Rules.lean and Lang.lean headers).
-/
import CerberusHeapLang.Rules
import CerberusHeapLang.Potential

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

/-! ## The procedure specification table (calls arc C3) -/

/-- PROCEDURE SPECIFICATIONS: per procedure symbol and argument values,
    a precondition and a postcondition on the DELIVERED value — the bare
    Core value the RETURN plugs into the caller's saved context
    (`mk_value_pe cval` in step_ctx's RETURN arm, Core_reduction.lean:484
    col ≈2276; annotations erased). Logical variables are the caller's
    choice of instance: a spec is quantified at use by the argument
    values (Hoare's procedure rule in its classical shape). RefinedC's
    `fn_params` (function.v:42–51) carries the same content; the table
    is a PARAMETER of the judgment because `Eproc` names a file symbol
    (design note Q7, D1) — the persistent-assertion form is the wrapper
    function pointers will need (`Eccall`), not this arc's concern. -/
abbrev ProcSpec (GF : BundledGFunctors) : Type :=
  sym → List value → IProp GF × (value → IProp GF)

/-- THE EMPTY TABLE: no procedure may be called (precondition `False`).
    Every pre-C3 statement is recovered at this table: the call clause at
    `emptyProcSpec` entails `|={⊤}=> ⌜False⌝` — C2's `⌜False⌝` guard under
    the update (`wps_empty_call_false`; the C3 range audit's R-1). -/
def emptyProcSpec {GF : BundledGFunctors} : ProcSpec GF :=
  fun _ _ => (iprop(⌜False⌝), fun _ => iprop(⌜True⌝))

@[simp] theorem emptyProcSpec_fst {GF : BundledGFunctors} (f : sym) (vs : List value) :
    (emptyProcSpec (GF := GF) f vs).1 = iprop(⌜False⌝) := rfl

/-! ## The saved context plugged (the engine's `apply_ctx`, Core_reduction.lean:388,
at the three frames `callRedex?` builds — `rfl` equations for rewriting) -/

@[simp] theorem apply_ctx_CTX (e : CoreExpr) : apply_ctx CTX e = e := rfl

@[simp] theorem apply_ctx_sseq (a : List annot) (pat : pattern) (ctx : context)
    (e2 e : CoreExpr) :
    apply_ctx (Csseq a pat ctx e2) e = Expr a (Esseq pat (apply_ctx ctx e) e2) := rfl

@[simp] theorem apply_ctx_wseq (a : List annot) (pat : pattern) (ctx : context)
    (e2 e : CoreExpr) :
    apply_ctx (Cwseq a pat ctx e2) e = Expr a (Ewseq pat (apply_ctx ctx e) e2) := rfl

@[simp] theorem apply_ctx_annot (a : List annot) (ds : List dyn_annotation) (ctx : context)
    (e : CoreExpr) :
    apply_ctx (Cannot a ds ctx) e = Expr a (Eannot ds (apply_ctx ctx e)) := rfl

/-! ## Per-constructor value-test facts (match-reduction discipline) -/

@[simp] theorem toVal_sseq_node (a : List annot) (pat : pattern)
    (e1 e2 : CoreExpr) : toVal (Expr a (Esseq pat e1 e2)) = none := rfl

@[simp] theorem toVal_bound_node (a : List annot) (b : CoreExpr) :
    toVal (Expr a (Ebound b)) = none := rfl

@[simp] theorem toVal_unseq_node (a : List annot) (es : List CoreExpr) :
    toVal (Expr a (Eunseq es)) = none := rfl

@[simp] theorem apply_ctx_bound (a : List annot) (ctx : context) (e : CoreExpr) :
    apply_ctx (Cbound a ctx) e = Expr a (Ebound (apply_ctx ctx e)) := rfl

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

/-- One unfolding of the statement WP. FOUR clauses — value / jump
    redex / CALL redex / step (S3 had three; probe Wps.lean:154). The
    jump clause's payload: label resolution in the current procedure's
    fiber `M.labelsAt p`, argument evaluation by the pure evaluator at
    the CURRENT env, the cons-shaped-env WF fact, and the per-label
    precondition — all pure but `Ls`, so the clause is Ψ- and
    frame-independent (what makes sequencing a transfer).

    THE CALL CLAUSE (calls arc C3; replaces C2's `⌜False⌝` guard): at a
    call redex in context (`callRedex? e = some (ctx, f, pes)` — the
    redex located outside-in with the context the engine's PCALL arm
    CAPTURES, Core_reduction.lean:484 col 18133) the judgment demands
    what the engine's round needs to succeed — the procedure resolves
    (`lookupProc`, `call_proc`'s stdlib-first lookup), the arity matches,
    the arguments evaluate at the current env — and the SPECIFICATION:
    the table's precondition `(Θ f vs).1` now, and, a step later, for
    every returned value `ret` satisfying `(Θ f vs).2 ret` AND every
    static annotation list `a1` on the returned value node (E1: RETURN
    plugs `Expr e_annots (Epure (mk_value_pe cval))` — the callee's final
    node's list rides, the caller cannot know it), the judgment of the
    CALLER'S CONTINUATION `apply_ctx ctx (pure ret)` at the caller's OWN
    env `ρ` — exactly the configuration RETURN produces (col ≈2276:
    `arena := apply_ctx caller_ctx (… mk_value_pe cval)`, `env := env'`
    the popped stack). The `▷` pays for the call round and
    makes the clause contractive in `F`; the callee's body is nobody's
    business here — `procSpecs` verifies every body once, and the
    collapse `wps_sound_cps` ties the knot (the one Löb).

    THE STEP CLAUSE is the base `wp_lift_step` premise shape at this
    instance's `numLatersPerStep = 0`, minus forks, QUANTIFIED OVER THE
    CALL STACK, EXECUTION LOCATION, CURRENT LOCATION AND RUN SUPPLIES
    `(κ, ℓ, lc, sp)`: the judgment is indexed by the current PROCEDURE `p`
    only (`⟨κ, p, ℓ, lc, sp⟩` is the configuration's control; E1 added the
    location the general arm writes at every round and the run state's
    live supplies — both invisible to the judgment, exactly as `ℓ`). Forcing fact: RETURN does not restore `exec_loc` (PCALL
    pushes `push_exec_loc`, RETURN writes `current_proc_opt`/`env`/
    `stack0`/`arena` only), so the caller's continuation after a return
    runs at a control that differs from the call-time control in
    `execLoc`; a judgment indexed by the full control could not be
    re-entered there. Every C1/C2 rule was control-general (the C1
    range audit), so nothing is lost: the pre-C3 judgment at `ctl` is
    the instance `κ := ctl.κ, ℓ := ctl.execLoc` of this one at
    `p := ctl.proc` and `Θ := emptyProcSpec`. -/
def wps.pre [SpikeGS hlc GF] (M : MachineCtx) (p : Option sym) (Ls : LabelSpec GF)
    (Θ : ProcSpec GF)
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
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel (M.labelsAt p) lp.1 = some (params, cont)⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern M.file ρ lp.2 = some vs⌝ ∗ Ls lp.1 vs ρ)
    | none =>
      match callRedex? e with
      | some (ctx, f, pes) =>
        iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (body : CoreExpr)
          (vs : List value),
          ⌜lookupProc M.file M.extern f = some (params, body)⌝ ∗
          ⌜params.length = vs.length⌝ ∗
          ⌜evalPexprs M.tagDefs M.extern M.file ρ pes = some vs⌝ ∗
          (Θ f vs).1 ∗
          ▷ ∀ (ret : value) (a1 : List annot), (Θ f vs).2 ret -∗
            F Ψ (apply_ctx ctx (ofValA (.pure a1 [] ret))) ρ)
      | none =>
        iprop(∀ (κ : List (Option sym × context)) (ℓ : exec_location)
          (lc : CerbLocation.Loc) (sp : RunSup)
          (σ₁ : Mem) (ns : Nat) (obs obs' : List Empty) (nt : Nat),
          ⌜M.runState.sym_supply ≤ sp.sym⌝ -∗
          stateInterp σ₁ ns (obs ++ obs') nt ={⊤,∅}=∗
          ⌜PrimStep.Reducible ((⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩ : CoreRt), σ₁)⌝ ∗
          ▷ ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
            ⌜((⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩ : CoreRt), σ₁) -<obs>-> (r, σ₂, eₜ)⌝ -∗ £ 1 ={∅,⊤}=∗
            stateInterp σ₂ (ns + 1) obs' nt ∗ F Ψ r.e r.ρ)

instance wps.pre.contractive [SpikeGS hlc GF] (M : MachineCtx) (p : Option sym)
    (Ls : LabelSpec GF) (Θ : ProcSpec GF) :
    OFE.Contractive (wps.pre (GF := GF) M p Ls Θ) where
  distLater_dist := by
    intro n F F' HF Ψ e ρ
    unfold wps.pre
    cases toVal e
    case some => exact .rfl
    case none =>
      cases jumpRedex? e
      case some => exact .rfl
      cases callRedex? e
      case some =>
        refine BIFUpdate.ne.ne ?_
        refine BI.exists_ne fun params => ?_
        refine BI.exists_ne fun body => ?_
        refine BI.exists_ne fun vs => ?_
        refine BI.sep_ne.ne .rfl ?_
        refine BI.sep_ne.ne .rfl ?_
        refine BI.sep_ne.ne .rfl ?_
        refine BI.sep_ne.ne .rfl ?_
        refine OFE.Contractive.distLater_dist fun m m_n => ?_
        refine BI.forall_ne fun ret => ?_
        refine BI.forall_ne fun a1 => ?_
        refine BI.wand_ne.ne .rfl ?_
        exact HF m m_n _ _ _
      refine BI.forall_ne fun κ => ?_
      refine BI.forall_ne fun ℓ => ?_
      refine BI.forall_ne fun lc => ?_
      refine BI.forall_ne fun sp => ?_
      refine BI.forall_ne fun σ₁ => ?_
      refine BI.forall_ne fun ns => ?_
      refine BI.forall_ne fun obs => ?_
      refine BI.forall_ne fun obs' => ?_
      refine BI.forall_ne fun nt => ?_
      refine BI.wand_ne.ne .rfl ?_
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
    the probe's `wps`). `wps M p Ls Θ Ψ e ρ`: machine context, current
    procedure, its label specification, the procedure specification
    table, postcondition, expression, live environment stack. -/
def wps [SpikeGS hlc GF] (M : MachineCtx) (p : Option sym) (Ls : LabelSpec GF)
    (Θ : ProcSpec GF) :
    (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF :=
  fixpoint (wps.pre M p Ls Θ)

theorem wps_unfold [SpikeGS hlc GF] {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF}
    {Θ : ProcSpec GF}
    {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr} {ρ : EnvStack} :
    wps (GF := GF) M p Ls Θ Ψ e ρ ⊣⊢ wps.pre M p Ls Θ (wps M p Ls Θ) Ψ e ρ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wps.pre M p Ls Θ).toContractiveHom)).dist Ψ e ρ

variable [SpikeGS hlc GF]
variable {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}

/-! ## Structural rules -/

/-- Value rule at the canonical value injections (the donor's Return
    channel / probe `wps_val`). -/
theorem wps_ofVal {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeVal)
    (ρ : EnvStack) :
    Ψ w ρ ⊢ wps M p Ls Θ Ψ (ofVal w) ρ := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toVal_ofVal]
  iintro H
  imodintro
  iexact H

/-- Value rule at ANY static annotation lists (E1): the erased value
    lands in the postcondition. -/
theorem wps_ofValA {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeValA)
    (ρ : EnvStack) :
    Ψ w.erase ρ ⊢ wps M p Ls Θ Ψ (ofValA w) ρ := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toVal_ofValA]
  iintro H
  imodintro
  iexact H

/-- Value-channel inversion at the injections (the wps analog of
    `wp_value_fupd'`'s forward direction), at any annotation lists. -/
theorem wps_value_inv {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeValA)
    (ρ : EnvStack) :
    wps M p Ls Θ Ψ (ofValA w) ρ ⊢ iprop(|={⊤}=> Ψ w.erase ρ) := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toVal_ofValA]
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
    (h : ∀ (κ : List (Option sym × context)) (ℓ : exec_location)
      (lc : CerbLocation.Loc) (sp : RunSup),
      AtomicStep M ⟨κ, p, ℓ, lc, sp⟩ e ρ c P Q)
    (hnv : toVal e = none)
    (hnj : jumpRedex? e = none) (hnc : callRedex? e = none) :
    iprop(P ∗ (∀ w : SpikeVal, Q w -∗ Ψ w ρ)) ⊢ wps M p Ls Θ Ψ e ρ := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, hnv, hnj, hnc]
  iintro ⟨HP, HΨ⟩ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  cases obs with
  | cons o _ => exact o.elim
  | nil =>
  simp only [List.nil_append]
  imod (h κ ℓ lc sp ⊤ ∅ Std.LawfulSet.empty_subset σ₁ ns obs' nt) $$ [$HP $Hσ]
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
    (hl : lookupLabel (M.labelsAt p) l = some (params, cont))
    (hvs : evalPexprs M.tagDefs M.extern M.file (ev0 :: evs) pes = some vs) :
    Ls l vs (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Erun ra l pes)) (ev0 :: evs) := by
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

/-- THE CALL RULE at a call redex IN CONTEXT (calls arc C3; the
    design note's `wps_call` is the root instance `wps_call_root`):
    to verify a call of `f` whose arguments evaluate to `vs`, establish
    the table's precondition `(Θ f vs).1` and verify the CALLER'S
    CONTINUATION — the saved context plugged with the returned value —
    at the caller's own env, for every return value satisfying the
    postcondition. Near-definitional: the judgment's call clause IS this
    rule (the `▷` is paid at the call round inside the collapse). The
    callee's body is not this rule's business: `procSpecs`. Arguments
    evaluate INSIDE the engine's PCALL round (`full_eval_pexpr'` over
    the whole list), so there is no separate operand-evaluation form.
    RefinedC: `typed_call`/`type_call_fnptr` (programs.v:117,
    function.v:131–137). -/
theorem wps_call {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr} {ctx : context}
    {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    (ρ : EnvStack)
    (hc : callRedex? e = some (ctx, f, pes))
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length)
    (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs) :
    iprop((Θ f vs).1 ∗ (∀ (ret : value) (a1 : List annot), (Θ f vs).2 ret -∗
        wps M p Ls Θ Ψ (apply_ctx ctx (ofValA (.pure a1 [] ret))) ρ)) ⊢
      wps M p Ls Θ Ψ e ρ := by
  have htv : toVal e = none := toVal_none_of_callRedex?_some hc
  have hjr : jumpRedex? e = none := jumpRedex?_none_of_callRedex?_some hc
  rw [wps_unfold.to_eq]
  simp only [wps.pre, htv, hjr, hc]
  iintro ⟨Hpre, Hcont⟩
  imodintro
  iexists params, body, vs
  isplit
  · ipureintro; exact hf
  isplit
  · ipureintro; exact hlen
  isplit
  · ipureintro; exact hvs
  isplitl [Hpre]
  · iexact Hpre
  inext
  iexact Hcont

/-- At the EMPTY table a call redex is unverifiable (C2's `⌜False⌝` guard,
    recovered under the update): the clause's precondition is `False`.
    Twin of `wpt_empty_call_false`. -/
theorem wps_empty_call_false {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr}
    {ρ : EnvStack} {q : context × sym × List (generic_pexpr Unit sym)}
    (hc : callRedex? e = some q) :
    wps M p Ls emptyProcSpec Ψ e ρ ⊢ iprop(|={⊤}=> ⌜False⌝) := by
  obtain ⟨ctx, f, pes⟩ := q
  have htv : toVal e = none := toVal_none_of_callRedex?_some hc
  have hjr : jumpRedex? e = none := jumpRedex?_none_of_callRedex?_some hc
  rw [wps_unfold.to_eq]
  simp only [wps.pre, htv, hjr, hc, emptyProcSpec_fst]
  iintro H
  imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, %hF, -⟩
  exact hF.elim

/-- THE CALL RULE at the root redex `Eproc` (the design note's
    `wps_call`, §3 Q1): the continuation is the bare returned value at
    the caller's env. Composes under `Esseq`/`Ewseq`/`Eannot` through
    the sequencing and annotation rules, whose call cases are exactly
    this rule in context. -/
theorem wps_call_root {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (ra : core_run_annotation) (f : sym) (pes : List (generic_pexpr Unit sym))
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    (ρ : EnvStack)
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length)
    (hvs : evalPexprs M.tagDefs M.extern M.file ρ pes = some vs) :
    iprop((Θ f vs).1 ∗ (∀ (ret : value) (a1 : List annot), (Θ f vs).2 ret -∗
        wps M p Ls Θ Ψ (ofValA (.pure a1 [] ret)) ρ)) ⊢
      wps M p Ls Θ Ψ (Expr a (Eproc ra (Sym f) pes)) ρ :=
  wps_call ρ (callRedex?_proc a ra f pes) hf hlen hvs

/-- Monotonicity/consequence in the value channel (probe `wps_wand`;
    S3: jump exits are Ψ-independent — the label preconditions
    carry everything across a jump — so the statement survives the
    jump clause verbatim; its case is a pass-through). -/
theorem wps_wand {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr)
    (ρ : EnvStack) :
    wps M p Ls Θ Ψ₁ e ρ ⊢
      iprop((∀ w ρ', Ψ₁ w ρ' -∗ Ψ₂ w ρ') -∗ wps M p Ls Θ Ψ₂ e ρ) := by
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
      cases hcr : callRedex? e with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq, wps_unfold.to_eq]
        simp only [wps.pre, htv, hjr, hcr]
        iintro H HΨ
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ρ H' HΨ
      | none =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr, hcr]
      iintro H HΨ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨$, H⟩
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
    wps M p Ls Θ (fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) e ρ ⊢ wps M p Ls Θ Ψ e ρ := by
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
      cases hcr : callRedex? e with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq, wps_unfold.to_eq]
        simp only [wps.pre, htv, hjr, hcr]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ρ H'
      | none =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr, hcr]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨$, H⟩
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
    wps M p Ls₁ Θ Ψ e ρ ⊢ wps M p Ls₂ Θ Ψ e ρ := by
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
      cases hcr : callRedex? e with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [(wps_unfold (Ls := Ls₁)).to_eq, (wps_unfold (Ls := Ls₂)).to_eq]
        simp only [wps.pre, htv, hjr, hcr]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ρ H'
      | none =>
      rw [(wps_unfold (Ls := Ls₁)).to_eq, (wps_unfold (Ls := Ls₂)).to_eq]
      simp only [wps.pre, htv, hjr, hcr]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨$, H⟩
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
    iprop(wps M p Ls Θ Ψ e ρ ∗ R) ⊢
      wps M p Ls Θ (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ := by
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

/-- THE STATEMENT FRAME RULE (labels included): `wps M p Ls Θ Ψ e ρ ∗ R ⊢
    wps M p (frameLs R Ls) Θ (Ψ ∗ R) e ρ`. Value exit: the frame joins the
    postcondition; jump: the frame joins the label precondition (this
    is exactly what `frameLs` is for); step: Löb. -/
theorem wps_frame_labels {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (e : CoreExpr) (ρ : EnvStack) :
    wps M p Ls Θ Ψ e ρ ⊢
      iprop(R -∗ wps M p (frameLs R Ls) Θ (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ) := by
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
      cases hcr : callRedex? e with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq, wps_unfold.to_eq]
        simp only [wps.pre, htv, hjr, hcr]
        iintro H HR
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ρ H' HR
      | none =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr, hcr]
      iintro H HR %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨$, H⟩
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

/-- Annotation reindexing (the lockstep argument) over `wps`. E1: two
    wraps of the same body differing in the dyn-annotation payload AND in
    the wrapper node's static annotations step in lockstep — the static
    lists reach only the location write, which the judgment quantifies. -/
theorem wps_annot_reindex (aA aB : List annot) (dsA dsB : List dyn_annotation)
    (c : CoreExpr) (ρ : EnvStack) {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (hΦ : ∀ w ρ', Ψ₁ (SpikeVal.merge dsA w) ρ' = Ψ₂ (SpikeVal.merge dsB w) ρ') :
    wps M p Ls Θ Ψ₁ (Expr aA (Eannot dsA c)) ρ ⊢
      wps M p Ls Θ Ψ₂ (Expr aB (Eannot dsB c)) ρ := by
  iloeb as IH generalizing %aA %aB %dsA %dsB %c %ρ %hΦ
  rcases toVal_annot_cases aA c dsA with ⟨a2, b, v, rfl, hA⟩ | hA
  · -- value on both sides
    have hB : toVal (Expr aB (Eannot dsB (ofValA (.pure a2 b v)))) =
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
    have hB : toVal (Expr aB (Eannot dsB c)) = none := by
      rcases toVal_annot_cases aB c dsB with ⟨a2, b, v, rfl, _⟩ | hB
      · rw [show toVal (Expr aA (Eannot dsA (ofValA (.pure a2 b v)))) =
            some (.annot dsA v) from rfl] at hA
        cases hA
      · exact hB
    -- the two wraps share the jump-redex answer (`jumpRedex?` never
    -- reads the dyn-annotation payload)
    have hEq : jumpRedex? (Expr aB (Eannot dsB c)) =
        jumpRedex? (Expr aA (Eannot dsA c)) := by
      rw [jumpRedex?_annot, jumpRedex?_annot]
    -- the two wraps have a call redex together or not at all (the
    -- captured `Cannot` frame differs by the payload, so only the
    -- `none`-ness transfers — which is all the guard reads)
    have hEqC : callRedex? (Expr aB (Eannot dsB c)) = none ↔
        callRedex? (Expr aA (Eannot dsA c)) = none := by
      rw [callRedex?_annot, callRedex?_annot]
      split <;> simp
    cases hjr : jumpRedex? (Expr aA (Eannot dsA c)) with
    | some lp =>
      -- S3 JUMP CASE: the two clauses are the SAME FORMULA — the
      -- jump discards the wrapper, and the clause never mentions Φ.
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, hA, hB, hjr, hEq.trans hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? (Expr aA (Eannot dsA c)) with
      | some q =>
        -- the body carries the call redex; the two wraps capture it in
        -- `Cannot` frames differing only in the payload, so the two
        -- continuations are the two wraps of the SAME plugged body
        have hnr : annotRooted c = false := by
          cases hr : annotRooted c with
          | false => rfl
          | true => rw [callRedex?_annot_of_root _ _ hr] at hcr; cases hcr
        obtain ⟨c₀, f₀, pes₀, hq₀⟩ : ∃ c₀ f₀ pes₀, callRedex? c = some (c₀, f₀, pes₀) := by
          cases hc : callRedex? c with
          | none => rw [callRedex?_annot_of_not_root _ _ hnr, hc] at hcr; cases hcr
          | some q₀ => obtain ⟨c₀, f₀, pes₀⟩ := q₀; exact ⟨c₀, f₀, pes₀, rfl⟩
        have hcrA : callRedex? (Expr aA (Eannot dsA c)) = some (Cannot aA dsA c₀, f₀, pes₀) := by
          rw [callRedex?_annot_of_not_root _ _ hnr, hq₀]; rfl
        have hcrB : callRedex? (Expr aB (Eannot dsB c)) = some (Cannot aB dsB c₀, f₀, pes₀) := by
          rw [callRedex?_annot_of_not_root _ _ hnr, hq₀]; rfl
        rw [wps_unfold.to_eq, wps_unfold.to_eq]
        simp only [wps.pre, hA, hB, hjr, hEq.trans hjr, hcrA, hcrB, apply_ctx_annot]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %aA %aB %dsA %dsB %(apply_ctx c₀ (ofValA (.pure a1 [] ret))) %ρ %hΦ H'
      | none =>
      have hcrB : callRedex? (Expr aB (Eannot dsB c)) = none := hEqC.mpr hcr
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, hA, hB, hjr, hEq.trans hjr, hcr, hcrB]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
        rcases hstep.1.annot_inv with ⟨hg, hnj, hnc, hnv, c', ρ', ctl', σ'', hs, _⟩ |
            ⟨a2, ds2, c'', rfl, _⟩ |
            ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
            ⟨hg, hcall⟩ | ⟨a2, b1, v, pc, κ', hb, hκ, _⟩
        · exact ⟨[], ⟨Expr aB (Eannot dsB c'), ρ', ctl', M⟩, _, [],
            ⟨Step.annot_ctx hnj hnc hnv hg hs, rfl, rfl⟩⟩
        · exact ⟨[], ⟨Expr (aB ++ a2) (Eannot (dsB ++ ds2) c''), ρ,
            (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd aB, M⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
        · rw [jumpRedex?_annot_of_not_root _ _ hg, hj] at hjr; cases hjr
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [callRedex?_body_none_of_annot hg hcr] at h; cases h
        · subst hb
          exact absurd hA (by simp)
      · inext
        iintro %e₂ %σ₂ %eₜ %HstepB Hcred
        obtain ⟨hstepB, hlbl, rfl⟩ := HstepB
        rcases hstepB.annot_inv with ⟨hg, hnj, hnc, hnv, c', ρ', ctl', σ'', hs, hout⟩ |
            ⟨a2, ds2, c'', rfl, hout⟩ |
            ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
            ⟨hg, hcall⟩ | ⟨a2, b1, v, pc, κ', hb, hκ, _⟩
        · obtain ⟨e₂e, e₂ρ, e₂ctl, e₂M⟩ := e₂
          simp only at hlbl
          obtain rfl : M = e₂M := hlbl.symm
          obtain ⟨he, hρ, hctl, hσ⟩ : e₂e = Expr aB (Eannot dsB c') ∧ e₂ρ = ρ' ∧
              e₂ctl = ctl' ∧ σ₂ = σ'' := by
            simpa [Prod.mk.injEq] using hout
          subst he hρ hctl hσ
          imod H $$ %(⟨Expr aA (Eannot dsA c'), e₂ρ, e₂ctl, M⟩ : CoreRt) %_ %([])
            %⟨Step.annot_ctx hnj hnc hnv hg hs, rfl, rfl⟩ Hcred with ⟨$, H⟩
          imodintro
          iapply IH $$ %aA %aB %dsA %dsB %c' %e₂ρ %hΦ H
        · obtain ⟨e₂e, e₂ρ, e₂ctl, e₂M⟩ := e₂
          simp only at hlbl
          obtain rfl : M = e₂M := hlbl.symm
          obtain ⟨he, hρ, hctl, hσ⟩ : e₂e = Expr (aB ++ a2) (Eannot (dsB ++ ds2) c'') ∧
              e₂ρ = ρ ∧ e₂ctl = (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd aB ∧ σ₂ = σ₁ := by
            simpa [Prod.mk.injEq] using hout
          subst he hctl
          obtain rfl : ρ = e₂ρ := hρ.symm
          obtain rfl : σ₁ = σ₂ := hσ.symm
          imod H $$ %(⟨Expr (aA ++ a2) (Eannot (dsA ++ ds2) c''), ρ,
              (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd aA, M⟩ : CoreRt) %_
            %([]) %⟨Step.annot_merge, rfl, rfl⟩ Hcred with ⟨$, H⟩
          imodintro
          iapply IH $$ %(aA ++ a2) %(aB ++ a2) %(dsA ++ ds2) %(dsB ++ ds2) %c'' %ρ
            %(fun w ρ' => by
              rw [← SpikeVal.merge_merge, ← SpikeVal.merge_merge]
              exact hΦ (SpikeVal.merge ds2 w) ρ') H
        · rw [jumpRedex?_annot_of_not_root _ _ hg, hj] at hjr; cases hjr
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [callRedex?_body_none_of_annot hg hcrB] at h; cases h
        · subst hb
          exact absurd hB (by simp)

/-- `wps` commutes with the run-time dyn-annotation wrapper: to
    verify `{A}e`, verify `e` with the postcondition translated along
    `merge` (the merge case exits through the reindexing lemma). E1: at
    ANY static annotations `a` on the wrapper node (the engine's
    UNSEQ-ANNOT residue carries the `unseq` node's list, E4). -/
theorem wps_annot (a : List annot) (ds : List dyn_annotation) (e : CoreExpr) (ρ : EnvStack)
    {Ψ : SpikeVal → EnvStack → IProp GF} :
    wps M p Ls Θ (fun w ρ' => Ψ (SpikeVal.merge ds w) ρ') e ρ ⊢
      wps M p Ls Θ Ψ (Expr a (Eannot ds e)) ρ := by
  iloeb as IH generalizing %a %ds %e %ρ
  cases hv : toVal e with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal hv
    cases wa with
    | pure a1 b1 v =>
      -- the wrap is itself a value: .annot ds v
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, toVal_ofValA, SpikeValA.erase_pure,
        show toVal (Expr a (Eannot ds (ofValA (.pure a1 b1 v)))) =
          some (.annot ds v) from rfl]
      iintro H
      imod H with H
      imodintro
      rw [show (SpikeVal.annot ds v) = SpikeVal.merge ds (SpikeVal.pure v)
        from rfl]
      iexact H
    | annot a1 a2 b1 ds2 v =>
      -- double annot: one deterministic ANNOTS-merge step to a value
      rw [(wps_unfold
        (e := Expr a (Eannot ds (ofValA (.annot a1 a2 b1 ds2 v))))).to_eq]
      simp only [wps.pre,
        show toVal (Expr a (Eannot ds (ofValA (.annot a1 a2 b1 ds2 v)))) = none from rfl,
        show jumpRedex? (Expr a (Eannot ds (ofValA (.annot a1 a2 b1 ds2 v)))) = none from rfl,
        show callRedex? (Expr a (Eannot ds (ofValA (.annot a1 a2 b1 ds2 v)))) = none from rfl]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.annot_inv with ⟨hg, hnj, hnc, hnv, c', ρ', ctl', σ'', hs', hout⟩ |
          ⟨a2', ds2', c'', hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
          ⟨hg, hcall⟩ | ⟨a2', b1', v', pc, κ', hb, hκ, _⟩
      · rw [show annotRooted (ofValA (.annot a1 a2 b1 ds2 v)) = true from rfl] at hg
        cases hg
      · obtain ⟨rfl, rfl, rfl⟩ : a1 = a2' ∧ ds2 = ds2' ∧
            Expr a2 (Epure (Pexpr b1 () (PEval v))) = c'' := by
          simpa using hb
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = Expr (a ++ a1)
              (Eannot (ds ++ ds2) (Expr a2 (Epure (Pexpr b1 () (PEval v))))) ∧
            rρ = ρ ∧ rctl = (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd a ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrctl
        obtain rfl : ρ = rρ := hrρ.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        ihave H := wps_value_inv (.annot a1 a2 b1 ds2 v) ρ $$ H
        imod H with H
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · rw [show Expr (a ++ a1) (Eannot (ds ++ ds2) (Expr a2 (Epure (Pexpr b1 () (PEval v))))) =
            ofValA (.annot (a ++ a1) a2 b1 (ds ++ ds2) v) from rfl]
          iapply wps_ofValA (.annot (a ++ a1) a2 b1 (ds ++ ds2) v) ρ
          rw [show (SpikeValA.annot (a ++ a1) a2 b1 (ds ++ ds2) v).erase =
            SpikeVal.merge ds (SpikeValA.annot a1 a2 b1 ds2 v).erase from rfl]
          iexact H
      · rw [show annotRooted (ofValA (.annot a1 a2 b1 ds2 v)) = true from rfl] at hg
        cases hg
      · rw [show annotRooted (ofValA (.annot a1 a2 b1 ds2 v)) = true from rfl] at hg
        cases hg
      · simp at hb
  | none =>
    by_cases hr : annotRooted e = true
    · -- annot-rooted body: the wrap merges; exit through reindexing
      obtain ⟨a2, ds2, c, rfl⟩ : ∃ a2 ds2 c, e = Expr a2 (Eannot ds2 c) := by
        unfold annotRooted at hr
        split at hr
        · rename_i a2 ds2 c
          exact ⟨a2, ds2, c, rfl⟩
        · cases hr
      rw [(wps_unfold (e := Expr a (Eannot ds (Expr a2 (Eannot ds2 c))))).to_eq]
      simp only [wps.pre, toVal_annot_none hv,
        show jumpRedex? (Expr a (Eannot ds (Expr a2 (Eannot ds2 c)))) = none from
          jumpRedex?_annot_of_root _ _ rfl,
        show callRedex? (Expr a (Eannot ds (Expr a2 (Eannot ds2 c)))) = none from
          callRedex?_annot_of_root _ _ rfl]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.annot_inv with ⟨hg, hnj, hnc, hnv, c', ρ', ctl', σ'', hs', hout⟩ |
          ⟨a2', ds2', c'', hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
          ⟨hg, hcall⟩ | ⟨a2', b1', v', pc, κ', hb, hκ, _⟩
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
      · obtain ⟨rfl, rfl, rfl⟩ : a2 = a2' ∧ ds2 = ds2' ∧ c = c'' := by
          simpa using hb
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = Expr (a ++ a2) (Eannot (ds ++ ds2) c) ∧
            rρ = ρ ∧ rctl = (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd a ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrctl
        obtain rfl : ρ = rρ := hrρ.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · iapply (wps_annot_reindex
            (Ψ₁ := fun w ρ' => iprop(Ψ (SpikeVal.merge ds w) ρ'))
            a2 (a ++ a2) ds2 (ds ++ ds2) c ρ
            (fun w ρ' => congrArg (fun z => Ψ z ρ')
              (SpikeVal.merge_merge ds ds2 w))) $$ H
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
      · cases hb
    · -- plain body: jump-clause transfer, or reduction in the Cannot
      -- frame + Löb
      have hr' : annotRooted e = false := by simpa using hr
      have hwrap : toVal (Expr a (Eannot ds e)) = none :=
        toVal_annot_none hv
      cases hjr : jumpRedex? e with
      | some lp =>
        -- S3 JUMP CASE: wrap and body share the clause formula.
        rw [wps_unfold.to_eq, wps_unfold.to_eq]
        simp only [wps.pre, hv, hwrap, hjr,
          (jumpRedex?_annot_of_not_root a ds hr').trans hjr]
        iintro H
        iexact H
      | none =>
        cases hcr : callRedex? e with
        | some q =>
          obtain ⟨ctx, f, pes⟩ := q
          rw [wps_unfold.to_eq, wps_unfold.to_eq]
          simp only [wps.pre, hv, hwrap, hjr,
            (jumpRedex?_annot_of_not_root a ds hr').trans hjr,
            hcr, callRedex?_annot_of_not_root a ds hr', Option.map_some,
            apply_ctx_annot]
          iintro H
          imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
          imodintro
          iexists params, body, vs
          isplit
          · ipureintro; exact h1
          isplit
          · ipureintro; exact h2
          isplit
          · ipureintro; exact h3
          isplitl [Hpre]
          · iexact Hpre
          inext
          iintro %ret %a1 Hpost
          ihave H' := Hcont $$ %ret %a1 Hpost
          iapply IH $$ %a %ds %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ρ H'
        | none =>
        rw [wps_unfold.to_eq, wps_unfold.to_eq]
        simp only [wps.pre, hv, hwrap, hjr,
          (jumpRedex?_annot_of_not_root a ds hr').trans hjr,
          hcr, callRedex?_annot_of_not_root a ds hr', Option.map_none]
        iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
        imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
          exact ⟨[], ⟨Expr a (Eannot ds e'.e), e'.ρ, e'.ctl, M⟩, _, [],
            ⟨Step.annot_ctx hjr hcr hv hr' hstep.1, rfl, rfl⟩⟩
        · inext
          iintro %e₂ %σ₂ %eₜ %HstepW Hcred
          obtain ⟨hstepW, hlbl, rfl⟩ := HstepW
          rcases hstepW.annot_inv with ⟨hg, hnj, hnc, hnv, e'', ρ', ctl', σ'', hs, hout⟩ |
              ⟨a2, ds2, c, heq, hout⟩ |
              ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
              ⟨hg, hcall⟩ | ⟨a2', b1', v', pc, κ', hb, hκ, _⟩
          · obtain ⟨e₂e, e₂ρ, e₂ctl, e₂M⟩ := e₂
            simp only at hlbl
            obtain rfl : M = e₂M := hlbl.symm
            obtain ⟨he, hρ, hctl, hσ⟩ : e₂e = Expr a (Eannot ds e'') ∧
                e₂ρ = ρ' ∧ e₂ctl = ctl' ∧ σ₂ = σ'' := by
              simpa [Prod.mk.injEq] using hout
            subst he hρ hctl hσ
            imod H $$ %(⟨e'', e₂ρ, e₂ctl, M⟩ : CoreRt) %_ %([]) %⟨hs, rfl, rfl⟩ Hcred
              with ⟨$, H⟩
            imodintro
            iapply IH $$ %a %ds %e'' %e₂ρ H
          · exact absurd heq (by
              intro heq
              rw [heq] at hr'
              simp [annotRooted] at hr')
          · rw [hjr] at hj; cases hj
          · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
            rw [hcr] at h; cases h
          · rw [hb] at hv; simp at hv

/-! ## The `bound` frame (E1)

The emitted Core wraps every full expression in `bound(...)`
(`Ebound`). On the sequential fragment the frame is INERT: every
sub-step passes through `Cbound` (`Step.bound_ctx`, get_ctx's Ebound arm
core_reduction.lem:563–568), jumps and calls pass through it unchanged
(`jumpRedex?_bound`/`callRedex?_bound`, the captured context grows a
`Cbound` frame), and REMOVE-BOUND (step_ctx's general arm,
core_reduction.lem:1214–1226) delivers the value BARE — the DYNAMIC
ANNOTATIONS of an annotated value are DISCARDED. So the inner
postcondition sees the value at `.pure w.val`. -/

/-- (proof device) `wps_bound` with its two static premises carried inside
    the entailment for the Löb induction. -/
theorem wps_bound_aux {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot) (b : CoreExpr)
    (ρ : EnvStack) :
    iprop(⌜negFree b = true ∧ pot b ≤ lemDefaultFuel⌝ ∗
      wps M p Ls Θ (fun w ρ' => Ψ (SpikeVal.pure w.val) ρ') b ρ) ⊢
      wps M p Ls Θ Ψ (Expr a (Ebound b)) ρ := by
  iloeb as IH generalizing %b %ρ
  cases htv : toVal b with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq, (wps_unfold (e := Expr a (Ebound (ofValA wa)))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_bound_node, jumpRedex?_bound, jumpRedex?_ofValA,
      callRedex?_bound, callRedex?_ofValA, Option.map_none]
    iintro ⟨-, H⟩ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases wa with
      | pure a1 b1 v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.bound_pure, rfl, rfl⟩⟩
      | annot a1 a2 b1 ds v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.bound_annot, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.bound_inv with ⟨_, _, _, _, _, _, _, hnv', _, _⟩ |
        ⟨a1, b1, v, hb, hout⟩ | ⟨a1, a2, b1, ds, v, hb, hout⟩ |
        ⟨_, _, _, _, _, _, _, hj, _, _, _, _⟩ | hcall | ⟨_, _, _, hn, _, _⟩
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · obtain rfl := ofValA_inj hb
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      subst hrctl hre
      obtain rfl : ρ = rρ := hrρ.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imod H with H
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iapply wps_ofValA (.pure a1 b1 v) ρ
        simp only [SpikeValA.erase_pure, SpikeVal.val]
        iexact H
    · obtain rfl := ofValA_inj hb
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      subst hrctl hre
      obtain rfl : ρ = rρ := hrρ.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imod H with H
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iapply wps_ofValA (.pure a2 b1 v) ρ
        simp only [SpikeValA.erase_pure, SpikeValA.erase_annot, SpikeVal.val]
        iexact H
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      rw [callRedex?_ofValA] at h; cases h
    · rw [negRedex?_ofValA] at hn; cases hn
  | none =>
    cases hjr : jumpRedex? b with
    | some lp =>
      rw [wps_unfold.to_eq, (wps_unfold (e := Expr a (Ebound b))).to_eq]
      simp only [wps.pre, htv, toVal_bound_node, jumpRedex?_bound, hjr]
      iintro ⟨-, H⟩
      iexact H
    | none =>
      cases hcr : callRedex? b with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq, (wps_unfold (e := Expr a (Ebound b))).to_eq]
        simp only [wps.pre, htv, toVal_bound_node, jumpRedex?_bound, hjr, callRedex?_bound, hcr,
          Option.map_some, apply_ctx_bound]
        iintro ⟨%hst, H⟩
        obtain ⟨hnf, hpot⟩ := hst
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        obtain ⟨an, ra, hb⟩ := callRedex?_apply_ctx_eq hcr
        have hnf' : negFree (apply_ctx ctx (ofValA (.pure a1 [] ret))) = true := by
          rw [hb] at hnf; exact negFree_apply_ctx_of hnf (negFree_ofValA _)
        have hpot' : pot (apply_ctx ctx (ofValA (.pure a1 [] ret))) ≤ lemDefaultFuel := by
          have hplug := pot_apply_ctx_plug ctx (Expr an (Eproc ra (Sym f) pes))
            (ofValA (.pure a1 [] ret))
          rw [← hb] at hplug
          rw [show pot (Expr an (Eproc ra (Sym f) pes)) = 2 from rfl, pot_ofValA_pure] at hplug
          omega
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ρ
        isplitr
        · ipureintro
          exact ⟨hnf', hpot'⟩
        · iexact H'
      | none =>
        rw [wps_unfold.to_eq, (wps_unfold (e := Expr a (Ebound b))).to_eq]
        simp only [wps.pre, htv, toVal_bound_node, jumpRedex?_bound, hjr, callRedex?_bound, hcr,
          Option.map_none]
        iintro ⟨%hst, H⟩ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
        obtain ⟨hnf, hpot⟩ := hst
        have hnn : negRedex? b = none := negRedex?_none_of_negFree hnf
        have hsz : esize b ≤ lemDefaultFuel := Nat.le_trans (esize_le_pot b) hpot
        imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨obs0, ⟨Expr a (Ebound r'.e), r'.ρ, r'.ctl, M⟩, σ', [],
            ⟨Step.bound_ctx hjr hcr hnn htv hs', rfl, rfl⟩⟩
        inext
        iintro %r %σ₂ %eₜ %Hstep Hcred
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', -, hnv', hs', hout⟩ |
            ⟨_, _, _, hb, _⟩ | ⟨_, _, _, _, _, hb, _⟩ |
            ⟨_, _, _, _, _, _, _, hj, _, _, _, _⟩ | hcall | ⟨_, _, _, hn, _, _⟩
        · obtain ⟨re, rρ, rctl, rM⟩ := r
          simp only at hlbl
          obtain rfl : M = rM := hlbl.symm
          simp only [Prod.mk.injEq] at hout
          obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
          subst hre
          obtain rfl : ρ'' = rρ := hrρ.symm
          obtain rfl : ctl'' = rctl := hrctl.symm
          obtain rfl : σ'' = σ₂ := hσ.symm
          imod H $$ %(⟨b', ρ'', ctl'', M⟩ : CoreRt) %σ'' %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred
            with ⟨$, H⟩
          imodintro
          iapply IH $$ %b' %ρ''
          isplitr
          · ipureintro
            exact ⟨Step.negFree_preserved hs' hsz hnj hnc' hnv' hnf,
              Nat.le_trans (Step.pot_le hs' hsz hnj hnc' hnv' hnf) hpot⟩
          · iexact H
        · rw [hb, toVal_ofValA] at htv; cases htv
        · rw [hb, toVal_ofValA] at htv; cases htv
        · rw [hjr] at hj; cases hj
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [hcr] at h; cases h
        · rw [hnn] at hn; cases hn

/-- `wps` through the `bound` frame (E1) for a NEGATIVE-FREE body within the
    engine's fuel (E5): the `bound` frame performs the negative-action round
    itself (`Step.neg_bound`), so the congruence is sound exactly for bodies
    that never reach one — `negFree`, preserved by every round of the body
    (`Step.negFree_preserved`) with the size invariant `pot` (`Step.pot_le`,
    `esize_le_pot`). Both premises are decided by `rfl` on emitted programs. -/
theorem wps_bound {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot) (b : CoreExpr)
    (ρ : EnvStack) (hnf : negFree b = true) (hpot : pot b ≤ lemDefaultFuel) :
    wps M p Ls Θ (fun w ρ' => Ψ (SpikeVal.pure w.val) ρ') b ρ ⊢
      wps M p Ls Θ Ψ (Expr a (Ebound b)) ρ := by
  iintro H
  iapply wps_bound_aux a b ρ
  isplitr
  · ipureintro
    exact ⟨hnf, hpot⟩
  · iexact H

/-! ## THE SEQUENCING RULE (the jump-aware statement shape — probe
`wps_seq`; the phase-1 proof is the value-beta / annot-beta / step
three-way, S3 adds the jump-clause transfer as the fourth case) -/

theorem wps_seq {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M p Ls Θ (fun w ρ' => wps M p Ls Θ
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    -- e1 is finished: the beta step (LETS-PURE / LETS-ANNOT) at the
    -- cons-shaped env; the continuation comes from the premise's
    -- value channel.
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_sseq_node, jumpRedex?_sseq,
      jumpRedex?_ofValA, callRedex?_sseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with H
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases wa with
      | pure a1 b1 v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_pure, rfl, rfl⟩⟩
      | annot a1 a2 b1 ds v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_annot, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
        ⟨_, _, a1, b1, v, _, _, _, he1, _, hout⟩ |
        ⟨_, _, a1, a2, b1, ds, v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · -- LETS-PURE: successor (e2, ρ, σ)
      obtain rfl : wa = .pure a1 b1 v := ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = e2 ∧ rρ = ev0 :: evs ∧
          rctl = (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd a ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      subst hrρ hrctl
      obtain rfl : e2 = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · rw [show (fun u ρ'' => Ψ (SpikeVal.mergeInto (SpikeValA.pure a1 b1 v).erase u) ρ'')
          = Ψ from rfl]
        iexact H
    · -- LETS-ANNOT: successor ({ds}e2, ρ, σ); exit through wps_annot
      obtain rfl : wa = .annot a1 a2 b1 ds v := ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = Expr [] (Eannot ds e2) ∧
          rρ = ev0 :: evs ∧ rctl = (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd a ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      subst hre hrρ hrctl
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · rw [show (fun u ρ'' => Ψ (SpikeVal.mergeInto (SpikeValA.annot a1 a2 b1 ds v).erase u) ρ'')
          = fun u ρ'' => Ψ (SpikeVal.merge ds u) ρ'' from rfl]
        iapply wps_annot [] ds e2 (ev0 :: evs) $$ H
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · exact (tuplePat_ne_base hpatT1).elim
    · exact (tuplePat_ne_base hpatT2).elim
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      simp at h
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
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        -- the call redex under the frame: the two call clauses agree up
        -- to the captured `Csseq` frame (`apply_ctx_sseq`); the caller's
        -- continuation re-enters through the IH.
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
            e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr,
          Option.map_some, apply_ctx_sseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      -- e1 steps: inversion factor + congruence lift + Löb; the
      -- stack stays CONS-SHAPED (`Step.env_cons` — S3's survivor of
      -- the retired env invariance) and the IH re-enters at the new
      -- head frame; the framed step's control write is threaded (E1).
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
          e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.sseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = Expr a (Esseq (Pattern pa
            (CaseBase (none, bty))) e1' e2) ∧ rρ = ev0' :: evs ∧
            rctl = ctl'' ∧ σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrρ hrctl hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

/-- THE WEAK-SEQUENCING RULE at the wildcard pattern (S1b DRIFT TEST
    — the `wps_seq` clone over the Ewseq lane; same jump-aware
    four-way proof: value-beta / annot-beta / frame step / jump
    transfer). -/
theorem wps_wseq {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M p Ls Θ (fun w ρ' => wps M p Ls Θ
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_wseq_node, jumpRedex?_wseq,
      jumpRedex?_ofValA, callRedex?_wseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with H
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      cases wa with
      | pure a1 b1 v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.wseq_pure, rfl, rfl⟩⟩
      | annot a1 a2 b1 ds v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.wseq_annot, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
        ⟨_, _, a1, b1, v, _, _, _, he1, _, hout⟩ |
        ⟨_, _, a1, a2, b1, ds, v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · -- LETW-PURE: successor (e2, ρ, σ)
      obtain rfl : wa = .pure a1 b1 v := ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = e2 ∧ rρ = ev0 :: evs ∧
          rctl = (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd a ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      subst hrρ hrctl
      obtain rfl : e2 = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · rw [show (fun u ρ'' => Ψ (SpikeVal.mergeInto (SpikeValA.pure a1 b1 v).erase u) ρ'')
          = Ψ from rfl]
        iexact H
    · -- LETW-ANNOT: successor ({ds}e2, ρ, σ); exit through wps_annot
      obtain rfl : wa = .annot a1 a2 b1 ds v := ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = Expr [] (Eannot ds e2) ∧
          rρ = ev0 :: evs ∧ rctl = (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd a ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      subst hre hrρ hrctl
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · rw [show (fun u ρ'' => Ψ (SpikeVal.mergeInto (SpikeValA.annot a1 a2 b1 ds v).erase u) ρ'')
          = fun u ρ'' => Ψ (SpikeVal.merge ds u) ρ'' from rfl]
        iapply wps_annot [] ds e2 (ev0 :: evs) $$ H
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · exact (symPat_ne_base hpatS1).elim
    · exact (symPat_ne_base hpatS2).elim
    · exact (tuplePat_ne_base hpatT1).elim
    · exact (tuplePat_ne_base hpatT2).elim
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      simp at h
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
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
            e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr, callRedex?_wseq, hcr,
          Option.map_some, apply_ctx_wseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      -- e1 steps: inversion factor + congruence lift + Löb
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
          e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr, callRedex?_wseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.wseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = Expr a (Ewseq (Pattern pa
            (CaseBase (none, bty))) e1' e2) ∧ rρ = ev0' :: evs ∧
            rctl = ctl'' ∧ σ₂ = σ'' := by
          simpa [Prod.mk.injEq] using hout
        subst hre hrρ hrctl hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · exact (symPat_ne_base hpatS1).elim
      · exact (symPat_ne_base hpatS2).elim
      · exact (tuplePat_ne_base hpatT1).elim
      · exact (tuplePat_ne_base hpatT2).elim
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

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
    iprop(⌜evalPexpr M.tagDefs M.extern M.file ρ g = some (boolValue b)⌝ ∗
      wps M p Ls Θ Ψ (bif b then e2 else e3) ρ) ⊢
      wps M p Ls Θ Ψ (Expr a (Eif g e2 e3)) ρ := by
  rw [(wps_unfold (e := Expr a (Eif g e2 e3))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Eif g e2 e3)) = none from rfl,
    show jumpRedex? (Expr a (Eif g e2 e3)) = none from rfl,
    show callRedex? (Expr a (Eif g e2 e3)) = none from rfl]
  iintro ⟨%hg, H⟩ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases b
    · exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.if_false hg, rfl, rfl⟩⟩
    · exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.if_true hg, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  have hout : re = (bif b then e2 else e3) ∧ rρ = ρ ∧
      rctl = (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd a ∧ σ₂ = σ₁ := by
    rcases hs.if_inv with ⟨hg', hout⟩ | ⟨hg', hout⟩ <;> cases b <;>
      first
        | (simpa [Prod.mk.injEq] using hout)
        | (rw [hg] at hg'; simp [boolValue] at hg')
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hout
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- Eif, true branch — the `b := true` instance of `wps_if` with the
    verdict at the meta level (retained as a derived corollary). -/
theorem wps_if_true {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack)
    (hg : evalPexpr M.tagDefs M.extern M.file ρ g = some Vtrue) :
    wps M p Ls Θ Ψ e2 ρ ⊢ wps M p Ls Θ Ψ (Expr a (Eif g e2 e3)) ρ := by
  iintro H
  iapply wps_if a g e2 e3 ρ true
  isplit
  · ipureintro; exact hg
  · rw [show (bif true then e2 else e3) = e2 from rfl]
    iexact H

/-- Eif, false branch — the `b := false` instance of `wps_if`. -/
theorem wps_if_false {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack)
    (hg : evalPexpr M.tagDefs M.extern M.file ρ g = some Vfalse) :
    wps M p Ls Θ Ψ e3 ρ ⊢ wps M p Ls Θ Ψ (Expr a (Eif g e2 e3)) ρ := by
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
    wps M p Ls Θ Ψ body (bindSaveParams ps cvals (ev0 :: evs)) ⊢
      wps M p Ls Θ Ψ (Expr a (Esave sb ps body)) (ev0 :: evs) := by
  rw [(wps_unfold (e := Expr a (Esave sb ps body))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Esave sb ps body)) = none from rfl,
    show jumpRedex? (Expr a (Esave sb ps body)) = none from rfl,
    show callRedex? (Expr a (Esave sb ps body)) = none from rfl]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.save hvals, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨ev0', evs', hρeq, hout⟩ := hs.save_vals_inv hvals
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
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
    (hvals : evalPexprs M.tagDefs M.extern M.file ρ (saveParamPexprs ps) = some cvals) :
    wps M p Ls Θ Ψ (Expr a (Esave sb (saveParamsWithValues ps cvals) body)) ρ ⊢
      wps M p Ls Θ Ψ (Expr a (Esave sb ps body)) ρ := by
  rw [(wps_unfold (e := Expr a (Esave sb ps body))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Esave sb ps body)) = none from rfl,
    show jumpRedex? (Expr a (Esave sb ps body)) = none from rfl,
    show callRedex? (Expr a (Esave sb ps body)) = none from rfl]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.save_eval hnv hvals, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨cvals', hvals', hout⟩ := hs.save_op_inv hnv
  obtain rfl : cvals = cvals' := Option.some.inj (hvals.symm.trans hvals')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
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
    (hvals : evalPexprs M.tagDefs M.extern M.file (ev0 :: evs) (saveParamPexprs ps) = some cvals) :
    wps M p Ls Θ Ψ body (bindSaveParams ps cvals (ev0 :: evs)) ⊢
      wps M p Ls Θ Ψ (Expr a (Esave sb ps body)) (ev0 :: evs) := by
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
    wps M p Ls Θ Ψ e' ρ ⊢ wps M p Ls Θ Ψ (Expr a (Ecase pe pats)) ρ := by
  rw [(wps_unfold (e := Expr a (Ecase pe pats))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Ecase pe pats)) = none from rfl,
    show jumpRedex? (Expr a (Ecase pe pats)) = none from rfl,
    show callRedex? (Expr a (Ecase pe pats)) = none from rfl]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨e', ρ, (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd a, M⟩, σ₁, [], ⟨Step.case_value hv hsel, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨e'', hsel', hout⟩ := hs.case_value_inv hv
  obtain rfl : e' = e'' := Option.some.inj (hsel.symm.trans hsel')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
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
theorem wps_pure {Ψ : SpikeVal → EnvStack → IProp GF} {a : List annot}
    (pe : generic_pexpr Unit sym) (ρ : EnvStack) {v : value}
    (hnv : valueFromPexpr pe = none) (hv : evalPexpr M.tagDefs M.extern M.file ρ pe = some v) :
    Ψ (.pure v) ρ ⊢ wps M p Ls Θ Ψ (Expr a (Epure pe)) ρ := by
  rw [(wps_unfold (e := Expr a (Epure pe))).to_eq]
  simp only [wps.pre, toVal_pure_none hnv, jumpRedex?_pure, callRedex?_pure]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.pure_eval hnv hv, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨v', -, hv', hout⟩ := hs.pure_inv hnv
  obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · rw [show Expr a (Epure (Pexpr [] () (PEval v))) =
      ofValA (.pure a [] v) from rfl]
    iapply wps_ofValA (.pure a [] v) ρ
    simp only [SpikeValA.erase_pure]
    iexact H

/-- ACTION_EVAL for a load with an unevaluated pointer operand (S4):
    ONE deterministic engine step evaluating the operand through the
    certified evaluator to the canonical load redex, over which the
    certified load axiom then applies (`Step.load_eval`). -/
theorem wps_load_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 : generic_pexpr Unit sym) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue}
    (hnv2 : valueFromPexpr pe2 = none)
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv))) :
    wps M p Ls Θ Ψ (loadExpr a loc ann ty pv mo) ρ ⊢
      wps M p Ls Θ Ψ (loadOpRedex a loc ann ty pe2 mo) ρ := by
  rw [(wps_unfold (e := loadOpRedex a loc ann ty pe2 mo)).to_eq]
  simp only [wps.pre, loadOpRedex, loadExpr, toVal_action_node, jumpRedex?_action, callRedex?_action]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.load_eval hnv2 hv2, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', hv2', hout⟩ := hs.load_op_inv hnv2
  obtain rfl : pv = pv' := by
    simpa using Option.some.inj (hv2.symm.trans hv2')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
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
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pe : generic_pexpr Unit sym) (ρ : EnvStack)
    {pv : CerbMem.PointerValue}
    (hnv : valueFromPexpr pe = none)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ pe = some (Vobject (OVpointer pv))) :
    wps M p Ls Θ Ψ (killExpr a loc ann kind pv) ρ ⊢
      wps M p Ls Θ Ψ (killOpRedex a loc ann kind pe) ρ := by
  rw [(wps_unfold (e := killOpRedex a loc ann kind pe)).to_eq]
  simp only [wps.pre, killOpRedex, killExpr, toVal_action_node, jumpRedex?_action, callRedex?_action]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.kill_eval hnv hv, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', hv', hout⟩ := hs.kill_op_inv hnv
  obtain rfl : pv = pv' := by
    simpa using Option.some.inj (hv.symm.trans hv')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- ACTION_EVAL for an alloc's operands (kill/free arc K3; the
    `wps_store_eval` twin): an `alloc(pe1, pe2)` whose operands evaluate to
    the integers `align`/`size` is verified by verifying the alloc at
    those values. -/
theorem wps_alloc_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (pe1 pe2 : generic_pexpr Unit sym) (pref : prefix0) (ρ : EnvStack)
    {align size : CerbMem.IntegerValue}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vobject (OVinteger align)))
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVinteger size))) :
    wps M p Ls Θ Ψ (allocExpr a loc ann align size pref) ρ ⊢
      wps M p Ls Θ Ψ (allocOpRedex a loc ann pe1 pe2 pref) ρ := by
  rw [(wps_unfold (e := allocOpRedex a loc ann pe1 pe2 pref)).to_eq]
  simp only [wps.pre, allocOpRedex, allocExpr, toVal_action_node, jumpRedex?_action, callRedex?_action]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.alloc_eval hnv hv1 hv2, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨al', sz', hv1', hv2', hout⟩ := hs.alloc_op_inv hnv
  obtain rfl : align = al' := by
    simpa using Option.some.inj (hv1.symm.trans hv1')
  obtain rfl : size = sz' := by
    simpa using Option.some.inj (hv2.symm.trans hv2')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- ACTION_EVAL for a create's operands (E1; the `wps_alloc_eval` twin):
    a `create(pe1, pe2)` whose operands evaluate to an integer alignment and
    a ctype — the emitted shape is `create(Ivalignof(ty), ty)`, evaluated by
    `evalPexpr_tyctor`/`evalTyCtor_alignof` — is verified by verifying the
    create at those values. -/
theorem wps_create_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (pe1 pe2 : generic_pexpr Unit sym) (pref : prefix0) (ρ : EnvStack)
    {align : CerbMem.IntegerValue} {ty : ctype}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some (Vobject (OVinteger align)))
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vctype ty)) :
    wps M p Ls Θ Ψ (createExpr a loc ann align ty pref) ρ ⊢
      wps M p Ls Θ Ψ (createOpRedex a loc ann pe1 pe2 pref) ρ := by
  rw [(wps_unfold (e := createOpRedex a loc ann pe1 pe2 pref)).to_eq]
  simp only [wps.pre, createOpRedex, createExpr, toVal_action_node, jumpRedex?_action,
    callRedex?_action]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.create_eval hnv hv1 hv2, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨al', ty', hv1', hv2', hout⟩ := hs.create_op_inv hnv
  obtain rfl : align = al' := by
    simpa using Option.some.inj (hv1.symm.trans hv1')
  obtain rfl : ty = ty' := by
    simpa using Option.some.inj (hv2.symm.trans hv2')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
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
    wps M p Ls Θ (fun w ρ' => iprop(∃ (ov : object_value),
        ⌜w.val = Vloaded (LVspecified ov)⌝ ∗
        wps M p Ls Θ (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2
          (update_env (specPat pa pb x bty) (Vloaded (LVspecified ov)) ρ')))
      e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Esseq (specPat pa pb x bty) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (specPat pa pb x bty)
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_sseq_node, jumpRedex?_sseq,
      jumpRedex?_ofValA, callRedex?_sseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with ⟨%ov, %hval, Hinner⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    cases wa with
    | pure a1 b1 v =>
      obtain rfl : v = Vloaded (LVspecified ov) := hval
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_spec_pure, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', a1', b1', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', _, _, _, ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (specPat_ne_base hpat.symm).elim
      · exact (specPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ ov = ov' := by
          simpa using ofValA_inj he1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hrρ
        obtain rfl : e2 = re := hre.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · rw [show (fun u ρ'' =>
            Ψ (SpikeVal.mergeInto (SpikeValA.pure a1 b1
              (Vloaded (LVspecified ov))).erase u) ρ'') = Ψ from rfl]
          iexact Hinner
      · exact absurd (ofValA_inj he1) (by simp)
      · exact (symPat_ne_spec hpat).elim
      · exact (symPat_ne_spec hpat).elim
      · exact (specPat_ne_tuple hpatT1).elim
      · exact (specPat_ne_tuple hpatT2).elim
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        simp at h
    | annot a1 a2 b1 ds v =>
      obtain rfl : v = Vloaded (LVspecified ov) := hval
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_spec_annot, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', _, _, ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', a1', a2', b1', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (specPat_ne_base hpat.symm).elim
      · exact (specPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact absurd (ofValA_inj he1) (by simp)
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ ov = ov' := by
          simpa using ofValA_inj he1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hre hrρ
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · rw [show (fun u ρ'' =>
            Ψ (SpikeVal.mergeInto (SpikeValA.annot a1 a2 b1 ds
              (Vloaded (LVspecified ov))).erase u) ρ'') =
            (fun u ρ'' => Ψ (SpikeVal.merge ds u) ρ'') from rfl]
          iapply wps_annot [] ds e2 _ $$ Hinner
      · exact (symPat_ne_spec hpat).elim
      · exact (symPat_ne_spec hpat).elim
      · exact (specPat_ne_tuple hpatT1).elim
      · exact (specPat_ne_tuple hpatT2).elim
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        simp [callRedex?, annotRooted] at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (specPat pa pb x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Esseq (specPat pa pb x bty) e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr,
          Option.map_some, apply_ctx_sseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (specPat pa pb x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Esseq (specPat pa pb x bty)
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.sseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · exact (specPat_ne_tuple hpatT1).elim
      · exact (specPat_ne_tuple hpatT2).elim
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

/-! ## The plain-symbol-binder sequencing rule (list-reverse phase A)

`lets x = e1 in e2` at a bare symbol pattern — the memop result's
binding idiom (Step.lean `symPat`). The premise's value channel
carries the PURE-value shape fact (E1: the mirror now has the
LETS-ANNOT beta at this binder too — `Step.sseq_sym_annot` — but this
rule is stated at heads delivering BARE values; an annotated-head face
is a rule addition, not needed by the emitted shapes of E1, whose
symbol-bound heads are `create`, `bound(…)` and the memop), and the
continuation is verified at the value-bound environment. -/

theorem wps_seq_sym {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M p Ls Θ (fun w ρ' => iprop(∃ (v : value),
        ⌜w = SpikeVal.pure v⌝ ∗
        wps M p Ls Θ Ψ e2 (update_env (symPat pa x bty) v ρ')))
      e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Esseq (symPat pa x bty) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (symPat pa x bty)
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_sseq_node, jumpRedex?_sseq,
      jumpRedex?_ofValA, callRedex?_sseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with ⟨%v, %hval, Hinner⟩
    obtain ⟨a1, b1, rfl⟩ : ∃ a1 b1, wa = .pure a1 b1 v := by
      cases wa with
      | pure a1 b1 v' => cases hval; exact ⟨a1, b1, rfl⟩
      | annot a1 a2 b1 ds v' => cases hval
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_sym_pure, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
        ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨pa', x', bty', a1', b1', v', _, _, hpat, he1, _, hout⟩ |
        ⟨pa', x', bty', _, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
      obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ v = v' := by
        simpa using ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      subst hrctl
      subst hrρ
      obtain rfl : e2 = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iexact Hinner
    · exact absurd (ofValA_inj he1) (by simp)
    · exact (symPat_ne_tuple hpatT1).elim
    · exact (symPat_ne_tuple hpatT2).elim
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      simp at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (symPat pa x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Esseq (symPat pa x bty) e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr,
          Option.map_some, apply_ctx_sseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (symPat pa x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Esseq (symPat pa x bty)
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.sseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · exact (symPat_ne_tuple hpatT1).elim
      · exact (symPat_ne_tuple hpatT2).elim
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

/-! ## The pointer-test memop rules (list-reverse phase A)

The null test as the ENGINE's own pointer memop, at the wps stratum:
`wps_memop_ptreq` consumes the pure single-layer `eqPtrval` verdict
(Heap.lean's `eqPtrval_null_null` / `eqPtrval_cell_null` /
`eqPtrval_null_cell` discharge `hres` at the fragment's shapes);
`wps_memop_eval` is the one-step operand evaluation into the
canonical value-operand redex (the memop analog of
`wps_load_eval`). -/


/-- E2: THE STRONG-SEQUENCING RULE at a flat TUPLE binder (`let strong (a, b)
    = e1 in e2`): the head delivers a BARE tuple value, the continuation is
    verified at the tuple-bound environment (`update_env` at the tuple
    pattern — the engine's `Ctuple` arm, zipping leaves against components).
    The `wps_seq_sym` clone. -/
theorem wps_seq_tuple {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (ls : List TupleLeaf)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M p Ls Θ (fun w ρ' => iprop(∃ (vs : List value),
        ⌜w = SpikeVal.pure (Vtuple vs)⌝ ∗
        wps M p Ls Θ Ψ e2 (update_env (tuplePat pa ls) (Vtuple vs) ρ')))
      e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Esseq (tuplePat pa ls) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (tuplePat pa ls)
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_sseq_node, jumpRedex?_sseq,
      jumpRedex?_ofValA, callRedex?_sseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with ⟨%vs, %hval, Hinner⟩
    obtain ⟨a1, b1, rfl⟩ : ∃ a1 b1, wa = .pure a1 b1 (Vtuple vs) := by
      cases wa with
      | pure a1 b1 v' => cases hval; exact ⟨a1, b1, rfl⟩
      | annot a1 a2 b1 ds v' => cases hval
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_tuple_pure, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
        ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs0, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨pa', ls', a1', b1', vs', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, he1, _, _⟩ |
        hcall
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · exact (tuplePat_ne_base hpat.symm).elim
    · exact (tuplePat_ne_base hpat.symm).elim
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · exact (specPat_ne_tuple hpat.symm).elim
    · exact (specPat_ne_tuple hpat.symm).elim
    · exact (symPat_ne_tuple hpat.symm).elim
    · exact (symPat_ne_tuple hpat.symm).elim
    · obtain ⟨rfl, rfl⟩ := tuplePat_inj hpat
      obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ vs = vs' := by
        simpa using ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      subst hrctl
      subst hrρ
      obtain rfl : e2 = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iexact Hinner
    · exact absurd (ofValA_inj he1) (by simp)
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      simp at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (tuplePat pa ls) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Esseq (tuplePat pa ls) e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr,
          Option.map_some, apply_ctx_sseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (tuplePat pa ls) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Esseq (tuplePat pa ls)
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.sseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

/-! ## The pointer-test memop rules (list-reverse phase A)

The null test as the ENGINE's own pointer memop, at the wps stratum:
`wps_memop_ptreq` consumes the pure single-layer `eqPtrval` verdict
(Heap.lean's `eqPtrval_null_null` / `eqPtrval_cell_null` /
`eqPtrval_null_cell` discharge `hres` at the fragment's shapes);
`wps_memop_eval` is the one-step operand evaluation into the
canonical value-operand redex (the memop analog of
`wps_load_eval`). -/

/-- E2: THE WEAK-SEQUENCING RULE at the plain-symbol binder (`let weak x =
    e1 in e2`): the head delivers a BARE value, bound verbatim (the
    `wps_seq_sym` clone over the Cwseq frame). -/
theorem wps_wseq_sym {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M p Ls Θ (fun w ρ' => iprop(∃ (v : value),
        ⌜w = SpikeVal.pure v⌝ ∗
        wps M p Ls Θ Ψ e2 (update_env (symPat pa x bty) v ρ')))
      e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Ewseq (symPat pa x bty) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Ewseq (symPat pa x bty)
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_wseq_node, jumpRedex?_wseq,
      jumpRedex?_ofValA, callRedex?_wseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with ⟨%v, %hval, Hinner⟩
    obtain ⟨a1, b1, rfl⟩ : ∃ a1 b1, wa = .pure a1 b1 v := by
      cases wa with
      | pure a1 b1 v' => cases hval; exact ⟨a1, b1, rfl⟩
      | annot a1 a2 b1 ds v' => cases hval
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.wseq_sym_pure, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
        ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs0, _, _, hj, _, _, _, _⟩ |
        ⟨pa', x', bty', a1', b1', v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, he1, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
      obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ v = v' := by
        simpa using ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      subst hrctl
      subst hrρ
      obtain rfl : e2 = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iexact Hinner
    · exact absurd (ofValA_inj he1) (by simp)
    · exact (symPat_ne_tuple hpatT1).elim
    · exact (symPat_ne_tuple hpatT2).elim
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      simp at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (symPat pa x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Ewseq (symPat pa x bty) e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr, callRedex?_wseq, hcr,
          Option.map_some, apply_ctx_wseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (symPat pa x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr, callRedex?_wseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Ewseq (symPat pa x bty)
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.wseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

/-! ## The pointer-test memop rules (list-reverse phase A)

The null test as the ENGINE's own pointer memop, at the wps stratum:
`wps_memop_ptreq` consumes the pure single-layer `eqPtrval` verdict
(Heap.lean's `eqPtrval_null_null` / `eqPtrval_cell_null` /
`eqPtrval_null_cell` discharge `hres` at the fragment's shapes);
`wps_memop_eval` is the one-step operand evaluation into the
canonical value-operand redex (the memop analog of
`wps_load_eval`). -/

/-- E2: THE WEAK-SEQUENCING RULE at a flat TUPLE binder — the corpus's `let
    weak (a, b) = e1 in e2` (the `wps_seq_tuple` clone over the Cwseq frame). -/
theorem wps_wseq_tuple {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (ls : List TupleLeaf)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M p Ls Θ (fun w ρ' => iprop(∃ (vs : List value),
        ⌜w = SpikeVal.pure (Vtuple vs)⌝ ∗
        wps M p Ls Θ Ψ e2 (update_env (tuplePat pa ls) (Vtuple vs) ρ')))
      e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Ewseq (tuplePat pa ls) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Ewseq (tuplePat pa ls)
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_wseq_node, jumpRedex?_wseq,
      jumpRedex?_ofValA, callRedex?_wseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with ⟨%vs, %hval, Hinner⟩
    obtain ⟨a1, b1, rfl⟩ : ∃ a1 b1, wa = .pure a1 b1 (Vtuple vs) := by
      cases wa with
      | pure a1 b1 v' => cases hval; exact ⟨a1, b1, rfl⟩
      | annot a1 a2 b1 ds v' => cases hval
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.wseq_tuple_pure, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
        ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs0, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨pa', ls', a1', b1', vs', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, he1, _, _⟩ |
        hcall
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · exact (tuplePat_ne_base hpat.symm).elim
    · exact (tuplePat_ne_base hpat.symm).elim
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · exact (symPat_ne_tuple hpat.symm).elim
    · exact (symPat_ne_tuple hpat.symm).elim
    · obtain ⟨rfl, rfl⟩ := tuplePat_inj hpat
      obtain ⟨rfl, rfl, rfl⟩ : a1 = a1' ∧ b1 = b1' ∧ vs = vs' := by
        simpa using ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      subst hrctl
      subst hrρ
      obtain rfl : e2 = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iexact Hinner
    · exact absurd (ofValA_inj he1) (by simp)
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      simp at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (tuplePat pa ls) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Ewseq (tuplePat pa ls) e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr, callRedex?_wseq, hcr,
          Option.map_some, apply_ctx_wseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (tuplePat pa ls) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr, callRedex?_wseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Ewseq (tuplePat pa ls)
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.wseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

/-! ## E4: the `unseq` rules (dialect arc E4, docs/2026-09-05_e4-notes.md)

The sequential driver reduces an `unseq` one component at a time, the LAST
reducible component first (`Step.unseq_ctx`, the engine's `get_ctx_unseq_aux`
order, core_reduction.lem:590–601), and at all values completes the node into
the annotated tuple `{A_1 ++ … ++ A_n}(v_1, …, v_n)` when the components'
dynamic annotations do not race (`Step.unseq_vals`; a race is the engine's
UB035 kill, `complete_unseq_vals`, for which no rule exists). The rules are
therefore SEQUENTIAL COMPOSITION in the engine's order — the Reynolds/O'Hearn
reading: the components are proved one after another against the resources
each needs, framing is the judgment's, the post is at the tuple.
`wps_unseq_focus` peels the focused component (the value it delivers, at ANY
static annotation lists — the term keeps the value node, so the continuation
is quantified over the exact value `wa`); `wps_unseq_vals` closes the node. -/

/-- E4: the judgment absorbs a leading update — every clause of `wps.pre`
    begins with `|={⊤}=>` or a `={⊤,∅}=∗` wand (the classical `fupd_wp`). -/
theorem fupd_wps {Ψ : SpikeVal → EnvStack → IProp GF} (e : CoreExpr) (ρ : EnvStack) :
    iprop(|={⊤}=> wps M p Ls Θ Ψ e ρ) ⊢ wps M p Ls Θ Ψ e ρ := by
  rw [wps_unfold.to_eq]
  cases htv : toVal e with
  | some w =>
    simp only [wps.pre, htv]
    iintro H
    imod H with H
    iexact H
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      simp only [wps.pre, htv, hjr]
      iintro H
      imod H with H
      iexact H
    | none =>
      cases hcr : callRedex? e with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        simp only [wps.pre, htv, hjr, hcr]
        iintro H
        imod H with H
        iexact H
      | none =>
        simp only [wps.pre, htv, hjr, hcr]
        iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
        imod H with H
        iapply H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ

/-- THE FOCUS RULE (partial): `unseq(es1, e, es2)` with every component of
    `es2` a value and ccall-free siblings reduces `e` first (the engine's
    last-reducible-first order); when `e` delivers a value `w`, the node
    continues as `unseq(es1, wa, es2)` for the EXACT value node `wa` erasing
    to `w` (the term keeps the value node; the continuation is stated at
    every such `wa` because the post only sees `w`). -/
theorem wps_unseq_focus {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (es1 : List CoreExpr) (e : CoreExpr) (es2 : List CoreExpr) (ρ : EnvStack)
    (hv2 : valsOnly es2 = true) (hcc : ccallFreeList (es1 ++ es2) = true) :
    wps M p Ls Θ (fun w ρ' => iprop(∀ wa : SpikeValA, ⌜wa.erase = w⌝ -∗
        wps M p Ls Θ Ψ (Expr a (Eunseq (es1 ++ ofValA wa :: es2))) ρ')) e ρ ⊢
      wps M p Ls Θ Ψ (Expr a (Eunseq (es1 ++ e :: es2))) ρ := by
  iloeb as IH generalizing %e %ρ
  cases htv : toVal e with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    iintro H
    ihave H' := wps_value_inv (M := M) (p := p) (Ls := Ls) (Θ := Θ) wa ρ $$ H
    iapply fupd_wps
    imod H' with H'
    imodintro
    iapply H' $$ %wa %rfl
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      rw [wps_unfold.to_eq, (wps_unfold (e := Expr a (Eunseq (es1 ++ e :: es2)))).to_eq]
      simp only [wps.pre, htv, toVal_unseq_node, jumpRedex?_unseq_focus a htv hv2, hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? e with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq, (wps_unfold (e := Expr a (Eunseq (es1 ++ e :: es2)))).to_eq]
        simp only [wps.pre, htv, toVal_unseq_node, jumpRedex?_unseq_focus a htv hv2, hjr,
          callRedex?_unseq_focus a htv hv2, hcr, Option.map_some, apply_ctx_unseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ρ H'
      | none =>
        rw [wps_unfold.to_eq, (wps_unfold (e := Expr a (Eunseq (es1 ++ e :: es2)))).to_eq]
        simp only [wps.pre, htv, toVal_unseq_node, jumpRedex?_unseq_focus a htv hv2, hjr,
          callRedex?_unseq_none htv hv2 hcr, hcr]
        iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
        imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨obs0, ⟨Expr a (Eunseq (es1 ++ r'.e :: es2)), r'.ρ, r'.ctl, M⟩, σ', [],
            ⟨Step.unseq_ctx hv2 hcc hjr hcr htv hs', rfl, rfl⟩⟩
        inext
        iintro %r %σ₂ %eₜ %Hstep Hcred
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.unseq_inv with
            ⟨es1', e0, es2', e0', ρ'', ctl'', σ'', heq, hv2', -, hnj, hnc', hnv', hs', hout⟩ |
            ⟨ws, fps, cvals, heq, -, -⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            ⟨es1', e0, es2', heq, hnv', hv2', hcall⟩
        · obtain ⟨rfl, rfl, rfl⟩ := focus_unique heq htv hnv' hv2 hv2'
          obtain ⟨re, rρ, rctl, rM⟩ := r
          simp only at hlbl
          obtain rfl : M = rM := hlbl.symm
          simp only [Prod.mk.injEq] at hout
          obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
          subst hre
          obtain rfl : ρ'' = rρ := hrρ.symm
          obtain rfl : ctl'' = rctl := hrctl.symm
          obtain rfl : σ'' = σ₂ := hσ.symm
          imod H $$ %(⟨e0', ρ'', ctl'', M⟩ : CoreRt) %σ'' %([] : List CoreRt)
            %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
          imodintro
          iapply IH $$ %e0' %ρ'' H
        · have h1 : valsOnly (es1 ++ e :: es2) = true := by
            rw [heq]; exact valsOnly_map_ofValA ws
          rw [valsOnly_append_cons_false htv] at h1
          cases h1
        · rw [jumpRedex?_unseq_focus a htv hv2, hjr] at hj; cases hj
        · obtain ⟨rfl, rfl, rfl⟩ := focus_unique heq htv hnv' hv2 hv2'
          obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [hcr] at h; cases h

/-- THE COMPLETION RULE (partial): `unseq(v_1, …, v_n)` at all-value
    components whose dynamic annotations do not race (`collectUnseq`, the
    engine's `one_step_unseq_aux`) is ONE deterministic engine step to the
    annotated tuple `{fps}(cvals)` — an annotated VALUE, so the post is at
    `.annot fps (Vtuple cvals)` (E2's tuple binder at an annotated head,
    `wps_wseq_tuple_annot`, is what consumes it). -/
theorem wps_unseq_vals {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (ws : List SpikeValA) (ρ : EnvStack) {fps : List dyn_annotation} {cvals : List value}
    (hcol : collectUnseq ([], []) ws = some (fps, cvals)) :
    Ψ (.annot fps (Vtuple cvals)) ρ ⊢
      wps M p Ls Θ Ψ (Expr a (Eunseq (ws.map ofValA))) ρ := by
  rw [(wps_unfold (e := Expr a (Eunseq (ws.map ofValA)))).to_eq]
  simp only [wps.pre, toVal_unseq_node, jumpRedex?_unseq_vals, callRedex?_unseq_vals]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.unseq_vals hcol, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  rcases hs.unseq_inv with
      ⟨es1, e0, es2, _, _, _, _, heq, hv2, -, -, -, hnv0, -, -⟩ |
      ⟨ws', fps', cvals', heq, hcol', hout⟩ |
      ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
      ⟨es1, e0, es2, heq, hnv0, hv2, hcall⟩
  · have h1 : valsOnly (es1 ++ e0 :: es2) = true := by
      rw [← heq]; exact valsOnly_map_ofValA ws
    rw [valsOnly_append_cons_false hnv0] at h1
    cases h1
  · obtain rfl := map_ofValA_inj heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hcol.symm.trans hcol'))
    obtain ⟨re, rρ, rctl, rM⟩ := r
    simp only at hlbl
    obtain rfl : M = rM := hlbl.symm
    simp only [Prod.mk.injEq] at hout
    obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
    subst hrctl hre
    obtain rfl : ρ = rρ := hrρ.symm
    obtain rfl : σ₁ = σ₂ := hσ.symm
    imod Hclose with -
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · rw [show Expr a (Eannot fps (Expr [] (Epure (Pexpr [] () (PEval (Vtuple cvals)))))) =
        ofValA (.annot a [] [] fps (Vtuple cvals)) from rfl]
      iapply wps_ofValA (.annot a [] [] fps (Vtuple cvals)) ρ
      simp only [SpikeValA.erase_annot]
      iexact H
  · rw [jumpRedex?_unseq_vals] at hj; cases hj
  · have h1 : valsOnly (es1 ++ e0 :: es2) = true := by
      rw [← heq]; exact valsOnly_map_ofValA ws
    rw [valsOnly_append_cons_false hnv0] at h1
    cases h1

/-- E2's flat TUPLE binder at an ANNOTATED head (LETW-ANNOT at the tuple
    pattern, `Step.wseq_tuple_annot`, core_reduction.lem:397–405): the
    corpus's `let weak (a, b) = unseq(…) in e2` — the `unseq` delivers the
    annotated tuple `{A}(v_1, …)`, the binder binds the components and the
    dynamic annotations RIDE onto the continuation (`Expr [] (Eannot ds e2)`;
    `wps_annot` then merges them into `e2`'s value). The rule at a BARE tuple
    head is `wps_wseq_tuple` (E2); this is its annotated face (E4). -/
theorem wps_wseq_tuple_annot {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (ls : List TupleLeaf)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M p Ls Θ (fun w ρ' => iprop(∃ (vs : List value) (ds : List dyn_annotation),
        ⌜w = SpikeVal.annot ds (Vtuple vs)⌝ ∗
        wps M p Ls Θ Ψ (Expr [] (Eannot ds e2)) (update_env (tuplePat pa ls) (Vtuple vs) ρ')))
      e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Ewseq (tuplePat pa ls) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Ewseq (tuplePat pa ls)
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_wseq_node, jumpRedex?_wseq,
      jumpRedex?_ofValA, callRedex?_wseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with ⟨%vs, %ds, %hval, Hinner⟩
    obtain ⟨a1, a2, b1, rfl⟩ : ∃ a1 a2 b1, wa = .annot a1 a2 b1 ds (Vtuple vs) := by
      cases wa with
      | pure a1 b1 v' => cases hval
      | annot a1 a2 b1 ds' v' => cases hval; exact ⟨a1, a2, b1, rfl⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.wseq_tuple_annot, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
        ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs0, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpat, he1, _, _⟩ |
        ⟨pa', ls', a1', a2', b1', ds', vs', _, _, hpat, he1, _, hout⟩ |
        hcall
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · exact (tuplePat_ne_base hpat.symm).elim
    · exact (tuplePat_ne_base hpat.symm).elim
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · exact (symPat_ne_tuple hpat.symm).elim
    · exact (symPat_ne_tuple hpat.symm).elim
    · exact absurd (ofValA_inj he1) (by simp)
    · obtain ⟨rfl, rfl⟩ := tuplePat_inj hpat
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ vs = vs' := by
        simpa using ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      subst hrctl
      subst hrρ
      obtain rfl : Expr [] (Eannot ds e2) = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iexact Hinner
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      rw [callRedex?_ofValA] at h
      cases h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (tuplePat pa ls) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Ewseq (tuplePat pa ls) e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr, callRedex?_wseq, hcr,
          Option.map_some, apply_ctx_wseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Ewseq (tuplePat pa ls) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_wseq_node, jumpRedex?_wseq, hjr, callRedex?_wseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Ewseq (tuplePat pa ls)
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.wseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

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
theorem wps_memop_ptreq {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (pv1 pv2 : CerbMem.PointerValue) {b : Bool} (ρ : EnvStack)
    (hres : ∀ σ : Mem, applyMemM (CerbMem.eqPtrval default pv1 pv2) σ =
      some (b, σ)) :
    Ψ (.pure (boolValue b)) ρ ⊢
      wps M p Ls Θ Ψ (memopPtrEqVals a (Vobject (OVpointer pv1))
        (Vobject (OVpointer pv2))) ρ := by
  rw [(wps_unfold (e := memopPtrEqVals a (Vobject (OVpointer pv1))
    (Vobject (OVpointer pv2)))).to_eq]
  simp only [wps.pre, memopPtrEqVals, memopRedex, toVal_memop_node,
    jumpRedex?_memop, callRedex?_memop]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [],
      ⟨Step.memop_ptreq rfl rfl (hres σ₁), rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨b', σ'', hmem, hout⟩ := hs.memop_ptreq_inv rfl rfl
  rw [hres σ₁] at hmem
  obtain ⟨rfl, rfl⟩ : b = b' ∧ σ₁ = σ'' := by
    have h := Option.some.inj hmem
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
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
theorem wps_memop_eval {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (mop : memop) (pe1 pe2 : generic_pexpr Unit sym)
    {v1 v2 : value} (ρ : EnvStack)
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hv1 : evalPexpr M.tagDefs M.extern M.file ρ pe1 = some v1)
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some v2) :
    wps M p Ls Θ Ψ (memopRedex a mop
      [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) ρ ⊢
      wps M p Ls Θ Ψ (memopRedex a mop [pe1, pe2]) ρ := by
  rw [(wps_unfold (e := memopRedex a mop [pe1, pe2])).to_eq]
  simp only [wps.pre, memopRedex, toVal_memop_node, jumpRedex?_memop, callRedex?_memop]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.memop_eval hnv hv1 hv2, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨v1', v2', hv1', hv2', hout⟩ := hs.memop_op_inv hnv
  obtain rfl : v1 = v1' := Option.some.inj (hv1.symm.trans hv1')
  obtain rfl : v2 = v2' := Option.some.inj (hv2.symm.trans hv2')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
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
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 pe3 : generic_pexpr Unit sym) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue} {cv : value}
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr M.tagDefs M.extern M.file ρ pe3 = some cv) :
    wps M p Ls Θ Ψ (storeExpr a loc ann ty pv cv mo) ρ ⊢
      wps M p Ls Θ Ψ (storeOpRedex a loc ann ty pe2 pe3 mo) ρ := by
  rw [(wps_unfold (e := storeOpRedex a loc ann ty pe2 pe3 mo)).to_eq]
  simp only [wps.pre, storeOpRedex, storeExpr, toVal_action_node, jumpRedex?_action, callRedex?_action]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [],
      ⟨Step.store_eval hnv hv2 hv3, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', cv', hv2', hv3', hout⟩ := hs.store_op_inv hnv
  obtain rfl : pv = pv' := by
    simpa using Option.some.inj (hv2.symm.trans hv2')
  obtain rfl : cv = cv' := Option.some.inj (hv3.symm.trans hv3')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
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
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (storeExpr a loc ann ty pv cv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => store_atomic a loc ann ty pv cv mo mv bs ρ hmv hst) rfl rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%fp, %hw, Hpt'⟩
    subst hw
    iapply HΨ $$ Hpt'

/-- Load small axiom over `wps` (any fraction, UB-excluding — the
    `htrap` premise excludes the _Bool trap arm as in `wp_load`). -/
theorem wps_load {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv dq ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv dq ty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] (loadedVal M.tagDefs pv ty bs)) ρ)) ⊢
      wps M p Ls Θ Ψ (loadExpr a loc ann ty pv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => load_atomic a loc ann ty pv mo dq bs ρ htrap) rfl rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%hw, Hpt'⟩
    subst hw
    iapply HΨ $$ Hpt'

/-- THE DISPOSE RULE over `wps` (kill/free arc K2): `kill_atomic`
    lifted. The classical `{p ↦ -} kill(static ty, p) {emp}`: full
    ownership of the created object's cell is consumed; the
    continuation runs at the BARE unit value (no footprint annotation
    — the engine's continuation is `mk_value_e Vunit`, so no `_plain`
    form is needed) and is offered the persistent DEAD cell
    `deadObj` at the pointer's id and base (drop it: `wps_kill_emp`).
    `hstatic`: the kill is static — the dynamic `free` is `wps_free`
    (K3), over the region bundle. -/
theorem wps_kill {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      ((∃ (id a : Int), ⌜pv = cellPtr id a⌝ ∗ deadObj M.tagDefs id a ty) -∗
        Ψ (SpikeVal.pure Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (killExpr a loc ann kind pv) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => kill_atomic a loc ann kind pv ty bs ρ hstatic) rfl rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%hw, Hd⟩
    subst hw
    iapply HΨ $$ Hd

/-- The textbook face: `{p ↦ -} kill(static ty, p) {emp}` — the dead
    cell dropped. -/
theorem wps_kill_emp {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗ Ψ (SpikeVal.pure Vunit) ρ) ⊢
      wps M p Ls Θ Ψ (killExpr a loc ann kind pv) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_kill a loc ann kind pv ty bs ρ hstatic
  isplitl [Hpt]
  · iexact Hpt
  · iintro -
    iexact HΨ

/-- THE PUBLIC ALLOCATION RULE for DYNAMIC storage (kill/free arc K3;
    `alloc_atomic` lifted): the budget `regionCost alignN sizeN` buys
    `alloc(alignN, sizeN)`; the continuation binds the fresh region
    pointer `cellPtr id a` with the whole REGION at full ownership
    (`regionOwn`, untyped, unspecified bytes) and its machine-address
    bounds. `hcost`: a positive cost — every positive size
    (`regionCost_pos`), or size 0 at alignment ≥ 2; see `alloc_atomic`. -/
theorem wps_alloc {Ψ : SpikeVal → EnvStack → IProp GF}
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov sprov : CerbMem.Provenance) (alignN sizeN : Int)
    (pref : prefix0) (ρ : EnvStack)
    (hcost : 0 < regionCost alignN sizeN) :
    iprop(allocBudget (GF := GF) (regionCost alignN sizeN) ∗
      (∀ (id a : Int),
        (regionOwn id a sizeN.toNat (.own 1) (List.replicate sizeN.toNat undefByte) ∗
          ⌜0 < a ∧ a + (sizeN.toNat : Int) ≤ 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer (cellPtr id a)))) ρ)) ⊢
      wps M p Ls Θ Ψ (allocExpr an loc ann (.IV aprov alignN) (.IV sprov sizeN) pref) ρ := by
  iintro ⟨Hb, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => alloc_atomic an loc ann aprov sprov alignN sizeN pref ρ hcost) rfl rfl rfl
  isplitl [Hb]
  · iexact Hb
  · iintro %w ⟨%id, %a, %hw, Hr, %hb⟩
    subst hw
    iapply HΨ
    isplitl [Hr]
    · iexact Hr
    · ipureintro
      exact hb

/-- THE FREE RULE at the statement stratum (kill/free arc K3;
    `free_atomic` lifted): the whole live region at full ownership is
    consumed; the continuation runs at the BARE unit value and is offered
    the persistent DEAD region `deadRegion` (drop it: `wps_free_emp`).
    `hdyn`: the kill is dynamic — `free(p)`. The operand form is the
    kind-generic `wps_kill_eval`. -/
theorem wps_free {Ψ : SpikeVal → EnvStack → IProp GF}
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (id a : Int) (n : Nat) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hdyn : is_dynamic kind = true) :
    iprop(regionOwn (GF := GF) id a n (.own 1) bs ∗
      (deadRegion id a n -∗ Ψ (SpikeVal.pure Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (killExpr an loc ann kind (cellPtr id a)) ρ := by
  iintro ⟨Hr, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => free_atomic an loc ann kind id a n bs ρ hdyn) rfl rfl rfl
  isplitl [Hr]
  · iexact Hr
  · iintro %w ⟨%hw, Hd⟩
    subst hw
    iapply HΨ $$ Hd

/-- The textbook face: `{p ↦ region} free(p) {emp}` — the dead region
    dropped. -/
theorem wps_free_emp {Ψ : SpikeVal → EnvStack → IProp GF}
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (id a : Int) (n : Nat) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hdyn : is_dynamic kind = true) :
    iprop(regionOwn (GF := GF) id a n (.own 1) bs ∗ Ψ (SpikeVal.pure Vunit) ρ) ⊢
      wps M p Ls Θ Ψ (killExpr an loc ann kind (cellPtr id a)) ρ := by
  iintro ⟨Hr, HΨ⟩
  iapply wps_free an loc ann kind id a n bs ρ hdyn
  isplitl [Hr]
  · iexact Hr
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
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (.pure Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (storeExpr a loc ann ty pv cv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_store a loc ann ty pv cv mo mv bs ρ hmv hst
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt'
  rw [hΨ]
  iapply HΨ $$ Hpt'

/-- `wps_load` for an annotation-insensitive postcondition. -/
theorem wps_load_plain {Ψ : SpikeVal → EnvStack → IProp GF}
    (hΨ : ∀ (ds : List dyn_annotation) (v : value) (ρ' : EnvStack),
      Ψ (.annot ds v) ρ' = Ψ (.pure v) ρ')
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv dq ty bs ∗
      (pointsToCell M.tagDefs pv dq ty bs -∗ Ψ (.pure (loadedVal M.tagDefs pv ty bs)) ρ)) ⊢
      wps M p Ls Θ Ψ (loadExpr a loc ann ty pv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_load a loc ann ty pv mo dq bs ρ htrap
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
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (mo : memory_order) (dqm dqb : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(pointsToView M.tagDefs (GF := GF) id a aty off dqm dqb vty bs ∗
      (∀ fp, pointsToView M.tagDefs id a aty off dqm dqb vty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M p Ls Θ Ψ (loadExpr an loc ann vty (cellPtr id (a + (off : Int))) mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => loadAt_atomic an loc ann id a aty off vty mo dqm dqb bs ρ hdec htrap)
    rfl rfl rfl
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
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order) (dqm : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hst : StorableView M.tagDefs vty mv) :
    iprop(pointsToView M.tagDefs (GF := GF) id a aty off dqm (.own 1) vty bs ∗
      (∀ fp, pointsToView M.tagDefs id a aty off dqm (.own 1) vty
          (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (storeExpr an loc ann vty (cellPtr id (a + (off : Int))) cv mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => storeAt_atomic an loc ann id a aty off vty cv mo dqm bs ρ hmv hst)
    rfl rfl rfl
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
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
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
      wps M p Ls Θ Ψ (loadExpr an loc ann vty (cellPtr id (a + (off : Int))) mo)
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
  iapply wps_load_at an loc ann id a aty off vty mo dq dq
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
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
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
      wps M p Ls Θ Ψ (storeExpr an loc ann vty (cellPtr id (a + (off : Int))) cv mo)
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
  iapply wps_store_at an loc ann id a aty off vty cv mo (.own 1)
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

/-! ## THE REGION ACCESS RULES at the statement stratum (kill/free arc K5)

Typed load/store THROUGH A REGION POINTER: the `regionLoadAt_atomic`/
`regionStoreAt_atomic` specifications lifted (the `wps_load_at`/
`wps_store_at` twins over the typed region view), and the whole-region
interior forms over `regionOwn` (the `wps_load_cell_at`/`wps_store_cell_at`
twins: carve the typed subrange out of the whole region, run the typed
rule, uncarve — the recomposition of a store IS `spliceBytes`). The
operand forms are the pointer-generic `wps_load_eval`/`wps_store_eval`. -/

/-- TYPED SUBRANGE LOAD THROUGH A REGION small axiom (any fractions,
    UB-excluding): loading a typed region view delivers the fixed decode
    of its byte image; the view rides through untouched. -/
theorem wps_load_region_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (mo : memory_order) (dqm dqb : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(typedRegionView M.tagDefs (GF := GF) id a n off dqm dqb vty bs ∗
      (∀ fp, typedRegionView M.tagDefs id a n off dqm dqb vty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M p Ls Θ Ψ (loadExpr an loc ann vty (cellPtr id (a + (off : Int))) mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => regionLoadAt_atomic an loc ann id a n off vty mo dqm dqb bs ρ hdec htrap)
    rfl rfl rfl
  isplitl [Hv]
  · iexact Hv
  · iintro %w ⟨%fp, %hw, Hv'⟩
    subst hw
    iapply HΨ $$ Hv'

/-- FULL-OWNERSHIP TYPED SUBRANGE STORE THROUGH A REGION small axiom
    (UB-excluding): storing through a typed region view REPLACES the
    view's byte image wholesale. The serialization premises are the
    `StorableView` facts at the accessed type. -/
theorem wps_store_region_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order) (dqm : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hst : StorableView M.tagDefs vty mv) :
    iprop(typedRegionView M.tagDefs (GF := GF) id a n off dqm (.own 1) vty bs ∗
      (∀ fp, typedRegionView M.tagDefs id a n off dqm (.own 1) vty
          (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (storeExpr an loc ann vty (cellPtr id (a + (off : Int))) cv mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => regionStoreAt_atomic an loc ann id a n off vty cv mo dqm bs ρ hmv hst)
    rfl rfl rfl
  isplitl [Hv]
  · iexact Hv
  · iintro %w ⟨%fp, %hw, Hv'⟩
    subst hw
    iapply HΨ $$ Hv'

/-- Interior typed load THROUGH whole-region ownership (any accessed
    type and offset; the region rides through untouched). Derived from
    `wps_load_region_at` by `regionOwn_carve`/`regionOwn_uncarve`. -/
theorem wps_load_regionOwn_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hbound : off + CerbMem.sizeofCtype M.tagDefs vty ≤ n)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(regionOwn (GF := GF) id a n dq bs ∗
      (∀ fp, regionOwn id a n dq bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M p Ls Θ Ψ (loadExpr an loc ann vty (cellPtr id (a + (off : Int))) mo)
        ρ := by
  iintro ⟨Hr, HΨ⟩
  icases (regionOwn_carve M.tagDefs id a n off dq vty bs hbound) $$ Hr
    with ⟨%hlen, Hv, Hpre, Hsuf⟩
  have htk : (bs.take off).length = off := by
    simp [List.length_take]
    omega
  have hsplit : bs = bs.take off ++
      ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty) ++
        (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty)) := by
    rw [List.take_append_drop, List.take_append_drop]
  iapply wps_load_region_at an loc ann id a n off vty mo dq dq _ ρ hdec htrap
  isplitl [Hv]
  · iexact Hv
  iintro %fp Hv
  iapply HΨ
  have hEnt : regionOwn (GF := GF) id a n dq (bs.take off ++
      ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty) ++
        (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty))) ⊢
      regionOwn id a n dq bs := by
    rw [← hsplit]
  iapply hEnt
  iapply regionOwn_uncarve M.tagDefs id a n off dq vty _ _ _ htk (by rw [← hsplit]; exact hlen)
  isplitl [Hv]
  · iexact Hv
  isplitl [Hpre]
  · iexact Hpre
  · iexact Hsuf

/-- Interior typed store THROUGH whole-region ownership: the region's
    image is SPLICED at the accessed subrange. Derived from
    `wps_store_region_at` by `regionOwn_carve`/`regionOwn_uncarve`. No
    decode-inertness premise: a region has no allocation type to be
    inert at. -/
theorem wps_store_regionOwn_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (an : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hbound : off + CerbMem.sizeofCtype M.tagDefs vty ≤ n)
    (hst : StorableView M.tagDefs vty mv) :
    iprop(regionOwn (GF := GF) id a n (.own 1) bs ∗
      (∀ fp, regionOwn id a n (.own 1)
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (storeExpr an loc ann vty (cellPtr id (a + (off : Int))) cv mo)
        ρ := by
  iintro ⟨Hr, HΨ⟩
  icases (regionOwn_carve M.tagDefs id a n off (.own 1) vty bs hbound) $$ Hr
    with ⟨%hlen, Hv, Hpre, Hsuf⟩
  have htk : (bs.take off).length = off := by
    simp [List.length_take]
    omega
  have hsplice : spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs =
      bs.take off ++ ((CerbMem.memValueToBytes M.tagDefs [] mv).2 ++
        (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty)) := by
    unfold spliceBytes
    rw [List.append_assoc, List.drop_drop, hst.len]
  have hlen' : (bs.take off ++ ((CerbMem.memValueToBytes M.tagDefs [] mv).2 ++
      (bs.drop off).drop (CerbMem.sizeofCtype M.tagDefs vty))).length = n := by
    rw [List.length_append, List.length_append, htk, hst.len, List.length_drop,
      List.length_drop, hlen]
    omega
  iapply wps_store_region_at an loc ann id a n off vty cv mo (.own 1) _ ρ hmv hst
  isplitl [Hv]
  · iexact Hv
  iintro %fp Hv
  iapply HΨ
  rw [hsplice]
  iapply regionOwn_uncarve M.tagDefs id a n off (.own 1) vty _ _ _ htk hlen'
  isplitl [Hv]
  · iexact Hv
  isplitl [Hpre]
  · iexact Hpre
  · iexact Hsuf


/-! ## THE ALLOCATION RULE (alloc arc P1.4; RESTATED over the budget,
kill/free arc K2.5)

- `wps_create` — THE PUBLIC RULE: precondition `allocBudget (allocCost
  ty alignN)` (the ∗-splittable capacity, Heap.lean "The allocation
  budget"), existential/continuation-bound pointer result with the
  fresh whole-cell points-to and the pointer's machine-address bounds;
  the budget is CONSUMED. It is `create_atomic` (Rules.lean) lifted by
  `wps_of_atomic` — no cursor stratum remains: the former exact-cursor
  `wps_create_cursor_internal` and the ordered plan `allocCap (req ::
  rest)` are RETIRED (no client owns the cursor since K2.5; its
  fragment lives in the state interpretation, `budgetInterp`). NO
  cursor vocabulary in the statement (the P1 grep test, unchanged).
  Launchable: the allocation-aware launchers (Adequacy/TotalAdequacy)
  grant `allocBudget B` from real Cerberus memory via `launchResources`
  under `LaunchCoh … B` (`B ≤ headroom lastAddress`).
- `wps_create_of_plan` — the plan-shaped reading: the former statement
  with `allocCap reqs` read as `allocBudget (planCost reqs)`, derived
  from `wps_create` by `allocBudget_split` (the notes' plan → budget
  derivation).

Donor shape: RefinedC's alloc_new_blocks/alloc_alive discipline
(theories/caesium/ghost_state.v) — there the allocator is part of the
state interpretation and the client sees an existential fresh location
(lifting.v:979-998), and Caesium never refuses an allocation; here the
engine's allocator is a deterministic downward cursor WITH an
out-of-memory kill, so a capacity resource is forced — the classical
additive budget, coupled by the inequality `B ≤ headroom lastAddress`
(no-OOM policy: docs/2026-09-03_k2.5-notes.md, superseding the P1.1
plan record). -/

section CreateRule
open Iris.Std.PartialMap

/-- THE PUBLIC ALLOCATION RULE (alloc arc P1.4, restated K2.5): the
    budget `allocCost ty alignN = sizeof ty + max(alignN, 1) − 1` buys
    one `create` of `ty` at alignment `alignN`; the returned pointer is
    CONTINUATION-BOUND (its allocation id and address occur nowhere in
    the precondition), delivered with full whole-cell ownership at
    unspecified bytes and its pure machine-address bounds `0 < addrOf p
    < 2^64` (alloc arc P2). Side premises: `hsz` pins a real object
    type (the engine's `max 1` padding away — formerly carried inside
    the plan), `hatom` a non-atomic one; `hinert` is the unspecified
    image's decode-inertness AT EVERY ADDRESS (rfl for scalar and
    integer-array types). The no-OOM guard is NOT a premise: it rides
    inside the budget (the coupling inequality, `create_atomic`). The
    statement contains no `AllocCursor`/`lastAddress`/`nextAllocId`/
    `freshBase`/`cursorOwn` — the P1 grep test. -/
theorem wps_create {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (ty : ctype)
    (pref : prefix0) (ρ : EnvStack)
    (hsz : 0 < CerbMem.sizeofCtype M.tagDefs ty) (hatom : atomicTy ty = false)
    (hinert : ∀ a : Int, decIndep M.tagDefs a ty
      (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte)) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs ty alignN) ∗
      (∀ p : CerbMem.PointerValue,
        (pointsToCell M.tagDefs p (.own 1) ty
            (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte) ∗
          ⌜0 < addrOf p ∧ addrOf p < 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer p))) ρ)) ⊢
      wps M p Ls Θ Ψ (createExpr a loc ann (.IV aprov alignN) ty pref) ρ := by
  iintro ⟨Hb, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => create_atomic a loc ann aprov alignN ty pref ρ hsz hatom hinert) rfl rfl rfl
  isplitl [Hb]
  · iexact Hb
  · iintro %w ⟨%p, %hw, Hpt, %hb⟩
    subst hw
    iapply HΨ
    isplitl [Hpt]
    · iexact Hpt
    · ipureintro
      exact hb

/-- THE PLAN-SHAPED READING (the K2.5 plan → budget derivation): the
    former `allocCap (req :: rest)` rule with the plan read as its
    summed cost — capacity for the whole plan buys the head request and
    returns capacity for the rest. Derived from `wps_create` by
    `allocBudget_split`; a client may also hold MORE than the plan
    (`allocBudget_weaken`), which the ordered plan could not express. -/
theorem wps_create_of_plan {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (req : AllocReq) (rest : List AllocReq)
    (pref : prefix0) (ρ : EnvStack)
    (hsz : 0 < CerbMem.sizeofCtype M.tagDefs req.ty) (hatom : atomicTy req.ty = false)
    (hinert : ∀ a : Int, decIndep M.tagDefs a req.ty
      (List.replicate (CerbMem.sizeofCtype M.tagDefs req.ty) undefByte)) :
    iprop(allocBudget (GF := GF) (planCost M.tagDefs (req :: rest)) ∗
      (∀ p : CerbMem.PointerValue,
        (pointsToCell M.tagDefs p (.own 1) req.ty
            (List.replicate (CerbMem.sizeofCtype M.tagDefs req.ty) undefByte) ∗
          allocBudget (planCost M.tagDefs rest) ∗
          ⌜0 < addrOf p ∧ addrOf p < 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer p))) ρ)) ⊢
      wps M p Ls Θ Ψ (createExpr a loc ann (.IV aprov req.align) req.ty pref) ρ := by
  rw [planCost_cons]
  iintro ⟨Hb, HΨ⟩
  icases (allocBudget_split (allocCost M.tagDefs req.ty req.align)
    (planCost M.tagDefs rest)).1 $$ Hb with ⟨Hb, Hrest⟩
  iapply wps_create a loc ann aprov req.align req.ty pref ρ hsz hatom hinert
  isplitl [Hb]
  · iexact Hb
  iintro %p ⟨Hpt, %hb⟩
  iapply HΨ
  isplitl [Hpt]
  · iexact Hpt
  isplitl [Hrest]
  · iexact Hrest
  · ipureintro
    exact hb

end CreateRule

/-! ## Block specifications, procedure specifications, THE COLLAPSE, and the loop rules

The collapse into the base Iris WP (the sole adequacy interface).
S3 form as pre-declared: `wps_sound` gains the `blockSpecs` premise
and the one Löb-tied jump case (the donor `wps_block_rec` analog,
probe report §2 — the mutual-□ + iLöb of the donor SPLITS: the
per-label proofs, `blockSpecs_intro`, need NO Löb because the jump
clause breaks the back-edge circularity; the single Löb induction
lands here, simultaneously the stmt-WP-to-WP collapse). Calls arc C3:
the collapse becomes CPS over the ambient control (`wps_sound_cps`,
RefinedC's `stmt_wp_def` shape, lifting.v:1002) and gains the
`procSpecs` premise; the SAME Löb now ties every back edge AND every
call (Hoare's rule for recursive procedures: each body is verified
assuming the table for all procedures, itself included). -/

/-- All block specifications (donor `[∗ map] wps_block`,
    lifting.v:1302/1306's premise collection, flat form —
    unregistered labels are vacuous because the lookup premise is
    unsatisfiable; probe `blockSpecs`). The jump-time env is
    quantified in cons shape (registered continuations are
    sseq-extended and closed under the registration discipline, so
    per-label proofs quantify it freely; the jump binds the
    parameters over whatever env the jump arrives in). Indexed by the
    procedure `p` whose label fiber is consulted (C3). -/
abbrev blockSpecs (M : MachineCtx) (p : Option sym) (Ls : LabelSpec GF) (Θ : ProcSpec GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) : IProp GF :=
  iprop(□ ∀ (l : sym) (params : List (sym × core_base_type))
    (cont : CoreExpr) (vs : List value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)),
    ⌜lookupLabel (M.labelsAt p) l = some (params, cont)⌝ -∗ Ls l vs (ev0 :: evs) -∗
      wps M p Ls Θ Ψ cont (bindArgs params vs (ev0 :: evs)))

/-- THE PER-LABEL INVARIANT RULE (partial correctness, the default
    loop rule): assembling the block specifications needs NO Löb and
    no mutual assumption — the back-edge circularity is broken by
    the jump clause (each body's own back edges discharge against
    `Ls` directly, via `wps_run`). This is where the label-context
    shape pays: the donor `wps_block_rec`'s mutual-□ premise is not
    needed; its Löb lives in `wps_sound_cps`. -/
theorem blockSpecs_intro {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l params cont vs ev0 evs,
      lookupLabel (M.labelsAt p) l = some (params, cont) →
      Ls l vs (ev0 :: evs) ⊢ wps (GF := GF) M p Ls Θ Ψ cont
        (bindArgs params vs (ev0 :: evs))) :
    ⊢ blockSpecs M p Ls Θ Ψ := by
  unfold blockSpecs
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %hQ HLs
  iapply h l params cont vs ev0 evs hQ $$ HLs

/-- FRAMING THE BLOCK SPECIFICATIONS: block specifications at `Ls`
    are block specifications at the framed context, with the frame
    joining the postcondition — the per-label bodies are framed by
    `wps_frame_labels`. -/
theorem blockSpecs_frame {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF) :
    blockSpecs (GF := GF) M p Ls Θ Ψ ⊢
      blockSpecs M p (frameLs R Ls) Θ (fun w ρ' => iprop(Ψ w ρ' ∗ R)) := by
  iintro #HB
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %hQ ⟨HLs, HR⟩
  ihave HW := HB $$ %l %params %cont %vs %ev0 %evs %hQ HLs
  iapply wps_frame_labels R cont (bindArgs params vs (ev0 :: evs)) $$ HW HR

/-- Monotonicity of the block specifications in the postcondition (the
    `blockSpecsT_mono` twin, QA-1/M-3; through `wps_wand`). -/
theorem blockSpecs_mono {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ w ρ', Ψ₁ w ρ' ⊢ Ψ₂ w ρ') :
    blockSpecs (GF := GF) M p Ls Θ Ψ₁ ⊢ blockSpecs M p Ls Θ Ψ₂ := by
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

/-! ### Procedure specifications (calls arc C3) -/

/-- PROCEDURE SPECIFICATIONS HOLD (the twin of `blockSpecs`; RefinedC's
    conjunction of every function's `typed_function`,
    tutorial/adequacy/adequacy.v:108–128): every procedure the file
    declares (`lookupProc`, `call_proc`'s stdlib-first read) meets its
    table entry at EVERY argument list of the right arity and EVERY
    caller environment `ρ` — there is a label specification `Ls` for the
    activation under which its label bodies are verified (`blockSpecs`
    at the callee's fiber `M.labelsAt (some f)`) and its body, entered
    at the fresh parameter frame `procEnv params vs` pushed on `ρ`
    (`call_proc`'s fold, `env := proc_env :: th_st.env`), delivers the
    postcondition on the value. The body is verified ASSUMING the table
    `Θ` for every procedure, itself included: Hoare's rule for
    recursive procedures; the knot is tied once, in `wps_sound_cps`.

    `∀ ρ` OVER THE CALLER'S TAIL IS FORCED: `lookup_env`
    (Core_aux.lean:872) searches ALL frames top-down, so a body's read
    of a symbol its own frame does not bind would resolve in the
    CALLER's frames — the specification must therefore hold for every
    tail. A body whose free symbols are its parameters and locals never
    reaches the tail (every read is a head-frame hit, `lookup_env_head`
    on the `SymFrame` `procEnv` builds), so `∀ ρ` costs nothing in a
    body proof; no closedness side condition enters the logic. The
    postcondition ignores the callee's final env: RETURN pops it
    (`Step.ret`), and the caller's env is restored verbatim
    (`SameTail`, threaded by the collapse). -/
abbrev procSpecs (M : MachineCtx) (Θ : ProcSpec GF) : IProp GF :=
  iprop(□ ∀ (f : sym) (params : List (sym × core_base_type)) (body : CoreExpr)
    (vs : List value) (ρ : EnvStack),
    ⌜lookupProc M.file M.extern f = some (params, body)⌝ -∗ ⌜params.length = vs.length⌝ -∗
    ∃ (Ls : LabelSpec GF),
      blockSpecs M (some f) Ls Θ (fun w _ => (Θ f vs).2 w.val) ∗
      ((Θ f vs).1 -∗
        wps M (some f) Ls Θ (fun w _ => (Θ f vs).2 w.val) body (procEnv params vs :: ρ)))

/-- THE PROCEDURE RULE'S INTRODUCTION (the twin of `blockSpecs_intro`):
    a client discharges `procSpecs` for a concrete file by ONE label
    table `Lsₚ` (per procedure and argument list) and, per declared
    procedure, its block specifications and ONE `wps` proof of its body
    under the precondition — assuming `Θ` for every call inside (the
    body's own calls, recursive ones included, discharge by `wps_call`
    against the table). NO Löb here: the circularity is broken by the
    call clause, exactly as the jump clause breaks the back edges; the
    single Löb is `wps_sound_cps`'s. -/
theorem procSpecs_intro (Lsₚ : sym → List value → LabelSpec GF)
    (hB : ∀ f params body vs, lookupProc M.file M.extern f = some (params, body) →
      params.length = vs.length →
      ⊢ blockSpecs (GF := GF) M (some f) (Lsₚ f vs) Θ (fun w _ => (Θ f vs).2 w.val))
    (hW : ∀ f params body vs (ρ : EnvStack),
      lookupProc M.file M.extern f = some (params, body) → params.length = vs.length →
      (Θ f vs).1 ⊢ wps (GF := GF) M (some f) (Lsₚ f vs) Θ (fun w _ => (Θ f vs).2 w.val) body
        (procEnv params vs :: ρ)) :
    ⊢ procSpecs M Θ := by
  unfold procSpecs
  imodintro
  iintro %f %params %body %vs %ρ %hf %hlen
  iexists Lsₚ f vs
  isplit
  · exact hB f params body vs hf hlen
  · iintro Hpre
    iapply hW f params body vs ρ hf hlen $$ Hpre

/-- The empty table is trivially met: no precondition is satisfiable. -/
theorem procSpecs_empty : ⊢ procSpecs (GF := GF) M emptyProcSpec := by
  unfold procSpecs
  imodintro
  iintro %f %params %body %vs %ρ %_ %_
  iexists (fun _ _ _ => iprop(⌜False⌝))
  isplit
  · unfold blockSpecs
    imodintro
    iintro %l %params' %cont %vs' %ev0 %evs %_ %hF
    exact hF.elim
  · simp only [emptyProcSpec_fst]
    iintro %hF
    exact hF.elim

/-! ### The return at the raw WP (the collapse's two devices) -/

/-- THE RETURN ROUND at the raw WP: a bare value under a frame steps by
    `Step.ret` alone (`Step.ret_inv`) — to the value plugged into the
    saved context (its pexpr annotations reset, the node's riding), at
    the popped env and the caller's procedure, the execution location,
    the current location and the supplies riding. -/
theorem wp_ret {Φ : CoreRVal → IProp GF} (a1 b1 : List annot) (v : value) (ev0 : Fmap sym value)
    (evs : EnvStack) (p₀ : Option sym) (ctx : context)
    (κ : List (Option sym × context)) (q : Option sym) (ℓ : exec_location)
    (lc : CerbLocation.Loc) (sp : RunSup) :
    WP (⟨apply_ctx ctx (ofValA (.pure a1 [] v)), evs, ⟨κ, p₀, ℓ, lc, sp⟩, M⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ {{ Φ }} ⊢
      WP (⟨ofValA (.pure a1 b1 v), ev0 :: evs, ⟨(p₀, ctx) :: κ, q, ℓ, lc, sp⟩, M⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  iintro H
  iapply wp_lift_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.ret, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨ev0', evs', heq, hout⟩ := hs.ret_inv
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hre hrρ hrctl
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · simp only [List.length_nil, Nat.add_zero]
    iexact Hσ
  isplitr []
  · iexact H
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

/-- REMOVE-ANNOT under a frame at the raw WP: the annotated value taus
    to the inner bare value node at the same env and control
    (`Step.ret_annot`, `Step.ret_annot_inv`); the bare value then returns
    (`wp_ret`). -/
theorem wp_ret_annot {Φ : CoreRVal → IProp GF} (a1 a2 b1 : List annot) (ds : List dyn_annotation)
    (v : value) (ρ : EnvStack) (pc : Option sym × context) (κ : List (Option sym × context))
    (q : Option sym) (ℓ : exec_location) (lc : CerbLocation.Loc) (sp : RunSup) :
    WP (⟨ofValA (.pure a2 b1 v), ρ, ⟨pc :: κ, q, ℓ, lc, sp⟩, M⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ {{ Φ }} ⊢
      WP (⟨ofValA (.annot a1 a2 b1 ds v), ρ, ⟨pc :: κ, q, ℓ, lc, sp⟩, M⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  iintro H
  iapply wp_lift_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.ret_annot, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  have hout := hs.ret_annot_inv
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hre hrctl
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · simp only [List.length_nil, Nat.add_zero]
    iexact Hσ
  isplitr []
  · iexact H
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

/-! ### THE COLLAPSE -/

/-- THE LÖB-TIED ELIMINATION IN CPS OVER THE AMBIENT CONTROL (calls arc
    C3; the donor `wps_block_rec` analog + the stmt-WP-to-WP collapse in
    one, now in RefinedC's `stmt_wp_def` shape, lifting.v:1002–1003):
    under the procedure specifications and the block specifications of
    the current procedure, the statement WP at `(p, e, ρ)` entails the
    base Iris WP of the configuration `⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩` at ANY
    call stack `κ`, execution location `ℓ`, current location `lc` and run
    supplies `sp` (E1: the two live-state fields are ambient exactly as
    `ℓ` is — written along the way, never read by the judgment), given a
    CONTINUATION `K` that accepts every value `w` the statement delivers
    at a final env `ρ'` with the frames below the head preserved
    (`SameTail ρ ρ'`), at ANY execution location `ℓ'`, current location
    `lc'` and supplies `sp'`, with the value's own static annotation
    lists, and yields the WP of the value at that configuration. ONE Löb
    induction ties every back edge AND every call:
    - VALUE: `K`.
    - JUMP: the (□) block spec turns the label precondition into the
      body's statement WP; the IH, a step later (the jump step's `▷`).
    - CALL (`Step.call`, its inversion `Step.call_inv`): the callee's
      body is verified by `procSpecs` at its own label spec, at the
      pushed frame `procEnv params vs :: ρ`, under the pushed control
      (`Ctl.callPush`); the IH applies to it with the continuation `K'`
      that performs THE RETURN: the callee's final env is `ev0' :: ρ`
      (`SameTail`), its value is bare or annotated (`wp_ret`,
      `wp_ret_annot`), and RETURN lands in the caller's continuation
      `apply_ctx ctx (pure ret)` at the caller's env `ρ` and procedure
      `p` — where the call clause's continuation and the IH (again) take
      over, with the caller's own `K`. `▷` is paid by the call round.
    - STEP: the IH at the successor, `K` composed with the step's
      `SameTail`.
    At `κ = []` with `K := wp_value` this is the pre-C3 statement
    (`wps_sound`); the recursion knot is Hoare's: `procSpecs` assumes
    the table for every body, the IH is the assumption discharged.
    Partial correctness (donor parity). -/
theorem wps_sound_cps (p : Option sym) (Ls : LabelSpec GF) {Ψ : SpikeVal → EnvStack → IProp GF}
    (κ : List (Option sym × context)) (ℓ : exec_location) (lc : CerbLocation.Loc) (sp : RunSup)
    (e : CoreExpr) (ρ : EnvStack)
    (Φ : CoreRVal → IProp GF) :
    procSpecs M Θ ⊢
      iprop(blockSpecs M p Ls Θ Ψ -∗ wps M p Ls Θ Ψ e ρ -∗
        ⌜M.runState.sym_supply ≤ sp.sym⌝ -∗
        (∀ (ℓ' : exec_location) (lc' : CerbLocation.Loc) (sp' : RunSup) (w : SpikeValA)
          (ρ' : EnvStack), ⌜SameTail ρ ρ'⌝ -∗ ⌜M.runState.sym_supply ≤ sp'.sym⌝ -∗
          Ψ w.erase ρ' -∗
          WP (⟨ofValA w, ρ', ⟨κ, p, ℓ', lc', sp'⟩, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ Φ }}) -∗
        WP (⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ Φ }}) := by
  iintro #HP
  iloeb as IH generalizing %p %Ls %Ψ %κ %ℓ %lc %sp %e %ρ %Φ
  iintro #HB Hwps %hsb HK
  cases htv : toVal e with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    ihave H := wps_value_inv wa ρ $$ Hwps
    iapply fupd_wp
    imod H with H
    imodintro
    iapply HK $$ %ℓ %lc %sp %wa %ρ %(SameTail.refl ρ) %hsb H
  | none =>
    have htoval : ToVal.toVal (Val := CoreRVal) (⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩ : CoreRt) = none :=
      toValRt_eq_none_of_toVal_none htv
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iapply wp_lift_step htoval
      iintro %σ₁ %ns %obs %obs' %nt Hσ
      imod Hwps with ⟨%params, %cont, %vs, %ev0, %evs, %hρ, %hl, %hvs, HLs⟩
      subst hρ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨cont, bindArgs params vs (ev0 :: evs),
          (⟨κ, p, ℓ, lc, sp⟩ : Ctl).upd (redexAnnots e), M⟩, σ₁, [],
          ⟨Step.run hjr hl hvs, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      obtain ⟨params', cont', vs', ev0', evs', hρ', hl', hvs', hout⟩ := hs.jump_inv hjr
      obtain ⟨rfl, rfl⟩ : params = params' ∧ cont = cont' := by
        rw [hl] at hl'
        exact ⟨congrArg Prod.fst (Option.some.inj hl'),
          congrArg Prod.snd (Option.some.inj hl')⟩
      obtain rfl : vs = vs' := by
        rw [hvs] at hvs'
        exact Option.some.inj hvs'
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      obtain rfl : cont = re := hre.symm
      subst hrρ hrctl
      obtain rfl : σ₁ = σ₂ := hσ.symm
      have hst : SameTail (ev0 :: evs) (bindArgs params vs (ev0 :: evs)) := hs.sameTail rfl
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · simp only [List.length_nil, Nat.add_zero]
        iexact Hσ
      isplitr []
      · ihave Hwps' := HB $$ %l %params %cont %vs %ev0 %evs %hl HLs
        simp only [Ctl.upd_mk]
        iapply IH $$ %p %Ls %Ψ %κ %ℓ %(locUpd (redexAnnots e) lc) %sp %cont
          %(bindArgs params vs (ev0 :: evs)) %Φ HB Hwps' %hsb
        iintro %ℓ' %lc' %sp' %w %ρ' %hst' %hsb' HΨ
        iapply HK $$ %ℓ' %lc' %sp' %w %ρ' %(hst.trans hst') %hsb' HΨ
      · simp only [Algebra.BigOpL.bigOpL_nil]
        itrivial
    | none =>
      cases hcr : callRedex? e with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq]
        simp only [wps.pre, htv, hjr, hcr]
        iapply wp_lift_step htoval
        iintro %σ₁ %ns %obs %obs' %nt Hσ
        imod Hwps with ⟨%params, %body, %vs, %hf, %hlen, %hvs, Hpre, Hcont⟩
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hclose
        isplitr
        · ipureintro
          exact ⟨[], ⟨body, procEnv params vs :: ρ,
            (⟨κ, p, ℓ, lc, sp⟩ : Ctl).callPush (redexAnnots e) ctx f, M⟩, σ₁, [],
            ⟨Step.call hcr hvs hf hlen, rfl, rfl⟩⟩
        inext
        iintro %r %σ₂ %eₜ %Hstep Hcred
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        obtain ⟨params', body', vs', hvs', hf', hlen', hout⟩ := hs.call_inv hcr
        obtain ⟨rfl, rfl⟩ : params = params' ∧ body = body' := by
          rw [hf] at hf'
          exact ⟨congrArg Prod.fst (Option.some.inj hf'),
            congrArg Prod.snd (Option.some.inj hf')⟩
        obtain rfl : vs = vs' := by
          rw [hvs] at hvs'
          exact Option.some.inj hvs'
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        obtain rfl : body = re := hre.symm
        obtain rfl : procEnv params vs :: ρ = rρ := hrρ.symm
        obtain rfl : (⟨κ, p, ℓ, lc, sp⟩ : Ctl).callPush (redexAnnots e) ctx f = rctl :=
          hrctl.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        imodintro
        isplitl [Hσ]
        · simp only [List.length_nil, Nat.add_zero]
          iexact Hσ
        isplitr []
        · ihave HS := HP $$ %(f) %params %body %vs %ρ %hf %hlen
          icases HS with ⟨%Ls', #HB', Hbody⟩
          ihave Hbody := Hbody $$ Hpre
          simp only [Ctl.callPush]
          iapply IH $$ %(some f) %Ls' %(fun w _ => (Θ f vs).2 w.val)
            %((p, ctx) :: κ) %(push_exec_loc f (locUpd (redexAnnots e) lc) ℓ)
            %(locUpd (redexAnnots e) lc) %sp %body
            %(procEnv params vs :: ρ) %Φ HB' Hbody %hsb
          -- K': the RETURN into the caller's continuation
          iintro %ℓ' %lc' %sp' %w %ρ' %hst %hsb'
          obtain ⟨ev0', rfl⟩ := hst.cons_inv
          cases w with
          | pure a1 b1 v =>
            dsimp only [SpikeValA.erase, SpikeVal.val]
            iintro Hpost
            ihave Hw := Hcont $$ %v %a1 Hpost
            iapply wp_ret
            iapply IH $$ %p %Ls %Ψ %κ %ℓ' %lc' %sp' %(apply_ctx ctx (ofValA (.pure a1 [] v)))
              %ρ %Φ HB Hw %hsb' HK
          | annot a1 a2 b1 ds v =>
            dsimp only [SpikeValA.erase, SpikeVal.val]
            iintro Hpost
            ihave Hw := Hcont $$ %v %a2 Hpost
            iapply wp_ret_annot
            iapply wp_ret
            iapply IH $$ %p %Ls %Ψ %κ %ℓ' %lc' %sp' %(apply_ctx ctx (ofValA (.pure a2 [] v)))
              %ρ %Φ HB Hw %hsb' HK
        · simp only [Algebra.BigOpL.bigOpL_nil]
          itrivial
      | none =>
      rw [wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr, hcr]
      iapply wp_lift_step htoval
      iintro %σ₁ %ns %obs %obs' %nt Hσ
      imod Hwps $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, Hwps⟩
      imodintro
      isplitr
      · ipureintro
        exact hred
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, hnil⟩ := Hstep
      obtain ⟨re, rρ, ⟨rκ, rp, rℓ, rlc, rsp⟩, rM⟩ := r
      simp only at hlbl hs
      obtain rfl : M = rM := hlbl.symm
      have hce := Step.ctl_eq hs hcr htv
      obtain ⟨rfl, rfl, rfl⟩ : κ = rκ ∧ p = rp ∧ ℓ = rℓ := ⟨hce.1.symm, hce.2.1.symm, hce.2.2.symm⟩
      have hst : SameTail ρ rρ := hs.sameTail rfl
      imod Hwps $$ %(⟨re, rρ, ⟨κ, p, ℓ, rlc, rsp⟩, M⟩ : CoreRt) %σ₂ %eₜ %(⟨hs, rfl, hnil⟩ :
          ((⟨e, ρ, ⟨κ, p, ℓ, lc, sp⟩, M⟩ : CoreRt), σ₁) -<obs>->
            ((⟨re, rρ, ⟨κ, p, ℓ, rlc, rsp⟩, M⟩ : CoreRt), σ₂, eₜ)) Hcred
        with ⟨HSI, Hwps⟩
      imodintro
      isplitl [HSI]
      · subst hnil
        simp only [List.length_nil, Nat.add_zero]
        iexact HSI
      isplitr []
      · iapply IH $$ %p %Ls %Ψ %κ %ℓ %rlc %rsp %re %rρ %Φ HB Hwps
          %(Nat.le_trans hsb hs.sup_sym_le)
        iintro %ℓ' %lc' %sp' %w %ρ' %hst' %hsb' HΨ
        iapply HK $$ %ℓ' %lc' %sp' %w %ρ' %(hst.trans hst') %hsb' HΨ
      · subst hnil
        simp only [Algebra.BigOpL.bigOpL_nil]
        itrivial

/-- THE COLLAPSE AT THE ENTRY CONTROL (the pre-C3 statement, with the
    table and the procedure specifications threaded): under the
    procedure specifications and the block specifications of the current
    procedure, at an EMPTY call stack the statement WP entails the base
    Iris WP with the value-channel postcondition at the ERASED value —
    `wps_sound_cps` with `K := wp_value` (a value at `κ = []` is a
    Language value). At `Θ := emptyProcSpec` (`wps_sound_empty`) this is
    textually the pre-C3 theorem. -/
theorem wps_sound {Ψ : SpikeVal → EnvStack → IProp GF} {ctl : Ctl} (hκ : ctl.κ = [])
    (hsb : M.runState.sym_supply ≤ ctl.sup.sym)
    (e : CoreExpr) (ρ : EnvStack) :
    iprop(procSpecs M Θ ∗ blockSpecs M ctl.proc Ls Θ Ψ) ⊢
      iprop(wps M ctl.proc Ls Θ Ψ e ρ -∗
        WP (⟨e, ρ, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, Ψ w.sv w.ρ }}) := by
  obtain ⟨κ, p, ℓ, lc, sp⟩ := ctl
  simp only at hκ hsb
  subst hκ
  dsimp only
  iintro ⟨#HP, #HB⟩ Hwps
  iapply wps_sound_cps p Ls [] ℓ lc sp e ρ _ $$ HP HB Hwps %hsb
  iintro %ℓ' %lc' %sp' %w %ρ' %_ %_ HΨ
  iapply (wp_value (e := (⟨ofValA w, ρ', ⟨[], p, ℓ', lc', sp'⟩, M⟩ : CoreRt))
    (v := (⟨w, ρ', p, ℓ', M, lc', sp'⟩ : CoreRVal)) ⟨rfl⟩)
  dsimp only [CoreRVal.sv]
  iexact HΨ

/-- The collapse at the EMPTY table: no procedure specifications are
    needed (`procSpecs_empty`) — every pre-C3 client's statement,
    verbatim. -/
theorem wps_sound_empty {Ψ : SpikeVal → EnvStack → IProp GF} {ctl : Ctl} (hκ : ctl.κ = [])
    (hsb : M.runState.sym_supply ≤ ctl.sup.sym)
    (e : CoreExpr) (ρ : EnvStack) :
    blockSpecs M ctl.proc Ls emptyProcSpec Ψ ⊢
      iprop(wps M ctl.proc Ls emptyProcSpec Ψ e ρ -∗
        WP (⟨e, ρ, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, Ψ w.sv w.ρ }}) := by
  iintro #HB
  iapply wps_sound hκ hsb e ρ
  isplit
  · iapply procSpecs_empty
  · iexact HB

/-- THE WHOLE-LOOP FRAME RULE (derived): under the procedure and block
    specifications at `Ls`, a statement WP FRAMED by `R` collapses to the
    base WP with `R` in the postcondition — `R` crosses every back edge
    and every call (the labels are framed by `blockSpecs_frame`, the
    judgment by `wps_frame_labels` — whose call case carries `R` into the
    caller's continuation — and `wps_sound` runs at the framed
    context). -/
theorem wps_sound_frame {Ψ : SpikeVal → EnvStack → IProp GF} {ctl : Ctl} (hκ : ctl.κ = [])
    (hsb : M.runState.sym_supply ≤ ctl.sup.sym)
    (R : IProp GF) (e : CoreExpr) (ρ : EnvStack) :
    iprop(procSpecs M Θ ∗ blockSpecs M ctl.proc Ls Θ Ψ) ⊢
      iprop(wps M ctl.proc Ls Θ Ψ e ρ ∗ R -∗
        WP (⟨e, ρ, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, Ψ w.sv w.ρ ∗ R }}) := by
  iintro ⟨#HP, #HB⟩ ⟨H, HR⟩
  ihave HW := wps_frame_labels R e ρ $$ H HR
  ihave HB' := blockSpecs_frame R $$ HB
  iapply wps_sound hκ hsb e ρ $$ [$HP $HB'] HW

/-- The whole-loop frame rule at the EMPTY table (the pre-C3 statement). -/
theorem wps_sound_frame_empty {Ψ : SpikeVal → EnvStack → IProp GF} {ctl : Ctl}
    (hκ : ctl.κ = []) (hsb : M.runState.sym_supply ≤ ctl.sup.sym)
    (R : IProp GF) (e : CoreExpr) (ρ : EnvStack) :
    blockSpecs M ctl.proc Ls emptyProcSpec Ψ ⊢
      iprop(wps M ctl.proc Ls emptyProcSpec Ψ e ρ ∗ R -∗
        WP (⟨e, ρ, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, Ψ w.sv w.ρ ∗ R }}) := by
  iintro #HB
  iapply wps_sound_frame hκ hsb R e ρ
  isplit
  · iapply procSpecs_empty
  · iexact HB

/-! ## E5 (slice 2): the negative-action protocol's rule faces
(dialect arc E5, docs/2026-09-05_e5-notes.md — the `case` EVAL round, the
excluded store's two rounds, the negative-action round at the `bound`, the
`bound` through a weak tuple binder's head, and the derived ASSIGNMENT rule) -/

/-- E5: THE `case` EVAL ROUND at a NON-value scrutinee (`Step.case_eval` —
    one_step0's Ecase `Nothing` arm, core_reduction.lem:323–339): the
    scrutinee evaluates through the certified evaluator and the node is
    rebuilt at the value; the next round is `wps_case_value`. The corpus's
    `case a_510 of …` / `case (a_518, a_519) of …` at symbol scrutinees. -/

theorem wps_case_eval {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (pe : generic_pexpr Unit sym) (pats : List (pattern × CoreExpr)) (ρ : EnvStack)
    {cval : value} (hnv : valueFromPexpr pe = none)
    (hv : evalPexpr M.tagDefs M.extern M.file ρ pe = some cval) :
    wps M p Ls Θ Ψ (Expr a (Ecase (Pexpr [] () (PEval cval)) pats)) ρ ⊢
      wps M p Ls Θ Ψ (Expr a (Ecase pe pats)) ρ := by
  rw [(wps_unfold (e := Expr a (Ecase pe pats))).to_eq]
  simp only [wps.pre, show toVal (Expr a (Ecase pe pats)) = none from rfl,
    show jumpRedex? (Expr a (Ecase pe pats)) = none from rfl,
    show callRedex? (Expr a (Ecase pe pats)) = none from rfl]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.case_eval hnv hv, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨cval', hv', hout⟩ := hs.case_op_inv hnv
  obtain rfl : cval = cval' := Option.some.inj (hv.symm.trans hv')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- `excludedStoreExpr` (Rules.lean) IS the completeness side's redex
    spelling at the non-locking store. -/
theorem excludedStoreExpr_eq (a : List annot) (n : Nat) (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (ty : ctype) (pv : CerbMem.PointerValue) (cv : value)
    (mo : memory_order) :
    excludedStoreExpr a n loc ann ty pv cv mo = excludedStoreRedex a n loc ann false ty pv cv mo := rfl

/-- E5: ACTION_EVAL for the EXCLUDED store at operands not all values
    (`Step.excluded_store_eval`; step_action's Store0 `_, _, _` arm under
    `process_action (Just n)`, core_reduction.lem:721–727) — the node is
    rebuilt at the evaluated operands; `wps_store_eval`'s twin. -/
theorem wps_excluded_store_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (n : Nat) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 pe3 : generic_pexpr Unit sym) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue} {cv : value}
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hv2 : evalPexpr M.tagDefs M.extern M.file ρ pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr M.tagDefs M.extern M.file ρ pe3 = some cv) :
    wps M p Ls Θ Ψ (excludedStoreExpr a n loc ann ty pv cv mo) ρ ⊢
      wps M p Ls Θ Ψ (excludedStoreOpRedex a n loc ann ty pe2 pe3 mo) ρ := by
  rw [(wps_unfold (e := excludedStoreOpRedex a n loc ann ty pe2 pe3 mo)).to_eq]
  simp only [wps.pre, excludedStoreOpRedex, excludedStoreExpr,
    show ∀ (b : List annot) (act : CoreAction), toVal (Expr b (Eexcluded n act)) = none from
      fun _ _ => rfl,
    jumpRedex?_excluded, callRedex?_excluded]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [],
      ⟨Step.excluded_store_eval hnv hv2 hv3, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨pv', cv', hv2', hv3', hout⟩ := hs.excluded_store_op_inv hnv
  obtain rfl : pv = pv' := by
    simpa using Option.some.inj (hv2.symm.trans hv2')
  obtain rfl : cv = cv' := Option.some.inj (hv3.symm.trans hv3')
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  simp only [Prod.mk.injEq] at hout
  obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
  subst hrctl
  subst hre
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-- E5: THE EXCLUDED STORE small axiom over `wps` (`excluded_store_atomic`
    lifted; `wps_store`'s twin) — the postcondition's value is the NEGATIVE
    annotated unit `{DA_neg n [] fp} Unit`. -/
theorem wps_excluded_store {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (n : Nat) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_neg n [] fp] Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (excludedStoreExpr a n loc ann ty pv cv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => excluded_store_atomic a n loc ann ty pv cv mo mv bs ρ hmv hst)
    rfl rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%fp, %hw, Hpt'⟩
    subst hw
    iapply HΨ $$ Hpt'

/-- E5: THE NEGATIVE-ACTION ROUND at the `bound` (`Step.neg_bound`; step_ctx's
    `Eaction (Paction Neg act)` arm at `BOUND_NO_SSEQ`, core_reduction.lem:
    1290–1309): the body `b` holds a negative action at the spine hole
    (`negRedex? b`, its inner context `ctxA` with no strong sequence), and the
    frame REWRITES it to `negRewrite n s ctxA act` at the exclusion id `n`
    and the fresh binder `s = fresh_given_int k` drawn from the run supplies.
    The client's continuation is quantified over BOTH draws; about the
    symbol draw it learns exactly the judgments' supply bound — `k` is at or
    above the floor `M.runState.sym_supply` (`wps.pre`'s step clause). -/
theorem wps_neg_round {Ψ : SpikeVal → EnvStack → IProp GF} (an : List annot) (b : CoreExpr)
    (ρ : EnvStack) {ctxA : context} {a : List annot} {act : CoreAction}
    (hn : negRedex? b = some (ctxA, a, act)) (hss : break_at_sseq ctxA = none) :
    iprop(∀ (n k : Nat), ⌜M.runState.sym_supply ≤ k⌝ -∗
      wps M p Ls Θ Ψ (Expr an (Ebound (negRewrite n (fresh_given_int k) ctxA act))) ρ) ⊢
      wps M p Ls Θ Ψ (Expr an (Ebound b)) ρ := by
  have htv : toVal b = none := toVal_none_of_negRedex?_some hn
  have hjr : jumpRedex? b = none := jumpRedex?_none_of_negRedex?_some hn
  have hcr : callRedex? b = none := callRedex?_none_of_negRedex?_some hn
  rw [(wps_unfold (e := Expr an (Ebound b))).to_eq]
  simp only [wps.pre, toVal_bound_node, jumpRedex?_bound, hjr, callRedex?_bound, hcr,
    Option.map_none]
  iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.neg_bound hn hss, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  rcases hs.bound_inv with ⟨_, _, _, _, _, _, hnn, _, _, _⟩ |
      ⟨a1, b1, v, hb, _⟩ | ⟨a1, a2, b1, ds, v, hb, _⟩ |
      ⟨_, _, _, _, _, _, _, hj, _, _, _, _⟩ | hcall | ⟨ctxA', a', act', hn', hss', hout⟩
  · rw [hn] at hnn; cases hnn
  · rw [hb, toVal_ofValA] at htv; cases htv
  · rw [hb, toVal_ofValA] at htv; cases htv
  · rw [hjr] at hj; cases hj
  · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
    rw [hcr] at h; cases h
  · rw [hn] at hn'
    obtain ⟨rfl, rfl, rfl⟩ : ctxA = ctxA' ∧ a = a' ∧ act = act' := by simpa using hn'
    obtain ⟨re, rρ, rctl, rM⟩ := r
    simp only at hlbl
    obtain rfl : M = rM := hlbl.symm
    simp only [Prod.mk.injEq] at hout
    obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
    subst hrctl hre
    obtain rfl : ρ = rρ := hrρ.symm
    obtain rfl : σ₁ = σ₂ := hσ.symm
    imod Hclose with -
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iapply H $$ %(sp.excl) %(sp.sym) %hsb

/-- E5 (slice 2, proof device): `wps_bound_wseq_tuple` with its two static
    premises inside the entailment — the Löb induction runs over the HEAD
    `e1` of the weak tuple binder under the `bound`, so the premises must
    be re-established at every successor (`Step.negFree_preserved`,
    `Step.pot_le`). -/
theorem wps_bound_wseq_tuple_aux {Ψ : SpikeVal → EnvStack → IProp GF} (an a pa : List annot)
    (ls : List TupleLeaf) (e1 e2 : CoreExpr) (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    iprop(⌜negFree e1 = true ∧ pot e1 ≤ lemDefaultFuel⌝ ∗
      wps M p Ls Θ (fun w ρ' => iprop(∃ (vs : List value) (ds : List dyn_annotation),
        ⌜w = SpikeVal.annot ds (Vtuple vs)⌝ ∗
        wps M p Ls Θ Ψ (Expr an (Ebound (Expr [] (Eannot ds e2))))
          (update_env (tuplePat pa ls) (Vtuple vs) ρ'))) e1 (ev0 :: evs)) ⊢
      wps M p Ls Θ Ψ (Expr an (Ebound (Expr a (Ewseq (tuplePat pa ls) e1 e2)))) (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr an (Ebound (Expr a (Ewseq (tuplePat pa ls) (ofValA wa) e2))))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_bound_node, jumpRedex?_bound, jumpRedex?_wseq,
      jumpRedex?_ofValA, callRedex?_bound, callRedex?_wseq, callRedex?_ofValA, Option.map_none]
    iintro ⟨-, H⟩ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with ⟨%vs, %ds, %hval, Hinner⟩
    obtain ⟨a1, a2, b1, rfl⟩ : ∃ a1 a2 b1, wa = .annot a1 a2 b1 ds (Vtuple vs) := by
      cases wa with
      | pure a1 b1 v' => cases hval
      | annot a1 a2 b1 ds' v' => cases hval; exact ⟨a1, a2, b1, rfl⟩
    have hjr' : jumpRedex? (Expr a (Ewseq (tuplePat pa ls)
        (ofValA (.annot a1 a2 b1 ds (Vtuple vs))) e2)) = none := by
      rw [jumpRedex?_wseq, jumpRedex?_ofValA]
    have hcr' : callRedex? (Expr a (Ewseq (tuplePat pa ls)
        (ofValA (.annot a1 a2 b1 ds (Vtuple vs))) e2)) = none := by
      rw [callRedex?_wseq, callRedex?_ofValA]; rfl
    have hnn' : negRedex? (Expr a (Ewseq (tuplePat pa ls)
        (ofValA (.annot a1 a2 b1 ds (Vtuple vs))) e2)) = none := by
      rw [negRedex?_wseq, negRedex?_ofValA]; rfl
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨_, _, _, _⟩, _, [],
        ⟨Step.bound_ctx hjr' hcr' hnn' rfl Step.wseq_tuple_annot, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.bound_inv with ⟨b', ρ'', ctl'', σ'', -, -, -, -, hs', hout⟩ |
        ⟨_, _, _, hb, _⟩ | ⟨_, _, _, _, _, hb, _⟩ |
        ⟨_, _, _, _, _, _, _, hj, _, _, _, _⟩ | hcall | ⟨_, _, _, hn, _, _⟩
    · rcases hs'.wseq_inv with ⟨e1', _, _, _, _, _, hnv', _, _⟩ |
          ⟨_, _, _, _, v', _, _, hpat, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs0, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpat, he1, _, _⟩ |
          ⟨pa', ls', a1', a2', b1', ds', vs', _, _, hpat, he1, _, hout'⟩ |
          hcall'
      · rw [toVal_ofValA] at hnv'; cases hnv'
      · exact (tuplePat_ne_base hpat.symm).elim
      · exact (tuplePat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofValA] at hj; cases hj
      · exact (symPat_ne_tuple hpat.symm).elim
      · exact (symPat_ne_tuple hpat.symm).elim
      · exact absurd (ofValA_inj he1) (by simp)
      · obtain ⟨rfl, rfl⟩ := tuplePat_inj hpat
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ vs = vs' := by
          simpa using ofValA_inj he1
        simp only [Prod.mk.injEq] at hout'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hout'
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl hrρ hre
        subst hσ
        imod Hclose with -
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · iexact Hinner
      · obtain ⟨_, _, _, h⟩ := hcall'.callRedex?_some
        rw [callRedex?_ofValA] at h; cases h
    · have htv' := toVal_wseq_node a (tuplePat pa ls) (ofValA (.annot a1 a2 b1 ds (Vtuple vs))) e2
      rw [hb, toVal_ofValA] at htv'; cases htv'
    · have htv' := toVal_wseq_node a (tuplePat pa ls) (ofValA (.annot a1 a2 b1 ds (Vtuple vs))) e2
      rw [hb, toVal_ofValA] at htv'; cases htv'
    · rw [hjr'] at hj; cases hj
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      rw [hcr'] at h; cases h
    · rw [hnn'] at hn; cases hn
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr an (Ebound (Expr a (Ewseq (tuplePat pa ls) e1 e2))))).to_eq]
      simp only [wps.pre, htv, toVal_bound_node, jumpRedex?_bound, jumpRedex?_wseq, hjr]
      iintro ⟨-, H⟩
      iexact H
    | none =>
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr an (Ebound (Expr a (Ewseq (tuplePat pa ls) e1 e2))))).to_eq]
        simp only [wps.pre, htv, toVal_bound_node, jumpRedex?_bound, jumpRedex?_wseq, hjr,
          callRedex?_bound, callRedex?_wseq, hcr, Option.map_some, apply_ctx_bound, apply_ctx_wseq]
        iintro ⟨%hst, H⟩
        obtain ⟨hnf, hpot⟩ := hst
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        obtain ⟨an', ra, hb⟩ := callRedex?_apply_ctx_eq hcr
        have hnf' : negFree (apply_ctx ctx (ofValA (.pure a1 [] ret))) = true := by
          rw [hb] at hnf; exact negFree_apply_ctx_of hnf (negFree_ofValA _)
        have hpot' : pot (apply_ctx ctx (ofValA (.pure a1 [] ret))) ≤ lemDefaultFuel := by
          have hplug := pot_apply_ctx_plug ctx (Expr an' (Eproc ra (Sym f) pes))
            (ofValA (.pure a1 [] ret))
          rw [← hb] at hplug
          rw [show pot (Expr an' (Eproc ra (Sym f) pes)) = 2 from rfl, pot_ofValA_pure] at hplug
          omega
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs
        isplitr
        · ipureintro
          exact ⟨hnf', hpot'⟩
        · iexact H'
      | none =>
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr an (Ebound (Expr a (Ewseq (tuplePat pa ls) e1 e2))))).to_eq]
        simp only [wps.pre, htv, toVal_bound_node, jumpRedex?_bound, jumpRedex?_wseq, hjr,
          callRedex?_bound, callRedex?_wseq, hcr, Option.map_none]
        iintro ⟨%hst, H⟩ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
        obtain ⟨hnf, hpot⟩ := hst
        have hsz : esize e1 ≤ lemDefaultFuel := Nat.le_trans (esize_le_pot e1) hpot
        have hjr' : jumpRedex? (Expr a (Ewseq (tuplePat pa ls) e1 e2)) = none := by
          rw [jumpRedex?_wseq, hjr]
        have hcr' : callRedex? (Expr a (Ewseq (tuplePat pa ls) e1 e2)) = none :=
          callRedex?_wseq_none hcr
        have hnn' : negRedex? (Expr a (Ewseq (tuplePat pa ls) e1 e2)) = none := by
          rw [negRedex?_wseq, negRedex?_none_of_negFree hnf]; rfl
        imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨obs0, ⟨Expr an (Ebound (Expr a (Ewseq (tuplePat pa ls) r'.e e2))), r'.ρ, r'.ctl, M⟩,
            σ', [], ⟨Step.bound_ctx hjr' hcr' hnn' (toVal_wseq_node _ _ _ _)
              (Step.wseq_ctx hjr hcr htv hs'), rfl, rfl⟩⟩
        inext
        iintro %r %σ₂ %eₜ %Hstep Hcred
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.bound_inv with ⟨b', ρ'', ctl'', σ'', -, -, -, -, hs', hout⟩ |
            ⟨_, _, _, hb, _⟩ | ⟨_, _, _, _, _, hb, _⟩ |
            ⟨_, _, _, _, _, _, _, hj, _, _, _, _⟩ | hcall | ⟨_, _, _, hn, _, _⟩
        · rcases hs'.wseq_inv with ⟨e1', ρ3, ctl3, σ3, hnj, hnc', hnv', hs'', hout'⟩ |
              ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
              ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
              ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
              ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
              ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
              ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
              ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
              hcall'
          · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'' (Step.ctl_eq hs'' hnc' hnv').1
            simp only [Prod.mk.injEq] at hout'
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hout'
            obtain ⟨re, rρ, rctl, rM⟩ := r
            simp only at hlbl
            obtain rfl : M = rM := hlbl.symm
            simp only [Prod.mk.injEq] at hout
            obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
            subst hrctl hre hrρ hσ
            imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
              %([] : List CoreRt) %⟨hs'', rfl, rfl⟩ Hcred with ⟨$, H⟩
            imodintro
            iapply IH $$ %e1' %ev0' %evs
            isplitr
            · ipureintro
              exact ⟨Step.negFree_preserved hs'' hsz hjr hcr htv hnf,
                Nat.le_trans (Step.pot_le hs'' hsz hjr hcr htv hnf) hpot⟩
            · iexact H
          · rw [he1, toVal_ofValA] at htv; cases htv
          · rw [he1, toVal_ofValA] at htv; cases htv
          · rw [hjr] at hj; cases hj
          · rw [he1, toVal_ofValA] at htv; cases htv
          · rw [he1, toVal_ofValA] at htv; cases htv
          · rw [he1, toVal_ofValA] at htv; cases htv
          · rw [he1, toVal_ofValA] at htv; cases htv
          · obtain ⟨_, _, _, h⟩ := hcall'.callRedex?_some
            rw [hcr] at h; cases h
        · have htv' := toVal_wseq_node a (tuplePat pa ls) e1 e2
          rw [hb, toVal_ofValA] at htv'; cases htv'
        · have htv' := toVal_wseq_node a (tuplePat pa ls) e1 e2
          rw [hb, toVal_ofValA] at htv'; cases htv'
        · rw [hjr'] at hj; cases hj
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [hcr'] at h; cases h
        · rw [hnn'] at hn; cases hn

/-- E5 (slice 2): `bound` THROUGH THE HEAD of a weak flat-tuple binder — the
    emitted assignment statement's opening rounds, `bound(let weak (p, v) =
    E in K)`: while the head `E` reduces (negative-free, within the fuel) the
    `bound` frame is a congruence (`Step.bound_ctx` ∘ `Step.wseq_ctx`); at the
    head's annotated tuple the binder fires under the frame
    (`Step.wseq_tuple_annot`), delivering `bound({A} K)` at the extended
    environment — whatever `K` is: the tail `K` may contain the negative
    action `wps_bound` cannot admit (its round is the frame's own,
    `wps_neg_round`). -/
theorem wps_bound_wseq_tuple {Ψ : SpikeVal → EnvStack → IProp GF} (an a pa : List annot)
    (ls : List TupleLeaf) (e1 e2 : CoreExpr) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hnf : negFree e1 = true) (hpot : pot e1 ≤ lemDefaultFuel) :
    wps M p Ls Θ (fun w ρ' => iprop(∃ (vs : List value) (ds : List dyn_annotation),
        ⌜w = SpikeVal.annot ds (Vtuple vs)⌝ ∗
        wps M p Ls Θ Ψ (Expr an (Ebound (Expr [] (Eannot ds e2))))
          (update_env (tuplePat pa ls) (Vtuple vs) ρ'))) e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr an (Ebound (Expr a (Ewseq (tuplePat pa ls) e1 e2)))) (ev0 :: evs) := by
  iintro H
  iapply wps_bound_wseq_tuple_aux an a pa ls e1 e2 ev0 evs
  isplitr
  · ipureintro
    exact ⟨hnf, hpot⟩
  · iexact H

/-! ## E5 (slice 2): THE ASSIGNMENT STATEMENT — the negative-action protocol
as ONE derived rule -/

/-- The body of the emitted assignment statement AFTER its opening tuple
    binder: `{A}(let weak _: unit = neg(store(ty, pe2, pe3)) in pure(per))` —
    the shape `wps_bound_wseq_tuple` delivers under the `bound` once
    `let weak (p, v) = unseq(…)` has bound the operands (every corpus
    assignment, E0 §B.9; `ds` = the tuple's dynamic annotations, `[]` when the
    operands were pure). -/
def negAssignBody (a0 a1 a2 a3 pa : List annot) (ds : List dyn_annotation)
    (bty : core_base_type) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 pe3 per : generic_pexpr Unit sym) (mo : memory_order) : CoreExpr :=
  Expr a0 (Eannot ds (Expr a1 (Ewseq (Pattern pa (CaseBase (none, bty)))
    (Expr a2 (Eaction (Paction polarity.Neg0 (Action loc ann
      (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))))
    (Expr a3 (Epure per)))))

/-- The negative-action spine search at the assignment body: the redex is
    the negative store, its inner context the annotation frame over the
    wildcard weak binder (`Cannot a0 ds (Cwseq a1 _ CTX (pure per))`) — no
    strong sequence, no nested `bound`: the engine's `BOUND_NO_SSEQ` arm. -/
theorem negRedex?_negAssignBody (a0 a1 a2 a3 pa : List annot) (ds : List dyn_annotation)
    (bty : core_base_type) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 pe3 per : generic_pexpr Unit sym) (mo : memory_order) :
    negRedex? (negAssignBody a0 a1 a2 a3 pa ds bty loc ann ty pe2 pe3 per mo) =
      some (Cannot a0 ds (Cwseq a1 (Pattern pa (CaseBase (none, bty))) CTX (Expr a3 (Epure per))),
        a2, Action loc ann (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)) := rfl

theorem break_at_sseq_negAssign (a0 a1 pa : List annot) (ds : List dyn_annotation)
    (bty : core_base_type) (e2 : CoreExpr) :
    break_at_sseq (Cannot a0 ds (Cwseq a1 (Pattern pa (CaseBase (none, bty))) CTX e2)) = none := rfl

/-- THE ASSIGNMENT RULE (E5): the emitted `x = E;` statement's tail, from the
    negative store to the delivered value, as ONE rule — Reynolds/O'Hearn's
    assignment axiom `{p ↦ -} p := v {p ↦ v}` at the dialect's statement
    shape. The engine's protocol behind it (nine rounds, each a mirrored
    rule of this module): the negative-action round at the `bound`
    (`wps_neg_round`: the exclusion id and the fresh binder `s` drawn from
    the run supplies), the rewritten body under the frame (`wps_bound`), the
    `(_, s)` tuple binder over the `unseq` (`wps_wseq_tuple_annot`), the
    unseq's last reducible component first (`wps_unseq_focus`: the annotated
    wildcard binder over `pure(Unit)` and the pure tail `per`, `wps_annot`/
    `wps_wseq`/`wps_pure`), then the excluded store's two rounds
    (`wps_excluded_store_eval`, `wps_excluded_store` — THE POINTS-TO IS
    CONSUMED HERE), the unseq's completion into the negative-annotated tuple
    (`wps_unseq_vals`: race-free by the exclusion id, `do_race_addExcl_neg`),
    the binder `s ↦ per`'s value, the read `pure(s)` and REMOVE-BOUND.

    What the CLIENT sees: the cell's points-to before, the cell's points-to
    at the stored bytes after, the delivered value `per`'s (the statement's
    own value, `conv_loaded_int(ty, v)`), and the environment extended by
    the FRESH binder `s ↦ per` — `s = fresh_given_int k` at a supply `k` AT
    OR ABOVE THE FLOOR `M.runState.sym_supply` (the judgments' supply bound,
    `wps.pre`), so a client whose program symbols all lie below the floor
    knows `s` collides with none of them (`symOrd_ne_eq_of_num_ne`). The
    exclusion id and the footprint never reach the client. -/
theorem wps_neg_bound {Ψ : SpikeVal → EnvStack → IProp GF}
    (an a0 a1 a2 a3 pa : List annot) (ds : List dyn_annotation) (bty : core_base_type)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 pe3 per : generic_pexpr Unit sym) (mo : memory_order)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (hf : SymFrame ev0)
    {pv : CerbMem.PointerValue} {cv vr : value} (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte)
    (hex : ∀ x, resolveExtern M.extern x = x)
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hv2 : evalPexpr M.tagDefs M.extern M.file (ev0 :: evs) pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr M.tagDefs M.extern M.file (ev0 :: evs) pe3 = some cv)
    (hnvr : valueFromPexpr per = none)
    (hvr : evalPexpr M.tagDefs M.extern M.file (ev0 :: evs) per = some vr)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (∀ (s : sym), ⌜∃ k, s = fresh_given_int k ∧ M.runState.sym_supply ≤ k⌝ -∗
        pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.pure vr) (envAdd s vr ev0 :: evs))) ⊢
      wps M p Ls Θ Ψ (Expr an (Ebound (negAssignBody a0 a1 a2 a3 pa ds bty loc ann ty pe2 pe3 per mo)))
        (ev0 :: evs) := by
  iintro ⟨Hpt, HΨ⟩
  -- 1. the negative-action round at the `bound`
  iapply wps_neg_round an _ _ (negRedex?_negAssignBody a0 a1 a2 a3 pa ds bty loc ann ty pe2 pe3 per mo)
    (break_at_sseq_negAssign a0 a1 pa ds bty (Expr a3 (Epure per)))
  iintro %n %k %hk
  rw [negRewrite_eq]
  simp only [add_exclusion_annot, add_exclusion_wseq, add_exclusion_CTX, apply_ctx_annot,
    apply_ctx_wseq, apply_ctx_CTX]
  -- 2. the rewritten body is negative-free and within the fuel: `bound` is a congruence
  iapply wps_bound an _ _ rfl (by
    simp only [pot_wseq, pot_unseq, potList_cons, potList_nil, pot_excluded, pot_annot,
      pot_pure_val, pot_pure_sym]
    have := pot_pure_le_two (a := a3) per
    rw [show lemDefaultFuel = 999999 + 1 from rfl]
    omega)
  -- 3. the `(_, s)` binder over the unseq
  rw [show (Pattern [] (CaseCtor Ctuple [Pattern [] (CaseBase (none, BTy_unit)),
      Pattern [] (CaseBase (some (fresh_given_int k), BTy_unit))]) : pattern) =
    tuplePat [] [([], none, BTy_unit), ([], some (fresh_given_int k), BTy_unit)] from rfl]
  iapply wps_wseq_tuple_annot [] [] _ _ _ ev0 evs
  -- 4. the unseq: its LAST reducible component first — the annotated wildcard binder
  rw [show ([Expr [] (Eexcluded n (Action loc ann (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo))),
      Expr a0 (Eannot (List.map (addExcl n) ds) (Expr a1 (Ewseq (Pattern pa (CaseBase (none, bty)))
        (Expr [] (Epure (Pexpr [] () (PEval Vunit)))) (Expr a3 (Epure per)))))] : List CoreExpr) =
    [Expr [] (Eexcluded n (Action loc ann (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))] ++
      Expr a0 (Eannot (List.map (addExcl n) ds) (Expr a1 (Ewseq (Pattern pa (CaseBase (none, bty)))
        (Expr [] (Epure (Pexpr [] () (PEval Vunit)))) (Expr a3 (Epure per))))) :: [] from rfl]
  iapply wps_unseq_focus [] _ _ [] (ev0 :: evs) rfl rfl
  iapply wps_annot
  iapply wps_wseq a1 pa bty _ _ ev0 evs
  rw [show (Expr [] (Epure (Pexpr [] () (PEval Vunit))) : CoreExpr) = ofValA (.pure [] [] Vunit) from rfl]
  iapply wps_ofValA (.pure [] [] Vunit) (ev0 :: evs)
  simp only [SpikeValA.erase_pure]
  iapply wps_pure per (ev0 :: evs) hnvr hvr
  simp only [SpikeVal.mergeInto, SpikeVal.merge]
  iintro %wa %hwa
  obtain ⟨wa1, wa2, wb, rfl⟩ : ∃ a1' a2' b1', wa = .annot a1' a2' b1' (List.map (addExcl n) ds) vr := by
    cases wa with
    | pure _ _ _ => cases hwa
    | annot _ _ _ _ _ => cases hwa; exact ⟨_, _, _, rfl⟩
  -- 5. the excluded store: the remaining reducible component
  rw [show ([Expr [] (Eexcluded n (Action loc ann (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo)))] ++
      ofValA (.annot wa1 wa2 wb (List.map (addExcl n) ds) vr) :: [] : List CoreExpr) =
    [] ++ Expr [] (Eexcluded n (Action loc ann (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo))) ::
      [ofValA (.annot wa1 wa2 wb (List.map (addExcl n) ds) vr)] from rfl]
  iapply wps_unseq_focus [] [] _ [ofValA (.annot wa1 wa2 wb (List.map (addExcl n) ds) vr)] (ev0 :: evs)
    (by rw [valsOnly_cons, valsOnly_nil, isValE_ofValA])
    (by rw [List.nil_append, ccallFreeList, ccallFree_ofValA]; rfl)
  rw [show (Expr [] (Eexcluded n (Action loc ann (Store0 false (Pexpr [] () (PEval (Vctype ty))) pe2 pe3 mo))) : CoreExpr) =
    excludedStoreOpRedex [] n loc ann ty pe2 pe3 mo from rfl]
  iapply wps_excluded_store_eval [] n loc ann ty pe2 pe3 mo (ev0 :: evs) hnv hv2 hv3
  iapply wps_excluded_store [] n loc ann ty pv cv mo mv bs (ev0 :: evs) hmv hst
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt' %wa' %hwa'
  obtain ⟨c1, c2, c3, rfl⟩ : ∃ c1 c2 c3, wa' = .annot c1 c2 c3 [DA_neg n [] fp] Vunit := by
    cases wa' with
    | pure _ _ _ => cases hwa'
    | annot _ _ _ _ _ => cases hwa'; exact ⟨_, _, _, rfl⟩
  -- 6. the unseq completes into the negative-annotated tuple: no race (the exclusion id)
  rw [show ([] ++ ofValA (.annot c1 c2 c3 [DA_neg n [] fp] Vunit) ::
      [ofValA (.annot wa1 wa2 wb (List.map (addExcl n) ds) vr)] : List CoreExpr) =
    [SpikeValA.annot c1 c2 c3 [DA_neg n [] fp] Vunit,
      SpikeValA.annot wa1 wa2 wb (List.map (addExcl n) ds) vr].map ofValA from rfl]
  iapply wps_unseq_vals [] _ (ev0 :: evs)
    (fps := List.map (addExcl n) ds ++ [DA_neg n [] fp]) (cvals := [Vunit, vr])
    (by simp only [collectUnseq, do_race_nil_right, do_race_addExcl_neg, combine_dyn_annotations,
      Bool.false_eq_true, if_false, List.append_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append])
  -- 7. the binder `(_, s) ↦ (Unit, vr)`, the read `pure(s)`, REMOVE-BOUND
  iexists [Vunit, vr], (List.map (addExcl n) ds ++ [DA_neg n [] fp])
  isplit
  · ipureintro; rfl
  rw [update_env_tuple_wild_sym]
  iapply wps_annot
  iapply wps_pure (Pexpr [] () (PEsym (fresh_given_int k))) _ rfl (by
    rw [evalPexpr_sym_of_resolve _ _ _ (hex _)]
    exact lookup_env_head (by rw [envAdd_lookup hf symCmpK, if_pos (symOrd_self _)]) evs)
  simp only [SpikeVal.merge, SpikeVal.val]
  iapply HΨ $$ %(fresh_given_int k) %⟨k, rfl, hk⟩ Hpt'

/-- Strong symbol binding when the head delivers an annotated value.
    Bind the underlying value and retain its dynamic annotations around
    the continuation, exactly as the engine's LETS-ANNOT step does. -/
theorem wps_seq_sym_annot {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    wps M p Ls Θ (fun w ρ' => iprop(∃ (v : value) (ds : List dyn_annotation),
        ⌜w = SpikeVal.annot ds v⌝ ∗
        wps M p Ls Θ Ψ (Expr [] (Eannot ds e2)) (update_env (symPat pa x bty) v ρ')))
      e1 (ev0 :: evs) ⊢
      wps M p Ls Θ Ψ (Expr a (Esseq (symPat pa x bty) e1 e2))
        (ev0 :: evs) := by
  iloeb as IH generalizing %e1 %ev0 %evs
  cases htv : toVal e1 with
  | some w =>
    obtain ⟨wa, rfl, rfl⟩ := ofValA_of_toVal htv
    rw [wps_unfold.to_eq,
      (wps_unfold (e := Expr a (Esseq (symPat pa x bty)
        (ofValA wa) e2))).to_eq]
    simp only [wps.pre, toVal_ofValA, toVal_sseq_node, jumpRedex?_sseq,
      jumpRedex?_ofValA, callRedex?_sseq, callRedex?_ofValA, Option.map_none]
    iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
    imod H with ⟨%v, %ds, %hval, Hinner⟩
    obtain ⟨a1, a2, b1, rfl⟩ : ∃ a1 a2 b1, wa = .annot a1 a2 b1 ds v := by
      cases wa with
      | pure a1 b1 v' => cases hval
      | annot a1 a2 b1 ds' v' => cases hval; exact ⟨a1, a2, b1, rfl⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_sym_annot, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hlbl, rfl⟩ := Hstep
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
        ⟨_, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, v', _, _, hpat, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨pa', x', bty', a1', b1', v', _, _, hpat, he1, _, hout⟩ |
        ⟨pa', x', bty', a1', a2', b1', ds', v', _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · rw [toVal_ofValA] at hnv'; cases hnv'
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · rw [jumpRedex?_ofValA] at hj; cases hj
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · exact absurd (ofValA_inj he1) (by simp)
    · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ : a1 = a1' ∧ a2 = a2' ∧ b1 = b1' ∧ ds = ds' ∧ v = v' := by
        simpa using ofValA_inj he1
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      simp only [Prod.mk.injEq] at hout
      obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
      subst hrctl
      subst hrρ
      obtain rfl : Expr [] (Eannot ds e2) = re := hre.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iexact Hinner
    · exact (symPat_ne_tuple hpatT1).elim
    · exact (symPat_ne_tuple hpatT2).elim
    · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
      rw [callRedex?_ofValA] at h
      cases h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (symPat pa x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr]
      iintro H
      iexact H
    | none =>
      cases hcr : callRedex? e1 with
      | some q =>
        obtain ⟨ctx, f, pes⟩ := q
        rw [wps_unfold.to_eq,
          (wps_unfold (e := Expr a (Esseq (symPat pa x bty) e1 e2))).to_eq]
        simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr,
          Option.map_some, apply_ctx_sseq]
        iintro H
        imod H with ⟨%params, %body, %vs, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        inext
        iintro %ret %a1 Hpost
        ihave H' := Hcont $$ %ret %a1 Hpost
        iapply IH $$ %(apply_ctx ctx (ofValA (.pure a1 [] ret))) %ev0 %evs H'
      | none =>
      rw [wps_unfold.to_eq,
        (wps_unfold (e := Expr a (Esseq (symPat pa x bty) e1 e2))).to_eq]
      simp only [wps.pre, htv, toVal_sseq_node, jumpRedex?_sseq, hjr, callRedex?_sseq, hcr, Option.map_none]
      iintro H %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ
      imod H $$ %κ %ℓ %lc %sp %σ₁ %ns %obs %obs' %nt %hsb Hσ with ⟨%hred, H⟩
      imodintro
      isplit
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hlbl', hnil'⟩ := hps
        exact ⟨obs0, ⟨Expr a (Esseq (symPat pa x bty)
            r'.e e2), r'.ρ, r'.ctl, M⟩, σ', [],
          ⟨Step.sseq_ctx hjr hcr htv hs', rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hs', hout⟩ |
          ⟨_, _, _, _, v, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, ds, v, _, _, _, he1, _, _⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
          hcall
      · obtain ⟨ev0', rfl⟩ := Step.env_cons hs' (Step.ctl_eq hs' hnc' hnv').1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        simp only [Prod.mk.injEq] at hout
        obtain ⟨hre, hrρ, hrctl, hσ⟩ := hout
        subst hrctl
        subst hre hrρ hσ
        imod H $$ %(⟨e1', ev0' :: evs, rctl, M⟩ : CoreRt) %σ₂
          %([] : List CoreRt) %⟨hs', rfl, rfl⟩ Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ev0' %evs H
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [hjr] at hj; cases hj
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · rw [he1, toVal_ofValA] at htv; cases htv
      · exact (symPat_ne_tuple hpatT1).elim
      · exact (symPat_ne_tuple hpatT2).elim
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        rw [hcr] at h; cases h

/-- Whole-cell load retaining the exact read footprint. This strengthens
    `wps_load` for clients that must discharge unsequenced race checks. -/
theorem wps_load_footprint {Ψ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv dq ty bs ∗
      (pointsToCell M.tagDefs pv dq ty bs -∗
        Ψ (.annot [DA_pos [] (loadFootprint M.tagDefs pv ty)]
          (loadedVal M.tagDefs pv ty bs)) ρ)) ⊢
      wps M p Ls Θ Ψ (loadExpr a loc ann ty pv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wps_of_atomic (fun _ _ _ _ => load_atomic a loc ann ty pv mo dq bs ρ htrap) rfl rfl rfl
  isplitl [Hpt]
  · iexact Hpt
  iintro %w ⟨%hw, Hpt⟩
  subst hw
  iapply HΨ $$ Hpt

end CerberusHeapLang
