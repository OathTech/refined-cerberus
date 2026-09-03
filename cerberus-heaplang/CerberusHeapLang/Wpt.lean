/-
CerberusHeapLang.Wpt — the total label-context judgment `wpt`.

THE SHAPE: the total analogue of `wps` (Wps.lean) — the same
label-context statement logic, but TOTAL: `wpt M p Ls Θ k Ψ e ρ` means
"e delivers a value satisfying Ψ within k engine-drive steps
(delivery protocol included), given that every registered label body
meets its own budget (`blockSpecsT`) and every declared procedure body
its table entry at its budget (`procSpecsT`, calls arc C3)". It is
defined WITHOUT a fixpoint, by well-founded recursion on the step
budget `k` (`wpt.pre`: value / jump redex / call redex / step clauses;
the recursive occurrence in the step clause is at `k - 1`, in the call
clause at the continuation's budget `k'` with the split `1 + m + k' ≤ k`
— the call round, the callee's budget `m` (its return included), the
rest of the caller — and the jump clause does not recurse — the body's
obligation lives in `blockSpecsT` at the target's own budget). No Löb
and no ▷: the least-fixpoint discipline of iris-lean's own
`TotalWeakestPre`, realized through the budget's well-foundedness. The
judgment is indexed by the current PROCEDURE `p`, the step clause
quantified over the call stack and execution location, as `wps` is.

THE MANDATORY DECREASE: label preconditions are INDEXED BY A VARIANT
`m : Nat` (`LabelSpecT` — the classical Floyd variant as a
specification parameter, so heap-resident measures such as a chain
length enter through the invariant), and the jump clause REQUIRES
`1 + m ≤ k`: the target label's budget plus the jump step itself must
fit in the remaining budget. Since a body is verified (`blockSpecsT`)
at budget `m` and budgets only shrink along steps, every back edge
strictly decreases a well-founded `Nat` measure. The variant is
simultaneously a step budget, so one derivation yields two results:
- `wpt_sound_cps` collapses the judgment into iris-lean's
  `TotalWeakestPre` (`WP … [{ … }]`), in CPS over the ambient control by
  strong induction on the budget (a back edge lands in the target's
  variant budget, a call lands the callee in `m` and the continuation in
  `k'`, both below `k` by the split; the return is `twp_ret`/
  `twp_ret_annot`) — `wpt_sound`/`wpt_sound_empty` are its entry-control
  faces — a metatheorem (the judgment is a sound total WP) that no
  export consumes;
- `wpt_driver_aux` (ProdLoop.lean) is the simulation into the
  engine: a proved `wpt … k` plus the seeded footprint yields the
  driver-delivery fact `DriverDoneAt` — the SHIPPED driver's per-thread
  loop returns PROGRAM-DONE within `k + 2` iterations — the shipped
  round `loop_step_frag_same` (DriverCollapse.lean) discharging one
  budget unit per iteration. Every total export goes this way; no Iris
  adequacy result is in any total export's cone. It is stated at the EMPTY
  table `emptyProcSpecT` (the call clause unsatisfiable there,
  `wpt_empty_call_false`) and stays there: the total lane THROUGH CALLS
  is the shipped-driver CPS induction `wpt_driver_cps` (ProdLoop.lean,
  calls arc C4 — the driver-level twin of `wpt_sound_cps`), the route of
  the recursive-fib production statement.
Deleting the decrease premise makes both inductions fail to elaborate
(they are ON the budget) and would make the self-jump loop derivable;
`diverge_total_unprovable` (DivergeExhibit.lean) records, at the
engine, that a total derivation for that loop is `False`.

BUDGET ACCOUNTING (uniform): a rule's budget = its own engine steps
plus the DELIVERY COST of its final value (`deliveryCost`, Rules.lean:
1 for a bare pure value — PROGRAM-DONE; 2 for an annotated value —
the REMOVE-ANNOT tau then PROGRAM-DONE). Sequencing composes budgets
additively (`k1 + k2`): the bound value's delivery cost prepays the
beta step (pure) or the beta plus the wrapper's eventual merge
(annot). Block entry costs `saveEntryCost ps` (1 at literal
initializers, 2 otherwise). Budgets are upper bounds (`wpt_mono_k`);
rules take slack premises (`c ≤ k`) at value-delivering leaves and
`+1` at deterministic taus.

THE CONTENTS mirror Wps.lean rule for rule: the memory rules through
`wpt_of_atomic` (`wpt_store`, `wpt_load`, the `_at`/`_cell_at`/`_plain`
forms, `wpt_create` at cost `2 ≤ k`); sequencing (`wpt_seq`,
`wpt_seq_spec`, `wpt_seq_sym`, `wpt_wseq`); `wpt_if`, `wpt_case_value`;
`wpt_save`/`wpt_run` (the latter with the decrease premise `1 + m ≤
k`); the call rule `wpt_call`/`wpt_call_root` (with the budget split);
operand evaluation and the memop; the pure exit and the
annotation layer; consequence (`wpt_mono`, `wpt_mono_k`, `wpt_mono_Ls`,
`wpt_fupd` — by strong induction on the budget since C3, the call
clause's continuation sitting below `k - 1`); framing (`wpt_frame`,
`wpt_frame_labels`/`frameLsT`); `blockSpecsT_intro` with
`blockSpecsT_frame`/`blockSpecsT_mono`; `procSpecsT_intro` with
`procSpecsT_empty`; and the collapses `wpt_sound_cps`/`wpt_sound`/
`wpt_sound_empty`.
-/
import CerberusHeapLang.Wps

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- Variant-indexed per-label preconditions (the total stratum's
    label context): `Ls l m vs ρ` — the label `l`'s precondition at
    VARIANT VALUE `m` (its body's step budget), jump-argument values
    `vs`, jump-time env `ρ`. The variant is a logical index, so
    heap-dependent measures (e.g. the length of the list a pointer
    argument heads) are pinned by the invariant itself. -/
abbrev LabelSpecT (GF : BundledGFunctors) : Type :=
  sym → Nat → List value → EnvStack → IProp GF

/-- BUDGET-INDEXED PROCEDURE SPECIFICATIONS (calls arc C3; the total
    twin of `ProcSpec`, the `LabelSpecT` precedent): `Θ f m vs` — the
    procedure `f`'s precondition and postcondition on the delivered
    value at CALLEE BUDGET `m` and argument values `vs`. The budget is a
    logical index chosen by the caller at the call (the call clause's
    split `1 + m + k' ≤ k`), so a recursive activation's budget sits
    strictly inside its caller's. -/
abbrev ProcSpecT (GF : BundledGFunctors) : Type :=
  sym → Nat → List value → IProp GF × (value → IProp GF)

/-- THE EMPTY TABLE at the total stratum (C2's guard, recovered). -/
def emptyProcSpecT {GF : BundledGFunctors} : ProcSpecT GF :=
  fun _ _ _ => (iprop(⌜False⌝), fun _ => iprop(⌜True⌝))

@[simp] theorem emptyProcSpecT_fst {GF : BundledGFunctors} (f : sym) (m : Nat)
    (vs : List value) : (emptyProcSpecT (GF := GF) f m vs).1 = iprop(⌜False⌝) := rfl

/-! The delivery cost of a value (`deliveryCost`: PROGRAM-DONE costs
one drive step; an annot value pays the REMOVE-ANNOT tau first) is
defined in Rules.lean, where the atomic step specification carries
it. -/

/-! ## The judgment -/

/-- One layer of the total statement judgment at budget `k`. FOUR
    clauses, mirroring `wps.pre` (Wps.lean) with the total
    strengthenings:
    - VALUE: the delivery cost must fit the remaining budget.
    - JUMP: the payload of `wps.pre`'s jump clause PLUS the mandatory
      decrease `1 + m ≤ k` at the ∃-chosen variant `m` (never
      optional — audit F-02).
    - CALL (calls arc C3; replaces C2's `⌜False⌝` guard): the payload of
      `wps.pre`'s call clause PLUS THE BUDGET SPLIT `1 + m + k' ≤ k` —
      one unit for the call round, the callee's budget `m` (the table's
      index, `ProcSpecT`: the callee's delivery cost IS its return
      protocol — 1 for a bare value, the RETURN tau; 2 for an annotated
      one, REMOVE-ANNOT then RETURN — exactly as the top-level protocol's
      PROGRAM-DONE costs, `deliveryCost`), and the CONTINUATION's budget
      `k'`, at which the caller's continuation `apply_ctx ctx (pure ret)`
      is judged. The recursive occurrence sits at `k' < k`: the judgment
      is defined by well-founded recursion on the budget, the
      continuation family `F` ranging over every smaller budget (the
      structural `k - 1` of the three-clause form cannot express the
      split).
    - STEP: the twp-shaped step obligation — NO later, NO credit (total
      WPs admit no Löb); the continuation `F` at budget `k-1`, and at
      `k = 0` the clause is `⌜False⌝`. Quantified over the call stack and
      execution location `(κ, ℓ)` exactly as `wps.pre` (the judgment is
      indexed by the current procedure `p`; the `wps.pre` docstring has
      the forcing fact — RETURN does not restore `exec_loc`). -/
def wpt.pre [SpikeGS hlc GF] (M : MachineCtx) (p : Option sym) (Ls : LabelSpecT GF)
    (Θ : ProcSpecT GF) (k : Nat)
    (F : ∀ (k' : Nat), k' < k →
      (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr) (ρ : EnvStack) :
    IProp GF :=
  match toVal e with
  | some w => iprop(⌜deliveryCost w ≤ k⌝ ∗ |={⊤}=> Ψ w ρ)
  | none =>
    match jumpRedex? e with
    | some lp =>
      iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (cont : CoreExpr)
        (vs : List value) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
        (m : Nat),
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel (M.labelsAt p) lp.1 = some (params, cont)⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ lp.2 = some vs⌝ ∗
        ⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ)
    | none =>
      match callRedex? e with
      | some q =>
        iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (body : CoreExpr)
          (vs : List value) (m k' : Nat) (hb : 1 + m + k' ≤ k),
          ⌜lookupProc M.file M.extern q.2.1 = some (params, body)⌝ ∗
          ⌜params.length = vs.length⌝ ∗
          ⌜evalPexprs M.tagDefs M.extern ρ q.2.2 = some vs⌝ ∗
          (Θ q.2.1 m vs).1 ∗
          ∀ (ret : value), (Θ q.2.1 m vs).2 ret -∗
            F k' (by omega) Ψ (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ)
      | none =>
        match hk : k with
        | 0 => iprop(⌜False⌝)
        | k' + 1 =>
          iprop(∀ (κ : List (Option sym × context)) (ℓ : exec_location)
            (σ₁ : Mem) (ns : Nat) (obs : List Empty) (nt : Nat),
            stateInterp σ₁ ns obs nt ={⊤,∅}=∗
            ⌜PrimStep.Reducible ((⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt), σ₁)⌝ ∗
            ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
              ⌜((⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝
                ={∅,⊤}=∗
              stateInterp σ₂ (ns + 1) obs nt ∗ F k' (by omega) Ψ r.e r.ρ)

/-- THE TOTAL STATEMENT JUDGMENT: well-founded recursion on the step
    budget (header note — no fixpoint machinery; the budget IS the
    well-founded measure; C3: the recursion is over EVERY smaller
    budget, so the call clause can split the budget between the callee
    and the continuation). `wpt M p Ls Θ k Ψ e ρ`: machine context,
    current procedure, its variant-indexed label specification, the
    budget-indexed procedure specification table, budget,
    postcondition, expression, live environment stack. -/
def wpt [SpikeGS hlc GF] (M : MachineCtx) (p : Option sym) (Ls : LabelSpecT GF)
    (Θ : ProcSpecT GF) :
    Nat → (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF
  | k => wpt.pre M p Ls Θ k (fun k' _ => wpt M p Ls Θ k')
termination_by k => k

variable [SpikeGS hlc GF]
variable {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}

/-! ## Per-clause unfolding equations -/

/-- One unfolding of the well-founded definition. -/
theorem wpt_unfold (k : Nat) (Ψ : SpikeVal → EnvStack → IProp GF) (e : CoreExpr)
    (ρ : EnvStack) :
    wpt M p Ls Θ k Ψ e ρ = wpt.pre M p Ls Θ k (fun k' _ => wpt M p Ls Θ k') Ψ e ρ := by
  rw [wpt]

theorem wpt_val_eq {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    {e : CoreExpr} {w : SpikeVal} {ρ : EnvStack} (htv : toVal e = some w) :
    wpt M p Ls Θ k Ψ e ρ = iprop(⌜deliveryCost w ≤ k⌝ ∗ |={⊤}=> Ψ w ρ) := by
  rw [wpt_unfold]; simp only [wpt.pre, htv]

theorem wpt_jump_eq {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    {e : CoreExpr} {l : sym} {pes : List (generic_pexpr Unit sym)}
    {ρ : EnvStack} (htv : toVal e = none)
    (hjr : jumpRedex? e = some (l, pes)) :
    wpt M p Ls Θ k Ψ e ρ =
      iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (cont : CoreExpr)
        (vs : List value) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
        (m : Nat),
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel (M.labelsAt p) l = some (params, cont)⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ pes = some vs⌝ ∗
        ⌜1 + m ≤ k⌝ ∗ Ls l m vs ρ) := by
  rw [wpt_unfold]; simp only [wpt.pre, htv, hjr]

theorem wpt_zero_step_eq {Ψ : SpikeVal → EnvStack → IProp GF}
    {e : CoreExpr} {ρ : EnvStack} (htv : toVal e = none)
    (hjr : jumpRedex? e = none) (hcr : callRedex? e = none) :
    wpt M p Ls Θ 0 Ψ e ρ = iprop(⌜False⌝) := by
  rw [wpt_unfold]; simp only [wpt.pre, htv, hjr, hcr]

/-- THE CALL CLAUSE (calls arc C3, replacing C2's guard equation): at a
    call redex in context the total judgment at budget `k` is the
    specification obligation with the budget split `1 + m + k' ≤ k`,
    the continuation judged at `k'`. -/
theorem wpt_call_eq {Ψ : SpikeVal → EnvStack → IProp GF} {k : Nat}
    {e : CoreExpr} {ρ : EnvStack} (htv : toVal e = none)
    (hjr : jumpRedex? e = none) {q : context × sym × List (generic_pexpr Unit sym)}
    (hcr : callRedex? e = some q) :
    wpt M p Ls Θ k Ψ e ρ =
      iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (body : CoreExpr)
        (vs : List value) (m k' : Nat) (_ : 1 + m + k' ≤ k),
        ⌜lookupProc M.file M.extern q.2.1 = some (params, body)⌝ ∗
        ⌜params.length = vs.length⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ q.2.2 = some vs⌝ ∗
        (Θ q.2.1 m vs).1 ∗
        ∀ (ret : value), (Θ q.2.1 m vs).2 ret -∗
          wpt M p Ls Θ k' Ψ (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ) := by
  rw [wpt_unfold]; simp only [wpt.pre, htv, hjr, hcr]

theorem wpt_step_eq {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    {e : CoreExpr} {ρ : EnvStack} (htv : toVal e = none)
    (hjr : jumpRedex? e = none) (hcr : callRedex? e = none) :
    wpt M p Ls Θ (k + 1) Ψ e ρ =
      iprop(∀ (κ : List (Option sym × context)) (ℓ : exec_location)
        (σ₁ : Mem) (ns : Nat) (obs : List Empty) (nt : Nat),
        stateInterp σ₁ ns obs nt ={⊤,∅}=∗
        ⌜PrimStep.Reducible ((⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt), σ₁)⌝ ∗
        ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
          ⌜((⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝
            ={∅,⊤}=∗
          stateInterp σ₂ (ns + 1) obs nt ∗ wpt M p Ls Θ k Ψ r.e r.ρ) := by
  rw [wpt_unfold]; simp only [wpt.pre, htv, hjr, hcr]

/-- At the EMPTY table a call redex is unverifiable (C2's guard,
    recovered): the clause's precondition is `False`. -/
theorem wpt_empty_call_false {Ψ : SpikeVal → EnvStack → IProp GF} {k : Nat}
    {e : CoreExpr} {ρ : EnvStack} (htv : toVal e = none)
    (hjr : jumpRedex? e = none) {q : context × sym × List (generic_pexpr Unit sym)}
    (hcr : callRedex? e = some q) :
    wpt M p Ls emptyProcSpecT k Ψ e ρ ⊢ iprop(|={⊤}=> ⌜False⌝) := by
  rw [wpt_call_eq htv hjr hcr]
  simp only [emptyProcSpecT_fst]
  iintro H
  imod H with ⟨%params, %body, %vs, %m, %k', %hb, %h1, %h2, %h3, %hF, -⟩
  exact hF.elim

/-! ## Structural rules -/

/-- Budget weakening: the judgment states an upper bound (strong
    induction on the budget: the call clause's continuation sits at a
    smaller budget than `k - 1`). -/
theorem wpt_mono_k {Ψ : SpikeVal → EnvStack → IProp GF} {k k' : Nat}
    (hk : k ≤ k') (e : CoreExpr) (ρ : EnvStack) :
    wpt M p Ls Θ k Ψ e ρ ⊢ wpt M p Ls Θ k' Ψ e ρ := by
  induction k using Nat.strongRecOn generalizing k' e ρ with
  | ind k IH =>
  cases htv : toVal e with
  | some w =>
    rw [wpt_val_eq k htv, wpt_val_eq k' htv]
    iintro ⟨%hc, H⟩
    isplit
    · ipureintro; exact Nat.le_trans hc hk
    · iexact H
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq k htv hjr, wpt_jump_eq k' htv hjr]
      iintro H
      imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %h1, %h2, %h3, %h4, HLs⟩
      imodintro
      iexists params, cont, vs, ev0, evs, m
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplit
      · ipureintro; exact Nat.le_trans h4 hk
      iexact HLs
    | none =>
    cases hcr : callRedex? e with
    | some q =>
      rw [wpt_call_eq htv hjr hcr, wpt_call_eq htv hjr hcr]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k₁, %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k₁, (Nat.le_trans hb hk)
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iexact Hcont
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro %h
        exact h.elim
      | succ m =>
        obtain ⟨m', rfl⟩ : ∃ m', k' = m' + 1 := ⟨k' - 1, by omega⟩
        rw [wpt_step_eq m htv hjr hcr, wpt_step_eq m' htv hjr hcr]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH m (Nat.lt_succ_self m) (by omega) (r.e) (r.ρ) $$ H

/-- Monotonicity in the postcondition (budget preserved; the jump
    clause is Ψ-independent — the pass-through mirrors `wps_wand`,
    which this rule replaces at the total stratum in ⊢-level form:
    the total judgment has no Löb, so the consequence function is a
    meta-level entailment family). The call clause's continuation
    rides by the induction at its smaller budget. -/
theorem wpt_mono {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ w ρ', Ψ₁ w ρ' ⊢ Ψ₂ w ρ') (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    wpt M p Ls Θ k Ψ₁ e ρ ⊢ wpt M p Ls Θ k Ψ₂ e ρ := by
  induction k using Nat.strongRecOn generalizing e ρ with
  | ind k IH =>
  cases htv : toVal e with
  | some w =>
    rw [wpt_val_eq (Ψ := Ψ₁) k htv, wpt_val_eq (Ψ := Ψ₂) k htv]
    iintro ⟨%hc, H⟩
    isplit
    · ipureintro; exact hc
    · imod H with H
      imodintro
      iapply h w ρ $$ H
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq (Ψ := Ψ₁) k htv hjr, wpt_jump_eq (Ψ := Ψ₂) k htv hjr]
    | none =>
    cases hcr : callRedex? e with
    | some q =>
      rw [wpt_call_eq (Ψ := Ψ₁) htv hjr hcr, wpt_call_eq (Ψ := Ψ₂) htv hjr hcr]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k₁, %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k₁, hb
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k₁ (by omega) (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ $$ H'
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq (Ψ := Ψ₁) htv hjr hcr, wpt_zero_step_eq (Ψ := Ψ₂) htv hjr hcr]
      | succ m =>
        rw [wpt_step_eq (Ψ := Ψ₁) m htv hjr hcr, wpt_step_eq (Ψ := Ψ₂) m htv hjr hcr]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH m (Nat.lt_succ_self m) (r.e) (r.ρ) $$ H

/-- Monotonicity in the LABEL CONTEXT (alloc arc P2): a judgment at
    a pointwise-stronger label context transports to a weaker one —
    the jump clause's payload maps through the entailment, the value,
    call and step clauses are label-free. (The production reversal wraps
    the generic list label spec in an existential over the
    engine-picked allocation ids; this is the transport.) -/
theorem wpt_mono_Ls {Ls₁ Ls₂ : LabelSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l m vs ρ', Ls₁ l m vs ρ' ⊢ Ls₂ l m vs ρ')
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    wpt M p Ls₁ Θ k Ψ e ρ ⊢ wpt M p Ls₂ Θ k Ψ e ρ := by
  induction k using Nat.strongRecOn generalizing e ρ with
  | ind k IH =>
  cases htv : toVal e with
  | some w =>
    rw [wpt_val_eq (Ls := Ls₁) k htv, wpt_val_eq (Ls := Ls₂) k htv]
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq (Ls := Ls₁) k htv hjr, wpt_jump_eq (Ls := Ls₂) k htv hjr]
      iintro H
      imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %h1, %h2, %h3, %h4, HLs⟩
      imodintro
      iexists params, cont, vs, ev0, evs, m
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplit
      · ipureintro; exact h4
      iapply h l m vs ρ $$ HLs
    | none =>
    cases hcr : callRedex? e with
    | some q =>
      rw [wpt_call_eq (Ls := Ls₁) htv hjr hcr, wpt_call_eq (Ls := Ls₂) htv hjr hcr]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k₁, %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k₁, hb
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k₁ (by omega) (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ $$ H'
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq (Ls := Ls₁) htv hjr hcr, wpt_zero_step_eq (Ls := Ls₂) htv hjr hcr]
      | succ m =>
        rw [wpt_step_eq (Ls := Ls₁) m htv hjr hcr, wpt_step_eq (Ls := Ls₂) m htv hjr hcr]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH m (Nat.lt_succ_self m) (r.e) (r.ρ) $$ H

/-- POSTCONDITION-MODALITY ABSORPTION at the total stratum (the
    `wps_fupd` twin, QA-1/M-3): the update is paid at the value exit
    (the value clause is fupd-headed), passes a jump untouched (the
    jump clause is Ψ-independent), rides through calls and steps by
    budget induction. -/
theorem wpt_fupd {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat) (e : CoreExpr)
    (ρ : EnvStack) :
    wpt M p Ls Θ k (fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) e ρ ⊢ wpt M p Ls Θ k Ψ e ρ := by
  induction k using Nat.strongRecOn generalizing e ρ with
  | ind k IH =>
  cases htv : toVal e with
  | some w =>
    rw [wpt_val_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) k htv,
      wpt_val_eq (Ψ := Ψ) k htv]
    iintro ⟨%hc, H⟩
    isplit
    · ipureintro; exact hc
    · imod H with H
      imod H with H
      imodintro
      iexact H
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) k htv hjr,
        wpt_jump_eq (Ψ := Ψ) k htv hjr]
    | none =>
    cases hcr : callRedex? e with
    | some q =>
      rw [wpt_call_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) htv hjr hcr,
        wpt_call_eq (Ψ := Ψ) htv hjr hcr]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k₁, %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k₁, hb
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k₁ (by omega) (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ $$ H'
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) htv hjr hcr,
          wpt_zero_step_eq (Ψ := Ψ) htv hjr hcr]
      | succ m =>
        rw [wpt_step_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) m htv hjr hcr,
          wpt_step_eq (Ψ := Ψ) m htv hjr hcr]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH m (Nat.lt_succ_self m) (r.e) (r.ρ) $$ H

/-! ## Statement-level framing at the total stratum (alloc arc P4.2,
R-05): the frame rides through the value exit and every back edge by
framing the variant-indexed label context pointwise (Wps.lean,
"Statement-level framing"). -/

/-- Framing of a variant-indexed label context. -/
abbrev frameLsT (R : IProp GF) (Ls : LabelSpecT GF) : LabelSpecT GF :=
  fun l m vs ρ => iprop(Ls l m vs ρ ∗ R)

/-- THE TOTAL STATEMENT FRAME RULE (labels included): induction on the
    budget, clause by clause — the value clause keeps its cost bound,
    the jump clause keeps its variant decrease, the call clause keeps
    its budget split (the frame rides into the caller's continuation). -/
theorem wpt_frame_labels {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    wpt M p Ls Θ k Ψ e ρ ⊢
      iprop(R -∗ wpt M p (frameLsT R Ls) Θ k (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ) := by
  induction k using Nat.strongRecOn generalizing e ρ with
  | ind k IH =>
  cases htv : toVal e with
  | some w =>
    rw [wpt_val_eq (Ls := Ls) k htv, wpt_val_eq (Ls := frameLsT R Ls) k htv]
    iintro ⟨%hc, H⟩ HR
    isplit
    · ipureintro; exact hc
    · imod H with H
      imodintro
      isplitl [H]
      · iexact H
      · iexact HR
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq (Ls := Ls) k htv hjr, wpt_jump_eq (Ls := frameLsT R Ls) k htv hjr]
      iintro H HR
      imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %h1, %h2, %h3, %h4, HLs⟩
      imodintro
      iexists params, cont, vs, ev0, evs, m
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplit
      · ipureintro; exact h4
      isplitl [HLs]
      · iexact HLs
      · iexact HR
    | none =>
    cases hcr : callRedex? e with
    | some q =>
      rw [wpt_call_eq (Ls := Ls) htv hjr hcr, wpt_call_eq (Ls := frameLsT R Ls) htv hjr hcr]
      iintro H HR
      imod H with ⟨%params, %body, %vs, %m, %k₁, %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k₁, hb
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k₁ (by omega) (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ
        $$ H' HR
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq (Ls := Ls) htv hjr hcr, wpt_zero_step_eq (Ls := frameLsT R Ls) htv hjr hcr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq (Ls := Ls) m htv hjr hcr, wpt_step_eq (Ls := frameLsT R Ls) m htv hjr hcr]
        iintro H HR %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH m (Nat.lt_succ_self m) (r.e) (r.ρ) $$ H HR

/-- The value-channel frame at a FIXED label context (derived: frame
    the labels, then drop the frame from them — the total analogue of
    `wps_frame`; what a straight-line client needs). -/
theorem wpt_frame {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    iprop(wpt M p Ls Θ k Ψ e ρ ∗ R) ⊢
      wpt M p Ls Θ k (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ := by
  iintro ⟨H, HR⟩
  iapply wpt_mono_Ls (Ls₁ := frameLsT R Ls) (fun l m vs ρ' => BI.sep_elim_left) k e ρ
  iapply wpt_frame_labels R k e ρ $$ H HR

/-- Value rule (delivery cost within budget). -/
theorem wpt_ofVal {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeVal)
    (ρ : EnvStack) {k : Nat} (hk : deliveryCost w ≤ k) :
    Ψ w ρ ⊢ wpt M p Ls Θ k Ψ (ofVal w) ρ := by
  rw [wpt_val_eq k (toVal_ofVal w)]
  iintro H
  isplit
  · ipureintro; exact hk
  · imodintro
    iexact H

/-- LIFTING AN ATOMIC STEP SPECIFICATION (Rules.lean `AtomicStep`) to
    the total judgment: one budget unit for the step plus the
    delivered value's cost — `c + 1 ≤ k`. Every memory rule below is
    this lemma applied to its small axiom's atomic specification
    (professor review 1, required fix 8). -/
theorem wpt_of_atomic {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr}
    {ρ : EnvStack} {c : Nat} {P : IProp GF} {Q : SpikeVal → IProp GF} {k : Nat}
    (h : ∀ (κ : List (Option sym × context)) (ℓ : exec_location),
      AtomicStep M ⟨κ, p, ℓ⟩ e ρ c P Q)
    (hnv : toVal e = none)
    (hnj : jumpRedex? e = none) (hnc : callRedex? e = none) (hk : c + 1 ≤ k) :
    iprop(P ∗ (∀ w : SpikeVal, Q w -∗ Ψ w ρ)) ⊢ wpt M p Ls Θ k Ψ e ρ := by
  obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by omega⟩
  rw [wpt_step_eq k1 hnv hnj hnc]
  iintro ⟨HP, HΨ⟩ %κ %ℓ %σ₁ %ns %obs %nt Hσ
  imod (h κ ℓ ⊤ ∅ Std.LawfulSet.empty_subset σ₁ ns obs nt) $$ [$HP $Hσ]
    with ⟨%hred, Hcont⟩
  imodintro
  isplitr
  · ipureintro
    exact hred
  iintro %r %σ₂ %eₜ %Hstep
  imod Hcont $$ %r %σ₂ %eₜ %Hstep with ⟨Hσ', %w, %hw, HQ⟩
  obtain ⟨rfl, rfl, hc⟩ := hw
  imodintro
  isplitl [Hσ']
  · iexact Hσ'
  · iapply (wpt_ofVal w ρ (by omega))
    iapply HΨ $$ HQ

/-- THE TOTAL JUMP RULE (the total analog of `wps_run`): a
    registered jump is verified by the label's precondition at the
    argument values AND the mandatory budget decrease
    `1 + μ l vs ≤ k` — the well-founded variant obligation, never
    optional (audit F-02 criterion). -/
theorem wpt_run {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (ra : core_run_annotation) (l : sym)
    (pes : List (generic_pexpr Unit sym))
    {params : List (sym × core_base_type)} {cont : CoreExpr}
    {vs : List value} (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (m : Nat) {k : Nat}
    (hl : lookupLabel (M.labelsAt p) l = some (params, cont))
    (hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some vs)
    (hμ : 1 + m ≤ k) :
    Ls l m vs (ev0 :: evs) ⊢
      wpt M p Ls Θ k Ψ (Expr a (Erun ra l pes)) (ev0 :: evs) := by
  rw [wpt_jump_eq k (show toVal (Expr a (Erun ra l pes)) = none from rfl)
    (jumpRedex?_run a ra l pes)]
  iintro H
  imodintro
  iexists params, cont, vs, ev0, evs, m
  isplit
  · ipureintro; rfl
  isplit
  · ipureintro; exact hl
  isplit
  · ipureintro; exact hvs
  isplit
  · ipureintro; exact hμ
  iexact H

/-- THE TOTAL CALL RULE at a call redex IN CONTEXT (calls arc C3; the
    total analog of `wps_call`): the table's precondition at the callee's
    budget `m`, the caller's continuation at budget `k'`, and THE BUDGET
    SPLIT `1 + m + k' ≤ k` — the call round, the callee (its return
    included, `deliveryCost`), the rest of the caller. Near-definitional:
    the judgment's call clause IS this rule. -/
theorem wpt_call {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr} {ctx : context}
    {f : sym} {pes : List (generic_pexpr Unit sym)}
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    (ρ : EnvStack) {m k' k : Nat}
    (hc : callRedex? e = some (ctx, f, pes))
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length)
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
    (hk : 1 + m + k' ≤ k) :
    iprop((Θ f m vs).1 ∗ (∀ (ret : value), (Θ f m vs).2 ret -∗
        wpt M p Ls Θ k' Ψ (apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ)) ⊢
      wpt M p Ls Θ k Ψ e ρ := by
  have htv : toVal e = none := by
    cases h : toVal e with
    | none => rfl
    | some w => rw [← ofVal_of_toVal h, callRedex?_ofVal] at hc; cases hc
  have hjr : jumpRedex? e = none := jumpRedex?_none_of_callRedex?_some hc
  rw [wpt_call_eq htv hjr hc]
  iintro ⟨Hpre, Hcont⟩
  imodintro
  iexists params, body, vs, m, k', hk
  isplit
  · ipureintro; exact hf
  isplit
  · ipureintro; exact hlen
  isplit
  · ipureintro; exact hvs
  isplitl [Hpre]
  · iexact Hpre
  iexact Hcont

/-- THE TOTAL CALL RULE at the root redex `Eproc`. -/
theorem wpt_call_root {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (ra : core_run_annotation) (f : sym) (pes : List (generic_pexpr Unit sym))
    {params : List (sym × core_base_type)} {body : CoreExpr} {vs : List value}
    (ρ : EnvStack) {m k' k : Nat}
    (hf : lookupProc M.file M.extern f = some (params, body))
    (hlen : params.length = vs.length)
    (hvs : evalPexprs M.tagDefs M.extern ρ pes = some vs)
    (hk : 1 + m + k' ≤ k) :
    iprop((Θ f m vs).1 ∗ (∀ (ret : value), (Θ f m vs).2 ret -∗
        wpt M p Ls Θ k' Ψ (Expr [] (Epure (Pexpr [] () (PEval ret)))) ρ)) ⊢
      wpt M p Ls Θ k Ψ (Expr a (Eproc ra (Sym f) pes)) ρ :=
  wpt_call ρ (callRedex?_proc a ra f pes) hf hlen hvs hk

/-! ## The deterministic-tau lifting (one lemma for every
state-preserving deterministic step; the per-construct rules are its
instances plus one inversion each) -/

/-- A state-preserving deterministic step costs one budget unit. -/
theorem wpt_det_step {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr}
    {ρ : EnvStack} {e' : CoreExpr} {ρ' : EnvStack} {k : Nat}
    (htv : toVal e = none) (hjr : jumpRedex? e = none) (hcr : callRedex? e = none)
    (hstep : ∀ (κ : List (Option sym × context)) (ℓ : exec_location) (σ : Mem),
      Step M (e, ρ, ⟨κ, p, ℓ⟩, σ) (e', ρ', ⟨κ, p, ℓ⟩, σ))
    (hdet : ∀ (κ : List (Option sym × context)) (ℓ : exec_location) (σ : Mem) (out : Config),
      Step M (e, ρ, ⟨κ, p, ℓ⟩, σ) out → out = (e', ρ', ⟨κ, p, ℓ⟩, σ)) :
    wpt M p Ls Θ k Ψ e' ρ' ⊢ wpt M p Ls Θ (k + 1) Ψ e ρ := by
  rw [wpt_step_eq k htv hjr hcr]
  iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨e', ρ', ⟨κ, p, ℓ⟩, M⟩, σ₁, [], hstep κ ℓ σ₁, rfl, rfl⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  have hout := hdet κ ℓ σ₁ _ hs
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs hcr htv).symm
  obtain ⟨hre, hrρ, hσ⟩ : re = e' ∧ rρ = ρ' ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre hrρ
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  · iexact H

/-! ## Branch/entry rules (instances of the tau lifting) -/

/-- THE CONDITIONAL RULE at the total stratum (QA-1/Q4: the verdict
    inside the logic; one tau) — an instance of the deterministic-tau
    lifting at each verdict. -/
theorem wpt_if {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack) (b : Bool)
    {k : Nat} :
    iprop(⌜evalPexpr M.tagDefs M.extern ρ g = some (boolValue b)⌝ ∗
      wpt M p Ls Θ k Ψ (bif b then e2 else e3) ρ) ⊢
      wpt M p Ls Θ (k + 1) Ψ (Expr a (Eif g e2 e3)) ρ := by
  cases b
  · rw [show (bif false then e2 else e3) = e3 from rfl]
    iintro ⟨%hg, H⟩
    iapply wpt_det_step rfl rfl rfl (fun _ _ _ => Step.if_false hg)
      (fun _ _ σ out hs => by
        rcases hs.if_inv with ⟨hg', -⟩ | ⟨-, hout⟩
        · rw [hg] at hg'; cases hg'
        · exact hout)
    iexact H
  · rw [show (bif true then e2 else e3) = e2 from rfl]
    iintro ⟨%hg, H⟩
    iapply wpt_det_step rfl rfl rfl (fun _ _ _ => Step.if_true hg)
      (fun _ _ σ out hs => by
        rcases hs.if_inv with ⟨-, hout⟩ | ⟨hg', -⟩
        · exact hout
        · rw [hg] at hg'; cases hg')
    iexact H

/-- Eif, true branch — the `b := true` instance of `wpt_if` (derived
    corollary, verdict at the meta level). -/
theorem wpt_if_true {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack) {k : Nat}
    (hg : evalPexpr M.tagDefs M.extern ρ g = some Vtrue) :
    wpt M p Ls Θ k Ψ e2 ρ ⊢ wpt M p Ls Θ (k + 1) Ψ (Expr a (Eif g e2 e3)) ρ := by
  iintro H
  iapply wpt_if a g e2 e3 ρ true
  isplit
  · ipureintro; exact hg
  · rw [show (bif true then e2 else e3) = e2 from rfl]
    iexact H

/-- Eif, false branch — the `b := false` instance of `wpt_if`. -/
theorem wpt_if_false {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack) {k : Nat}
    (hg : evalPexpr M.tagDefs M.extern ρ g = some Vfalse) :
    wpt M p Ls Θ k Ψ e3 ρ ⊢ wpt M p Ls Θ (k + 1) Ψ (Expr a (Eif g e2 e3)) ρ := by
  iintro H
  iapply wpt_if a g e2 e3 ρ false
  isplit
  · ipureintro; exact hg
  · rw [show (bif false then e2 else e3) = e3 from rfl]
    iexact H

/-- Ecase at a VALUE scrutinee, total (the `wps_case_value` twin,
    QA-1/M-3): the substitution TAU is deterministic and
    state-preserving — an instance of `wpt_det_step`. -/
theorem wpt_case_value {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (pe : generic_pexpr Unit sym) (pats : List (pattern × CoreExpr))
    {cval : value} {e' : CoreExpr} (ρ : EnvStack) {k : Nat}
    (hv : valueFromPexpr pe = some cval)
    (hsel : select_case subst_sym_expr cval pats = some e') :
    wpt M p Ls Θ k Ψ e' ρ ⊢ wpt M p Ls Θ (k + 1) Ψ (Expr a (Ecase pe pats)) ρ :=
  wpt_det_step rfl rfl rfl (fun _ _ _ => Step.case_value hv hsel)
    (fun _ _ σ out hs => by
      obtain ⟨cval', e'', hv', hsel', hout⟩ := hs.case_inv
      obtain rfl : cval = cval' := Option.some.inj (hv.symm.trans hv')
      obtain rfl : e' = e'' := Option.some.inj (hsel.symm.trans hsel')
      exact hout)

/-- Esave ENTRY at VALUE initializers (the TAU arm; one tau) — the
    literal instance of `wpt_save`. -/
theorem wpt_save_vals {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) {cvals : List value}
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) {k : Nat}
    (hvals : valueFromPexprs (saveParamPexprs ps) = some cvals) :
    wpt M p Ls Θ k Ψ body (bindSaveParams ps cvals (ev0 :: evs)) ⊢
      wpt M p Ls Θ (k + 1) Ψ (Expr a (Esave sb ps body)) (ev0 :: evs) :=
  wpt_det_step rfl rfl rfl (fun _ _ _ => Step.save hvals)
    (fun _ _ σ out hs => by
      obtain ⟨ev0', evs', hρeq, hout⟩ := hs.save_vals_inv hvals
      exact hout)

/-- Esave PARAMETER EVALUATION (the EVAL arm, `Step.save_eval`; one
    tau): initializers not all values evaluate and the node is
    re-formed with literal initializers. -/
theorem wpt_save_eval {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) {cvals : List value} (ρ : EnvStack) {k : Nat}
    (hnv : valueFromPexprs (saveParamPexprs ps) = none)
    (hvals : evalPexprs M.tagDefs M.extern ρ (saveParamPexprs ps) = some cvals) :
    wpt M p Ls Θ k Ψ (Expr a (Esave sb (saveParamsWithValues ps cvals) body)) ρ ⊢
      wpt M p Ls Θ (k + 1) Ψ (Expr a (Esave sb ps body)) ρ :=
  wpt_det_step rfl rfl rfl (fun _ _ _ => Step.save_eval hnv hvals)
    (fun _ _ σ out hs => by
      obtain ⟨cvals', hvals', hout⟩ := hs.save_op_inv hnv
      obtain rfl : cvals = cvals' := Option.some.inj (hvals.symm.trans hvals')
      exact hout)

/-- The engine's entry cost of an Esave node: one tau at value
    initializers (the TAU arm), two otherwise (EVAL then TAU) — the
    engine's own dispatch (`valueFromPexprs`) decides, so at literal
    initializers it is `1` by `rfl`. -/
def saveEntryCost
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))) : Nat :=
  match valueFromPexprs (saveParamPexprs ps) with
  | some _ => 1
  | none => 2

theorem saveEntryCost_of_vals
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {cvals : List value} (h : valueFromPexprs (saveParamPexprs ps) = some cvals) :
    saveEntryCost ps = 1 := by
  unfold saveEntryCost; rw [h]

theorem saveEntryCost_of_eval
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    (h : valueFromPexprs (saveParamPexprs ps) = none) :
    saveEntryCost ps = 2 := by
  unfold saveEntryCost; rw [h]

/-- ESAVE ENTRY at the total stratum (QA-1/H-1 generality): the
    initializers evaluate at the entry env to `cvals`, the body is
    verified at the parameter-bound env at budget `k`, and the node
    costs its engine entry cost on top (`saveEntryCost ps`: `1` at
    literal initializers — the pre-QA-1 statement `wpt_save_vals` is
    the instance — `2` at live-variable initializers). -/
theorem wpt_save {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) {cvals : List value}
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) {k : Nat}
    (hvals : evalPexprs M.tagDefs M.extern (ev0 :: evs) (saveParamPexprs ps) = some cvals) :
    wpt M p Ls Θ k Ψ body (bindSaveParams ps cvals (ev0 :: evs)) ⊢
      wpt M p Ls Θ (k + saveEntryCost ps) Ψ (Expr a (Esave sb ps body)) (ev0 :: evs) := by
  cases hv : valueFromPexprs (saveParamPexprs ps) with
  | some cvals' =>
    obtain rfl : cvals = cvals' := Option.some.inj
      (hvals.symm.trans (evalPexprs_of_valueFromPexprs M.tagDefs M.extern _ hv))
    rw [saveEntryCost_of_vals hv]
    exact wpt_save_vals a sb ps body ev0 evs hv
  | none =>
    rw [saveEntryCost_of_eval hv, show k + 2 = (k + 1) + 1 from rfl]
    refine .trans ?_ (wpt_save_eval a sb ps body (ev0 :: evs) hv hvals)
    rw [← bindSaveParams_withValues ps cvals]
    exact wpt_save_vals a sb _ body ev0 evs (valueFromPexprs_withValues ps cvals
      ((List.length_map ..).symm.trans (evalPexprs_length _ _ _ hvals)))

/-- PURE at a non-value pexpr: one big-step evaluation tau, then the
    bare value's delivery (total cost 2 ≤ k). -/
theorem wpt_pure {Ψ : SpikeVal → EnvStack → IProp GF}
    (pe : generic_pexpr Unit sym) (ρ : EnvStack) {v : value} {k : Nat}
    (hk : 2 ≤ k)
    (hnv : valueFromPexpr pe = none) (hv : evalPexpr M.tagDefs M.extern ρ pe = some v) :
    Ψ (.pure v) ρ ⊢ wpt M p Ls Θ k Ψ (Expr ([] : List annot) (Epure pe)) ρ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine .trans (wpt_ofVal (M := M) (p := p) (Ls := Ls) (Θ := Θ) (.pure v) ρ (by simp only [deliveryCost_pure]; exact Nat.le_of_succ_le_succ hk)) ?_
  exact wpt_det_step (toVal_pure_none hnv) (jumpRedex?_pure _ _) (callRedex?_pure _ _)
    (fun _ _ _ => Step.pure_eval hnv hv)
    (fun _ _ σ out hs => by
      obtain ⟨v', -, hv', hout⟩ := hs.pure_inv hnv
      obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
      exact hout)

/-- ACTION_EVAL for a load's pointer operand (one tau). -/
theorem wpt_load_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 : generic_pexpr Unit sym) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue} {k : Nat}
    (hnv2 : valueFromPexpr pe2 = none)
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv))) :
    wpt M p Ls Θ k Ψ (loadExpr loc ann ty pv mo) ρ ⊢
      wpt M p Ls Θ (k + 1) Ψ (loadOpRedex loc ann ty pe2 mo) ρ :=
  wpt_det_step rfl rfl rfl (fun _ _ _ => Step.load_eval hnv2 hv2)
    (fun _ _ σ out hs => by
      obtain ⟨pv', hv2', hout⟩ := hs.load_op_inv hnv2
      obtain rfl : pv = pv' := by
        simpa using Option.some.inj (hv2.symm.trans hv2')
      simpa [loadExpr] using hout)

/-- ACTION_EVAL for a kill's pointer operand (one tau; kill/free arc K2). -/
theorem wpt_kill_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pe : generic_pexpr Unit sym) (ρ : EnvStack)
    {pv : CerbMem.PointerValue} {k : Nat}
    (hnv : valueFromPexpr pe = none)
    (hv : evalPexpr M.tagDefs M.extern ρ pe = some (Vobject (OVpointer pv))) :
    wpt M p Ls Θ k Ψ (killExpr loc ann kind pv) ρ ⊢
      wpt M p Ls Θ (k + 1) Ψ (killOpRedex loc ann kind pe) ρ :=
  wpt_det_step rfl rfl rfl (fun _ _ _ => Step.kill_eval hnv hv)
    (fun _ _ σ out hs => by
      obtain ⟨pv', hv', hout⟩ := hs.kill_op_inv hnv
      obtain rfl : pv = pv' := by
        simpa using Option.some.inj (hv.symm.trans hv')
      simpa [killExpr] using hout)

/-- ACTION_EVAL for a store's operands (one tau). -/
theorem wpt_store_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 pe3 : generic_pexpr Unit sym) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue} {cv : value} {k : Nat}
    (hnv : valueFromPexprs [pe2, pe3] = none)
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv)))
    (hv3 : evalPexpr M.tagDefs M.extern ρ pe3 = some cv) :
    wpt M p Ls Θ k Ψ (storeExpr loc ann ty pv cv mo) ρ ⊢
      wpt M p Ls Θ (k + 1) Ψ (storeOpRedex loc ann ty pe2 pe3 mo) ρ :=
  wpt_det_step rfl rfl rfl (fun _ _ _ => Step.store_eval hnv hv2 hv3)
    (fun _ _ σ out hs => by
      obtain ⟨pv', cv', hv2', hv3', hout⟩ := hs.store_op_inv hnv
      obtain rfl : pv = pv' := by
        simpa using Option.some.inj (hv2.symm.trans hv2')
      obtain rfl : cv = cv' := Option.some.inj (hv3.symm.trans hv3')
      simpa [storeExpr] using hout)

/-- ACTION_EVAL for an alloc's operands (one tau; kill/free arc K3). -/
theorem wpt_alloc_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (pe1 pe2 : generic_pexpr Unit sym) (pref : prefix0) (ρ : EnvStack)
    {align size : CerbMem.IntegerValue} {k : Nat}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hv1 : evalPexpr M.tagDefs M.extern ρ pe1 = some (Vobject (OVinteger align)))
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVinteger size))) :
    wpt M p Ls Θ k Ψ (allocExpr loc ann align size pref) ρ ⊢
      wpt M p Ls Θ (k + 1) Ψ (allocOpRedex loc ann pe1 pe2 pref) ρ :=
  wpt_det_step rfl rfl rfl (fun _ _ _ => Step.alloc_eval hnv hv1 hv2)
    (fun _ _ σ out hs => by
      obtain ⟨al', sz', hv1', hv2', hout⟩ := hs.alloc_op_inv hnv
      obtain rfl : align = al' := by
        simpa using Option.some.inj (hv1.symm.trans hv1')
      obtain rfl : size = sz' := by
        simpa using Option.some.inj (hv2.symm.trans hv2')
      simpa [allocExpr] using hout)

/-- Memop-operand evaluation (one tau). -/
theorem wpt_memop_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (mop : memop) (pe1 pe2 : generic_pexpr Unit sym)
    {v1 v2 : value} (ρ : EnvStack) {k : Nat}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hv1 : evalPexpr M.tagDefs M.extern ρ pe1 = some v1)
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some v2) :
    wpt M p Ls Θ k Ψ (memopRedex mop
      [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) ρ ⊢
      wpt M p Ls Θ (k + 1) Ψ (memopRedex mop [pe1, pe2]) ρ :=
  wpt_det_step rfl rfl rfl (fun _ _ _ => Step.memop_eval hnv hv1 hv2)
    (fun _ _ σ out hs => by
      obtain ⟨v1', v2', hv1', hv2', hout⟩ := hs.memop_op_inv hnv
      obtain rfl : v1 = v1' := Option.some.inj (hv1.symm.trans hv1')
      obtain rfl : v2 = v2' := Option.some.inj (hv2.symm.trans hv2')
      exact hout)

/-- The pointer-equality memop at value operands: one
    state-verbatim step then the bare boolean's delivery (cost
    2 ≤ k). -/
theorem wpt_memop_ptreq {Ψ : SpikeVal → EnvStack → IProp GF}
    (pv1 pv2 : CerbMem.PointerValue) {b : Bool} (ρ : EnvStack) {k : Nat}
    (hk : 2 ≤ k)
    (hres : ∀ σ : Mem, applyMemM (CerbMem.eqPtrval default pv1 pv2) σ =
      some (b, σ)) :
    Ψ (.pure (boolValue b)) ρ ⊢
      wpt M p Ls Θ k Ψ (memopPtrEqVals (Vobject (OVpointer pv1))
        (Vobject (OVpointer pv2))) ρ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine .trans (wpt_ofVal (M := M) (p := p) (Ls := Ls) (Θ := Θ) (.pure (boolValue b)) ρ
    (by simp only [deliveryCost_pure]; exact Nat.le_of_succ_le_succ hk)) ?_
  exact wpt_det_step rfl rfl rfl
    (fun _ _ σ => Step.memop_ptreq rfl rfl (hres σ))
    (fun _ _ σ out hs => by
      obtain ⟨b', σ'', hmem, hout⟩ := hs.memop_ptreq_inv rfl rfl
      rw [hres σ] at hmem
      obtain ⟨rfl, rfl⟩ : b = b' ∧ σ = σ'' := by
        have h := Option.some.inj hmem
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      exact hout)

/-! ## The annotation layer at the total stratum (mirrors of
`wps_annot_reindex`/`wps_annot`; Löb replaced by strong induction on
the budget — annotation reduction is lockstep, so reindexing is
budget-preserving and the wrapper costs exactly one unit: its
eventual merge step) -/

/-- Annotation reindexing over `wpt` (budget-preserving). -/
theorem wpt_annot_reindex (a : List annot) (dsA dsB : List dyn_annotation)
    (c : CoreExpr) (ρ : EnvStack) {k : Nat}
    {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (hΦ : ∀ w ρ', Ψ₁ (SpikeVal.merge dsA w) ρ' = Ψ₂ (SpikeVal.merge dsB w) ρ') :
    wpt M p Ls Θ k Ψ₁ (Expr a (Eannot dsA c)) ρ ⊢
      wpt M p Ls Θ k Ψ₂ (Expr a (Eannot dsB c)) ρ := by
  induction k using Nat.strongRecOn generalizing a dsA dsB c ρ Ψ₁ Ψ₂ with
  | ind k IH =>
  rcases toVal_annot_cases a c dsA with ⟨rfl, v, rfl, hA⟩ | hA
  · -- value on both sides (delivery cost 2 = 2)
    have hB : toVal (Expr ([] : List annot) (Eannot dsB (ofVal (.pure v)))) =
        some (.annot dsB v) := rfl
    rw [wpt_val_eq (Ψ := Ψ₁) k hA, wpt_val_eq (Ψ := Ψ₂) k hB]
    iintro ⟨%hc, H⟩
    isplit
    · ipureintro; exact hc
    · imod H with H
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
    have hEq : jumpRedex? (Expr a (Eannot dsB c)) =
        jumpRedex? (Expr a (Eannot dsA c)) := by
      rw [jumpRedex?_annot, jumpRedex?_annot]
    have hEqC : callRedex? (Expr a (Eannot dsB c)) = none ↔
        callRedex? (Expr a (Eannot dsA c)) = none := by
      rw [callRedex?_annot, callRedex?_annot]
      split <;> simp
    cases hjr : jumpRedex? (Expr a (Eannot dsA c)) with
    | some lp =>
      -- the two jump clauses are the SAME FORMULA (Ψ-free, same budget)
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq (Ψ := Ψ₁) k hA hjr,
        wpt_jump_eq (Ψ := Ψ₂) k hB (hEq.trans hjr)]
    | none =>
    cases hcr : callRedex? (Expr a (Eannot dsA c)) with
    | some q =>
      -- the body carries the call redex; the two wraps capture it in
      -- `Cannot` frames differing only in the payload
      have hnr : annotRooted c = false := by
        cases hr : annotRooted c with
        | false => rfl
        | true => rw [callRedex?_annot_of_root _ _ hr] at hcr; cases hcr
      obtain ⟨q₀, hq₀⟩ : ∃ q₀, callRedex? c = some q₀ := by
        cases hc : callRedex? c with
        | none => rw [callRedex?_annot_of_not_root _ _ hnr, hc] at hcr; cases hcr
        | some q₀ => exact ⟨q₀, rfl⟩
      have hcrA : callRedex? (Expr a (Eannot dsA c)) = some (Cannot a dsA q₀.1, q₀.2) := by
        rw [callRedex?_annot_of_not_root _ _ hnr, hq₀]; rfl
      have hcrB : callRedex? (Expr a (Eannot dsB c)) = some (Cannot a dsB q₀.1, q₀.2) := by
        rw [callRedex?_annot_of_not_root _ _ hnr, hq₀]; rfl
      rw [wpt_call_eq (Ψ := Ψ₁) hA hjr hcrA, wpt_call_eq (Ψ := Ψ₂) hB (hEq.trans hjr) hcrB]
      simp only [apply_ctx_annot]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k', %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k', hb
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k' (by omega) a dsA dsB (apply_ctx q₀.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ hΦ $$ H'
    | none =>
      have hcrB : callRedex? (Expr a (Eannot dsB c)) = none := hEqC.mpr hcr
      cases k with
      | zero =>
        rw [wpt_zero_step_eq (Ψ := Ψ₁) hA hjr hcr,
          wpt_zero_step_eq (Ψ := Ψ₂) hB (hEq.trans hjr) hcrB]
      | succ m =>
        rw [wpt_step_eq (Ψ := Ψ₁) m hA hjr hcr,
          wpt_step_eq (Ψ := Ψ₂) m hB (hEq.trans hjr) hcrB]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
          rcases hstep.1.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs, _⟩ |
              ⟨a2, ds2, c'', rfl, _⟩ |
              ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
              ⟨hg, hcall⟩ | ⟨v', pc, κ, ha, hb, hκ, _⟩
          · exact ⟨[], ⟨Expr a (Eannot dsB c'), ρ', ⟨κ, p, ℓ⟩, M⟩, _, [],
              ⟨Step.annot_ctx hnj hg hs, rfl, rfl⟩⟩
          · exact ⟨[], ⟨Expr (a ++ a2) (Eannot (dsB ++ ds2) c''), ρ, ⟨κ, p, ℓ⟩, M⟩, _, [],
              ⟨Step.annot_merge, rfl, rfl⟩⟩
          · rw [jumpRedex?_annot_of_not_root _ _ hg, hj] at hjr; cases hjr
          · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
            rw [callRedex?_body_none_of_annot hg hcr] at h; cases h
          · subst ha hb
            exact absurd hA (by simp [toVal])
        · iintro %e₂ %σ₂ %eₜ %HstepB
          obtain ⟨hstepB, hlbl, rfl⟩ := HstepB
          rcases hstepB.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs, hout⟩ |
              ⟨a2, ds2, c'', rfl, hout⟩ |
              ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
              ⟨hg, hcall⟩ | ⟨v', pc, κ, ha, hb, hκ, _⟩
          · obtain ⟨e₂e, e₂ρ, e₂ctl, e₂M⟩ := e₂
            simp only at hlbl
            obtain rfl : M = e₂M := hlbl.symm
            obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = e₂ctl := (Step.ctl_eq hstepB hcrB hB).symm
            obtain ⟨he, hρ, hσ⟩ : e₂e = Expr a (Eannot dsB c') ∧ e₂ρ = ρ' ∧
                σ₂ = σ'' := by
              simpa [Prod.mk.injEq] using hout
            subst he hρ hσ
            imod H $$ %(⟨Expr a (Eannot dsA c'), e₂ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) %_ %([])
              %⟨Step.annot_ctx hnj hg hs, rfl, rfl⟩ with ⟨$, H⟩
            imodintro
            iapply IH m (Nat.lt_succ_self m) a dsA dsB c' e₂ρ hΦ $$ H
          · obtain ⟨e₂e, e₂ρ, e₂ctl, e₂M⟩ := e₂
            simp only at hlbl
            obtain rfl : M = e₂M := hlbl.symm
            obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = e₂ctl := (Step.ctl_eq hstepB hcrB hB).symm
            obtain ⟨he, hρ, hσ⟩ : e₂e = Expr (a ++ a2) (Eannot (dsB ++ ds2) c'') ∧
                e₂ρ = ρ ∧ σ₂ = σ₁ := by
              simpa [Prod.mk.injEq] using hout
            subst he
            obtain rfl : ρ = e₂ρ := hρ.symm
            obtain rfl : σ₁ = σ₂ := hσ.symm
            imod H $$ %(⟨Expr (a ++ a2) (Eannot (dsA ++ ds2) c''), ρ,
                ⟨κ, p, ℓ⟩, M⟩ : CoreRt) %_
              %([]) %⟨Step.annot_merge, rfl, rfl⟩ with ⟨$, H⟩
            imodintro
            iapply IH m (Nat.lt_succ_self m) (a ++ a2) (dsA ++ ds2) (dsB ++ ds2)
              c'' ρ
              (fun w ρ' => by
                rw [← SpikeVal.merge_merge, ← SpikeVal.merge_merge]
                exact hΦ (SpikeVal.merge ds2 w) ρ') $$ H
          · rw [jumpRedex?_annot_of_not_root _ _ hg, hj] at hjr; cases hjr
          · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
            rw [callRedex?_body_none_of_annot hg hcrB] at h; cases h
          · subst ha hb
            exact absurd hB (by simp [toVal])

/-- `wpt` commutes with the run-time dyn-annotation wrapper: one
    budget unit per wrapper (its eventual merge step; a jump-through
    or a value-forming wrap costs none — the unit is slack there). -/
theorem wpt_annot (ds : List dyn_annotation) (e : CoreExpr) (ρ : EnvStack)
    {k : Nat} {Ψ : SpikeVal → EnvStack → IProp GF} :
    wpt M p Ls Θ k (fun w ρ' => Ψ (SpikeVal.merge ds w) ρ') e ρ ⊢
      wpt M p Ls Θ (k + 1) Ψ (Expr ([] : List annot) (Eannot ds e)) ρ := by
  induction k using Nat.strongRecOn generalizing ds e ρ with
  | ind k IH =>
  cases hv : toVal e with
  | some w =>
    have he := ofVal_of_toVal hv
    subst he
    cases w with
    | pure v =>
      -- the wrap is itself a value: .annot ds v
      rw [wpt_val_eq k (toVal_ofVal (.pure v)),
        wpt_val_eq (k + 1)
          (show toVal (Expr ([] : List annot) (Eannot ds (ofVal (.pure v)))) =
            some (.annot ds v) from rfl)]
      iintro ⟨%hc, H⟩
      isplit
      · ipureintro
        have hc' : 1 ≤ k := by simpa [deliveryCost] using hc
        simp only [deliveryCost_annot]
        omega
      · imod H with H
        imodintro
        rw [show (SpikeVal.annot ds v) = SpikeVal.merge ds (SpikeVal.pure v)
          from rfl]
        iexact H
    | annot ds2 v =>
      -- double annot: one deterministic ANNOTS-merge step to a value
      rw [wpt_val_eq k (toVal_ofVal (.annot ds2 v)),
        wpt_step_eq k
          (show toVal (Expr ([] : List annot)
            (Eannot ds (ofVal (SpikeVal.annot ds2 v)))) = none from rfl)
          (show jumpRedex? (Expr ([] : List annot)
            (Eannot ds (ofVal (SpikeVal.annot ds2 v)))) = none from rfl)
          (show callRedex? (Expr ([] : List annot)
            (Eannot ds (ofVal (SpikeVal.annot ds2 v)))) = none from rfl)]
      iintro ⟨%hc, H⟩ %κ %ℓ %σ₁ %ns %obs %nt Hσ
      have hc2 : 2 ≤ k := by simpa [deliveryCost] using hc
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs', hout⟩ |
          ⟨a2, ds2', c'', hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
          ⟨hg, hcall⟩ | ⟨v', pc, κ, ha, hb, hκ, _⟩
      · rw [show annotRooted (ofVal (SpikeVal.annot ds2 v)) = true from rfl] at hg
        cases hg
      · obtain ⟨rfl, rfl, rfl⟩ : ([] : List annot) = a2 ∧ ds2 = ds2' ∧
            Expr ([] : List annot) (Epure (Pexpr [] () (PEval v))) = c'' := by
          simpa [ofVal] using hb
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs rfl rfl).symm
        obtain ⟨hre, hrρ, hσ⟩ : re = Expr ([] : List annot)
              (Eannot (ds ++ ds2)
                (Expr [] (Epure (Pexpr [] () (PEval v))))) ∧
            rρ = ρ ∧ σ₂ = σ₁ := by
          simpa [Prod.mk.injEq, ofVal] using hout
        subst hre
        obtain rfl : ρ = rρ := hrρ.symm
        obtain rfl : σ₁ = σ₂ := hσ.symm
        imod Hclose with -
        imod H with H
        imodintro
        isplitl [Hσ]
        · iexact Hσ
        · rw [show Expr ([] : List annot) (Eannot (ds ++ ds2)
              (Expr [] (Epure (Pexpr [] () (PEval v))))) =
            ofVal (.annot (ds ++ ds2) v) from rfl]
          iapply wpt_ofVal (.annot (ds ++ ds2) v) ρ
            (by simp only [deliveryCost_annot]; omega)
          rw [show (SpikeVal.annot (ds ++ ds2) v) =
            SpikeVal.merge ds (SpikeVal.annot ds2 v) from rfl]
          iexact H
      · rw [show annotRooted (ofVal (SpikeVal.annot ds2 v)) = true from rfl]
          at hg
        cases hg
      · rw [show annotRooted (ofVal (SpikeVal.annot ds2 v)) = true from rfl] at hg
        cases hg
      · simp [ofVal] at hb
  | none =>
    by_cases hr : annotRooted e = true
    · -- annot-rooted body: the wrap merges; exit through reindexing
      obtain ⟨a2, ds2, c, rfl⟩ : ∃ a2 ds2 c, e = Expr a2 (Eannot ds2 c) := by
        unfold annotRooted at hr
        split at hr
        · rename_i a2 ds2 c
          exact ⟨a2, ds2, c, rfl⟩
        · cases hr
      rw [wpt_step_eq k (toVal_annot_none hv)
        (show jumpRedex? (Expr ([] : List annot)
            (Eannot ds (Expr a2 (Eannot ds2 c)))) = none from
          jumpRedex?_annot_of_root _ _ rfl)
        (show callRedex? (Expr ([] : List annot)
            (Eannot ds (Expr a2 (Eannot ds2 c)))) = none from
          callRedex?_annot_of_root _ _ rfl)]
      iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.annot_inv with ⟨hg, hnj, c', ρ', σ'', hs', hout⟩ |
          ⟨a2', ds2', c'', hb, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
          ⟨hg, hcall⟩ | ⟨v', pc, κ, ha, hb, hκ, _⟩
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
      · obtain ⟨rfl, rfl, rfl⟩ : a2 = a2' ∧ ds2 = ds2' ∧ c = c'' := by
          simpa using hb
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl :=
          (Step.ctl_eq hs (callRedex?_annot_of_root _ _ rfl) (toVal_annot_none hv)).symm
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
          iapply (wpt_annot_reindex
            (Ψ₁ := fun w ρ' => iprop(Ψ (SpikeVal.merge ds w) ρ'))
            a2 ds2 (ds ++ ds2) c ρ
            (fun w ρ' => congrArg (fun z => Ψ z ρ')
              (SpikeVal.merge_merge ds ds2 w))) $$ H
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
      · cases hb
    · -- plain body: jump-clause transfer, or lockstep reduction
      have hr' : annotRooted e = false := by simpa using hr
      have hwrap : toVal (Expr ([] : List annot) (Eannot ds e)) = none :=
        toVal_annot_none hv
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq k hv hjr,
          wpt_jump_eq (k + 1) hwrap
            ((jumpRedex?_annot_of_not_root ([] : List annot) ds hr').trans hjr)]
        iintro H
        imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %h1, %h2, %h3, %h4, HLs⟩
        imodintro
        iexists params, cont, vs, ev0, evs, m
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplit
        · ipureintro; exact Nat.le_trans h4 (Nat.le_succ k)
        iexact HLs
      | none =>
      cases hcr : callRedex? e with
      | some q =>
        rw [wpt_call_eq hv hjr hcr,
          wpt_call_eq hwrap ((jumpRedex?_annot_of_not_root ([] : List annot) ds hr').trans hjr)
            (show callRedex? (Expr ([] : List annot) (Eannot ds e)) =
                some (Cannot [] ds q.1, q.2) by
              rw [callRedex?_annot_of_not_root ([] : List annot) ds hr', hcr]; rfl)]
        simp only [apply_ctx_annot]
        iintro H
        imod H with ⟨%params, %body, %vs, %m, %k', %hb, %h1, %h2, %h3, Hpre, Hcont⟩
        imodintro
        iexists params, body, vs, m, k' + 1, (by omega)
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplitl [Hpre]
        · iexact Hpre
        iintro %ret Hpost
        ihave H' := Hcont $$ %ret Hpost
        iapply IH k' (by omega) ds (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ρ $$ H'
      | none =>
        cases k with
        | zero =>
          rw [wpt_zero_step_eq hv hjr hcr]
          iintro %h
          exact h.elim
        | succ m =>
          rw [wpt_step_eq m hv hjr hcr,
            wpt_step_eq (m + 1) hwrap
              ((jumpRedex?_annot_of_not_root ([] : List annot) ds hr').trans
                hjr) (callRedex?_annot_none hcr)]
          iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
          imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
          imodintro
          isplit
          · ipureintro
            obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
            exact ⟨[], ⟨Expr ([] : List annot) (Eannot ds e'.e), e'.ρ, ⟨κ, p, ℓ⟩, M⟩, _, [],
              ⟨Step.annot_ctx hjr hr' (hstep.1.retag hcr hv), rfl, rfl⟩⟩
          iintro %e₂ %σ₂ %eₜ %HstepW
          obtain ⟨hstepW, hlbl, rfl⟩ := HstepW
          rcases hstepW.annot_inv with ⟨hg, hnj, e'', ρ', σ'', hs, hout⟩ |
              ⟨a2, ds2, c, heq, hout⟩ |
              ⟨l, pes, params, cont, vs, _, _, hg, hj, _, _, _, _⟩ |
              ⟨hg, hcall⟩ | ⟨v', pc, κ, ha, hb, hκ, _⟩
          · obtain ⟨e₂e, e₂ρ, e₂ctl, e₂M⟩ := e₂
            simp only at hlbl
            obtain rfl : M = e₂M := hlbl.symm
            obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = e₂ctl :=
              (Step.ctl_eq hstepW (callRedex?_annot_none hcr) hwrap).symm
            obtain ⟨he, hρ, hσ⟩ : e₂e = Expr ([] : List annot) (Eannot ds e'') ∧
                e₂ρ = ρ' ∧ σ₂ = σ'' := by
              simpa [Prod.mk.injEq] using hout
            subst he hρ hσ
            imod H $$ %(⟨e'', e₂ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) %_ %([]) %⟨hs, rfl, rfl⟩
              with ⟨$, H⟩
            imodintro
            iapply IH m (Nat.lt_succ_self m) ds e'' e₂ρ $$ H
          · exact absurd heq (by
              intro heq
              rw [heq] at hr'
              simp [annotRooted] at hr')
          · rw [hjr] at hj; cases hj
          · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
            rw [hcr] at h; cases h
          · rw [hb] at hv; simp [toVal] at hv

/-! ## THE TOTAL SEQUENCING RULES (budgets compose additively; the
bound value's delivery cost prepays the beta and — for annot
values — the wrapper unit) -/

/-- The jump-clause transfer through an Esseq frame with budget
    weakening (shared by all three sequencing rules; the frame is
    DISCARDED by the jump, so the clause formulas differ only in the
    budget bound). -/
theorem wpt_jump_frame_sseq {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (pat : pattern) {e1 : CoreExpr} (e2 : CoreExpr)
    (ρ : EnvStack) {l : sym} {pes : List (generic_pexpr Unit sym)}
    {k k' : Nat} (hkk : k ≤ k')
    (htv : toVal e1 = none) (hjr : jumpRedex? e1 = some (l, pes)) :
    wpt M p Ls Θ k Ψ₁ e1 ρ ⊢
      wpt M p Ls Θ k' Ψ₂ (Expr a (Esseq pat e1 e2)) ρ := by
  rw [wpt_jump_eq (Ψ := Ψ₁) k htv hjr,
    wpt_jump_eq (Ψ := Ψ₂) k' (toVal_sseq_node a pat e1 e2)
      (by rw [jumpRedex?_sseq]; exact hjr)]
  iintro H
  imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %h1, %h2, %h3, %h4, HLs⟩
  imodintro
  iexists params, cont, vs, ev0, evs, m
  isplit
  · ipureintro; exact h1
  isplit
  · ipureintro; exact h2
  isplit
  · ipureintro; exact h3
  isplit
  · ipureintro; exact Nat.le_trans h4 hkk
  iexact HLs

/-- THE TOTAL SEQUENCING RULE at the wildcard pattern: budgets add.
    (Total analog of `wps_seq`; the Löb of the wps proof becomes
    strong induction on e1's budget.) -/
theorem wpt_seq {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (k1 k2 : Nat) :
    wpt M p Ls Θ k1 (fun w ρ' => wpt M p Ls Θ k2
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wpt M p Ls Θ (k1 + k2) Ψ
        (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
        (ev0 :: evs) := by
  induction k1 using Nat.strongRecOn generalizing e1 ev0 evs with
  | ind k1 IH =>
  cases htv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k1 (toVal_ofVal w)]
    cases k1 with
    | zero =>
      iintro ⟨%hc, -⟩
      exact absurd hc (by cases w <;> simp [deliveryCost])
    | succ m =>
      rw [show m + 1 + k2 = (m + k2) + 1 by omega,
        wpt_step_eq (m + k2)
          (toVal_sseq_node a (Pattern pa (CaseBase (none, bty))) (ofVal w) e2)
          (by rw [jumpRedex?_sseq, jumpRedex?_ofVal]) (by simp)]
      iintro ⟨%hc, H⟩ %κ %ℓ %σ₁ %ns %obs %nt Hσ
      imod H with H
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        cases w with
        | pure v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_pure, rfl, rfl⟩⟩
        | annot ds v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_annot, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
          ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds, v, _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
          ⟨_, _, _, _, _, _, hpat, _, _, _⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
      · -- LETS-PURE: successor (e2, ρ, σ)
        obtain rfl : w = .pure v := by
          cases w with
          | pure v' => simpa [ofVal] using he1
          | annot ds' v' => exact absurd he1 (by simp [ofVal])
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (by simp) (toVal_sseq_node _ _ _ _)).symm
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
          iapply wpt_mono_k (Nat.le_add_left k2 m) e2 (ev0 :: evs) $$ H
      · -- LETS-ANNOT: successor ({ds}e2, ρ, σ); exit through wpt_annot
        obtain rfl : w = .annot ds v := by
          cases w with
          | pure v' => exact absurd he1 (by simp [ofVal])
          | annot ds' v' =>
            obtain ⟨h1, h2⟩ : ds' = ds ∧ v' = v := by simpa [ofVal] using he1
            rw [h1, h2]
        have hm : 1 ≤ m := by
          have : (2 : Nat) ≤ m + 1 := by simpa [deliveryCost] using hc
          omega
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (by simp) (toVal_sseq_node _ _ _ _)).symm
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
          iapply wpt_mono_k (show k2 + 1 ≤ m + k2 by omega) _ _
          iapply wpt_annot ds e2 (ev0 :: evs) $$ H
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        simp at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      exact wpt_jump_frame_sseq a _ e2 _ (Nat.le_add_right k1 k2) htv hjr
    | none =>
    cases hcr : callRedex? e1 with
    | some q =>
      rw [wpt_call_eq htv hjr hcr,
        wpt_call_eq (toVal_sseq_node a (Pattern pa (CaseBase (none, bty))) e1 e2)
          (by rw [jumpRedex?_sseq]; exact hjr)
          (show callRedex? (Expr a (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2)) =
              some (Csseq a (Pattern pa (CaseBase (none, bty))) q.1 e2, q.2) by
            rw [callRedex?_sseq, hcr]; rfl)]
      simp only [apply_ctx_sseq]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k', %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k' + k2, (by omega)
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k' (by omega) (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ev0 evs $$ H'
    | none =>
      cases k1 with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq m htv hjr hcr,
          show m + 1 + k2 = (m + k2) + 1 by omega,
          wpt_step_eq (m + k2)
            (toVal_sseq_node a (Pattern pa (CaseBase (none, bty))) e1 e2)
            (by rw [jumpRedex?_sseq, hjr]) (callRedex?_sseq_none hcr)]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨[], ⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              r'.e e2), r'.ρ, ⟨κ, p, ℓ⟩, M⟩, σ', [],
            ⟨Step.sseq_ctx hjr htv (hs'.retag hcr htv), rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
            ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
            ⟨_, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
            ⟨_, _, _, _, _, _, hpat, _, _, _⟩ |
            hcall
        · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'
          obtain ⟨re, rρ, rctl, rM⟩ := r
          simp only at hlbl
          obtain rfl : M = rM := hlbl.symm
          obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (callRedex?_sseq_none hcr) (toVal_sseq_node _ _ _ _)).symm
          obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Esseq (Pattern pa
              (CaseBase (none, bty))) e1' e2) ∧ rρ = ev0' :: evs ∧
              σ₂ = σ'' := by
            simpa [Prod.mk.injEq] using hout
          subst hre hrρ hσ
          imod H $$ %(⟨e1', ev0' :: evs, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) %σ₂ %([] : List CoreRt)
            %⟨hs', rfl, rfl⟩ with ⟨$, H⟩
          imodintro
          iapply IH m (Nat.lt_succ_self m) e1' ev0' evs $$ H
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [hjr] at hj; cases hj
        · exact (specPat_ne_base hpat).elim
        · exact (specPat_ne_base hpat).elim
        · exact (symPat_ne_base hpat).elim
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [hcr] at h; cases h

/-- The jump-clause transfer through an Ewseq frame (the `wpt_jump_frame_sseq`
    twin). -/
theorem wpt_jump_frame_wseq {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (pat : pattern) {e1 : CoreExpr} (e2 : CoreExpr)
    (ρ : EnvStack) {l : sym} {pes : List (generic_pexpr Unit sym)}
    {k k' : Nat} (hkk : k ≤ k')
    (htv : toVal e1 = none) (hjr : jumpRedex? e1 = some (l, pes)) :
    wpt M p Ls Θ k Ψ₁ e1 ρ ⊢
      wpt M p Ls Θ k' Ψ₂ (Expr a (Ewseq pat e1 e2)) ρ := by
  rw [wpt_jump_eq (Ψ := Ψ₁) k htv hjr,
    wpt_jump_eq (Ψ := Ψ₂) k' (toVal_wseq_node a pat e1 e2)
      (by rw [jumpRedex?_wseq]; exact hjr)]
  iintro H
  imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %h1, %h2, %h3, %h4, HLs⟩
  imodintro
  iexists params, cont, vs, ev0, evs, m
  isplit
  · ipureintro; exact h1
  isplit
  · ipureintro; exact h2
  isplit
  · ipureintro; exact h3
  isplit
  · ipureintro; exact Nat.le_trans h4 hkk
  iexact HLs

/-- THE TOTAL WEAK-SEQUENCING RULE at the wildcard pattern (the
    `wps_wseq` twin, QA-1/M-3 — the `wpt_seq` clone through the Cwseq
    frame; budgets add). -/
theorem wpt_wseq {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (bty : core_base_type) (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (k1 k2 : Nat) :
    wpt M p Ls Θ k1 (fun w ρ' => wpt M p Ls Θ k2
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wpt M p Ls Θ (k1 + k2) Ψ
        (Expr a (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2))
        (ev0 :: evs) := by
  induction k1 using Nat.strongRecOn generalizing e1 ev0 evs with
  | ind k1 IH =>
  cases htv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k1 (toVal_ofVal w)]
    cases k1 with
    | zero =>
      iintro ⟨%hc, -⟩
      exact absurd hc (by cases w <;> simp [deliveryCost])
    | succ m =>
      rw [show m + 1 + k2 = (m + k2) + 1 by omega,
        wpt_step_eq (m + k2)
          (toVal_wseq_node a (Pattern pa (CaseBase (none, bty))) (ofVal w) e2)
          (by rw [jumpRedex?_wseq, jumpRedex?_ofVal]) (by simp)]
      iintro ⟨%hc, H⟩ %κ %ℓ %σ₁ %ns %obs %nt Hσ
      imod H with H
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        cases w with
        | pure v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.wseq_pure, rfl, rfl⟩⟩
        | annot ds v => exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.wseq_annot, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
          ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds, v, _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
      · -- LETS-PURE: successor (e2, ρ, σ)
        obtain rfl : w = .pure v := by
          cases w with
          | pure v' => simpa [ofVal] using he1
          | annot ds' v' => exact absurd he1 (by simp [ofVal])
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (by simp) (toVal_wseq_node _ _ _ _)).symm
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
          iapply wpt_mono_k (Nat.le_add_left k2 m) e2 (ev0 :: evs) $$ H
      · -- LETS-ANNOT: successor ({ds}e2, ρ, σ); exit through wpt_annot
        obtain rfl : w = .annot ds v := by
          cases w with
          | pure v' => exact absurd he1 (by simp [ofVal])
          | annot ds' v' =>
            obtain ⟨h1, h2⟩ : ds' = ds ∧ v' = v := by simpa [ofVal] using he1
            rw [h1, h2]
        have hm : 1 ≤ m := by
          have : (2 : Nat) ≤ m + 1 := by simpa [deliveryCost] using hc
          omega
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (by simp) (toVal_wseq_node _ _ _ _)).symm
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
          iapply wpt_mono_k (show k2 + 1 ≤ m + k2 by omega) _ _
          iapply wpt_annot ds e2 (ev0 :: evs) $$ H
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        simp at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      exact wpt_jump_frame_wseq a _ e2 _ (Nat.le_add_right k1 k2) htv hjr
    | none =>
    cases hcr : callRedex? e1 with
    | some q =>
      rw [wpt_call_eq htv hjr hcr,
        wpt_call_eq (toVal_wseq_node a (Pattern pa (CaseBase (none, bty))) e1 e2)
          (by rw [jumpRedex?_wseq]; exact hjr)
          (show callRedex? (Expr a (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2)) =
              some (Cwseq a (Pattern pa (CaseBase (none, bty))) q.1 e2, q.2) by
            rw [callRedex?_wseq, hcr]; rfl)]
      simp only [apply_ctx_wseq]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k', %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k' + k2, (by omega)
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k' (by omega) (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ev0 evs $$ H'
    | none =>
      cases k1 with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq m htv hjr hcr,
          show m + 1 + k2 = (m + k2) + 1 by omega,
          wpt_step_eq (m + k2)
            (toVal_wseq_node a (Pattern pa (CaseBase (none, bty))) e1 e2)
            (by rw [jumpRedex?_wseq, hjr]) (callRedex?_wseq_none hcr)]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨[], ⟨Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
              r'.e e2), r'.ρ, ⟨κ, p, ℓ⟩, M⟩, σ', [],
            ⟨Step.wseq_ctx hjr htv (hs'.retag hcr htv), rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
            ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            hcall
        · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'
          obtain ⟨re, rρ, rctl, rM⟩ := r
          simp only at hlbl
          obtain rfl : M = rM := hlbl.symm
          obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (callRedex?_wseq_none hcr) (toVal_wseq_node _ _ _ _)).symm
          obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Ewseq (Pattern pa
              (CaseBase (none, bty))) e1' e2) ∧ rρ = ev0' :: evs ∧
              σ₂ = σ'' := by
            simpa [Prod.mk.injEq] using hout
          subst hre hrρ hσ
          imod H $$ %(⟨e1', ev0' :: evs, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) %σ₂ %([] : List CoreRt)
            %⟨hs', rfl, rfl⟩ with ⟨$, H⟩
          imodintro
          iapply IH m (Nat.lt_succ_self m) e1' ev0' evs $$ H
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [hjr] at hj; cases hj
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [hcr] at h; cases h

/-- THE TOTAL Specified-binder sequencing rule (total analog of
    `wps_seq_spec`). -/
theorem wpt_seq_spec {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa pb : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (k1 k2 : Nat) :
    wpt M p Ls Θ k1 (fun w ρ' => iprop(∃ (ov : object_value),
        ⌜w.val = Vloaded (LVspecified ov)⌝ ∗
        wpt M p Ls Θ k2 (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2
          (update_env (specPat pa pb x bty) (Vloaded (LVspecified ov)) ρ')))
      e1 (ev0 :: evs) ⊢
      wpt M p Ls Θ (k1 + k2) Ψ (Expr a (Esseq (specPat pa pb x bty) e1 e2))
        (ev0 :: evs) := by
  induction k1 using Nat.strongRecOn generalizing e1 ev0 evs with
  | ind k1 IH =>
  cases htv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k1 (toVal_ofVal w)]
    cases k1 with
    | zero =>
      iintro ⟨%hc, -⟩
      exact absurd hc (by cases w <;> simp [deliveryCost])
    | succ m =>
      rw [show m + 1 + k2 = (m + k2) + 1 by omega,
        wpt_step_eq (m + k2)
          (toVal_sseq_node a (specPat pa pb x bty) (ofVal w) e2)
          (by rw [jumpRedex?_sseq, jumpRedex?_ofVal]) (by simp)]
      iintro ⟨%hc, H⟩ %κ %ℓ %σ₁ %ns %obs %nt Hσ
      imod H with ⟨%ov, %hval, Hinner⟩
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      cases w with
      | pure v =>
        obtain rfl : v = Vloaded (LVspecified ov) := hval
        isplitr
        · ipureintro
          exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_spec_pure, rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
            ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
            ⟨_, _, _, v', _, _, hpat, he1, _, hout⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
            ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
            ⟨_, _, _, _, _, _, hpat, _, _, _⟩ |
            hcall
        · rw [toVal_ofVal] at hnv'; cases hnv'
        · exact (specPat_ne_base hpat.symm).elim
        · exact (specPat_ne_base hpat.symm).elim
        · rw [jumpRedex?_ofVal] at hj; cases hj
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
          obtain rfl : ov = ov' := by simpa [ofVal] using he1
          obtain ⟨re, rρ, rctl, rM⟩ := r
          simp only at hlbl
          obtain rfl : M = rM := hlbl.symm
          obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (by simp) (toVal_sseq_node _ _ _ _)).symm
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
            iapply wpt_mono_k (Nat.le_add_left k2 m) e2 _ $$ Hinner
        · exact absurd he1 (by simp [ofVal])
        · exact (symPat_ne_spec hpat).elim
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          simp at h
      | annot ds v =>
        obtain rfl : v = Vloaded (LVspecified ov) := hval
        have hm : 1 ≤ m := by
          have : (2 : Nat) ≤ m + 1 := by simpa [deliveryCost] using hc
          omega
        isplitr
        · ipureintro
          exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_spec_annot, rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
            ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
            ⟨_, _, _, v', _, _, hpat, he1, _, hout⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
            ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
            ⟨_, _, _, _, _, _, hpat, _, _, _⟩ |
            hcall
        · rw [toVal_ofVal] at hnv'; cases hnv'
        · exact (specPat_ne_base hpat.symm).elim
        · exact (specPat_ne_base hpat.symm).elim
        · rw [jumpRedex?_ofVal] at hj; cases hj
        · exact absurd he1 (by simp [ofVal])
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := specPat_inj hpat
          obtain ⟨rfl, rfl⟩ : ds = ds' ∧ ov = ov' := by
            simpa [ofVal] using he1
          obtain ⟨re, rρ, rctl, rM⟩ := r
          simp only at hlbl
          obtain rfl : M = rM := hlbl.symm
          obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (by simp) (toVal_sseq_node _ _ _ _)).symm
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
            iapply wpt_mono_k (show k2 + 1 ≤ m + k2 by omega) _ _
            iapply wpt_annot ds e2 _ $$ Hinner
        · exact (symPat_ne_spec hpat).elim
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          simp at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      exact wpt_jump_frame_sseq a _ e2 _ (Nat.le_add_right k1 k2) htv hjr
    | none =>
    cases hcr : callRedex? e1 with
    | some q =>
      rw [wpt_call_eq htv hjr hcr,
        wpt_call_eq (toVal_sseq_node a (specPat pa pb x bty) e1 e2)
          (by rw [jumpRedex?_sseq]; exact hjr)
          (show callRedex? (Expr a (Esseq (specPat pa pb x bty) e1 e2)) =
              some (Csseq a (specPat pa pb x bty) q.1 e2, q.2) by
            rw [callRedex?_sseq, hcr]; rfl)]
      simp only [apply_ctx_sseq]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k', %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k' + k2, (by omega)
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k' (by omega) (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ev0 evs $$ H'
    | none =>
      cases k1 with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq m htv hjr hcr,
          show m + 1 + k2 = (m + k2) + 1 by omega,
          wpt_step_eq (m + k2)
            (toVal_sseq_node a (specPat pa pb x bty) e1 e2)
            (by rw [jumpRedex?_sseq, hjr]) (callRedex?_sseq_none hcr)]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨[], ⟨Expr a (Esseq (specPat pa pb x bty)
              r'.e e2), r'.ρ, ⟨κ, p, ℓ⟩, M⟩, σ', [],
            ⟨Step.sseq_ctx hjr htv (hs'.retag hcr htv), rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
            ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
            ⟨_, _, _, _, _, _, _, he1, _, _⟩ |
            hcall
        · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'
          obtain ⟨re, rρ, rctl, rM⟩ := r
          simp only at hlbl
          obtain rfl : M = rM := hlbl.symm
          obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (callRedex?_sseq_none hcr) (toVal_sseq_node _ _ _ _)).symm
          obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Esseq (specPat pa pb x bty)
              e1' e2) ∧ rρ = ev0' :: evs ∧
              σ₂ = σ'' := by
            simpa [Prod.mk.injEq] using hout
          subst hre hrρ hσ
          imod H $$ %(⟨e1', ev0' :: evs, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) %σ₂ %([] : List CoreRt)
            %⟨hs', rfl, rfl⟩ with ⟨$, H⟩
          imodintro
          iapply IH m (Nat.lt_succ_self m) e1' ev0' evs $$ H
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [hjr] at hj; cases hj
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [hcr] at h; cases h

/-- THE TOTAL plain-symbol-binder sequencing rule (total analog of
    `wps_seq_sym`). -/
theorem wpt_seq_sym {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (k1 k2 : Nat) :
    wpt M p Ls Θ k1 (fun w ρ' => iprop(∃ (v : value),
        ⌜w = SpikeVal.pure v⌝ ∗
        wpt M p Ls Θ k2 Ψ e2 (update_env (symPat pa x bty) v ρ')))
      e1 (ev0 :: evs) ⊢
      wpt M p Ls Θ (k1 + k2) Ψ (Expr a (Esseq (symPat pa x bty) e1 e2))
        (ev0 :: evs) := by
  induction k1 using Nat.strongRecOn generalizing e1 ev0 evs with
  | ind k1 IH =>
  cases htv : toVal e1 with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k1 (toVal_ofVal w)]
    cases k1 with
    | zero =>
      iintro ⟨%hc, -⟩
      exact absurd hc (by cases w <;> simp [deliveryCost])
    | succ m =>
      rw [show m + 1 + k2 = (m + k2) + 1 by omega,
        wpt_step_eq (m + k2)
          (toVal_sseq_node a (symPat pa x bty) (ofVal w) e2)
          (by rw [jumpRedex?_sseq, jumpRedex?_ofVal]) (by simp)]
      iintro ⟨%hc, H⟩ %κ %ℓ %σ₁ %ns %obs %nt Hσ
      imod H with ⟨%v, %hval, Hinner⟩
      subst hval
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _, _⟩, _, [], ⟨Step.sseq_sym_pure, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
          ⟨_, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨_, _, _, v', _, _, hpat, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
          ⟨pa', pb', x', bty', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', pb', x', bty', ds', ov', _, _, hpat, he1, _, hout⟩ |
          ⟨pa', x', bty', v', _, _, hpat, he1, _, hout⟩ |
          hcall
      · rw [toVal_ofVal] at hnv'; cases hnv'
      · exact (symPat_ne_base hpat.symm).elim
      · exact (symPat_ne_base hpat.symm).elim
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (symPat_ne_spec hpat.symm).elim
      · exact (symPat_ne_spec hpat.symm).elim
      · obtain ⟨rfl, rfl, rfl⟩ := symPat_inj hpat
        obtain rfl : v = v' := by simpa [ofVal] using he1
        obtain ⟨re, rρ, rctl, rM⟩ := r
        simp only at hlbl
        obtain rfl : M = rM := hlbl.symm
        obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (by simp) (toVal_sseq_node _ _ _ _)).symm
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
        · iapply wpt_mono_k (Nat.le_add_left k2 m) e2 _ $$ Hinner
      · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
        simp at h
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      exact wpt_jump_frame_sseq a _ e2 _ (Nat.le_add_right k1 k2) htv hjr
    | none =>
    cases hcr : callRedex? e1 with
    | some q =>
      rw [wpt_call_eq htv hjr hcr,
        wpt_call_eq (toVal_sseq_node a (symPat pa x bty) e1 e2)
          (by rw [jumpRedex?_sseq]; exact hjr)
          (show callRedex? (Expr a (Esseq (symPat pa x bty) e1 e2)) =
              some (Csseq a (symPat pa x bty) q.1 e2, q.2) by
            rw [callRedex?_sseq, hcr]; rfl)]
      simp only [apply_ctx_sseq]
      iintro H
      imod H with ⟨%params, %body, %vs, %m, %k', %hb, %h1, %h2, %h3, Hpre, Hcont⟩
      imodintro
      iexists params, body, vs, m, k' + k2, (by omega)
      isplit
      · ipureintro; exact h1
      isplit
      · ipureintro; exact h2
      isplit
      · ipureintro; exact h3
      isplitl [Hpre]
      · iexact Hpre
      iintro %ret Hpost
      ihave H' := Hcont $$ %ret Hpost
      iapply IH k' (by omega) (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval ret))))) ev0 evs $$ H'
    | none =>
      cases k1 with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq m htv hjr hcr,
          show m + 1 + k2 = (m + k2) + 1 by omega,
          wpt_step_eq (m + k2)
            (toVal_sseq_node a (symPat pa x bty) e1 e2)
            (by rw [jumpRedex?_sseq, hjr]) (callRedex?_sseq_none hcr)]
        iintro H %κ %ℓ %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨[], ⟨Expr a (Esseq (symPat pa x bty)
              r'.e e2), r'.ρ, ⟨κ, p, ℓ⟩, M⟩, σ', [],
            ⟨Step.sseq_ctx hjr htv (hs'.retag hcr htv), rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
        obtain ⟨hs, hlbl, rfl⟩ := Hstep
        rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hs', hout⟩ |
            ⟨_, _, v, _, _, _, he1, _, _⟩ | ⟨_, _, ds, v, _, _, _, he1, _, _⟩ |
            ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩ |
            ⟨_, _, _, _, _, _, _, _, he1, _, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, he1, _, _⟩ |
            ⟨_, _, _, _, _, _, _, he1, _, _⟩ |
            hcall
        · obtain ⟨ev0', rfl⟩ := Step.env_cons hs'
          obtain ⟨re, rρ, rctl, rM⟩ := r
          simp only at hlbl
          obtain rfl : M = rM := hlbl.symm
          obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl := (Step.ctl_eq hs (callRedex?_sseq_none hcr) (toVal_sseq_node _ _ _ _)).symm
          obtain ⟨hre, hrρ, hσ⟩ : re = Expr a (Esseq (symPat pa x bty)
              e1' e2) ∧ rρ = ev0' :: evs ∧
              σ₂ = σ'' := by
            simpa [Prod.mk.injEq] using hout
          subst hre hrρ hσ
          imod H $$ %(⟨e1', ev0' :: evs, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) %σ₂ %([] : List CoreRt)
            %⟨hs', rfl, rfl⟩ with ⟨$, H⟩
          imodintro
          iapply IH m (Nat.lt_succ_self m) e1' ev0' evs $$ H
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [hjr] at hj; cases hj
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · obtain ⟨_, _, _, h⟩ := hcall.callRedex?_some
          rw [hcr] at h; cases h

/-! ## The generic typed-subrange rules at the total stratum
(corollaries of the atomic step specifications `loadAt_atomic` /
`storeAt_atomic` (Rules.lean) through `wpt_of_atomic`; the successor
value's delivery cost (2: an annot value) plus the access step itself
price the rules at 3 budget units) -/

/-- GENERIC TYPED SUBRANGE LOAD (total form; cost 3 ≤ k). -/
theorem wpt_load_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (mo : memory_order) (dqm dqb : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(pointsToView M.tagDefs (GF := GF) id a aty off dqm dqb vty bs ∗
      (∀ fp, pointsToView M.tagDefs id a aty off dqm dqb vty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wpt M p Ls Θ k Ψ (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => loadAt_atomic loc ann id a aty off vty mo dqm dqb bs ρ hdec htrap)
    rfl rfl rfl hk
  isplitl [Hv]
  · iexact Hv
  · iintro %w ⟨%fp, %hw, Hv'⟩
    subst hw
    iapply HΨ $$ Hv'

/-- GENERIC FULL-OWNERSHIP TYPED SUBRANGE STORE (total form; cost
    3 ≤ k). -/
theorem wpt_store_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order) (dqm : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hst : StorableView M.tagDefs vty mv) :
    iprop(pointsToView M.tagDefs (GF := GF) id a aty off dqm (.own 1) vty bs ∗
      (∀ fp, pointsToView M.tagDefs id a aty off dqm (.own 1) vty
          (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => storeAt_atomic loc ann id a aty off vty cv mo dqm bs ρ hmv hst)
    rfl rfl rfl hk
  isplitl [Hv]
  · iexact Hv
  · iintro %w ⟨%fp, %hw, Hv'⟩
    subst hw
    iapply HΨ $$ Hv'

/-- Interior typed load THROUGH whole-cell ownership (total form;
    derived from `wpt_load_at` by the same subrange split/join glue
    as `wps_load_cell_at`). -/
theorem wpt_load_cell_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hbound : off + CerbMem.sizeofCtype M.tagDefs vty ≤ CerbMem.sizeofCtype M.tagDefs aty)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(cellOwn M.tagDefs (GF := GF) id dq (SpikeCell.mk a aty bs) ∗
      (∀ fp, cellOwn M.tagDefs id dq (SpikeCell.mk a aty bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wpt M p Ls Θ k Ψ (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo)
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
  iapply wpt_load_at loc ann id a aty off vty mo dq dq
    ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) ρ hk hdec htrap
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

/-- Interior typed store THROUGH whole-cell ownership (total form;
    the spliced-image recomposition of `wps_store_cell_at`). -/
theorem wpt_store_cell_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (aty : ctype) (off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hbound : off + CerbMem.sizeofCtype M.tagDefs vty ≤ CerbMem.sizeofCtype M.tagDefs aty)
    (hst : StorableView M.tagDefs vty mv)
    (hdec' : decIndep M.tagDefs a aty
      (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs)) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a aty bs) ∗
      (∀ fp, cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a aty
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo)
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
  iapply wpt_store_at loc ann id a aty off vty cv mo (.own 1)
    ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) ρ hk hmv hst
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

/-! ## THE REGION ACCESS RULES at the total stratum (kill/free arc K5;
corollaries of `regionLoadAt_atomic`/`regionStoreAt_atomic` through
`wpt_of_atomic`, priced at 3 as the object `_at` rules; the whole-region
forms by `regionOwn_carve`/`regionOwn_uncarve` as at `wps`) -/

/-- TYPED SUBRANGE LOAD THROUGH A REGION (total form; cost 3 ≤ k). -/
theorem wpt_load_region_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (mo : memory_order) (dqm dqb : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(typedRegionView M.tagDefs (GF := GF) id a n off dqm dqb vty bs ∗
      (∀ fp, typedRegionView M.tagDefs id a n off dqm dqb vty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wpt M p Ls Θ k Ψ (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => regionLoadAt_atomic loc ann id a n off vty mo dqm dqb bs ρ hdec htrap)
    rfl rfl rfl hk
  isplitl [Hv]
  · iexact Hv
  · iintro %w ⟨%fp, %hw, Hv'⟩
    subst hw
    iapply HΨ $$ Hv'

/-- FULL-OWNERSHIP TYPED SUBRANGE STORE THROUGH A REGION (total form;
    cost 3 ≤ k). -/
theorem wpt_store_region_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order) (dqm : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hst : StorableView M.tagDefs vty mv) :
    iprop(typedRegionView M.tagDefs (GF := GF) id a n off dqm (.own 1) vty bs ∗
      (∀ fp, typedRegionView M.tagDefs id a n off dqm (.own 1) vty
          (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => regionStoreAt_atomic loc ann id a n off vty cv mo dqm bs ρ hmv hst)
    rfl rfl rfl hk
  isplitl [Hv]
  · iexact Hv
  · iintro %w ⟨%fp, %hw, Hv'⟩
    subst hw
    iapply HΨ $$ Hv'

/-- Interior typed load THROUGH whole-region ownership (total form;
    derived from `wpt_load_region_at` by carve/uncarve). -/
theorem wpt_load_regionOwn_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hbound : off + CerbMem.sizeofCtype M.tagDefs vty ≤ n)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      vty ((bs.drop off).take (CerbMem.sizeofCtype M.tagDefs vty)) = mv)
    (htrap : loadTrapV vty mv = false) :
    iprop(regionOwn (GF := GF) id a n dq bs ∗
      (∀ fp, regionOwn id a n dq bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wpt M p Ls Θ k Ψ (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo)
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
  iapply wpt_load_region_at loc ann id a n off vty mo dq dq _ ρ hk hdec htrap
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

/-- Interior typed store THROUGH whole-region ownership (total form; the
    image spliced at the accessed subrange). -/
theorem wpt_store_regionOwn_at {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (n off : Nat) (vty : ctype)
    (cv : value) (mo : memory_order)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ vty)) cv = some mv)
    (hbound : off + CerbMem.sizeofCtype M.tagDefs vty ≤ n)
    (hst : StorableView M.tagDefs vty mv) :
    iprop(regionOwn (GF := GF) id a n (.own 1) bs ∗
      (∀ fp, regionOwn id a n (.own 1)
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo)
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
  iapply wpt_store_region_at loc ann id a n off vty cv mo (.own 1) _ ρ hk hmv hst
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


/-- WHOLE-CELL STORE at the total stratum (the `wps_store` twin —
    Phase 5, the counter loop's total lane; named `wpt_store`
    before QA-1/Q10): the `off := 0` instance of the generic subrange
    rule, with the splice collapsed to the stored image
    (`|img| = |bs| = sizeof ty`) and the write-side
    decode-independence supplied by `StorableAt.stored_dec`. -/
theorem wpt_store {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {k : Nat} (hk : 3 ≤ k)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (storeExpr loc ann ty pv cv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => store_atomic loc ann ty pv cv mo mv bs ρ hmv hst) rfl rfl rfl hk
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%fp, %hw, Hpt'⟩
    subst hw
    iapply HΨ $$ Hpt'

/-- WHOLE-CELL LOAD at the total stratum (the `wps_load` twin,
    QA-1/M-3): `load_atomic` lifted; `htrap` excludes the `_Bool`
    trap-representation kill exactly as `wps_load`'s. -/
theorem wpt_load {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {k : Nat} (hk : 3 ≤ k)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv dq ty bs ∗
      (∀ fp, pointsToCell M.tagDefs pv dq ty bs -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] (loadedVal M.tagDefs pv ty bs)) ρ)) ⊢
      wpt M p Ls Θ k Ψ (loadExpr loc ann ty pv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => load_atomic loc ann ty pv mo dq bs ρ htrap) rfl rfl rfl hk
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%fp, %hw, Hpt'⟩
    subst hw
    iapply HΨ $$ Hpt'

/-- THE DISPOSE RULE at the total stratum (kill/free arc K2):
    `kill_atomic` lifted at the derived cost bound `2 ≤ k` — one kill
    step plus the bare unit's delivery (`deliveryCost (.pure Vunit) =
    1`, as `wpt_create`). -/
theorem wpt_kill {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {k : Nat} (hk : 2 ≤ k) (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      ((∃ (id a : Int), ⌜pv = cellPtr id a⌝ ∗ deadObj M.tagDefs id a ty) -∗
        Ψ (SpikeVal.pure Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (killExpr loc ann kind pv) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => kill_atomic loc ann kind pv ty bs ρ hstatic) rfl rfl rfl hk
  isplitl [Hpt]
  · iexact Hpt
  · iintro %w ⟨%hw, Hd⟩
    subst hw
    iapply HΨ $$ Hd

/-- The textbook face at the total stratum: the dead cell dropped. -/
theorem wpt_kill_emp {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (pv : CerbMem.PointerValue) (ty : ctype) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {k : Nat} (hk : 2 ≤ k) (hstatic : is_dynamic kind = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗ Ψ (SpikeVal.pure Vunit) ρ) ⊢
      wpt M p Ls Θ k Ψ (killExpr loc ann kind pv) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_kill loc ann kind pv ty bs ρ hk hstatic
  isplitl [Hpt]
  · iexact Hpt
  · iintro -
    iexact HΨ

/-- THE PUBLIC TOTAL ALLOCATION RULE for DYNAMIC storage (kill/free arc
    K3): `alloc_atomic` lifted at the derived cost bound `2 ≤ k` (one
    alloc step + the bare pointer's delivery, as `wpt_create`). -/
theorem wpt_alloc {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov sprov : CerbMem.Provenance) (alignN sizeN : Int)
    (pref : prefix0) (ρ : EnvStack) {k : Nat} (hk : 2 ≤ k)
    (hcost : 0 < regionCost alignN sizeN) :
    iprop(allocBudget (GF := GF) (regionCost alignN sizeN) ∗
      (∀ (id a : Int),
        (regionOwn id a sizeN.toNat (.own 1) (List.replicate sizeN.toNat undefByte) ∗
          ⌜0 < a ∧ a + (sizeN.toNat : Int) ≤ 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer (cellPtr id a)))) ρ)) ⊢
      wpt M p Ls Θ k Ψ (allocExpr loc ann (.IV aprov alignN) (.IV sprov sizeN) pref) ρ := by
  iintro ⟨Hb, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => alloc_atomic loc ann aprov sprov alignN sizeN pref ρ hcost)
    rfl rfl rfl hk
  isplitl [Hb]
  · iexact Hb
  · iintro %w ⟨%id, %a, %hw, Hr, %hb⟩
    subst hw
    iapply HΨ
    isplitl [Hr]
    · iexact Hr
    · ipureintro
      exact hb

/-- THE FREE RULE at the total stratum (kill/free arc K3): `free_atomic`
    lifted at the derived cost bound `2 ≤ k` — one kill step plus the bare
    unit's delivery (as `wpt_kill`). -/
theorem wpt_free {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (id a : Int) (n : Nat) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {k : Nat} (hk : 2 ≤ k) (hdyn : is_dynamic kind = true) :
    iprop(regionOwn (GF := GF) id a n (.own 1) bs ∗
      (deadRegion id a n -∗ Ψ (SpikeVal.pure Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (killExpr loc ann kind (cellPtr id a)) ρ := by
  iintro ⟨Hr, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => free_atomic loc ann kind id a n bs ρ hdyn) rfl rfl rfl hk
  isplitl [Hr]
  · iexact Hr
  · iintro %w ⟨%hw, Hd⟩
    subst hw
    iapply HΨ $$ Hd

/-- The textbook face at the total stratum: the dead region dropped. -/
theorem wpt_free_emp {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (kind : kill_kind)
    (id a : Int) (n : Nat) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {k : Nat} (hk : 2 ≤ k) (hdyn : is_dynamic kind = true) :
    iprop(regionOwn (GF := GF) id a n (.own 1) bs ∗ Ψ (SpikeVal.pure Vunit) ρ) ⊢
      wpt M p Ls Θ k Ψ (killExpr loc ann kind (cellPtr id a)) ρ := by
  iintro ⟨Hr, HΨ⟩
  iapply wpt_free loc ann kind id a n bs ρ hk hdyn
  isplitl [Hr]
  · iexact Hr
  · iintro -
    iexact HΨ

/-! ## The plain-value forms of the whole-cell small axioms (QA-1/Q12)

The engine's action continuations carry the footprint residue
`DA_pos [] fp` (the REMOVE-ANNOT value protocol); the primitive rules
therefore quantify the footprint in every client proof. For
postconditions that do not read annotations — `Ψ (.annot ds v) ρ = Ψ
(.pure v) ρ`, which every exhibit's `Ψ` satisfies — the textbook forms
follow: `{p ↦ -} store(p, v) {p ↦ v}` with no `∀ fp`. Derived, stated
once each alongside the primitives. -/

/-- The annotation-insensitive postconditions. -/
def AnnotInsensitive {GF : BundledGFunctors} (Ψ : SpikeVal → EnvStack → IProp GF) : Prop :=
  ∀ (ds : List dyn_annotation) (v : value) (ρ : EnvStack), Ψ (.annot ds v) ρ = Ψ (.pure v) ρ

/-- `wpt_store` for an annotation-insensitive postcondition. -/
theorem wpt_store_plain {Ψ : SpikeVal → EnvStack → IProp GF} (hΨ : AnnotInsensitive Ψ)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (mv : CerbMem.MemValue) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {k : Nat} (hk : 3 ≤ k)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ ty)) cv = some mv)
    (hst : StorableAt M.tagDefs ty mv) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own 1) ty bs ∗
      (pointsToCell M.tagDefs pv (.own 1) ty (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (.pure Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (storeExpr loc ann ty pv cv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_store loc ann ty pv cv mo mv bs ρ hk hmv hst
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt'
  rw [hΨ]
  iapply HΨ $$ Hpt'

/-- `wpt_load` for an annotation-insensitive postcondition. -/
theorem wpt_load_plain {Ψ : SpikeVal → EnvStack → IProp GF} (hΨ : AnnotInsensitive Ψ)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pv : CerbMem.PointerValue) (mo : memory_order) (dq : DFrac)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {k : Nat} (hk : 3 ≤ k)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, ty, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv dq ty bs ∗
      (pointsToCell M.tagDefs pv dq ty bs -∗ Ψ (.pure (loadedVal M.tagDefs pv ty bs)) ρ)) ⊢
      wpt M p Ls Θ k Ψ (loadExpr loc ann ty pv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_load loc ann ty pv mo dq bs ρ hk htrap
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt'
  rw [hΨ]
  iapply HΨ $$ Hpt'

/-! ## The allocation rules at the total stratum (alloc arc P1.4)

Total mirror of Wps.lean §CreateRule (RESTATED over the budget at
K2.5): the public `wpt_create` (`allocBudget`-premised, cursor-free
statement, `create_atomic` lifted by `wpt_of_atomic`) and its
plan-shaped reading `wpt_create_of_plan`; the former exact-cursor
`wpt_create_cursor_internal` is RETIRED with the plan.

THE COST BOUND, DERIVED AGAINST THE DRIVER'S ROUNDS (not copied from
the charter): a bare create is one relational create step — the wpt
step clause consumes 1 budget unit, which `wpt_driver_aux` maps to one
iteration of the shipped loop (`loop_step_frag_same` at the create
redex) — and its result is the BARE pure pointer value (`Step.create` —
"a BARE value, no Eannot residue", Step.lean's create docstring), whose
delivery costs `deliveryCost (.pure _) = 1` — one PROGRAM-DONE round
(`loop_step_done`). Total: `2 ≤ k`, the charter's expected minimum,
confirmed (contrast `wpt_store_at`'s `3 ≤ k`: a store's result is an
ANNOT value, whose delivery pays the REMOVE-ANNOT tau first). -/

section CreateRuleT
open Iris.Std.PartialMap

/-- THE PUBLIC TOTAL ALLOCATION RULE (alloc arc P1.4, restated K2.5):
    the total analogue of `wps_create` at the DERIVED cost bound `2 ≤ k`
    (see the section header — one create step + one pure-value delivery
    against the driver's rounds). Statement is cursor-free (the P1 grep test);
    the budget `allocCost ty alignN` buys the create, the continuation
    binds the fresh pointer with full whole-cell ownership and (alloc
    arc P2) its pure machine-address bounds `0 < addrOf p < 2^64`. -/
theorem wpt_create {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (ty : ctype)
    (pref : prefix0) (ρ : EnvStack) {k : Nat} (hk : 2 ≤ k)
    (hsz : 0 < CerbMem.sizeofCtype M.tagDefs ty) (hatom : atomicTy ty = false)
    (hinert : ∀ a : Int, decIndep M.tagDefs a ty
      (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte)) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs ty alignN) ∗
      (∀ p : CerbMem.PointerValue,
        (pointsToCell M.tagDefs p (.own 1) ty
            (List.replicate (CerbMem.sizeofCtype M.tagDefs ty) undefByte) ∗
          ⌜0 < addrOf p ∧ addrOf p < 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer p))) ρ)) ⊢
      wpt M p Ls Θ k Ψ (createExpr loc ann (.IV aprov alignN) ty pref) ρ := by
  iintro ⟨Hb, HΨ⟩
  iapply wpt_of_atomic (fun _ _ => create_atomic loc ann aprov alignN ty pref ρ hsz hatom hinert)
    rfl rfl rfl hk
  isplitl [Hb]
  · iexact Hb
  · iintro %w ⟨%p, %hw, Hpt, %hb⟩
    subst hw
    iapply HΨ
    isplitl [Hpt]
    · iexact Hpt
    · ipureintro
      exact hb

/-- The plan-shaped reading of `wpt_create` (mirror of
    `wps_create_of_plan`): capacity for `req :: rest` buys the head
    request and returns capacity for the rest, by `allocBudget_split`. -/
theorem wpt_create_of_plan {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (req : AllocReq) (rest : List AllocReq)
    (pref : prefix0) (ρ : EnvStack) {k : Nat} (hk : 2 ≤ k)
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
      wpt M p Ls Θ k Ψ (createExpr loc ann (.IV aprov req.align) req.ty pref) ρ := by
  rw [planCost_cons]
  iintro ⟨Hb, HΨ⟩
  icases (allocBudget_split (allocCost M.tagDefs req.ty req.align)
    (planCost M.tagDefs rest)).1 $$ Hb with ⟨Hb, Hrest⟩
  iapply wpt_create loc ann aprov req.align req.ty pref ρ hk hsz hatom hinert
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

end CreateRuleT

/-! ## Total block specifications, total procedure specifications, and THE COLLAPSE into Iris TWP -/

/-- TOTAL BLOCK SPECIFICATIONS: every registered label's body meets
    its OWN variant value `m` (every m at which its precondition is
    claimed). This is the real total rule that replaces the retired
    `blockSpecs_intro_variant`: because the body is verified at
    budget `m` and the jump clause demands `1 + m' ≤ (remaining
    budget) ≤ m`, every back edge carries a strict decrease of the
    well-founded measure — the obligation is structural, not an
    optional hypothesis. Indexed by the procedure `p` whose fiber is
    consulted (C3). -/
abbrev blockSpecsT (M : MachineCtx) (p : Option sym) (Ls : LabelSpecT GF) (Θ : ProcSpecT GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) : IProp GF :=
  iprop(□ ∀ (l : sym) (params : List (sym × core_base_type))
    (cont : CoreExpr) (vs : List value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (m : Nat),
    ⌜lookupLabel (M.labelsAt p) l = some (params, cont)⌝ -∗
      Ls l m vs (ev0 :: evs) -∗
      wpt M p Ls Θ m Ψ cont (bindArgs params vs (ev0 :: evs)))

/-- Introduction from per-label entailments. -/
theorem blockSpecsT_intro {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l params cont vs ev0 evs m,
      lookupLabel (M.labelsAt p) l = some (params, cont) →
      Ls l m vs (ev0 :: evs) ⊢ wpt (GF := GF) M p Ls Θ m Ψ cont
        (bindArgs params vs (ev0 :: evs))) :
    ⊢ blockSpecsT M p Ls Θ Ψ := by
  unfold blockSpecsT
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %m %hQ HLs
  iapply h l params cont vs ev0 evs m hQ $$ HLs

/-- Monotonicity of the block specifications in the postcondition. -/
theorem blockSpecsT_mono {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ w ρ', Ψ₁ w ρ' ⊢ Ψ₂ w ρ') :
    blockSpecsT (GF := GF) M p Ls Θ Ψ₁ ⊢ blockSpecsT M p Ls Θ Ψ₂ := by
  iintro #HB
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %m %hQ HLs
  iapply wpt_mono h m cont (bindArgs params vs (ev0 :: evs))
  iapply HB $$ %l %params %cont %vs %ev0 %evs %m %hQ HLs

/-- FRAMING THE TOTAL BLOCK SPECIFICATIONS. -/
theorem blockSpecsT_frame {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF) :
    blockSpecsT (GF := GF) M p Ls Θ Ψ ⊢
      blockSpecsT M p (frameLsT R Ls) Θ (fun w ρ' => iprop(Ψ w ρ' ∗ R)) := by
  iintro #HB
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %m %hQ ⟨HLs, HR⟩
  ihave HW := HB $$ %l %params %cont %vs %ev0 %evs %m %hQ HLs
  iapply wpt_frame_labels R m cont (bindArgs params vs (ev0 :: evs)) $$ HW HR

/-! ### Total procedure specifications (calls arc C3) -/

/-- TOTAL PROCEDURE SPECIFICATIONS HOLD (the twin of `procSpecs`,
    Wps.lean, at the total stratum): every declared procedure meets its
    table entry at every budget `m`, argument list of the right arity
    and caller environment — a label specification for the activation
    under which its label bodies are verified, and its body verified
    WITHIN BUDGET `m` (its return included) from the precondition. The
    body assumes the table for every call inside, recursive ones
    included, each at ITS budget: the budget split of the call clause
    is what makes a recursive body's total derivation well-founded —
    the recursive activation's `m'` sits strictly inside the caller's
    `m` (`1 + m' + k' ≤ m`). -/
abbrev procSpecsT (M : MachineCtx) (Θ : ProcSpecT GF) : IProp GF :=
  iprop(□ ∀ (f : sym) (params : List (sym × core_base_type)) (body : CoreExpr)
    (m : Nat) (vs : List value) (ρ : EnvStack),
    ⌜lookupProc M.file M.extern f = some (params, body)⌝ -∗ ⌜params.length = vs.length⌝ -∗
    ∃ (Ls : LabelSpecT GF),
      blockSpecsT M (some f) Ls Θ (fun w _ => (Θ f m vs).2 w.val) ∗
      ((Θ f m vs).1 -∗
        wpt M (some f) Ls Θ m (fun w _ => (Θ f m vs).2 w.val) body (procEnv params vs :: ρ)))

/-- The introduction: one label table, per procedure its block
    specifications and one budgeted body proof under the precondition
    (no Löb, no induction — the budget discipline is inside the
    judgment). -/
theorem procSpecsT_intro (Lsₚ : sym → Nat → List value → LabelSpecT GF)
    (hB : ∀ f params body m vs, lookupProc M.file M.extern f = some (params, body) →
      params.length = vs.length →
      ⊢ blockSpecsT (GF := GF) M (some f) (Lsₚ f m vs) Θ (fun w _ => (Θ f m vs).2 w.val))
    (hW : ∀ f params body m vs (ρ : EnvStack),
      lookupProc M.file M.extern f = some (params, body) → params.length = vs.length →
      (Θ f m vs).1 ⊢ wpt (GF := GF) M (some f) (Lsₚ f m vs) Θ m
        (fun w _ => (Θ f m vs).2 w.val) body (procEnv params vs :: ρ)) :
    ⊢ procSpecsT M Θ := by
  unfold procSpecsT
  imodintro
  iintro %f %params %body %m %vs %ρ %hf %hlen
  iexists Lsₚ f m vs
  isplit
  · exact hB f params body m vs hf hlen
  · iintro Hpre
    iapply hW f params body m vs ρ hf hlen $$ Hpre

/-- The empty table is trivially met. -/
theorem procSpecsT_empty : ⊢ procSpecsT (GF := GF) M emptyProcSpecT := by
  unfold procSpecsT
  imodintro
  iintro %f %params %body %m %vs %ρ %_ %_
  iexists (fun _ _ _ _ => iprop(⌜False⌝))
  isplit
  · unfold blockSpecsT
    imodintro
    iintro %l %params' %cont %vs' %ev0 %evs %m' %_ %hF
    exact hF.elim
  · simp only [emptyProcSpecT_fst]
    iintro %hF
    exact hF.elim

/-! ### The return at the raw TWP (the collapse's two devices) -/

/-- THE RETURN ROUND at the raw TWP (`Step.ret`, `Step.ret_inv`). -/
theorem twp_ret {Φ : CoreRVal → IProp GF} (v : value) (ev0 : Fmap sym value)
    (evs : EnvStack) (p₀ : Option sym) (ctx : context)
    (κ : List (Option sym × context)) (q : Option sym) (ℓ : exec_location) :
    WP (⟨apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))), evs, ⟨κ, p₀, ℓ⟩, M⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ [{ Φ }] ⊢
      WP (⟨Expr [] (Epure (Pexpr [] () (PEval v))), ev0 :: evs, ⟨(p₀, ctx) :: κ, q, ℓ⟩, M⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ [{ Φ }] := by
  iintro H
  rw [(twp.unfold (e := (⟨Expr [] (Epure (Pexpr [] () (PEval v))), ev0 :: evs,
    ⟨(p₀, ctx) :: κ, q, ℓ⟩, M⟩ : CoreRt))).to_eq]
  simp only [twp.pre, show ToVal.toVal (Val := CoreRVal) (⟨Expr [] (Epure (Pexpr [] () (PEval v))),
    ev0 :: evs, ⟨(p₀, ctx) :: κ, q, ℓ⟩, M⟩ : CoreRt) = none from rfl]
  iintro %σ₁ %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨⟨_, _, _, _⟩, σ₁, [], ⟨Step.ret, rfl, rfl⟩⟩
  iintro %obs₂ %r %σ₂ %eₜ %Hstep
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  obtain ⟨ev0', evs', heq, hout⟩ := hs.ret_inv
  obtain ⟨rfl, rfl⟩ := List.cons.inj heq
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = apply_ctx ctx (Expr [] (Epure (Pexpr [] () (PEval v)))) ∧
      rρ = evs ∧ rctl = ⟨κ, p₀, ℓ⟩ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre hrρ hrctl
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplit
  · ipureintro
    exact List.empty_eq_nil obs₂
  isplitl [Hσ]
  · simp only [List.length_nil, Nat.add_zero]
    iexact Hσ
  isplitr []
  · iexact H
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

/-- REMOVE-ANNOT under a frame at the raw TWP (`Step.ret_annot`,
    `Step.ret_annot_inv`). -/
theorem twp_ret_annot {Φ : CoreRVal → IProp GF} (ds : List dyn_annotation) (v : value)
    (ρ : EnvStack) (pc : Option sym × context) (κ : List (Option sym × context))
    (q : Option sym) (ℓ : exec_location) :
    WP (⟨Expr [] (Epure (Pexpr [] () (PEval v))), ρ, ⟨pc :: κ, q, ℓ⟩, M⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ [{ Φ }] ⊢
      WP (⟨Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v))))), ρ, ⟨pc :: κ, q, ℓ⟩, M⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ [{ Φ }] := by
  iintro H
  rw [(twp.unfold (e := (⟨Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v))))), ρ,
    ⟨pc :: κ, q, ℓ⟩, M⟩ : CoreRt))).to_eq]
  simp only [twp.pre, show ToVal.toVal (Val := CoreRVal) (⟨Expr [] (Eannot ds
    (Expr [] (Epure (Pexpr [] () (PEval v))))), ρ, ⟨pc :: κ, q, ℓ⟩, M⟩ : CoreRt) = none from rfl]
  iintro %σ₁ %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨⟨_, _, _, _⟩, σ₁, [], ⟨Step.ret_annot, rfl, rfl⟩⟩
  iintro %obs₂ %r %σ₂ %eₜ %Hstep
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  have hout := hs.ret_annot_inv
  obtain ⟨re, rρ, rctl, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
  obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = Expr [] (Epure (Pexpr [] () (PEval v))) ∧
      rρ = ρ ∧ rctl = ⟨pc :: κ, q, ℓ⟩ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hre hrctl
  obtain rfl : ρ = rρ := hrρ.symm
  obtain rfl : σ₁ = σ₂ := hσ.symm
  imod Hclose with -
  imodintro
  isplit
  · ipureintro
    exact List.empty_eq_nil obs₂
  isplitl [Hσ]
  · simp only [List.length_nil, Nat.add_zero]
    iexact Hσ
  isplitr []
  · iexact H
  · simp only [Algebra.BigOpL.bigOpL_nil]
    itrivial

/-! ### THE COLLAPSE -/

/-- THE COLLAPSE INTO IRIS TOTAL WP, IN CPS OVER THE AMBIENT CONTROL
    (calls arc C3; audit F-02, remediation item 1: the pinned
    `TotalWeakestPre` keeps its consumer): under the total procedure and
    block specifications, the total statement judgment at budget `k`
    entails the Iris TWP of `⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩` at any call stack and
    execution location, given the continuation `K` (the same shape as
    `wps_sound_cps`). NO Löb: STRONG INDUCTION ON THE BUDGET — a step
    decreases it by one; a back edge lands in the target body's variant
    budget, strictly below the jump point's remaining budget by the
    MANDATORY decrease; a call lands the callee's body in its budget `m`
    and the caller's continuation in `k'`, both strictly below `k` by the
    BUDGET SPLIT `1 + m + k' ≤ k`. The return into the caller's
    continuation is `twp_ret`/`twp_ret_annot`. (Deleting either decrease
    premise makes this induction unjustifiable — the structural form of
    the audit's negative criterion, now for calls too.) -/
theorem wpt_sound_cps (p : Option sym) (Ls : LabelSpecT GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) (k : Nat)
    (κ : List (Option sym × context)) (ℓ : exec_location) (e : CoreExpr) (ρ : EnvStack)
    (Φ : CoreRVal → IProp GF) :
    procSpecsT M Θ ⊢
      iprop(blockSpecsT M p Ls Θ Ψ -∗ wpt M p Ls Θ k Ψ e ρ -∗
        (∀ (ℓ' : exec_location) (w : SpikeVal) (ρ' : EnvStack), ⌜SameTail ρ ρ'⌝ -∗ Ψ w ρ' -∗
          WP (⟨ofVal w, ρ', ⟨κ, p, ℓ'⟩, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ Φ }]) -∗
        WP (⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ Φ }]) := by
  induction k using Nat.strongRecOn generalizing p Ls Ψ κ ℓ e ρ Φ with
  | ind k IH =>
  iintro #HP #HB
  cases htv : toVal e with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k (toVal_ofVal w)]
    iintro ⟨-, H⟩ HK
    iapply twp.fupd_twp
    imod H with H
    imodintro
    iapply HK $$ %ℓ %w %ρ %(SameTail.refl ρ) H
  | none =>
    have htoval : ToVal.toVal (Val := CoreRVal) (⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) = none :=
      toValRt_eq_none_of_toVal_none htv
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq k htv hjr,
        (twp.unfold (e := (⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt))).to_eq]
      simp only [twp.pre, htoval]
      iintro H HK %σ₁ %ns %obs %nt Hσ
      imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %hρ, %hl, %hvs, %hμ, HLs⟩
      subst hρ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨⟨cont, bindArgs params vs (ev0 :: evs), ⟨κ, p, ℓ⟩, M⟩, σ₁, [],
          ⟨Step.run_of_jumpRedex hjr hl hvs, rfl, rfl⟩⟩
      iintro %obs₂ %r %σ₂ %eₜ %Hstep
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
      obtain ⟨re, rρ, rctl, rM⟩ := r
      simp only at hlbl
      obtain rfl : M = rM := hlbl.symm
      obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = rctl :=
        (Step.ctl_eq hs (callRedex?_none_of_jumpRedex?_some hjr) htv).symm
      obtain ⟨hre, hrρ, hσ⟩ : re = cont ∧
          rρ = bindArgs params vs (ev0 :: evs) ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      obtain rfl : cont = re := hre.symm
      subst hrρ
      obtain rfl : σ₁ = σ₂ := hσ.symm
      have hst : SameTail (ev0 :: evs) (bindArgs params vs (ev0 :: evs)) := hs.sameTail
      imod Hclose with -
      imodintro
      isplit
      · ipureintro
        exact List.empty_eq_nil obs₂
      isplitl [Hσ]
      · simp only [List.length_nil, Nat.add_zero]
        iexact Hσ
      isplitr []
      · ihave Hwpt := HB $$ %l %params %cont %vs %ev0 %evs %m %hl HLs
        iapply IH m (by omega) p Ls Ψ κ ℓ cont (bindArgs params vs (ev0 :: evs)) Φ
          $$ HP HB Hwpt
        iintro %ℓ' %w %ρ' %hst' HΨ
        iapply HK $$ %ℓ' %w %ρ' %(hst.trans hst') HΨ
      · simp only [Algebra.BigOpL.bigOpL_nil]
        itrivial
    | none =>
    cases hcr : callRedex? e with
    | some q =>
      -- THE CALL: the callee's body under `procSpecsT` at its budget, the
      -- IH twice (body, then the caller's continuation after the return)
      rw [wpt_call_eq htv hjr hcr,
        (twp.unfold (e := (⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt))).to_eq]
      simp only [twp.pre, htoval]
      have hq : callRedex? e = some (q.1, q.2.1, q.2.2) := hcr
      iintro H HK %σ₁ %ns %obs %nt Hσ
      imod H with ⟨%params, %body, %vs, %m, %k', %hb, %hf, %hlen, %hvs, Hpre, Hcont⟩
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨⟨body, procEnv params vs :: ρ,
          ⟨(p, q.1) :: κ, some q.2.1, push_exec_loc q.2.1 M.currentLoc ℓ⟩, M⟩, σ₁, [],
          ⟨Step.call hq hvs hf hlen, rfl, rfl⟩⟩
      iintro %obs₂ %r %σ₂ %eₜ %Hstep
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      obtain ⟨params', body', vs', hvs', hf', hlen', hout⟩ := hs.call_inv hq
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
      obtain ⟨hre, hrρ, hrctl, hσ⟩ : re = body ∧ rρ = procEnv params vs :: ρ ∧
          rctl = ⟨(p, q.1) :: κ, some q.2.1, push_exec_loc q.2.1 M.currentLoc ℓ⟩ ∧
          σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      obtain rfl : body = re := hre.symm
      obtain rfl : procEnv params vs :: ρ = rρ := hrρ.symm
      obtain rfl : (⟨(p, q.1) :: κ, some q.2.1, push_exec_loc q.2.1 M.currentLoc ℓ⟩ : Ctl) = rctl :=
        hrctl.symm
      obtain rfl : σ₁ = σ₂ := hσ.symm
      imod Hclose with -
      imodintro
      isplit
      · ipureintro
        exact List.empty_eq_nil obs₂
      isplitl [Hσ]
      · simp only [List.length_nil, Nat.add_zero]
        iexact Hσ
      isplitr []
      · ihave HS := HP $$ %(q.2.1) %params %body %m %vs %ρ %hf %hlen
        icases HS with ⟨%Ls', #HB', Hbody⟩
        ihave Hbody := Hbody $$ Hpre
        iapply IH m (by omega) (some q.2.1) Ls' (fun w _ => (Θ q.2.1 m vs).2 w.val)
          ((p, q.1) :: κ) (push_exec_loc q.2.1 M.currentLoc ℓ) body
          (procEnv params vs :: ρ) Φ $$ HP HB' Hbody
        -- K': the RETURN into the caller's continuation at budget k'
        iintro %ℓ' %w %ρ' %hst
        obtain ⟨ev0', rfl⟩ := hst.cons_inv
        cases w with
        | pure v =>
          rw [show (SpikeVal.pure v).val = v from rfl]
          iintro Hpost
          ihave Hw := Hcont $$ %v Hpost
          rw [show ofVal (SpikeVal.pure v) = Expr [] (Epure (Pexpr [] () (PEval v))) from rfl]
          iapply twp_ret
          iapply IH k' (by omega) p Ls Ψ κ ℓ'
            (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval v))))) ρ Φ $$ HP HB Hw HK
        | annot ds v =>
          rw [show (SpikeVal.annot ds v).val = v from rfl]
          iintro Hpost
          ihave Hw := Hcont $$ %v Hpost
          rw [show ofVal (SpikeVal.annot ds v) =
            Expr [] (Eannot ds (Expr [] (Epure (Pexpr [] () (PEval v))))) from rfl]
          iapply twp_ret_annot
          iapply twp_ret
          iapply IH k' (by omega) p Ls Ψ κ ℓ'
            (apply_ctx q.1 (Expr [] (Epure (Pexpr [] () (PEval v))))) ρ Φ $$ HP HB Hw HK
      · simp only [Algebra.BigOpL.bigOpL_nil]
        itrivial
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro %hf
        exact hf.elim
      | succ k1 =>
        rw [wpt_step_eq k1 htv hjr hcr,
          (twp.unfold (e := (⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt))).to_eq]
        simp only [twp.pre, htoval]
        iintro H HK %σ₁ %ns %obs %nt Hσ
        imod H $$ %κ %ℓ %σ₁ %ns %obs %nt Hσ with ⟨%hred, Hstep⟩
        imodintro
        isplitr
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain rfl : obs0 = [] := List.empty_eq_nil obs0
          exact ⟨r', σ', eₜ', hps⟩
        iintro %obs₂ %e₂ %σ₂ %eₜ %Hprim
        obtain rfl : obs₂ = [] := List.empty_eq_nil obs₂
        obtain ⟨hs2, hlbl2, rfl⟩ := Hprim
        have he₂ : e₂ = (⟨e₂.e, e₂.ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt) := by
          obtain ⟨e₂e, e₂ρ, e₂ctl, e₂M⟩ := e₂
          simp only at hlbl2
          obtain rfl : (⟨κ, p, ℓ⟩ : Ctl) = e₂ctl := (Step.ctl_eq hs2 hcr htv).symm
          rw [hlbl2]
        have hst : SameTail ρ e₂.ρ := by
          rw [he₂] at hs2
          exact hs2.sameTail
        imod Hstep $$ %e₂ %σ₂ %([] : List CoreRt)
          %(⟨hs2, hlbl2, rfl⟩ :
            ((⟨e, ρ, ⟨κ, p, ℓ⟩, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (e₂, σ₂, []))
          with ⟨HSI, Hwpt⟩
        imodintro
        isplit
        · ipureintro
          rfl
        isplitl [HSI]
        · simp only [List.length_nil, Nat.add_zero]
          iexact HSI
        isplitr []
        · rw [he₂]
          iapply IH k1 (Nat.lt_succ_self k1) p Ls Ψ κ ℓ e₂.e e₂.ρ Φ $$ HP HB Hwpt
          iintro %ℓ' %w %ρ' %hst' HΨ
          iapply HK $$ %ℓ' %w %ρ' %(hst.trans hst') HΨ
        · simp only [Algebra.BigOpL.bigOpL_nil]
          itrivial

/-- THE COLLAPSE AT THE ENTRY CONTROL (the pre-C3 statement, with the
    table and the total procedure specifications threaded):
    `wpt_sound_cps` with `K := twp.value`. -/
theorem wpt_sound {Ψ : SpikeVal → EnvStack → IProp GF} {ctl : Ctl} (hκ : ctl.κ = [])
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    iprop(procSpecsT M Θ ∗ blockSpecsT M ctl.proc Ls Θ Ψ) ⊢
      iprop(wpt M ctl.proc Ls Θ k Ψ e ρ -∗
        WP (⟨e, ρ, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ w, Ψ w.w w.ρ }]) := by
  obtain ⟨κ, p, ℓ⟩ := ctl
  simp only at hκ
  subst hκ
  dsimp only
  iintro ⟨#HP, #HB⟩ Hwpt
  iapply wpt_sound_cps p Ls Ψ k [] ℓ e ρ _ $$ HP HB Hwpt
  iintro %ℓ' %w %ρ' %_ HΨ
  iapply (twp.value (e := (⟨ofVal w, ρ', ⟨[], p, ℓ'⟩, M⟩ : CoreRt))
    (v := (⟨w, ρ', p, ℓ', M⟩ : CoreRVal)) rfl)
  iexact HΨ

/-- The total collapse at the EMPTY table (the pre-C3 statement
    verbatim; `procSpecsT_empty`). -/
theorem wpt_sound_empty {Ψ : SpikeVal → EnvStack → IProp GF} {ctl : Ctl} (hκ : ctl.κ = [])
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    blockSpecsT M ctl.proc Ls emptyProcSpecT Ψ ⊢
      iprop(wpt M ctl.proc Ls emptyProcSpecT k Ψ e ρ -∗
        WP (⟨e, ρ, ctl, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ w, Ψ w.w w.ρ }]) := by
  iintro #HB
  iapply wpt_sound hκ k e ρ
  isplit
  · iapply procSpecsT_empty
  · iexact HB

end CerberusHeapLang
