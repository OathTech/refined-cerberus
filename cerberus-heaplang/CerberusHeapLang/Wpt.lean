/-
CerberusHeapLang.Wpt — the total label-context judgment `wpt`.

THE SHAPE: the total analogue of `wps` (Wps.lean) — the same
label-context statement logic, but TOTAL: `wpt M Ls k Ψ e ρ` means
"e delivers a value satisfying Ψ within k engine-drive steps
(delivery protocol included), given that every registered label body
meets its own budget" (`blockSpecsT`). It is defined WITHOUT a
fixpoint, by structural recursion on the step budget `k` (`wpt.pre`:
value / jump redex / step clauses; the recursive occurrence in the
step clause is at `k - 1`, and the jump clause does not recurse — the
body's obligation lives in `blockSpecsT` at the target's own budget).
No Löb and no ▷: the least-fixpoint discipline of iris-lean's own
`TotalWeakestPre`, realized through the budget's well-foundedness.

THE MANDATORY DECREASE: label preconditions are INDEXED BY A VARIANT
`m : Nat` (`LabelSpecT` — the classical Floyd variant as a
specification parameter, so heap-resident measures such as a chain
length enter through the invariant), and the jump clause REQUIRES
`1 + m ≤ k`: the target label's budget plus the jump step itself must
fit in the remaining budget. Since a body is verified (`blockSpecsT`)
at budget `m` and budgets only shrink along steps, every back edge
strictly decreases a well-founded `Nat` measure. The variant is
simultaneously a step budget, so one derivation yields two results:
- `wpt_sound` collapses the judgment into iris-lean's
  `TotalWeakestPre` (`WP … [{ … }]`), by strong induction on the
  budget — a metatheorem (the judgment is a sound total WP) that no
  export consumes;
- `wpt_drive_aux` (TotalAdequacy.lean) is the simulation into the
  engine: a proved `wpt … k` plus the seeded footprint yields the
  unconditional `driveU … k = .done` equation, the device lemma
  `outcomesU_of_step` (Soundness.lean) discharging one `driveU` step
  per budget unit. Every total export
  goes this way; no Iris adequacy result is in any total export's cone.
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
k`); operand evaluation and the memop; the pure exit and the
annotation layer; consequence (`wpt_mono`, `wpt_mono_k`, `wpt_mono_Ls`,
`wpt_fupd`); framing (`wpt_frame`, `wpt_frame_labels`/`frameLsT`);
`blockSpecsT_intro` with `blockSpecsT_frame`/`blockSpecsT_mono`; and
the collapse `wpt_sound`.
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

/-! The delivery cost of a value (`deliveryCost`: PROGRAM-DONE costs
one drive step; an annot value pays the REMOVE-ANNOT tau first) is
defined in Rules.lean, where the atomic step specification carries
it. -/

/-! ## The judgment -/

/-- One layer of the total statement judgment at budget `k`. Three
    clauses, mirroring `wps.pre` (Wps.lean) with the total
    strengthenings:
    - VALUE: the delivery cost must fit the remaining budget.
    - JUMP: the payload of `wps.pre`'s jump clause PLUS the mandatory
      decrease `1 + m ≤ k` at the ∃-chosen variant `m` (never
      optional — audit F-02).
    - STEP: the twp-shaped step obligation — NO later, NO credit
      (total WPs admit no Löb); the continuation `F` is the
      recursive occurrence at budget `k-1`, and at `k = 0` the
      clause is `⌜False⌝` (a non-value, non-jump term cannot deliver
      within zero steps). -/
def wpt.pre [SpikeGS hlc GF] (M : MachineCtx) (Ls : LabelSpecT GF)
    (k : Nat)
    (F : (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF)
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
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel M.labels lp.1 = some (params, cont)⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ lp.2 = some vs⌝ ∗
        ⌜1 + m ≤ k⌝ ∗ Ls lp.1 m vs ρ)
    | none =>
      match k with
      | 0 => iprop(⌜False⌝)
      | _ + 1 =>
        iprop(∀ (σ₁ : Mem) (ns : Nat) (obs : List Empty) (nt : Nat),
          stateInterp σ₁ ns obs nt ={⊤,∅}=∗
          ⌜PrimStep.Reducible ((⟨e, ρ, M⟩ : CoreRt), σ₁)⌝ ∗
          ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
            ⌜((⟨e, ρ, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝
              ={∅,⊤}=∗
            stateInterp σ₂ (ns + 1) obs nt ∗ F Ψ r.e r.ρ)

/-- THE TOTAL STATEMENT JUDGMENT: structural recursion on the step
    budget (header note — no fixpoint machinery; the budget IS the
    well-founded measure). -/
def wpt [SpikeGS hlc GF] (M : MachineCtx) (Ls : LabelSpecT GF) :
    Nat → (SpikeVal → EnvStack → IProp GF) → CoreExpr → EnvStack → IProp GF
  | 0 => wpt.pre M Ls 0 (fun _ _ _ => iprop(⌜False⌝))
  | k + 1 => wpt.pre M Ls (k + 1) (wpt M Ls k)

variable [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpecT GF}

/-! ## Per-clause unfolding equations -/

theorem wpt_val_eq {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    {e : CoreExpr} {w : SpikeVal} {ρ : EnvStack} (htv : toVal e = some w) :
    wpt M Ls k Ψ e ρ = iprop(⌜deliveryCost w ≤ k⌝ ∗ |={⊤}=> Ψ w ρ) := by
  cases k <;> simp only [wpt, wpt.pre, htv]

theorem wpt_jump_eq {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    {e : CoreExpr} {l : sym} {pes : List (generic_pexpr Unit sym)}
    {ρ : EnvStack} (htv : toVal e = none)
    (hjr : jumpRedex? e = some (l, pes)) :
    wpt M Ls k Ψ e ρ =
      iprop(|={⊤}=> ∃ (params : List (sym × core_base_type)) (cont : CoreExpr)
        (vs : List value) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
        (m : Nat),
        ⌜ρ = ev0 :: evs⌝ ∗ ⌜lookupLabel M.labels l = some (params, cont)⌝ ∗
        ⌜evalPexprs M.tagDefs M.extern ρ pes = some vs⌝ ∗
        ⌜1 + m ≤ k⌝ ∗ Ls l m vs ρ) := by
  cases k <;> simp only [wpt, wpt.pre, htv, hjr]

theorem wpt_zero_step_eq {Ψ : SpikeVal → EnvStack → IProp GF}
    {e : CoreExpr} {ρ : EnvStack} (htv : toVal e = none)
    (hjr : jumpRedex? e = none) :
    wpt M Ls 0 Ψ e ρ = iprop(⌜False⌝) := by
  simp only [wpt, wpt.pre, htv, hjr]

theorem wpt_step_eq {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    {e : CoreExpr} {ρ : EnvStack} (htv : toVal e = none)
    (hjr : jumpRedex? e = none) :
    wpt M Ls (k + 1) Ψ e ρ =
      iprop(∀ (σ₁ : Mem) (ns : Nat) (obs : List Empty) (nt : Nat),
        stateInterp σ₁ ns obs nt ={⊤,∅}=∗
        ⌜PrimStep.Reducible ((⟨e, ρ, M⟩ : CoreRt), σ₁)⌝ ∗
        ∀ (r : CoreRt) (σ₂ : Mem) (eₜ : List CoreRt),
          ⌜((⟨e, ρ, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (r, σ₂, eₜ)⌝
            ={∅,⊤}=∗
          stateInterp σ₂ (ns + 1) obs nt ∗ wpt M Ls k Ψ r.e r.ρ) := by
  simp only [wpt, wpt.pre, htv, hjr]

/-! ## Structural rules -/

/-- Budget weakening: the judgment states an upper bound. -/
theorem wpt_mono_k {Ψ : SpikeVal → EnvStack → IProp GF} {k k' : Nat}
    (hk : k ≤ k') (e : CoreExpr) (ρ : EnvStack) :
    wpt M Ls k Ψ e ρ ⊢ wpt M Ls k' Ψ e ρ := by
  induction k generalizing k' e ρ with
  | zero =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq 0 htv, wpt_val_eq k' htv]
      iintro ⟨%hc, H⟩
      isplit
      · ipureintro; exact Nat.le_trans hc hk
      · iexact H
    | none =>
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq 0 htv hjr, wpt_jump_eq k' htv hjr]
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
        rw [wpt_zero_step_eq htv hjr]
        iintro %h
        exact h.elim
  | succ m IH =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (m + 1) htv, wpt_val_eq k' htv]
      iintro ⟨%hc, H⟩
      isplit
      · ipureintro; exact Nat.le_trans hc hk
      · iexact H
    | none =>
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq (m + 1) htv hjr, wpt_jump_eq k' htv hjr]
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
        obtain ⟨m', rfl⟩ : ∃ m', k' = m' + 1 := ⟨k' - 1, by omega⟩
        rw [wpt_step_eq m htv hjr, wpt_step_eq m' htv hjr]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH (by omega) (r.e) (r.ρ) $$ H

/-- Monotonicity in the postcondition (budget preserved; the jump
    clause is Ψ-independent — the pass-through mirrors `wps_wand`,
    which this rule replaces at the total stratum in ⊢-level form:
    the total judgment has no Löb, so the consequence function is a
    meta-level entailment family). -/
theorem wpt_mono {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ w ρ', Ψ₁ w ρ' ⊢ Ψ₂ w ρ') (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    wpt M Ls k Ψ₁ e ρ ⊢ wpt M Ls k Ψ₂ e ρ := by
  induction k generalizing e ρ with
  | zero =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (Ψ := Ψ₁) 0 htv, wpt_val_eq (Ψ := Ψ₂) 0 htv]
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
        rw [wpt_jump_eq (Ψ := Ψ₁) 0 htv hjr, wpt_jump_eq (Ψ := Ψ₂) 0 htv hjr]
      | none =>
        rw [wpt_zero_step_eq (Ψ := Ψ₁) htv hjr,
          wpt_zero_step_eq (Ψ := Ψ₂) htv hjr]
  | succ m IH =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (Ψ := Ψ₁) (m + 1) htv, wpt_val_eq (Ψ := Ψ₂) (m + 1) htv]
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
        rw [wpt_jump_eq (Ψ := Ψ₁) (m + 1) htv hjr,
          wpt_jump_eq (Ψ := Ψ₂) (m + 1) htv hjr]
      | none =>
        rw [wpt_step_eq (Ψ := Ψ₁) m htv hjr, wpt_step_eq (Ψ := Ψ₂) m htv hjr]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH (r.e) (r.ρ) $$ H

/-- Monotonicity in the LABEL CONTEXT (alloc arc P2): a judgment at
    a pointwise-stronger label context transports to a weaker one —
    the jump clause's payload maps through the entailment, the value
    and step clauses are label-free. (The production reversal wraps
    the generic list label spec in an existential over the
    engine-picked allocation ids; this is the transport.) -/
theorem wpt_mono_Ls {Ls₁ Ls₂ : LabelSpecT GF}
    {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l m vs ρ', Ls₁ l m vs ρ' ⊢ Ls₂ l m vs ρ')
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    wpt M Ls₁ k Ψ e ρ ⊢ wpt M Ls₂ k Ψ e ρ := by
  induction k generalizing e ρ with
  | zero =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (Ls := Ls₁) 0 htv, wpt_val_eq (Ls := Ls₂) 0 htv]
    | none =>
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq (Ls := Ls₁) 0 htv hjr,
          wpt_jump_eq (Ls := Ls₂) 0 htv hjr]
        iintro H
        imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %h1, %h2, %h3,
          %h4, HLs⟩
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
        rw [wpt_zero_step_eq (Ls := Ls₁) htv hjr,
          wpt_zero_step_eq (Ls := Ls₂) htv hjr]
  | succ m IH =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (Ls := Ls₁) (m + 1) htv, wpt_val_eq (Ls := Ls₂) (m + 1) htv]
    | none =>
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq (Ls := Ls₁) (m + 1) htv hjr,
          wpt_jump_eq (Ls := Ls₂) (m + 1) htv hjr]
        iintro H
        imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m', %h1, %h2, %h3,
          %h4, HLs⟩
        imodintro
        iexists params, cont, vs, ev0, evs, m'
        isplit
        · ipureintro; exact h1
        isplit
        · ipureintro; exact h2
        isplit
        · ipureintro; exact h3
        isplit
        · ipureintro; exact h4
        iapply h l m' vs ρ $$ HLs
      | none =>
        rw [wpt_step_eq (Ls := Ls₁) m htv hjr, wpt_step_eq (Ls := Ls₂) m htv hjr]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH (r.e) (r.ρ) $$ H

/-- POSTCONDITION-MODALITY ABSORPTION at the total stratum (the
    `wps_fupd` twin, QA-1/M-3): the update is paid at the value exit
    (the value clause is fupd-headed), passes a jump untouched (the
    jump clause is Ψ-independent), rides through steps by budget
    induction. -/
theorem wpt_fupd {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat) (e : CoreExpr)
    (ρ : EnvStack) :
    wpt M Ls k (fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) e ρ ⊢ wpt M Ls k Ψ e ρ := by
  induction k generalizing e ρ with
  | zero =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) 0 htv,
        wpt_val_eq (Ψ := Ψ) 0 htv]
      iintro ⟨%hc, H⟩
      isplit
      · ipureintro; exact hc
      imod H with H
      iexact H
    | none =>
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) 0 htv hjr,
          wpt_jump_eq (Ψ := Ψ) 0 htv hjr]
      | none =>
        rw [wpt_zero_step_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) htv hjr,
          wpt_zero_step_eq (Ψ := Ψ) htv hjr]
  | succ m IH =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) (m + 1) htv,
        wpt_val_eq (Ψ := Ψ) (m + 1) htv]
      iintro ⟨%hc, H⟩
      isplit
      · ipureintro; exact hc
      imod H with H
      iexact H
    | none =>
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) (m + 1) htv hjr,
          wpt_jump_eq (Ψ := Ψ) (m + 1) htv hjr]
      | none =>
        rw [wpt_step_eq (Ψ := fun w ρ' => iprop(|={⊤}=> Ψ w ρ')) m htv hjr,
          wpt_step_eq (Ψ := Ψ) m htv hjr]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH (r.e) (r.ρ) $$ H

/-! ## Statement-level framing at the total stratum (alloc arc P4.2,
R-05): the frame rides through the value exit and every back edge by
framing the variant-indexed label context pointwise (Wps.lean,
"Statement-level framing"). -/

/-- Framing of a variant-indexed label context. -/
abbrev frameLsT (R : IProp GF) (Ls : LabelSpecT GF) : LabelSpecT GF :=
  fun l m vs ρ => iprop(Ls l m vs ρ ∗ R)

/-- THE TOTAL STATEMENT FRAME RULE (labels included): induction on the
    budget, clause by clause — the value clause keeps its cost bound,
    the jump clause keeps its variant decrease. -/
theorem wpt_frame_labels {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    wpt M Ls k Ψ e ρ ⊢
      iprop(R -∗ wpt M (frameLsT R Ls) k (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ) := by
  induction k generalizing e ρ with
  | zero =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (Ls := Ls) 0 htv, wpt_val_eq (Ls := frameLsT R Ls) 0 htv]
      iintro ⟨%hc, H⟩ HR
      isplit
      · ipureintro; exact hc
      imod H with H
      imodintro
      isplitl [H]
      · iexact H
      · iexact HR
    | none =>
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq (Ls := Ls) 0 htv hjr,
          wpt_jump_eq (Ls := frameLsT R Ls) 0 htv hjr]
        iintro H HR
        imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %h1, %h2, %h3,
          %h4, HLs⟩
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
        rw [wpt_zero_step_eq (Ls := Ls) htv hjr,
          wpt_zero_step_eq (Ls := frameLsT R Ls) htv hjr]
        iintro %h -
        exact h.elim
  | succ m IH =>
    cases htv : toVal e with
    | some w =>
      rw [wpt_val_eq (Ls := Ls) (m + 1) htv, wpt_val_eq (Ls := frameLsT R Ls) (m + 1) htv]
      iintro ⟨%hc, H⟩ HR
      isplit
      · ipureintro; exact hc
      imod H with H
      imodintro
      isplitl [H]
      · iexact H
      · iexact HR
    | none =>
      cases hjr : jumpRedex? e with
      | some lp =>
        obtain ⟨l, pes⟩ := lp
        rw [wpt_jump_eq (Ls := Ls) (m + 1) htv hjr,
          wpt_jump_eq (Ls := frameLsT R Ls) (m + 1) htv hjr]
        iintro H HR
        imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m', %h1, %h2, %h3,
          %h4, HLs⟩
        imodintro
        iexists params, cont, vs, ev0, evs, m'
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
        rw [wpt_step_eq (Ls := Ls) m htv hjr, wpt_step_eq (Ls := frameLsT R Ls) m htv hjr]
        iintro H HR %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨$, H⟩
        imodintro
        iintro %r %σ₂ %eₜ %Hstep
        imod H $$ %r %σ₂ %eₜ %Hstep with ⟨$, H⟩
        imodintro
        iapply IH (r.e) (r.ρ) $$ H HR

/-- The value-channel frame at a FIXED label context (derived: frame
    the labels, then drop the frame from them — the total analogue of
    `wps_frame`; what a straight-line client needs). -/
theorem wpt_frame {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF)
    (k : Nat) (e : CoreExpr) (ρ : EnvStack) :
    iprop(wpt M Ls k Ψ e ρ ∗ R) ⊢
      wpt M Ls k (fun w ρ' => iprop(Ψ w ρ' ∗ R)) e ρ := by
  iintro ⟨H, HR⟩
  iapply wpt_mono_Ls (Ls₁ := frameLsT R Ls) (fun l m vs ρ' => BI.sep_elim_left) k e ρ
  iapply wpt_frame_labels R k e ρ $$ H HR

/-- Value rule (delivery cost within budget). -/
theorem wpt_ofVal {Ψ : SpikeVal → EnvStack → IProp GF} (w : SpikeVal)
    (ρ : EnvStack) {k : Nat} (hk : deliveryCost w ≤ k) :
    Ψ w ρ ⊢ wpt M Ls k Ψ (ofVal w) ρ := by
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
    (h : AtomicStep M e ρ c P Q) (hnv : toVal e = none)
    (hnj : jumpRedex? e = none) (hk : c + 1 ≤ k) :
    iprop(P ∗ (∀ w : SpikeVal, Q w -∗ Ψ w ρ)) ⊢ wpt M Ls k Ψ e ρ := by
  obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by omega⟩
  rw [wpt_step_eq k1 hnv hnj]
  iintro ⟨HP, HΨ⟩ %σ₁ %ns %obs %nt Hσ
  imod (h ⊤ ∅ Std.LawfulSet.empty_subset σ₁ ns obs nt) $$ [$HP $Hσ]
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
    (hl : lookupLabel M.labels l = some (params, cont))
    (hvs : evalPexprs M.tagDefs M.extern (ev0 :: evs) pes = some vs)
    (hμ : 1 + m ≤ k) :
    Ls l m vs (ev0 :: evs) ⊢
      wpt M Ls k Ψ (Expr a (Erun ra l pes)) (ev0 :: evs) := by
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

/-! ## The deterministic-tau lifting (one lemma for every
state-preserving deterministic step; the per-construct rules are its
instances plus one inversion each) -/

/-- A state-preserving deterministic step costs one budget unit. -/
theorem wpt_det_step {Ψ : SpikeVal → EnvStack → IProp GF} {e : CoreExpr}
    {ρ : EnvStack} {e' : CoreExpr} {ρ' : EnvStack} {k : Nat}
    (htv : toVal e = none) (hjr : jumpRedex? e = none)
    (hstep : ∀ σ : Mem, Step M (e, ρ, σ) (e', ρ', σ))
    (hdet : ∀ (σ : Mem) (out : CoreExpr × EnvStack × Mem),
      Step M (e, ρ, σ) out → out = (e', ρ', σ)) :
    wpt M Ls k Ψ e' ρ' ⊢ wpt M Ls (k + 1) Ψ e ρ := by
  rw [wpt_step_eq k htv hjr]
  iintro H %σ₁ %ns %obs %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨e', ρ', M⟩, σ₁, [], hstep σ₁, rfl, rfl⟩
  iintro %r %σ₂ %eₜ %Hstep
  obtain ⟨hs, hlbl, rfl⟩ := Hstep
  have hout := hdet σ₁ _ hs
  obtain ⟨re, rρ, rM⟩ := r
  simp only at hlbl
  obtain rfl : M = rM := hlbl.symm
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
      wpt M Ls k Ψ (bif b then e2 else e3) ρ) ⊢
      wpt M Ls (k + 1) Ψ (Expr a (Eif g e2 e3)) ρ := by
  cases b
  · rw [show (bif false then e2 else e3) = e3 from rfl]
    iintro ⟨%hg, H⟩
    iapply wpt_det_step rfl rfl (fun _ => Step.if_false hg)
      (fun σ out hs => by
        rcases hs.if_inv with ⟨hg', -⟩ | ⟨-, hout⟩
        · rw [hg] at hg'; cases hg'
        · exact hout)
    iexact H
  · rw [show (bif true then e2 else e3) = e2 from rfl]
    iintro ⟨%hg, H⟩
    iapply wpt_det_step rfl rfl (fun _ => Step.if_true hg)
      (fun σ out hs => by
        rcases hs.if_inv with ⟨-, hout⟩ | ⟨hg', -⟩
        · exact hout
        · rw [hg] at hg'; cases hg')
    iexact H

/-- Eif, true branch — the `b := true` instance of `wpt_if` (derived
    corollary, verdict at the meta level). -/
theorem wpt_if_true {Ψ : SpikeVal → EnvStack → IProp GF} (a : List annot)
    (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) (ρ : EnvStack) {k : Nat}
    (hg : evalPexpr M.tagDefs M.extern ρ g = some Vtrue) :
    wpt M Ls k Ψ e2 ρ ⊢ wpt M Ls (k + 1) Ψ (Expr a (Eif g e2 e3)) ρ := by
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
    wpt M Ls k Ψ e3 ρ ⊢ wpt M Ls (k + 1) Ψ (Expr a (Eif g e2 e3)) ρ := by
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
    wpt M Ls k Ψ e' ρ ⊢ wpt M Ls (k + 1) Ψ (Expr a (Ecase pe pats)) ρ :=
  wpt_det_step rfl rfl (fun _ => Step.case_value hv hsel)
    (fun σ out hs => by
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
    wpt M Ls k Ψ body (bindSaveParams ps cvals (ev0 :: evs)) ⊢
      wpt M Ls (k + 1) Ψ (Expr a (Esave sb ps body)) (ev0 :: evs) :=
  wpt_det_step rfl rfl (fun _ => Step.save hvals)
    (fun σ out hs => by
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
    wpt M Ls k Ψ (Expr a (Esave sb (saveParamsWithValues ps cvals) body)) ρ ⊢
      wpt M Ls (k + 1) Ψ (Expr a (Esave sb ps body)) ρ :=
  wpt_det_step rfl rfl (fun _ => Step.save_eval hnv hvals)
    (fun σ out hs => by
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
    wpt M Ls k Ψ body (bindSaveParams ps cvals (ev0 :: evs)) ⊢
      wpt M Ls (k + saveEntryCost ps) Ψ (Expr a (Esave sb ps body)) (ev0 :: evs) := by
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
    Ψ (.pure v) ρ ⊢ wpt M Ls k Ψ (Expr ([] : List annot) (Epure pe)) ρ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine .trans (wpt_ofVal (M := M) (Ls := Ls) (.pure v) ρ (by simp only [deliveryCost_pure]; exact Nat.le_of_succ_le_succ hk)) ?_
  exact wpt_det_step (toVal_pure_none hnv) (jumpRedex?_pure _ _)
    (fun _ => Step.pure_eval hnv hv)
    (fun σ out hs => by
      obtain ⟨v', -, hv', hout⟩ := hs.pure_inv
      obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
      exact hout)

/-- ACTION_EVAL for a load's pointer operand (one tau). -/
theorem wpt_load_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (ty : ctype)
    (pe2 : generic_pexpr Unit sym) (mo : memory_order) (ρ : EnvStack)
    {pv : CerbMem.PointerValue} {k : Nat}
    (hnv2 : valueFromPexpr pe2 = none)
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some (Vobject (OVpointer pv))) :
    wpt M Ls k Ψ (loadExpr loc ann ty pv mo) ρ ⊢
      wpt M Ls (k + 1) Ψ (loadOpRedex loc ann ty pe2 mo) ρ :=
  wpt_det_step rfl rfl (fun _ => Step.load_eval hnv2 hv2)
    (fun σ out hs => by
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
    wpt M Ls k Ψ (killExpr loc ann kind pv) ρ ⊢
      wpt M Ls (k + 1) Ψ (killOpRedex loc ann kind pe) ρ :=
  wpt_det_step rfl rfl (fun _ => Step.kill_eval hnv hv)
    (fun σ out hs => by
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
    wpt M Ls k Ψ (storeExpr loc ann ty pv cv mo) ρ ⊢
      wpt M Ls (k + 1) Ψ (storeOpRedex loc ann ty pe2 pe3 mo) ρ :=
  wpt_det_step rfl rfl (fun _ => Step.store_eval hnv hv2 hv3)
    (fun σ out hs => by
      obtain ⟨pv', cv', hv2', hv3', hout⟩ := hs.store_op_inv hnv
      obtain rfl : pv = pv' := by
        simpa using Option.some.inj (hv2.symm.trans hv2')
      obtain rfl : cv = cv' := Option.some.inj (hv3.symm.trans hv3')
      simpa [storeExpr] using hout)

/-- Memop-operand evaluation (one tau). -/
theorem wpt_memop_eval {Ψ : SpikeVal → EnvStack → IProp GF}
    (mop : memop) (pe1 pe2 : generic_pexpr Unit sym)
    {v1 v2 : value} (ρ : EnvStack) {k : Nat}
    (hnv : valueFromPexprs [pe1, pe2] = none)
    (hv1 : evalPexpr M.tagDefs M.extern ρ pe1 = some v1)
    (hv2 : evalPexpr M.tagDefs M.extern ρ pe2 = some v2) :
    wpt M Ls k Ψ (memopRedex mop
      [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) ρ ⊢
      wpt M Ls (k + 1) Ψ (memopRedex mop [pe1, pe2]) ρ :=
  wpt_det_step rfl rfl (fun _ => Step.memop_eval hnv hv1 hv2)
    (fun σ out hs => by
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
      wpt M Ls k Ψ (memopPtrEqVals (Vobject (OVpointer pv1))
        (Vobject (OVpointer pv2))) ρ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine .trans (wpt_ofVal (M := M) (Ls := Ls) (.pure (boolValue b)) ρ
    (by simp only [deliveryCost_pure]; exact Nat.le_of_succ_le_succ hk)) ?_
  exact wpt_det_step rfl rfl
    (fun σ => Step.memop_ptreq rfl rfl (hres σ))
    (fun σ out hs => by
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
    wpt M Ls k Ψ₁ (Expr a (Eannot dsA c)) ρ ⊢
      wpt M Ls k Ψ₂ (Expr a (Eannot dsB c)) ρ := by
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
    cases hjr : jumpRedex? (Expr a (Eannot dsA c)) with
    | some lp =>
      -- the two jump clauses are the SAME FORMULA (Ψ-free, same budget)
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq (Ψ := Ψ₁) k hA hjr,
        wpt_jump_eq (Ψ := Ψ₂) k hB (hEq.trans hjr)]
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq (Ψ := Ψ₁) hA hjr,
          wpt_zero_step_eq (Ψ := Ψ₂) hB (hEq.trans hjr)]
      | succ m =>
        rw [wpt_step_eq (Ψ := Ψ₁) m hA hjr,
          wpt_step_eq (Ψ := Ψ₂) m hB (hEq.trans hjr)]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
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
        · iintro %e₂ %σ₂ %eₜ %HstepB
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
              %⟨Step.annot_ctx hnj hg hs, rfl, rfl⟩ with ⟨$, H⟩
            imodintro
            iapply IH m (Nat.lt_succ_self m) a dsA dsB c' e₂ρ hΦ $$ H
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
              %([]) %⟨Step.annot_merge, rfl, rfl⟩ with ⟨$, H⟩
            imodintro
            iapply IH m (Nat.lt_succ_self m) (a ++ a2) (dsA ++ ds2) (dsB ++ ds2)
              c'' ρ
              (fun w ρ' => by
                rw [← SpikeVal.merge_merge, ← SpikeVal.merge_merge]
                exact hΦ (SpikeVal.merge ds2 w) ρ') $$ H
          · rw [jumpRedex?_annot_of_not_root _ _ hg, hj] at hjr; cases hjr

/-- `wpt` commutes with the run-time dyn-annotation wrapper: one
    budget unit per wrapper (its eventual merge step; a jump-through
    or a value-forming wrap costs none — the unit is slack there). -/
theorem wpt_annot (ds : List dyn_annotation) (e : CoreExpr) (ρ : EnvStack)
    {k : Nat} {Ψ : SpikeVal → EnvStack → IProp GF} :
    wpt M Ls k (fun w ρ' => Ψ (SpikeVal.merge ds w) ρ') e ρ ⊢
      wpt M Ls (k + 1) Ψ (Expr ([] : List annot) (Eannot ds e)) ρ := by
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
            (Eannot ds (ofVal (SpikeVal.annot ds2 v)))) = none from rfl)]
      iintro ⟨%hc, H⟩ %σ₁ %ns %obs %nt Hσ
      have hc2 : 2 ≤ k := by simpa [deliveryCost] using hc
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
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
          jumpRedex?_annot_of_root _ _ rfl)]
      iintro H %σ₁ %ns %obs %nt Hσ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.annot_merge, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
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
          iapply (wpt_annot_reindex
            (Ψ₁ := fun w ρ' => iprop(Ψ (SpikeVal.merge ds w) ρ'))
            a2 ds2 (ds ++ ds2) c ρ
            (fun w ρ' => congrArg (fun z => Ψ z ρ')
              (SpikeVal.merge_merge ds ds2 w))) $$ H
      · rw [show annotRooted (Expr a2 (Eannot ds2 c)) = true from rfl] at hg
        cases hg
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
        cases k with
        | zero =>
          rw [wpt_zero_step_eq hv hjr]
          iintro %h
          exact h.elim
        | succ m =>
          rw [wpt_step_eq m hv hjr,
            wpt_step_eq (m + 1) hwrap
              ((jumpRedex?_annot_of_not_root ([] : List annot) ds hr').trans
                hjr)]
          iintro H %σ₁ %ns %obs %nt Hσ
          imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
          imodintro
          isplit
          · ipureintro
            obtain ⟨obs0, e', σ', eₜ, hstep⟩ := hred
            exact ⟨[], ⟨Expr ([] : List annot) (Eannot ds e'.e), e'.ρ, M⟩, _, [],
              ⟨Step.annot_ctx hjr hr' hstep.1, rfl, rfl⟩⟩
          iintro %e₂ %σ₂ %eₜ %HstepW
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
            imod H $$ %(⟨e'', e₂ρ, M⟩ : CoreRt) %_ %([]) %⟨hs, rfl, rfl⟩
              with ⟨$, H⟩
            imodintro
            iapply IH m (Nat.lt_succ_self m) ds e'' e₂ρ $$ H
          · exact absurd heq (by
              intro heq
              rw [heq] at hr'
              simp [annotRooted] at hr')
          · rw [hjr] at hj; cases hj

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
    wpt M Ls k Ψ₁ e1 ρ ⊢
      wpt M Ls k' Ψ₂ (Expr a (Esseq pat e1 e2)) ρ := by
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
    wpt M Ls k1 (fun w ρ' => wpt M Ls k2
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wpt M Ls (k1 + k2) Ψ
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
          (by rw [jumpRedex?_sseq, jumpRedex?_ofVal])]
      iintro ⟨%hc, H⟩ %σ₁ %ns %obs %nt Hσ
      imod H with H
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        cases w with
        | pure v => exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_pure, rfl, rfl⟩⟩
        | annot ds v => exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_annot, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
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
          iapply wpt_mono_k (show k2 + 1 ≤ m + k2 by omega) _ _
          iapply wpt_annot ds e2 (ev0 :: evs) $$ H
      · rw [jumpRedex?_ofVal] at hj; cases hj
      · exact (specPat_ne_base hpat).elim
      · exact (specPat_ne_base hpat).elim
      · exact (symPat_ne_base hpat).elim
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      exact wpt_jump_frame_sseq a _ e2 _ (Nat.le_add_right k1 k2) htv hjr
    | none =>
      cases k1 with
      | zero =>
        rw [wpt_zero_step_eq htv hjr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq m htv hjr,
          show m + 1 + k2 = (m + k2) + 1 by omega,
          wpt_step_eq (m + k2)
            (toVal_sseq_node a (Pattern pa (CaseBase (none, bty))) e1 e2)
            (by rw [jumpRedex?_sseq, hjr])]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨[], ⟨Expr a (Esseq (Pattern pa (CaseBase (none, bty)))
              r'.e e2), r'.ρ, M⟩, σ', [],
            ⟨Step.sseq_ctx hjr hs', rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
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
            %⟨hs', rfl, rfl⟩ with ⟨$, H⟩
          imodintro
          iapply IH m (Nat.lt_succ_self m) e1' ev0' evs $$ H
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [hjr] at hj; cases hj
        · exact (specPat_ne_base hpat).elim
        · exact (specPat_ne_base hpat).elim
        · exact (symPat_ne_base hpat).elim

/-- The jump-clause transfer through an Ewseq frame (the `wpt_jump_frame_sseq`
    twin). -/
theorem wpt_jump_frame_wseq {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (a : List annot) (pat : pattern) {e1 : CoreExpr} (e2 : CoreExpr)
    (ρ : EnvStack) {l : sym} {pes : List (generic_pexpr Unit sym)}
    {k k' : Nat} (hkk : k ≤ k')
    (htv : toVal e1 = none) (hjr : jumpRedex? e1 = some (l, pes)) :
    wpt M Ls k Ψ₁ e1 ρ ⊢
      wpt M Ls k' Ψ₂ (Expr a (Ewseq pat e1 e2)) ρ := by
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
    wpt M Ls k1 (fun w ρ' => wpt M Ls k2
        (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2 ρ') e1 (ev0 :: evs) ⊢
      wpt M Ls (k1 + k2) Ψ
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
          (by rw [jumpRedex?_wseq, jumpRedex?_ofVal])]
      iintro ⟨%hc, H⟩ %σ₁ %ns %obs %nt Hσ
      imod H with H
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        cases w with
        | pure v => exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.wseq_pure, rfl, rfl⟩⟩
        | annot ds v => exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.wseq_annot, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
      obtain ⟨hs, hlbl, rfl⟩ := Hstep
      rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hs', hout⟩ |
          ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds, v, _, _, _, he1, _, hout⟩ |
          ⟨l, pes, params, cont, vs, _, _, hj, _, _, _, _⟩
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
          iapply wpt_mono_k (show k2 + 1 ≤ m + k2 by omega) _ _
          iapply wpt_annot ds e2 (ev0 :: evs) $$ H
      · rw [jumpRedex?_ofVal] at hj; cases hj
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      exact wpt_jump_frame_wseq a _ e2 _ (Nat.le_add_right k1 k2) htv hjr
    | none =>
      cases k1 with
      | zero =>
        rw [wpt_zero_step_eq htv hjr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq m htv hjr,
          show m + 1 + k2 = (m + k2) + 1 by omega,
          wpt_step_eq (m + k2)
            (toVal_wseq_node a (Pattern pa (CaseBase (none, bty))) e1 e2)
            (by rw [jumpRedex?_wseq, hjr])]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨[], ⟨Expr a (Ewseq (Pattern pa (CaseBase (none, bty)))
              r'.e e2), r'.ρ, M⟩, σ', [],
            ⟨Step.wseq_ctx hjr hs', rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
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
            %⟨hs', rfl, rfl⟩ with ⟨$, H⟩
          imodintro
          iapply IH m (Nat.lt_succ_self m) e1' ev0' evs $$ H
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [hjr] at hj; cases hj

/-- THE TOTAL Specified-binder sequencing rule (total analog of
    `wps_seq_spec`). -/
theorem wpt_seq_spec {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa pb : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (k1 k2 : Nat) :
    wpt M Ls k1 (fun w ρ' => iprop(∃ (ov : object_value),
        ⌜w.val = Vloaded (LVspecified ov)⌝ ∗
        wpt M Ls k2 (fun u ρ'' => Ψ (SpikeVal.mergeInto w u) ρ'') e2
          (update_env (specPat pa pb x bty) (Vloaded (LVspecified ov)) ρ')))
      e1 (ev0 :: evs) ⊢
      wpt M Ls (k1 + k2) Ψ (Expr a (Esseq (specPat pa pb x bty) e1 e2))
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
          (by rw [jumpRedex?_sseq, jumpRedex?_ofVal])]
      iintro ⟨%hc, H⟩ %σ₁ %ns %obs %nt Hσ
      imod H with ⟨%ov, %hval, Hinner⟩
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      cases w with
      | pure v =>
        obtain rfl : v = Vloaded (LVspecified ov) := hval
        isplitr
        · ipureintro
          exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_spec_pure, rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
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
            iapply wpt_mono_k (Nat.le_add_left k2 m) e2 _ $$ Hinner
        · exact absurd he1 (by simp [ofVal])
        · exact (symPat_ne_spec hpat).elim
      | annot ds v =>
        obtain rfl : v = Vloaded (LVspecified ov) := hval
        have hm : 1 ≤ m := by
          have : (2 : Nat) ≤ m + 1 := by simpa [deliveryCost] using hc
          omega
        isplitr
        · ipureintro
          exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_spec_annot, rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
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
            iapply wpt_mono_k (show k2 + 1 ≤ m + k2 by omega) _ _
            iapply wpt_annot ds e2 _ $$ Hinner
        · exact (symPat_ne_spec hpat).elim
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      exact wpt_jump_frame_sseq a _ e2 _ (Nat.le_add_right k1 k2) htv hjr
    | none =>
      cases k1 with
      | zero =>
        rw [wpt_zero_step_eq htv hjr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq m htv hjr,
          show m + 1 + k2 = (m + k2) + 1 by omega,
          wpt_step_eq (m + k2)
            (toVal_sseq_node a (specPat pa pb x bty) e1 e2)
            (by rw [jumpRedex?_sseq, hjr])]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨[], ⟨Expr a (Esseq (specPat pa pb x bty)
              r'.e e2), r'.ρ, M⟩, σ', [],
            ⟨Step.sseq_ctx hjr hs', rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
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
            %⟨hs', rfl, rfl⟩ with ⟨$, H⟩
          imodintro
          iapply IH m (Nat.lt_succ_self m) e1' ev0' evs $$ H
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [hjr] at hj; cases hj
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv

/-- THE TOTAL plain-symbol-binder sequencing rule (total analog of
    `wps_seq_sym`). -/
theorem wpt_seq_sym {Ψ : SpikeVal → EnvStack → IProp GF}
    (a pa : List annot) (x : sym) (bty : core_base_type)
    (e1 e2 : CoreExpr)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (k1 k2 : Nat) :
    wpt M Ls k1 (fun w ρ' => iprop(∃ (v : value),
        ⌜w = SpikeVal.pure v⌝ ∗
        wpt M Ls k2 Ψ e2 (update_env (symPat pa x bty) v ρ')))
      e1 (ev0 :: evs) ⊢
      wpt M Ls (k1 + k2) Ψ (Expr a (Esseq (symPat pa x bty) e1 e2))
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
          (by rw [jumpRedex?_sseq, jumpRedex?_ofVal])]
      iintro ⟨%hc, H⟩ %σ₁ %ns %obs %nt Hσ
      imod H with ⟨%v, %hval, Hinner⟩
      subst hval
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨_, _, _⟩, _, [], ⟨Step.sseq_sym_pure, rfl, rfl⟩⟩
      iintro %r %σ₂ %eₜ %Hstep
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
        · iapply wpt_mono_k (Nat.le_add_left k2 m) e2 _ $$ Hinner
  | none =>
    cases hjr : jumpRedex? e1 with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      exact wpt_jump_frame_sseq a _ e2 _ (Nat.le_add_right k1 k2) htv hjr
    | none =>
      cases k1 with
      | zero =>
        rw [wpt_zero_step_eq htv hjr]
        iintro %h
        exact h.elim
      | succ m =>
        rw [wpt_step_eq m htv hjr,
          show m + 1 + k2 = (m + k2) + 1 by omega,
          wpt_step_eq (m + k2)
            (toVal_sseq_node a (symPat pa x bty) e1 e2)
            (by rw [jumpRedex?_sseq, hjr])]
        iintro H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨%hred, H⟩
        imodintro
        isplit
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain ⟨hs', hlbl', hnil'⟩ := hps
          exact ⟨[], ⟨Expr a (Esseq (symPat pa x bty)
              r'.e e2), r'.ρ, M⟩, σ', [],
            ⟨Step.sseq_ctx hjr hs', rfl, rfl⟩⟩
        iintro %r %σ₂ %eₜ %Hstep
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
            %⟨hs', rfl, rfl⟩ with ⟨$, H⟩
          imodintro
          iapply IH m (Nat.lt_succ_self m) e1' ev0' evs $$ H
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [hjr] at hj; cases hj
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv
        · rw [he1, toVal_ofVal] at htv; cases htv

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
      wpt M Ls k Ψ (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wpt_of_atomic (loadAt_atomic loc ann id a aty off vty mo dqm dqb bs ρ hdec htrap)
    rfl rfl hk
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
      wpt M Ls k Ψ (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo)
        ρ := by
  iintro ⟨Hv, HΨ⟩
  iapply wpt_of_atomic (storeAt_atomic loc ann id a aty off vty cv mo dqm bs ρ hmv hst)
    rfl rfl hk
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
      wpt M Ls k Ψ (loadExpr loc ann vty (cellPtr id (a + (off : Int))) mo)
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
      wpt M Ls k Ψ (storeExpr loc ann vty (cellPtr id (a + (off : Int))) cv mo)
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
      wpt M Ls k Ψ (storeExpr loc ann ty pv cv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_of_atomic (store_atomic loc ann ty pv cv mo mv bs ρ hmv hst) rfl rfl hk
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
      wpt M Ls k Ψ (loadExpr loc ann ty pv mo) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_of_atomic (load_atomic loc ann ty pv mo dq bs ρ htrap) rfl rfl hk
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
      wpt M Ls k Ψ (killExpr loc ann kind pv) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_of_atomic (kill_atomic loc ann kind pv ty bs ρ hstatic) rfl rfl hk
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
      wpt M Ls k Ψ (killExpr loc ann kind pv) ρ := by
  iintro ⟨Hpt, HΨ⟩
  iapply wpt_kill loc ann kind pv ty bs ρ hk hstatic
  isplitl [Hpt]
  · iexact Hpt
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
      wpt M Ls k Ψ (storeExpr loc ann ty pv cv mo) ρ := by
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
      wpt M Ls k Ψ (loadExpr loc ann ty pv mo) ρ := by
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

THE COST BOUND, DERIVED AGAINST `driveU` (not copied from the
charter): a bare create is one relational create step — the wpt step
clause consumes 1 budget unit, which `wpt_drive_aux` maps to one
`driveU` round (`outcomesU_of_step` at the create redex) — and its
result is the BARE pure pointer value (`Step.create` — "a BARE
value, no Eannot residue", Step.lean's create docstring), whose
delivery costs `deliveryCost (.pure _) = 1` — one `driveU` round
(`outcomesU_done`). Total: `2 ≤ k`, the charter's expected minimum,
confirmed (contrast `wpt_store_at`'s `3 ≤ k`: a store's result is an
ANNOT value, whose delivery pays the REMOVE-ANNOT tau first). -/

section CreateRuleT
open Iris.Std.PartialMap

/-- THE PUBLIC TOTAL ALLOCATION RULE (alloc arc P1.4, restated K2.5):
    the total analogue of `wps_create` at the DERIVED cost bound `2 ≤ k`
    (see the section header — one create step + one pure-value delivery
    against `driveU`). Statement is cursor-free (the P1 grep test);
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
      wpt M Ls k Ψ (createExpr loc ann (.IV aprov alignN) ty pref) ρ := by
  iintro ⟨Hb, HΨ⟩
  iapply wpt_of_atomic (create_atomic loc ann aprov alignN ty pref ρ hsz hatom hinert)
    rfl rfl hk
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
      wpt M Ls k Ψ (createExpr loc ann (.IV aprov req.align) req.ty pref) ρ := by
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

/-! ## Total block specifications and THE COLLAPSE into Iris TWP -/

/-- TOTAL BLOCK SPECIFICATIONS: every registered label's body meets
    its OWN variant value `m` (every m at which its precondition is
    claimed). This is the real total rule that replaces the retired
    `blockSpecs_intro_variant`: because the body is verified at
    budget `m` and the jump clause demands `1 + m' ≤ (remaining
    budget) ≤ m`, every back edge carries a strict decrease of the
    well-founded measure — the obligation is structural, not an
    optional hypothesis. -/
abbrev blockSpecsT (M : MachineCtx) (Ls : LabelSpecT GF)
    (Ψ : SpikeVal → EnvStack → IProp GF) : IProp GF :=
  iprop(□ ∀ (l : sym) (params : List (sym × core_base_type))
    (cont : CoreExpr) (vs : List value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (m : Nat),
    ⌜lookupLabel M.labels l = some (params, cont)⌝ -∗
      Ls l m vs (ev0 :: evs) -∗
      wpt M Ls m Ψ cont (bindArgs params vs (ev0 :: evs)))

/-- Introduction from per-label entailments. -/
theorem blockSpecsT_intro {Ψ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ l params cont vs ev0 evs m,
      lookupLabel M.labels l = some (params, cont) →
      Ls l m vs (ev0 :: evs) ⊢ wpt (GF := GF) M Ls m Ψ cont
        (bindArgs params vs (ev0 :: evs))) :
    ⊢ blockSpecsT M Ls Ψ := by
  unfold blockSpecsT
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %m %hQ HLs
  iapply h l params cont vs ev0 evs m hQ $$ HLs

/-- Monotonicity of the block specifications in the postcondition. -/
theorem blockSpecsT_mono {Ψ₁ Ψ₂ : SpikeVal → EnvStack → IProp GF}
    (h : ∀ w ρ', Ψ₁ w ρ' ⊢ Ψ₂ w ρ') :
    blockSpecsT (GF := GF) M Ls Ψ₁ ⊢ blockSpecsT M Ls Ψ₂ := by
  iintro #HB
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %m %hQ HLs
  iapply wpt_mono h m cont (bindArgs params vs (ev0 :: evs))
  iapply HB $$ %l %params %cont %vs %ev0 %evs %m %hQ HLs

/-- FRAMING THE TOTAL BLOCK SPECIFICATIONS. -/
theorem blockSpecsT_frame {Ψ : SpikeVal → EnvStack → IProp GF} (R : IProp GF) :
    blockSpecsT (GF := GF) M Ls Ψ ⊢
      blockSpecsT M (frameLsT R Ls) (fun w ρ' => iprop(Ψ w ρ' ∗ R)) := by
  iintro #HB
  imodintro
  iintro %l %params %cont %vs %ev0 %evs %m %hQ ⟨HLs, HR⟩
  ihave HW := HB $$ %l %params %cont %vs %ev0 %evs %m %hQ HLs
  iapply wpt_frame_labels R m cont (bindArgs params vs (ev0 :: evs)) $$ HW HR

/-- THE COLLAPSE INTO IRIS TOTAL WP (audit F-02, remediation item 1:
    the pinned `TotalWeakestPre` gains its consumer): under the total
    block specifications, the total statement judgment entails the
    Iris TWP with the value-channel postcondition. NO Löb: the
    induction is on the budget — steps decrease it by one, and a
    back edge lands in the target body's variant budget, strictly
    below the jump point's remaining budget by the MANDATORY
    decrease premise. (Deleting that premise makes this induction
    unjustifiable — the structural form of the audit's negative
    criterion.) -/
theorem wpt_sound {Ψ : SpikeVal → EnvStack → IProp GF} (k : Nat)
    (e : CoreExpr) (ρ : EnvStack) :
    blockSpecsT M Ls Ψ ⊢
      iprop(wpt M Ls k Ψ e ρ -∗
        WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ [{ w, Ψ w.w w.ρ }]) := by
  induction k using Nat.strongRecOn generalizing e ρ with
  | ind k IH =>
  cases htv : toVal e with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k (toVal_ofVal w),
      (twp.unfold (e := (⟨ofVal w, ρ, M⟩ : CoreRt))).to_eq]
    simp only [twp.pre, language_toVal_eq, toValRt_mk, toVal_ofVal,
      Option.map_some]
    iintro #HB ⟨-, H⟩
    imod H with H
    imodintro
    iexact H
  | none =>
    have htoval : ToVal.toVal (Val := CoreRVal) (⟨e, ρ, M⟩ : CoreRt) = none := by
      rw [language_toVal_eq, toValRt_mk, htv]
      rfl
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq k htv hjr,
        (twp.unfold (e := (⟨e, ρ, M⟩ : CoreRt))).to_eq]
      simp only [twp.pre, htoval]
      iintro #HB H %σ₁ %ns %obs %nt Hσ
      imod H with ⟨%params, %cont, %vs, %ev0, %evs, %m, %hρ, %hl, %hvs, %hμ, HLs⟩
      subst hρ
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨⟨cont, bindArgs params vs (ev0 :: evs), M⟩, σ₁, [],
          ⟨Step.run_of_jumpRedex hjr hl hvs, rfl, rfl⟩⟩
      iintro %κ %r %σ₂ %eₜ %Hstep
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
      isplit
      · ipureintro
        exact List.empty_eq_nil κ
      isplitl [Hσ]
      · simp only [List.length_nil, Nat.add_zero]
        iexact Hσ
      isplitr []
      · ihave Hwpt := HB $$ %l %params %cont %vs %ev0 %evs %m %hl HLs
        iapply IH m (by omega) cont (bindArgs params vs (ev0 :: evs))
          $$ HB Hwpt
      · simp only [Algebra.BigOpL.bigOpL_nil]
        itrivial
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq htv hjr]
        iintro #HB %hf
        exact hf.elim
      | succ k1 =>
        rw [wpt_step_eq k1 htv hjr,
          (twp.unfold (e := (⟨e, ρ, M⟩ : CoreRt))).to_eq]
        simp only [twp.pre, htoval]
        iintro #HB H %σ₁ %ns %obs %nt Hσ
        imod H $$ %σ₁ %ns %obs %nt Hσ with ⟨%hred, Hstep⟩
        imodintro
        isplitr
        · ipureintro
          obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
          obtain rfl : obs0 = [] := List.empty_eq_nil obs0
          exact ⟨r', σ', eₜ', hps⟩
        iintro %κ %e₂ %σ₂ %eₜ %Hprim
        obtain rfl : κ = [] := List.empty_eq_nil κ
        obtain ⟨hs2, hlbl2, rfl⟩ := Hprim
        imod Hstep $$ %e₂ %σ₂ %([] : List CoreRt)
          %(⟨hs2, hlbl2, rfl⟩ :
            ((⟨e, ρ, M⟩ : CoreRt), σ₁) -<([] : List Empty)>-> (e₂, σ₂, []))
          with ⟨HSI, Hwpt⟩
        imodintro
        isplit
        · ipureintro
          rfl
        isplitl [HSI]
        · simp only [List.length_nil, Nat.add_zero]
          iexact HSI
        isplitr []
        · have he₂ : e₂ = (⟨e₂.e, e₂.ρ, M⟩ : CoreRt) := by
            obtain ⟨e₂e, e₂ρ, e₂M⟩ := e₂
            simp only at hlbl2
            rw [hlbl2]
          rw [he₂]
          iapply IH k1 (Nat.lt_succ_self k1) e₂.e e₂.ρ $$ HB Hwpt
        · simp only [Algebra.BigOpL.bigOpL_nil]
          itrivial

end CerberusHeapLang
