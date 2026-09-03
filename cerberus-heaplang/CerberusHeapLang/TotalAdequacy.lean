/-
CerberusHeapLang.TotalAdequacy — total correctness at the engine: the
budget-to-drive-length simulation.

`wpt_drive_aux` / `wpt_engine_boundU` (+ `_alloc`): the total
judgment's budget is realized as a concrete `driveU` length. From
`wpt … k … e ρ` (with `blockSpecsT` for the registered bodies) plus
the seeded footprint, the engine's drive AT LENGTH k DELIVERS:
`driveU M aids k (M.thread e ρ ctl) σ = .done v σ'` with the postcondition
readout — the unconditional total equations the exhibits export (fib
at `2·n + 4`, list reversal at `13·|ns| + 7`, the tree rotation at
19), with ZERO example-level Step constructors: the simulation is
proved once, here, by strong induction on the budget with the device
lemma `outcomesU_of_step` (Soundness.lean, over `dischargeStep`)
discharging one `driveU` step per budget unit — the shipped-round
certification `engine_step_matchU` (Round.lean) is not consumed here. No
Iris adequacy result is in the cone: `wpt_sound` (Wpt.lean) is a
metatheorem consumed by no export.

FUEL HONESTY WITHOUT ACCUMULATION: the per-step `outcomesU_of_step`
obligation is `esize e ≤ lemDefaultFuel` for the CURRENT term only;
the static potential `pot` (Potential.lean — `Frag.pot_step_bound`,
`Frag.esize_le_pot`) turns it into the two run-length-independent
hypotheses `pot e₀ ≤ lemDefaultFuel` and `pot cont ≤ lemDefaultFuel`
per registered body — the same two the partial statements carry
(Adequacy.lean).

THE STATE-INERT CONE: programs built without memory actions
(`stateInert` — no Eaction/Ememop/Ecase; `StateInertLabels` for the
registered bodies) preserve the memory state step by step
(`Frag.stateInert_step`), so their total equations pin the final
state to the initial one — fib's exported equation keeps its verbatim
`.done (fib n) σ₀` shape through the generic theorem.

`DriverDoneAt` and `readoutPost` are the delivery vocabulary the
production collapse (ProdLoop.lean) restates this simulation in.

PROVISIONAL ([USER 2026-09-02], DECISIONS.md; Adequacy.lean header).
`wpt_engine_boundU` and `wpt_engine_boundU_alloc` are stated over
`driveU`, and so are the total exhibit equations derived from them
(`*_total`, `alloc_create_launch_smoke`). Each is PROVISIONAL, in
exactly this sense: a sound fact about `driveU`, this package's loop
around the engine's `step_ctx`; not yet the root-of-trust statement,
which is over the shipped driver and awaits the cerberus-lean
fuel-exhaustion outcome
(docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md,
repository root); restated with no other change when it lands. The
root-of-trust exports are the production statements that consume
this simulation through `wpt_driver_done_alloc` → `prod_run_eqJ`
(`exhibitA_prod`, `*_certified_production`): those are over the
shipped `runND ∘ drive ∘ initial_driver_state`.
-/
import CerberusHeapLang.Wpt
import CerberusHeapLang.Adequacy

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib


/-! ## The state-inert cone (memory-action-free programs preserve
the memory state — what lets fib's exported total equation pin its
final state) -/

/-- Syntactically memory-inert: no actions, no memops, no case (the
    conservative closure the fib-class exhibits need; memops and
    loads are individually state-preserving but excluded to keep the
    predicate one-directional and small). -/
def stateInert : CoreExpr → Bool
  | Expr _ (Esseq _ e1 e2) => stateInert e1 && stateInert e2
  | Expr _ (Ewseq _ e1 e2) => stateInert e1 && stateInert e2
  | Expr _ (Eannot _ b) => stateInert b
  | Expr _ (Eif _ e2 e3) => stateInert e2 && stateInert e3
  | Expr _ (Esave _ _ body) => stateInert body
  | Expr _ (Eaction _) => false
  | Expr _ (Ememop _ _) => false
  | Expr _ (Ecase _ _) => false
  | _ => true

/-- Every registered label body is state-inert. -/
def StateInertLabels (M : MachineCtx) (ctl : Ctl) : Prop :=
  ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
    stateInert cont = true

/-- State-inert cone steps preserve the memory state, and inertness
    is preserved (or the step is the jump, which also preserves the
    state). -/
theorem Frag.stateInert_step {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {ctl : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : Frag e) (hin : stateInert e = true)
    (hs : Step M (e, ρ, ctl, σ) (e', ρ', ctl, σ')) :
    σ' = σ ∧ (stateInert e' = true ∨
      ∃ l pes params cont, jumpRedex? e = some (l, pes) ∧
        lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧ e' = cont) := by
  induction hf generalizing e' ρ' σ' with
  | call hpes hdep => exact (Step.call_ne_same_ctl (callRedex?_callRedex _ _ _) hs).elim
  | val_pure v => exact (Step.pure_val_elim hs rfl).elim
  | store => simp [stateInert, storeRedex] at hin
  | load => simp [stateInert, loadRedex] at hin
  | create => simp [stateInert, createRedex] at hin
  | kill => simp [stateInert, killRedex] at hin
  | kill_op hnvK hpK hdK => simp [stateInert, killOpRedex] at hin
  | alloc => simp [stateInert, allocRedex] at hin
  | alloc_op hnvA hp1 hp2 hd1 hd2 => simp [stateInert, allocOpRedex] at hin
  | sseq hf1 hf2 ih1 ih2 =>
    obtain ⟨hin1, hin2⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, Bool.and_eq_true] using hin
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds', v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ih1 hin1 hstep
      rcases hin' with hin1' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by
          simp [stateInert, Bool.and_eq_true, hin1', hin2])⟩
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl (by simpa [stateInert] using hin2)⟩
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_sseq, hj], hl, h1⟩⟩
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
    · exact hcall.ne_same_ctl.elim
  | wseq hf1 hf2 ih1 ih2 =>
    obtain ⟨hin1, hin2⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, Bool.and_eq_true] using hin
    rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds', v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ih1 hin1 hstep
      rcases hin' with hin1' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by
          simp [stateInert, Bool.and_eq_true, hin1', hin2])⟩
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl (by simpa [stateInert] using hin2)⟩
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_wseq, hj], hl, h1⟩⟩
    · exact hcall.ne_same_ctl.elim
  | annot hfb ihb =>
    rename_i ds0 b0
    have hinb : stateInert b0 = true := by simpa [stateInert] using hin
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩ |
        ⟨-, hcall⟩ | ⟨v', pc', κ', ha', hb', hκ', hout'⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ihb hinb hstep
      rcases hin' with hinb' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by simpa [stateInert] using hinb')⟩
      · rw [hnj] at hj1
        cases hj1
    · subst hb
      obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      refine ⟨h3, .inl ?_⟩
      have : stateInert c = true := by simpa [stateInert] using hinb
      simpa [stateInert] using this
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_annot_of_not_root _ _ hg, hj], hl, h1⟩⟩
    · exact hcall.ne_same_ctl.elim
    · obtain ⟨rfl, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by simpa [Prod.mk.injEq] using hout'
      exact ⟨h3, .inl rfl⟩
  | save hp hd hb ih =>
    rcases hs.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
        ⟨cvals, hnv, hvals, hout⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl (by simpa [stateInert, saveRedex] using hin)⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl (by simpa [stateInert, saveRedex] using hin)⟩
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    obtain ⟨hin2, hin3⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, ifRedex, Bool.and_eq_true] using hin
    rcases hs.if_inv with ⟨-, hout⟩ | ⟨-, hout⟩ <;>
      (obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout)
    · subst h1
      exact ⟨h3, .inl hin2⟩
    · subst h1
      exact ⟨h3, .inl hin3⟩
  | run hpes hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    exact ⟨h3, .inr ⟨_, _, params, cont, rfl, hl, h1⟩⟩
  | sseq_spec hf1 hf2 ih1 ih2 =>
    obtain ⟨hin1, hin2⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, Bool.and_eq_true] using hin
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ih1 hin1 hstep
      rcases hin' with hin1' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by
          simp [stateInert, Bool.and_eq_true, hin1', hin2])⟩
      · rw [hnj] at hj1
        cases hj1
    · exact (specPat_ne_base hpat.symm).elim
    · exact (specPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_sseq, hj], hl, h1⟩⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl (by simpa [stateInert] using hin2)⟩
    · exact (symPat_ne_spec hpat).elim
    · exact hcall.ne_same_ctl.elim
  | pure_sym =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv rfl
    obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact ⟨h3, .inl rfl⟩
  | load_op hnv2 hp2 hd2 => simp [stateInert, loadOpRedex] at hin
  | sseq_sym hb hf1 hf2 ih1 ih2 =>
    obtain ⟨hin1, hin2⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, Bool.and_eq_true] using hin
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hnv', hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ih1 hin1 hstep
      rcases hin' with hin1' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by
          simp [stateInert, Bool.and_eq_true, hin1', hin2])⟩
      · rw [hnj] at hj1
        cases hj1
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_sseq, hj], hl, h1⟩⟩
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
    · exact hcall.ne_same_ctl.elim
  | memop_vals v1 v2 => simp [stateInert, memopPtrEqVals, memopRedex] at hin
  | memop_op hnv hp1 hp2 hpd1 hpd2 => simp [stateInert, memopRedex] at hin
  | store_op hnv hp2 hp3 hpd2 hpd3 =>
    simp [stateInert, storeOpRedex] at hin
  | case_value hbr hbsz =>
    simp [stateInert, caseRedex] at hin

/-! ## THE GENERIC MEASURE→DRIVE-FUEL SIMULATION (the cost half) -/

/-- The engine-readout postcondition shape both launch theorems
    consume (the total analog of the partial lane's readout wand). -/
abbrev readoutPost {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (ψ : value → Mem → Prop) : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
    stateInterp σ' ns κs nt ={⊤,∅}=∗ ⌜ψ w.val σ'⌝)

/-! ## Readout plumbing for sequenced prefixes: the engine readout
only reads the ERASED value, so an annotation-merge on the sequenced
value is absorbed (the LETS-ANNOT residue of a prefix store never
reaches ψ). -/

theorem val_mergeInto_annot (ds : List dyn_annotation) (v : value)
    (u : SpikeVal) :
    (SpikeVal.mergeInto (.annot ds v) u).val = u.val := by
  cases u <;> rfl

theorem readoutPost_mergeInto_annot {GF : BundledGFunctors}
    [SpikeGS .hasLC GF] (ψ : value → Mem → Prop)
    (ds : List dyn_annotation) (v : value) :
    (fun (u : SpikeVal) (ρ' : EnvStack) =>
      readoutPost (GF := GF) ψ (SpikeVal.mergeInto (.annot ds v) u) ρ') =
    (fun (u : SpikeVal) (ρ' : EnvStack) => readoutPost (GF := GF) ψ u ρ') := by
  funext u ρ'
  unfold readoutPost
  rw [val_mergeInto_annot ds v u]

/-- The engine readout only reads the ERASED value, so a prefix
    store's annotation-merge is absorbed (element-wise face of
    `readoutPost_mergeInto_annot`, robust against the abbrev's
    unfolding under unification). -/
theorem readoutPost_annot_absorb {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (ψ : value → Mem → Prop) (ds : List dyn_annotation) (v : value)
    (u : SpikeVal) (ρ' : EnvStack) :
    readoutPost (GF := GF) ψ u ρ' ⊢
      readoutPost ψ (SpikeVal.mergeInto (.annot ds v) u) ρ' := by
  rw [congrFun (congrFun (readoutPost_mergeInto_annot ψ ds v) u) ρ']

/-- Monotonicity of the readout in the pure postcondition. -/
theorem readoutPost_mono {hlc : HasLC} {GF : BundledGFunctors}
    [SpikeGS hlc GF] {ψ ψ' : value → Mem → Prop}
    (h : ∀ v σ, ψ v σ → ψ' v σ) (w : SpikeVal) (ρ' : EnvStack) :
    readoutPost (GF := GF) ψ w ρ' ⊢ readoutPost ψ' w ρ' := by
  iintro H %σ' %ns %κs %nt Hσ
  imod H $$ %σ' %ns %κs %nt Hσ with %hp
  ipureintro
  exact h _ _ hp


/-- The simulation's pure conclusion: the drive at fuel k DELIVERS,
    the delivered value and final state satisfy the readout, and on
    the state-inert cone the final state is the initial one. -/
abbrev DriveDoneAt (M : MachineCtx) (ctl : Ctl) (aids : Nat → Nat) (k : Nat) (e : CoreExpr)
    (ρ : EnvStack) (σ : Mem) (ψ : value → Mem → Prop) : Prop :=
  ∃ v σ', driveU M aids k (M.thread e ρ ctl) σ = .done v σ' ∧ ψ v σ' ∧
    (stateInert e = true ∧ StateInertLabels M ctl → σ' = σ)

/-- THE SIMULATION (audit F-02, the cost half): the total statement
    judgment's budget IS drive fuel — one `driveU` step
    (`outcomesU_of_step`, the device lemma) per budget unit, the delivery protocol
    prepaid by the value clause, jumps prepaid by the mandatory
    decrease. Strong induction on the budget; no Löb, no
    step-indexing, no per-example Step chains ever again. -/
theorem wpt_drive_aux {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    {M : MachineCtx} (hwf : M.SeqWF) {ctl : Ctl} (hκ : ctl.κ = [])
    (hQf : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : LabelSpecT GF) (ψ : value → Mem → Prop) :
    ∀ (k : Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem) (ns nt : Nat) (aids : Nat → Nat),
      Frag e → pot e ≤ lemDefaultFuel →
      iprop(stateInterp (GF := GF) σ ns ([] : List Empty) nt ∗
          blockSpecsT M ctl.proc Ls emptyProcSpecT (readoutPost ψ) ∗
          wpt M ctl.proc Ls emptyProcSpecT k (readoutPost ψ) e (ev0 :: evs)) ⊢
        iprop(|={⊤|}=> ⌜DriveDoneAt M ctl aids k e (ev0 :: evs) σ ψ⌝) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
  intro e ev0 evs σ ns nt aids hfrag hpot
  cases htv : toVal e with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k (toVal_ofVal w)]
    iintro ⟨Hσ, -, ⟨%hc, Hpost⟩⟩
    imod Hpost with Hpost
    imod Hpost $$ %σ %ns %([] : List Empty) %nt Hσ with %hψ
    ipureintro
    cases w with
    | pure v =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
        have hc' : 1 ≤ k := by simpa [deliveryCost] using hc
        omega⟩
      refine ⟨v, σ, ?_, hψ, fun _ => rfl⟩
      rw [driveU_succ, stepOutcomes_thread, outcomesU_done hwf hκ]
    | annot ds v =>
      obtain ⟨k'', rfl⟩ : ∃ k'', k = k'' + 2 := ⟨k - 2, by
        have hc' : 2 ≤ k := by simpa [deliveryCost] using hc
        omega⟩
      refine ⟨v, σ, ?_, hψ, fun _ => rfl⟩
      rw [show k'' + 2 = (k'' + 1) + 1 from rfl,
        show driveU M aids (k'' + 1 + 1)
            (M.thread (ofVal (.annot ds v)) (ev0 :: evs) ctl) σ =
          driveU M (fun i => aids (i + 1)) (k'' + 1)
            (M.thread (ofVal (.pure v)) (ev0 :: evs) ctl) σ from by
          rw [driveU_succ, stepOutcomes_thread, outcomesU_remove_annot],
        driveU_succ, stepOutcomes_thread, outcomesU_done hwf hκ]
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq k htv hjr]
      iintro ⟨Hσ, #HB, HJ⟩
      imod HJ with ⟨%params, %cont, %vs, %ev0', %evs', %m, %hρ, %hl, %hvs,
        %hμ, HLs⟩
      obtain ⟨rfl, rfl⟩ : ev0 = ev0' ∧ evs = evs' := by
        injection hρ with h1 h2
        exact ⟨h1, h2⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hs : Step M (e, ev0 :: evs, ctl, σ)
          (cont, bindArgs params vs (ev0 :: evs), ctl, σ) :=
        Step.run_of_jumpRedex hjr hl hvs
      obtain ⟨ev0'', hbind⟩ := Step.env_cons hs
      ihave Hwpt := HB $$ %l %params %cont %vs %ev0 %evs %m %hl HLs
      ihave Hwpt' : wpt M ctl.proc Ls emptyProcSpecT k' (readoutPost ψ) cont
          (bindArgs params vs (ev0 :: evs)) $$ [Hwpt]
      · iapply wpt_mono_k (show m ≤ k' by omega) cont _ $$ Hwpt
      rw [hbind]
      have hstep_eq : driveU M aids (k' + 1) (M.thread e (ev0 :: evs) ctl) σ =
          driveU M (fun i => aids (i + 1)) k'
            (M.thread cont (ev0'' :: evs) ctl) σ := by
        rw [driveU_succ, stepOutcomes_thread,
          outcomesU_of_step (aids 0) hfrag
            (Nat.le_trans hfrag.esize_le_pot hpot) hs, hbind]
      have hf : DriveDoneAt M ctl (fun i => aids (i + 1)) k' cont
            (ev0'' :: evs) σ ψ →
          DriveDoneAt M ctl aids (k' + 1) e (ev0 :: evs) σ ψ := by
        rintro ⟨v, σ', hdone, hψ, hin⟩
        refine ⟨v, σ', ?_, hψ, ?_⟩
        · rw [hstep_eq]
          exact hdone
        · rintro ⟨hinE, hinL⟩
          exact hin ⟨hinL l params cont hl, hinL⟩
      iapply fupd_finally_mono (pure_mono hf)
      iapply IH k' (Nat.lt_succ_self k') cont ev0'' evs σ ns nt
        (fun i => aids (i + 1)) (hQf l params cont hl)
        (hQpot l params cont hl) $$ [$Hσ $HB $Hwpt']
    | none =>
      cases hcr : callRedex? e with
      | some q =>
        iintro ⟨-, -, H⟩
        ihave H := wpt_empty_call_false htv hjr hcr $$ H
        imod H with %hf
        exact hf.elim
      | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq htv hjr hcr]
        iintro ⟨-, -, %hf⟩
        exact hf.elim
      | succ k' =>
        rw [wpt_step_eq k' htv hjr hcr]
        iintro ⟨Hσ, #HB, H⟩
        imod H $$ %(ctl.κ) %(ctl.execLoc) %σ %ns %([] : List Empty) %nt Hσ with ⟨%hred, Hwand⟩
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs, hM, hnil⟩ := hps
        subst hnil
        obtain ⟨re, rρ, rctl, rM⟩ := r'
        simp only at hs hM
        obtain rfl : M = rM := hM.symm
        obtain rfl : ctl = rctl := (Step.ctl_eq hs hcr htv).symm
        obtain ⟨ev0', rfl⟩ := Step.env_cons hs
        imod Hwand $$ %(⟨re, ev0' :: evs, ctl, M⟩ : CoreRt) %σ' %([] : List CoreRt)
          %(⟨hs, rfl, rfl⟩ :
            ((⟨e, ev0 :: evs, ctl, M⟩ : CoreRt), σ) -<([] : List Empty)>->
              ((⟨re, ev0' :: evs, ctl, M⟩ : CoreRt), σ', []))
          with ⟨Hσ', Hwpt⟩
        have hfrag' : Frag re := hfrag.step hQf hs
        have hpot' : pot re ≤ lemDefaultFuel := by
          rcases Frag.pot_step_bound hfrag hs with hle |
              ⟨l0, pes0, params0, cont0, hj0, hl0, rfl⟩
          · omega
          · rw [hjr] at hj0
            cases hj0
        have hstep_eq : driveU M aids (k' + 1) (M.thread e (ev0 :: evs) ctl) σ =
            driveU M (fun i => aids (i + 1)) k'
              (M.thread re (ev0' :: evs) ctl) σ' := by
          rw [driveU_succ, stepOutcomes_thread,
            outcomesU_of_step (aids 0) hfrag
              (Nat.le_trans hfrag.esize_le_pot hpot) hs]
        have hf : DriveDoneAt M ctl (fun i => aids (i + 1)) k' re
              (ev0' :: evs) σ' ψ →
            DriveDoneAt M ctl aids (k' + 1) e (ev0 :: evs) σ ψ := by
          rintro ⟨v, σ'', hdone, hψ, hin⟩
          refine ⟨v, σ'', ?_, hψ, ?_⟩
          · rw [hstep_eq]
            exact hdone
          · rintro ⟨hinE, hinL⟩
            obtain ⟨hσeq, hin'⟩ := hfrag.stateInert_step hinE hs
            rcases hin' with hinE' | ⟨l0, pes0, _, _, hj0, -, -⟩
            · rw [hin ⟨hinE', hinL⟩, hσeq]
            · rw [hjr] at hj0
              cases hj0
        iapply fupd_finally_mono (pure_mono hf)
        iapply IH k' (Nat.lt_succ_self k') re ev0' evs σ' (ns + 1) nt
          (fun i => aids (i + 1)) hfrag' hpot' $$ [$Hσ' $HB $Hwpt]

/-! ## The launch: pure engine conclusions from a SpikeGpreS functor
list (the total analog of `engine_adequacyU`) -/

/-- THE TOTAL ENGINE BOUND at any machine context (the cost half's
    engine face): a proved total judgment at budget k plus the
    seeded footprint implies the drive AT FUEL k delivers a value
    satisfying ψ — an unconditional `.done` equation, no partiality;
    state pinned on the state-inert cone. PROVISIONAL: stated over
    `driveU` (module header). -/
theorem wpt_engine_boundU {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF) {ctl : Ctl} (hκ : ctl.κ = [])
    (hQf : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel) (hcoh : Coh M.tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c)) ⊢
        iprop(blockSpecsT M ctl.proc Ls emptyProcSpecT (readoutPost ψ) ∗
          wpt M ctl.proc Ls emptyProcSpecT k (readoutPost ψ) e₀ (ev00 :: evs0)))
    (aids : Nat → Nat) :
    ∃ v σ', driveU M aids k (M.thread e₀ (ev00 :: evs0) ctl) σ₀ = .done v σ' ∧
      ψ v σ' ∧ (stateInert e₀ = true ∧ StateInertLabels M ctl → σ' = σ₀) := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine (fupd_finally_soundness .hasLC 0 ⊤ _ ?_)
  iintro %Hinv Hcred
  letI : InvGS_gen .hasLC GF := Hinv
  icases Hcred with -
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  imod budgetInit with ⟨%Gc, HBa⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk, budgetGS := Gc }
  ihave HB0 := budgetAuth_of_init (hlc := .hasLC) (GF := GF) $$ HBa
  imod (spikeCells_alloc M.tagDefs σ₀ m₀ hcoh) $$ [$Hmi $Hbi]
    with ⟨%mm, %mb, %hmbo, Hmi, Hbi, Hcells⟩
  ihave HW := hwp $$ Hcells
  icases HW with ⟨HB, Hwpt⟩
  ihave Hσ : stateInterp (GF := GF) σ₀ 0 ([] : List Empty) 0 $$ [Hmi Hbi Hki HB0]
  · rw [stateInterp_eq]
    iexists mm, mb, (∅ : SpikeHeapF AllocCursor)
    isplit
    · ipureintro
      exact hmbo.cohG hcoh
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    isplitl [Hki]
    · iexact Hki
    · iapply budgetInterp_zero
      iexact HB0
  iapply wpt_drive_aux hwf hκ hQf hQpot Ls ψ k e₀ ev00 evs0 σ₀ 0 0 aids
    hfrag hpot $$ [$Hσ $HB $Hwpt]

/-- ALLOCATION-AWARE total engine bound (alloc arc P1.3): as
    `wpt_engine_boundU`, but launched through the one shared
    `launchResources` helper — the client's total proof receives the
    footprint cells AND the budget `allocBudget B` (K2.5); the cursor ghost heap is
    launched NONEMPTY at the real `⟨lastAddress, nextAllocId⟩`. The
    cursor-free launcher above remains for no-allocation programs
    (charter P1.3's incremental-migration allowance). PROVISIONAL:
    stated over `driveU` (module header). -/
theorem wpt_engine_boundU_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF) {ctl : Ctl} (hκ : ctl.κ = [])
    (hQf : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell) (B : Nat)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel)
    (hl : LaunchCoh M.tagDefs σ₀ m₀ B)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c) ∗ allocBudget B) ⊢
        iprop(blockSpecsT M ctl.proc Ls emptyProcSpecT (readoutPost ψ) ∗
          wpt M ctl.proc Ls emptyProcSpecT k (readoutPost ψ) e₀ (ev00 :: evs0)))
    (aids : Nat → Nat) :
    ∃ v σ', driveU M aids k (M.thread e₀ (ev00 :: evs0) ctl) σ₀ = .done v σ' ∧
      ψ v σ' ∧ (stateInert e₀ = true ∧ StateInertLabels M ctl → σ' = σ₀) := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine (fupd_finally_soundness .hasLC 0 ⊤ _ ?_)
  iintro %Hinv Hcred
  letI : InvGS_gen .hasLC GF := Hinv
  icases Hcred with -
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  imod budgetInit with ⟨%Gc, HBa⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk, budgetGS := Gc }
  ihave HB0 := budgetAuth_of_init (hlc := .hasLC) (GF := GF) $$ HBa
  imod (launchResources M.tagDefs σ₀ m₀ B hl) $$ [$Hmi $Hbi $Hki $HB0]
    with ⟨Hσ, Hcells, Hcap⟩
  ihave HW := hwp $$ [$Hcells $Hcap]
  icases HW with ⟨HB, Hwpt⟩
  iapply wpt_drive_aux hwf hκ hQf hQpot Ls ψ k e₀ ev00 evs0 σ₀ 0 0 aids
    hfrag hpot $$ [$Hσ $HB $Hwpt]

end CerberusHeapLang
