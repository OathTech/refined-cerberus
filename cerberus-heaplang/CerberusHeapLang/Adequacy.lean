/-
CerberusHeapLang.Adequacy — adequacy: where proofs in the derived
logic become facts about the engine's execution.

Three layers:
1. `drive` — the ENGINE'S EXECUTION at the frozen minimal context:
   the discharge loop {step_ctx → Driver.lean:273 discharge} as a
   definition over engine objects (thread_state, MemState,
   core_step2), with an explicit per-step action-id supply and
   explicit fuel. Engine vocabulary only.
2. `spike_step_adequacy` — the Iris adequacy instance: the bundled
   ghost state `SpikeGS` is CONSTRUCTED here (genHeap_init over the
   initial cell map), and iris-lean's `wp_strong_adequacy_gen`
   yields NotStuck + postcondition readout for every Step-reachable
   configuration. HeapLang's heap_adequacy
   (Iris/HeapLang/PrimitiveLaws.lean:131) is the template; the
   strong variant is needed because the fragment's postconditions
   read out the FINAL MEMORY STATE (through the state
   interpretation), not just the value.
3. `spike_engine_adequacy` — THE ENGINE-ONLY STATEMENT: a proved WP
   plus a seeded MemState satisfying the precondition footprint
   implies the engine's drive never kills (no UB, no error kill, no
   ILLTYPED refusal, no off-protocol step) and any final value+state
   it delivers satisfies the postcondition readout. The CONCLUSION
   quantifies over engine objects only (the program term, the
   MemState, drive fuel, the action-id supply, DriveResult); Step /
   WP / Iris vocabulary appears only in the hypotheses (that is the
   point: the derived logic's guarantees land as engine facts).

Certification direction used (Soundness.lean header): engine-
completeness. Each drive step is `engine_complete`'s unique engine
behavior; Step-matched behaviors stay in the WP-covered cone,
refusals contradict NotStuck, and the value protocol composes the
REMOVE-ANNOT tau with PROGRAM-DONE (annotations erased by
`SpikeVal.val` in the readout — the value-classification divergence
registered in Step.lean's `SpikeVal` docstring).

FUEL HONESTY (inherited): `esize e₀ + n ≤ lemDefaultFuel` bounds the
drive length so get_ctx's opaque fuel-exhaustion leaf stays
unreachable (Soundness.lean header). Termination is NOT claimed
(partial correctness): `.more` carries no obligation.
-/
import CerberusHeapLang.Rules
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib
open Iris.Std.PartialMap in
section


/-! ## The engine drive -/

/-- Result of driving the engine for a bounded number of steps. -/
inductive DriveResult : Type where
  /-- fuel ran out with the machine resting here (no claim is made) -/
  | more (th : thread_state) (σ : Mem)
  /-- PROGRAM-DONE: the engine delivered a value -/
  | done (v : value) (σ : Mem)
  /-- the engine killed: `Undef0` (UB), `Error0`, or `Other`
      (the full loadM/storeM failure vocabulary —
      docs/2026-08-30_spike-recon.md §2.6) -/
  | killed (r : kill_reason mem_error)
  /-- refusal (Step_error2 / ILLTYPED) or any off-protocol engine
      behavior -/
  | stuck

/-- One drive scrutinee at a machine context (the {step_ctx →
    discharge} composite the loop iterates). -/
def stepOutcomes (M : MachineCtx) (aid : Nat) (th : thread_state)
    (σ : Mem) : List EngineOutcome :=
  (step_ctx M.tagDefs σ M.file M.extern M.tid (M.parent, th)).map
    (dischargeStep aid M.runState σ)

theorem stepOutcomes_thread (M : MachineCtx) (aid : Nat) (e : CoreExpr)
    (ρ : EnvStack) (σ : Mem) :
    stepOutcomes M aid (M.thread e ρ) σ = outcomesU M aid e ρ σ := rfl

/-- THE ENGINE'S EXECUTION AT A MACHINE CONTEXT (S1b — the ONE
    drive): iterate {`step_ctx` → `dischargeStep`} with every
    immutable drawn from the context (the sequential driver's loop
    projected to (thread_state, MemState) — Soundness.lean header
    for the cited projections). `aids` supplies the driver's
    per-step action-id draws (Driver.lean:284); the fragment ignores
    them (D2), and the theorems hold for every supply. -/
def driveU (M : MachineCtx) (aids : Nat → Nat) :
    Nat → thread_state → Mem → DriveResult
  | 0, th, σ => .more th σ
  | n+1, th, σ =>
    match stepOutcomes M (aids 0) th σ with
    | [.next th' σ'] => driveU M (fun i => aids (i+1)) n th' σ'
    | [.done v] => .done v σ
    | [.killed r] => .killed r
    | _ => .stuck

/-- The succ-step equation of the unified drive (rfl, named for
    rewriting). -/
theorem driveU_succ (M : MachineCtx) (aids : Nat → Nat) (n : Nat)
    (th : thread_state) (σ : Mem) :
    driveU M aids (n+1) th σ =
      (match stepOutcomes M (aids 0) th σ with
        | [.next th' σ'] => driveU M (fun i => aids (i+1)) n th' σ'
        | [.done v] => DriveResult.done v σ
        | [.killed r] => DriveResult.killed r
        | _ => DriveResult.stuck) := rfl

/-- THE ENGINE'S EXECUTION at the frozen straight-line context — the
    `spikeCtx` INSTANCE of the one drive (S1b: the drive/driveJ split
    disappears; the exported statements keep their vocabulary through
    these definitional instances). The body is definitionally the old
    frozen-profile loop. -/
def drive (aids : Nat → Nat) : Nat → thread_state → Mem → DriveResult :=
  driveU spikeCtx aids

/-- The succ-step equation at the straight-line instance, in the old
    frozen spelling (rfl — rewriting aid for the simulation lemmas). -/
theorem drive_succ_eq (aids : Nat → Nat) (n : Nat) (th : thread_state)
    (σ : Mem) :
    drive aids (n+1) th σ =
      (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
          (dischargeStep (aids 0) spikeRunState σ) with
        | [.next th' σ'] => drive (fun i => aids (i+1)) n th' σ'
        | [.done v] => DriveResult.done v σ
        | [.killed r] => DriveResult.killed r
        | _ => DriveResult.stuck) := rfl

/-- The drive's one-step scrutinee at an envThread arena IS
    `engineOutcomes` (definitional). -/
theorem drive_scrutinee_env (aid : Nat) (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, envThread e ρ)).map
        (dischargeStep aid spikeRunState σ) = engineOutcomes aid e ρ σ := rfl

/-- ... at the exported entry env. -/
theorem drive_scrutinee (aid : Nat) (e : CoreExpr) (σ : Mem) :
    (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, spikeThread e)).map
        (dischargeStep aid spikeRunState σ) = engineOutcomes aid e spikeEnv σ := rfl

/-! ## Step chains and iris thread-pool reachability -/

/-- Reachability along the fragment's Step (single thread; env-
    carrying configurations, S1). -/
def Reach : CoreRt × Mem → CoreRt × Mem → Prop :=
  Relation.ReflTransGen (fun a b =>
    Step a.1.M (a.1.e, a.1.ρ, a.2) (b.1.e, b.1.ρ, b.2) ∧ b.1.M = a.1.M)

/-- Transport into the iris thread-pool reduction (the pool stays a
    singleton: the fragment forks nothing). -/
theorem Reach.toPool {c c' : CoreRt × Mem} (h : Reach c c') :
    ([c.1], c.2) -·->ₜₚ* ([c'.1], c'.2) := by
  induction h with
  | refl => exact .refl
  | @tail b b' hr hstep ih =>
    exact ih.tail ⟨([] : List Empty),
      Language.Step.of_primStep (⟨hstep.1, hstep.2, rfl⟩ :
        PrimStep.primStep (b.1, b.2) ([] : List Empty)
          (b'.1, b'.2, ([] : List CoreRt)))
        (t₁ := []) (t₂ := [])⟩

/-! ## Step-level adequacy: constructing SpikeGS and applying iris -/

/-- Iris adequacy over Step, with final-state readout: constructs
    the bundled ghost state (SpikeGS — nothing is assumed
    pre-allocated) from the initial cell map and applies
    `wp_strong_adequacy_gen`. The postcondition is a readout wand:
    it consumes the final state interpretation, so cell ownership at
    the end pins facts about the FINAL MemState. -/
theorem spike_step_adequacy {GF : BundledGFunctors} [SpikeGpreS GF]
    (e : CoreRt) (σ : Mem) (m₀ : SpikeHeapF SpikeCell) (hcoh : Coh σ m₀)
    (φp : CoreRVal → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, pointsTo i (.own 1) c)) ⊢
        WP e @ Stuckness.NotStuck; ⊤ {{ v, iprop(∀ (σ' : Mem) (ns : Nat)
          (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜φp v σ'⌝) }})
    {t2 : List CoreRt} {σ2 : Mem}
    (hreach : ([e], σ) -·->ₜₚ* (t2, σ2)) :
    (∀ e2 ∈ t2, PrimStep.NotStuck (Val := CoreRVal) (e2, σ2)) ∧
    (∀ (w : CoreRVal) (t2' : List CoreRt), t2 = ofValRt w :: t2' → φp w σ2) := by
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF) (hlc := .hasLC) Stuckness.NotStuck [e] σ n κs t2 σ2 _
    (fun _ => 0) ?_ hsteps
  intro instInv
  imod (genHeap_init (H := SpikeHeapF) m₀) with ⟨%G, Hint, Hpts, Htok⟩
  letI instGS : SpikeGS .hasLC GF := { heap := G }
  imodintro
  iexists fun (σ' : Mem) (_ : Nat) (_ : List Empty) (_ : Nat) =>
    iprop(∃ m, ⌜Coh σ' m⌝ ∗ genHeapInterp m)
  iexists [fun (v : CoreRVal) => iprop(∀ (σ' : Mem) (ns : Nat)
    (κs' : List Empty) (nt : Nat), stateInterp σ' ns κs' nt ={⊤, ∅}=∗ ⌜φp v σ'⌝)]
  iexists fun _ => iprop(True)
  iexists fun _ _ _ _ => fupd_intro
  dsimp only
  isplitl [Hint]
  · iexists m₀
    isplit
    · ipureintro
      exact hcoh
    · iexact Hint
  isplitl [Hpts]
  · iapply BigSepL2.bigSepL2_singleton
    ihave HW := hwp $$ Hpts
    iexact HW
  iintro %es' %t2' %heqt %hlen %hnsp Hst Hposts Hforks
  have hns : ∀ e2 ∈ t2, PrimStep.NotStuck (Val := CoreRVal) (e2, σ2) :=
    fun e2 he2 => hnsp e2 rfl he2
  obtain ⟨e1', rfl⟩ : ∃ x, es' = [x] := by
    cases es' with
    | nil => simp at hlen
    | cons a l =>
      cases l with
      | nil => exact ⟨a, rfl⟩
      | cons b l' => simp at hlen
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hposts with ⟨%eh, %Φt, %HeqΦ, Hpost, Hrest⟩
  cases hv : ToVal.toVal (Val := CoreRVal) eh with
  | none =>
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    refine ⟨hns, fun w t2'' heq2 => ?_⟩
    rw [heqt] at heq2
    injection HeqΦ with h1 h2
    subst h1
    injection heq2 with h3 h4
    rw [h3, language_toVal_eq, toValRt_ofValRt] at hv
    cases hv
  | some w =>
    dsimp only [Option.elim_some]
    imod Hpost $$ %σ2 %n %([] : List Empty) %(t2'.length) Hst with %hφw
    ipureintro
    refine ⟨hns, fun w' t2'' heq2 => ?_⟩
    rw [heqt] at heq2
    injection HeqΦ with h1 h2
    subst h1
    injection heq2 with h3 h4
    rw [h3, language_toVal_eq, toValRt_ofValRt] at hv
    injection hv with h5
    subst h5
    exact hφw

/-! ## The drive classification -/

/-- What each drive outcome must satisfy: fuel exhaustion is
    unconstrained (partial correctness), delivered values carry the
    postcondition (with the D1 annotation erasure: the delivered
    engine value is `w.val` for the WP-level value `w`), and the
    killed/stuck channels are unreachable. -/
def DriveOk (φp : CoreRVal → Mem → Prop) : DriveResult → Prop
  | .more _ _ => True
  | .done v σ' => ∃ w : CoreRVal, w.val = v ∧ φp w σ'
  | .killed _ => False
  | .stuck => False

/-- Driving a bare value at any SeqWF context: PROGRAM-DONE. -/
theorem driveU_value_pure {M : MachineCtx} (hwf : M.SeqWF)
    (φp : CoreRVal → Mem → Prop) (aids : Nat → Nat)
    (v : value) (ρ : EnvStack) (σ : Mem)
    (h : ∃ w : CoreRVal, w.val = v ∧ φp w σ) :
    ∀ n, DriveOk φp (driveU M aids n (M.thread (ofVal (.pure v)) ρ) σ)
  | 0 => trivial
  | n+1 => by
    rw [driveU_succ, stepOutcomes_thread, outcomesU_done hwf]
    exact h

/-- THE UNIFIED CLASSIFICATION (S1b — the one drive classification,
    at any machine context; the straight-line and jump lanes are its
    instances): from StepU-level NotStuck + value readout over
    `Reach`, every driveU outcome is DriveOk — via
    `engine_step_matchU`, one certification case per step. The old
    J-lane's `LabeledAt` tie hypothesis is GONE (context-derived);
    the label cone/budget hypotheses remain (registered continuations
    are the jump targets). The S1a probe's extern restriction is
    RETIRED (S1b′ — extern threaded through the evaluator bridge
    tower, design record §5.2): the context is arbitrary. -/
theorem drive_classifyU {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (n₀ : Nat)
    (hQsz : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      esize cont + n₀ ≤ lemDefaultFuel)
    (e₀ : CoreExpr) (ρ₀ : EnvStack) (σ₀ : Mem)
    (φp : CoreRVal → Mem → Prop)
    (hNS : ∀ (r : CoreRt) (σ : Mem),
      Reach ((⟨e₀, ρ₀, M⟩ : CoreRt), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRVal) (r, σ))
    (hRES : ∀ (w : CoreRVal) (σ : Mem),
      Reach ((⟨e₀, ρ₀, M⟩ : CoreRt), σ₀) (ofValRt w, σ) → φp w σ) :
    ∀ (n : Nat), n ≤ n₀ →
    ∀ (aids : Nat → Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem),
      Reach ((⟨e₀, ρ₀, M⟩ : CoreRt), σ₀) ((⟨e, ev0 :: evs, M⟩ : CoreRt), σ) →
      Frag e → esize e + n ≤ lemDefaultFuel →
      DriveOk φp (driveU M aids n (M.thread e (ev0 :: evs)) σ) := by
  intro n
  induction n with
  | zero => intro _ aids e ev0 evs σ _ _ _; trivial
  | succ n ih =>
    intro hn₀ aids e ev0 evs σ hreach hf hfuel
    cases hv : toVal e with
    | some w =>
      have he := ofVal_of_toVal hv
      subst he
      cases w with
      | pure v =>
        exact driveU_value_pure hwf φp aids v (ev0 :: evs) σ
          ⟨⟨.pure v, ev0 :: evs, M⟩, rfl,
            hRES ⟨.pure v, ev0 :: evs, M⟩ σ hreach⟩ (n+1)
      | annot ds v =>
        rw [driveU_succ, stepOutcomes_thread, outcomesU_remove_annot]
        exact driveU_value_pure hwf φp _ v (ev0 :: evs) σ
          ⟨⟨.annot ds v, ev0 :: evs, M⟩, rfl,
            hRES ⟨.annot ds v, ev0 :: evs, M⟩ σ hreach⟩ n
    | none =>
      rcases hNS ⟨e, ev0 :: evs, M⟩ σ hreach with hval | ⟨obs, r', σ', efs, hprim⟩
      · rw [language_toVal_eq, toValRt_mk, hv] at hval
        cases hval
      · obtain ⟨hs, hM, -⟩ := hprim
        obtain ⟨re', rρ', rM'⟩ := r'
        simp only at hs hM
        obtain rfl : M = rM' := hM.symm
        obtain ⟨ev0', rfl⟩ := Step.env_cons hs
        rw [driveU_succ, stepOutcomes_thread,
          engine_step_matchU (aids 0) hf (by omega) hs]
        refine ih (by omega) _ re' ev0' evs σ'
          (hreach.tail ⟨hs, rfl⟩) (hf.step hQf hs) ?_
        rcases hf.esize_step_bound hs with hle | ⟨l, pes, params, cont, -, hl, hec⟩
        · omega
        · rw [hec]
          have := hQsz l params cont hl
          omega

/-- ADEQUACY AT A MACHINE CONTEXT (engine-only conclusion, the one
    adequacy of which the straight-line and jump exports are
    instances): a proved WP at the unified tuple plus the seeded
    memory implies driveU from the context's thread never kills,
    never derails, and any delivered value satisfies the readout.
    Explicit WF hypothesis (statement-change class (D)): `SeqWF`.
    The S1a probe's extern restriction is retired (S1b′). -/
theorem engine_adequacyU {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hcoh : Coh σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, pointsTo i (.own 1) c)) ⊢
        WP (⟨e₀, ev00 :: evs0, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, iprop(∀ (σ' : Mem) (ns : Nat)
          (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝) }})
    (n : Nat) (aids : Nat → Nat)
    (hfuel : esize e₀ + n ≤ lemDefaultFuel)
    (hQsz : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      esize cont + n ≤ lemDefaultFuel) :
    (∀ r, driveU M aids n (M.thread e₀ (ev00 :: evs0)) σ₀ ≠ .killed r) ∧
    (driveU M aids n (M.thread e₀ (ev00 :: evs0)) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveU M aids n (M.thread e₀ (ev00 :: evs0)) σ₀ = .done v σ' →
      ψ v σ') := by
  have hadeq := fun (t2 : List CoreRt) (σ2 : Mem)
      (h : ([(⟨e₀, ev00 :: evs0, M⟩ : CoreRt)], σ₀) -·->ₜₚ* (t2, σ2)) =>
    spike_step_adequacy ⟨e₀, ev00 :: evs0, M⟩ σ₀ m₀ hcoh
      (fun w σ' => ψ w.val σ') hwp h
  have hNS : ∀ (r : CoreRt) (σ : Mem),
      Reach ((⟨e₀, ev00 :: evs0, M⟩ : CoreRt), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRVal) (r, σ) := by
    intro r σ hr
    exact (hadeq [r] σ (Reach.toPool hr)).1 r (by simp)
  have hRES : ∀ (w : CoreRVal) (σ : Mem),
      Reach ((⟨e₀, ev00 :: evs0, M⟩ : CoreRt), σ₀) (ofValRt w, σ) →
      ψ w.val σ := by
    intro w σ hr
    exact (hadeq [ofValRt w] σ (Reach.toPool hr)).2 w [] rfl
  have hok : DriveOk (fun w σ' => ψ w.val σ')
      (driveU M aids n (M.thread e₀ (ev00 :: evs0)) σ₀) :=
    drive_classifyU hwf hQf n hQsz e₀ (ev00 :: evs0) σ₀ _ hNS hRES
      n (Nat.le_refl n) aids e₀ ev00 evs0 σ₀ .refl hfrag hfuel
  refine ⟨fun r hdr => ?_, fun hds => ?_, fun v σ' hdv => ?_⟩
  · rw [hdr] at hok; exact hok
  · rw [hds] at hok; exact hok
  · rw [hdv] at hok
    obtain ⟨w, hwv, hφ⟩ := hok
    rw [← hwv]
    exact hφ

/-- The spike context has no registered labels (its run state's
    `labeled` is empty), so the label-cone hypotheses are vacuous. -/
theorem spikeCtx_labels_none (l : sym)
    {pc : List (sym × core_base_type) × CoreExpr}
    (h : lookupLabel spikeCtx.labels l = some pc) : False := by
  rw [spikeCtx_labels, lookupLabel_empty] at h
  cases h

/-! ## THE ADEQUACY STATEMENT (engine-only conclusion) -/

/-- ADEQUACY: a proved WP triple over the fragment (hypotheses may —
    must — speak Iris/Step; they are the derived layer) plus a
    seeded initial MemState whose live cells carry the precondition
    footprint (Coh + the cell big-sep) implies, about THE ENGINE and
    nothing else: driving `step_ctx` with the sequential driver's
    discharge from the seeded state
    - never enters the killed channel (no UB, no error-kill — recon
      §2.6's full vocabulary),
    - never derails (no ILLTYPED refusal, no off-protocol step), and
    - if it delivers a value, that value and the final memory state
      satisfy the postcondition readout ψ.
    Quantifiers in the conclusion range over engine objects only:
    the program term, MemStates, fuel, the action-id supply, and the
    drive's outcome. Termination is not claimed (`.more` is
    unconstrained); the fuel bound keeps get_ctx's opaque
    fuel-exhaustion leaf out of range (Soundness.lean, FUEL
    HONESTY). -/
theorem spike_engine_adequacy {GF : BundledGFunctors} [SpikeGpreS GF]
    (e₀ : CoreExpr) (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hcoh : Coh σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, pointsTo i (.own 1) c)) ⊢
        WP (⟨e₀, spikeEnv, spikeCtx⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, iprop(∀ (σ' : Mem) (ns : Nat)
          (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝) }})
    (n : Nat) (aids : Nat → Nat)
    (hfuel : esize e₀ + n ≤ lemDefaultFuel) :
    (∀ r, drive aids n (spikeThread e₀) σ₀ ≠ .killed r) ∧
    (drive aids n (spikeThread e₀) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      drive aids n (spikeThread e₀) σ₀ = .done v σ' → ψ v σ') :=
  engine_adequacyU (GF := GF) (M := spikeCtx) spikeCtx_wf
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
    e₀ fmapEmpty [] σ₀ m₀ hfrag hcoh ψ hwp n aids hfuel
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)

/-! ## THE EXPORTED FACE: semantic triples over engine configurations
([USER 2026-08-30], the final-form instruction)

"For a small subset of core expressions; for any cerberus
configuration that satisfies the pre-state; we step to a cerberus
configuration that satisfies the post-state; and pre/post states
obey the frame rule."

Vocabulary: footprints are allocation-rooted cell maps; ∗ is
disjoint map union; a configuration SATISFIES a footprint via `Sat`
(= Coh: each cell live, writable, in-bounds, exactly those bytes;
cells pairwise range-disjoint) — everything OUTSIDE the footprint is
arbitrary, and the triple's rest-quantifier `R` returns it VERBATIM
(the semantic frame). The Iris WP/GenHeap machinery is interior: it
appears only inside `ProvenTriple` (the judgment that the derived
logic proved the triple), never in `SemTriple`. -/

/-- Footprints: allocation-rooted cell maps. -/
abbrev CellMap := SpikeHeapF SpikeCell

/-- Satisfaction of a footprint by an engine memory configuration
    (Coh, Heap.lean): constrains exactly the footprint's cells —
    liveness, writability, bounds, exact bytes, pairwise
    range-disjointness, per-cell side-table inertness; the rest of
    the configuration (other allocations/bytes, the union-member and
    function-pointer tables) is arbitrary. -/
abbrev Sat (σ : Mem) (m : CellMap) : Prop := Coh σ m

/-- Satisfaction is closed under shrinking the footprint (substitute
    into larger/more constraining contexts, satisfaction side). -/
theorem Sat.mono {σ : Mem} {m m' : CellMap} (h : Sat σ m) (hsub : m' ⊆ m) :
    Sat σ m' :=
  ⟨fun i c hg => h.cells i c (hsub i c hg),
   fun i j c1 c2 hne h1 h2 => h.disj i j c1 c2 hne (hsub _ _ h1) (hsub _ _ h2)⟩

/-- THE SEMANTIC TRIPLE ⦃P⦄ e ⦃post⦄, engine vocabulary only: for
    every configuration that splits as P ⊎ R — footprint P satisfied,
    rest R ARBITRARY — the engine's drive never kills or derails,
    and any delivered value v comes with a post-footprint Q with
    `post v Q`, THE SAME R returned verbatim (Sat σ' (Iris.Std.PartialMap.union Q R)).
    Partial correctness: fuel exhaustion (.more) is unconstrained;
    the fuel bound is the engine's own get_ctx budget (Soundness.lean,
    FUEL HONESTY). -/
def SemTriple (e : CoreExpr) (P : CellMap)
    (post : value → CellMap → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat σ (Iris.Std.PartialMap.union P R) →
  ∀ (n : Nat) (aids : Nat → Nat), esize e + n ≤ lemDefaultFuel →
    (∀ r, drive aids n (spikeThread e) σ ≠ .killed r) ∧
    (drive aids n (spikeThread e) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), drive aids n (spikeThread e) σ = .done v σ' →
      ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧ Sat σ' (Iris.Std.PartialMap.union Q R))

/-- INTERIOR: the derived logic (the slice-A separation logic — Iris
    WP over Step) proves the footprint triple. This definition is
    the only place the WP appears in the exported layer. -/
abbrev ProvenTriple (GF : BundledGFunctors) [SpikeGpreS GF] (e : CoreExpr)
    (P : CellMap) (post : value → CellMap → Prop) : Prop :=
  ∀ [SpikeGS .hasLC GF],
    iprop(([∗map] i ↦ c ∈ P, pointsTo i (.own 1) c)) ⊢
      WP (⟨e, spikeEnv, spikeCtx⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w,
        iprop(∃ Q : CellMap, ⌜post (CoreRVal.val w) Q⌝ ∗
          ([∗map] i ↦ c ∈ Q, pointsTo i (.own 1) c)) }}

/-! interior extraction lemmas -/

/-- genHeap_valid, big-footprint form (mirrors gen_heap's
    ghost_map_lookup_big). -/
theorem genHeap_valid_big {GF : BundledGFunctors}
    {H : Type _ → Type _} {L V : Type _} [Std.LawfulFiniteMap H L]
    [G : genHeapGS L V GF H] {σ m0 : H V} {dq : DFrac} :
    iprop(genHeapInterp σ ∗ ([∗map] l ↦ v ∈ m0, pointsTo l dq v)) ⊢
      (⌜m0 ⊆ σ⌝ : IProp GF) := by
  unfold genHeapInterp
  simp only [pointsTo]
  iintro ⟨⟨%m, -, Hσ, -⟩, Hm⟩
  iapply ghost_map_lookup_big m0 $$ Hσ [Hm]
  iexact Hm

/-- Full ownership of two footprints forces their key-disjointness
    (two full cells at one key are invalid). -/
theorem bigSepM_own_disjoint {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (Q R : CellMap) :
    iprop(([∗map] i ↦ c ∈ Q, pointsTo i (.own 1) c) ∗
          ([∗map] i ↦ c ∈ R, pointsTo i (.own 1) c)) ⊢
      (⌜Q ##ₘ R⌝ : IProp GF) := by
  by_cases hd : Q ##ₘ R
  · iintro -
    ipureintro
    exact hd
  · obtain ⟨k, hk⟩ : ∃ k, ¬(Iris.Std.PartialMap.get? Q k = none ∨
        Iris.Std.PartialMap.get? R k = none) :=
      Classical.not_forall.mp
        (fun hall => hd ((Iris.Std.PartialMap.disjoint_iff Q R).mpr hall))
    obtain ⟨cq, hcq⟩ : ∃ c, Iris.Std.PartialMap.get? Q k = some c := by
      cases h : Iris.Std.PartialMap.get? Q k with
      | none => exact absurd (.inl h) hk
      | some c => exact ⟨c, rfl⟩
    obtain ⟨cr, hcr⟩ : ∃ c, Iris.Std.PartialMap.get? R k = some c := by
      cases h : Iris.Std.PartialMap.get? R k with
      | none => exact absurd (.inr h) hk
      | some c => exact ⟨c, rfl⟩
    iintro ⟨HQ, HR⟩
    ihave HkQ := BigSepM.bigSepM_lookup hcq $$ HQ
    ihave HkR := BigSepM.bigSepM_lookup hcr $$ HR
    ihave %hne := pointsTo_ne $$ HkQ [HkR]
    · iexact HkR
    exact absurd rfl hne

/-- The cell-footprint readout: post-cells + frame-cells consume the
    final state interpretation into the pure semantic-triple
    conclusion. -/
theorem cells_readout {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (post : value → CellMap → Prop) (R : CellMap) (vv : value) :
    iprop((∃ Q : CellMap, ⌜post vv Q⌝ ∗
        ([∗map] i ↦ c ∈ Q, pointsTo i (.own 1) c)) ∗
        ([∗map] i ↦ c ∈ R, pointsTo i (.own 1) c)) ⊢
      iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
        stateInterp σ' ns κs nt ={⊤, ∅}=∗
          ⌜∃ Q : CellMap, post vv Q ∧ Q ##ₘ R ∧ Coh σ' (Iris.Std.PartialMap.union Q R)⌝) := by
  iintro ⟨⟨%Q, %hpost, HQ⟩, HR⟩ %σ' %ns %κs %nt Hsi
  icases (stateInterp_iff σ' ns κs nt).mp $$ Hsi with ⟨%m, %Hcoh, Hh⟩
  ihave %hd : ⌜Q ##ₘ R⌝ $$ [HQ HR]
  · iapply bigSepM_own_disjoint Q R $$ [$HQ $HR]
  ihave HQR : iprop([∗map] i ↦ c ∈ (Iris.Std.PartialMap.union Q R), pointsTo i (.own 1) c)
      $$ [HQ HR]
  · iapply (BigSepM.bigSepM_union hd).2 $$ [$HQ $HR]
  ihave %hsub : ⌜(Iris.Std.PartialMap.union Q R) ⊆ m⌝ $$ [Hh HQR]
  · iapply genHeap_valid_big $$ [$Hh $HQR]
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact ⟨Q, hpost, hd, Sat.mono Hcoh hsub⟩

/-- THE HEADLINE: soundness of the derived logic's triples at the
    semantic level — a proved footprint triple holds of the ENGINE
    over every splitting configuration. -/
theorem semantic_triple_sound {GF : BundledGFunctors} [SpikeGpreS GF]
    {e : CoreExpr} (hfrag : Frag e) {P : CellMap}
    {post : value → CellMap → Prop}
    (hwp : ProvenTriple GF e P post) :
    SemTriple e P post := by
  intro R hdisj σ hsat n aids hfuel
  refine spike_engine_adequacy (GF := GF) e σ (Iris.Std.PartialMap.union P R) hfrag hsat
    (fun v σ' => ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧ Coh σ' (Iris.Std.PartialMap.union Q R)) ?_ n aids hfuel
  intro instGS
  refine .trans (BigSepM.bigSepM_union hdisj).1 ?_
  iintro ⟨HP, HR⟩
  ihave HW := hwp $$ HP
  iapply spike_wp_wand $$ HW
  iintro %w Hpost
  iapply cells_readout post R (CoreRVal.val w)
  isplitl [Hpost]
  · iexact Hpost
  · iexact HR

/-- THE FRAME RULE at the semantic level: a proved footprint triple
    substitutes into any larger context — ⦃P ∗ F⦄ e ⦃post ∗ F⦄, the
    frame F verbatim. (The rest-quantifier already makes each
    SemTriple frame-closed over the UNNAMED rest; this theorem
    additionally moves a NAMED frame F across the triple.) -/
theorem semantic_frame {GF : BundledGFunctors} [SpikeGpreS GF]
    {e : CoreExpr} (hfrag : Frag e) {P : CellMap} (F : CellMap)
    {post : value → CellMap → Prop} (hPF : P ##ₘ F)
    (hwp : ProvenTriple GF e P post) :
    SemTriple e (Iris.Std.PartialMap.union P F)
      (fun v Q => ∃ Q₀ : CellMap, post v Q₀ ∧ Q₀ ##ₘ F ∧ Q = Iris.Std.PartialMap.union Q₀ F) := by
  refine semantic_triple_sound (GF := GF) hfrag ?_
  intro instGS
  refine .trans (BigSepM.bigSepM_union hPF).1 ?_
  iintro ⟨HP, HF⟩
  ihave HW := hwp $$ HP
  iapply spike_wp_wand $$ HW
  iintro %w HQex
  icases HQex with ⟨%Q₀, %hp, HQ⟩
  ihave %hd : ⌜Q₀ ##ₘ F⌝ $$ [HQ HF]
  · iapply bigSepM_own_disjoint Q₀ F $$ [$HQ $HF]
  iexists (Iris.Std.PartialMap.union Q₀ F)
  isplit
  · ipureintro
    exact ⟨Q₀, hp, hd, rfl⟩
  · iapply (BigSepM.bigSepM_union hd).2
    isplitl [HQ]
    · iexact HQ
    · iexact HF

/-! ## THE JUMP-PROFILE DRIVE AND ADEQUACY (the loop exhibits' lane)

S1b: `driveJ` is the `rsCtx` INSTANCE of the one drive (the drive
loop itself reads no current-proc — only the discharge's run state
differs from the straight-line profile), definitionally the old
frozen-profile loop; the J-lane theorems are `procCtx` instances of
the unified classification/adequacy, with the old `LabeledAt` tie
hypothesis kept in the STATEMENTS as the honest link between the
quantified run state and the label map the label-cone hypotheses
speak about (interior theorems derive `(procCtx p rs).labels = Q`
from it — `procCtx_labels`). -/

/-- The engine's execution at the jump profile — the run-state
    instance of the one drive (definitionally the old body). -/
def driveJ (rs : core_run_state) (aids : Nat → Nat) :
    Nat → thread_state → Mem → DriveResult :=
  driveU (rsCtx rs) aids

theorem driveJ_scrutinee (p : sym) (rs : core_run_state) (aid : Nat)
    (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, procThread p e ρ)).map
        (dischargeStep aid rs σ) = engineOutcomesP p aid rs e ρ σ := rfl

/-- The succ-step equation at the run-state instance, old spelling
    (rfl). -/
theorem driveJ_succ_eq (rs : core_run_state) (aids : Nat → Nat) (n : Nat)
    (th : thread_state) (σ : Mem) :
    driveJ rs aids (n+1) th σ =
      (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
          (dischargeStep (aids 0) rs σ) with
        | [.next th' σ'] => driveJ rs (fun i => aids (i+1)) n th' σ'
        | [.done v] => DriveResult.done v σ
        | [.killed r] => DriveResult.killed r
        | _ => DriveResult.stuck) := rfl

/-- The one drive at the proc-carrying context IS the run-state
    instance (the drive loop reads no proc; pointwise the two
    contexts' read fields coincide definitionally). -/
theorem driveU_procCtx (p : sym) (rs : core_run_state) :
    ∀ (n : Nat) (aids : Nat → Nat) (th : thread_state) (σ : Mem),
      driveU (procCtx p rs) aids n th σ = driveJ rs aids n th σ
  | 0, aids, th, σ => rfl
  | n+1, aids, th, σ => by
    rw [driveU_succ]
    show (match stepOutcomes (rsCtx rs) (aids 0) th σ with
      | [.next th' σ'] => driveU (procCtx p rs) (fun i => aids (i+1)) n th' σ'
      | [.done v] => DriveResult.done v σ
      | [.killed r] => DriveResult.killed r
      | _ => DriveResult.stuck) = driveJ rs aids (n+1) th σ
    rw [show driveJ rs aids (n+1) th σ =
      (match stepOutcomes (rsCtx rs) (aids 0) th σ with
        | [.next th' σ'] => driveJ rs (fun i => aids (i+1)) n th' σ'
        | [.done v] => DriveResult.done v σ
        | [.killed r] => DriveResult.killed r
        | _ => DriveResult.stuck) from rfl]
    cases houts : stepOutcomes (rsCtx rs) (aids 0) th σ with
    | nil => rfl
    | cons o rest =>
      cases rest with
      | cons o2 rest2 => cases o <;> rfl
      | nil =>
        cases o with
        | next th' σ' => exact driveU_procCtx p rs n (fun i => aids (i+1)) th' σ'
        | done v => rfl
        | killed r => rfl
        | error s => rfl
        | offFragment => rfl

/-- Driving a bare value at the jump profile: PROGRAM-DONE. -/
theorem driveJ_value_pure (p : sym) (rs : core_run_state)
    (φp : CoreRVal → Mem → Prop) (aids : Nat → Nat)
    (v : value) (ρ : EnvStack) (σ : Mem)
    (h : ∃ w : CoreRVal, w.val = v ∧ φp w σ) :
    ∀ n, DriveOk φp (driveJ rs aids n (procThread p (ofVal (.pure v)) ρ) σ) :=
  fun n => driveU_procCtx p rs n aids _ σ ▸
    driveU_value_pure (M := procCtx p rs) (procCtx_wf p rs) φp aids v ρ σ h n

/-! ## The termination-accounting primitives at the driveJ lane
(one certified drive step per mirror step, and the value delivery;
the fib exhibit's UNCONDITIONAL total theorem chains them by
induction on the variant). S1b statement change (class (A)): the
mirror step's index is the `procCtx p rs` instance (the old
separate `Q` index is the context's DERIVED label map — interior
lookups rewrite by `procCtx_labels hQ`). -/

/-- ONE certified drive step: wherever the mirror steps at a cone
    configuration at the proc-carrying context (tie `hQ` links the
    quantified run state to the label map the caller reasons with),
    driveJ takes exactly that step. -/
theorem driveJ_step {Q : LabelMap} {p : sym} {rs : core_run_state}
    (hQ : LabeledAt rs p Q) (aids : Nat → Nat) (n : Nat)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step (procCtx p rs) (e, ev0 :: evs, σ) (e', ρ', σ')) :
    driveJ rs aids (n + 1) (procThread p e (ev0 :: evs)) σ =
      driveJ rs (fun i => aids (i + 1)) n (procThread p e' ρ') σ' := by
  rw [← driveU_procCtx p rs (n+1) aids _ σ, ← driveU_procCtx p rs n _ _ σ']
  rw [show (procThread p e (ev0 :: evs)) =
    (procCtx p rs).thread e (ev0 :: evs) from rfl,
    show (procThread p e' ρ') = (procCtx p rs).thread e' ρ' from rfl]
  rw [driveU_succ, stepOutcomes_thread,
    engine_step_matchU (aids 0) hf hsz hs]

/-- Value delivery: driveJ at a bare value is PROGRAM-DONE, state
    verbatim. -/
theorem driveJ_done (p : sym) (rs : core_run_state) (aids : Nat → Nat)
    (n : Nat) (v : value) (ρ : EnvStack) (σ : Mem) :
    driveJ rs aids (n + 1) (procThread p (ofVal (.pure v)) ρ) σ =
      .done v σ := by
  rw [← driveU_procCtx p rs (n+1) aids _ σ,
    show (procThread p (ofVal (.pure v)) ρ) =
      (procCtx p rs).thread (ofVal (.pure v)) ρ from rfl,
    driveU_succ, stepOutcomes_thread, outcomesU_done (procCtx_wf p rs)]

/-- ADEQUACY AT THE JUMP PROFILE (engine-only conclusion) — the
    `procCtx` instance of `engine_adequacyU`: a proved base-WP at
    the context-carrying tuple plus the seeded memory implies driveJ
    from the proc-carrying thread never kills, never derails, and
    any delivered value satisfies the postcondition readout. The run
    state is a parameter carrying the label tie; the label map's
    cone membership and static size bound are the honest R3-interim
    hypotheses. -/
theorem engine_adequacyJ {GF : BundledGFunctors} [SpikeGpreS GF]
    {Q : LabelMap} {p : sym} {rs : core_run_state}
    (hQ : LabeledAt rs p Q)
    (hQf : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      Frag cont)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hcoh : Coh σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, pointsTo i (.own 1) c)) ⊢
        WP (⟨e₀, ev00 :: evs0, procCtx p rs⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, iprop(∀ (σ' : Mem) (ns : Nat)
          (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝) }})
    (n : Nat) (aids : Nat → Nat)
    (hfuel : esize e₀ + n ≤ lemDefaultFuel)
    (hQsz : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      esize cont + n ≤ lemDefaultFuel) :
    (∀ r, driveJ rs aids n (procThread p e₀ (ev00 :: evs0)) σ₀ ≠ .killed r) ∧
    (driveJ rs aids n (procThread p e₀ (ev00 :: evs0)) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids n (procThread p e₀ (ev00 :: evs0)) σ₀ = .done v σ' →
      ψ v σ') := by
  have hlbl : (procCtx p rs).labels = Q := procCtx_labels hQ
  have h := engine_adequacyU (GF := GF) (M := procCtx p rs)
    (procCtx_wf p rs)
    (fun l params cont hl => hQf l params cont (by rwa [hlbl] at hl))
    e₀ ev00 evs0 σ₀ m₀ hfrag hcoh ψ hwp n aids hfuel
    (fun l params cont hl => hQsz l params cont (by rwa [hlbl] at hl))
  rw [show (procCtx p rs).thread e₀ (ev00 :: evs0) =
    procThread p e₀ (ev00 :: evs0) from rfl,
    driveU_procCtx p rs n aids _ σ₀] at h
  exact h

end
end CerberusHeapLang
