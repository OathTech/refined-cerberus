/-
CerberusHeapLang.Adequacy — spike artifact 4b: adequacy.

Three layers:
1. `drive` — the ENGINE'S EXECUTION at the frozen minimal context:
   the recon §3.3 discharge loop {step_ctx → Driver.lean:273
   discharge} as a definition over engine objects (thread_state,
   MemState, core_step2), with an explicit per-step action-id supply
   and explicit fuel. Engine vocabulary only.
2. `spike_step_adequacy` — the Iris adequacy instance: the bundled
   ghost state `SpikeGS` is CONSTRUCTED here (genHeap_init over the
   initial cell map — closing slice A's D11 honest gap), and iris-
   lean's `wp_strong_adequacy_gen` yields NotStuck + postcondition
   readout for every Step-reachable configuration. HeapLang's
   heap_adequacy (Iris/HeapLang/PrimitiveLaws.lean:131) is the
   template; the strong variant is needed because the fragment's
   postconditions read out the FINAL MEMORY STATE (through the state
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
D1 REMOVE-ANNOT tau with PROGRAM-DONE (annotations erased by
`SpikeVal.val` in the readout).

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
      (recon §2.6 — the full loadM/storeM failure vocabulary) -/
  | killed (r : kill_reason mem_error)
  /-- refusal (Step_error2 / ILLTYPED) or any off-protocol engine
      behavior -/
  | stuck

/-- THE ENGINE'S EXECUTION at the frozen context: iterate
    {`step_ctx` → `dischargeStep`} (the sequential driver's loop
    projected to (thread_state, MemState) — Soundness.lean header
    for the cited projections). `aids` supplies the driver's
    per-step action-id draws (Driver.lean:284); the fragment ignores
    them (D2), and the theorems hold for every supply. -/
def drive (aids : Nat → Nat) : Nat → thread_state → Mem → DriveResult
  | 0, th, σ => .more th σ
  | n+1, th, σ =>
    match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
        (dischargeStep (aids 0) spikeRunState σ) with
    | [.next th' σ'] => drive (fun i => aids (i+1)) n th' σ'
    | [.done v] => .done v σ
    | [.killed r] => .killed r
    | _ => .stuck

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
    Step a.1.lbl (a.1.e, a.1.ρ, a.2) (b.1.e, b.1.ρ, b.2) ∧ b.1.lbl = a.1.lbl)

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
    the bundled ghost state (SpikeGS — the slice-A D11 gap closes
    here) from the initial cell map and applies
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

/-- Driving a bare value: one PROGRAM-DONE step. -/
theorem drive_value_pure (φp : CoreRVal → Mem → Prop) (aids : Nat → Nat)
    (v : value) (ρ : EnvStack) (σ : Mem)
    (h : ∃ w : CoreRVal, w.val = v ∧ φp w σ) :
    ∀ n, DriveOk φp (drive aids n (envThread (ofVal (.pure v)) ρ) σ)
  | 0 => trivial
  | n+1 => by
    unfold drive
    rw [drive_scrutinee_env,
      show engineOutcomes (aids 0) (ofVal (.pure v)) ρ σ = [.done v] by
        unfold engineOutcomes; rw [engineSteps_done]; rfl]
    exact h

/-- The classification: from Step-level NotStuck + value readout
    (both over Reach), every drive outcome is DriveOk — via
    `engine_complete`, one certification case per step. -/
theorem drive_classify (e₀ : CoreExpr) (ρ₀ : EnvStack) (σ₀ : Mem)
    (φp : CoreRVal → Mem → Prop)
    (hNS : ∀ (r : CoreRt) (σ : Mem), Reach ((⟨e₀, ρ₀, spikeLbl⟩ : CoreRt), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRVal) (r, σ))
    (hRES : ∀ (w : CoreRVal) (σ : Mem),
      Reach ((⟨e₀, ρ₀, spikeLbl⟩ : CoreRt), σ₀) (ofValRt w, σ) → φp w σ)
    (n : Nat) :
    ∀ (aids : Nat → Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem),
      Reach ((⟨e₀, ρ₀, spikeLbl⟩ : CoreRt), σ₀) ((⟨e, ev0 :: evs, spikeLbl⟩ : CoreRt), σ) →
      FragP e → esize e + n ≤ lemDefaultFuel →
      DriveOk φp (drive aids n (envThread e (ev0 :: evs)) σ) := by
  induction n with
  | zero => intro aids e ev0 evs σ _ _ _; trivial
  | succ n ih =>
    intro aids e ev0 evs σ hreach hf hfuel
    obtain ⟨o, houts, hmatch⟩ :=
      engine_complete (aids 0) σ ev0 evs hf (by omega)
    unfold drive
    rw [drive_scrutinee_env, houts]
    cases hmatch with
    | @step e' ρ' σ' hs =>
      obtain rfl : ρ' = ev0 :: evs := Step.env_invariant_frag hf hs
      exact ih _ _ _ _ _ (hreach.tail ⟨hs, rfl⟩) (hf.step hs)
        (by have := Step.esize_succ hf hs; omega)
    | @removeAnnot ds v hann =>
      subst hann
      exact drive_value_pure φp _ v (ev0 :: evs) σ
        ⟨⟨.annot ds v, ev0 :: evs, spikeLbl⟩, rfl,
          hRES ⟨.annot ds v, ev0 :: evs, spikeLbl⟩ σ hreach⟩ n
    | @done v hpure =>
      subst hpure
      exact ⟨⟨.pure v, ev0 :: evs, spikeLbl⟩, rfl,
        hRES ⟨.pure v, ev0 :: evs, spikeLbl⟩ σ hreach⟩
    | refused href hnostep hnv =>
      rcases hNS ⟨e, ev0 :: evs, spikeLbl⟩ σ hreach with hval | ⟨obs, e', σ', efs, hprim⟩
      · rw [language_toVal_eq, toValRt_mk, hnv] at hval
        cases hval
      · exact absurd hprim.1 (hnostep _)

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
    (hfrag : FragP e₀) (hcoh : Coh σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, pointsTo i (.own 1) c)) ⊢
        WP (⟨e₀, spikeEnv, spikeLbl⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, iprop(∀ (σ' : Mem) (ns : Nat)
          (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝) }})
    (n : Nat) (aids : Nat → Nat)
    (hfuel : esize e₀ + n ≤ lemDefaultFuel) :
    (∀ r, drive aids n (spikeThread e₀) σ₀ ≠ .killed r) ∧
    (drive aids n (spikeThread e₀) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      drive aids n (spikeThread e₀) σ₀ = .done v σ' → ψ v σ') := by
  have hadeq := fun (t2 : List CoreRt) (σ2 : Mem)
      (h : ([(⟨e₀, spikeEnv, spikeLbl⟩ : CoreRt)], σ₀) -·->ₜₚ* (t2, σ2)) =>
    spike_step_adequacy ⟨e₀, spikeEnv, spikeLbl⟩ σ₀ m₀ hcoh (fun w σ' => ψ w.val σ') hwp h
  have hNS : ∀ (r : CoreRt) (σ : Mem),
      Reach ((⟨e₀, spikeEnv, spikeLbl⟩ : CoreRt), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRVal) (r, σ) := by
    intro r σ hr
    exact (hadeq [r] σ (Reach.toPool hr)).1 r (by simp)
  have hRES : ∀ (w : CoreRVal) (σ : Mem),
      Reach ((⟨e₀, spikeEnv, spikeLbl⟩ : CoreRt), σ₀) (ofValRt w, σ) →
      ψ w.val σ := by
    intro w σ hr
    exact (hadeq [ofValRt w] σ (Reach.toPool hr)).2 w [] rfl
  have hok0 := drive_classify e₀ spikeEnv σ₀ (fun w σ' => ψ w.val σ') hNS hRES
    n aids e₀ fmapEmpty [] σ₀ .refl hfrag hfuel
  have hok : DriveOk (fun w σ' => ψ w.val σ')
      (drive aids n (spikeThread e₀) σ₀) := hok0
  refine ⟨fun r hdr => ?_, fun hds => ?_, fun v σ' hdv => ?_⟩
  · rw [hdr] at hok; exact hok
  · rw [hds] at hok; exact hok
  · rw [hdv] at hok
    obtain ⟨w, hwv, hφ⟩ := hok
    rw [← hwv]
    exact hφ

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
      WP (⟨e, spikeEnv, spikeLbl⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w,
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
    {e : CoreExpr} (hfrag : FragP e) {P : CellMap}
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
    {e : CoreExpr} (hfrag : FragP e) {P : CellMap} (F : CellMap)
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

/-! ## S3 — THE JUMP-PROFILE DRIVE AND ADEQUACY

`driveJ` iterates the same {step_ctx → discharge} loop at a
PARAMETERIZED run state (Erun reads `labeled` through it; the
fragment's monads return it verbatim, so it stays constant across
the drive — mirroring that the real driver never writes `labeled`
on this path). Classification differs from the phase-1 lane in
shape (recorded finding): completeness is MATCH-GIVEN-STEP
(`engine_step_matchJ`) — the WP's NotStuck supplies the mirror step
at every reachable configuration, whose rule premises carry every
panic-exclusion fact; no refusal case ever arises. Fuel: the
in-budget hypotheses (additive on the current segment + the static
per-label bound for the R3 jump reset — the mission-sanctioned
interim until the termination-accounting slot). -/

/-- The engine's execution at the jump profile. -/
def driveJ (rs : core_run_state) (aids : Nat → Nat) :
    Nat → thread_state → Mem → DriveResult
  | 0, th, σ => .more th σ
  | n+1, th, σ =>
    match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
        (dischargeStep (aids 0) rs σ) with
    | [.next th' σ'] => driveJ rs (fun i => aids (i+1)) n th' σ'
    | [.done v] => .done v σ
    | [.killed r] => .killed r
    | _ => .stuck

theorem driveJ_scrutinee (p : sym) (rs : core_run_state) (aid : Nat)
    (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, procThread p e ρ)).map
        (dischargeStep aid rs σ) = engineOutcomesP p aid rs e ρ σ := rfl

/-- Driving a bare value at the jump profile: PROGRAM-DONE. -/
theorem driveJ_value_pure (p : sym) (rs : core_run_state)
    (φp : CoreRVal → Mem → Prop) (aids : Nat → Nat)
    (v : value) (ρ : EnvStack) (σ : Mem)
    (h : ∃ w : CoreRVal, w.val = v ∧ φp w σ) :
    ∀ n, DriveOk φp (driveJ rs aids n (procThread p (ofVal (.pure v)) ρ) σ)
  | 0 => trivial
  | n+1 => by
    unfold driveJ
    rw [driveJ_scrutinee, engineOutcomesP_done]
    exact h

/-- The J-lane drive classification: from Step-level NotStuck +
    value readout over `Reach` (at the label-carrying tuple), every
    driveJ outcome is DriveOk — via `engine_step_matchJ`, one
    certification case per step. Hypotheses: the Q↔labeled tie, the
    label map's cone membership + static size bound (the R3 reset
    budget), and the in-budget segment bound. -/
theorem drive_classifyJ {Q : LabelMap} {p : sym} {rs : core_run_state}
    (hQ : LabeledAt rs p Q)
    (hQf : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      FragJ cont)
    (n₀ : Nat)
    (hQsz : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      esize cont + n₀ ≤ lemDefaultFuel)
    (e₀ : CoreExpr) (ρ₀ : EnvStack) (σ₀ : Mem)
    (φp : CoreRVal → Mem → Prop)
    (hNS : ∀ (r : CoreRt) (σ : Mem),
      Reach ((⟨e₀, ρ₀, Q⟩ : CoreRt), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRVal) (r, σ))
    (hRES : ∀ (w : CoreRVal) (σ : Mem),
      Reach ((⟨e₀, ρ₀, Q⟩ : CoreRt), σ₀) (ofValRt w, σ) → φp w σ) :
    ∀ (n : Nat), n ≤ n₀ →
    ∀ (aids : Nat → Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem),
      Reach ((⟨e₀, ρ₀, Q⟩ : CoreRt), σ₀) ((⟨e, ev0 :: evs, Q⟩ : CoreRt), σ) →
      FragJ e → esize e + n ≤ lemDefaultFuel →
      DriveOk φp (driveJ rs aids n (procThread p e (ev0 :: evs)) σ) := by
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
        exact driveJ_value_pure p rs φp aids v (ev0 :: evs) σ
          ⟨⟨.pure v, ev0 :: evs, Q⟩, rfl,
            hRES ⟨.pure v, ev0 :: evs, Q⟩ σ hreach⟩ (n+1)
      | annot ds v =>
        unfold driveJ
        rw [driveJ_scrutinee, engineOutcomesP_remove_annot]
        exact driveJ_value_pure p rs φp _ v (ev0 :: evs) σ
          ⟨⟨.annot ds v, ev0 :: evs, Q⟩, rfl,
            hRES ⟨.annot ds v, ev0 :: evs, Q⟩ σ hreach⟩ n
    | none =>
      rcases hNS ⟨e, ev0 :: evs, Q⟩ σ hreach with hval | ⟨obs, r', σ', efs, hprim⟩
      · rw [language_toVal_eq, toValRt_mk, hv] at hval
        cases hval
      · obtain ⟨hs, hlbl, -⟩ := hprim
        obtain ⟨re', rρ', rQ'⟩ := r'
        simp only at hs hlbl
        obtain rfl : Q = rQ' := hlbl.symm
        obtain ⟨ev0', rfl⟩ := Step.env_cons hs
        unfold driveJ
        rw [driveJ_scrutinee,
          engine_step_matchJ (aids 0) hQ hf (by omega) hs]
        refine ih (by omega) _ re' ev0' evs σ'
          (hreach.tail ⟨hs, rfl⟩) (hf.step hQf hs) ?_
        rcases hf.esize_step_bound hs with hle |
            ⟨l, pes, params, cont, hj, hl, hec⟩
        · omega
        · rw [hec]
          have := hQsz l params cont hl
          omega

/-! ## S4 — the termination-accounting primitives at the driveJ
lane (the step-bound product's building blocks: one certified drive
step per mirror step, and the value delivery; the fib exhibit's
UNCONDITIONAL total theorem chains them by induction on the
variant). -/

/-- ONE certified drive step: wherever the mirror steps at a FragJ
    configuration (labels tied), driveJ takes exactly that step. -/
theorem driveJ_step {Q : LabelMap} {p : sym} {rs : core_run_state}
    (hQ : LabeledAt rs p Q) (aids : Nat → Nat) (n : Nat)
    {e e' : CoreExpr} {ev0 : Fmap sym value} {evs : List (Fmap sym value)}
    {ρ' : EnvStack} {σ σ' : Mem}
    (hf : FragJ e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step Q (e, ev0 :: evs, σ) (e', ρ', σ')) :
    driveJ rs aids (n + 1) (procThread p e (ev0 :: evs)) σ =
      driveJ rs (fun i => aids (i + 1)) n (procThread p e' ρ') σ' := by
  rw [show driveJ rs aids (n + 1) (procThread p e (ev0 :: evs)) σ =
    (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0
        (none, procThread p e (ev0 :: evs))).map
        (dischargeStep (aids 0) rs σ) with
      | [.next th' σ'] => driveJ rs (fun i => aids (i + 1)) n th' σ'
      | [.done v] => .done v σ
      | [.killed r] => .killed r
      | _ => .stuck) from rfl]
  rw [driveJ_scrutinee, engine_step_matchJ (aids 0) hQ hf hsz hs]

/-- Value delivery: driveJ at a bare value is PROGRAM-DONE, state
    verbatim. -/
theorem driveJ_done (p : sym) (rs : core_run_state) (aids : Nat → Nat)
    (n : Nat) (v : value) (ρ : EnvStack) (σ : Mem) :
    driveJ rs aids (n + 1) (procThread p (ofVal (.pure v)) ρ) σ =
      .done v σ := by
  rw [show driveJ rs aids (n + 1) (procThread p (ofVal (.pure v)) ρ) σ =
    (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0
        (none, procThread p (ofVal (.pure v)) ρ)).map
        (dischargeStep (aids 0) rs σ) with
      | [.next th' σ'] => driveJ rs (fun i => aids (i + 1)) n th' σ'
      | [.done v] => .done v σ
      | [.killed r] => .killed r
      | _ => .stuck) from rfl]
  rw [driveJ_scrutinee, engineOutcomesP_done]

/-- ADEQUACY AT THE JUMP PROFILE (engine-only conclusion): a proved
    base-WP at the label-carrying tuple plus the seeded memory
    implies driveJ from the proc-carrying thread never kills, never
    derails, and any delivered value satisfies the postcondition
    readout. The run state is a parameter carrying the label tie;
    the label map's cone membership and static size bound are the
    honest R3-interim hypotheses (arc plan: the in-budget form until
    the termination-accounting slot). -/
theorem engine_adequacyJ {GF : BundledGFunctors} [SpikeGpreS GF]
    {Q : LabelMap} {p : sym} {rs : core_run_state}
    (hQ : LabeledAt rs p Q)
    (hQf : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      FragJ cont)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : FragJ e₀) (hcoh : Coh σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, pointsTo i (.own 1) c)) ⊢
        WP (⟨e₀, ev00 :: evs0, Q⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
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
  have hadeq := fun (t2 : List CoreRt) (σ2 : Mem)
      (h : ([(⟨e₀, ev00 :: evs0, Q⟩ : CoreRt)], σ₀) -·->ₜₚ* (t2, σ2)) =>
    spike_step_adequacy ⟨e₀, ev00 :: evs0, Q⟩ σ₀ m₀ hcoh
      (fun w σ' => ψ w.val σ') hwp h
  have hNS : ∀ (r : CoreRt) (σ : Mem),
      Reach ((⟨e₀, ev00 :: evs0, Q⟩ : CoreRt), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRVal) (r, σ) := by
    intro r σ hr
    exact (hadeq [r] σ (Reach.toPool hr)).1 r (by simp)
  have hRES : ∀ (w : CoreRVal) (σ : Mem),
      Reach ((⟨e₀, ev00 :: evs0, Q⟩ : CoreRt), σ₀) (ofValRt w, σ) →
      ψ w.val σ := by
    intro w σ hr
    exact (hadeq [ofValRt w] σ (Reach.toPool hr)).2 w [] rfl
  have hok : DriveOk (fun w σ' => ψ w.val σ')
      (driveJ rs aids n (procThread p e₀ (ev00 :: evs0)) σ₀) :=
    drive_classifyJ hQ hQf n hQsz e₀ (ev00 :: evs0) σ₀ _ hNS hRES
      n (Nat.le_refl n) aids e₀ ev00 evs0 σ₀ .refl hfrag hfuel
  refine ⟨fun r hdr => ?_, fun hds => ?_, fun v σ' hdv => ?_⟩
  · rw [hdr] at hok; exact hok
  · rw [hds] at hok; exact hok
  · rw [hdv] at hok
    obtain ⟨w, hwv, hφ⟩ := hok
    rw [← hwv]
    exact hφ

end
end CerberusHeapLang
