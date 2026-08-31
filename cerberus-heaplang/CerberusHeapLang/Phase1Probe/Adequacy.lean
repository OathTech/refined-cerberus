/-
CerberusHeapLang.Phase1Probe.Adequacy — PHASE-1 PROBE MODULE (S1a):
the adequacy chain over the unified relation, the frozen-corpus
oracle re-proof, and the Ecase engine-facing regression.

CONTENTS:
- `spike_step_adequacyU`: iris adequacy at the unified language
  (SpikeGS constructed inside, as before — the ghost/state layer is
  shared with the old language, only the Language bundle is new).
- `drive_classifyU` / `engine_adequacyU`: the drive classification
  and the engine-only adequacy at ANY machine context (SeqWF + the
  registered extern probe restriction). Note what is gone relative
  to `engine_adequacyJ`: the `LabeledAt` tie hypothesis (derived
  from the context) and the frozen thread profiles.
- THE ORACLE RE-PROOF: `exhibitB_semantic_unified` re-proves the
  exported `exhibitB_semantic` STATEMENT VERBATIM (the old
  `SemTriple`, over the old `drive`) through the unified route:
  wp_storeU → spike_step_adequacyU → drive_classifyU →
  engine_adequacyU at `spikeCtx` → `driveU_spike`. Zero statement
  change — the K1 kill criterion's test, passed.
- THE ECASE REGRESSION (audit F-01 acceptance shape at probe
  scale): `case_regression_drive` is an engine-facing theorem whose
  program EXECUTES the value-scrutinee Ecase rule, stated over the
  canonical unified drive (and, at the spike instance, over the old
  `drive` verbatim). The WP-consumer rule (wps_case over the
  unified language) is S1b work — registered in the design record.
-/
import CerberusHeapLang.Phase1Probe.Lang
import CerberusHeapLang.Exhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib
open Iris.Std.PartialMap in
section

/-! ## Reachability and the iris thread pool (unified tuples) -/

/-- Reachability along the unified relation (context-preserving, as
    the engine is on the sequential path). -/
def ReachU : CoreRtU × Mem → CoreRtU × Mem → Prop :=
  Relation.ReflTransGen (fun a b =>
    StepU a.1.M (a.1.e, a.1.ρ, a.2) (b.1.e, b.1.ρ, b.2) ∧ b.1.M = a.1.M)

theorem ReachU.toPool {c c' : CoreRtU × Mem} (h : ReachU c c') :
    ([c.1], c.2) -·->ₜₚ* ([c'.1], c'.2) := by
  induction h with
  | refl => exact .refl
  | @tail b b' hr hstep ih =>
    exact ih.tail ⟨([] : List Empty),
      Language.Step.of_primStep (⟨hstep.1, hstep.2, rfl⟩ :
        PrimStep.primStep (b.1, b.2) ([] : List Empty)
          (b'.1, b'.2, ([] : List CoreRtU)))
        (t₁ := []) (t₂ := [])⟩

/-! ## Step-level adequacy at the unified language -/

/-- Iris adequacy over StepU with final-state readout (the
    `spike_step_adequacy` proof at the unified tuples; SpikeGS is
    constructed here, nothing pre-allocated). -/
theorem spike_step_adequacyU {GF : BundledGFunctors} [SpikeGpreS GF]
    (e : CoreRtU) (σ : Mem) (m₀ : SpikeHeapF SpikeCell) (hcoh : Coh σ m₀)
    (φp : CoreRValU → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, pointsTo i (.own 1) c)) ⊢
        WP e @ Stuckness.NotStuck; ⊤ {{ v, iprop(∀ (σ' : Mem) (ns : Nat)
          (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜φp v σ'⌝) }})
    {t2 : List CoreRtU} {σ2 : Mem}
    (hreach : ([e], σ) -·->ₜₚ* (t2, σ2)) :
    (∀ e2 ∈ t2, PrimStep.NotStuck (Val := CoreRValU) (e2, σ2)) ∧
    (∀ (w : CoreRValU) (t2' : List CoreRtU), t2 = ofValRtU w :: t2' → φp w σ2) := by
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF) (hlc := .hasLC) Stuckness.NotStuck [e] σ n κs t2 σ2 _
    (fun _ => 0) ?_ hsteps
  intro instInv
  imod (genHeap_init (H := SpikeHeapF) m₀) with ⟨%G, Hint, Hpts, Htok⟩
  letI instGS : SpikeGS .hasLC GF := { heap := G }
  imodintro
  iexists fun (σ' : Mem) (_ : Nat) (_ : List Empty) (_ : Nat) =>
    iprop(∃ m, ⌜Coh σ' m⌝ ∗ genHeapInterp m)
  iexists [fun (v : CoreRValU) => iprop(∀ (σ' : Mem) (ns : Nat)
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
  have hns : ∀ e2 ∈ t2, PrimStep.NotStuck (Val := CoreRValU) (e2, σ2) :=
    fun e2 he2 => hnsp e2 rfl he2
  obtain ⟨e1', rfl⟩ : ∃ x, es' = [x] := by
    cases es' with
    | nil => simp at hlen
    | cons a l =>
      cases l with
      | nil => exact ⟨a, rfl⟩
      | cons b l' => simp at hlen
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hposts with ⟨%eh, %Φt, %HeqΦ, Hpost, Hrest⟩
  cases hv : ToVal.toVal (Val := CoreRValU) eh with
  | none =>
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    refine ⟨hns, fun w t2'' heq2 => ?_⟩
    rw [heqt] at heq2
    injection HeqΦ with h1 h2
    subst h1
    injection heq2 with h3 h4
    rw [h3, language_toVal_eqU, toValRtU_ofValRtU] at hv
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
    rw [h3, language_toVal_eqU, toValRtU_ofValRtU] at hv
    injection hv with h5
    subst h5
    exact hφw

/-! ## The drive classification at a machine context -/

/-- DriveOk at the unified values. -/
def DriveOkU (φp : CoreRValU → Mem → Prop) : DriveResult → Prop
  | .more _ _ => True
  | .done v σ' => ∃ w : CoreRValU, w.val = v ∧ φp w σ'
  | .killed _ => False
  | .stuck => False

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

/-- Driving a bare value: PROGRAM-DONE (under SeqWF). -/
theorem driveU_value_pure {M : MachineCtx} (hwf : M.SeqWF)
    (φp : CoreRValU → Mem → Prop) (aids : Nat → Nat)
    (v : value) (ρ : EnvStack) (σ : Mem)
    (h : ∃ w : CoreRValU, w.val = v ∧ φp w σ) :
    ∀ n, DriveOkU φp (driveU M aids n (M.thread (ofVal (.pure v)) ρ) σ)
  | 0 => trivial
  | n+1 => by
    rw [driveU_succ, stepOutcomes_thread, outcomesU_done hwf]
    exact h

/-- The classification: from StepU-level NotStuck + value readout
    over ReachU, every driveU outcome is DriveOkU — via
    `engine_step_matchU`, one certification case per step. The old
    theorem's `LabeledAt` tie is GONE (context-derived); the label
    cone/budget hypotheses remain (registered continuations are the
    jump targets). -/
theorem drive_classifyU {M : MachineCtx} (hwf : M.SeqWF)
    (hext : M.extern = fmapEmpty)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      FragU cont)
    (n₀ : Nat)
    (hQsz : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      esize cont + n₀ ≤ lemDefaultFuel)
    (e₀ : CoreExpr) (ρ₀ : EnvStack) (σ₀ : Mem)
    (φp : CoreRValU → Mem → Prop)
    (hNS : ∀ (r : CoreRtU) (σ : Mem),
      ReachU ((⟨e₀, ρ₀, M⟩ : CoreRtU), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRValU) (r, σ))
    (hRES : ∀ (w : CoreRValU) (σ : Mem),
      ReachU ((⟨e₀, ρ₀, M⟩ : CoreRtU), σ₀) (ofValRtU w, σ) → φp w σ) :
    ∀ (n : Nat), n ≤ n₀ →
    ∀ (aids : Nat → Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem),
      ReachU ((⟨e₀, ρ₀, M⟩ : CoreRtU), σ₀) ((⟨e, ev0 :: evs, M⟩ : CoreRtU), σ) →
      FragU e → esize e + n ≤ lemDefaultFuel →
      DriveOkU φp (driveU M aids n (M.thread e (ev0 :: evs)) σ) := by
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
      · rw [language_toVal_eqU, toValRtU_mk, hv] at hval
        cases hval
      · obtain ⟨hs, hM, -⟩ := hprim
        obtain ⟨re', rρ', rM'⟩ := r'
        simp only at hs hM
        obtain rfl : M = rM' := hM.symm
        obtain ⟨ev0', rfl⟩ := StepU.env_cons hs
        rw [driveU_succ, stepOutcomes_thread,
          engine_step_matchU hext (aids 0) hf (by omega) hs]
        refine ih (by omega) _ re' ev0' evs σ'
          (hreach.tail ⟨hs, rfl⟩) (hf.step hQf hs) ?_
        rcases hf.esize_step hs with hle | ⟨l, params, cont, hl, hec⟩
        · omega
        · rw [hec]
          have := hQsz l params cont hl
          omega

/-! ## Engine-only adequacy at a machine context -/

/-- ADEQUACY AT A MACHINE CONTEXT (engine-only conclusion): a proved
    WP at the unified tuple plus the seeded memory implies driveU
    from the context's thread never kills, never derails, and any
    delivered value satisfies the readout. Hypotheses beyond the old
    `engine_adequacyJ`: SeqWF (explicit, was baked into the frozen
    profiles) and the registered extern probe restriction; GONE: the
    LabeledAt tie. -/
theorem engine_adequacyU {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF) (hext : M.extern = fmapEmpty)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      FragU cont)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : FragU e₀) (hcoh : Coh σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, pointsTo i (.own 1) c)) ⊢
        WP (⟨e₀, ev00 :: evs0, M⟩ : CoreRtU) @ Stuckness.NotStuck; ⊤
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
  have hadeq := fun (t2 : List CoreRtU) (σ2 : Mem)
      (h : ([(⟨e₀, ev00 :: evs0, M⟩ : CoreRtU)], σ₀) -·->ₜₚ* (t2, σ2)) =>
    spike_step_adequacyU ⟨e₀, ev00 :: evs0, M⟩ σ₀ m₀ hcoh
      (fun w σ' => ψ w.val σ') hwp h
  have hNS : ∀ (r : CoreRtU) (σ : Mem),
      ReachU ((⟨e₀, ev00 :: evs0, M⟩ : CoreRtU), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRValU) (r, σ) := by
    intro r σ hr
    exact (hadeq [r] σ (ReachU.toPool hr)).1 r (by simp)
  have hRES : ∀ (w : CoreRValU) (σ : Mem),
      ReachU ((⟨e₀, ev00 :: evs0, M⟩ : CoreRtU), σ₀) (ofValRtU w, σ) →
      ψ w.val σ := by
    intro w σ hr
    exact (hadeq [ofValRtU w] σ (ReachU.toPool hr)).2 w [] rfl
  have hok : DriveOkU (fun w σ' => ψ w.val σ')
      (driveU M aids n (M.thread e₀ (ev00 :: evs0)) σ₀) :=
    drive_classifyU hwf hext hQf n hQsz e₀ (ev00 :: evs0) σ₀ _ hNS hRES
      n (Nat.le_refl n) aids e₀ ev00 evs0 σ₀ .refl hfrag hfuel
  refine ⟨fun r hdr => ?_, fun hds => ?_, fun v σ' hdv => ?_⟩
  · rw [hdr] at hok; exact hok
  · rw [hds] at hok; exact hok
  · rw [hdv] at hok
    obtain ⟨w, hwv, hφ⟩ := hok
    rw [← hwv]
    exact hφ

/-! ## THE FROZEN-CORPUS ORACLE: the exported statements, re-proved
through the unified route.

`ProvenTripleU` is the interior judgment at the unified language
pinned to the spike instance (the exported statements' launch
profile). `semantic_triple_soundU`/`semantic_frameU` conclude the
OLD `SemTriple` — the exported statement shape, VERBATIM, over the
old `drive` — via `driveU_spike`. -/

/-- The spike context has no registered labels (its run state's
    `labeled` is empty), so the label-cone hypotheses are vacuous. -/
theorem spikeCtx_labels_none (l : sym)
    {pc : List (sym × core_base_type) × CoreExpr}
    (h : lookupLabel spikeCtx.labels l = some pc) : False := by
  rw [spikeCtx_labels, lookupLabel_empty] at h
  cases h

/-- The interior judgment: the derived logic (over the UNIFIED
    language) proves the footprint triple at the spike instance. -/
abbrev ProvenTripleU (GF : BundledGFunctors) [SpikeGpreS GF] (e : CoreExpr)
    (P : CellMap) (post : value → CellMap → Prop) : Prop :=
  ∀ [SpikeGS .hasLC GF],
    iprop(([∗map] i ↦ c ∈ P, pointsTo i (.own 1) c)) ⊢
      WP (⟨e, spikeEnv, spikeCtx⟩ : CoreRtU) @ Stuckness.NotStuck; ⊤ {{ w,
        iprop(∃ Q : CellMap, ⌜post (CoreRValU.val w) Q⌝ ∗
          ([∗map] i ↦ c ∈ Q, pointsTo i (.own 1) c)) }}

/-- Soundness of unified-route triples at the semantic level — THE
    OLD `SemTriple`, statement shape untouched. -/
theorem semantic_triple_soundU {GF : BundledGFunctors} [SpikeGpreS GF]
    {e : CoreExpr} (hfrag : FragU e) {P : CellMap}
    {post : value → CellMap → Prop}
    (hwp : ProvenTripleU GF e P post) :
    SemTriple e P post := by
  intro R hdisj σ hsat n aids hfuel
  have h := engine_adequacyU (GF := GF) (M := spikeCtx) spikeCtx_wf rfl
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
    e fmapEmpty [] σ (Iris.Std.PartialMap.union P R) hfrag hsat
    (fun v σ' => ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧
      Coh σ' (Iris.Std.PartialMap.union Q R)) ?_ n aids hfuel
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
  · have heq : driveU spikeCtx aids n (spikeCtx.thread e [fmapEmpty]) σ =
        drive aids n (spikeThread e) σ := driveU_spike n aids _ σ
    rw [heq] at h
    exact h
  · intro instGS
    refine .trans (BigSepM.bigSepM_union hdisj).1 ?_
    iintro ⟨HP, HR⟩
    ihave HW := hwp $$ HP
    iapply wp_wandU $$ HW
    iintro %w Hpost
    iapply cells_readout post R (CoreRValU.val w)
    isplitl [Hpost]
    · iexact Hpost
    · iexact HR

/-- THE FRAME RULE through the unified route (the old
    `semantic_frame`, statement shape untouched). -/
theorem semantic_frameU {GF : BundledGFunctors} [SpikeGpreS GF]
    {e : CoreExpr} (hfrag : FragU e) {P : CellMap} (F : CellMap)
    {post : value → CellMap → Prop} (hPF : P ##ₘ F)
    (hwp : ProvenTripleU GF e P post) :
    SemTriple e (Iris.Std.PartialMap.union P F)
      (fun v Q => ∃ Q₀ : CellMap, post v Q₀ ∧ Q₀ ##ₘ F ∧
        Q = Iris.Std.PartialMap.union Q₀ F) := by
  refine semantic_triple_soundU (GF := GF) hfrag ?_
  intro instGS
  refine .trans (BigSepM.bigSepM_union hPF).1 ?_
  iintro ⟨HP, HF⟩
  ihave HW := hwp $$ HP
  iapply wp_wandU $$ HW
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

/-! ## The oracle exhibit: exhibit (b), unified route -/

theorem fragB_U : FragU progB := FragU.store loc0_lib

/-- The store's footprint triple through the unified logic
    (provenB's proof with the unified small axiom). -/
theorem provenB_U {GF : BundledGFunctors} [SpikeGpreS GF] :
    ProvenTripleU GF progB mA (fun v Q => v = Vunit ∧ Q = mA7) := by
  intro instGS
  refine bigSepA_ptx.trans ?_
  iintro Hx
  ihave HW := wp_storeU (M := spikeCtx) (s := Stuckness.NotStuck) (E := ⊤)
    loc0 empty_annotation intTy xPtr sevenVal NA sevenMval bytesX spikeEnv
    seven_encodes seven_storable $$ Hx
  iapply wp_wandU $$ HW
  iintro %v ⟨%fp, %hv, Hx⟩
  iexists mA7
  isplit
  · ipureintro
    subst hv
    exact ⟨rfl, rfl⟩
  · ihave HC := ptx_to_cells $$ Hx
    iexact HC

/-- THE RE-PROVED EXPORT (frozen-corpus oracle, K1): the statement
    of `exhibitB_semantic` VERBATIM — old `SemTriple`, old `drive`,
    old footprints — proved through the unified relation end to end.
    Statement diff vs the frozen corpus: ZERO. -/
theorem exhibitB_semantic_unified {GF : BundledGFunctors} [SpikeGpreS GF] :
    SemTriple progB (Iris.Std.PartialMap.union mA mF)
      (fun v Q => ∃ Q₀, (v = Vunit ∧ Q₀ = mA7) ∧ Q₀ ##ₘ mF ∧
        Q = Iris.Std.PartialMap.union Q₀ mF) :=
  semantic_frameU (GF := GF) fragB_U mF mA_disj_mF provenB_U

/-! ## The Ecase engine-facing regression (F-01 at probe scale) -/

/-- The regression program: `case Vtrue of _ => unit end` — value
    scrutinee, wildcard branch (binder patterns are S1b: they need
    the substitution-closure lemmas — design record §5). -/
def progCase : CoreExpr :=
  caseRedex (Pexpr [] () (PEval Vtrue))
    [(Pattern [] (CaseBase (none, BTy_unit)), ofVal (.pure Vunit))]

/-- The selection computes (the wildcard matches anything, binds
    nothing — match_pattern's `CaseBase (none, _)` arm). -/
theorem progCase_select :
    select_case subst_sym_expr Vtrue
      [(Pattern [] (CaseBase (none, BTy_unit)), ofVal (.pure Vunit))] =
      some (ofVal (.pure Vunit)) := rfl

/-- progCase is in the unified cone — the RED row's cone membership,
    with branch closure discharged. -/
theorem fragU_progCase : FragU progCase := by
  refine FragU.case_value (fun e' hsel => ?_) (fun e' hsel => ?_)
  · rw [progCase_select] at hsel
    obtain rfl : ofVal (.pure Vunit) = e' := Option.some.inj hsel
    exact fragU_ofVal _
  · rw [progCase_select] at hsel
    obtain rfl : ofVal (.pure Vunit) = e' := Option.some.inj hsel
    exact Nat.le_refl _

/-- THE REGRESSION at the unified drive, any context (SeqWF + the
    extern probe restriction): the program executes the Ecase rule
    (step 1 is `StepU.case_value` — nothing else fires) and
    delivers unit. -/
theorem case_regression_engine {M : MachineCtx} (hwf : M.SeqWF)
    (hext : M.extern = fmapEmpty) (n : Nat) (aids : Nat → Nat)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (σ : Mem) :
    driveU M aids (n + 2) (M.thread progCase (ev0 :: evs)) σ =
      .done Vunit σ := by
  rw [driveU_step hext aids (n + 1) fragU_progCase
    (by rw [show esize progCase = 1 from rfl]; unfold lemDefaultFuel; omega)
    (StepU.case_value (valueFromPexpr_val _ _) progCase_select)]
  exact driveU_done hwf _ n Vunit (ev0 :: evs) σ

/-- ... and at the OLD `drive`, verbatim vocabulary (via the
    spike-instance equation): the F-01 acceptance shape — an Ecase
    program with a theorem over the canonical engine execution. -/
theorem case_regression_drive (n : Nat) (aids : Nat → Nat) (σ : Mem) :
    drive aids (n + 2) (spikeThread progCase) σ = .done Vunit σ := by
  rw [← driveU_spike]
  exact case_regression_engine spikeCtx_wf rfl n aids fmapEmpty [] σ

end
end CerberusHeapLang
