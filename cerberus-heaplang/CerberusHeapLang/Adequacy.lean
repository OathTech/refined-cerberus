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
    (dischargeStep M.tagDefs aid M.runState σ)

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
          (dischargeStep spikeCtx.tagDefs (aids 0) spikeRunState σ) with
        | [.next th' σ'] => drive (fun i => aids (i+1)) n th' σ'
        | [.done v] => DriveResult.done v σ
        | [.killed r] => DriveResult.killed r
        | _ => DriveResult.stuck) := rfl

/-- The drive's one-step scrutinee at an envThread arena IS
    `engineOutcomes` (definitional). -/
theorem drive_scrutinee_env (aid : Nat) (e : CoreExpr) (ρ : EnvStack) (σ : Mem) :
    (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, envThread e ρ)).map
        (dischargeStep spikeCtx.tagDefs aid spikeRunState σ) = engineOutcomes aid e ρ σ := rfl

/-- ... at the exported entry env. -/
theorem drive_scrutinee (aid : Nat) (e : CoreExpr) (σ : Mem) :
    (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, spikeThread e)).map
        (dischargeStep spikeCtx.tagDefs aid spikeRunState σ) = engineOutcomes aid e spikeEnv σ := rfl

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

/-! ## The ghost launch (Phase 2 carrier): the three heaps from a
cell footprint. A footprint cell becomes one metadata entry plus its
byte range; the cursor heap starts EMPTY (existing launches owe no
allocator facts — the cursor-owning launch is a separate variant). -/

open Iris.Std.PartialMap in
/-- The meta/byte ghost images of a cell footprint (characterized —
    the launch builds them by allocation). -/
structure MetaByteOf (tds : CerbTags.TagDefsMap) (m : SpikeHeapF SpikeCell) (mm : SpikeHeapF MetaCell)
    (mb : SpikeHeapF CerbMem.AbsByte) : Prop where
  meta_sub : ∀ i mc, get? mm i = some mc →
    ∃ c, get? m i = some c ∧ mc = metaOf tds c
  meta_all : ∀ i c, get? m i = some c → get? mm i = some (metaOf tds c)
  byte_cov : ∀ k b, get? mb k = some b → ∃ i c, get? m i = some c ∧
    c.addr ≤ k ∧ k < c.addr + c.bytes.length ∧
    b = (c.bytes[(k - c.addr).toNat]?).getD undefByte
  byte_all : ∀ i c, get? m i = some c → ∀ (j : Nat), j < c.bytes.length →
    get? mb (c.addr + (j : Int)) = c.bytes[j]?

open Iris.Std.PartialMap in
/-- A footprint's ghost images couple to any state the footprint
    satisfies (cursor-free). -/
theorem MetaByteOf.cohG {tds : CerbTags.TagDefsMap} {σ : Mem} {m : SpikeHeapF SpikeCell}
    {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
    (hcoh : Coh tds σ m) (h : MetaByteOf tds m mm mb) :
    CohG σ mm mb (∅ : SpikeHeapF AllocCursor) := by
  have hnone : ∀ k : Int, get? (∅ : SpikeHeapF AllocCursor) k = none :=
    fun k => Iris.Std.LawfulPartialMap.get?_empty k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id mc hget
    obtain ⟨c, hc, rfl⟩ := h.meta_sub id mc hget
    exact (hcoh.cells id c hc).toMetaCoh
  · intro i j mci mcj hne hgi hgj
    obtain ⟨ci, hci, rfl⟩ := h.meta_sub i mci hgi
    obtain ⟨cj, hcj, rfl⟩ := h.meta_sub j mcj hgj
    exact (cellsDisjoint_iff_metaDisjoint tds ci cj).mp
      (hcoh.disj i j ci cj hne hci hcj)
  · intro k b hget
    obtain ⟨i, c, hc, hk1, hk2, rfl⟩ := h.byte_cov k b hget
    have hcc := hcoh.cells i c hc
    have hj : ((k - c.addr).toNat) < c.bytes.length := by omega
    have := byteAt_of_readBytesFrom σ c.addr (CerbMem.sizeofCtype tds c.ty)
      c.bytes hcc.bytes (k - c.addr).toNat (by rw [hcc.len] at hj; exact hj)
    rw [show c.addr + (((k - c.addr).toNat : Nat) : Int) = k by omega] at this
    exact this
  · intro k c hget
    rw [hnone k] at hget
    cases hget
  · intro c hget
    rw [hnone 0] at hget
    cases hget
  · intro hne
    exact absurd (hnone 0) hne
  · intro hne
    exact absurd (hnone 0) hne
  · intro hne
    exact absurd (hnone 0) hne
  · intro hne
    exact absurd (hnone 0) hne
  · intro hne
    exact absurd (hnone 0) hne

open Iris.Std.PartialMap in
/-- THE LAUNCH ALLOCATION: from empty meta/byte heaps, allocate every
    footprint cell (metadata entry + byte range), delivering the
    per-cell whole-allocation ownership. -/
theorem spikeCells_alloc (tds : CerbTags.TagDefsMap) {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (σ : Mem) (m : SpikeHeapF SpikeCell) (hcoh : Coh tds σ m) :
    iprop(metaInterp (GF := GF) (∅ : SpikeHeapF MetaCell) ∗
        byteInterp (∅ : SpikeHeapF CerbMem.AbsByte)) ⊢
      |==> iprop(∃ mm mb, ⌜MetaByteOf tds m mm mb⌝ ∗
        metaInterp mm ∗ byteInterp mb ∗
        ([∗map] i ↦ c ∈ m, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) := by
  induction m using Iris.Std.LawfulFiniteMap.induction_on with
  | hemp =>
    iintro ⟨Hmi, Hbi⟩
    imodintro
    iexists (∅ : SpikeHeapF MetaCell), (∅ : SpikeHeapF CerbMem.AbsByte)
    isplit
    · ipureintro
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i
      · intro mc h
        rw [Iris.Std.LawfulPartialMap.get?_empty] at h
        cases h
      · intro c h
        rw [Iris.Std.LawfulPartialMap.get?_empty] at h
        cases h
      · intro b h
        rw [Iris.Std.LawfulPartialMap.get?_empty] at h
        cases h
      · intro c h
        rw [Iris.Std.LawfulPartialMap.get?_empty] at h
        cases h
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iapply BigSepM.bigSepM_empty
      itrivial
  | hins i c m'' Hl IH =>
    have hsub : m'' ⊆ Iris.Std.PartialMap.insert m'' i c := by
      intro k v hk
      have hne : k ≠ i := fun h => by
        subst h
        rw [Hl] at hk
        cases hk
      rw [Iris.Std.get?_insert_ne (fun h => hne h.symm)]
      exact hk
    have hcoh'' : Coh tds σ m'' :=
      ⟨fun i c hg => hcoh.cells i c (hsub i c hg),
       fun i j c1 c2 hne h1 h2 =>
         hcoh.disj i j c1 c2 hne (hsub _ _ h1) (hsub _ _ h2)⟩
    have hci : get? (Iris.Std.PartialMap.insert m'' i c) i = some c :=
      Iris.Std.get?_insert_eq rfl
    have hcc := hcoh.cells i c hci
    iintro ⟨Hmi, Hbi⟩
    imod (IH hcoh'') $$ [$Hmi $Hbi] with ⟨%mm, %mb, %hmbo, Hmi, Hbi, Hcells⟩
    -- metadata freshness
    have hfreshm : get? mm i = none := by
      cases hg : get? mm i with
      | none => rfl
      | some mc =>
        obtain ⟨c', hc', -⟩ := hmbo.meta_sub i mc hg
        rw [Hl] at hc'
        cases hc'
    imod (metaHeap_alloc (metaOf tds c) hfreshm) $$ [$Hmi] with ⟨Hmi, Hmnew⟩
    -- byte-range freshness
    have hfreshb : (rangeMap c.addr c.bytes) ##ₘ mb := by
      rw [Iris.Std.PartialMap.disjoint_iff]
      intro k
      cases hg : get? mb k with
      | none => exact .inr rfl
      | some b =>
        left
        rw [rangeMap_get?]
        rw [if_neg ?_]
        obtain ⟨j, cj, hcj, hk1, hk2, -⟩ := hmbo.byte_cov k b hg
        have hne : i ≠ j := fun h => by
          subst h
          rw [Hl] at hcj
          cases hcj
        have hdisj := hcoh.disj i j c cj hne hci (hsub j cj hcj)
        have hlc := (hcoh.cells i c hci).len
        have hlcj := (hcoh''.cells j cj hcj).len
        simp only [cellsDisjoint] at hdisj
        intro hcon
        obtain ⟨h1, h2⟩ := hcon
        omega
    imod (byteHeap_alloc_big (rangeMap c.addr c.bytes) hfreshb)
      $$ [$Hbi] with ⟨Hbi, Hbnew⟩
    imodintro
    iexists (Iris.Std.PartialMap.insert mm i (metaOf tds c)),
      (Iris.Std.PartialMap.union (rangeMap c.addr c.bytes) mb)
    isplit
    · ipureintro
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j mc hg
        by_cases hj : j = i
        · subst hj
          rw [Iris.Std.get?_insert_eq rfl] at hg
          exact ⟨c, hci, (Option.some.inj hg).symm⟩
        · rw [Iris.Std.get?_insert_ne (fun h => hj h.symm)] at hg
          obtain ⟨c', hc', rfl⟩ := hmbo.meta_sub j mc hg
          exact ⟨c', hsub j c' hc', rfl⟩
      · intro j c' hg
        by_cases hj : j = i
        · subst hj
          rw [Iris.Std.get?_insert_eq rfl] at hg ⊢
          rw [(Option.some.inj hg)]
        · rw [Iris.Std.get?_insert_ne (fun h => hj h.symm)] at hg
          rw [Iris.Std.get?_insert_ne (fun h => hj h.symm)]
          exact hmbo.meta_all j c' hg
      · intro k b hg
        rw [PMunion_get?, rangeMap_get?] at hg
        by_cases hin : c.addr ≤ k ∧ k < c.addr + c.bytes.length
        · rw [if_pos hin] at hg
          simp only [Option.orElse] at hg
          refine ⟨i, c, hci, hin.1, hin.2, ?_⟩
          have hj : (k - c.addr).toNat < c.bytes.length := by omega
          rw [List.getElem?_eq_getElem hj] at hg ⊢
          simp only [Option.getD_some]
          exact (Option.some.inj hg).symm
        · rw [if_neg hin] at hg
          simp only [Option.orElse] at hg
          obtain ⟨j, cj, hcj, h1, h2, h3⟩ := hmbo.byte_cov k b hg
          exact ⟨j, cj, hsub j cj hcj, h1, h2, h3⟩
      · intro j c' hg jj hjj
        by_cases hj : j = i
        · subst hj
          rw [Iris.Std.get?_insert_eq rfl] at hg
          obtain rfl : c = c' := Option.some.inj hg
          rw [PMunion_get?, rangeMap_get?]
          rw [if_pos ⟨Int.le_add_of_nonneg_right (Int.natCast_nonneg _),
            Int.add_lt_add_left (by exact_mod_cast hjj) c.addr⟩]
          simp only [Option.orElse]
          rw [show (c.addr + (jj : Int) - c.addr).toNat = jj by omega,
            List.getElem?_eq_getElem hjj]
        · rw [Iris.Std.get?_insert_ne (fun h => hj h.symm)] at hg
          rw [PMunion_get?, rangeMap_get?]
          rw [if_neg ?_]
          · simp only [Option.orElse]
            exact hmbo.byte_all j c' hg jj hjj
          · have hne : i ≠ j := fun h => hj h.symm
            have hdisj := hcoh.disj i j c c' hne hci (hsub j c' hg)
            have hlc := (hcoh.cells i c hci).len
            have hlcj := (hcoh''.cells j c' hg).len
            simp only [cellsDisjoint] at hdisj
            intro hcon
            obtain ⟨h1, h2⟩ := hcon
            omega
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    ihave HBnew : bytesOwn c.addr (.own 1) c.bytes $$ [Hbnew]
    · iapply bigSepM_rangeMap $$ Hbnew
    iapply (BigSepM.bigSepM_insert (Φ := fun i c =>
      cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c) Hl).2
    isplitl [Hmnew HBnew]
    · iapply (cellOwn_iff tds i (.own 1) c).mpr
      isplitl [Hmnew]
      · iexact Hmnew
      isplitl [HBnew]
      · iexact HBnew
      · ipureintro
        exact ⟨hcc.len, hcc.dec_indep⟩
    · iexact Hcells

/-! ## Launch coherence and the allocation-aware launch (alloc arc
P1.2/P1.3)

`Coh` says the tracked cells exist and are disjoint. `LaunchCoh`
extends it with exactly the allocator-health facts `CohG` states
non-vacuously once cursor key 0 is PRESENT (charter P1.2's list):
every tracked allocation id is below `σ.nextAllocId`; ids at or
above `σ.nextAllocId` are absent from both the live and the dead
allocation tables; every tracked allocation (hence every tracked
byte) lies at or above the downward cursor `σ.lastAddress`; and the
requested initial plan fits the actual
`⟨σ.lastAddress, σ.nextAllocId⟩`. (Spelling note vs the charter's
`LaunchCoh σ m`: the plan is an explicit third argument — the
charter's fourth fact mentions the requested plan, which is not a
function of σ and m.) -/

open Iris.Std.PartialMap in
/-- Launch coherence: footprint coherence + allocator health + the
    plan fit. What an allocation-aware launcher demands of the
    initial state. -/
structure LaunchCoh (tds : CerbTags.TagDefsMap) (σ : Mem) (m : SpikeHeapF SpikeCell)
    (reqs : List AllocReq) : Prop where
  coh : Coh tds σ m
  id_lt : ∀ i c, get? m i = some c → i < σ.nextAllocId
  fresh_alloc : ∀ id : Int, σ.nextAllocId ≤ id →
    σ.allocations.get? id = none
  fresh_dead : ∀ id : Int, σ.nextAllocId ≤ id →
    σ.deadAllocations.contains id = false
  addr_lo : ∀ i c, get? m i = some c → σ.lastAddress ≤ c.addr
  plan : PlanFits tds ⟨σ.lastAddress, σ.nextAllocId⟩ reqs
  /-- The launch cursor respects the machine address bound (real
      Cerberus starts the downward cursor at 0xFFFFFFFFFFFF < 2^64;
      alloc arc P2 — rides inside `allocCap` so the public create
      rules can export the fresh pointer's address-WF bounds). -/
  la_wf : σ.lastAddress ≤ 2 ^ 64

open Iris.Std.PartialMap in
/-- Launch coherence at the EMPTY footprint: allocator health + the
    plan (cold-start programs allocate everything themselves). -/
theorem LaunchCoh.empty (tds : CerbTags.TagDefsMap) (σ : Mem) (reqs : List AllocReq)
    (halloc : ∀ id : Int, σ.nextAllocId ≤ id →
      σ.allocations.get? id = none)
    (hdead : ∀ id : Int, σ.nextAllocId ≤ id →
      σ.deadAllocations.contains id = false)
    (hplan : PlanFits tds ⟨σ.lastAddress, σ.nextAllocId⟩ reqs)
    (hla : σ.lastAddress ≤ 2 ^ 64) :
    LaunchCoh tds σ (∅ : SpikeHeapF SpikeCell) reqs := by
  have hnone : ∀ i : Int, get? (∅ : SpikeHeapF SpikeCell) i = none :=
    fun i => Iris.Std.LawfulPartialMap.get?_empty i
  refine ⟨⟨?_, ?_⟩, ?_, halloc, hdead, ?_, hplan, hla⟩
  · intro i c hg
    rw [hnone i] at hg
    cases hg
  · intro i j c1 c2 hne h1 h2
    rw [hnone i] at h1
    cases h1
  · intro i c hg
    rw [hnone i] at hg
    cases hg
  · intro i c hg
    rw [hnone i] at hg
    cases hg

open Iris.Std.PartialMap in
/-- The launched coupling: a launch-coherent footprint's ghost
    images couple to σ WITH the cursor cell present at key 0 — the
    `cur_*` facts of `CohG` are NON-VACUOUS here (contrast
    `MetaByteOf.cohG` above, whose empty cursor map makes them
    vacuous), discharged from `LaunchCoh`'s allocator health. -/
theorem LaunchCoh.cohG {tds : CerbTags.TagDefsMap} {σ : Mem} {m : SpikeHeapF SpikeCell}
    {reqs : List AllocReq}
    {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
    (h : LaunchCoh tds σ m reqs) (hmbo : MetaByteOf tds m mm mb) :
    CohG σ mm mb
      (Iris.Std.PartialMap.insert (∅ : SpikeHeapF AllocCursor) 0
        ⟨σ.lastAddress, σ.nextAllocId⟩) := by
  have base := hmbo.cohG h.coh
  refine ⟨base.metas, base.metas_disj, base.bytes,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cursor_key
    intro k c hget
    by_cases hk : k = 0
    · exact hk
    · rw [Iris.Std.get?_insert_ne (fun hh => hk hh.symm),
        Iris.Std.LawfulPartialMap.get?_empty] at hget
      cases hget
  · -- cursor: the launched cell pins the REAL allocator fields
    intro c hget
    rw [Iris.Std.get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    exact ⟨rfl, rfl⟩
  · -- cur_dead
    intro _ id hle
    exact h.fresh_dead id hle
  · -- cur_alloc
    intro _ id hle
    exact h.fresh_alloc id hle
  · -- cur_meta_lt
    intro _ id mc hget
    obtain ⟨c, hc, rfl⟩ := hmbo.meta_sub id mc hget
    exact h.id_lt id c hc
  · -- cur_byte_lo: tracked bytes sit inside tracked cells, which sit
    -- at or above the cursor
    intro _ k b hget
    obtain ⟨i, c, hc, hk1, -, -⟩ := hmbo.byte_cov k b hget
    exact Int.le_trans (h.addr_lo i c hc) hk1
  · -- cur_meta_lo
    intro _ id mc hget
    obtain ⟨c, hc, rfl⟩ := hmbo.meta_sub id mc hget
    exact h.addr_lo id c hc

/-- The launched cursor key is NONEMPTY (merge-row-3 must-prove,
    stated once): key 0 of the launched cursor map holds the real
    allocator fields, so every `get? mk 0 ≠ none` hypothesis of
    `CohG`'s `cur_*` fields is satisfied at launch. -/
theorem launchCursor_key_nonempty (σ : Mem) :
    Iris.Std.PartialMap.get?
      (Iris.Std.PartialMap.insert (∅ : SpikeHeapF AllocCursor) 0
        ⟨σ.lastAddress, σ.nextAllocId⟩) 0 =
      some ⟨σ.lastAddress, σ.nextAllocId⟩ :=
  Iris.Std.get?_insert_eq rfl

open Iris.Std.PartialMap in
/-- THE SHARED ALLOCATION-AWARE LAUNCH (charter P1.3, the one
    helper): from the three empty ghost heaps, allocate every
    footprint cell AND the allocator cursor at key 0 — the
    previously missing allocation step in the launch path (R-01).
    Delivers the assembled state interpretation (cursor key
    nonempty; `CohG` non-vacuous through `LaunchCoh.cohG`), the
    per-cell ownership, and the abstract capacity `allocCap reqs`
    wrapping the exclusive cursor fragment. -/
theorem launchResources (tds : CerbTags.TagDefsMap) {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (σ : Mem) (m : SpikeHeapF SpikeCell) (reqs : List AllocReq)
    (h : LaunchCoh tds σ m reqs) :
    iprop(metaInterp (GF := GF) (∅ : SpikeHeapF MetaCell) ∗
        byteInterp (∅ : SpikeHeapF CerbMem.AbsByte) ∗
        cursorInterp (∅ : SpikeHeapF AllocCursor)) ⊢
      |==> iprop(stateInterp σ 0 ([] : List Empty) 0 ∗
        ([∗map] i ↦ c ∈ m, cellOwn tds (hlc := .hasLC) i (.own 1) c) ∗
        allocCap tds reqs) := by
  iintro ⟨Hmi, Hbi, Hki⟩
  imod (spikeCells_alloc tds σ m h.coh) $$ [$Hmi $Hbi]
    with ⟨%mm, %mb, %hmbo, Hmi, Hbi, Hcells⟩
  imod (cursorHeap_alloc (⟨σ.lastAddress, σ.nextAllocId⟩ : AllocCursor)
    (Iris.Std.LawfulPartialMap.get?_empty 0)) $$ [$Hki] with ⟨Hki, Hc⟩
  imodintro
  isplitl [Hmi Hbi Hki]
  · iapply (stateInterp_iff _ _ _ _).mpr
    iexists mm, mb,
      (Iris.Std.PartialMap.insert (∅ : SpikeHeapF AllocCursor) 0
        ⟨σ.lastAddress, σ.nextAllocId⟩)
    isplit
    · ipureintro
      exact h.cohG hmbo
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  isplitl [Hcells]
  · iexact Hcells
  · iapply allocCap_intro tds ⟨σ.lastAddress, σ.nextAllocId⟩ reqs h.plan
      h.la_wf $$ Hc

/-! ## Step-level adequacy: constructing SpikeGS and applying iris -/

/-- Iris adequacy over Step, with final-state readout: constructs
    the bundled ghost state (SpikeGS — nothing is assumed
    pre-allocated) from the initial cell map and applies
    `wp_strong_adequacy_gen`. The postcondition is a readout wand:
    it consumes the final state interpretation, so cell ownership at
    the end pins facts about the FINAL MemState. -/
theorem spike_step_adequacy (tds : CerbTags.TagDefsMap) {GF : BundledGFunctors} [SpikeGpreS GF]
    (e : CoreRt) (σ : Mem) (m₀ : SpikeHeapF SpikeCell) (hcoh : Coh tds σ m₀)
    (φp : CoreRVal → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
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
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk }
  imod (spikeCells_alloc tds σ m₀ hcoh) $$ [$Hmi $Hbi]
    with ⟨%mm, %mb, %hmbo, Hmi, Hbi, Hcells⟩
  imodintro
  iexists fun (σ' : Mem) (_ : Nat) (_ : List Empty) (_ : Nat) =>
    iprop(∃ mm mb mk, ⌜CohG σ' mm mb mk⌝ ∗
      metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk)
  iexists [fun (v : CoreRVal) => iprop(∀ (σ' : Mem) (ns : Nat)
    (κs' : List Empty) (nt : Nat), stateInterp σ' ns κs' nt ={⊤, ∅}=∗ ⌜φp v σ'⌝)]
  iexists fun _ => iprop(True)
  iexists fun _ _ _ _ => fupd_intro
  dsimp only
  isplitl [Hmi Hbi Hki]
  · iexists mm, mb, (∅ : SpikeHeapF AllocCursor)
    isplit
    · ipureintro
      exact hmbo.cohG hcoh
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  isplitl [Hcells]
  · iapply BigSepL2.bigSepL2_singleton
    ihave HW := hwp $$ Hcells
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

/-- ALLOCATION-AWARE step adequacy (alloc arc P1.3): as
    `spike_step_adequacy`, but launched through the one shared
    `launchResources` helper — the client's proof receives the
    footprint cells AND `allocCap reqs`, and the cursor ghost heap is
    launched NONEMPTY at the real `⟨lastAddress, nextAllocId⟩`. The
    cursor-free launcher above remains for no-allocation programs
    (charter P1.3's incremental-migration allowance; retire it for
    one complete launcher once every client is ported). -/
theorem spike_step_adequacy_alloc (tds : CerbTags.TagDefsMap) {GF : BundledGFunctors} [SpikeGpreS GF]
    (e : CoreRt) (σ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (reqs : List AllocReq) (hl : LaunchCoh tds σ m₀ reqs)
    (φp : CoreRVal → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀,
          cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        allocCap tds reqs) ⊢
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
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk }
  imod (launchResources tds σ m₀ reqs hl) $$ [$Hmi $Hbi $Hki]
    with ⟨Hσ, Hcells, Hcap⟩
  imodintro
  iexists fun (σ' : Mem) (_ : Nat) (_ : List Empty) (_ : Nat) =>
    iprop(∃ mm mb mk, ⌜CohG σ' mm mb mk⌝ ∗
      metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk)
  iexists [fun (v : CoreRVal) => iprop(∀ (σ' : Mem) (ns : Nat)
    (κs' : List Empty) (nt : Nat), stateInterp σ' ns κs' nt ={⊤, ∅}=∗ ⌜φp v σ'⌝)]
  iexists fun _ => iprop(True)
  iexists fun _ _ _ _ => fupd_intro
  dsimp only
  isplitl [Hσ]
  · iexact Hσ
  isplitl [Hcells Hcap]
  · iapply BigSepL2.bigSepL2_singleton
    ihave HW := hwp $$ [$Hcells $Hcap]
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
    (hfrag : Frag e₀) (hcoh : Coh M.tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
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
    spike_step_adequacy M.tagDefs ⟨e₀, ev00 :: evs0, M⟩ σ₀ m₀ hcoh
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
    (hfrag : Frag e₀) (hcoh : Coh spikeCtx.tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn spikeCtx.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
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

/-- ALLOCATION-AWARE engine adequacy at any machine context (alloc
    arc P2 — the partial lane's engine face for allocating clients):
    as `engine_adequacyU`, but launched through `launchResources` —
    the client's WP proof receives the footprint cells AND
    `allocCap reqs` (via `spike_step_adequacy_alloc`). -/
theorem engine_adequacyU_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell) (reqs : List AllocReq)
    (hfrag : Frag e₀) (hl : LaunchCoh M.tagDefs σ₀ m₀ reqs)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀,
          cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        allocCap M.tagDefs reqs) ⊢
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
    spike_step_adequacy_alloc M.tagDefs ⟨e₀, ev00 :: evs0, M⟩ σ₀ m₀ reqs hl
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

/-- ALLOCATION-AWARE spike-face engine adequacy (alloc arc P2): the
    `spike_engine_adequacy` face launched through `launchResources`
    — the drive-lane engine conclusion for a whole program that
    allocates its own cells from `allocCap`. -/
theorem spike_engine_adequacy_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    (e₀ : CoreExpr) (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (reqs : List AllocReq)
    (hfrag : Frag e₀) (hl : LaunchCoh spikeCtx.tagDefs σ₀ m₀ reqs)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀,
          cellOwn spikeCtx.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        allocCap spikeCtx.tagDefs reqs) ⊢
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
  engine_adequacyU_alloc (GF := GF) (M := spikeCtx) spikeCtx_wf
    (fun l params cont hl' => (spikeCtx_labels_none l hl').elim)
    e₀ fmapEmpty [] σ₀ m₀ reqs hfrag hl ψ hwp n aids hfuel
    (fun l params cont hl' => (spikeCtx_labels_none l hl').elim)

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
abbrev Sat (tds : CerbTags.TagDefsMap) (σ : Mem) (m : CellMap) : Prop := Coh tds σ m

/-- Satisfaction is closed under shrinking the footprint (substitute
    into larger/more constraining contexts, satisfaction side). -/
theorem Sat.mono {tds : CerbTags.TagDefsMap} {σ : Mem} {m m' : CellMap} (h : Sat tds σ m) (hsub : m' ⊆ m) :
    Sat tds σ m' :=
  ⟨fun i c hg => h.cells i c (hsub i c hg),
   fun i j c1 c2 hne h1 h2 => h.disj i j c1 c2 hne (hsub _ _ h1) (hsub _ _ h2)⟩

/-- Satisfaction of a (left-biased) union restricts to its left
    component: `get?` on the union answers the left map's entry
    verbatim wherever the left map is defined. -/
theorem Sat.union_left {tds : CerbTags.TagDefsMap} {σ : Mem} {Q R : CellMap}
    (h : Sat tds σ (Iris.Std.PartialMap.union Q R)) : Sat tds σ Q := by
  have hlift : ∀ i (c : SpikeCell), Iris.Std.PartialMap.get? Q i = some c →
      Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union Q R) i = some c := by
    intro i c hg
    have hu : Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union Q R) i =
        (Iris.Std.PartialMap.get? Q i).orElse
          (fun _ => Iris.Std.PartialMap.get? R i) :=
      Iris.Std.LawfulPartialMap.get?_union
    rw [hu, hg]
    rfl
  exact ⟨fun i c hg => h.cells i c (hlift i c hg),
    fun i j c1 c2 hne h1 h2 =>
      h.disj i j c1 c2 hne (hlift _ _ h1) (hlift _ _ h2)⟩

/-- THE SEMANTIC TRIPLE ⦃P⦄ e ⦃post⦄, engine vocabulary only: for
    every memory that splits as P ⊎ R — footprint P satisfied,
    rest R ARBITRARY — AT THE FIXED DEMO MACHINE PROFILE
    (`spikeThread`/`spikeCtx`/`spikeEnv`; the thread/context are not
    quantified — 2026-09-01 re-audit R-09, generalization owned by
    alloc arc P4) — the engine's drive never kills or derails,
    and any delivered value v comes with a post-footprint Q with
    `post v Q`, THE SAME R returned verbatim (Sat σ' (Iris.Std.PartialMap.union Q R)).
    Partial correctness: fuel exhaustion (.more) is unconstrained;
    the fuel bound is the engine's own get_ctx budget (Soundness.lean,
    FUEL HONESTY). -/
def SemTriple (e : CoreExpr) (P : CellMap)
    (post : value → CellMap → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat spikeCtx.tagDefs σ (Iris.Std.PartialMap.union P R) →
  ∀ (n : Nat) (aids : Nat → Nat), esize e + n ≤ lemDefaultFuel →
    (∀ r, drive aids n (spikeThread e) σ ≠ .killed r) ∧
    (drive aids n (spikeThread e) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), drive aids n (spikeThread e) σ = .done v σ' →
      ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧ Sat spikeCtx.tagDefs σ' (Iris.Std.PartialMap.union Q R))

/-- INTERIOR: the derived logic (the slice-A separation logic — Iris
    WP over Step) proves the footprint triple. This definition is
    the only place the WP appears in the exported layer. -/
abbrev ProvenTriple (GF : BundledGFunctors) [SpikeGpreS GF] (e : CoreExpr)
    (P : CellMap) (post : value → CellMap → Prop) : Prop :=
  ∀ [SpikeGS .hasLC GF],
    iprop(([∗map] i ↦ c ∈ P, cellOwn spikeCtx.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
      WP (⟨e, spikeEnv, spikeCtx⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w,
        iprop(∃ Q : CellMap, ⌜post (CoreRVal.val w) Q⌝ ∗
          ([∗map] i ↦ c ∈ Q, cellOwn spikeCtx.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) }}

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
theorem bigSepM_own_disjoint (tds : CerbTags.TagDefsMap) {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (Q R : CellMap) :
    iprop(([∗map] i ↦ c ∈ Q, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
          ([∗map] i ↦ c ∈ R, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
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
    icases (cellOwn_iff tds k (.own 1) cq).mp $$ HkQ with ⟨HkQm, -, -⟩
    icases (cellOwn_iff tds k (.own 1) cr).mp $$ HkR with ⟨HkRm, -, -⟩
    ihave %hne := metaOwn_ne $$ HkQm [HkRm]
    · iexact HkRm
    exact absurd rfl hne

open Iris.Std.PartialMap in
/-- Per-footprint extraction: whole-cell ownership of every cell of a
    footprint, against the coupling, yields footprint satisfaction —
    per-cell facts by `cellOwn_cellCoh`, pairwise disjointness through
    the metadata authority's `metas_disj` invariant. -/
theorem cellsOwn_facts (tds : CerbTags.TagDefsMap) {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    {σ : Mem} {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
    {mk : SpikeHeapF AllocCursor} (hG : CohG σ mm mb mk)
    (Q : SpikeHeapF SpikeCell) :
    iprop(metaInterp (GF := GF) mm ∗ byteInterp mb ∗
        ([∗map] i ↦ c ∈ Q, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
      (⌜∀ i c, get? Q i = some c →
        CellCoh tds σ i c ∧ get? mm i = some (metaOf tds c)⌝ : IProp GF) := by
  induction Q using Iris.Std.LawfulFiniteMap.induction_on with
  | hemp =>
    iintro ⟨-, -, -⟩
    ipureintro
    intro i c h
    rw [Iris.Std.LawfulPartialMap.get?_empty] at h
    cases h
  | hins i c Q'' Hl IH =>
    iintro ⟨Hmi, Hbi, HQ⟩
    icases (BigSepM.bigSepM_insert (Φ := fun i c =>
      cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c) Hl).1 $$ HQ with ⟨Hc, Hrest⟩
    ihave %hone : ⌜CellCoh tds σ i c ∧ get? mm i = some (metaOf tds c)⌝ $$ [Hmi Hbi Hc]
    · iapply cellOwn_cellCoh tds hG i (.own 1) c $$ [$Hmi $Hbi $Hc]
    ihave %hrest : ⌜∀ j c', get? Q'' j = some c' →
        CellCoh tds σ j c' ∧ get? mm j = some (metaOf tds c')⌝ $$ [Hmi Hbi Hrest]
    · iapply IH $$ [$Hmi $Hbi $Hrest]
    ipureintro
    intro j c' hg
    by_cases hj : j = i
    · subst hj
      rw [Iris.Std.get?_insert_eq rfl] at hg
      obtain rfl : c = c' := Option.some.inj hg
      exact hone
    · rw [Iris.Std.get?_insert_ne (fun h => hj h.symm)] at hg
      exact hrest j c' hg

open Iris.Std.PartialMap in
theorem cellsOwn_extract (tds : CerbTags.TagDefsMap) {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    {σ : Mem} {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
    {mk : SpikeHeapF AllocCursor} (hG : CohG σ mm mb mk)
    (Q : SpikeHeapF SpikeCell) :
    iprop(metaInterp (GF := GF) mm ∗ byteInterp mb ∗
        ([∗map] i ↦ c ∈ Q, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
      (⌜Coh tds σ Q⌝ : IProp GF) := by
  iintro ⟨Hmi, Hbi, HQ⟩
  ihave %hfacts : ⌜∀ i c, get? Q i = some c →
      CellCoh tds σ i c ∧ get? mm i = some (metaOf tds c)⌝ $$ [Hmi Hbi HQ]
  · iapply cellsOwn_facts tds hG Q $$ [$Hmi $Hbi $HQ]
  ipureintro
  refine ⟨fun i c hg => (hfacts i c hg).1, fun i j ci cj hne hgi hgj => ?_⟩
  exact (cellsDisjoint_iff_metaDisjoint tds ci cj).mpr
    (hG.metas_disj i j (metaOf tds ci) (metaOf tds cj) hne
      (hfacts i ci hgi).2 (hfacts j cj hgj).2)

/-- The cell-footprint readout: post-cells + frame-cells consume the
    final state interpretation into the pure semantic-triple
    conclusion. -/
theorem cells_readout (tds : CerbTags.TagDefsMap) {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (post : value → CellMap → Prop) (R : CellMap) (vv : value) :
    iprop((∃ Q : CellMap, ⌜post vv Q⌝ ∗
        ([∗map] i ↦ c ∈ Q, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) ∗
        ([∗map] i ↦ c ∈ R, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
      iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
        stateInterp σ' ns κs nt ={⊤, ∅}=∗
          ⌜∃ Q : CellMap, post vv Q ∧ Q ##ₘ R ∧ Coh tds σ' (Iris.Std.PartialMap.union Q R)⌝) := by
  iintro ⟨⟨%Q, %hpost, HQ⟩, HR⟩ %σ' %ns %κs %nt Hsi
  icases (stateInterp_iff σ' ns κs nt).mp $$ Hsi
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  ihave %hd : ⌜Q ##ₘ R⌝ $$ [HQ HR]
  · iapply bigSepM_own_disjoint tds Q R $$ [$HQ $HR]
  ihave HQR : iprop([∗map] i ↦ c ∈ (Iris.Std.PartialMap.union Q R),
      cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c) $$ [HQ HR]
  · iapply (BigSepM.bigSepM_union hd).2 $$ [$HQ $HR]
  ihave %hsat : ⌜Coh tds σ' (Iris.Std.PartialMap.union Q R)⌝ $$ [Hmi Hbi HQR]
  · iapply cellsOwn_extract tds HG (Iris.Std.PartialMap.union Q R) $$ [$Hmi $Hbi $HQR]
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact ⟨Q, hpost, hd, hsat⟩

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
    (fun v σ' => ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧ Coh spikeCtx.tagDefs σ' (Iris.Std.PartialMap.union Q R)) ?_ n aids hfuel
  intro instGS
  refine .trans (BigSepM.bigSepM_union hdisj).1 ?_
  iintro ⟨HP, HR⟩
  ihave HW := hwp $$ HP
  iapply spike_wp_wand $$ HW
  iintro %w Hpost
  iapply cells_readout spikeCtx.tagDefs post R (CoreRVal.val w)
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
  · iapply bigSepM_own_disjoint spikeCtx.tagDefs Q₀ F $$ [$HQ $HF]
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
        (dischargeStep (rsCtx rs).tagDefs aid rs σ) = engineOutcomesP p aid rs e ρ σ := rfl

/-- The succ-step equation at the run-state instance, old spelling
    (rfl). -/
theorem driveJ_succ_eq (rs : core_run_state) (aids : Nat → Nat) (n : Nat)
    (th : thread_state) (σ : Mem) :
    driveJ rs aids (n+1) th σ =
      (match (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
          (dischargeStep (rsCtx rs).tagDefs (aids 0) rs σ) with
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
    (hfrag : Frag e₀) (hcoh : Coh (procCtx p rs).tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn (procCtx p rs).tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
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
