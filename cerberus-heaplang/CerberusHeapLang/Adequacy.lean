/-
CerberusHeapLang.Adequacy — adequacy: where proofs in the derived
logic become facts about the engine's execution.

Four layers:
1. `driveU` — THE ENGINE'S EXECUTION at a machine context: the
   discharge loop {step_ctx → Driver.lean:273 discharge} as a
   definition over engine objects (thread_state, MemState,
   core_step2), with an explicit per-step action-id supply and
   explicit drive length. Engine vocabulary only, plus this package's
   projection `dischargeStep` (Soundness.lean) — the readout predicate
   the walkthrough prints. It is the one drive; `spikeCtx`/`procCtx`
   are contexts it runs at, not separate drives.
2. `spike_step_adequacy` — the Iris adequacy instance: the bundled
   ghost state `SpikeGS` is CONSTRUCTED here (`genHeap_init` over the
   initial cell map, `spikeCells_alloc`), and iris-lean's
   `wp_strong_adequacy_gen` yields NotStuck + postcondition readout
   for every Step-reachable configuration. HeapLang's heap_adequacy
   (Iris/HeapLang/PrimitiveLaws.lean:131) is the template; the strong
   variant is needed because the fragment's postconditions read out
   the FINAL MEMORY STATE (through the state interpretation), not
   just the value. `spike_step_adequacy_alloc` is the allocation-aware
   twin: `launchResources` under `LaunchCoh` also mints the allocator
   cursor and grants `allocCap`.
3. `engine_adequacyU` (+ `_alloc`) — THE ENGINE-ONLY STATEMENT: a
   proved WP plus a seeded MemState satisfying the precondition
   footprint implies the engine's drive never kills (no UB, no error
   kill, no ILLTYPED refusal, no off-protocol step) and any final
   value+state it delivers satisfies the postcondition readout. The
   CONCLUSION quantifies over engine objects only (the program term,
   the MemState, drive length, the action-id supply, DriveResult);
   Step / WP / Iris vocabulary appears only in the hypotheses.
4. `project_triple_pure` — THE HEADLINE PROJECTION: ANY Iris triple
   with a concrete-map precondition and an ARBITRARY Iris
   postcondition `Q` whose (framed) post pure-entails `ψ R w.val σ'`
   under the coupling projects to the BORING triple `MemTripleU M ρ e
   P ψ` — memory splits as P ⊎ R, the engine's drive never kills or
   derails at any length, and every delivered `(v, σ')` satisfies the
   PURE `ψ R v σ'` — with no Iris vocabulary in the conclusion. The
   pure-consequence lemmas (`*_consequence`) discharge its one
   Iris-shaped hypothesis for the points-to shapes. Properties are
   STATED in Iris; no rule is restated and no second assertion
   language exists. Beneath it, `project_triple` is the strongest-post
   form (post = "every pure consequence of `Q ∗ frame` at σ'"), from
   which the pure one is derived; `semantic_triple_soundU` is
   `project_triple` at the cells-shaped post (`SemTripleU_iff_Mem`).
   The precondition is footprint cells ONLY; the ALLOCATING twins
   `project_triple_pure_alloc` / `project_triple_alloc` take footprint
   cells ∗ `allocCap reqs` and conclude `MemTripleU_alloc` (the same
   triple launched under `LaunchCoh` with the plan;
   `MemTripleU_alloc_of_MemTripleU` records the direction that holds
   between the two); `struct_create_store_adequacy` is an instance.

TWO TRUST CLAIMS (the README's "The trust story"): (1) the
CLOSED-PROGRAM exports have Iris-free statements — cerberus-lean's
semantics (`step_ctx`/discharge, or the shipped driver) as the
referents plus the pure readout predicates (`Sat`/`CellCoh`,
`readBytesFrom`); iris-lean appears only INSIDE kernel-checked proof
terms and contributes no axiom (Audit.lean pins every export's cone to
the classical trio), so it is CHECKED, not trusted. (2) the REUSABLE
rules and `project_triple`'s hypotheses are stated in Iris assertions,
whose must-read set — `pointsToCell`/`cellOwn`, `CohG`, iris-lean's WP
and BI connectives — is the one sense in which iris-lean is "in the
trust base": definitions to read, not axioms to accept. The projection
makes claim (1) uniform: any property STATED in Iris lands as an
engine fact whose statement is Iris-free except for the
pure-consequence obligation the consequence lemmas discharge.

Certification direction used (Soundness.lean header): match-given-
step. Each drive step is `engine_step_matchU`'s unique engine
behaviour (`drive_classifyU`); Step-matched behaviours stay in the
WP-covered cone, refusals contradict NotStuck, and the value protocol
composes the REMOVE-ANNOT tau with PROGRAM-DONE (annotations erased by
`SpikeVal.val` in the readout).

FUEL HONESTY, STATIC FORM: the engine's get_ctx budget enters every
drive statement as the two STATIC premises `pot e₀ ≤ lemDefaultFuel`
and, per registered label body, `pot cont ≤ lemDefaultFuel`
(Potential.lean: `pot` never increases along a fragment step and
resets to the registered body at a jump, and it bounds `esize`), so
the drive length `n` is quantified UNBOUNDED — a partial-correctness
statement says something about every run, however long. The boring
triples `MemTripleU`/`MemTripleU_alloc`/`SemTripleU` carry NO fuel
premise: the static bounds are hypotheses of the projection theorems,
`rfl`-closed for authored programs. Termination is NOT claimed
(partial correctness): `.more` carries no obligation.
-/
import CerberusHeapLang.Rules
import CerberusHeapLang.Soundness
import CerberusHeapLang.Potential

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
  /-- the engine killed. `kill_reason mem_error` (Nondeterminism.lean:54)
      has three constructors. `Undef0 loc ubs` — undefined behaviour:
      from the memory model, a `mem_error` mapped through
      `undefinedFromMem_error` (Mem_common.lean:392) by `failReason`
      (CerbMem.lean:1439) — null/no-provenance/out-of-bounds/dead/
      outside-lifetime/atomic-member access, the `_Bool` trap
      representation on load, a store to a read-only allocation
      (`loadM` CerbMem.lean:1621-1664, `storeM` :1667-1730) — or from
      the Core-run layer's own `Undef` result (`liftCore_run`,
      Driver.lean:245-247). `Other err` — the non-UB memory errors: a
      store with an ill-typed memory value (`MerrOther`, :1702) and
      function-pointer access (`MerrAccess _ FunctionPtr`). `Error0 loc
      msg` — the Core-run layer's `Error` result (`liftCore_run`, same
      lines; never produced by `loadM`/`storeM`). "Never kills" below
      excludes ALL THREE, not only UB. -/
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

/-- THE UNIFIED CLASSIFICATION (the one drive classification, at any
    machine context): from Step-level NotStuck + value readout over
    `Reach`, every driveU outcome is DriveOk — via
    `engine_step_matchU`, one certification case per step. The fuel
    premises are STATIC (required fix 1): `pot e ≤ lemDefaultFuel` at
    the current term and `pot cont ≤ lemDefaultFuel` for every
    registered body; `Frag.pot_step_bound` carries the bound across a
    step (non-increase, or the jump reset to a registered body) and
    `Frag.esize_le_pot` discharges `engine_step_matchU`'s `esize`
    obligation, so the drive length `n` is UNBOUNDED. -/
theorem drive_classifyU {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (e₀ : CoreExpr) (ρ₀ : EnvStack) (σ₀ : Mem)
    (φp : CoreRVal → Mem → Prop)
    (hNS : ∀ (r : CoreRt) (σ : Mem),
      Reach ((⟨e₀, ρ₀, M⟩ : CoreRt), σ₀) (r, σ) →
      PrimStep.NotStuck (Val := CoreRVal) (r, σ))
    (hRES : ∀ (w : CoreRVal) (σ : Mem),
      Reach ((⟨e₀, ρ₀, M⟩ : CoreRt), σ₀) (ofValRt w, σ) → φp w σ) :
    ∀ (n : Nat) (aids : Nat → Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem),
      Reach ((⟨e₀, ρ₀, M⟩ : CoreRt), σ₀) ((⟨e, ev0 :: evs, M⟩ : CoreRt), σ) →
      Frag e → pot e ≤ lemDefaultFuel →
      DriveOk φp (driveU M aids n (M.thread e (ev0 :: evs)) σ) := by
  intro n
  induction n with
  | zero => intro aids e ev0 evs σ _ _ _; trivial
  | succ n ih =>
    intro aids e ev0 evs σ hreach hf hpot
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
          engine_step_matchU (aids 0) hf (Nat.le_trans hf.esize_le_pot hpot) hs]
        refine ih _ re' ev0' evs σ'
          (hreach.tail ⟨hs, rfl⟩) (hf.step hQf hs) ?_
        rcases hf.pot_step_bound hs with hle | ⟨l, pes, params, cont, -, hl, hec⟩
        · exact Nat.le_trans hle hpot
        · rw [hec]
          exact hQpot l params cont hl

/-- ADEQUACY AT A MACHINE CONTEXT (engine-only conclusion — THE
    adequacy, every closed-program export is an instance): a proved
    WP at the unified tuple plus the seeded memory implies driveU
    from the context's thread never kills, never derails, and any
    delivered value satisfies the readout — for EVERY drive length
    `n` and action-id supply. The fuel premises are the static
    `pot` bounds (program and every registered label body; required
    fix 1). Explicit WF hypothesis: `SeqWF`. -/
theorem engine_adequacyU {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel) (hcoh : Coh M.tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        WP (⟨e₀, ev00 :: evs0, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, iprop(∀ (σ' : Mem) (ns : Nat)
          (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝) }})
    (n : Nat) (aids : Nat → Nat) :
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
    drive_classifyU hwf hQf hQpot e₀ (ev00 :: evs0) σ₀ _ hNS hRES
      n aids e₀ ev00 evs0 σ₀ .refl hfrag hpot
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

/-- The straight-line profile registers no labels: the label-cone and
    label-budget premises of the adequacy/projection theorems are
    vacuous there (the two spellings every `spikeCtx` client passes). -/
theorem spikeCtx_labels_frag (l : sym) (params : List (sym × core_base_type))
    (cont : CoreExpr) (hl : lookupLabel spikeCtx.labels l = some (params, cont)) :
    Frag cont := (spikeCtx_labels_none l hl).elim

theorem spikeCtx_labels_pot (l : sym) (params : List (sym × core_base_type))
    (cont : CoreExpr) (hl : lookupLabel spikeCtx.labels l = some (params, cont)) :
    pot cont ≤ lemDefaultFuel := (spikeCtx_labels_none l hl).elim

/-- ALLOCATION-AWARE engine adequacy at any machine context (alloc
    arc P2 — the partial lane's engine face for allocating clients):
    as `engine_adequacyU`, but launched through `launchResources` —
    the client's WP proof receives the footprint cells AND
    `allocCap reqs` (via `spike_step_adequacy_alloc`). -/
theorem engine_adequacyU_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell) (reqs : List AllocReq)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel)
    (hl : LaunchCoh M.tagDefs σ₀ m₀ reqs)
    (ψ : value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀,
          cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        allocCap M.tagDefs reqs) ⊢
        WP (⟨e₀, ev00 :: evs0, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
          {{ w, iprop(∀ (σ' : Mem) (ns : Nat)
          (κs : List Empty) (nt : Nat),
          stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜ψ w.val σ'⌝) }})
    (n : Nat) (aids : Nat → Nat) :
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
    drive_classifyU hwf hQf hQpot e₀ (ev00 :: evs0) σ₀ _ hNS hRES
      n aids e₀ ev00 evs0 σ₀ .refl hfrag hpot
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
appears only inside `ProvenTripleU` (the judgment that the derived
logic proved the triple), never in `SemTripleU`. -/

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

/-- THE SEMANTIC TRIPLE ⦃P⦄ e ⦃post⦄ AT ANY MACHINE CONTEXT AND ENTRY
    ENVIRONMENT (alloc arc P4.3, R-09), engine vocabulary only: for
    every memory that splits as P ⊎ R — footprint P satisfied, rest R
    ARBITRARY — the engine's unified drive from `M`'s thread around
    `(e, ρ)` never kills or derails, and any delivered value `v` comes
    with a post-footprint `Q` with `post v Q`, THE SAME `R` returned
    verbatim (`Sat σ' (Q ∪ R)`). Partial correctness: fuel exhaustion
    (`.more`) is unconstrained, and the drive length `n` is UNBOUNDED
    — the triple carries no fuel premise (the engine's static get_ctx
    budget, `pot`, is a hypothesis of the projection theorems that
    produce triples; header, FUEL HONESTY). -/
def SemTripleU (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (post : value → CellMap → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat M.tagDefs σ (Iris.Std.PartialMap.union P R) →
  ∀ (n : Nat) (aids : Nat → Nat),
    (∀ r, driveU M aids n (M.thread e ρ) σ ≠ .killed r) ∧
    (driveU M aids n (M.thread e ρ) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), driveU M aids n (M.thread e ρ) σ = .done v σ' →
      ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧
        Sat M.tagDefs σ' (Iris.Std.PartialMap.union Q R))

/-- INTERIOR, at any machine context and entry environment: the derived
    logic (Iris WP over Step) proves the footprint triple. -/
abbrev ProvenTripleU (GF : BundledGFunctors) [SpikeGpreS GF] (M : MachineCtx)
    (ρ : EnvStack) (e : CoreExpr) (P : CellMap) (post : value → CellMap → Prop) : Prop :=
  ∀ [SpikeGS .hasLC GF],
    iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
      WP (⟨e, ρ, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w,
        iprop(∃ Q : CellMap, ⌜post (CoreRVal.val w) Q⌝ ∗
          ([∗map] i ↦ c ∈ Q, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) }}

/-! ## THE PROJECTION THEOREM ([USER 2026-09-02], DECISIONS: "don't
prove the rules, but show that any iris-level triple can be projected
into a 'boring' triple over semantic states. This gives us the ability
to state properties via iris but doesn't mirror the logic")

Target shape ([USER], verbatim): `s |= P && core_exec(prog, s) ~~> term
==> term = some(s') && s' |= Q`, P/Q "just memory + pure properties".
Here: `Sat σ (P ∪ R)` is `s |= P` (with the frame R built in, as
`SemTripleU` does); `driveU M aids n (M.thread e ρ) σ` is
`core_exec(prog, s)`; `.done v σ'` is `term = some(s')` (the two
other arms are the never-kills / never-derails conjuncts); `post R v
σ'` is `s' |= Q`. The projection's `post` is "every pure consequence
of the Iris postcondition (with the frame's cells) at σ'": a pure
`ψ` holds of `(v, σ')` whenever, against EVERY coupling witness for
σ', the Iris post `Q w` (for every `w` erasing to `v`) together with
the frame and the interpretation's components entails `⌜ψ⌝`. That
obligation is discharged by the pure-consequence lemmas below
(`cellOwn_consequence`, `pointsToCell_consequence`,
`cells_consequence`, and the `∗`/`∨`/`∃`/pure combinators) — it is
never opened by a client.

Two trust claims (header): `project_triple_pure`'s conclusion is
Iris-free, full stop; its one Iris-shaped HYPOTHESIS is the
pure-consequence obligation, in which `Q`, `CohG`,
`metaInterp`/`byteInterp` and `⊢` appear as the specification idiom
(definitions to read). Beneath it `project_triple` keeps that
obligation inside the post (strongest-post form). The proof is
`engine_adequacyU` + `stateInterp_readout` (the ONE open/close of the
state interpretation) + `spike_wp_wand`. The static fuel hypotheses
(`pot` bounds on the program and every registered body) are the
projection theorems' — the boring triples carry none (FUEL HONESTY,
static form). -/

/-- THE BORING TRIPLE WITH A MEMORY POSTCONDITION, at any machine
    context and entry environment: `SemTripleU` with the
    postcondition stated over the FINAL MEMORY (and given the rest
    footprint `R`, so the frame is part of the definition, not a
    separate rule): for every memory that splits as P ⊎ R — footprint
    P satisfied, rest R ARBITRARY — the engine's drive never kills or
    derails, and any delivered `(v, σ')` satisfies `post R v σ'`.
    `SemTripleU` is its instance at the cells-shaped post
    (`SemTripleU_iff_Mem`, definitional). Partial correctness; the
    drive length `n` is UNBOUNDED and the triple carries no fuel
    premise (the static `pot` bounds are the projection theorems'
    hypotheses). -/
def MemTripleU (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (post : CellMap → value → Mem → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), Sat M.tagDefs σ (Iris.Std.PartialMap.union P R) →
  ∀ (n : Nat) (aids : Nat → Nat),
    (∀ r, driveU M aids n (M.thread e ρ) σ ≠ .killed r) ∧
    (driveU M aids n (M.thread e ρ) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), driveU M aids n (M.thread e ρ) σ = .done v σ' →
      post R v σ')

/-- `SemTripleU` IS the memory-post triple at the cells-shaped
    postcondition (definitionally: the two unfold to the same
    proposition). -/
theorem SemTripleU_iff_Mem (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (post : value → CellMap → Prop) :
    SemTripleU M ρ e P post ↔
      MemTripleU M ρ e P (fun R v σ' => ∃ Q : CellMap, post v Q ∧ Q ##ₘ R ∧
        Sat M.tagDefs σ' (Iris.Std.PartialMap.union Q R)) :=
  Iff.rfl

/-- Interior: an assertion entails the pure fact "every ψ it
    pure-entails holds" (the pure-implication law, classical). -/
theorem consequences_intro {GF : BundledGFunctors} {Φ : IProp GF} {H : Prop → Prop}
    (h : ∀ ψ : Prop, H ψ → Φ ⊢ (⌜ψ⌝ : IProp GF)) :
    Φ ⊢ (⌜∀ ψ : Prop, H ψ → ψ⌝ : IProp GF) := by
  refine .trans ?_ BI.pure_forall.2
  refine BI.forall_intro fun ψ => ?_
  by_cases hH : H ψ
  · exact (h ψ hH).trans (BI.pure_mono fun hψ _ => hψ)
  · exact BI.pure_intro fun h' => absurd h' hH

/-- THE PROJECTION, STRONGEST-POST FORM: any Iris triple with a
    concrete-map precondition and an ARBITRARY Iris postcondition `Q`
    (over the logic's values, at any bundled ghost state) projects to
    the boring triple whose postcondition is every pure consequence
    of `Q w ∗ frame-cells` at the final memory, for every `w` erasing
    to the delivered value. `engine_adequacyU` + `stateInterp_readout`
    + `spike_wp_wand`; the well-formedness, fragment and static fuel
    hypotheses are `engine_adequacyU`'s, unchanged. The headline
    `project_triple_pure` below is derived from this. -/
theorem project_triple {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    {e : CoreExpr} (hfrag : Frag e) (hpot : pot e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        WP (⟨e, ev0 :: evs, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }}) :
    MemTripleU M (ev0 :: evs) e P (fun R v σ' => ∀ ψ : Prop,
      (∀ [SpikeGS .hasLC GF] (w : CoreRVal), w.val = v →
        ∀ (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
          (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
        iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
          metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ⌝ : IProp GF)) → ψ) := by
  intro R hdisj σ hsat n aids
  refine engine_adequacyU (GF := GF) hwf hQf hQpot e ev0 evs σ (Iris.Std.PartialMap.union P R)
    hfrag hpot hsat _ ?_ n aids
  intro instGS
  refine .trans (BigSepM.bigSepM_union hdisj).1 ?_
  iintro ⟨HP, HR⟩
  ihave HW := hwp $$ HP
  iapply spike_wp_wand $$ HW
  iintro %w HQ
  ihave HΦ : iprop(Q w ∗ ([∗map] i ↦ c ∈ R,
      cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) $$ [HQ HR]
  · isplitl [HQ]
    · iexact HQ
    · iexact HR
  iapply stateInterp_readout (fun σ' mm mb mk hG => consequences_intro fun ψ hH =>
    BI.sep_assoc.1.trans (hH w rfl mm mb mk hG)) $$ HΦ


/-- THE HEADLINE: THE BORING TRIPLE (professor review 1, required fix
    2). Any Iris triple with a concrete-map precondition and an
    ARBITRARY Iris postcondition `Q` projects to the boring triple
    `MemTripleU M ρ e P ψ` for a PURE `ψ : CellMap → value → Mem →
    Prop`, provided `Q w ∗ frame-cells` pure-entails `ψ R w.val σ'`
    against every coupling witness for the final memory σ'. The
    conclusion is engine vocabulary only: memory splits as P ⊎ R, the
    engine's drive (any length, any action-id supply) never kills or
    derails, and every delivered `(v, σ')` satisfies `ψ R v σ'`. The
    one Iris-shaped hypothesis `hpost` is discharged for the points-to
    shapes by the `*_consequence` lemmas below. Derived from the
    strongest-post form `project_triple`. -/
theorem project_triple_pure {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    {e : CoreExpr} (hfrag : Frag e) (hpot : pot e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (ψ : CellMap → value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        WP (⟨e, ev0 :: evs, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }})
    (hpost : ∀ [SpikeGS .hasLC GF] (w : CoreRVal) (R : CellMap) (σ' : Mem)
      (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
      (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
      iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ R w.val σ'⌝ : IProp GF)) :
    MemTripleU M (ev0 :: evs) e P ψ := by
  intro R hdisj σ hsat n aids
  have h := project_triple (GF := GF) hwf hQf hQpot hfrag hpot ev0 evs P Q hwp
    R hdisj σ hsat n aids
  refine ⟨h.1, h.2.1, fun v σ' hd => h.2.2 v σ' hd (ψ R v σ') ?_⟩
  intro _ w hw mm mb mk hG
  subst hw
  exact hpost w R σ' mm mb mk hG

/-! ## THE ALLOCATING PROJECTION (P6.1, review finding H-1)

`project_triple`'s precondition is footprint ownership ALONE, so a
client whose Iris precondition includes `allocCap` (every program
that `create`s) cannot reach `MemTripleU` through it. The allocating
projection below launches as `engine_adequacyU_alloc` does —
`launchResources` under `LaunchCoh`, the client's WP proof receiving
the footprint cells AND `allocCap reqs` — and concludes the boring
triple `MemTripleU_alloc`, whose ONLY difference from `MemTripleU` is
the launch precondition: `LaunchCoh M.tagDefs σ (P ∪ R) reqs` in
place of `Sat M.tagDefs σ (P ∪ R)`. The two genuinely differ:
`LaunchCoh` is `Sat` (its `coh` field) PLUS the allocator-health
facts the create rule's soundness needs — every id at or above the
engine's `nextAllocId` is unallocated and not dead, every footprint
cell sits at or above the downward cursor `lastAddress`, the request
plan fits the actual `⟨lastAddress, nextAllocId⟩`, and the cursor is
below `2^64` — none of which follows from `Sat` (a memory can carry
the footprint and still have its allocator cursor sitting on top of
those cells). The frame stays built into the definition (`R`
returned to the post), the post is the same "every pure consequence
of the Iris post" as `project_triple`'s, and `MemTripleU` implies
`MemTripleU_alloc` at every plan (`MemTripleU_alloc_of_MemTripleU`):
the allocating triple is the weaker conclusion, paid for by the
stronger launch premise. -/

/-- THE BORING TRIPLE WITH A MEMORY POSTCONDITION, LAUNCHED WITH AN
    ALLOCATION PLAN: `MemTripleU` with `Sat σ (P ∪ R)` replaced by
    `LaunchCoh M.tagDefs σ (P ∪ R) reqs` (footprint satisfied AND the
    allocator healthy with the plan `reqs` fitting the engine's own
    cursor). Frame built in (`R` arbitrary, returned to the post);
    partial correctness; the drive length is unbounded and no fuel
    premise is carried, as in `MemTripleU`. -/
def MemTripleU_alloc (M : MachineCtx) (ρ : EnvStack) (e : CoreExpr) (P : CellMap)
    (reqs : List AllocReq) (post : CellMap → value → Mem → Prop) : Prop :=
  ∀ (R : CellMap), P ##ₘ R →
  ∀ (σ : Mem), LaunchCoh M.tagDefs σ (Iris.Std.PartialMap.union P R) reqs →
  ∀ (n : Nat) (aids : Nat → Nat),
    (∀ r, driveU M aids n (M.thread e ρ) σ ≠ .killed r) ∧
    (driveU M aids n (M.thread e ρ) σ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem), driveU M aids n (M.thread e ρ) σ = .done v σ' →
      post R v σ')

/-- The non-allocating boring triple implies the allocating one at
    every plan: `LaunchCoh` contains `Sat` (its `coh` field), so a
    statement that needs no allocator health holds a fortiori under
    it. The converse fails (the launch premise is genuinely
    stronger). -/
theorem MemTripleU_alloc_of_MemTripleU {M : MachineCtx} {ρ : EnvStack} {e : CoreExpr}
    {P : CellMap} {post : CellMap → value → Mem → Prop}
    (h : MemTripleU M ρ e P post) (reqs : List AllocReq) :
    MemTripleU_alloc M ρ e P reqs post :=
  fun R hdisj σ hl n aids => h R hdisj σ hl.coh n aids

/-- THE ALLOCATING PROJECTION: any Iris triple whose precondition is
    footprint ownership plus the allocation capacity `allocCap reqs`,
    with an ARBITRARY Iris postcondition `Q`, projects to the boring
    triple `MemTripleU_alloc` whose postcondition is every pure
    consequence of `Q w ∗ frame-cells` at the final memory — the
    same post as `project_triple`'s. Proof: `engine_adequacyU_alloc`
    (the `launchResources` launch under `LaunchCoh`) +
    `stateInterp_readout` + `spike_wp_wand`; the well-formedness,
    fragment and static fuel hypotheses are `engine_adequacyU_alloc`'s,
    unchanged. Strongest-post form; `project_triple_pure_alloc` below
    is the boring headline derived from it. -/
theorem project_triple_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    {e : CoreExpr} (hfrag : Frag e) (hpot : pot e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (reqs : List AllocReq) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        allocCap M.tagDefs reqs) ⊢
        WP (⟨e, ev0 :: evs, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }}) :
    MemTripleU_alloc M (ev0 :: evs) e P reqs (fun R v σ' => ∀ ψ : Prop,
      (∀ [SpikeGS .hasLC GF] (w : CoreRVal), w.val = v →
        ∀ (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
          (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
        iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
          metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ⌝ : IProp GF)) → ψ) := by
  intro R hdisj σ hl n aids
  refine engine_adequacyU_alloc (GF := GF) hwf hQf hQpot e ev0 evs σ
    (Iris.Std.PartialMap.union P R) reqs hfrag hpot hl _ ?_ n aids
  intro instGS
  refine .trans (BI.sep_mono (BigSepM.bigSepM_union hdisj).1 .rfl) ?_
  iintro ⟨⟨HP, HR⟩, HC⟩
  ihave HW := hwp $$ [$HP $HC]
  iapply spike_wp_wand $$ HW
  iintro %w HQ
  ihave HΦ : iprop(Q w ∗ ([∗map] i ↦ c ∈ R,
      cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)) $$ [HQ HR]
  · isplitl [HQ]
    · iexact HQ
    · iexact HR
  iapply stateInterp_readout (fun σ' mm mb mk hG => consequences_intro fun ψ hH =>
    BI.sep_assoc.1.trans (hH w rfl mm mb mk hG)) $$ HΦ


/-- THE ALLOCATING HEADLINE: the boring triple for allocating clients
    (required fix 2, `_alloc` twin of `project_triple_pure`): an Iris
    triple whose precondition is footprint cells ∗ `allocCap reqs` and
    whose framed post pure-entails `ψ R w.val σ'` projects to
    `MemTripleU_alloc M ρ e P reqs ψ` — engine vocabulary only in the
    conclusion. Derived from `project_triple_alloc`. -/
theorem project_triple_pure_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    {e : CoreExpr} (hfrag : Frag e) (hpot : pot e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (P : CellMap) (reqs : List AllocReq) (Q : ∀ [SpikeGS .hasLC GF], CoreRVal → IProp GF)
    (ψ : CellMap → value → Mem → Prop)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ P, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        allocCap M.tagDefs reqs) ⊢
        WP (⟨e, ev0 :: evs, M⟩ : CoreRt) @ Stuckness.NotStuck; ⊤ {{ w, Q w }})
    (hpost : ∀ [SpikeGS .hasLC GF] (w : CoreRVal) (R : CellMap) (σ' : Mem)
      (mm : SpikeHeapF MetaCell) (mb : SpikeHeapF CerbMem.AbsByte)
      (mk : SpikeHeapF AllocCursor), CohG σ' mm mb mk →
      iprop(Q w ∗ ([∗map] i ↦ c ∈ R, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ R w.val σ'⌝ : IProp GF)) :
    MemTripleU_alloc M (ev0 :: evs) e P reqs ψ := by
  intro R hdisj σ hl n aids
  have h := project_triple_alloc (GF := GF) hwf hQf hQpot hfrag hpot ev0 evs P reqs Q hwp
    R hdisj σ hl n aids
  refine ⟨h.1, h.2.1, fun v σ' hd => h.2.2 v σ' hd (ψ R v σ') ?_⟩
  intro _ w hw mm mb mk hG
  subst hw
  exact hpost w R σ' mm mb mk hG

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

/-! ## The pure-consequence lemmas (the projection's obligations, discharged)

Shape: `Φ ∗ metaInterp mm ∗ byteInterp mb ⊢ ⌜<memory fact about σ>⌝`
under `CohG σ mm mb mk` — exactly the hypothesis `stateInterp_readout`
consumes and the obligation `project_triple`'s post states. One lemma
per assertion shape the exhibits' postconditions use (whole cell,
points-to, a cell footprint with a frame) and the `∗`/`∨`/`∃`/pure
combinators; the readouts below and the exhibits' readouts are
`stateInterp_readout` applied to compositions of these. -/

section Consequences

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}

/-- A pure conjunct is its own consequence. -/
theorem pure_consequence (φ : Prop) :
    iprop(⌜φ⌝ ∗ metaInterp (GF := GF) mm ∗ byteInterp mb) ⊢ (⌜φ⌝ : IProp GF) :=
  BI.sep_elim_left

/-- `∗`: pure conclusions are duplicable, so each conjunct reads out
    against the whole interpretation. -/
theorem sep_consequence {Φ₁ Φ₂ : IProp GF} {ψ₁ ψ₂ : Prop}
    (h₁ : iprop(Φ₁ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₁⌝ : IProp GF))
    (h₂ : iprop(Φ₂ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₂⌝ : IProp GF)) :
    iprop((Φ₁ ∗ Φ₂) ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₁ ∧ ψ₂⌝ : IProp GF) := by
  refine .trans (BI.and_intro ?_ ?_) BI.pure_and.1
  · exact (BI.sep_mono_left BI.sep_elim_left).trans h₁
  · exact (BI.sep_mono_left BI.sep_elim_right).trans h₂

/-- `∨`. -/
theorem or_consequence {Φ₁ Φ₂ : IProp GF} {ψ₁ ψ₂ : Prop}
    (h₁ : iprop(Φ₁ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₁⌝ : IProp GF))
    (h₂ : iprop(Φ₂ ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₂⌝ : IProp GF)) :
    iprop((Φ₁ ∨ Φ₂) ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ₁ ∨ ψ₂⌝ : IProp GF) :=
  BI.sep_or_right.1.trans ((BI.or_mono h₁ h₂).trans BI.pure_or.1)

/-- `∃`. -/
theorem exists_consequence {α : Type _} {Φ : α → IProp GF} {ψ : α → Prop}
    (h : ∀ a, iprop(Φ a ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜ψ a⌝ : IProp GF)) :
    iprop((∃ a, Φ a) ∗ metaInterp mm ∗ byteInterp mb) ⊢ (⌜∃ a, ψ a⌝ : IProp GF) :=
  BI.sep_exists_right.1.trans ((BI.exists_mono h).trans BI.pure_exists.1)

variable {σ : Mem} {mk : SpikeHeapF AllocCursor} (hG : CohG σ mm mb mk)
include hG

/-- Whole-cell ownership at ANY fraction: the cell's engine-facing
    backing facts hold of σ (`cellOwn_cellCoh`, Heap.lean). -/
theorem cellOwn_consequence (tds : CerbTags.TagDefsMap) (i : Int) (dq : DFrac) (c : SpikeCell) :
    iprop(cellOwn tds (GF := GF) i dq c ∗ metaInterp mm ∗ byteInterp mb) ⊢
      (⌜CellCoh tds σ i c⌝ : IProp GF) :=
  (BI.sep_comm.1.trans BI.sep_assoc.1).trans
    ((cellOwn_cellCoh tds hG i dq c).trans (BI.pure_mono And.left))

/-- Points-to: the pointer is the cell's `cellPtr`, and the cell's
    backing facts hold of σ. -/
theorem pointsToCell_consequence (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    (dq : DFrac) (ty : ctype) (bs : List CerbMem.AbsByte) :
    iprop(pointsToCell tds (GF := GF) pv dq ty bs ∗ metaInterp mm ∗ byteInterp mb) ⊢
      (⌜∃ i a, pv = cellPtr i a ∧ CellCoh tds σ i ⟨a, ty, bs⟩⌝ : IProp GF) := by
  refine (BI.sep_mono_left (pointsToCell_cellOwn_iff tds pv dq ty bs).1).trans ?_
  exact exists_consequence fun i => exists_consequence fun a =>
    sep_consequence (pure_consequence _) (cellOwn_consequence hG tds i dq _)

end Consequences

section ConsequencesCells

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]
variable {σ : Mem} {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
  {mk : SpikeHeapF AllocCursor} (hG : CohG σ mm mb mk)
include hG

/-- A footprint of whole cells: satisfaction (`cellsOwn_extract`
    reordered to the consequence shape). -/
theorem cellsOwn_consequence (tds : CerbTags.TagDefsMap) (Q : CellMap) :
    iprop(([∗map] i ↦ c ∈ Q, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c) ∗
        metaInterp mm ∗ byteInterp mb) ⊢ (⌜Coh tds σ Q⌝ : IProp GF) :=
  (BI.sep_comm.1.trans BI.sep_assoc.1).trans (cellsOwn_extract tds hG Q)

/-- The cells-shaped postcondition WITH a frame: the post-footprint is
    disjoint from the frame and their union is satisfied (the
    `SemTripleU` conclusion; the cross-disjointness comes from the
    metadata authority through `bigSepM_own_disjoint`). -/
theorem cells_consequence (tds : CerbTags.TagDefsMap)
    (post : value → CellMap → Prop) (R : CellMap) (vv : value) :
    iprop(((∃ Q : CellMap, ⌜post vv Q⌝ ∗
        ([∗map] i ↦ c ∈ Q, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) ∗
        ([∗map] i ↦ c ∈ R, cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c)) ∗
        metaInterp mm ∗ byteInterp mb) ⊢
      (⌜∃ Q : CellMap, post vv Q ∧ Q ##ₘ R ∧
        Coh tds σ (Iris.Std.PartialMap.union Q R)⌝ : IProp GF) := by
  iintro ⟨⟨⟨%Q, %hpost, HQ⟩, HR⟩, Hmi, Hbi⟩
  ihave %hd : ⌜Q ##ₘ R⌝ $$ [HQ HR]
  · iapply bigSepM_own_disjoint tds Q R $$ [$HQ $HR]
  ihave HQR : iprop([∗map] i ↦ c ∈ (Iris.Std.PartialMap.union Q R),
      cellOwn tds (hlc := .hasLC) (GF := GF) i (.own 1) c) $$ [HQ HR]
  · iapply (BigSepM.bigSepM_union hd).2 $$ [$HQ $HR]
  ihave %hsat : ⌜Coh tds σ (Iris.Std.PartialMap.union Q R)⌝ $$ [Hmi Hbi HQR]
  · iapply cellsOwn_consequence hG tds (Iris.Std.PartialMap.union Q R) $$ [$HQR $Hmi $Hbi]
  ipureintro
  exact ⟨Q, hpost, hd, hsat⟩

end ConsequencesCells

/-- THE SINGLE-CELL READOUT (alloc arc P4.1 — the public face of the
    coupling for whole-cell clients; the exhibits consume this instead
    of opening the state interpretation): whole-cell ownership at ANY
    fraction reads the cell's engine-facing backing facts off the
    final state. -/
theorem cellOwn_readout (tds : CerbTags.TagDefsMap) {hlc : HasLC} {GF : BundledGFunctors}
    [SpikeGS hlc GF] (i : Int) (dq : DFrac) (c : SpikeCell) :
    cellOwn tds (GF := GF) i dq c ⊢
      iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
        stateInterp σ' ns κs nt ={⊤, ∅}=∗ ⌜CellCoh tds σ' i c⌝) :=
  stateInterp_readout fun _ _ _ _ hG => cellOwn_consequence hG tds i dq c

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
          ⌜∃ Q : CellMap, post vv Q ∧ Q ##ₘ R ∧ Coh tds σ' (Iris.Std.PartialMap.union Q R)⌝) :=
  stateInterp_readout fun _ _ _ _ hG => cells_consequence hG tds post R vv

/-- THE HEADLINE AT ANY MACHINE CONTEXT (alloc arc P4.3): soundness of
    the derived logic's triples at the semantic level — a proved
    footprint triple at a well-formed context, with every registered
    label body in the fragment, holds of the ENGINE over every
    splitting configuration, from any cons-shaped entry environment.
    (`project_triple` at the cells-shaped post — `SemTripleU_iff_Mem` —
    with the obligation discharged by `cells_consequence`.) -/
theorem semantic_triple_soundU {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    {e : CoreExpr} (hfrag : Frag e) (hpot : pot e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    {P : CellMap} {post : value → CellMap → Prop}
    (hwp : ProvenTripleU GF M (ev0 :: evs) e P post) :
    SemTripleU M (ev0 :: evs) e P post := by
  -- the projection at the cells-shaped post, its obligation discharged
  -- by `cells_consequence`
  rw [SemTripleU_iff_Mem]
  intro R hdisj σ hsat n aids
  have h := project_triple (GF := GF) hwf hQf hQpot hfrag hpot ev0 evs P
    (fun w => iprop(∃ Q : CellMap, ⌜post (CoreRVal.val w) Q⌝ ∗
      ([∗map] i ↦ c ∈ Q, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)))
    hwp R hdisj σ hsat n aids
  refine ⟨h.1, h.2.1, fun v σ' hd => h.2.2 v σ' hd _ ?_⟩
  intro _ w hw mm mb mk hG
  subst hw
  exact BI.sep_assoc.2.trans (cells_consequence hG M.tagDefs post R w.val)

/-- THE FRAME RULE at the semantic level, at any machine context: a
    proved footprint triple substitutes into any larger context —
    ⦃P ∗ F⦄ e ⦃post ∗ F⦄, the frame F verbatim. -/
theorem semantic_frameU {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    {e : CoreExpr} (hfrag : Frag e) (hpot : pot e ≤ lemDefaultFuel)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    {P : CellMap} (F : CellMap)
    {post : value → CellMap → Prop} (hPF : P ##ₘ F)
    (hwp : ProvenTripleU GF M (ev0 :: evs) e P post) :
    SemTripleU M (ev0 :: evs) e (Iris.Std.PartialMap.union P F)
      (fun v Q => ∃ Q₀ : CellMap, post v Q₀ ∧ Q₀ ##ₘ F ∧
        Q = Iris.Std.PartialMap.union Q₀ F) := by
  refine semantic_triple_soundU (GF := GF) hwf hQf hQpot hfrag hpot ev0 evs ?_
  intro instGS
  refine .trans (BigSepM.bigSepM_union hPF).1 ?_
  iintro ⟨HP, HF⟩
  ihave HW := hwp $$ HP
  iapply spike_wp_wand $$ HW
  iintro %w HQex
  icases HQex with ⟨%Q₀, %hp, HQ⟩
  ihave %hd : ⌜Q₀ ##ₘ F⌝ $$ [HQ HF]
  · iapply bigSepM_own_disjoint M.tagDefs Q₀ F $$ [$HQ $HF]
  iexists (Iris.Std.PartialMap.union Q₀ F)
  isplit
  · ipureintro
    exact ⟨Q₀, hp, hd, rfl⟩
  · iapply (BigSepM.bigSepM_union hd).2
    isplitl [HQ]
    · iexact HQ
    · iexact HF

end
end CerberusHeapLang
