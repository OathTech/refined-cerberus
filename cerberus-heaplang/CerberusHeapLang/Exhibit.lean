/-
CerberusHeapLang.Exhibit — the straight-line end-to-end exhibits,
concluded AT THE ENGINE LEVEL via adequacy.

(a) store-then-load: on a concrete state seeded through the engine's
    own allocateObject, the engine's drive of
    `lets _ = store(x,7) in load(x)` delivers the stored integer —
    a THEOREM whose value fact flows from the proved WP through
    spike_engine_adequacy (the drive's termination step-count is by
    execution; the VALUE and SAFETY facts are by adequacy, not by
    evaluation).
(b) the frame exhibit, discharged end-to-end:
    {x ↦ - ∗ y ↦ a} store(x,7) {x ↦ 7 ∗ y ↦ a} (Rules.exhibit, built
    by FRAME on the store small axiom) lands as an engine fact: the
    drive of store(x,7) cannot kill, and afterwards the real
    MemState holds 7's bytes at x and y's bytes UNCHANGED — the
    frame's locality read back from the engine's bytemap.
(c) disjoint sequential stores: `lets _ = store(x,5) in store(y,6)`
    updates BOTH cells non-conflictingly — wp_store per leg, each
    framed with the other cell, glued by triple_seq.

The seeded state: two int-cells allocated from the empty MemState by
`CerbMem.allocateObject` (the engine's allocator, CerbMem.lean:1469).
All concrete facts (pointers, addresses, Coh) are closed
computations.
-/
import CerberusHeapLang.Adequacy

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open scoped Iris.Std.PartialMap

/-! ## The seeded initial state (through the engine's allocator) -/

/-- Two int objects, allocated by the engine from the empty state. -/
def seeded : Option ((CerbMem.PointerValue × CerbMem.PointerValue) × Mem) :=
  match applyMemM (CerbMem.allocateObject 0 (PrefOther "spike-x")
      (CerbMem.integerIval 4) intTy none none) ({} : Mem) with
  | some (x, σ1) =>
    match applyMemM (CerbMem.allocateObject 0 (PrefOther "spike-y")
        (CerbMem.integerIval 4) intTy none none) σ1 with
    | some (y, σ2) => some ((x, y), σ2)
    | none => none
  | none => none

/-- The seeded state (the proofs below pin it to the `some` arm). -/
def σ₀ : Mem :=
  match seeded with
  | some (_, σ) => σ
  | none => {}

def xPtr : CerbMem.PointerValue :=
  match seeded with
  | some ((x, _), _) => x
  | none => .PV .Prov_none (.PVnull intTy)

def yPtr : CerbMem.PointerValue :=
  match seeded with
  | some ((_, y), _) => y
  | none => .PV .Prov_none (.PVnull intTy)

/-- x's address: top-of-memory minus one aligned int (the engine
    allocates downward from its address ceiling —
    docs/2026-08-30_spike-recon.md §2.5). -/
def xAddr : Int := 281474976710648

def yAddr : Int := 281474976710644

theorem xPtr_eq : xPtr = cellPtr 0 xAddr := rfl

theorem yPtr_eq : yPtr = cellPtr 1 yAddr := rfl

/-! ## The initial cells and the coupling invariant -/

/-- x's (uninitialized) byte image in the seeded state. -/
abbrev bytesX : List CerbMem.AbsByte := CerbMem.readBytesFrom σ₀ xAddr 4

abbrev bytesY : List CerbMem.AbsByte := CerbMem.readBytesFrom σ₀ yAddr 4

abbrev cellX : SpikeCell := ⟨xAddr, intTy, bytesX⟩

abbrev cellY : SpikeCell := ⟨yAddr, intTy, bytesY⟩

/-- Ghost map for exhibit (a): x's cell only. -/
def mA : SpikeHeapF SpikeCell := Iris.Std.PartialMap.insert ∅ 0 cellX

/-- Ghost map for exhibit (b): both cells. -/
def mB : SpikeHeapF SpikeCell :=
  Iris.Std.PartialMap.insert (Iris.Std.PartialMap.insert ∅ 0 cellX) 1 cellY

/-- x's allocation record as `allocateObject` builds it
    (CerbMem.lean:1483-1487). Stated symbolically and related to σ₀
    by shallow record-projection rfl, so no Std.TreeMap internals are
    ever reduced definitionally. -/
def allocX : CerbMem.Allocation :=
  { base := xAddr, size := 4, ty := some intTy,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "spike-x") none,
    prefix_ := PrefOther "spike-x" }

def allocY : CerbMem.Allocation :=
  { base := yAddr, size := 4, ty := some intTy,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "spike-y") none,
    prefix_ := PrefOther "spike-y" }

theorem σ₀_allocations :
    σ₀.allocations =
      ((({} : Mem).allocations.insert 0 allocX).insert 1 allocY) := rfl

theorem alloc_get_x : σ₀.allocations.get? 0 = some allocX := by
  rw [σ₀_allocations]
  simp [Std.TreeMap.getElem_insert]

theorem alloc_get_y : σ₀.allocations.get? 1 = some allocY := by
  rw [σ₀_allocations]
  simp

theorem bytes_len (a : Int) : (CerbMem.readBytesFrom σ₀ a 4).length = 4 := by
  unfold CerbMem.readBytesFrom
  simp

/- The bytes/len clauses are staged through `sizeofCtype _ = 4` so
   the unifier never tries to force the (TreeMap-backed, not
   definitionally reducible) byte lists themselves. -/

theorem cellCohX : CellCoh σ₀ 0 cellX :=
  ⟨rfl, ⟨allocX, alloc_get_x, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype cellX.ty = 4 from rfl]; exact bytes_len xAddr,
   by rw [show CerbMem.sizeofCtype cellX.ty = 4 from rfl],
   fun _ _ => rfl⟩

theorem cellCohY : CellCoh σ₀ 1 cellY :=
  ⟨rfl, ⟨allocY, alloc_get_y, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype cellY.ty = 4 from rfl]; exact bytes_len yAddr,
   by rw [show CerbMem.sizeofCtype cellY.ty = 4 from rfl],
   fun _ _ => rfl⟩

theorem cells_disjoint : cellsDisjoint cellY cellX := by
  left
  show yAddr + (CerbMem.sizeofCtype intTy : Int) ≤ xAddr
  rw [show (CerbMem.sizeofCtype intTy : Int) = 4 from rfl]
  unfold yAddr xAddr
  omega

theorem coh_mB : Coh σ₀ mB := by
  refine ⟨?_, ?_⟩
  · intro id c h
    by_cases h1 : id = 1
    · subst h1
      rw [mB, Iris.Std.get?_insert_eq rfl] at h
      cases h
      exact cellCohY
    · rw [mB, Iris.Std.get?_insert_ne (fun h' => h1 h'.symm)] at h
      by_cases h0 : id = 0
      · subst h0
        rw [Iris.Std.get?_insert_eq rfl] at h
        cases h
        exact cellCohX
      · rw [Iris.Std.get?_insert_ne (fun h' => h0 h'.symm)] at h
        rw [Iris.Std.LawfulPartialMap.get?_empty] at h
        cases h
  · intro id1 id2 c1 c2 hne h1 h2
    have hget : ∀ id c, Iris.Std.PartialMap.get? mB id = some c →
        (id = 0 ∧ c = cellX) ∨ (id = 1 ∧ c = cellY) := by
      intro id c h
      by_cases ha : id = 1
      · subst ha
        rw [mB, Iris.Std.get?_insert_eq rfl] at h
        cases h
        exact .inr ⟨rfl, rfl⟩
      · rw [mB, Iris.Std.get?_insert_ne (fun h' => ha h'.symm)] at h
        by_cases hb : id = 0
        · subst hb
          rw [Iris.Std.get?_insert_eq rfl] at h
          cases h
          exact .inl ⟨rfl, rfl⟩
        · rw [Iris.Std.get?_insert_ne (fun h' => hb h'.symm),
            Iris.Std.LawfulPartialMap.get?_empty] at h
          cases h
    rcases hget id1 c1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hget id2 c2 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · exact Or.symm cells_disjoint
    · exact cells_disjoint
    · exact absurd rfl hne

theorem coh_mA : Coh σ₀ mA := by
  refine ⟨?_, ?_⟩
  · intro id c h
    by_cases h0 : id = 0
    · subst h0
      rw [mA, Iris.Std.get?_insert_eq rfl] at h
      cases h
      exact cellCohX
    · rw [mA, Iris.Std.get?_insert_ne (fun h' => h0 h'.symm),
        Iris.Std.LawfulPartialMap.get?_empty] at h
      cases h
  · intro id1 id2 c1 c2 hne h1 h2
    by_cases ha : id1 = 0
    · subst ha
      by_cases hb : id2 = 0
      · exact absurd hb.symm hne
      · rw [mA, Iris.Std.get?_insert_ne (fun h' => hb h'.symm),
          Iris.Std.LawfulPartialMap.get?_empty] at h2
        cases h2
    · rw [mA, Iris.Std.get?_insert_ne (fun h' => ha h'.symm),
        Iris.Std.LawfulPartialMap.get?_empty] at h1
      cases h1

/-! ## The programs -/

/-- The action location. `.unknown` (not `.other "spike"` as in the
    recon probe): `getFilename .unknown = none`, so the non-library
    side condition is definitional — `.other` maps to the
    "<internal>" filename whose path-split refutation is a String
    computation the kernel has no business grinding through. -/
def loc0 : CerbLocation.Loc := .unknown

theorem loc0_lib : CerbLocation.isLibraryLocation loc0 = false := rfl

/-- Exhibit (a): `lets _ = store(x,7) in load(x)`. -/
abbrev progA : CoreExpr :=
  sseqExpr BTy_unit (storeExpr loc0 empty_annotation intTy xPtr sevenVal NA)
    (loadExpr loc0 empty_annotation intTy xPtr NA)

/-- Exhibit (b): the operator's frame program, `store(x,7)`. -/
abbrev progB : CoreExpr := storeExpr loc0 empty_annotation intTy xPtr sevenVal NA

theorem fragA : FragP progA := FragP.sseq (.store loc0_lib) (.load loc0_lib)

theorem fragB : FragP progB := FragP.store loc0_lib

/-- The engine's decode of 7's byte image is 7 again (recon §2.8:
    exact round-trip for `integerIval`-written values). -/
theorem loaded_seven :
    loadedVal xPtr intTy (CerbMem.memValueToBytes [] sevenMval).2 = sevenVal := rfl

theorem htrap_seven :
    cellLoadTrap ⟨addrOf xPtr, intTy,
      (CerbMem.memValueToBytes [] sevenMval).2⟩ = false := rfl

/-! ## The precondition big-seps -/

variable {GF : BundledGFunctors}

theorem cellPtr_inj {i a j b : Int} (h : cellPtr i a = cellPtr j b) :
    i = j ∧ a = b := by
  unfold cellPtr at h
  injection h with h1 h2
  injection h1 with h1
  injection h2 with _ h2
  exact ⟨h1, h2⟩

theorem bigSepA_ptx [SpikeGS .hasLC GF] :
    iprop(([∗map] i ↦ c ∈ mA, pointsTo i (.own 1) c)) ⊢
      pointsToCell (GF := GF) xPtr (.own 1) intTy bytesX := by
  refine .trans (BigSepM.bigSepM_insert (i := 0) (x := cellX)
    (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0)).1 ?_
  iintro ⟨Hx, -⟩
  iapply (pointsToCell_iff _ _ _ _).mpr
  iexists 0, xAddr
  isplit
  · ipureintro
    exact xPtr_eq
  · iexact Hx

/-! ## The proved footprint triples (interior derivations:
small axioms + SEQ from slice A, ending in the ProvenTriple shape) -/

/-- x's cell after the store of 7. -/
abbrev cellX7 : SpikeCell :=
  ⟨xAddr, intTy, (CerbMem.memValueToBytes [] sevenMval).2⟩

/-- Post-footprint of the two programs: x's cell updated to 7. -/
abbrev mA7 : CellMap := Iris.Std.PartialMap.insert ∅ 0 cellX7

/-- The y-frame footprint. -/
abbrev mF : CellMap := Iris.Std.PartialMap.insert ∅ 1 cellY

theorem mA_disj_mF : mA ##ₘ mF := by
  rw [Iris.Std.PartialMap.disjoint_iff]
  intro k
  by_cases h0 : k = 0
  · subst h0
    right
    rw [mF, Iris.Std.get?_insert_ne (by omega : (1 : Int) ≠ 0)]
    exact Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0
  · left
    rw [mA, Iris.Std.get?_insert_ne (fun h => h0 h.symm)]
    exact Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) k

/-- Repackage the single x-cell as its footprint big-sep. -/
theorem ptx_to_cells [SpikeGS .hasLC GF] :
    iprop(pointsToCell (GF := GF) xPtr (.own 1) intTy
      (CerbMem.memValueToBytes [] sevenMval).2) ⊢
      iprop([∗map] i ↦ c ∈ mA7, pointsTo i (.own 1) c) := by
  iintro Hx
  icases (pointsToCell_iff _ _ _ _).mp $$ Hx with ⟨%ix, %ax, %Hpx, Hx⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj (xPtr_eq.symm.trans Hpx)
  iapply (BigSepM.bigSepM_insert
    (Φ := fun (i : Int) (c : SpikeCell) => pointsTo i (.own 1) c)
    (i := 0) (x := cellX7)
    (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0)).2
  isplitl [Hx]
  · iexact Hx
  · iapply (BigSepM.bigSepM_empty_intro
      (P := (BIBase.emp : IProp GF))
      (Φ := fun (i : Int) (c : SpikeCell) => pointsTo i (.own 1) c))
    itrivial

/-- The store's footprint triple, proved in the derived logic:
    ⦃x ↦ bytesX⦄ store(x,7) ⦃unit; x ↦ seven-bytes⦄. -/
theorem provenB {GF : BundledGFunctors} [SpikeGpreS GF] :
    ProvenTriple GF progB mA (fun v Q => v = Vunit ∧ Q = mA7) := by
  intro instGS
  refine bigSepA_ptx.trans ?_
  iintro Hx
  ihave HW := wp_store (s := Stuckness.NotStuck) (E := ⊤) loc0 empty_annotation
    intTy xPtr sevenVal NA sevenMval bytesX spikeEnv seven_encodes seven_storable $$ Hx
  iapply spike_wp_wand $$ HW
  iintro %v ⟨%fp, %hv, Hx⟩
  iexists mA7
  isplit
  · ipureintro
    subst hv
    exact ⟨rfl, rfl⟩
  · ihave HC := ptx_to_cells $$ Hx
    iexact HC

/-- The store-then-load footprint triple:
    ⦃x ↦ bytesX⦄ lets _ = store(x,7) in load(x) ⦃Specified 7; x ↦ seven-bytes⦄. -/
theorem provenA {GF : BundledGFunctors} [SpikeGpreS GF] :
    ProvenTriple GF progA mA (fun v Q => v = sevenVal ∧ Q = mA7) := by
  intro instGS
  refine bigSepA_ptx.trans (.trans ?_ (wp_sseq [] [] BTy_unit _ _ fmapEmpty []))
  iintro Hx
  ihave HW := wp_store (s := Stuckness.NotStuck) (E := ⊤) loc0 empty_annotation
    intTy xPtr sevenVal NA sevenMval bytesX spikeEnv seven_encodes seven_storable $$ Hx
  iapply spike_wp_wand $$ HW
  iintro %v ⟨%fp, %hv, Hx⟩
  subst hv
  iapply BI.later_intro
  ihave HW2 := wp_load (s := Stuckness.NotStuck) (E := ⊤) loc0 empty_annotation
    intTy xPtr NA (.own 1) (CerbMem.memValueToBytes [] sevenMval).2 spikeEnv
    htrap_seven $$ Hx
  iapply spike_wp_wand $$ HW2
  iintro %w ⟨%fp2, %hw, Hx⟩
  iexists mA7
  isplit
  · ipureintro
    subst hw
    refine ⟨?_, rfl⟩
    simp only [mergeInto, CoreRVal.val, CoreRVal.merge_mk, SpikeVal.val_merge]
    exact loaded_seven
  · ihave HC := ptx_to_cells $$ Hx
    iexact HC

/-! ## THE EXHIBITS: the semantic triples, and their instances at the
seeded engine state -/

/-- EXHIBIT (a) AS A SEMANTIC TRIPLE: over EVERY engine configuration
    splitting as (x-cell) ⊎ rest, the drive of
    `lets _ = store(x,7) in load(x)` cannot kill or derail, and any
    delivered value is Specified(7) with x's cell updated and the
    rest verbatim. -/
theorem exhibitA_semantic {GF : BundledGFunctors} [SpikeGpreS GF] :
    SemTriple progA mA (fun v Q => v = sevenVal ∧ Q = mA7) :=
  semantic_triple_sound (GF := GF) fragA provenA

/-- EXHIBIT (b), the operator's FRAME EXHIBIT at the semantic level:
    the store's x-footprint triple, framed by y's cell —
    ⦃x ↦ - ∗ y ↦ a⦄ store(x,7) ⦃x ↦ 7 ∗ y ↦ a⦄ over engine
    configurations, y (and all unnamed rest) verbatim. -/
theorem exhibitB_semantic {GF : BundledGFunctors} [SpikeGpreS GF] :
    SemTriple progB (Iris.Std.PartialMap.union mA mF)
      (fun v Q => ∃ Q₀, (v = Vunit ∧ Q₀ = mA7) ∧ Q₀ ##ₘ mF ∧
        Q = Iris.Std.PartialMap.union Q₀ mF) :=
  semantic_frame (GF := GF) fragB mF mA_disj_mF provenB

/-- Exhibit (a) at the seeded engine instance (rest := ∅). -/
theorem exhibitA_engine (n : Nat) (aids : Nat → Nat) (hn : n ≤ 999998) :
    (∀ r, drive aids n (spikeThread progA) σ₀ ≠ .killed r) ∧
    (drive aids n (spikeThread progA) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      drive aids n (spikeThread progA) σ₀ = .done v σ' → v = sevenVal) := by
  have h := exhibitA_semantic (GF := SpikeGF) ∅
    (Iris.Std.LawfulPartialMap.disjoint_empty_right mA) σ₀
    (by rw [show Iris.Std.PartialMap.union mA ∅ = mA from
        Iris.Std.LawfulPartialMap.union_empty_right]
        exact coh_mA)
    n aids
    (by rw [show esize progA = 2 from rfl]; unfold lemDefaultFuel; omega)
  refine ⟨h.1, h.2.1, fun v σ' hd => ?_⟩
  obtain ⟨Q, ⟨hv, _⟩, _, _⟩ := h.2.2 v σ' hd
  exact hv

/-- Exhibit (b) at the seeded engine instance: after the store, the
    engine's bytemap holds 7's image at x and y's bytes UNCHANGED —
    frame locality read back from the real memory. -/
theorem exhibitB_engine (n : Nat) (aids : Nat → Nat) (hn : n ≤ 999999) :
    (∀ r, drive aids n (spikeThread progB) σ₀ ≠ .killed r) ∧
    (drive aids n (spikeThread progB) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      drive aids n (spikeThread progB) σ₀ = .done v σ' →
        v = Vunit ∧
        CerbMem.readBytesFrom σ' xAddr 4 =
          (CerbMem.memValueToBytes [] sevenMval).2 ∧
        CerbMem.readBytesFrom σ' yAddr 4 = bytesY) := by
  have hcohBu : Sat σ₀ (Iris.Std.PartialMap.union
      (Iris.Std.PartialMap.union mA mF) ∅) := by
    rw [show Iris.Std.PartialMap.union (Iris.Std.PartialMap.union mA mF) ∅ =
        Iris.Std.PartialMap.union mA mF from
      Iris.Std.LawfulPartialMap.union_empty_right]
    refine ⟨?_, ?_⟩
    · intro id c h
      rw [show Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union mA mF) id =
          (Iris.Std.PartialMap.get? mA id).orElse
            (fun _ => Iris.Std.PartialMap.get? mF id) from
        Iris.Std.LawfulPartialMap.get?_union] at h
      by_cases h0 : id = 0
      · subst h0
        rw [mA, Iris.Std.get?_insert_eq rfl] at h
        cases h
        exact cellCohX
      · rw [mA, Iris.Std.get?_insert_ne (fun h' => h0 h'.symm),
          Iris.Std.LawfulPartialMap.get?_empty] at h
        simp only [Option.orElse] at h
        by_cases h1 : id = 1
        · subst h1
          rw [mF, Iris.Std.get?_insert_eq rfl] at h
          cases h
          exact cellCohY
        · rw [mF, Iris.Std.get?_insert_ne (fun h' => h1 h'.symm),
            Iris.Std.LawfulPartialMap.get?_empty] at h
          cases h
    · intro id1 id2 c1 c2 hne h1 h2
      have hget : ∀ id c, Iris.Std.PartialMap.get?
          (Iris.Std.PartialMap.union mA mF) id = some c →
          (id = 0 ∧ c = cellX) ∨ (id = 1 ∧ c = cellY) := by
        intro id c h
        rw [show Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union mA mF) id =
            (Iris.Std.PartialMap.get? mA id).orElse
              (fun _ => Iris.Std.PartialMap.get? mF id) from
          Iris.Std.LawfulPartialMap.get?_union] at h
        by_cases h0 : id = 0
        · subst h0
          rw [mA, Iris.Std.get?_insert_eq rfl] at h
          cases h
          exact .inl ⟨rfl, rfl⟩
        · rw [mA, Iris.Std.get?_insert_ne (fun h' => h0 h'.symm),
            Iris.Std.LawfulPartialMap.get?_empty] at h
          simp only [Option.orElse] at h
          by_cases h1 : id = 1
          · subst h1
            rw [mF, Iris.Std.get?_insert_eq rfl] at h
            cases h
            exact .inr ⟨rfl, rfl⟩
          · rw [mF, Iris.Std.get?_insert_ne (fun h' => h1 h'.symm),
              Iris.Std.LawfulPartialMap.get?_empty] at h
            cases h
      rcases hget id1 c1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases hget id2 c2 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hne
      · exact Or.symm cells_disjoint
      · exact cells_disjoint
      · exact absurd rfl hne
  have h := exhibitB_semantic (GF := SpikeGF) ∅
    (Iris.Std.LawfulPartialMap.disjoint_empty_right _) σ₀ hcohBu n aids
    (by rw [show esize progB = 1 from rfl]; unfold lemDefaultFuel; omega)
  refine ⟨h.1, h.2.1, fun v σ' hd => ?_⟩
  obtain ⟨Q, ⟨Q₀, ⟨hv, hQ0⟩, hdisj, hQ⟩, _, hsat⟩ := h.2.2 v σ' hd
  subst hQ0 hQ
  have hsat' : Sat σ' (Iris.Std.PartialMap.union mA7 mF) :=
    Sat.mono hsat (by
      rw [show Iris.Std.PartialMap.union
          (Iris.Std.PartialMap.union mA7 mF) ∅ =
          Iris.Std.PartialMap.union mA7 mF from
        Iris.Std.LawfulPartialMap.union_empty_right])
  have hgx : Iris.Std.PartialMap.get?
      (Iris.Std.PartialMap.union mA7 mF) 0 = some cellX7 := by
    rw [show Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union mA7 mF) 0 =
        (Iris.Std.PartialMap.get? mA7 0).orElse
          (fun _ => Iris.Std.PartialMap.get? mF 0) from
      Iris.Std.LawfulPartialMap.get?_union, mA7, Iris.Std.get?_insert_eq rfl]
    rfl
  have hgy : Iris.Std.PartialMap.get?
      (Iris.Std.PartialMap.union mA7 mF) 1 = some cellY := by
    rw [show Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union mA7 mF) 1 =
        (Iris.Std.PartialMap.get? mA7 1).orElse
          (fun _ => Iris.Std.PartialMap.get? mF 1) from
      Iris.Std.LawfulPartialMap.get?_union, mA7,
      Iris.Std.get?_insert_ne (by omega : (0 : Int) ≠ 1),
      Iris.Std.LawfulPartialMap.get?_empty]
    simp only [Option.orElse]
    rw [mF, Iris.Std.get?_insert_eq rfl]
  have hcx := (hsat'.cells 0 _ hgx).bytes
  have hcy := (hsat'.cells 1 _ hgy).bytes
  rw [show CerbMem.sizeofCtype intTy = 4 from rfl] at hcx hcy
  exact ⟨hv, hcx, hcy⟩

/-! ## Termination of exhibit (a): the drive actually delivers

The recon probe as a theorem: six drive steps reach PROGRAM-DONE.
(Adequacy gives safety and pins the value; this simulation, built
from the same per-rule certification lemmas, adds termination.) -/

/-- The state after the store. -/
def σ₁ : Mem :=
  CerbMem.writeBytesTo σ₀ xAddr (CerbMem.memValueToBytes [] sevenMval).2

theorem drive_next {aids : Nat → Nat} {n : Nat} {th th' : thread_state}
    {σ σ' : Mem}
    (h : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
      (dischargeStep (aids 0) spikeRunState σ) = [.next th' σ']) :
    drive aids (n+1) th σ = drive (fun i => aids (i+1)) n th' σ' := by
  rw [drive.eq_def]
  dsimp only
  rw [h]

theorem drive_done {aids : Nat → Nat} {n : Nat} {th : thread_state} {σ : Mem}
    {v : value}
    (h : (step_ctx fmapEmpty σ spikeFile fmapEmpty 0 (none, th)).map
      (dischargeStep (aids 0) spikeRunState σ) = [.done v]) :
    drive aids (n+1) th σ = .done v σ := by
  rw [drive.eq_def]
  dsimp only
  rw [h]

/-- The store's footprint / the load's footprint. -/
def fpS : CerbMem.Footprint := .FP .W xAddr 4
def fpL : CerbMem.Footprint := .FP .R xAddr 4

/-- store discharges actively on the seeded state (the memM building
    block from slice A, instantiated). -/
theorem store_applies :
    applyMemM (CerbMem.storeM loc0 intTy false xPtr sevenMval) σ₀ =
      some (fpS, σ₁) :=
  storeM_success σ₀ 0 cellX sevenMval loc0 cellCohX seven_storable

/-- Coh survives the store (slice A's Coh.store, instantiated). -/
theorem coh_after_store :
    Coh σ₁ (Iris.Std.PartialMap.insert mA 0
      ⟨xAddr, intTy, (CerbMem.memValueToBytes [] sevenMval).2⟩) :=
  Coh.store σ₀ mA 0 cellX sevenMval coh_mA (Iris.Std.get?_insert_eq rfl)
    seven_storable

theorem load_applies :
    applyMemM (CerbMem.loadM loc0 intTy xPtr) σ₁ =
      some ((fpL, decodeCell ⟨xAddr, intTy,
        (CerbMem.memValueToBytes [] sevenMval).2⟩), σ₁) :=
  loadM_success σ₁ 0 ⟨xAddr, intTy, (CerbMem.memValueToBytes [] sevenMval).2⟩
    loc0 (coh_after_store.cells 0 _ (Iris.Std.get?_insert_eq rfl))
    htrap_seven

/-- The intermediate arenas. -/
def eA1 : CoreExpr :=
  Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [] (Eannot [DA_pos [] fpS]
      (Expr [] (Epure (Pexpr [] () (PEval Vunit))))))
    (loadExpr loc0 empty_annotation intTy xPtr NA))

def eA2 : CoreExpr :=
  Expr [] (Eannot [DA_pos [] fpS] (loadExpr loc0 empty_annotation intTy xPtr NA))

def eA3 : CoreExpr :=
  Expr [] (Eannot [DA_pos [] fpS] (Expr [] (Eannot [DA_pos [] fpL]
    (Expr [] (Epure (Pexpr [] () (PEval sevenVal)))))))

/-- THE PROBE, AS A THEOREM: six engine steps from the seeded state
    end in the engine delivering `Specified(7)` (with adequacy's
    exhibitA_engine pinning that this is the only possible delivery
    and that no drive of any length can kill). -/
theorem exhibitA_terminates (aids : Nat → Nat) :
    drive aids 6 (spikeThread progA) σ₀ = .done sevenVal σ₁ := by
  -- step 1: the store request, discharged against storeM
  rw [drive_next (th' := spikeThread eA1) (σ' := σ₁) ?s1]
  case s1 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_store
      (Decomp.toJ (Decomp.sseq (pa := []) (bty := BTy_unit)
        (e2 := loadExpr loc0 empty_annotation intTy xPtr NA)
        (Decomp.root (Redex.store (loc := loc0) (ann := empty_annotation)
          (lk := false) (ty := intTy) (pv := xPtr) (cv := sevenVal)
          (mo := NA) loc0_lib))))
      (by decide) loc0_lib seven_encodes spikeEnv σ₀
    rw [show engineSteps progA spikeEnv σ₀ = _ from hE]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_store_active store_applies]
    rfl
  -- step 2: LETS-ANNOT
  rw [drive_next (th' := spikeThread eA2) (σ' := σ₁) ?s2]
  case s2 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_beta_annot (pa := []) (bty := BTy_unit)
      (ds := [DA_pos [] fpS]) (v := Vunit)
      (e2 := loadExpr loc0 empty_annotation intTy xPtr NA)
      (Decomp.toJ (Decomp.root Redex.beta_annot)) (by decide) fmapEmpty [] σ₁
    rw [show engineSteps eA1 spikeEnv σ₁ = _ from hE]
    rfl
  -- step 3: the load request, discharged against loadM
  rw [drive_next (th' := spikeThread eA3) (σ' := σ₁) ?s3]
  case s3 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_load
      (Decomp.toJ (Decomp.annot (ds := [DA_pos [] fpS]) rfl rfl (fun n => rfl)
        (Decomp.root (Redex.load (loc := loc0) (ann := empty_annotation)
          (ty := intTy) (pv := xPtr) (mo := NA) loc0_lib))))
      (by decide) loc0_lib spikeEnv σ₁
    rw [show engineSteps eA2 spikeEnv σ₁ = _ from hE]
    simp only [List.map_cons, List.map_nil]
    rw [dischargeStep_load_active load_applies]
    rfl
  -- step 4: ANNOTS merge
  rw [drive_next
    (th' := spikeThread (ofVal (.annot [DA_pos [] fpS, DA_pos [] fpL] sevenVal)))
    (σ' := σ₁) ?s4]
  case s4 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    have hE := engineSteps_merge (ds1 := [DA_pos [] fpS])
      (ds2 := [DA_pos [] fpL])
      (Decomp.toJ (Decomp.root (Redex.merge
        (b := Expr [] (Epure (Pexpr [] () (PEval sevenVal)))) rfl)))
      rfl (by decide) spikeEnv σ₁
    rw [show engineSteps eA3 spikeEnv σ₁ = _ from hE]
    rfl
  -- step 5: REMOVE-ANNOT
  rw [drive_next (th' := spikeThread (ofVal (.pure sevenVal))) (σ' := σ₁) ?s5]
  case s5 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    rw [engineSteps_remove_annot]
    rfl
  -- step 6: PROGRAM-DONE
  rw [drive_done ?s6]
  case s6 =>
    rw [drive_scrutinee]
    unfold engineOutcomes
    rw [engineSteps_done]
    rfl

/-! ## EXHIBIT C ([USER 2026-08-30]): disjoint sequential stores,
exported to the engine level

`lets _ = store(x,5) in store(y,6)` on the two seeded cells. The
interior derivation is `exhibitC_triple` (Rules.lean) — wp_store per
leg FRAMED with the other cell, glued by triple_seq; the export
below only repackages its footprint form through
`semantic_triple_sound`. The postcondition carries NO value clause:
`triple_seq`'s assertion-postcondition form (deliberately, the
wildcard-binding fragment shape) discards the delivered value, and
re-deriving it monolithically would defeat the exhibit's point —
the update facts are the content. -/

/-- Exhibit (c): `lets _ = store(x,5) in store(y,6)`, x/y the two
    seeded disjoint cells. -/
abbrev progC : CoreExpr :=
  sseqExpr BTy_unit (storeExpr loc0 empty_annotation intTy xPtr fiveVal NA)
    (storeExpr loc0 empty_annotation intTy yPtr sixVal NA)

theorem fragC : FragP progC := FragP.sseq (.store loc0_lib) (.store loc0_lib)

/-- The two cells after the two stores. -/
abbrev cellX5 : SpikeCell := ⟨xAddr, intTy, fiveBytes⟩

abbrev cellY6 : SpikeCell := ⟨yAddr, intTy, sixBytes⟩

/-- Post-footprint of progC: BOTH cells updated, non-conflictingly. -/
abbrev mC : CellMap :=
  Iris.Std.PartialMap.insert (Iris.Std.PartialMap.insert ∅ 0 cellX5) 1 cellY6

theorem mB_base_get1 :
    Iris.Std.PartialMap.get?
      (Iris.Std.PartialMap.insert (∅ : CellMap) 0 cellX) 1 = none := by
  rw [Iris.Std.get?_insert_ne (by omega : (0 : Int) ≠ 1)]
  exact Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 1

theorem mC_base_get1 :
    Iris.Std.PartialMap.get?
      (Iris.Std.PartialMap.insert (∅ : CellMap) 0 cellX5) 1 = none := by
  rw [Iris.Std.get?_insert_ne (by omega : (0 : Int) ≠ 1)]
  exact Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 1

/-- Unpack mB's big-sep into the two pointer-shaped cells. -/
theorem bigSepB_pts [SpikeGS .hasLC GF] :
    iprop(([∗map] i ↦ c ∈ mB, pointsTo i (.own 1) c)) ⊢
      iprop(pointsToCell (GF := GF) xPtr (.own 1) intTy bytesX ∗
        pointsToCell yPtr (.own 1) intTy bytesY) := by
  refine .trans (BigSepM.bigSepM_insert (i := 1) (x := cellY) mB_base_get1).1 ?_
  iintro ⟨Hy, Hbase⟩
  icases (BigSepM.bigSepM_insert (i := 0) (x := cellX)
    (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0)).1
    $$ Hbase with ⟨Hx, -⟩
  isplitl [Hx]
  · iapply (pointsToCell_iff _ _ _ _).mpr
    iexists 0, xAddr
    isplit
    · ipureintro
      exact xPtr_eq
    · iexact Hx
  · iapply (pointsToCell_iff _ _ _ _).mpr
    iexists 1, yAddr
    isplit
    · ipureintro
      exact yPtr_eq
    · iexact Hy

/-- Repackage the two updated cells as mC's big-sep. -/
theorem cells_to_mC [SpikeGS .hasLC GF] :
    iprop(pointsToCell (GF := GF) xPtr (.own 1) intTy fiveBytes ∗
      pointsToCell yPtr (.own 1) intTy sixBytes) ⊢
      iprop([∗map] i ↦ c ∈ mC, pointsTo i (.own 1) c) := by
  iintro ⟨Hx, Hy⟩
  icases (pointsToCell_iff _ _ _ _).mp $$ Hx with ⟨%ix, %ax, %Hpx, Hx⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj (xPtr_eq.symm.trans Hpx)
  icases (pointsToCell_iff _ _ _ _).mp $$ Hy with ⟨%iy, %ay, %Hpy, Hy⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj (yPtr_eq.symm.trans Hpy)
  iapply (BigSepM.bigSepM_insert
    (Φ := fun (i : Int) (c : SpikeCell) => pointsTo i (.own 1) c)
    (i := 1) (x := cellY6) mC_base_get1).2
  isplitl [Hy]
  · iexact Hy
  · iapply (BigSepM.bigSepM_insert
      (Φ := fun (i : Int) (c : SpikeCell) => pointsTo i (.own 1) c)
      (i := 0) (x := cellX5)
      (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0)).2
    isplitl [Hx]
    · iexact Hx
    · iapply (BigSepM.bigSepM_empty_intro
        (P := (BIBase.emp : IProp GF))
        (Φ := fun (i : Int) (c : SpikeCell) => pointsTo i (.own 1) c))
      itrivial

/-- The two-store footprint triple: the interior compositional
    derivation `exhibitC_triple` repackaged at footprint granularity
    — no re-derivation, only big-sep ↔ pointsToCell plumbing. -/
theorem provenC {GF : BundledGFunctors} [SpikeGpreS GF] :
    ProvenTriple GF progC mB (fun _ Q => Q = mC) := by
  intro instGS
  refine bigSepB_pts.trans ((exhibitC_triple xPtr yPtr loc0 loc0
    empty_annotation empty_annotation NA NA BTy_unit bytesX bytesY).trans ?_)
  apply wp_mono
  intro v
  iintro ⟨Hx, Hy⟩
  iexists mC
  isplit
  · ipureintro
    rfl
  · iapply cells_to_mC
    isplitl [Hx]
    · iexact Hx
    · iexact Hy

/-- EXHIBIT (c) AS A SEMANTIC TRIPLE: over EVERY engine configuration
    splitting as (x-cell ∗ y-cell) ⊎ R — the frame R ARBITRARY — the
    drive of `lets _ = store(x,5) in store(y,6)` cannot kill or
    derail, and any completed run updates BOTH cells (x to 5's bytes,
    y to 6's bytes) with R verbatim: the two stores do not conflict. -/
theorem exhibitC_semantic {GF : BundledGFunctors} [SpikeGpreS GF] :
    SemTriple progC mB (fun _ Q => Q = mC) :=
  semantic_triple_sound (GF := GF) fragC provenC

/-- Exhibit (c) at the seeded engine instance (rest := ∅): after the
    two stores, the engine's bytemap holds 5's image at x AND 6's
    image at y — the non-conflicting update read back from the real
    memory. -/
theorem exhibitC_engine (n : Nat) (aids : Nat → Nat) (hn : n ≤ 999998) :
    (∀ r, drive aids n (spikeThread progC) σ₀ ≠ .killed r) ∧
    (drive aids n (spikeThread progC) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      drive aids n (spikeThread progC) σ₀ = .done v σ' →
        CerbMem.readBytesFrom σ' xAddr 4 = fiveBytes ∧
        CerbMem.readBytesFrom σ' yAddr 4 = sixBytes) := by
  have h := exhibitC_semantic (GF := SpikeGF) ∅
    (Iris.Std.LawfulPartialMap.disjoint_empty_right mB) σ₀
    (by rw [show Iris.Std.PartialMap.union mB ∅ = mB from
        Iris.Std.LawfulPartialMap.union_empty_right]
        exact coh_mB)
    n aids
    (by rw [show esize progC = 2 from rfl]; unfold lemDefaultFuel; omega)
  refine ⟨h.1, h.2.1, fun v σ' hd => ?_⟩
  obtain ⟨Q, hQ, _, hsat⟩ := h.2.2 v σ' hd
  subst hQ
  have hsat' : Sat σ' mC :=
    Sat.mono hsat (by
      rw [show Iris.Std.PartialMap.union mC ∅ = mC from
        Iris.Std.LawfulPartialMap.union_empty_right])
  have hgx : Iris.Std.PartialMap.get? mC 0 = some cellX5 := by
    rw [show Iris.Std.PartialMap.get? mC 0 =
        Iris.Std.PartialMap.get?
          (Iris.Std.PartialMap.insert (∅ : CellMap) 0 cellX5) 0 from
      Iris.Std.get?_insert_ne (by omega : (1 : Int) ≠ 0)]
    exact Iris.Std.get?_insert_eq rfl
  have hgy : Iris.Std.PartialMap.get? mC 1 = some cellY6 :=
    Iris.Std.get?_insert_eq rfl
  have hcx := (hsat'.cells 0 _ hgx).bytes
  have hcy := (hsat'.cells 1 _ hgy).bytes
  rw [show CerbMem.sizeofCtype intTy = 4 from rfl] at hcx hcy
  exact ⟨hcx, hcy⟩

end CerberusHeapLang
