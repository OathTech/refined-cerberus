/-
CerberusHeapLang.Exhibit — the straight-line end-to-end exhibits,
concluded AT THE ENGINE LEVEL via adequacy.

(a) store-then-load: on a concrete state seeded through the engine's
    own allocateObject, the engine's drive of
    `lets _ = store(x,7) in load(x)` delivers the stored integer —
    a THEOREM whose value fact flows from the proved WP through
    `engine_adequacy` (the VALUE and SAFETY facts are by adequacy, not
    by evaluation; the referent is the shipped driver's per-thread loop
    at every fuel, `DriverSafeCtl`).
(b) the frame exhibit, discharged end-to-end:
    {x ↦ - ∗ y ↦ a} store(x,7) {x ↦ 7 ∗ y ↦ a} (`wps_exhibit_store_frame`,
    Examples/Layout.lean, built by FRAME on the store small axiom)
    lands as an engine fact: the drive of store(x,7) cannot kill, and
    afterwards the real MemState holds 7's bytes at x and y's bytes
    UNCHANGED — the frame's locality read back from the engine's
    bytemap.
(c) disjoint sequential stores: `lets _ = store(x,5) in store(y,6)`
    updates BOTH cells non-conflictingly — the store small axiom per
    leg, glued by the sequencing rule (`wps_exhibit_seq_stores`).

The interior derivations: (b)'s `provenB` is the raw-WP small axiom
`wp_store` directly; (a)'s `provenA` and (c)'s `provenC` are
statement-stratum derivations (`wps_seq`/`wps_store`/`wps_load`,
resp. `wps_exhibit_seq_stores`) collapsed into the base WP by
`wps_sound` at the vacuous label context — the one route every other
exhibit takes.

The seeded state: two int-cells allocated from the empty MemState by
`CerbMem.allocateObject` (the engine's allocator, CerbMem.lean:1469).
All concrete facts (pointers, addresses, Coh) are closed
computations.
-/
import CerberusHeapLang.API
import CerberusHeapLang.Examples.Layout

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open scoped Iris.Std.PartialMap

/-! ## The seeded initial state (through the engine's allocator) -/

/-- Two int objects, allocated by the engine from the empty state. -/
def seeded : Option ((CerbMem.PointerValue × CerbMem.PointerValue) × Mem) :=
  match applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "spike-x")
      (CerbMem.integerIval 4) intTy none none) ({} : Mem) with
  | some (x, σ1) =>
    match applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "spike-y")
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

/- The bytes/len clauses are staged through `sizeofCtype tds _ = 4` so
   the unifier never tries to force the (TreeMap-backed, not
   definitionally reducible) byte lists themselves. -/

theorem cellCohX : CellCoh fmapEmpty σ₀ 0 cellX :=
  ⟨rfl, ⟨allocX, alloc_get_x, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype fmapEmpty cellX.ty = 4 from rfl]; exact bytes_len xAddr,
   by rw [show CerbMem.sizeofCtype fmapEmpty cellX.ty = 4 from rfl],
   fun _ _ => rfl⟩

theorem cellCohY : CellCoh fmapEmpty σ₀ 1 cellY :=
  ⟨rfl, ⟨allocY, alloc_get_y, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype fmapEmpty cellY.ty = 4 from rfl]; exact bytes_len yAddr,
   by rw [show CerbMem.sizeofCtype fmapEmpty cellY.ty = 4 from rfl],
   fun _ _ => rfl⟩

theorem cells_disjoint : cellsDisjoint fmapEmpty cellY cellX := by
  left
  show yAddr + (CerbMem.sizeofCtype fmapEmpty intTy : Int) ≤ xAddr
  rw [show (CerbMem.sizeofCtype fmapEmpty intTy : Int) = 4 from rfl]
  unfold yAddr xAddr
  omega

theorem coh_mB : Coh fmapEmpty σ₀ mB := by
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

theorem coh_mA : Coh fmapEmpty σ₀ mA := by
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

/-- Exhibit (a): `lets _ = store(x,7) in load(x)`. -/
abbrev progA : CoreExpr :=
  sseqExpr BTy_unit (storeExpr loc0 empty_annotation intTy xPtr sevenVal NA)
    (loadExpr loc0 empty_annotation intTy xPtr NA)

/-- Exhibit (b): the operator's frame program, `store(x,7)`. -/
abbrev progB : CoreExpr := storeExpr loc0 empty_annotation intTy xPtr sevenVal NA

theorem fragA : Frag progA := Frag.sseq (.store) (.load)

theorem fragB : Frag progB := Frag.store

/-- The engine's decode of 7's byte image is 7 again (recon §2.8:
    exact round-trip for `integerIval`-written values). -/
theorem loaded_seven {tds : CerbTags.TagDefsMap} :
    loadedVal tds xPtr intTy (CerbMem.memValueToBytes tds [] sevenMval).2 = sevenVal := rfl

theorem htrap_seven {tds : CerbTags.TagDefsMap} :
    cellLoadTrap tds ⟨addrOf xPtr, intTy,
      (CerbMem.memValueToBytes tds [] sevenMval).2⟩ = false := rfl

/-! ## The precondition big-seps -/

variable {GF : BundledGFunctors}

theorem bigSepA_ptx [SpikeGS .hasLC GF] :
    iprop(([∗map] i ↦ c ∈ mA, cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
      pointsToCell fmapEmpty (GF := GF) xPtr (.own 1) intTy bytesX := by
  refine .trans (BigSepM.bigSepM_insert (i := 0) (x := cellX)
    (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0)).1 ?_
  iintro ⟨Hx, -⟩
  iapply (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mpr
  iexists 0, xAddr
  isplit
  · ipureintro
    exact xPtr_eq
  · iexact Hx

/-! ## The proved footprint triples (interior derivations:
small axioms + SEQ from slice A, ending in the ProvenTriple shape at
the straight-line profile `spikeCtx`/`spikeEnv`) -/

/-- x's cell after the store of 7. -/
abbrev cellX7 : SpikeCell :=
  ⟨xAddr, intTy, (CerbMem.memValueToBytes fmapEmpty [] sevenMval).2⟩

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
    iprop(pointsToCell fmapEmpty (GF := GF) xPtr (.own 1) intTy
      (CerbMem.memValueToBytes fmapEmpty [] sevenMval).2) ⊢
      iprop([∗map] i ↦ c ∈ mA7, cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c) := by
  iintro Hx
  icases (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mp $$ Hx with ⟨%ix, %ax, %Hpx, Hx⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj (xPtr_eq.symm.trans Hpx)
  iapply (BigSepM.bigSepM_insert
    (Φ := fun (i : Int) (c : SpikeCell) => cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)
    (i := 0) (x := cellX7)
    (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0)).2
  isplitl [Hx]
  · iexact Hx
  · iapply (BigSepM.bigSepM_empty_intro
      (P := (BIBase.emp : IProp GF))
      (Φ := fun (i : Int) (c : SpikeCell) => cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c))
    itrivial

/-- The store's footprint triple, proved in the derived logic:
    ⦃x ↦ bytesX⦄ store(x,7) ⦃unit; x ↦ seven-bytes⦄. -/
theorem provenB {GF : BundledGFunctors} [SpikeGpreS GF] :
    ProvenTriple GF spikeCtx spikeCtl spikeEnv progB mA (fun v Q => v = Vunit ∧ Q = mA7) := by
  intro instGS
  refine bigSepA_ptx.trans ?_
  iintro Hx
  ihave HW := wp_store (s := Stuckness.NotStuck) (E := ⊤) (M := spikeCtx) (ctl := spikeCtl) loc0 empty_annotation
    intTy xPtr sevenVal NA sevenMval bytesX spikeEnv seven_encodes (seven_storable _) rfl $$ Hx
  iapply spike_wp_wand $$ HW
  iintro %v ⟨%fp, %hv, Hx⟩
  iexists mA7
  isplit
  · ipureintro
    subst hv
    exact ⟨rfl, rfl⟩
  · ihave HC := ptx_to_cells $$ Hx
    iexact HC

/-- Vacuous block specifications at the straight-line profile (no
    label is registered), at any postcondition. -/
theorem spike_blockSpecs [SpikeGS .hasLC GF] (Ψ : SpikeVal → EnvStack → IProp GF) :
    ⊢ blockSpecs (GF := GF) spikeCtx none (fun _ _ _ => iprop(False)) emptyProcSpec Ψ :=
  blockSpecs_intro fun l _ _ _ _ _ hl => (spikeCtx_labels_none l hl).elim

/-- The store-then-load footprint triple:
    ⦃x ↦ bytesX⦄ lets _ = store(x,7) in load(x) ⦃Specified 7; x ↦ seven-bytes⦄
    — `wps_seq` over `wps_store` then `wps_load`, collapsed into the
    base WP by `wps_sound`. -/
theorem provenA {GF : BundledGFunctors} [SpikeGpreS GF] :
    ProvenTriple GF spikeCtx spikeCtl spikeEnv progA mA (fun v Q => v = sevenVal ∧ Q = mA7) := by
  intro instGS
  refine bigSepA_ptx.trans ?_
  refine .trans ?_ ((BI.emp_sep.2.trans (BI.sep_mono
    ((spike_blockSpecs (fun w _ => iprop(∃ Q : CellMap, ⌜w.val = sevenVal ∧ Q = mA7⌝ ∗
        ([∗map] i ↦ c ∈ Q, cellOwn spikeCtx.tagDefs (hlc := .hasLC) (GF := GF) i (.own 1) c)))).trans
      (wps_sound_empty (ctl := spikeCtl) rfl progA spikeEnv)) .rfl)).trans
    BI.wand_elim_left)
  rw [show (progA : CoreExpr) =
    Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
      (storeExpr loc0 empty_annotation intTy xPtr sevenVal NA)
      (loadExpr loc0 empty_annotation intTy xPtr NA)) from rfl]
  iintro Hx
  iapply wps_seq
  iapply wps_store loc0 empty_annotation intTy xPtr sevenVal NA sevenMval bytesX
    spikeEnv seven_encodes (seven_storable _)
  isplitl [Hx]
  · iexact Hx
  iintro %fp Hx
  iapply wps_load loc0 empty_annotation intTy xPtr NA (.own 1)
    (CerbMem.memValueToBytes fmapEmpty [] sevenMval).2 spikeEnv htrap_seven
  isplitl [Hx]
  · iexact Hx
  iintro %fp2 Hx
  iexists mA7
  isplit
  · ipureintro
    exact ⟨loaded_seven, rfl⟩
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
    SemTriple spikeCtx spikeCtl spikeEnv progA mA (fun v Q => v = sevenVal ∧ Q = mA7) :=
  semantic_triple_sound (GF := GF) rfl rfl (ctl := spikeCtl) rfl spikeCtx_labels_frag spikeCtx_labels_pot spikeCtx_fragProcs
    fragA
    (Nat.le_trans fragA.pot_le_two
      (by rw [show esize progA = 2 from rfl]; unfold lemDefaultFuel; omega))
    fmapEmpty [] provenA

/-- EXHIBIT (b), the operator's FRAME EXHIBIT at the semantic level:
    the store's x-footprint triple, framed by y's cell —
    ⦃x ↦ - ∗ y ↦ a⦄ store(x,7) ⦃x ↦ 7 ∗ y ↦ a⦄ over engine
    configurations, y (and all unnamed rest) verbatim. -/
theorem exhibitB_semantic {GF : BundledGFunctors} [SpikeGpreS GF] :
    SemTriple spikeCtx spikeCtl spikeEnv progB (Iris.Std.PartialMap.union mA mF)
      (fun v Q => ∃ Q₀, (v = Vunit ∧ Q₀ = mA7) ∧ Q₀ ##ₘ mF ∧
        Q = Iris.Std.PartialMap.union Q₀ mF) :=
  semantic_frame (GF := GF) rfl rfl (ctl := spikeCtl) rfl spikeCtx_labels_frag spikeCtx_labels_pot spikeCtx_fragProcs
    fragB
    (Nat.le_trans fragB.pot_le_two
      (by rw [show esize progB = 1 from rfl]; unfold lemDefaultFuel; omega))
    fmapEmpty [] mF mA_disj_mF provenB

/-- Exhibit (a) at the seeded engine instance (rest := ∅): from any
    driver state holding the straight-line thread at the seeded memory,
    the shipped loop at every fuel exhausts or delivers `Specified(7)`. -/
theorem exhibitA_engine :
    DriverSafeCtl spikeCtx (spikeThread progA) progA spikeEnv spikeCtl σ₀
      (fun v _ => v = sevenVal) := by
  refine (exhibitA_semantic (GF := SpikeGF) ∅
    (Iris.Std.LawfulPartialMap.disjoint_empty_right mA) σ₀
    (by rw [show Iris.Std.PartialMap.union mA ∅ = mA from
        Iris.Std.LawfulPartialMap.union_empty_right]
        exact coh_mA)
    (spikeThread progA) rfl).mono ?_
  intro v σ' ⟨Q, ⟨hv, _⟩, _, _⟩
  exact hv

/-- Exhibit (b) at the seeded engine instance: after the store, the
    engine's bytemap holds 7's image at x and y's bytes UNCHANGED —
    frame locality read back from the real memory. -/
theorem exhibitB_engine :
    DriverSafeCtl spikeCtx (spikeThread progB) progB spikeEnv spikeCtl σ₀
      (fun v σ' =>
        v = Vunit ∧
        CerbMem.readBytesFrom σ' xAddr 4 =
          (CerbMem.memValueToBytes fmapEmpty [] sevenMval).2 ∧
        CerbMem.readBytesFrom σ' yAddr 4 = bytesY) := by
  have hcohBu : Sat fmapEmpty σ₀ (Iris.Std.PartialMap.union
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
  refine (exhibitB_semantic (GF := SpikeGF) ∅
    (Iris.Std.LawfulPartialMap.disjoint_empty_right _) σ₀ hcohBu
    (spikeThread progB) rfl).mono ?_
  intro v σ' hpost
  obtain ⟨Q, ⟨Q₀, ⟨hv, hQ0⟩, hdisj, hQ⟩, _, hsat⟩ := hpost
  subst hQ0 hQ
  have hsat' : Sat fmapEmpty σ' (Iris.Std.PartialMap.union mA7 mF) :=
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
  rw [show CerbMem.sizeofCtype fmapEmpty intTy = 4 from rfl] at hcx hcy
  exact ⟨hv, hcx, hcy⟩

/-! ## The total judgment for exhibit (a): `progA_wpt` (budget 6 =
store 3 + load 3) is the derivation the total lane runs; its
shipped-pipeline export is `exhibitA_prod` (ProdExhibit.lean, on the
self-contained twin `progAProd` that creates its own cell — the seeded
`progA` cannot start from the cold-start memory). The former
example-specific six-step engine simulation (`exhibitA_terminates`) is
RETIRED (alloc arc P2), and the former `exhibitA_total` over the package
loop `driveU` was deleted with the loop (fuel-lane restatement,
2026-09-03). Zero operational proof terms in this module. -/

/-- The seven image decodes back to `sevenMval` at ANY address (the
    table- and address-independent int decode). -/
theorem seven_reconstruct {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (ad : Int) :
    CerbMem.reconstructValue tds lum fpm ad intTy
      (((sevenBytes tds).drop 0).take (CerbMem.sizeofCtype tds intTy)) =
      sevenMval := rfl

theorem seven_fromMemValue : (valueFromMemValue sevenMval).2 = sevenVal := rfl

theorem seven_loadTrap : loadTrapV intTy sevenMval = false := rfl

/-- The engine-facing postcondition of the total route: `Specified 7`
    delivered, the final memory holding 7's image at the seeded
    cell. -/
def ψX (tds : CerbTags.TagDefsMap) : value → Mem → Prop := fun v σ' =>
  v = sevenVal ∧ CellCoh tds σ' 0 ⟨xAddr, intTy, sevenBytes tds⟩

/-- Exhibit (a) at the TOTAL judgment, budget 6 (store 3 + load 3),
    from the seeded cell's ownership alone. -/
theorem progA_wpt {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    iprop(pointsToCell M.tagDefs (GF := GF) xPtr (.own 1) intTy bytesX) ⊢
      wpt M p Ls Θ 6 (readoutPost (ψX M.tagDefs)) progA (ev0 :: evs) := by
  iintro Hpt
  rw [show (progA : CoreExpr) =
    Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
      (storeExpr loc0 empty_annotation intTy xPtr sevenVal NA)
      (loadExpr loc0 empty_annotation intTy xPtr NA)) from rfl,
    show (6 : Nat) = 3 + 3 from rfl]
  iapply wpt_seq
  iapply wpt_store loc0 empty_annotation intTy xPtr sevenVal NA
    sevenMval bytesX _ (Nat.le_refl 3) seven_encodes (seven_storable _)
  isplitl [Hpt]
  · iexact Hpt
  iintro %fp Hpt
  iapply wpt_mono
    (fun u ρ' => readoutPost_annot_absorb (ψX M.tagDefs) [DA_pos [] fp] Vunit u ρ') _ _
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj (xPtr_eq.symm.trans hpv)
  rw [show (xPtr : CerbMem.PointerValue) =
      cellPtr 0 (xAddr + ((0 : Nat) : Int)) from by
    rw [xPtr_eq]
    exact congrArg (cellPtr 0) (by omega)]
  iapply wpt_load_cell_at loc0 empty_annotation 0 xAddr intTy 0 intTy NA
    (.own 1) (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2 _
    (mv := sevenMval) (Nat.le_refl 3) (by omega)
    (fun lum fpm => seven_reconstruct lum fpm _) seven_loadTrap
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp2 Hcell
  iintro %σ2 %ns %κs %nt Hσ
  icases (stateInterp_iff σ2 ns κs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  ihave %Hcc : ⌜CellCoh M.tagDefs σ2 0 ⟨xAddr, intTy,
      (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2⟩ ∧
      Iris.Std.PartialMap.get? mm 0 = some (metaOf M.tagDefs
        (⟨xAddr, intTy, (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2⟩ :
          SpikeCell))⌝ $$ [Hmi Hbi Hcell]
  · iapply cellOwn_cellCoh M.tagDefs HG 0 (.own 1)
      ⟨xAddr, intTy, (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2⟩
      $$ [$Hmi $Hbi $Hcell]
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact ⟨seven_fromMemValue, Hcc.1⟩

/-! ## EXHIBIT C ([USER 2026-08-30]): disjoint sequential stores,
exported to the engine level

`lets _ = store(x,5) in store(y,6)` on the two seeded cells. The
interior derivation is `wps_exhibit_seq_stores` (Examples/Layout.lean)
— the store small axiom per leg, glued by the sequencing rule; the
export below collapses it into the base WP (`wps_sound`) and
repackages its footprint form through `semantic_triple_sound`. The
postcondition carries NO value clause: the exhibit's assertion-only
postcondition (deliberately, the wildcard-binding fragment shape)
discards the delivered value — the update facts are the content. -/

/-- Exhibit (c): `lets _ = store(x,5) in store(y,6)`, x/y the two
    seeded disjoint cells. -/
abbrev progC : CoreExpr :=
  sseqExpr BTy_unit (storeExpr loc0 empty_annotation intTy xPtr fiveVal NA)
    (storeExpr loc0 empty_annotation intTy yPtr sixVal NA)

theorem fragC : Frag progC := Frag.sseq (.store) (.store)

/-- The two cells after the two stores. -/
abbrev cellX5 : SpikeCell := ⟨xAddr, intTy, (fiveBytes fmapEmpty)⟩

abbrev cellY6 : SpikeCell := ⟨yAddr, intTy, (sixBytes fmapEmpty)⟩

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
    iprop(([∗map] i ↦ c ∈ mB, cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
      iprop(pointsToCell fmapEmpty (GF := GF) xPtr (.own 1) intTy bytesX ∗
        pointsToCell fmapEmpty yPtr (.own 1) intTy bytesY) := by
  refine .trans (BigSepM.bigSepM_insert (i := 1) (x := cellY) mB_base_get1).1 ?_
  iintro ⟨Hy, Hbase⟩
  icases (BigSepM.bigSepM_insert (i := 0) (x := cellX)
    (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0)).1
    $$ Hbase with ⟨Hx, -⟩
  isplitl [Hx]
  · iapply (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mpr
    iexists 0, xAddr
    isplit
    · ipureintro
      exact xPtr_eq
    · iexact Hx
  · iapply (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mpr
    iexists 1, yAddr
    isplit
    · ipureintro
      exact yPtr_eq
    · iexact Hy

/-- Repackage the two updated cells as mC's big-sep. -/
theorem cells_to_mC [SpikeGS .hasLC GF] :
    iprop(pointsToCell fmapEmpty (GF := GF) xPtr (.own 1) intTy (fiveBytes fmapEmpty) ∗
      pointsToCell fmapEmpty yPtr (.own 1) intTy (sixBytes fmapEmpty)) ⊢
      iprop([∗map] i ↦ c ∈ mC, cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c) := by
  iintro ⟨Hx, Hy⟩
  icases (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mp $$ Hx with ⟨%ix, %ax, %Hpx, Hx⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj (xPtr_eq.symm.trans Hpx)
  icases (pointsToCell_cellOwn_iff fmapEmpty _ _ _ _).mp $$ Hy with ⟨%iy, %ay, %Hpy, Hy⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj (yPtr_eq.symm.trans Hpy)
  iapply (BigSepM.bigSepM_insert
    (Φ := fun (i : Int) (c : SpikeCell) => cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)
    (i := 1) (x := cellY6) mC_base_get1).2
  isplitl [Hy]
  · iexact Hy
  · iapply (BigSepM.bigSepM_insert
      (Φ := fun (i : Int) (c : SpikeCell) => cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)
      (i := 0) (x := cellX5)
      (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) 0)).2
    isplitl [Hx]
    · iexact Hx
    · iapply (BigSepM.bigSepM_empty_intro
        (P := (BIBase.emp : IProp GF))
        (Φ := fun (i : Int) (c : SpikeCell) => cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c))
      itrivial

/-- The two-store footprint triple: the interior compositional
    derivation `wps_exhibit_seq_stores` collapsed into the base WP and
    repackaged at footprint granularity — no re-derivation, only
    big-sep ↔ pointsToCell fmapEmpty plumbing. -/
theorem provenC {GF : BundledGFunctors} [SpikeGpreS GF] :
    ProvenTriple GF spikeCtx spikeCtl spikeEnv progC mB (fun _ Q => Q = mC) := by
  intro instGS
  refine bigSepB_pts.trans ((wps_exhibit_seq_stores (M := spikeCtx) (p := none) (Θ := emptyProcSpec)
    (Ls := fun _ _ _ => iprop(False)) xPtr yPtr loc0 loc0
    empty_annotation empty_annotation NA NA BTy_unit bytesX bytesY fmapEmpty []).trans ?_)
  refine ((BI.emp_sep.2.trans (BI.sep_mono
    ((spike_blockSpecs _).trans (wps_sound_empty (ctl := spikeCtl) rfl progC spikeEnv)) .rfl)).trans
    BI.wand_elim_left).trans ?_
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
    SemTriple spikeCtx spikeCtl spikeEnv progC mB (fun _ Q => Q = mC) :=
  semantic_triple_sound (GF := GF) rfl rfl (ctl := spikeCtl) rfl spikeCtx_labels_frag spikeCtx_labels_pot spikeCtx_fragProcs
    fragC
    (Nat.le_trans fragC.pot_le_two
      (by rw [show esize progC = 2 from rfl]; unfold lemDefaultFuel; omega))
    fmapEmpty [] provenC

/-- Exhibit (c) at the seeded engine instance (rest := ∅): after the
    two stores, the engine's bytemap holds 5's image at x AND 6's
    image at y — the non-conflicting update read back from the real
    memory. -/
theorem exhibitC_engine :
    DriverSafeCtl spikeCtx (spikeThread progC) progC spikeEnv spikeCtl σ₀
      (fun _ σ' =>
        CerbMem.readBytesFrom σ' xAddr 4 = (fiveBytes fmapEmpty) ∧
        CerbMem.readBytesFrom σ' yAddr 4 = (sixBytes fmapEmpty)) := by
  refine (exhibitC_semantic (GF := SpikeGF) ∅
    (Iris.Std.LawfulPartialMap.disjoint_empty_right mB) σ₀
    (by rw [show Iris.Std.PartialMap.union mB ∅ = mB from
        Iris.Std.LawfulPartialMap.union_empty_right]
        exact coh_mB)
    (spikeThread progC) rfl).mono ?_
  intro v σ' hpost
  obtain ⟨Q, hQ, _, hsat⟩ := hpost
  subst hQ
  have hsat' : Sat fmapEmpty σ' mC :=
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
  rw [show CerbMem.sizeofCtype fmapEmpty intTy = 4 from rfl] at hcx hcy
  exact ⟨hcx, hcy⟩

end CerberusHeapLang
