/-
CerberusHeapLang.Examples.ReadinessSmoke — THE READINESS SMOKE TEST
(alloc arc P5, charter item 5): can a future type interpretation sit
above the raw logic without importing engine proofs or allocator
internals?

This module imports ONLY `CerberusHeapLang.API`. It defines one
semantic predicate of shape `PointerValue → IProp` for a two-field
object,

    twoField tds p xb yb  :=  ∃ id a, ⌜p = cellPtr id a⌝ ∗
                              view(id, a, offset 0) ↦ field xb ∗
                              view(id, a, offset 8) ↦ field yb

(the object is ONE allocation of type `long[2]`; the fields are the
two typed sub-range views of it, each holding half the metadata
knowledge and all of its own bytes), and DERIVES, from the public
rules alone,

- LOAD of either field (`twoField_load_x`, `twoField_load_y`),
- STORE to either field (`twoField_store_x`, `twoField_store_y`),
- ALLOCATE (`twoField_create`): a fresh two-field object from the
  allocation budget `allocBudget (allocCost objTy align)`,

each a one-screen client proof: the field-x rules are `wps_load_at`/
`wps_store_at` at offset 0; the field-y rules address the field the
way a Core program does — by the engine's own pointer arithmetic
`arrayShiftPtrval tds p long 1` — and are the same rules at offset 8
after the provenance-preserving shift law `cellPtr_arrayShift`; the
allocation rule is `wps_create` followed by the bundle→view
conversion (`pointsToCell_cellOwn_iff`, `cellOwn_view`) and ONE
`pointsToView_split` at half fractions (`twoField_of_cell`).

WHAT THIS IS NOT ([USER], the charter): not a RefinedC-style `type`
record, no subtyping, no automation. The predicate is indexed by the
fields' BYTE IMAGES, exactly as the raw rules are; the load rules
take the decode premise (`reconstructValue … = mv`) the raw rules
take, the store rules the storability premise. A type interpretation
would add a representation relation `value ↔ bytes` on top — that is
its business, not this smoke test's.

MEASURED (scripts/parametric_inventory.lean, client-module section):
this module has zero direct references to the ghost maps / `CohG` /
cursor, the `Step` inductive and its lemmas, the judgment unfoldings
and the plan model — the P5 notes record the line.
-/
import CerberusHeapLang.API

set_option autoImplicit false

namespace CerberusHeapLang.ReadinessSmoke

open Iris Iris.BI Iris.ProgramLogic

/-! ## The layout: one `long[2]` allocation, two 8-byte fields -/

/-- The field type: `signed long` (8 bytes in LP64). -/
def fieldTy : ctype := Ctype [] (.Basic (.Integer (.Signed .Long)))

/-- The object type: two fields in ONE allocation. -/
def objTy : ctype := Ctype [] (.Array0 fieldTy (some 2))

theorem fieldTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds fieldTy = 8 := rfl
theorem objTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds objTy = 16 := rfl

/-- The object type has positive size (the public create rules' `hsz`). -/
theorem objTy_size_pos {tds : CerbTags.TagDefsMap} : 0 < CerbMem.sizeofCtype tds objTy := by
  rw [objTy_size]
  decide
theorem objTy_nonatomic : atomicTy objTy = false := rfl

/-- The long-array decode consults no side table (the layout's
    inertness fact `wps_create` asks for). -/
theorem objTy_decIndep {tds : CerbTags.TagDefsMap} (a : Int) (bs : List CerbMem.AbsByte) :
    decIndep tds a objTy bs :=
  fun _ _ => rfl

theorem fieldTy_ne_void : ∀ q, fieldTy ≠ Ctype q .Void0 :=
  fun _ h => by unfold fieldTy at h; cases h

/-- The unspecified image of one fresh field. -/
abbrev undefField : List CerbMem.AbsByte := List.replicate 8 undefByte

/-- The second field's address, as a Core program computes it: the
    engine's own array shift by one `long`. -/
abbrev fieldYPtr (tds : CerbTags.TagDefsMap) (p : CerbMem.PointerValue) : CerbMem.PointerValue :=
  CerbMem.arrayShiftPtrval tds p fieldTy (CerbMem.integerIval 1)

/-- The shift law at this layout: `fieldYPtr` of a fragment pointer is
    the same allocation at base + 8 (`cellPtr_arrayShift`). -/
theorem fieldYPtr_cellPtr (tds : CerbTags.TagDefsMap) (id a : Int) :
    fieldYPtr tds (cellPtr id a) = cellPtr id (a + ((8 : Nat) : Int)) := by
  unfold fieldYPtr
  rw [cellPtr_arrayShift tds id a fieldTy 1 fieldTy_ne_void, fieldTy_size, Int.one_mul]

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-! ## The predicate -/

/-- THE TWO-FIELD OBJECT: `p` is the base of one `long[2]` allocation
    whose two fields hold the images `xb` (at offset 0) and `yb` (at
    offset 8). Each field is a typed sub-range view carrying half the
    allocation's metadata knowledge and full ownership of its bytes. -/
def twoField (tds : CerbTags.TagDefsMap) (p : CerbMem.PointerValue)
    (xb yb : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id a : Int), ⌜p = cellPtr id a⌝ ∗
    pointsToView tds id a objTy 0 (.own (Qp.half 1)) (.own 1) fieldTy xb ∗
    pointsToView tds id a objTy 8 (.own (Qp.half 1)) (.own 1) fieldTy yb)

theorem twoField_iff (tds : CerbTags.TagDefsMap) (p : CerbMem.PointerValue)
    (xb yb : List CerbMem.AbsByte) :
    twoField tds (GF := GF) p xb yb ⊣⊢
      iprop(∃ (id a : Int), ⌜p = cellPtr id a⌝ ∗
        pointsToView tds id a objTy 0 (.own (Qp.half 1)) (.own 1) fieldTy xb ∗
        pointsToView tds id a objTy 8 (.own (Qp.half 1)) (.own 1) fieldTy yb) := .rfl

/-- A fresh whole-object bundle IS an uninitialized two-field object:
    bundle → maximal view (`cellOwn_view`) → one split at half
    fractions. -/
theorem twoField_of_cell (tds : CerbTags.TagDefsMap) (p : CerbMem.PointerValue) :
    pointsToCell tds (GF := GF) p (.own 1) objTy
        (List.replicate (CerbMem.sizeofCtype tds objTy) undefByte) ⊢
      twoField tds p undefField undefField := by
  rw [show List.replicate (CerbMem.sizeofCtype tds objTy) undefByte =
    undefField ++ undefField from rfl]
  iintro Hpt
  icases (pointsToCell_cellOwn_iff tds p (.own 1) objTy _).mp $$ Hpt
    with ⟨%id, %a, %hp, Hcell⟩
  icases (cellOwn_view tds id (.own 1) _).1 $$ Hcell with ⟨Hv, -⟩
  have hsplit := pointsToView_split tds (GF := GF) id a objTy 0 (Qp.half 1) (Qp.half 1)
    (.own 1) objTy fieldTy fieldTy undefField undefField
    (by rw [objTy_size, fieldTy_size]) rfl
  rw [Qp.half_add_half, show (0 : Nat) + CerbMem.sizeofCtype tds fieldTy = 8 from rfl] at hsplit
  icases hsplit $$ Hv with ⟨Hx, Hy⟩
  iapply (twoField_iff _ _ _ _).mpr
  iexists id, a
  isplit
  · ipureintro
    exact hp
  isplitl [Hx]
  · iexact Hx
  · iexact Hy

section Rules

variable {M : MachineCtx} {Ls : LabelSpec GF}

/-! ## The derived rules (partial stratum) -/

/-- LOAD FIELD X: `wps_load_at` at offset 0. -/
theorem twoField_load_x {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (p : CerbMem.PointerValue) (mo : memory_order)
    (xb yb : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hdec : ∀ lum fpm ad, CerbMem.reconstructValue M.tagDefs lum fpm ad fieldTy xb = mv)
    (htrap : loadTrapV fieldTy mv = false) :
    iprop(twoField M.tagDefs (GF := GF) p xb yb ∗
      (∀ fp, twoField M.tagDefs p xb yb -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann fieldTy p mo) ρ := by
  iintro ⟨H, HΨ⟩
  icases (twoField_iff _ _ _ _).mp $$ H with ⟨%id, %a, %hp, Hx, Hy⟩
  rw [hp, show loadExpr loc ann fieldTy (cellPtr id a) mo =
    loadExpr loc ann fieldTy (cellPtr id (a + ((0 : Nat) : Int))) mo by simp]
  iapply wps_load_at loc ann id a objTy 0 fieldTy mo (.own (Qp.half 1)) (.own 1) xb ρ
    (fun lum fpm => hdec lum fpm _) htrap
  isplitl [Hx]
  · iexact Hx
  iintro %fp Hx
  iapply HΨ
  iapply (twoField_iff _ _ _ _).mpr
  iexists id, a
  isplit
  · ipureintro
    rfl
  isplitl [Hx]
  · iexact Hx
  · iexact Hy

/-- LOAD FIELD Y: the program addresses the field by the engine's
    array shift; `cellPtr_arrayShift` turns it into offset 8. -/
theorem twoField_load_y {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (p : CerbMem.PointerValue) (mo : memory_order)
    (xb yb : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hdec : ∀ lum fpm ad, CerbMem.reconstructValue M.tagDefs lum fpm ad fieldTy yb = mv)
    (htrap : loadTrapV fieldTy mv = false) :
    iprop(twoField M.tagDefs (GF := GF) p xb yb ∗
      (∀ fp, twoField M.tagDefs p xb yb -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann fieldTy (fieldYPtr M.tagDefs p) mo) ρ := by
  iintro ⟨H, HΨ⟩
  icases (twoField_iff _ _ _ _).mp $$ H with ⟨%id, %a, %hp, Hx, Hy⟩
  rw [hp, fieldYPtr_cellPtr]
  iapply wps_load_at loc ann id a objTy 8 fieldTy mo (.own (Qp.half 1)) (.own 1) yb ρ
    (fun lum fpm => hdec lum fpm _) htrap
  isplitl [Hy]
  · iexact Hy
  iintro %fp Hy
  iapply HΨ
  iapply (twoField_iff _ _ _ _).mpr
  iexists id, a
  isplit
  · ipureintro
    rfl
  isplitl [Hx]
  · iexact Hx
  · iexact Hy

/-- STORE FIELD X: `wps_store_at` at offset 0; the postcondition is the
    object with x's image replaced by the stored value's serialization. -/
theorem twoField_store_x {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (p : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (xb yb : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ fieldTy)) cv = some mv)
    (hst : StorableAt M.tagDefs fieldTy mv) :
    iprop(twoField M.tagDefs (GF := GF) p xb yb ∗
      (∀ fp, twoField M.tagDefs p (CerbMem.memValueToBytes M.tagDefs [] mv).2 yb -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann fieldTy p cv mo) ρ := by
  iintro ⟨H, HΨ⟩
  icases (twoField_iff _ _ _ _).mp $$ H with ⟨%id, %a, %hp, Hx, Hy⟩
  rw [hp, show storeExpr loc ann fieldTy (cellPtr id a) cv mo =
    storeExpr loc ann fieldTy (cellPtr id (a + ((0 : Nat) : Int))) cv mo by simp]
  iapply wps_store_at loc ann id a objTy 0 fieldTy cv mo (.own (Qp.half 1)) xb ρ
    hmv hst.toView
  isplitl [Hx]
  · iexact Hx
  iintro %fp Hx
  iapply HΨ
  iapply (twoField_iff _ _ _ _).mpr
  iexists id, a
  isplit
  · ipureintro
    rfl
  isplitl [Hx]
  · iexact Hx
  · iexact Hy

/-- STORE FIELD Y: through the engine's array shift, at offset 8. -/
theorem twoField_store_y {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (p : CerbMem.PointerValue) (cv : value) (mo : memory_order)
    (xb yb : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ fieldTy)) cv = some mv)
    (hst : StorableAt M.tagDefs fieldTy mv) :
    iprop(twoField M.tagDefs (GF := GF) p xb yb ∗
      (∀ fp, twoField M.tagDefs p xb (CerbMem.memValueToBytes M.tagDefs [] mv).2 -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann fieldTy (fieldYPtr M.tagDefs p) cv mo) ρ := by
  iintro ⟨H, HΨ⟩
  icases (twoField_iff _ _ _ _).mp $$ H with ⟨%id, %a, %hp, Hx, Hy⟩
  rw [hp, fieldYPtr_cellPtr]
  iapply wps_store_at loc ann id a objTy 8 fieldTy cv mo (.own (Qp.half 1)) yb ρ
    hmv hst.toView
  isplitl [Hy]
  · iexact Hy
  iintro %fp Hy
  iapply HΨ
  iapply (twoField_iff _ _ _ _).mpr
  iexists id, a
  isplit
  · ipureintro
    rfl
  isplitl [Hx]
  · iexact Hx
  · iexact Hy

/-- ALLOCATE: from the allocation budget `allocBudget (allocCost
    long[2] align)` (K2.5; formerly the plan `allocCap (⟨align, long[2]⟩
    :: rest)`), `create` delivers a fresh uninitialized two-field object
    (both fields unspecified) and the address bounds — the PUBLIC
    `wps_create` followed by `twoField_of_cell`. A client holding more
    budget splits it first (`allocBudget_split`). -/
theorem twoField_create {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int)
    (pref : prefix0) (ρ : EnvStack) :
    iprop(allocBudget (GF := GF) (allocCost M.tagDefs objTy alignN) ∗
      (∀ p : CerbMem.PointerValue,
        (twoField M.tagDefs p undefField undefField ∗
          ⌜0 < addrOf p ∧ addrOf p < 2 ^ 64⌝) -∗
        Ψ (SpikeVal.pure (Vobject (OVpointer p))) ρ)) ⊢
      wps M Ls Ψ (createExpr loc ann (.IV aprov alignN) objTy pref) ρ := by
  iintro ⟨Hcap, HΨ⟩
  iapply wps_create loc ann aprov alignN objTy pref ρ objTy_size_pos objTy_nonatomic
    (fun a => objTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p ⟨Hpt, %hb⟩
  iapply HΨ
  isplitl [Hpt]
  · iapply twoField_of_cell M.tagDefs p $$ Hpt
  · ipureintro
    exact hb

end Rules

end CerberusHeapLang.ReadinessSmoke
