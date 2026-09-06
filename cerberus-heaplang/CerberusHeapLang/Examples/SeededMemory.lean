/-
Authored memory fixture for Exhibit and its consumers.

The state and pointers are concrete data, independent of ambient fuel.
`seeded_eq` proves that the engine's two object allocations produce them
at every positive ambient budget; `seeded_zero` records exhaustion of the
initial memory bind. These are initialization equations, not proofs of
the exhibit programs. Their store/load claims use the public logic rules
in Exhibit.lean. This module is classified as a semantic test because its
initialization proof uses the engine-memory layer directly.
-/
import CerberusHeapLang.Examples.Layout

set_option autoImplicit false

namespace CerberusHeapLang

/-- The engine allocates downward from its address ceiling. -/
def xAddr : Int := 281474976710648

def yAddr : Int := 281474976710644

def xPtr : CerbMem.PointerValue := cellPtr 0 xAddr

def yPtr : CerbMem.PointerValue := cellPtr 1 yAddr

theorem xPtr_eq : xPtr = cellPtr 0 xAddr := rfl

theorem yPtr_eq : yPtr = cellPtr 1 yAddr := rfl

/-- The first allocation record, including the engine's prefix. -/
def allocX : CerbMem.Allocation :=
  { base := xAddr, size := 4, ty := some intTy,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "spike-x") none,
    prefix_ := PrefOther "spike-x" }

def allocY : CerbMem.Allocation :=
  { base := yAddr, size := 4, ty := some intTy,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "spike-y") none,
    prefix_ := PrefOther "spike-y" }

/-- Concrete result of the first allocation, including `lastUsed`. -/
def seededAfterX : Mem :=
  CerbMem.writeBytesTo
    { ({} : Mem) with
      nextAllocId := 1, lastUsed := some 0,
      lastAddress := xAddr, allocations := ({} : Mem).allocations.insert 0 allocX }
    xAddr (List.replicate 4 undefByte)

/-- The seeded state, identified with actual allocation by `seeded_eq`. -/
def σ₀ : Mem :=
  CerbMem.writeBytesTo
    { seededAfterX with
      nextAllocId := 2, lastUsed := some 1,
      lastAddress := yAddr, allocations := seededAfterX.allocations.insert 1 allocY }
    yAddr (List.replicate 4 undefByte)

theorem σ₀_allocations :
    σ₀.allocations =
      ((({} : Mem).allocations.insert 0 allocX).insert 1 allocY) := rfl

/-- Two int objects allocated by the engine from the empty state. -/
def seeded [LemFuel] : Option ((CerbMem.PointerValue × CerbMem.PointerValue) × Mem) :=
  match applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "spike-x")
      (CerbMem.integerIval 4) intTy none none) ({} : Mem) with
  | some (x, σ1) =>
    match applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "spike-y")
        (CerbMem.integerIval 4) intTy none none) σ1 with
    | some (y, σ2) => some ((x, y), σ2)
    | none => none
  | none => none

/-- Successful engine initialization agrees with the complete fixture
    state at every positive ambient budget. -/
theorem seeded_eq [LemFuel] (hfuel : 0 < LemFuel.fuel) :
    seeded = some ((xPtr, yPtr), σ₀) := by
  have hx : applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "spike-x")
      (CerbMem.integerIval 4) intTy none none) ({} : Mem) =
        some (xPtr, seededAfterX) :=
    allocateObject_success fmapEmpty {} (PrefOther "spike-x") .Prov_none 4 intTy
      hfuel (by decide) (by decide)
  have hy : applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "spike-y")
      (CerbMem.integerIval 4) intTy none none) seededAfterX = some (yPtr, σ₀) :=
    allocateObject_success fmapEmpty seededAfterX (PrefOther "spike-y") .Prov_none 4 intTy
      hfuel (by decide) (by decide)
  unfold seeded
  rw [hx]
  dsimp only
  rw [hy]

/-- Ambient zero cannot produce an initialized fixture. -/
theorem seeded_zero [LemFuel] (hzero : LemFuel.fuel = 0) : seeded = none := by
  unfold seeded CerbMem.allocateObject CerbMem.integerIval
  rw [applyMemM_bind_zero _ _ _ hzero]

end CerberusHeapLang
