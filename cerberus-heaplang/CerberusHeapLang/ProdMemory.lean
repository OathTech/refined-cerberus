/-
Production cold-start memory: the engine allocates and zeroes errno before
entering the program. The concrete state is independent of ambient fuel;
the allocation equation requires positive fuel, and a separate equation
records its zero-budget failure. Successful setup preserves the exact
metadata and byte map, including lastUsed.

This module proves the memory well-formedness and unallocated-byte
premises used by production launch coherence. ProdEntry connects these
initialization equations to the shipped drive pipeline. The driver and
program execution certificates are separate obligations.
-/
import CerberusHeapLang.Adequacy

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List
open scoped Iris.Std.PartialMap

def errnoAddr : Int := 281474976710648

def errnoPtr : CerbMem.PointerValue := cellPtr 0 errnoAddr

/-- The zero value the driver stores into errno. -/
def zeroMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (Signed Int_) (CerbMem.integerIval 0)

/-- errno's allocation, exactly as allocateObject builds it. -/
def errnoAllocRec : CerbMem.Allocation :=
  { base := errnoAddr, size := 4, ty := some signed_int,
    isReadonly := CerbMem.readonlyStatusForAlloc (PrefOther "errno") none,
    prefix_ := PrefOther "errno" }

/-- The engine's own errno allocation on the cold state. -/
def errnoSeeded [LemFuel] : Option (CerbMem.PointerValue × Mem) :=
  applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "errno")
    (CerbMem.alignofIval fmapEmpty signed_int) signed_int none none)
    CerbMem.initialMemState

/-- Concrete state after errno allocation. Its agreement with the engine
    at every positive ambient budget is `errnoSeeded_eq`. -/
def σE1 : Mem :=
  CerbMem.writeBytesTo
    { CerbMem.initialMemState with
      nextAllocId := 1, lastUsed := some 0, lastAddress := errnoAddr,
      allocations := CerbMem.initialMemState.allocations.insert 0 errnoAllocRec }
    errnoAddr (List.replicate 4 undefByte)

theorem errnoSeeded_eq [LemFuel] (hfuel : 0 < LemFuel.fuel) :
    errnoSeeded = some (errnoPtr, σE1) :=
  allocateObject_success fmapEmpty CerbMem.initialMemState (PrefOther "errno")
    .Prov_none 4 signed_int hfuel (by decide) (by decide)

/-- The initial allocation has no active result at ambient zero. -/
theorem errnoSeeded_zero [LemFuel] (hzero : LemFuel.fuel = 0) : errnoSeeded = none := by
  unfold errnoSeeded CerbMem.allocateObject
  change applyMemM (nd_bind _ _) CerbMem.initialMemState = none
  exact applyMemM_bind_zero _ _ _ hzero

theorem errno_alloc_eq [LemFuel] (hfuel : 0 < LemFuel.fuel) :
    applyMemM (CerbMem.allocateObject fmapEmpty 0 (PrefOther "errno")
      (CerbMem.alignofIval fmapEmpty signed_int) signed_int none none)
      CerbMem.initialMemState = some (errnoPtr, σE1) := errnoSeeded_eq hfuel

theorem σE1_allocations :
    σE1.allocations = (({} : Mem).allocations.insert 0 errnoAllocRec) := rfl

theorem errno_alloc_get : σE1.allocations.get? 0 = some errnoAllocRec := by
  rw [σE1_allocations]
  simp

theorem errno_bytes_len (a : Int) :
    (CerbMem.readBytesFrom σE1 a 4).length = 4 := by
  unfold CerbMem.readBytesFrom
  simp

/-- errno's ghost-shaped cell in σE1 (only used to drive
    storeM_success — errno is never a fragment cell). -/
abbrev errnoCell : SpikeCell :=
  ⟨errnoAddr, signed_int, CerbMem.readBytesFrom σE1 errnoAddr 4⟩

theorem errnoCellCoh : CellCoh fmapEmpty σE1 0 errnoCell :=
  ⟨rfl, ⟨errnoAllocRec, errno_alloc_get, rfl, rfl, rfl, rfl⟩, rfl,
   by rw [show CerbMem.sizeofCtype fmapEmpty errnoCell.ty = 4 from rfl]; exact errno_bytes_len errnoAddr,
   by rw [show CerbMem.sizeofCtype fmapEmpty errnoCell.ty = 4 from rfl],
   fun _ _ => rfl⟩

theorem zero_storable {tds : CerbTags.TagDefsMap} : StorableAt tds signed_int zeroMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The memory state at fragment start: errno allocated and zeroed by
    the engine's own operations — the production cold-start memory. -/
def prodMem₀ : Mem :=
  CerbMem.writeBytesTo { σE1 with lastUsed := some 0 } errnoAddr (CerbMem.memValueToBytes fmapEmpty [] zeroMval).2

theorem errno_store_eq [LemFuel] :
    applyMemM (CerbMem.storeM fmapEmpty (CerbLocation.other "errno init") signed_int
      false errnoPtr zeroMval) σE1 =
      some (.FP .W errnoAddr (CerbMem.sizeofCtype fmapEmpty signed_int), prodMem₀) :=
  storeM_success fmapEmpty σE1 0 errnoCell zeroMval _ errnoCellCoh zero_storable

/-- The complete memory computation used by the driver to initialize
    errno, before it is lifted into driver state. -/
theorem errno_init_eq [LemFuel] (hfuel : 0 < LemFuel.fuel) :
    runOne
      (nd_bind (CerbMem.allocateObject fmapEmpty 0 (PrefOther "errno")
          (CerbMem.alignofIval fmapEmpty signed_int) signed_int none none)
        (fun ptr => nd_bind
          (CerbMem.storeM fmapEmpty (CerbLocation.other "errno init") signed_int
            false ptr zeroMval)
          (fun _ => nd_return ptr))) CerbMem.initialMemState =
      (NDactive errnoPtr, prodMem₀) := by
  refine (runOne_bind_active hfuel (z := errnoPtr) (s' := σE1)
    (runOne_of_applyMemM (errno_alloc_eq hfuel))).trans ?_
  refine (runOne_bind_active hfuel
    (z := CerbMem.Footprint.FP .W errnoAddr (CerbMem.sizeofCtype fmapEmpty signed_int))
    (s' := prodMem₀) (runOne_of_applyMemM errno_store_eq)).trans ?_
  rfl

/-! ## Launch coherence at the production cold start (the CONCRETE
instance; the generic theorem is `LaunchCoh.cohG` in Adequacy.lean,
which encodes neither the errno address nor any demo's future
allocations) -/

theorem prodMem₀_nextAllocId : prodMem₀.nextAllocId = 1 := rfl

theorem prodMem₀_lastAddress : prodMem₀.lastAddress = errnoAddr := rfl

theorem prodMem₀_allocations :
    prodMem₀.allocations =
      (({} : Mem).allocations.insert 0 errnoAllocRec) := rfl

theorem prodMem₀_deadAllocations : prodMem₀.deadAllocations = [] := rfl

theorem prodMem₀_dynamicAddrs : prodMem₀.dynamicAddrs = [] := rfl

/-- THE COLD-START INVARIANT (K0, acceptance goal 3): the production
    initial memory is globally well formed. errno (id 0, below
    `nextAllocId = 1`) is the ONLY allocation, at the cursor
    (`lastAddress = errnoAddr = errnoAllocRec.base`), of size 4;
    nothing is dead; no dynamic address; the cursor is below 2^64. -/
theorem prodMem₀_memWF : MemWF prodMem₀ := by
  have hget : ∀ id : Int, prodMem₀.allocations.get? id =
      if (0 : Int) = id then some errnoAllocRec
      else ({} : Mem).allocations.get? id := by
    intro id
    rw [prodMem₀_allocations]
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
  have hempty : ∀ id : Int, ({} : Mem).allocations.get? id = none := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id al hg
    rw [hget] at hg
    split at hg
    · next h0 =>
      rw [← h0, prodMem₀_nextAllocId]
      decide
    · rw [hempty] at hg
      cases hg
  · intro id hc
    rw [prodMem₀_deadAllocations] at hc
    cases hc
  · intro id al hg
    rw [prodMem₀_deadAllocations]
    rfl
  · intro i j ai aj hne hgi hgj
    rw [hget] at hgi hgj
    split at hgi
    · next hi =>
      split at hgj
      · next hj => exact absurd (hi.symm.trans hj) hne
      · rw [hempty] at hgj
        cases hgj
    · rw [hempty] at hgi
      cases hgi
  · intro id al hg
    rw [hget] at hg
    split at hg
    · obtain rfl := Option.some.inj hg
      rw [prodMem₀_lastAddress]
      exact Int.le_refl _
    · rw [hempty] at hg
      cases hg
  · intro id al hg
    rw [hget] at hg
    split at hg
    · obtain rfl := Option.some.inj hg
      decide
    · rw [hempty] at hg
      cases hg
  · rw [prodMem₀_lastAddress]
    decide
  · rw [prodMem₀_lastAddress]
    decide
  · intro a ha
    rw [prodMem₀_dynamicAddrs] at ha
    cases ha
  · intro a ha
    rw [prodMem₀_dynamicAddrs] at ha
    cases ha

/-- Bytes below the post-setup allocator cursor remain unspecified.
    Both setup writes start at the cursor and therefore leave this
    entire range unchanged from the actual empty initial memory. -/
theorem prodMem₀_unallocated : UnallocatedBytes prodMem₀ := by
  intro a ha
  rw [prodMem₀_lastAddress] at ha
  unfold prodMem₀
  rw [byteAt_writeBytesTo_out _ _ _ a (by omega)]
  change byteAt σE1 a = undefByte
  unfold σE1
  rw [byteAt_writeBytesTo_out _ _ _ a (by omega)]
  rfl

/-- Launch coherence at the production cold start: the invariant
    (`prodMem₀_memWF`), actual fresh-byte range, and any budget within the cursor's
    headroom (`errnoAddr − 1`) launches the empty footprint
    allocation-aware (K2.5; formerly a plan fitting the cursor). -/
theorem prodMem₀_launchCoh (B : Nat)
    (hB : B ≤ headroom prodMem₀.lastAddress) :
    LaunchCoh fmapEmpty prodMem₀ (∅ : SpikeHeapF SpikeCell) B :=
  LaunchCoh.empty fmapEmpty prodMem₀ B prodMem₀_memWF hB prodMem₀_unallocated

end CerberusHeapLang
