/-
CerberusHeapLang.Heap — the points-to over the engine's memory state,
on iris-lean's GenHeap.

THE GHOST CARRIER is the donor-shaped split (Caesium heap/allocs;
RefinedC theories/caesium/ghost_state.v is the reference): three
GenHeaps coupled to the real `CerbMem.MemState` by `CohG`.
- A per-BYTE heap (absolute address ↦ `AbsByte`, the ghost fragment
  of the engine's own bytemap), so sub-range ownership splits and
  joins at real ∗ (`bytesOwn`, `pointsToView`).
- A per-allocation METADATA heap (allocation id ↦ base/type/size) —
  the provenance authority: `loadM`/`storeM` success is decided by the
  allocation table (liveness, bounds, writability, atomicity —
  CerbMem.lean:1586-1696), so byte content alone can never entail
  access success; the metadata cell carries exactly those facts and
  is the per-allocation exclusivity anchor (`metaOwn`).
- A one-cell ALLOCATOR-CURSOR heap (`AllocCursor`: `lastAddress` and
  `nextAllocId`, the two `MemState` fields `allocateObject` reads and
  writes; `cursorOwn`). Without it `create`'s reducibility is
  unprovable from footprints; with it the out-of-memory arm is a pure
  guard on owned state.
The whole-allocation `pointsToCell` is the MAXIMAL VIEW (offset 0,
view type = allocation type) plus the image's decode-inertness fact;
`SpikeCell`/`Coh`/`CellCoh` are the PURE footprint vocabulary of the
exported engine-facing statements (`Sat`/`MemTripleU`).

THE TAG-DEFINITION ENVIRONMENT. The engine's memory functions take the
tag-definition environment as an explicit leading argument
(`sizeofCtype`, `memValueToBytes`, `reconstructValue`, `loadM`,
`storeM`, `allocateObject`, …; the engine passes its reader binder
`_lemReader_tagDefs`, Driver.lean:273). It is a program-wide constant
of the language instance (Caesium's global environment in RefinedC),
so every predicate here whose footprint depends on type LAYOUT is
indexed by it explicitly — `(tds : CerbTags.TagDefsMap)` on
`StorableAt`, `CellCoh`, `Coh`, `decIndep`, `pointsToView`, `cellOwn`,
`pointsToCell`, `advanceCursor`, `PlanFits`, `allocCap` and the memory
lemmas — and the rules generic in a `MachineCtx` supply `M.tagDefs`
(the mirror's `Step.store/load/create` use `M.tagDefs` exactly as the
engine uses its reader). The STATE INTERPRETATION computes no layout:
the ghost metadata cell records the allocation's `size` as ghost data
(the engine's own `Allocation.size`, registered by `allocateObject`),
so `CohG` needs no environment and the Iris instance stays a plain
instance; the assertions pin `size = sizeofCtype tds ty`. Clients
state their footprints at the program's environment (`fmapEmpty` for
every demo — `spikeCtx`/`procCtx` are reducible, so `M.tagDefs`
unfolds to it under the proof mode's matching).

THE THREE ALLOCATION FACTS (after RefinedC's ghost_state.v split
heap_mapsto / loc_in_bounds / alloc_alive):
1. LINEAR/FRACTIONAL BYTES — the per-byte heap: `bytesOwn`, split at
   any list decomposition (`bytesOwn_append`) and at any fraction sum
   (`bytesOwn_fractional`), agreeing on contents (`bytesOwn_agree`).
2. PERSISTENT ALLOCATION KNOWLEDGE — id, base, allocation type, size
   and in-bounds facts, all read off the IMMUTABLE metadata cell:
   `allocMeta`/`locInBounds` (the metadata cell at the discarded
   fraction; the `Persistent` instances are the persistence law). Any
   view's metadata fraction can be traded for it
   (`pointsToView_persist`), and a persistent-metadata view yields its
   bounds knowledge without giving anything up
   (`pointsToView_locInBounds`). The bundles (`pointsToView`,
   `cellOwn`, `pointsToCell`) keep the metadata at a FRACTION `dqm`
   because full metadata ownership is the per-allocation EXCLUSIVITY
   anchor the frame theorem needs (`metaOwn_ne` →
   `bigSepM_own_disjoint`, Adequacy.lean) — a deliberate divergence
   from the donor, where the anchor is the killable `alloc_alive`.
3. NO LIVENESS/FREEABILITY TOKEN. kill/free is outside the fragment:
   METADATA IS IMMUTABLE — no rule updates a metadata cell
   (`metaHeap_alloc` mints; nothing writes) — so knowledge about an
   allocation, once obtained, holds forever, and there is no token to
   guard a deallocation that cannot happen. Named mover: when kill
   joins the fragment, the metadata heap gains the donor's
   alloc_alive/freeable split and the exclusivity anchor moves there.

STATE INTERPRETATION (memory only — no driver state):
`stateInterp σ _ _ _ := ∃ mm mb mk, ⌜CohG σ mm mb mk⌝ ∗ interps` over
the real `CerbMem.MemState`. `CohG` couples: byte cells to the bytemap
readout; metadata cells to live/writable/typed/non-atomic allocations,
pairwise range-disjoint; the cursor cell (key 0) to
`lastAddress`/`nextAllocId`, its PRESENCE carrying THE GLOBAL MEMORY
WELL-FORMEDNESS INVARIANT `MemWF σ` (`CohG.wf`) plus the one ghost-side
bound (tracked bytes at or above the cursor, `cur_byte_lo`) —
cursor-free launches owe nothing new. The allocation-aware launchers
(`launchResources`, Adequacy.lean, under `LaunchCoh`, whose `wf` field
is `MemWF σ`) mint the cursor cell and grant the abstract capacity
`allocCap` (this file) to the public create rules; the cursor-free
launchers remain for programs that do not allocate. FRESHNESS IS
GLOBAL (K0, acceptance goal 3): `MemWF` (section "The global memory
well-formedness invariant") states allocation-id discipline, live/dead
consistency, pairwise range disjointness of ALL live allocations, the
cursor bounds and the dynamic-address facts as engine facts about the
concrete allocation model, so a `create` is fresh from EVERY live
allocation of the state, tracked or not (`create_fresh_global`); the
production cold-start state satisfies it (`prodMem₀_memWF`,
ProdEntry.lean); `loadM`/`storeM`/`allocateObject` preserve it
(`MemWF.loadM`/`MemWF.storeM`/`MemWF.allocateObject`); `allocateRegion`
and `killM` are K3's stated obligations. `allocCap reqs` is an ORDERED REQUEST PLAN over
the exclusive cursor (`PlanFits`, whose guard is exactly
`allocateObject_success`'s premise pair), weakened only to a prefix
(`allocCap_weaken`) and never split across ∗ — the register row and
walkthrough §4 state the cost and the additive alternative. The
union-member/function-pointer side tables are SYMBOLIC (read-only
context): decode-inertness rides as a pure payload of `pointsToCell`
(`decIndep`; per-view decode premises on the generic rules), and
`StorableAt` carries the serialization-side analogues. For scalar and
integer-array images all of these are `rfl`.

Also here: the engine-memory success lemmas the rule proofs run —
`storeM_success`, `loadM_success`, `storeM_at`, `loadM_at`,
`allocateObject_success` — and the byte-map algebra
(`writeBytesTo_*`, `readBytesFrom_*`, `spliceBytes_*`).
-/
import Iris
import CerberusHeapLang.Step

set_option autoImplicit false

namespace CerberusHeapLang

open Iris

/-- The ghost-map functor (HeapLang's shape, Semantics.lean:127). -/
abbrev SpikeHeapF := fun (V : Type) => Std.ExtTreeMap Int V compare

/-- One allocation-rooted ghost cell: base address, C type, and the
    byte-list contents of the allocation's bytemap slice. -/
structure SpikeCell where
  addr : Int
  ty : ctype
  bytes : List CerbMem.AbsByte

/-- The fragment pointer shape: exactly what `allocateObject` returns
    (CerbMem.lean:1496) — provenance id + concrete address, no union
    member. R5: both components are load-bearing for loadM/storeM. -/
def cellPtr (id : Int) (a : Int) : CerbMem.PointerValue :=
  .PV (.Prov_some id) (.PVconcrete none a)

/-- Engine decode of a cell: `reconstructValue` (CerbMem.lean:774) at
    EMPTY side tables — the canonical decode; `CellCoh.dec_indep`
    says the cell decodes the same at ANY tables. The engine's own
    decoder, not a new one. -/
def decodeCell (tds : CerbTags.TagDefsMap) (c : SpikeCell) : CerbMem.MemValue :=
  CerbMem.reconstructValue tds [] [] c.addr c.ty c.bytes

/-- Mirror of loadM's `isBool` (CerbMem.lean:1598). -/
def boolTy : ctype → Bool
  | Ctype _ (.Basic (.Integer .Bool0)) => true
  | _ => false

/-- Mirror of loadM's `isTrap` guard (CerbMem.lean:1598-1604): the
    _Bool trap-representation UB arm. wp_load's precondition excludes
    it (R4: UB-excluding — this is one of the NDkilled arms). -/
def cellLoadTrap (tds : CerbTags.TagDefsMap) (c : SpikeCell) : Bool :=
  boolTy c.ty &&
    (match decodeCell tds c with
     | .MVinteger _ (.IV _ n) => n != 0 && n != 1
     | .MVunspecified _ => true
     | _ => false)

/-- Root atomicity test — feeds `isAtomicMemberAccess`
    (CerbMem.lean:1575-1585): a non-atomic cell type makes the
    atomic-member arm unreachable. -/
def atomicTy : ctype → Bool
  | Ctype _ (.Atomic _) => true
  | _ => false

/-- The pure facts about a (type, value) pair that make a store of
    `mv` at type `ty` succeed and preserve the coupling invariant.
    This is the spike-scale precursor of the donor's `v ◁ᵥ ty` value
    judgment (R2/R-viii — in the full build the typing stratum
    supplies exactly these):
    - `compat` excludes storeM's non-UB `Other` kill arm
      (`MerrOther "store with an ill-typed memory value"`,
      CerbMem.lean:1666 — checked FIRST, before pointer kind);
    - `fpm` says serialization adds no function-pointer entries
      (memValueToBytes threads funptrmap, CerbMem.lean:639);
    - `len` says the serialized image fills the type's footprint
      exactly (needed to re-read the cell and to leave neighbours
      untouched). All three are closed computations on concrete
      integer values (rfl-provable). -/
structure StorableAt (tds : CerbTags.TagDefsMap) (ty : ctype) (mv : CerbMem.MemValue) : Prop where
  compat : CerbMem.ctypeMemCompatible ty (CerbMem.typeofMval mv) = true
  fpm : ∀ fpm, (CerbMem.memValueToBytes tds fpm mv).1 = fpm
  len : ∀ fpm, ((CerbMem.memValueToBytes tds fpm mv).2).length = CerbMem.sizeofCtype tds ty
  /-- serialization is table-independent (storeM serializes at the
      state's CURRENT funptrmap, CerbMem.lean:1632/639; scalar
      values produce the same bytes at any table). -/
  bytes_fpm : ∀ fpm, (CerbMem.memValueToBytes tds fpm mv).2 =
    (CerbMem.memValueToBytes tds [] mv).2
  /-- the stored image decodes table-independently (feeds the written
      cell's `CellCoh.dec_indep`). -/
  stored_dec : ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap)
    (addr : Int),
    CerbMem.reconstructValue tds lum fpm addr ty (CerbMem.memValueToBytes tds [] mv).2 =
      CerbMem.reconstructValue tds [] [] addr ty (CerbMem.memValueToBytes tds [] mv).2

/-- The storability facts a TYPED-SUBRANGE store needs (QA-1/Q5 — the
    one vocabulary of the `*_store_at`/`*_store_cell_at` rules): the
    first four fields of `StorableAt`, without the write-side decode
    inertness `stored_dec` (which only the whole-cell rules consume,
    through `StorableAt`). `StorableAt.toView` is the forgetful map. -/
structure StorableView (tds : CerbTags.TagDefsMap) (ty : ctype) (mv : CerbMem.MemValue) : Prop where
  compat : CerbMem.ctypeMemCompatible ty (CerbMem.typeofMval mv) = true
  fpm : ∀ fpm, (CerbMem.memValueToBytes tds fpm mv).1 = fpm
  bytes_fpm : ∀ fpm, (CerbMem.memValueToBytes tds fpm mv).2 =
    (CerbMem.memValueToBytes tds [] mv).2
  len : ((CerbMem.memValueToBytes tds [] mv).2).length = CerbMem.sizeofCtype tds ty

theorem StorableAt.toView {tds : CerbTags.TagDefsMap} {ty : ctype} {mv : CerbMem.MemValue}
    (h : StorableAt tds ty mv) : StorableView tds ty mv :=
  ⟨h.compat, h.fpm, h.bytes_fpm, h.len []⟩

/-! ## The null-test memM facts (list-reverse phase A)

The honest null encoding: the engine's null pointer is
`nullPtrval ty = PV Prov_none (PVnull ty)` (CerbMem.lean:843), and
the engine's own pointer-equality memop `eqPtrval`
(CerbMem.lean:1731, mirroring impl_mem.ml:1830-1881 arm-for-arm)
answers the null test PURELY on the fragment's operand shapes:
- null vs null → `memReturn true` (impl_mem.ml:1832-1833);
- an allocation-backed concrete pointer (`cellPtr` — what
  `allocateObject` returns and what a load of stored pointer bytes
  reconstructs) vs null, either order → `memReturn false`
  (impl_mem.ml:1834-1836).
All three are single-layer active memM computations returning the
state verbatim — `applyMemM` shape by `rfl`. The remaining arms
(function pointers; the differing-provenance concrete/concrete
`msum` ND fork) are NOT single-layer and stay fail-closed outside
the mirror (Step.lean, `Step.memop_ptreq`). -/

theorem eqPtrval_null_null (t1 t2 : ctype) (σ : Mem) :
    applyMemM (CerbMem.eqPtrval default (CerbMem.nullPtrval t1)
      (CerbMem.nullPtrval t2)) σ = some (true, σ) := rfl

theorem eqPtrval_cell_null (id a : Int) (t : ctype) (σ : Mem) :
    applyMemM (CerbMem.eqPtrval default (cellPtr id a)
      (CerbMem.nullPtrval t)) σ = some (false, σ) := rfl

theorem eqPtrval_null_cell (t : ctype) (id a : Int) (σ : Mem) :
    applyMemM (CerbMem.eqPtrval default (CerbMem.nullPtrval t)
      (cellPtr id a)) σ = some (false, σ) := rfl

/-! ## Pure bytemap lemmas (writeBytesTo/readBytesFrom, CerbMem.lean:1420-1431) -/

section Bytemap

open CerbMem

private theorem wfold_get? (bs : List AbsByte)
    (m : Std.TreeMap Int AbsByte) (a k : Int) :
    ((bs.foldl (fun (acc : Std.TreeMap Int AbsByte × Int) b =>
        (acc.1.insert acc.2 b, acc.2 + 1)) (m, a)).1).get? k =
      if a ≤ k ∧ k < a + bs.length then bs[(k - a).toNat]? else m.get? k := by
  induction bs generalizing m a with
  | nil =>
    have h : ¬(a ≤ k ∧ k < a + (([] : List AbsByte).length : Int)) := by
      simp only [List.length_nil]; omega
    simp only [List.foldl_nil, if_neg h]
  | cons b bs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    have hins : (m.insert a b).get? k = if a = k then some b else m.get? k := by
      simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
    by_cases hk : k = a
    · rw [hk] at hins ⊢
      rw [if_neg (by omega), hins, if_pos rfl, if_pos (by omega),
        show (a - a).toNat = 0 from by omega]
      rfl
    · by_cases h1 : a + 1 ≤ k ∧ k < a + 1 + (bs.length : Int)
      · rw [if_pos h1, if_pos (by omega),
          show (k - a).toNat = (k - (a + 1)).toNat + 1 by omega]
        rfl
      · rw [if_neg h1, hins, if_neg (fun h => hk h.symm), if_neg (by omega)]

theorem writeBytesTo_bytemap_get? (st : Mem) (a : Int) (bs : List AbsByte)
    (k : Int) :
    (writeBytesTo st a bs).bytemap.get? k =
      if a ≤ k ∧ k < a + bs.length then bs[(k - a).toNat]? else st.bytemap.get? k := by
  simpa [writeBytesTo] using wfold_get? bs st.bytemap a k

@[simp] theorem writeBytesTo_allocations (st : Mem) (a : Int) (bs : List AbsByte) :
    (writeBytesTo st a bs).allocations = st.allocations := rfl

@[simp] theorem writeBytesTo_deadAllocations (st : Mem) (a : Int) (bs : List AbsByte) :
    (writeBytesTo st a bs).deadAllocations = st.deadAllocations := rfl

@[simp] theorem writeBytesTo_funptrmap (st : Mem) (a : Int) (bs : List AbsByte) :
    (writeBytesTo st a bs).funptrmap = st.funptrmap := rfl

@[simp] theorem writeBytesTo_lastUsedUnionMembers (st : Mem) (a : Int)
    (bs : List AbsByte) :
    (writeBytesTo st a bs).lastUsedUnionMembers = st.lastUsedUnionMembers := rfl

theorem readBytesFrom_writeBytesTo_self (st : Mem) (a : Int) (bs : List AbsByte) :
    readBytesFrom (writeBytesTo st a bs) a bs.length = bs := by
  unfold readBytesFrom
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < bs.length := h2
    simp only [List.getElem_map, List.getElem_range]
    have hget : (writeBytesTo st a bs).bytemap.get? (a + (i : Int)) = some bs[i] := by
      rw [writeBytesTo_bytemap_get?, if_pos (by omega)]
      rw [show ((a + (i : Int)) - a).toNat = i by omega]
      exact List.getElem?_eq_getElem hi
    rw [hget]

theorem readBytesFrom_writeBytesTo_disjoint (st : Mem) (a : Int)
    (bs : List AbsByte) (a' : Int) (n : Nat)
    (h : a' + n ≤ a ∨ a + bs.length ≤ a') :
    readBytesFrom (writeBytesTo st a bs) a' n = readBytesFrom st a' n := by
  unfold readBytesFrom
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := by simpa using hi
  have hout : ¬(a ≤ a' + i ∧ a' + (i : Int) < a + bs.length) := by omega
  rw [writeBytesTo_bytemap_get?, if_neg hout]

theorem MemState.set_funptrmap_self (σ : Mem) :
    ({ σ with funptrmap := σ.funptrmap } : Mem) = σ := rfl

end Bytemap

/-! ## The coupling invariant -/

open Iris.Std.PartialMap in
/-- Per-cell backing facts in the real memory state. -/
structure CellCoh (tds : CerbTags.TagDefsMap) (σ : Mem) (id : Int) (c : SpikeCell) : Prop where
  dead : σ.deadAllocations.contains id = false
  alloc : ∃ al, σ.allocations.get? id = some al ∧ al.base = c.addr ∧
    al.size = (CerbMem.sizeofCtype tds c.ty : Int) ∧ al.ty = some c.ty ∧
    al.isReadonly = .IsWritable
  nonAtomic : atomicTy c.ty = false
  len : c.bytes.length = CerbMem.sizeofCtype tds c.ty
  bytes : CerbMem.readBytesFrom σ c.addr (CerbMem.sizeofCtype tds c.ty) = c.bytes
  /-- INERTNESS ([USER 2026-08-30], the de-pin): the cell's decode is
      independent of the union-member and function-pointer side
      tables — exactly what loadM's value reconstruction reads them
      for (reconstructValue, CerbMem.lean:652: the unionmap enters
      only union arms, the funptrmap only pointer-byte arms). Under
      this premise the tables are READ-ONLY context (arbitrary,
      returned verbatim); for scalar cells the premise is `fun _ _ =>
      rfl`. The full-build shape is ghost ownership of the tables
      (funptrmap ↔ the donor's fntbl_entry analog); this premise is
      its degenerate case. -/
  dec_indep : ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap),
    CerbMem.reconstructValue tds lum fpm c.addr c.ty c.bytes = decodeCell tds c

def cellsDisjoint (tds : CerbTags.TagDefsMap) (c1 c2 : SpikeCell) : Prop :=
  c1.addr + (CerbMem.sizeofCtype tds c1.ty : Int) ≤ c2.addr ∨
  c2.addr + (CerbMem.sizeofCtype tds c2.ty : Int) ≤ c1.addr

open Iris.Std.PartialMap in
/-- The coupling invariant between the real MemState and the ghost
    cell map. -/
structure Coh (tds : CerbTags.TagDefsMap) (σ : Mem) (m : SpikeHeapF SpikeCell) : Prop where
  cells : ∀ id c, get? m id = some c → CellCoh tds σ id c
  disj : ∀ id1 id2 c1 c2, id1 ≠ id2 → get? m id1 = some c1 →
    get? m id2 = some c2 → cellsDisjoint tds c1 c2

/-! ## The memM computations under the invariant

These are the engine-unfolding facts wp_load/wp_store discharge into:
one-level applications of the real loadM/storeM (recon §5.4 seam (a)).
-/

/-- A non-atomic cell type makes the atomic-member arm
    (CerbMem.lean:1575-1585) unreachable. -/
theorem isAtomicMemberAccess_false (tds : CerbTags.TagDefsMap) (al : CerbMem.Allocation) (ty : ctype)
    (addr : Int) (hty : al.ty = some ty) (hatom : atomicTy ty = false) :
    CerbMem.isAtomicMemberAccess tds al ty addr = false := by
  unfold CerbMem.isAtomicMemberAccess
  rw [hty]
  cases ty with
  | Ctype q t => cases t <;> simp_all [atomicTy]

/-- Successful store: with a Coh-backed cell and a `StorableAt` value,
    `storeM` (CerbMem.lean:1632) takes exactly the active path and the
    state change is the byte write. Every guard the proof crosses is
    one NDkilled arm of the R4 vocabulary (recon §2.6), discharged by
    a named hypothesis. -/
theorem storeM_success (tds : CerbTags.TagDefsMap) (σ : Mem) (id : Int) (c : SpikeCell)
    (mv : CerbMem.MemValue) (loc : CerbLocation.Loc)
    (hcoh : CellCoh tds σ id c) (hst : StorableAt tds c.ty mv) :
    applyMemM (CerbMem.storeM tds loc c.ty false (cellPtr id c.addr) mv) σ =
      some (.FP .W c.addr (CerbMem.sizeofCtype tds c.ty),
        CerbMem.writeBytesTo σ c.addr (CerbMem.memValueToBytes tds [] mv).2) := by
  obtain ⟨al, hal, hbase, hsize, hty, hro⟩ := hcoh.alloc
  have hbounds : CerbMem.isInBounds al c.addr (CerbMem.sizeofCtype tds c.ty) = true := by
    simp [CerbMem.isInBounds, hbase, hsize]
  have hatomic := isAtomicMemberAccess_false tds al c.ty c.addr hty hcoh.nonAtomic
  rcases hmvb : CerbMem.memValueToBytes tds σ.funptrmap mv with ⟨fpm', bs'⟩
  have hfpm' : fpm' = σ.funptrmap := by
    have := hst.fpm σ.funptrmap
    rw [hmvb] at this
    exact this
  have hbs' : bs' = (CerbMem.memValueToBytes tds [] mv).2 := by
    have := hst.bytes_fpm σ.funptrmap
    rw [hmvb] at this
    exact this
  subst hfpm' hbs'
  unfold CerbMem.storeM applyMemM
  simp only [hst.compat, Bool.not_true, Bool.false_eq_true, if_false, cellPtr,
    hal, hbounds, hro, hatomic, hmvb]

/-- Successful load: with a Coh-backed cell that is not a _Bool trap,
    `loadM` (CerbMem.lean:1586) takes the active path, returns the
    cell's decode, and leaves the state unchanged. -/
theorem loadM_success (tds : CerbTags.TagDefsMap) (σ : Mem) (id : Int) (c : SpikeCell)
    (loc : CerbLocation.Loc)
    (hcoh : CellCoh tds σ id c) (htrap : cellLoadTrap tds c = false) :
    applyMemM (CerbMem.loadM tds loc c.ty (cellPtr id c.addr)) σ =
      some ((.FP .R c.addr (CerbMem.sizeofCtype tds c.ty), decodeCell tds c), σ) := by
  obtain ⟨al, hal, hbase, hsize, hty, hro⟩ := hcoh.alloc
  have hbounds : CerbMem.isInBounds al c.addr (CerbMem.sizeofCtype tds c.ty) = true := by
    simp [CerbMem.isInBounds, hbase, hsize]
  have hatomic := isAtomicMemberAccess_false tds al c.ty c.addr hty hcoh.nonAtomic
  have hdec : CerbMem.reconstructValue tds σ.lastUsedUnionMembers σ.funptrmap c.addr
      c.ty (CerbMem.readBytesFrom σ c.addr (CerbMem.sizeofCtype tds c.ty)) =
      decodeCell tds c := by
    rw [hcoh.bytes]
    exact hcoh.dec_indep _ _
  unfold CerbMem.loadM applyMemM
  simp only [cellPtr, hcoh.dead, Bool.false_eq_true, if_false, hal, hbounds,
    Bool.not_true, hatomic, hdec]
  -- the trap guard is the last gate. The hypothesis's matcher and the
  -- unfolded loadM's matcher are distinct constants stuck on the same
  -- scrutinees, so no defeq/simp bridge exists; case-explode the
  -- scrutinees until both reduce.
  unfold cellLoadTrap boolTy at htrap
  generalize decodeCell tds c = mval at htrap ⊢
  clear hdec hatomic hbounds hro hty hsize hbase hal al hcoh
  rcases c with ⟨ca, ⟨q, t⟩, cb⟩ <;> cases t <;> try simp_all
  rename_i bt
  cases bt <;> try simp_all
  rename_i ity
  cases ity <;> try simp_all
  cases mval <;> try simp_all
  rename_i iv
  cases iv
  simp_all
  rw [if_neg (fun hcond => by
    obtain ⟨h1, h2⟩ := hcond
    rw [htrap h1] at h2
    cases h2)]

/-- Interior slice of a whole-cell read (S4, the array exhibit):
    the byte image of a sub-range is the corresponding list slice. -/
theorem readBytesFrom_sub (σ : Mem) (a : Int) (m : Nat)
    (bs : List CerbMem.AbsByte)
    (hread : CerbMem.readBytesFrom σ a m = bs) (off k : Nat)
    (hok : off + k ≤ m) :
    CerbMem.readBytesFrom σ (a + (off : Int)) k = (bs.drop off).take k := by
  rw [← hread]
  unfold CerbMem.readBytesFrom
  apply List.ext_getElem
  · simp
    omega
  · intro j h1 h2
    have hj : j < k := by simpa using h1
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map,
      List.getElem_range]
    rw [show a + ((off : Int)) + (j : Int) = a + (((off + j : Nat)) : Int)
      by omega]

/-- Coh survives a Coh-backed store: the touched cell re-reads to the
    written image (exact footprint), the untouched cells are outside
    the written range (pairwise disjointness), the allocation table
    and the pinned side tables are untouched (isLocking = false,
    unionMem = none, funptrmap-neutral serialization). -/
theorem Coh.store (tds : CerbTags.TagDefsMap) (σ : Mem) (m : SpikeHeapF SpikeCell) (i : Int)
    (c : SpikeCell) (mv : CerbMem.MemValue)
    (hcoh : Coh tds σ m) (hget : Iris.Std.PartialMap.get? m i = some c)
    (hst : StorableAt tds c.ty mv) :
    Coh tds (CerbMem.writeBytesTo σ c.addr (CerbMem.memValueToBytes tds [] mv).2)
      (Iris.Std.PartialMap.insert m i
        ⟨c.addr, c.ty, (CerbMem.memValueToBytes tds [] mv).2⟩) := by
  generalize hbs : (CerbMem.memValueToBytes tds [] mv).2 = bs
  have hlen : bs.length = CerbMem.sizeofCtype tds c.ty := by
    rw [← hbs]; exact hst.len []
  have hcell' : ∀ j c', Iris.Std.PartialMap.get?
      (Iris.Std.PartialMap.insert m i (⟨c.addr, c.ty, bs⟩ : SpikeCell)) j =
        some c' →
      (j = i ∧ c' = ⟨c.addr, c.ty, bs⟩) ∨
      (j ≠ i ∧ Iris.Std.PartialMap.get? m j = some c') := by
    intro j c' h
    by_cases hid : j = i
    · subst hid
      rw [Iris.Std.get?_insert_eq rfl] at h
      exact .inl ⟨rfl, (Option.some.inj h).symm⟩
    · rw [Iris.Std.get?_insert_ne (fun h' => hid h'.symm)] at h
      exact .inr ⟨hid, h⟩
  refine ⟨?_, ?_⟩
  · intro j c' h
    rcases hcell' j c' h with ⟨rfl, rfl⟩ | ⟨hne, hold⟩
    · have hc := hcoh.cells _ c hget
      refine ⟨by simpa using hc.dead, ?_, hc.nonAtomic, hlen, ?_, ?_⟩
      · obtain ⟨al, hal, h1, h2, h3, h4⟩ := hc.alloc
        exact ⟨al, by simpa using hal, h1, h2, h3, h4⟩
      · show CerbMem.readBytesFrom (CerbMem.writeBytesTo σ c.addr bs) c.addr
          (CerbMem.sizeofCtype tds c.ty) = bs
        rw [← hlen]
        exact readBytesFrom_writeBytesTo_self σ c.addr bs
      · intro lum fpm
        show CerbMem.reconstructValue tds lum fpm c.addr c.ty bs = _
        rw [← hbs]
        exact hst.stored_dec lum fpm c.addr
    · have hc := hcoh.cells j c' hold
      have hdisj := hcoh.disj _ _ c' c hne hold hget
      refine ⟨by simpa using hc.dead, ?_, hc.nonAtomic, hc.len, ?_, hc.dec_indep⟩
      · obtain ⟨al, hal, h1, h2, h3, h4⟩ := hc.alloc
        exact ⟨al, by simpa using hal, h1, h2, h3, h4⟩
      · show CerbMem.readBytesFrom (CerbMem.writeBytesTo σ c.addr bs) c'.addr
          (CerbMem.sizeofCtype tds c'.ty) = c'.bytes
        rw [readBytesFrom_writeBytesTo_disjoint _ _ _ _ _ ?_]
        · exact hc.bytes
        · simp only [cellsDisjoint] at hdisj
          omega
  · intro j1 j2 c1 c2 hne h1 h2
    rcases hcell' j1 c1 h1 with ⟨rfl, rfl⟩ | ⟨hne1, hold1⟩ <;>
      rcases hcell' j2 c2 h2 with ⟨rfl, rfl⟩ | ⟨hne2, hold2⟩
    · exact absurd rfl hne
    · have h := hcoh.disj _ _ c c2 (fun h => hne2 h.symm) hget hold2
      simp only [cellsDisjoint] at h ⊢
      omega
    · have h := hcoh.disj _ _ c1 c hne1 hold1 hget
      simp only [cellsDisjoint] at h ⊢
      omega
    · exact hcoh.disj j1 j2 c1 c2 hne hold1 hold2

/-! ## Byte-splice algebra (Phase 2: generalized from the listrev
slice — the interior-store byte lemmas, now core and layout-free) -/

section Splice

open CerbMem

/-- The byte splice an interior store performs on a cell image. -/
def spliceBytes (off : Nat) (img bs : List AbsByte) : List AbsByte :=
  bs.take off ++ img ++ bs.drop (off + img.length)

theorem spliceBytes_length (off : Nat) (img bs : List AbsByte)
    (h : off + img.length ≤ bs.length) :
    (spliceBytes off img bs).length = bs.length := by
  simp [spliceBytes]
  omega

/-- Pointwise characterization of the splice. -/
theorem spliceBytes_getElem? (off : Nat) (img bs : List AbsByte)
    (hb : off + img.length ≤ bs.length) (k : Nat) :
    (spliceBytes off img bs)[k]? =
      if k < off then bs[k]?
      else if k < off + img.length then img[k - off]?
      else bs[k]? := by
  have hto : (bs.take off).length = off := by simp; omega
  have htoi : (bs.take off ++ img).length = off + img.length := by
    simp; omega
  unfold spliceBytes
  by_cases h1 : k < off
  · rw [if_pos h1,
      List.getElem?_append_left (by rw [htoi]; omega),
      List.getElem?_append_left (by rw [hto]; omega),
      List.getElem?_take, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : k < off + img.length
    · rw [if_pos h2,
        List.getElem?_append_left (by rw [htoi]; omega),
        List.getElem?_append_right (by rw [hto]; omega), hto]
    · rw [if_neg h2,
        List.getElem?_append_right (by rw [htoi]; omega), htoi,
        List.getElem?_drop]
      congr 1
      omega

/-- The interior write re-reads as the splice of the old image. -/
theorem readBytesFrom_write_interior (σ : Mem) (a : Int) (off : Nat)
    (img : List AbsByte) (n : Nat) (bs : List AbsByte)
    (hread : readBytesFrom σ a n = bs)
    (hb : off + img.length ≤ n) :
    readBytesFrom (writeBytesTo σ (a + (off : Int)) img) a n =
      spliceBytes off img bs := by
  have hbs : bs.length = n := by
    rw [← hread]; simp [readBytesFrom]
  apply List.ext_getElem?
  intro k
  by_cases hk : k < n
  · have hchar : ∀ (τ : Mem), (readBytesFrom τ a n)[k]? =
        some (match τ.bytemap.get? (a + (k : Int)) with
              | some b => b
              | none => { prov := .Prov_none, copyOffset := none,
                          value := none }) := by
      intro τ
      simp only [readBytesFrom, List.getElem?_map,
        List.getElem?_range hk, Option.map_some]
      rfl
    have hbsk : bs[k]? = some (match σ.bytemap.get? (a + (k : Int)) with
        | some b => b
        | none => { prov := .Prov_none, copyOffset := none,
                    value := none }) := by
      rw [← hread]
      exact hchar σ
    rw [hchar, spliceBytes_getElem? off img bs (by omega) k,
      writeBytesTo_bytemap_get?]
    by_cases hin : off ≤ k ∧ k < off + img.length
    · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show ((a + (k : Int)) - (a + (off : Int))).toNat = k - off by omega]
      rw [List.getElem?_eq_getElem (by omega : k - off < img.length)]
    · rw [if_neg (by omega)]
      have hout : (if k < off then bs[k]? else
          if k < off + img.length then img[k - off]? else bs[k]?) = bs[k]? := by
        by_cases h1 : k < off
        · rw [if_pos h1]
        · rw [if_neg h1, if_neg (by omega)]
      rw [hout, hbsk]
  · have hL : (readBytesFrom
        (writeBytesTo σ (a + (off : Int)) img) a n).length = n := by
      simp [readBytesFrom]
    have hR : (spliceBytes off img bs).length = n := by
      rw [spliceBytes_length off img bs (by omega)]
      exact hbs
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- A sub-slice strictly BELOW the spliced range is untouched
    (generalizes the listrev value-slice instance). -/
theorem spliceBytes_slice_below (off : Nat) (img bs : List AbsByte)
    (hb : off + img.length ≤ bs.length) (o' n : Nat) (h : o' + n ≤ off) :
    ((spliceBytes off img bs).drop o').take n = (bs.drop o').take n := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_drop]
  by_cases hk : k < n
  · rw [if_pos hk, if_pos hk, spliceBytes_getElem? off img bs hb (o' + k),
      if_pos (by omega)]
  · rw [if_neg hk, if_neg hk]

/-- The spliced range re-reads as exactly the image (generalizes the
    listrev next-slice instance). -/
theorem spliceBytes_slice_self (off : Nat) (img bs : List AbsByte)
    (hb : off + img.length ≤ bs.length) :
    ((spliceBytes off img bs).drop off).take img.length = img := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_drop]
  by_cases hk : k < img.length
  · rw [if_pos hk, spliceBytes_getElem? off img bs hb (off + k),
      if_neg (by omega), if_pos (by omega)]
    congr 1
    omega
  · rw [if_neg hk, List.getElem?_eq_none (by omega)]

/-- A sub-slice strictly ABOVE the spliced range is untouched. -/
theorem spliceBytes_slice_above (off : Nat) (img bs : List AbsByte)
    (hb : off + img.length ≤ bs.length) (o' n : Nat)
    (h : off + img.length ≤ o') :
    ((spliceBytes off img bs).drop o').take n = (bs.drop o').take n := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_drop]
  by_cases hk : k < n
  · rw [if_pos hk, if_pos hk, spliceBytes_getElem? off img bs hb (o' + k),
      if_neg (by omega), if_neg (by omega)]
  · rw [if_neg hk, if_neg hk]

/-- Coh survives an interior store into a Coh-backed cell (moved from
    the listrev slice — layout-free): the touched cell's image is
    spliced, other cells are outside the written sub-range, the
    allocation and side tables untouched. `hdec_indep` is the spliced
    image's table-independent decode. -/
theorem Coh.store_interior (tds : CerbTags.TagDefsMap) (σ : Mem) (m : SpikeHeapF SpikeCell) (i : Int)
    (c : SpikeCell) (off : Nat) (img : List AbsByte)
    (hcoh : Coh tds σ m) (hget : Iris.Std.PartialMap.get? m i = some c)
    (hbound : off + img.length ≤ sizeofCtype tds c.ty)
    (hdec_indep : ∀ (lum : List (Int × identifier)) (fpm : Funptrmap),
      reconstructValue tds lum fpm c.addr c.ty (spliceBytes off img c.bytes) =
        decodeCell tds ⟨c.addr, c.ty, spliceBytes off img c.bytes⟩) :
    Coh tds (writeBytesTo σ (c.addr + (off : Int)) img)
      (Iris.Std.PartialMap.insert m i
        ⟨c.addr, c.ty, spliceBytes off img c.bytes⟩) := by
  have hlenb : c.bytes.length = sizeofCtype tds c.ty := (hcoh.cells i c hget).len
  have hlen : (spliceBytes off img c.bytes).length = sizeofCtype tds c.ty := by
    rw [spliceBytes_length off img c.bytes (by omega)]
    exact hlenb
  have hreread : readBytesFrom
      (writeBytesTo σ (c.addr + (off : Int)) img) c.addr
      (sizeofCtype tds c.ty) = spliceBytes off img c.bytes :=
    readBytesFrom_write_interior σ c.addr off img (sizeofCtype tds c.ty)
      c.bytes (hcoh.cells i c hget).bytes hbound
  have hcell' : ∀ j c', Iris.Std.PartialMap.get?
      (Iris.Std.PartialMap.insert m i
        (⟨c.addr, c.ty, spliceBytes off img c.bytes⟩ : SpikeCell)) j =
        some c' →
      (j = i ∧ c' = ⟨c.addr, c.ty, spliceBytes off img c.bytes⟩) ∨
      (j ≠ i ∧ Iris.Std.PartialMap.get? m j = some c') := by
    intro j c' h
    by_cases hid : j = i
    · subst hid
      rw [Iris.Std.get?_insert_eq rfl] at h
      exact .inl ⟨rfl, (Option.some.inj h).symm⟩
    · rw [Iris.Std.get?_insert_ne (fun h' => hid h'.symm)] at h
      exact .inr ⟨hid, h⟩
  refine ⟨?_, ?_⟩
  · intro j c' h
    rcases hcell' j c' h with ⟨rfl, rfl⟩ | ⟨hne, hold⟩
    · have hc := hcoh.cells _ c hget
      refine ⟨by simpa using hc.dead, ?_, hc.nonAtomic, hlen, hreread, hdec_indep⟩
      obtain ⟨al, hal, h1, h2, h3, h4⟩ := hc.alloc
      exact ⟨al, by simpa using hal, h1, h2, h3, h4⟩
    · have hc := hcoh.cells j c' hold
      have hdisj := hcoh.disj _ _ c' c hne hold hget
      refine ⟨by simpa using hc.dead, ?_, hc.nonAtomic, hc.len, ?_, hc.dec_indep⟩
      · obtain ⟨al, hal, h1, h2, h3, h4⟩ := hc.alloc
        exact ⟨al, by simpa using hal, h1, h2, h3, h4⟩
      · show readBytesFrom
          (writeBytesTo σ (c.addr + (off : Int)) img) c'.addr
          (sizeofCtype tds c'.ty) = c'.bytes
        rw [readBytesFrom_writeBytesTo_disjoint _ _ _ _ _ ?_]
        · exact hc.bytes
        · simp only [cellsDisjoint] at hdisj
          omega
  · intro j1 j2 c1 c2 hne h1 h2
    rcases hcell' j1 c1 h1 with ⟨rfl, rfl⟩ | ⟨hne1, hold1⟩ <;>
      rcases hcell' j2 c2 h2 with ⟨rfl, rfl⟩ | ⟨hne2, hold2⟩
    · exact absurd rfl hne
    · have h := hcoh.disj _ _ c c2 (fun h => hne2 h.symm) hget hold2
      simp only [cellsDisjoint] at h ⊢
      omega
    · have h := hcoh.disj _ _ c1 c hne1 hold1 hget
      simp only [cellsDisjoint] at h ⊢
      omega
    · exact hcoh.disj j1 j2 c1 c2 hne hold1 hold2

end Splice

/-! ## Serialization fold lemmas (moved from the listrev slice —
layout-free: the engine's own intToBytes/bytesToInt algebra) -/

section SerFolds

open CerbMem

theorem intToBytes_length (n : Int) (sz : Nat) :
    (intToBytes n sz).length = sz := by
  unfold intToBytes
  simp

/-- Serialization at a nonnegative value: the `if` in intToBytes
    resolves. -/
theorem intToBytes_nonneg (n : Int) (sz : Nat) (h0 : 0 ≤ n) :
    intToBytes n sz = (List.range sz).map fun (i : Nat) =>
      some ((n >>> (i * 8)).toNat % 256).toUInt8 := by
  unfold intToBytes
  have hneg : (if n < 0 then ((1 <<< (sz * 8) : Nat) : Int) + n else n) = n :=
    if_neg (by omega)
  simp only [hneg]

/-- One `go` step of bytesToInt at a defined byte (the fold, exposed). -/
theorem bytesToInt_go_cons (p : Provenance) (c : Option Int)
    (v : UInt8) (rest : List AbsByte) (i : Nat) (acc : Int) :
    bytesToInt.go (⟨p, c, some v⟩ :: rest) i acc =
      bytesToInt.go rest (i + 1) (acc + (v.toNat : Int) <<< (i * 8)) := rfl

theorem bytesToInt_go_nil (i : Nat) (acc : Int) :
    bytesToInt.go [] i acc = acc := rfl

/-- bytesToInt at unsigned with all bytes defined IS the go fold. -/
theorem bytesToInt_of_all_some (bs : List AbsByte)
    (h : bs.any (·.value.isNone) = false) :
    bytesToInt bs false = some (bytesToInt.go bs 0 0) := by
  unfold bytesToInt
  rw [h]
  rfl

/-- The (LemLib-derived) BEq on Int at distinct operands. -/
theorem int_beq_eq_false (x y : Int) (h : x ≠ y) : (x == y) = false := by
  show (match defaultCompare x y with
        | LemOrdering.EQ => true | _ => false) = false
  unfold defaultCompare
  rcases hc : compare x y with h1 | h1 | h1
  · rfl
  · exact absurd (Int.compare_eq_eq.mp hc) h
  · rfl

theorem int_beq_refl (x : Int) : (x == x) = true := by
  show (match defaultCompare x x with
        | LemOrdering.EQ => true | _ => false) = true
  unfold defaultCompare
  rw [Int.compare_eq_eq.mpr rfl]

/-- The derived BEq on provenances is reflexive (splitBytesProv's
    shared-provenance fold needs it). -/
theorem provenance_beq_refl (p : Provenance) : (p == p) = true := by
  cases p with
  | Prov_none => rfl
  | Prov_some id =>
    show (match defaultCompare id id with
          | LemOrdering.EQ => true | _ => false) = true
    unfold defaultCompare
    rw [Int.compare_eq_eq.mpr rfl]
  | Prov_symbolic i =>
    show (match defaultCompare i i with
          | LemOrdering.EQ => true | _ => false) = true
    unfold defaultCompare
    rw [Int.compare_eq_eq.mpr rfl]
  | Prov_device => rfl

end SerFolds

/-! ## The generic typed-subrange memM layer (Phase 2, F-04)

Allocation-metadata authority (`MetaCoh`) is split from byte-range
contents; the load/store engine seams are proved ONCE, generic in
the accessed type and offset. `loadM_success`/`storeM_success` above
remain as the whole-cell instances (statement-frozen). -/

section GenericAccess

open CerbMem

/-- Allocation metadata: everything an access (and, from K2/K3 on, a
    kill) needs to know about the backing allocation, minus the byte
    contents. THE METADATA CELL (kill/free arc K1; RefinedC's
    `allocation` record, `theories/caesium/ghost_state.v` — `al_alive`
    is their liveness flag, `al_kind` their origin; the read-only flag
    and the OPTIONAL type are Cerberus-forced: `Allocation.isReadonly`
    exists, and `allocateRegion` records no type). Every field is
    coupled to the engine's `Allocation` record by `MetaCoh`; cites
    are `generated/CerbMem.lean` at the pin (cerberus-lean
    `ddcfc9199`). -/
structure MetaCell where
  /-- the allocation's base address (`Allocation.base`, :110) -/
  addr : Int
  /-- the allocation's type — `Allocation.ty : Option ctype` (:112,
      default `none`): `allocateObject` records `some ty` (:1518);
      `allocateRegion` records NOTHING (:1544 — regions are untyped;
      `isAtomicMemberAccess` :1609-1620 treats `none` as non-atomic). -/
  ty : Option ctype
  /-- the allocation's size in bytes — the engine's `Allocation.size`
      (registered by `allocateObject` :1518 as `(sizeofCtype tagDefs
      ty).max 1`, by `allocateRegion` :1544 as `sizeN.toNat`), carried
      as GHOST DATA so the coupling invariant computes no layout: the
      tag-definition environment enters only through the assertions
      (`metaOf`/`pointsToView`/`cellOwn` pin `size = sizeofCtype tds ty`). -/
  size : Nat
  /-- LIVENESS (RefinedC's `al_alive`): `true` iff the id is not in
      `deadAllocations` and its record is in `allocations`; `false` iff
      the id is dead and its record erased — `killM` does both in one
      update (:1576-1578). Nothing else writes either table (K0's writer
      census). The kill rules (K2/K3) are the ghost update to `false`;
      the bundles that grant access carry `true`. -/
  alive : Bool
  /-- READ-ONLY: `Allocation.isReadonly ≠ .IsWritable` (:113, :89-92).
      `allocateObject` sets `readonlyStatusForAlloc pref initOpt`
      (:1519) — `.IsWritable` at `initOpt = none` (:1490-1492, :1501),
      which is the only form the fragment's `create` issues
      (`Step.create`: `allocateObject … none none`; `CreateReadOnly` is
      not in the fragment); `allocateRegion` leaves the default
      `.IsWritable` (:1544). `storeM` refuses a read-only allocation
      with `MerrWriteOnReadOnly kind` (:1724-1725; UB033/UB064/
      UB_modifying_temporary_lifetime by kind, Mem_common.lean:392).
      The `isLocking` store (:1687-1693) is the only writer that flips
      it — outside every rule here (`storeExpr` is `Store0 false`). -/
  readonly : Bool
  /-- DYNAMIC (RefinedC's `al_kind = HeapAlloc`): the allocation's
      ORIGIN — `allocateRegion` (`Alloc0`/malloc) pushes the base onto
      `dynamicAddrs` (:1548) and is the only writer of that list;
      `allocateObject` (`Create`) does not (:1521-1523). Coupled in ONE
      direction only, `dynamic = true → base ∈ dynamicAddrs` (the K0
      range audit's N-1: the converse is not an engine invariant — a
      zero-size region at a created object's base puts that base in
      `dynamicAddrs`). K3's `free` rule takes "this allocation is
      dynamic" from here, never from `dynamicAddrs`. -/
  dynamic : Bool

/-- The metadata cell of a `create`d object: typed, at its layout
    size, of the given liveness and writability, never dynamic. -/
@[reducible] def objCell (tds : CerbTags.TagDefsMap) (a : Int) (ty : ctype)
    (alive readonly : Bool) : MetaCell :=
  ⟨a, some ty, sizeofCtype tds ty, alive, readonly, false⟩

/-- The metadata cell of an `alloc`ated region: untyped, of the
    requested size, writable, dynamic. -/
@[reducible] def regionCell (a : Int) (n : Nat) (alive : Bool) : MetaCell :=
  ⟨a, none, n, alive, false, true⟩

/-- The metadata of a footprint cell: a live, writable, created
    object of the cell's type. -/
@[reducible] def metaOf (tds : CerbTags.TagDefsMap) (c : SpikeCell) : MetaCell :=
  objCell tds c.addr c.ty true false

/-- Atomicity of an optional allocation type (`isAtomicMemberAccess`
    :1609-1620 reads `alloc.ty`; `none` is never atomic). -/
def atomicTyOpt : Option ctype → Bool
  | none => false
  | some ty => atomicTy ty

/-- The backing facts of a LIVE metadata cell in the real state: the
    id is not dead, its record is present and agrees with the cell on
    base, size, type and writability. -/
structure LiveCoh (σ : Mem) (id : Int) (mc : MetaCell) : Prop where
  dead : σ.deadAllocations.contains id = false
  alloc : ∃ al, σ.allocations.get? id = some al ∧ al.base = mc.addr ∧
    al.size = (mc.size : Int) ∧ al.ty = mc.ty ∧
    (al.isReadonly = .IsWritable ↔ mc.readonly = false)

/-- Per-allocation metadata facts in the real state (the coupling of
    every field of `MetaCell` to the engine's tables): a live cell is
    `LiveCoh`; a dead cell's id is in `deadAllocations` and its record
    is erased (`killM` :1576-1578); the type is non-atomic; a dynamic
    cell's base is in `dynamicAddrs` (`allocateRegion` :1548). For a
    footprint cell this is exactly `CellCoh` minus the byte-contents
    facts (`CellCoh.toMetaCoh`/`CellCoh.ofParts`). -/
structure MetaCoh (σ : Mem) (id : Int) (mc : MetaCell) : Prop where
  live : mc.alive = true → LiveCoh σ id mc
  dead : mc.alive = false → σ.deadAllocations.contains id = true ∧
    σ.allocations.get? id = none
  nonAtomic : atomicTyOpt mc.ty = false
  dynamic : mc.dynamic = true → mc.addr ∈ σ.dynamicAddrs

/-- `MetaCoh` reads three things of the state: the dead list, the
    record at `id`, and the dynamic list; any operation leaving them
    alone preserves it (byte writes, and — for the ids it does not
    touch — an allocation or a kill). -/
theorem MetaCoh.of_fields {σ σ' : Mem} {id : Int} {mc : MetaCell} (h : MetaCoh σ id mc)
    (h1 : σ'.deadAllocations = σ.deadAllocations)
    (h2 : σ'.allocations.get? id = σ.allocations.get? id)
    (h3 : σ'.dynamicAddrs = σ.dynamicAddrs) : MetaCoh σ' id mc := by
  refine ⟨fun ha => ?_, fun ha => ?_, h.nonAtomic, fun hd => ?_⟩
  · obtain ⟨hdead, al, hal, hb, hs, ht, hro⟩ := h.live ha
    exact ⟨by rw [h1]; exact hdead, al, by rw [h2]; exact hal, hb, hs, ht, hro⟩
  · obtain ⟨hdead, hnone⟩ := h.dead ha
    exact ⟨by rw [h1]; exact hdead, by rw [h2]; exact hnone⟩
  · rw [h3]
    exact h.dynamic hd

theorem CellCoh.toMetaCoh {σ : Mem} {id : Int} {c : SpikeCell} (tds : CerbTags.TagDefsMap)
    (h : CellCoh tds σ id c) : MetaCoh σ id (metaOf tds c) := by
  refine ⟨fun _ => ⟨h.dead, ?_⟩, fun ha => by simp at ha,
    by simpa [atomicTyOpt] using h.nonAtomic, fun hd => by simp at hd⟩
  obtain ⟨al, hal, hb, hs, ht, hro⟩ := h.alloc
  exact ⟨al, hal, hb, hs, ht, ⟨fun _ => rfl, fun _ => hro⟩⟩

/-- CellCoh assembled from its split parts: metadata authority +
    length + byte-range readout + decode inertness. -/
theorem CellCoh.ofParts {σ : Mem} {id : Int} {c : SpikeCell} (tds : CerbTags.TagDefsMap)
    (hm : MetaCoh σ id (metaOf tds c))
    (hlen : c.bytes.length = sizeofCtype tds c.ty)
    (hread : readBytesFrom σ c.addr (sizeofCtype tds c.ty) = c.bytes)
    (hdec : ∀ (lum : List (Int × identifier)) (fpm : Funptrmap),
      reconstructValue tds lum fpm c.addr c.ty c.bytes = decodeCell tds c) :
    CellCoh tds σ id c := by
  obtain ⟨hdead, al, hal, hb, hs, ht, hro⟩ := hm.live rfl
  exact ⟨hdead, ⟨al, hal, hb, hs, ht, hro.mpr rfl⟩,
    by simpa [atomicTyOpt] using hm.nonAtomic, hlen, hread, hdec⟩

/-- Range-disjointness of allocation metadata (the same formula as
    `cellsDisjoint`). -/
def metaDisjoint (m1 m2 : MetaCell) : Prop :=
  m1.addr + (m1.size : Int) ≤ m2.addr ∨
  m2.addr + (m2.size : Int) ≤ m1.addr

theorem cellsDisjoint_iff_metaDisjoint (tds : CerbTags.TagDefsMap) (c1 c2 : SpikeCell) :
    cellsDisjoint tds c1 c2 ↔ metaDisjoint (metaOf tds c1) (metaOf tds c2) :=
  Iff.rfl

/-- A non-atomic ALLOCATION type makes the atomic-member arm
    unreachable at ANY accessed lvalue type (the check reads only the
    allocation's type shape). -/
theorem isAtomicMemberAccess_false' (tds : CerbTags.TagDefsMap) (al : Allocation) (aty lty : ctype)
    (addr : Int) (hty : al.ty = some aty) (hatom : atomicTy aty = false) :
    isAtomicMemberAccess tds al lty addr = false := by
  unfold isAtomicMemberAccess
  rw [hty]
  cases aty with
  | Ctype q t => cases t <;> simp_all [atomicTy]

/-- The same at an OPTIONAL allocation type (the metadata cell's
    `ty`): an untyped region (`none`, `isAtomicMemberAccess`
    :1619-1620) or a non-atomic object type. -/
theorem isAtomicMemberAccess_false_opt (tds : CerbTags.TagDefsMap) (al : Allocation)
    (oty : Option ctype) (lty : ctype) (addr : Int) (hty : al.ty = oty)
    (hatom : atomicTyOpt oty = false) :
    isAtomicMemberAccess tds al lty addr = false := by
  cases oty with
  | none =>
    unfold isAtomicMemberAccess
    rw [hty]
  | some aty => exact isAtomicMemberAccess_false' tds al aty lty addr hty hatom

/-- The _Bool trap-representation guard at a decoded value (mirror of
    loadM's `isTrap`, CerbMem.lean:1598-1604); `cellLoadTrap` is its
    whole-cell instance (`cellLoadTrap_eq`). -/
def loadTrapV (ty : ctype) (mv : MemValue) : Bool :=
  boolTy ty &&
    (match mv with
     | .MVinteger _ (.IV _ n) => n != 0 && n != 1
     | .MVunspecified _ => true
     | _ => false)

theorem cellLoadTrap_eq (tds : CerbTags.TagDefsMap) (c : SpikeCell) :
    cellLoadTrap tds c = loadTrapV c.ty (decodeCell tds c) := rfl

/-- `applyMemM` is the active projection of the one-layer result
    (`runOne`, Step.lean). Stated here (moved from Round.lean at K1)
    so the KILLED arms can be stated as engine facts at the heap layer. -/
theorem applyMemM_eq_ndProj {α : Type} (m : CerbMem.memM α) (σ : Mem) :
    applyMemM m σ = ndProj (runOne m σ) := by
  rcases m with ⟨g⟩; rfl

/-- GENERIC IN-BOUNDS TYPED LOAD at a LIVE metadata cell (memM
    stratum): with metadata backing (any type, optional; any
    writability), an in-bounds offset, the range's byte image, and a
    non-trap decode, `loadM` at the accessed type takes the active
    path, returns the decode of the range image, and leaves the state
    unchanged. The one load seam of every typed-access rule:
    `loadM_at` (the created-object instance) and the read-only cell's
    rule consume it; K3's region loads will. -/
theorem loadM_live (tds : CerbTags.TagDefsMap) (σ : Mem) (id : Int) (mc : MetaCell) (off : Nat)
    (vty : ctype) (bs : List AbsByte) (mv : MemValue)
    (loc : CerbLocation.Loc)
    (hmeta : MetaCoh σ id mc) (halive : mc.alive = true)
    (hbound : off + sizeofCtype tds vty ≤ mc.size)
    (hread : readBytesFrom σ (mc.addr + (off : Int)) (sizeofCtype tds vty) = bs)
    (hdec : reconstructValue tds σ.lastUsedUnionMembers σ.funptrmap
      (mc.addr + (off : Int)) vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    applyMemM (loadM tds loc vty (cellPtr id (mc.addr + (off : Int)))) σ =
      some ((.FP .R (mc.addr + (off : Int)) (sizeofCtype tds vty), mv), σ) := by
  obtain ⟨hdead, al, hal, hbase, hsize, hty, -⟩ := hmeta.live halive
  have hbounds : isInBounds al (mc.addr + (off : Int)) (sizeofCtype tds vty) = true := by
    simp only [isInBounds, hbase, hsize]
    simp
    omega
  have hatomic := isAtomicMemberAccess_false_opt tds al mc.ty vty (mc.addr + (off : Int))
    hty hmeta.nonAtomic
  unfold loadM applyMemM
  simp only [cellPtr, hdead, Bool.false_eq_true, if_false, hal, hbounds,
    Bool.not_true, hatomic, hread, hdec]
  -- the trap gate: the unfolded matchers are stuck on the type and
  -- value scrutinees; explode them against the htrap hypothesis.
  unfold loadTrapV boolTy at htrap
  rcases vty with ⟨q, t⟩
  cases t <;> try simp_all
  rename_i bt
  cases bt <;> try simp_all
  rename_i ity
  cases ity <;> try simp_all
  cases mv <;> try simp_all
  rename_i iv
  cases iv
  simp_all
  rw [if_neg (fun hcond => by
    obtain ⟨h1, h2⟩ := hcond
    rw [htrap h1] at h2
    cases h2)]

/-- GENERIC IN-BOUNDS TYPED LOAD at a created object (the `objCell`
    instance of `loadM_live`; statement-frozen from Phase 2, the
    metadata literal now spelled through the extended cell). -/
theorem loadM_at (tds : CerbTags.TagDefsMap) (σ : Mem) (id a : Int) (aty : ctype) (off : Nat)
    (vty : ctype) (bs : List AbsByte) (mv : MemValue)
    (loc : CerbLocation.Loc)
    (hmeta : MetaCoh σ id (objCell tds a aty true false))
    (hbound : off + sizeofCtype tds vty ≤ sizeofCtype tds aty)
    (hread : readBytesFrom σ (a + (off : Int)) (sizeofCtype tds vty) = bs)
    (hdec : reconstructValue tds σ.lastUsedUnionMembers σ.funptrmap
      (a + (off : Int)) vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    applyMemM (loadM tds loc vty (cellPtr id (a + (off : Int)))) σ =
      some ((.FP .R (a + (off : Int)) (sizeofCtype tds vty), mv), σ) :=
  loadM_live tds σ id (objCell tds a aty true false) off vty bs mv loc hmeta rfl hbound
    hread hdec htrap

/-- GENERIC FULL-OWNERSHIP TYPED SUBRANGE STORE at a LIVE, WRITABLE
    metadata cell (memM stratum): with metadata backing and an
    in-bounds offset, `storeM` at the accessed type takes the active
    path and the state change is exactly the byte write of the
    serialized image at the interior address. The serialization
    premises are the `StorableAt` facts at the accessed type. The one
    store seam (`storeM_at` is its created-object instance); the
    writability premise `hro` is what the read-only cell cannot supply
    (`storeM_readonly_kills`). -/
theorem storeM_live (tds : CerbTags.TagDefsMap) (σ : Mem) (id : Int) (mc : MetaCell) (off : Nat)
    (vty : ctype) (mv : MemValue) (loc : CerbLocation.Loc)
    (hmeta : MetaCoh σ id mc) (halive : mc.alive = true) (hro : mc.readonly = false)
    (hbound : off + sizeofCtype tds vty ≤ mc.size)
    (hcompat : ctypeMemCompatible vty (typeofMval mv) = true)
    (hfpm : ∀ fpm, (memValueToBytes tds fpm mv).1 = fpm)
    (hbytes : ∀ fpm, (memValueToBytes tds fpm mv).2 =
      (memValueToBytes tds [] mv).2) :
    applyMemM (storeM tds loc vty false (cellPtr id (mc.addr + (off : Int))) mv) σ =
      some (.FP .W (mc.addr + (off : Int)) (sizeofCtype tds vty),
        writeBytesTo σ (mc.addr + (off : Int)) (memValueToBytes tds [] mv).2) := by
  obtain ⟨-, al, hal, hbase, hsize, hty, hiff⟩ := hmeta.live halive
  have hw : al.isReadonly = .IsWritable := hiff.mpr hro
  have hbounds : isInBounds al (mc.addr + (off : Int)) (sizeofCtype tds vty) = true := by
    simp only [isInBounds, hbase, hsize]
    simp
    omega
  have hatomic := isAtomicMemberAccess_false_opt tds al mc.ty vty (mc.addr + (off : Int))
    hty hmeta.nonAtomic
  rcases hmvb : memValueToBytes tds σ.funptrmap mv with ⟨fpm', bs'⟩
  have hfpm' : fpm' = σ.funptrmap := by
    have := hfpm σ.funptrmap
    rw [hmvb] at this
    exact this
  have hbs' : bs' = (memValueToBytes tds [] mv).2 := by
    have := hbytes σ.funptrmap
    rw [hmvb] at this
    exact this
  subst hfpm' hbs'
  unfold storeM applyMemM
  simp only [hcompat, Bool.not_true, Bool.false_eq_true, if_false, cellPtr,
    hal, hbounds, hw, hatomic, hmvb]

/-- GENERIC FULL-OWNERSHIP TYPED SUBRANGE STORE at a created object
    (the `objCell` instance of `storeM_live`; statement-frozen from
    Phase 2, the metadata literal now spelled through the extended
    cell). -/
theorem storeM_at (tds : CerbTags.TagDefsMap) (σ : Mem) (id a : Int) (aty : ctype) (off : Nat)
    (vty : ctype) (mv : MemValue) (loc : CerbLocation.Loc)
    (hmeta : MetaCoh σ id (objCell tds a aty true false))
    (hbound : off + sizeofCtype tds vty ≤ sizeofCtype tds aty)
    (hcompat : ctypeMemCompatible vty (typeofMval mv) = true)
    (hfpm : ∀ fpm, (memValueToBytes tds fpm mv).1 = fpm)
    (hbytes : ∀ fpm, (memValueToBytes tds fpm mv).2 =
      (memValueToBytes tds [] mv).2) :
    applyMemM (storeM tds loc vty false (cellPtr id (a + (off : Int))) mv) σ =
      some (.FP .W (a + (off : Int)) (sizeofCtype tds vty),
        writeBytesTo σ (a + (off : Int)) (memValueToBytes tds [] mv).2) :=
  storeM_live tds σ id (objCell tds a aty true false) off vty mv loc hmeta rfl rfl hbound
    hcompat hfpm hbytes

/-- THE STORE REFUSAL AT A READ-ONLY ALLOCATION, as an engine fact: at
    a live READ-ONLY metadata cell, an in-bounds, type-compatible
    `storeM` is KILLED with `MerrWriteOnReadOnly kind` for the
    allocation's read-only kind (CerbMem.lean:1724-1725, mirroring
    impl_mem.ml:1768-1770; the UB is UB033 / UB064 /
    UB_modifying_temporary_lifetime by kind, Mem_common.lean:392), the
    state untouched. Bounds are checked before writability (:1721-1723),
    hence `hbound`; the ill-typed-value guard comes first of all
    (:1702-1703), hence `hcompat`. This is why no store rule exists over
    `readonlyCell`: the engine's outcome is a kill, and `Step` has no
    step at a killed arm (`storeM_readonly_none`). -/
theorem storeM_readonly_kills (tds : CerbTags.TagDefsMap) (σ : Mem) (id : Int) (mc : MetaCell)
    (off : Nat) (vty : ctype) (mv : MemValue) (loc : CerbLocation.Loc)
    (hmeta : MetaCoh σ id mc) (halive : mc.alive = true) (hro : mc.readonly = true)
    (hbound : off + sizeofCtype tds vty ≤ mc.size)
    (hcompat : ctypeMemCompatible vty (typeofMval mv) = true) :
    ∃ kind, runOne (storeM tds loc vty false (cellPtr id (mc.addr + (off : Int))) mv) σ =
      (NDkilled (failReason (MerrWriteOnReadOnly kind) loc), σ) := by
  obtain ⟨-, al, hal, hbase, hsize, -, hiff⟩ := hmeta.live halive
  have hbounds : isInBounds al (mc.addr + (off : Int)) (sizeofCtype tds vty) = true := by
    simp only [isInBounds, hbase, hsize]
    simp
    omega
  obtain ⟨kind, hk⟩ : ∃ kind, al.isReadonly = .IsReadOnly kind := by
    cases hst : al.isReadonly with
    | IsWritable =>
      have := hiff.mp hst
      rw [hro] at this
      cases this
    | IsReadOnly kind => exact ⟨kind, rfl⟩
  refine ⟨kind, ?_⟩
  unfold storeM runOne
  simp only [hcompat, Bool.not_true, Bool.false_eq_true, if_false, cellPtr,
    hal, hbounds, hk]

/-- The read-only store has NO active arm: under the projection the
    fragment's `Step` fires on, the outcome is `none`. -/
theorem storeM_readonly_none (tds : CerbTags.TagDefsMap) (σ : Mem) (id : Int) (mc : MetaCell)
    (off : Nat) (vty : ctype) (mv : MemValue) (loc : CerbLocation.Loc)
    (hmeta : MetaCoh σ id mc) (halive : mc.alive = true) (hro : mc.readonly = true)
    (hbound : off + sizeofCtype tds vty ≤ mc.size)
    (hcompat : ctypeMemCompatible vty (typeofMval mv) = true) :
    applyMemM (storeM tds loc vty false (cellPtr id (mc.addr + (off : Int))) mv) σ = none := by
  obtain ⟨kind, hk⟩ := storeM_readonly_kills tds σ id mc off vty mv loc hmeta halive hro
    hbound hcompat
  rw [applyMemM_eq_ndProj, hk]
  rfl

end GenericAccess

/-! ## The allocator engine seam (Phase 2, D26 retirement) -/

section Allocator

open CerbMem

/-- The byte an uninitialized allocation is filled with
    (allocateObject's replicate payload, CerbMem.lean:1494). -/
def undefByte : AbsByte := { prov := .Prov_none, copyOffset := none, value := none }

/-- The base address `allocateObject` mints at cursor `la` for an
    allocation of `size` bytes at alignment operand `alignN`
    (CerbMem.lean:1475-1477). -/
def freshBase (la : Int) (alignN : Int) (size : Nat) : Int :=
  (alignDown (la - size).toNat (alignN.toNat.max 1) : Int)

/-- The fresh range ends at or below the old cursor (the downward
    allocator's arithmetic, exposed for the create rule's clients). -/
theorem freshBase_add_le (tds : CerbTags.TagDefsMap) (la : Int) (alignN : Int) (ty : ctype)
    (hsz : 0 < sizeofCtype tds ty)
    (hnz : freshBase la alignN (sizeofCtype tds ty) ≠ 0) :
    freshBase la alignN (sizeofCtype tds ty) + (sizeofCtype tds ty : Int) ≤ la := by
  have htoNat_pos : 0 < (la - (sizeofCtype tds ty : Int)).toNat := by
    rcases Nat.eq_zero_or_pos (la - (sizeofCtype tds ty : Int)).toNat
      with hz | hpos
    · exfalso
      apply hnz
      show (alignDown (la - (sizeofCtype tds ty : Int)).toNat
        (alignN.toNat.max 1) : Int) = 0
      rw [hz]
      simp [alignDown]
    · exact hpos
  have hle : alignDown (la - (sizeofCtype tds ty : Int)).toNat
      (alignN.toNat.max 1) ≤ (la - (sizeofCtype tds ty : Int)).toNat := by
    unfold alignDown
    exact Nat.div_mul_le_self _ _
  show (alignDown (la - (sizeofCtype tds ty : Int)).toNat
    (alignN.toNat.max 1) : Int) + (sizeofCtype tds ty : Int) ≤ la
  omega

/-- The fresh base is positive at a nonzero guard. -/
theorem freshBase_pos (tds : CerbTags.TagDefsMap) (la : Int) (alignN : Int) (ty : ctype)
    (hnz : freshBase la alignN (sizeofCtype tds ty) ≠ 0) :
    0 < freshBase la alignN (sizeofCtype tds ty) := by
  have h0 : 0 ≤ freshBase la alignN (sizeofCtype tds ty) :=
    Int.natCast_nonneg _
  omega

/-- The downward allocator never mints above its cursor: a machine
    bound on the cursor is a machine bound on every fresh base (the
    address-WF fact the public create rules export — alloc arc P2,
    the charter's "bounds knowledge" allowance). -/
theorem freshBase_lt_two64 (tds : CerbTags.TagDefsMap) (la : Int) (alignN : Int) (ty : ctype)
    (hsz : 0 < sizeofCtype tds ty)
    (hnz : freshBase la alignN (sizeofCtype tds ty) ≠ 0)
    (hla : la ≤ 2 ^ 64) :
    freshBase la alignN (sizeofCtype tds ty) < 2 ^ 64 := by
  have h := freshBase_add_le tds la alignN ty hsz hnz
  omega

/-- allocateObject SUCCESS, symbolic state: at a nonzero fresh base
    the allocator takes the active path, mints exactly
    `cellPtr σ.nextAllocId base`, bumps the cursor, registers the
    allocation, and clears the range to unspecified bytes. The `0 <
    sizeof ty` premise pins the engine's `max 1` padding away (a real
    C object type; zero-size allocations stay outside the logic). -/
theorem allocateObject_success (tds : CerbTags.TagDefsMap) (σ : Mem) (pref : prefix0)
    (aprov : Provenance) (alignN : Int) (ty : ctype)
    (hsz : 0 < sizeofCtype tds ty)
    (hnz : freshBase σ.lastAddress alignN (sizeofCtype tds ty) ≠ 0) :
    applyMemM (allocateObject tds 0 pref (.IV aprov alignN) ty none none) σ =
      some (cellPtr σ.nextAllocId
          (freshBase σ.lastAddress alignN (sizeofCtype tds ty)),
        writeBytesTo
          { σ with
              nextAllocId := σ.nextAllocId + 1,
              lastAddress := freshBase σ.lastAddress alignN (sizeofCtype tds ty),
              allocations := σ.allocations.insert σ.nextAllocId
                { base := freshBase σ.lastAddress alignN (sizeofCtype tds ty),
                  size := (sizeofCtype tds ty : Int),
                  ty := some ty,
                  isReadonly := .IsWritable,
                  prefix_ := pref } }
          (freshBase σ.lastAddress alignN (sizeofCtype tds ty))
          (List.replicate (sizeofCtype tds ty) undefByte)) := by
  have hmax : (sizeofCtype tds ty).max 1 = sizeofCtype tds ty := Nat.max_eq_left hsz
  have hbeq : ((freshBase σ.lastAddress alignN (sizeofCtype tds ty) == 0) = false) :=
    int_beq_eq_false _ _ hnz
  unfold allocateObject applyMemM
  simp only [freshBase, hmax] at hbeq ⊢
  rw [hbeq]
  simp only [readonlyStatusForAlloc_none, Bool.false_eq_true, if_false]
  rfl

end Allocator

/-! ## The global memory well-formedness invariant (kill/free arc K0;
the demo's acceptance goal 3)

`MemWF σ` is a PURE predicate on the engine's `MemState` alone — no
ghost state, no footprint — stating what the concrete allocator model
maintains about its own tables. It is carried by the state
interpretation (`CohG.wf`, under cursor presence) and by the
allocation-aware launch premise (`LaunchCoh.wf`), so "fresh" for
`create` means fresh IN THE CONCRETE ALLOCATION MODEL: the new range is
disjoint from EVERY live allocation of the state, tracked by the logic
or not (`create_fresh_global`; closes the 2026-09-02 detailed audit's
M-1, footprint-relative freshness). Every component is an engine fact,
cited against the pinned `generated/CerbMem.lean` (cerberus-lean
`ddcfc9199`):

- `live_lt`/`dead_lt` — allocation-id discipline. The only writers of
  `nextAllocId` are `allocateObject` (:1522) and `allocateRegion`
  (:1546), both `allocId + 1` with `allocId := st.nextAllocId`
  (:1515/:1543), and the only inserters into `allocations` at a NEW
  key are the same pair (:1523/:1547) at that id; `killM` moves an id
  from `allocations` to `deadAllocations` (:1576-1578). Ids are never
  reused.
- `live_dead` — live/dead consistency: `killM` erases the record in the
  same update that prepends the id to `deadAllocations` (:1577-1578);
  nothing ever re-inserts a dead id.
- `disj` — pairwise range disjointness of ALL live allocations: the
  downward cursor places every new range at or below `lastAddress`
  (`alignedAddr := alignDown (lastAddress - size).toNat align`,
  :1511-1512/:1539-1540; `freshBase_add_le`), and `cursor_lo` puts
  every live base at or above it.
- `cursor_lo` — the cursor bounds every live base from below: the
  cursor writers set `lastAddress := alignedAddr` = the new base
  (:1522/:1546); `killM` leaves the cursor alone (:1576-1578).
- `size_nonneg` — the honest size condition. `allocateObject` pads to
  `(sizeofCtype tagDefs ty).max 1` (:1510), so its records have size
  ≥ 1; `allocateRegion` takes `sizeN.toNat` (:1538) and admits ZERO
  (`malloc(0)`), so positivity is NOT an engine invariant across both
  allocators — `0 ≤ size` is. (Measured; the design note's `size_pos`
  is corrected here.)
- `la_wf` — the cursor's machine bound: the cold start is
  `0xFFFFFFFFFFFF` (:122) and the cursor only ever decreases to a
  fresh base below it.
- `dyn_lo`/`dyn_disj` — the DYNAMIC-ADDRESS component ([USER
  2026-09-02]: the arc includes dynamic allocation). MEASURED: the ONLY
  writer of `dynamicAddrs` in CerbMem.lean is `allocateRegion`'s
  prepend of the new base (:1548); `killM`'s dynamic arm READS it
  (:1573) and does NOT remove the address (:1576-1578 touch only
  `deadAllocations`/`allocations`); `allocateRegion` does not
  deduplicate (two zero-size regions at alignment 1 push the same
  address twice). So "every dynamic address is the base of a LIVE
  allocation" is NOT an engine invariant (counterexample: `alloc` then
  `free` — the address stays), and neither is `Nodup`. What the engine
  maintains, and what is stated: every dynamic address sits at or above
  the cursor (`dyn_lo`: it was the cursor when pushed, and the cursor
  only descends), and no dynamic address lies STRICTLY INSIDE a live
  allocation (`dyn_disj`: at push time it is at or below every live
  base; later allocations end at or below it). K3's `free` rule takes
  "this allocation's base is in `dynamicAddrs`" from the per-allocation
  metadata cell, not from here.

No byte-range component: `readBytesFrom` (:1462-1466) defaults a
missing key to the unspecified byte, so RefinedC's
`heap_state_alloc_alive_in_heap` has no Cerberus content.

PRESERVATION (this slice): every active outcome of `loadM`
(`MemWF.loadM`), `storeM` at either locking mode (`MemWF.storeM`; the
`isLocking` arm maps `allocations` preserving keys, bases and sizes,
:1689-1693) and `allocateObject` at any initializer
(`MemWF.allocateObject`), plus the explicit-shape `MemWF.create` the
coupling lemma `CohG.create` consumes and the byte-only
`MemWF.writeBytesTo`. K3's PROOF OBLIGATIONS (stated, not proved
here — no kill/alloc rules in this slice):
  `MemWF.allocateRegion : MemWF σ → applyMemM (allocateRegion tid pref
    align size) σ = some (pv, σ') → MemWF σ'`
  `MemWF.killM : MemWF σ → applyMemM (killM loc isDynamic pv) σ =
    some ((), σ') → MemWF σ'`
(the first is `MemWF.alloc` at `dyn := base :: σ.dynamicAddrs` with
`size := sizeN.toNat`; the second erases one live record: `disj`/
`cursor_lo`/`size_nonneg`/`dyn_disj` shrink, `dead_lt` for the new
dead id is `live_lt` of the erased record, `live_dead` for the others
is the erase). -/

section MemWF

open CerbMem

/-- Range disjointness of two allocation records (the allocation-table
    analogue of `cellsDisjoint`/`metaDisjoint`). -/
def allocDisjoint (a b : Allocation) : Prop :=
  a.base + a.size ≤ b.base ∨ b.base + b.size ≤ a.base

/-- THE GLOBAL MEMORY WELL-FORMEDNESS INVARIANT (section header: the
    per-component engine cites). -/
structure MemWF (σ : Mem) : Prop where
  /-- every live allocation id is below the next id -/
  live_lt : ∀ id al, σ.allocations.get? id = some al → id < σ.nextAllocId
  /-- every dead allocation id is below the next id -/
  dead_lt : ∀ id, σ.deadAllocations.contains id = true → id < σ.nextAllocId
  /-- live and dead ids are disjoint -/
  live_dead : ∀ id al, σ.allocations.get? id = some al →
    σ.deadAllocations.contains id = false
  /-- all live allocations are pairwise range-disjoint -/
  disj : ∀ i j ai aj, i ≠ j → σ.allocations.get? i = some ai →
    σ.allocations.get? j = some aj → allocDisjoint ai aj
  /-- every live base is at or above the downward cursor -/
  cursor_lo : ∀ id al, σ.allocations.get? id = some al → σ.lastAddress ≤ al.base
  /-- sizes are non-negative (`allocateRegion` admits zero) -/
  size_nonneg : ∀ id al, σ.allocations.get? id = some al → 0 ≤ al.size
  /-- the cursor respects the machine address bound -/
  la_wf : σ.lastAddress ≤ 2 ^ 64
  /-- every dynamic address is at or above the cursor -/
  dyn_lo : ∀ a, a ∈ σ.dynamicAddrs → σ.lastAddress ≤ a
  /-- no dynamic address lies strictly inside a live allocation -/
  dyn_disj : ∀ a, a ∈ σ.dynamicAddrs → ∀ id al, σ.allocations.get? id = some al →
    a ≤ al.base ∨ al.base + al.size ≤ a

/-- Ids at or above `nextAllocId` are not live (from `live_lt`). -/
theorem MemWF.fresh_alloc {σ : Mem} (h : MemWF σ) (id : Int) (hle : σ.nextAllocId ≤ id) :
    σ.allocations.get? id = none := by
  cases hget : σ.allocations.get? id with
  | none => rfl
  | some al =>
    exact absurd hle (Int.not_le.mpr (h.live_lt id al hget))

/-- Ids at or above `nextAllocId` are not dead (from `dead_lt`). -/
theorem MemWF.fresh_dead {σ : Mem} (h : MemWF σ) (id : Int) (hle : σ.nextAllocId ≤ id) :
    σ.deadAllocations.contains id = false := by
  cases hc : σ.deadAllocations.contains id with
  | false => rfl
  | true =>
    exact absurd hle (Int.not_le.mpr (h.dead_lt id hc))

/-- `MemWF` reads exactly five fields of the state; any operation that
    leaves them alone preserves it. -/
theorem MemWF.of_fields {σ σ' : Mem} (h : MemWF σ)
    (h1 : σ'.nextAllocId = σ.nextAllocId) (h2 : σ'.lastAddress = σ.lastAddress)
    (h3 : σ'.allocations = σ.allocations) (h4 : σ'.deadAllocations = σ.deadAllocations)
    (h5 : σ'.dynamicAddrs = σ.dynamicAddrs) : MemWF σ' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3, h1]; exact h.live_lt
  · rw [h4, h1]; exact h.dead_lt
  · rw [h3, h4]; exact h.live_dead
  · rw [h3]; exact h.disj
  · rw [h3, h2]; exact h.cursor_lo
  · rw [h3]; exact h.size_nonneg
  · rw [h2]; exact h.la_wf
  · rw [h5, h2]; exact h.dyn_lo
  · rw [h5, h3]; exact h.dyn_disj

/-- Byte writes touch only the bytemap (CerbMem.lean:1455-1460). -/
theorem MemWF.writeBytesTo {σ : Mem} (h : MemWF σ) (a : Int) (bs : List AbsByte) :
    MemWF (writeBytesTo σ a bs) :=
  h.of_fields rfl rfl rfl rfl rfl

/-- THE ALLOCATION STEP on the allocator fields, shared by both
    allocators (CerbMem.lean:1521-1523 / :1545-1548): a record whose
    range ends at or below the cursor is inserted at `nextAllocId`,
    the cursor drops to its base, the id advances, and the dynamic
    list either stays or gains the new base. -/
theorem MemWF.alloc {σ : Mem} (h : MemWF σ) (al : Allocation) (dyn : List Address)
    (hsize : 0 ≤ al.size) (hle : al.base + al.size ≤ σ.lastAddress)
    (hdyn : ∀ a, a ∈ dyn → a = al.base ∨ a ∈ σ.dynamicAddrs) :
    MemWF { σ with
              nextAllocId := σ.nextAllocId + 1,
              lastAddress := al.base,
              allocations := σ.allocations.insert σ.nextAllocId al,
              dynamicAddrs := dyn } := by
  have hget : ∀ id : Int, (σ.allocations.insert σ.nextAllocId al).get? id =
      if σ.nextAllocId = id then some al else σ.allocations.get? id := by
    intro id
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id al' hg
    dsimp only at hg ⊢
    rw [hget] at hg
    split at hg
    · next heq =>
      rw [← heq]
      exact Int.lt_succ _
    · exact Int.lt_trans (h.live_lt id al' hg) (Int.lt_succ _)
  · intro id hc
    dsimp only at hc ⊢
    exact Int.lt_trans (h.dead_lt id hc) (Int.lt_succ _)
  · intro id al' hg
    dsimp only at hg ⊢
    rw [hget] at hg
    split at hg
    · next heq =>
      subst heq
      exact h.fresh_dead _ (Int.le_refl _)
    · exact h.live_dead id al' hg
  · intro i j ai aj hne hgi hgj
    dsimp only at hgi hgj
    rw [hget] at hgi hgj
    split at hgi
    · next hi =>
      obtain rfl := Option.some.inj hgi
      rw [if_neg (fun hj => hne (hi.symm.trans hj))] at hgj
      exact Or.inl (Int.le_trans hle (h.cursor_lo j aj hgj))
    · split at hgj
      · obtain rfl := Option.some.inj hgj
        exact Or.inr (Int.le_trans hle (h.cursor_lo i ai hgi))
      · exact h.disj i j ai aj hne hgi hgj
  · intro id al' hg
    dsimp only at hg ⊢
    rw [hget] at hg
    split at hg
    · obtain rfl := Option.some.inj hg
      exact Int.le_refl _
    · exact Int.le_trans (Int.le_trans (Int.le_add_of_nonneg_right hsize) hle)
        (h.cursor_lo id al' hg)
  · intro id al' hg
    dsimp only at hg
    rw [hget] at hg
    split at hg
    · obtain rfl := Option.some.inj hg
      exact hsize
    · exact h.size_nonneg id al' hg
  · dsimp only
    exact Int.le_trans (Int.le_trans (Int.le_add_of_nonneg_right hsize) hle) h.la_wf
  · intro a ha
    dsimp only at ha ⊢
    rcases hdyn a ha with rfl | ha'
    · exact Int.le_refl _
    · exact Int.le_trans (Int.le_trans (Int.le_add_of_nonneg_right hsize) hle) (h.dyn_lo a ha')
  · intro a ha id al' hg
    dsimp only at ha hg
    rw [hget] at hg
    rcases hdyn a ha with rfl | ha'
    · split at hg
      · obtain rfl := Option.some.inj hg
        exact Or.inl (Int.le_refl _)
      · exact Or.inl (Int.le_trans (Int.le_trans (Int.le_add_of_nonneg_right hsize) hle)
          (h.cursor_lo id al' hg))
    · split at hg
      · obtain rfl := Option.some.inj hg
        exact Or.inr (Int.le_trans hle (h.dyn_lo a ha'))
      · exact h.dyn_disj a ha' id al' hg

/-- `freshBase_add_le` at an arbitrary byte count (the allocators'
    padded/raw sizes): a nonzero fresh base ends at or below the
    cursor. Positivity of the size is not needed. -/
theorem freshBase_add_le_nat (la alignN : Int) (size : Nat)
    (hnz : freshBase la alignN size ≠ 0) :
    freshBase la alignN size + (size : Int) ≤ la := by
  have htoNat_pos : 0 < (la - (size : Int)).toNat := by
    rcases Nat.eq_zero_or_pos (la - (size : Int)).toNat with hz | hpos
    · exfalso
      apply hnz
      show (alignDown (la - (size : Int)).toNat (alignN.toNat.max 1) : Int) = 0
      rw [hz]
      simp [alignDown]
    · exact hpos
  have hle : alignDown (la - (size : Int)).toNat (alignN.toNat.max 1) ≤
      (la - (size : Int)).toNat := by
    unfold alignDown
    exact Nat.div_mul_le_self _ _
  show (alignDown (la - (size : Int)).toNat (alignN.toNat.max 1) : Int) + (size : Int) ≤ la
  omega

/-- `MemWF` survives `create` in the exact shape `allocateObject_success`
    delivers (what `CohG.create` consumes). -/
theorem MemWF.create (tds : CerbTags.TagDefsMap) {σ : Mem} (h : MemWF σ) (pref : prefix0)
    (alignN : Int) (ty : ctype)
    (hsz : 0 < sizeofCtype tds ty)
    (hnz : freshBase σ.lastAddress alignN (sizeofCtype tds ty) ≠ 0) :
    MemWF (CerbMem.writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := freshBase σ.lastAddress alignN (sizeofCtype tds ty),
          allocations := σ.allocations.insert σ.nextAllocId
            { base := freshBase σ.lastAddress alignN (sizeofCtype tds ty),
              size := (sizeofCtype tds ty : Int),
              ty := some ty,
              isReadonly := .IsWritable,
              prefix_ := pref } }
      (freshBase σ.lastAddress alignN (sizeofCtype tds ty))
      (List.replicate (sizeofCtype tds ty) undefByte)) :=
  (h.alloc { base := freshBase σ.lastAddress alignN (sizeofCtype tds ty),
             size := (sizeofCtype tds ty : Int), ty := some ty,
             isReadonly := .IsWritable, prefix_ := pref } σ.dynamicAddrs
    (Int.natCast_nonneg _) (freshBase_add_le tds _ _ _ hsz hnz)
    (fun _ ha => Or.inr ha)).writeBytesTo _ _

/-- GLOBAL FRESHNESS OF `create` (acceptance goal 3's "fresh means fresh
    in the concrete allocation model"): under `MemWF`, at the guards of
    `allocateObject_success`, the id `allocateObject` mints is neither
    live nor dead, and the range it mints ends at or below the base of
    EVERY live allocation of the state — tracked by the logic or not.
    (`allocDisjoint` of the new record with each live record follows
    by `Or.inl`.) -/
theorem create_fresh_global (tds : CerbTags.TagDefsMap) (σ : Mem) (alignN : Int) (ty : ctype)
    (hwf : MemWF σ) (hsz : 0 < sizeofCtype tds ty)
    (hnz : freshBase σ.lastAddress alignN (sizeofCtype tds ty) ≠ 0) :
    σ.allocations.get? σ.nextAllocId = none ∧
    σ.deadAllocations.contains σ.nextAllocId = false ∧
    ∀ id al, σ.allocations.get? id = some al →
      freshBase σ.lastAddress alignN (sizeofCtype tds ty) + (sizeofCtype tds ty : Int) ≤ al.base :=
  ⟨hwf.fresh_alloc _ (Int.le_refl _), hwf.fresh_dead _ (Int.le_refl _),
   fun id al hg => Int.le_trans (freshBase_add_le tds _ _ _ hsz hnz) (hwf.cursor_lo id al hg)⟩

/-! ### Preservation by the engine's memory operations (every active
outcome, stated over `applyMemM` — the one-layer active projection the
rules consume). -/

/-- `loadM` never changes the state on its active arm
    (CerbMem.lean:1640). -/
theorem MemWF.loadM (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ty : ctype)
    (pv : PointerValue) {σ σ' : Mem} {r : Footprint × MemValue} (h : MemWF σ)
    (hrun : applyMemM (CerbMem.loadM tds loc ty pv) σ = some (r, σ')) : MemWF σ' := by
  unfold CerbMem.loadM at hrun
  rw [applyMemM_ND] at hrun
  dsimp only at hrun
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only at hrun <;>
    repeat' split at hrun
  all_goals (try dsimp only [ndProj] at hrun)
  all_goals first
    | (obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hrun)
       exact h.of_fields rfl rfl rfl rfl rfl)
    | cases hrun

/-- A key-, base- and size-preserving map over the allocation table
    (the `isLocking` store's readonly flip, CerbMem.lean:1689-1693)
    preserves `MemWF`. -/
theorem MemWF.map_allocs {σ : Mem} (h : MemWF σ) (f : Int → Allocation → Allocation)
    (hf : ∀ k a, (f k a).base = a.base ∧ (f k a).size = a.size) :
    MemWF { σ with allocations := σ.allocations.map f } := by
  have hget : ∀ (id : Int) (al' : Allocation), (σ.allocations.map f).get? id = some al' →
      ∃ al, σ.allocations.get? id = some al ∧ al' = f id al := by
    intro id al' hg
    rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_map] at hg
    cases hal : σ.allocations[id]? with
    | none => rw [hal] at hg; cases hg
    | some al =>
      rw [hal] at hg
      exact ⟨al, hal, (Option.some.inj hg).symm⟩
  refine ⟨?_, h.dead_lt, ?_, ?_, ?_, ?_, h.la_wf, h.dyn_lo, ?_⟩
  · intro id al' hg
    obtain ⟨al, hal, -⟩ := hget id al' hg
    exact h.live_lt id al hal
  · intro id al' hg
    obtain ⟨al, hal, -⟩ := hget id al' hg
    exact h.live_dead id al hal
  · intro i j ai' aj' hne hgi hgj
    obtain ⟨ai, hai, rfl⟩ := hget i ai' hgi
    obtain ⟨aj, haj, rfl⟩ := hget j aj' hgj
    have hd := h.disj i j ai aj hne hai haj
    unfold allocDisjoint at hd ⊢
    rw [(hf i ai).1, (hf i ai).2, (hf j aj).1, (hf j aj).2]
    exact hd
  · intro id al' hg
    obtain ⟨al, hal, rfl⟩ := hget id al' hg
    rw [(hf id al).1]
    exact h.cursor_lo id al hal
  · intro id al' hg
    obtain ⟨al, hal, rfl⟩ := hget id al' hg
    rw [(hf id al).2]
    exact h.size_nonneg id al hal
  · intro a ha id al' hg
    obtain ⟨al, hal, rfl⟩ := hget id al' hg
    rw [(hf id al).1, (hf id al).2]
    exact h.dyn_disj a ha id al hal

/-- `storeM`'s active arm writes bytes and side tables; at
    `isLocking = true` it also maps the allocation table preserving
    keys, bases and sizes (CerbMem.lean:1682-1693). -/
theorem MemWF.storeM (tds : CerbTags.TagDefsMap) (loc : CerbLocation.Loc) (ty : ctype)
    (lk : Bool) (pv : PointerValue) (mv : MemValue) {σ σ' : Mem} {fp : Footprint} (h : MemWF σ)
    (hrun : applyMemM (CerbMem.storeM tds loc ty lk pv mv) σ = some (fp, σ')) : MemWF σ' := by
  unfold CerbMem.storeM at hrun
  rw [applyMemM_ND] at hrun
  dsimp only at hrun
  rcases pv with ⟨prov, base⟩
  cases prov <;> cases base <;> dsimp only at hrun <;>
    repeat' split at hrun
  all_goals (try dsimp only [ndProj] at hrun)
  all_goals first
    | (obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hrun)
       first
         | exact h.of_fields rfl rfl rfl rfl rfl
         | exact (h.map_allocs _ (fun k a => by
             split <;> exact ⟨rfl, rfl⟩)).of_fields rfl rfl rfl rfl rfl)
    | cases hrun

/-- `allocateObject`'s active arm, at ANY initializer, is the
    allocation step on a record of padded size `(sizeof ty).max 1`
    followed by byte writes (CerbMem.lean:1510-1530). -/
theorem MemWF.allocateObject (tds : CerbTags.TagDefsMap) (tid : Nat) (pref : prefix0)
    (align : IntegerValue) (ty : ctype) (reqAddr : Option Int) (initOpt : Option MemValue)
    {σ σ' : Mem} {pv : PointerValue} (h : MemWF σ)
    (hrun : applyMemM (CerbMem.allocateObject tds tid pref align ty reqAddr initOpt) σ =
      some (pv, σ')) : MemWF σ' := by
  unfold CerbMem.allocateObject at hrun
  rcases align with ⟨_, alignN⟩
  rw [applyMemM_ND] at hrun
  dsimp only at hrun
  split at hrun
  · dsimp only [ndProj] at hrun
    cases hrun
  · next hne =>
    have hnz : freshBase σ.lastAddress alignN ((sizeofCtype tds ty).max 1) ≠ 0 := by
      intro heq
      apply hne
      rw [show (alignDown (σ.lastAddress - ((sizeofCtype tds ty).max 1 : Nat)).toNat
        (alignN.toNat.max 1) : Int) = freshBase σ.lastAddress alignN ((sizeofCtype tds ty).max 1)
        from rfl, heq]
      rfl
    have hwf' := h.alloc
      { base := freshBase σ.lastAddress alignN ((sizeofCtype tds ty).max 1),
        size := (((sizeofCtype tds ty).max 1 : Nat) : Int), ty := some ty,
        isReadonly := readonlyStatusForAlloc pref initOpt, prefix_ := pref }
      σ.dynamicAddrs (Int.natCast_nonneg _) (freshBase_add_le_nat _ _ _ hnz)
      (fun _ ha => Or.inr ha)
    split at hrun <;>
    · dsimp only [ndProj] at hrun
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hrun)
      exact hwf'.of_fields rfl rfl rfl rfl rfl

end MemWF

/-! ## The byte-level view of the state (Phase 2 coupling helpers) -/

section ByteAt

open CerbMem

/-- The byte the engine reads at address `k` (readBytesFrom's
    per-address readout, with its unspecified default). -/
def byteAt (σ : Mem) (k : Int) : AbsByte :=
  match σ.bytemap.get? k with
  | some b => b
  | none => undefByte

theorem readBytesFrom_eq_map_byteAt (σ : Mem) (a : Int) (n : Nat) :
    readBytesFrom σ a n =
      (List.range n).map (fun (i : Nat) => byteAt σ (a + (i : Int))) := by
  unfold readBytesFrom byteAt undefByte
  apply List.map_congr_left
  intro i _
  cases σ.bytemap.get? (a + (i : Int)) <;> rfl

theorem readBytesFrom_of_byteAt (σ : Mem) (a : Int)
    (bs : List AbsByte)
    (h : ∀ (i : Nat) (hi : i < bs.length), byteAt σ (a + (i : Int)) = bs[i]) :
    readBytesFrom σ a bs.length = bs := by
  rw [readBytesFrom_eq_map_byteAt]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact h i h2

theorem byteAt_of_readBytesFrom (σ : Mem) (a : Int) (n : Nat)
    (bs : List AbsByte) (h : readBytesFrom σ a n = bs) :
    ∀ (j : Nat), j < n → byteAt σ (a + (j : Int)) = (bs[j]?).getD undefByte := by
  intro j hj
  subst h
  rw [readBytesFrom_eq_map_byteAt]
  rw [List.getElem?_map, List.getElem?_range hj]
  rfl

theorem byteAt_writeBytesTo_in (σ : Mem) (a : Int) (bs : List AbsByte)
    (k : Int) (h1 : a ≤ k) (h2 : k < a + bs.length) :
    byteAt (writeBytesTo σ a bs) k =
      bs[(k - a).toNat]'(by omega) := by
  unfold byteAt
  rw [writeBytesTo_bytemap_get?, if_pos ⟨h1, h2⟩,
    List.getElem?_eq_getElem (by omega : (k - a).toNat < bs.length)]

theorem byteAt_writeBytesTo_out (σ : Mem) (a : Int) (bs : List AbsByte)
    (k : Int) (h : ¬(a ≤ k ∧ k < a + bs.length)) :
    byteAt (writeBytesTo σ a bs) k = byteAt σ k := by
  unfold byteAt
  rw [writeBytesTo_bytemap_get?, if_neg h]

@[simp] theorem writeBytesTo_lastAddress (st : Mem) (a : Int)
    (bs : List AbsByte) :
    (writeBytesTo st a bs).lastAddress = st.lastAddress := rfl

@[simp] theorem writeBytesTo_nextAllocId (st : Mem) (a : Int)
    (bs : List AbsByte) :
    (writeBytesTo st a bs).nextAllocId = st.nextAllocId := rfl

/-- MetaCoh is invariant under byte writes (the allocation and dead
    tables are untouched). -/
theorem MetaCoh.writeBytes {σ : Mem} {id : Int} {mc : MetaCell}
    (h : MetaCoh σ id mc) (a : Int) (bs : List AbsByte) :
    MetaCoh (writeBytesTo σ a bs) id mc :=
  h.of_fields rfl rfl rfl

end ByteAt

/-! ## Ghost-map range constructions -/

section RangeMaps

open CerbMem Iris.Std.PartialMap

/-- Insert a byte list along consecutive addresses (the ghost image
    of `writeBytesTo`). -/
def insertRange (m : SpikeHeapF AbsByte) (a : Int) :
    List AbsByte → SpikeHeapF AbsByte
  | [] => m
  | b :: bs => insertRange (Iris.Std.PartialMap.insert m a b) (a + 1) bs

theorem insertRange_get? (m : SpikeHeapF AbsByte) (a : Int)
    (bs : List AbsByte) (k : Int) :
    Iris.Std.PartialMap.get? (insertRange m a bs) k =
      if a ≤ k ∧ k < a + bs.length then bs[(k - a).toNat]?
      else Iris.Std.PartialMap.get? m k := by
  induction bs generalizing m a with
  | nil =>
    simp only [insertRange, List.length_nil]
    rw [if_neg (by omega)]
  | cons b bs ih =>
    simp only [insertRange, List.length_cons]
    rw [ih]
    by_cases hk : k = a
    · subst hk
      rw [if_neg (by omega), if_pos (by omega),
        Iris.Std.get?_insert_eq rfl,
        show (k - k).toNat = 0 by omega]
      rfl
    · by_cases h1 : a + 1 ≤ k ∧ k < a + 1 + (bs.length : Int)
      · rw [if_pos h1, if_pos (by omega),
          show (k - a).toNat = (k - (a + 1)).toNat + 1 by omega]
        rfl
      · rw [if_neg h1, if_neg (by omega),
          Iris.Std.get?_insert_ne (fun h => hk h.symm)]

/-- `get?` through the PartialMap union (the `∪` the GenHeap
    allocation lemmas produce, spelled explicitly — the ExtTreeMap
    `∪` instance is a different constant). -/
theorem PMunion_get? {V : Type} (m₁ m₂ : SpikeHeapF V) (k : Int) :
    Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union m₁ m₂) k =
      (Iris.Std.PartialMap.get? m₁ k).orElse
        (fun _ => Iris.Std.PartialMap.get? m₂ k) :=
  Iris.Std.LawfulPartialMap.get?_union

/-- The standalone byte-range map (a fresh allocation's ghost image;
    head-insert shape so the fragment big-sep peels by
    `bigSepM_insert`). -/
def rangeMap (a : Int) : List AbsByte → SpikeHeapF AbsByte
  | [] => ∅
  | b :: bs => Iris.Std.PartialMap.insert (rangeMap (a + 1) bs) a b

theorem rangeMap_get? (a : Int) (bs : List AbsByte) (k : Int) :
    Iris.Std.PartialMap.get? (rangeMap a bs) k =
      if a ≤ k ∧ k < a + bs.length then bs[(k - a).toNat]? else none := by
  induction bs generalizing a with
  | nil =>
    simp only [rangeMap, List.length_nil]
    rw [if_neg (by omega), Iris.Std.LawfulPartialMap.get?_empty]
  | cons b bs ih =>
    simp only [rangeMap, List.length_cons]
    by_cases hk : k = a
    · subst hk
      rw [Iris.Std.get?_insert_eq rfl, if_pos (by omega),
        show (k - k).toNat = 0 by omega]
      rfl
    · rw [Iris.Std.get?_insert_ne (fun h => hk h.symm), ih]
      by_cases h1 : a + 1 ≤ k ∧ k < a + 1 + (bs.length : Int)
      · rw [if_pos h1, if_pos (by omega),
          show (k - a).toNat = (k - (a + 1)).toNat + 1 by omega]
        rfl
      · rw [if_neg h1, if_neg (by omega)]

end RangeMaps

/-! ## Ghost state (Phase 2: the ownership split)

THE CARRIER (the registered growth step, executed): a per-BYTE heap
(absolute address ↦ AbsByte — the ghost fragment of the engine's own
`bytemap`), a per-allocation METADATA heap (allocation id ↦
base/type — the provenance/metadata authority), and a one-cell
ALLOCATOR-CURSOR heap (the D26 resource: lastAddress/nextAllocId
knowledge, without which `create`'s reducibility is unprovable).
Donor shape: Caesium's `heap : gmap addr byte` + `allocs : gmap
alloc_id allocation` split (RefinedC theories/caesium/ghost_state.v;
loc_in_bounds is their persistent metadata analogue, alloc_alive
their killable one — kill/free is outside this fragment, so the
metadata here is plain fractional and never dies; when kill joins
the fragment the metadata heap gains a liveness component — named
mover, registered in the phase notes). -/

/-- The allocator cursor: the two MemState fields `allocateObject`
    reads and writes (CerbMem.lean:1470-1490). -/
structure AllocCursor where
  lastAddr : Int
  nextId : Int
  deriving Inhabited

/-! ## The allocation plan (alloc arc P1.1 — the pure model of the
abstract allocation-capacity policy)

An `AllocReq` is the client-visible read-set of one `create`: the
alignment operand and the C object type. `advanceCursor` is the PURE
image of one successful `allocateObject` on the cursor fields — it
reuses EXACTLY the guards of `allocateObject_success` (this file,
§"The allocator engine seam": `0 < sizeofCtype ty` pins the engine's
`max 1` padding away, and `freshBase … ≠ 0` is the out-of-memory
kill arm, CerbMem.lean:1479) and EXACTLY its cursor update
(`lastAddress := freshBase la align (sizeof ty)`,
`nextAllocId := nid + 1` — CerbMem.lean:1475-1490). `PlanFits` runs
a request list IN ORDER (alignment rounding is not commutative —
`planFits_order_sensitive` below). The type-specific non-atomic and
decode-inert premises stay on the logical create rules, not here
(charter P1.1). -/

/-- One allocation request: alignment operand + C object type. -/
structure AllocReq where
  align : Int
  ty : ctype

/-- One successful `allocateObject`, on the cursor fields alone.
    Guard and update mirror `allocateObject_success` exactly (see
    the section note above); `none` is the engine's out-of-memory
    kill arm (or a zero-size type, which stays outside the logic). -/
def advanceCursor (tds : CerbTags.TagDefsMap) (c : AllocCursor) (r : AllocReq) : Option AllocCursor :=
  if 0 < CerbMem.sizeofCtype tds r.ty ∧
      freshBase c.lastAddr r.align (CerbMem.sizeofCtype tds r.ty) ≠ 0 then
    some ⟨freshBase c.lastAddr r.align (CerbMem.sizeofCtype tds r.ty),
      c.nextId + 1⟩
  else
    none

/-- A request list fits a cursor when every request advances it, in
    order. -/
def PlanFits (tds : CerbTags.TagDefsMap) (c : AllocCursor) : List AllocReq → Prop
  | [] => True
  | r :: rs =>
    match advanceCursor tds c r with
    | some c' => PlanFits tds c' rs
    | none => False

theorem advanceCursor_pos (tds : CerbTags.TagDefsMap) (c : AllocCursor) (r : AllocReq)
    (hsz : 0 < CerbMem.sizeofCtype tds r.ty)
    (hnz : freshBase c.lastAddr r.align (CerbMem.sizeofCtype tds r.ty) ≠ 0) :
    advanceCursor tds c r =
      some ⟨freshBase c.lastAddr r.align (CerbMem.sizeofCtype tds r.ty),
        c.nextId + 1⟩ := by
  unfold advanceCursor
  rw [if_pos ⟨hsz, hnz⟩]

/-- Inversion: a successful advance carries both engine guards and
    pins the next cursor to the allocator arithmetic. (Deleting the
    nonzero guard from `advanceCursor` breaks exactly this — and with
    it the internal create rule's `allocateObject_success` discharge:
    the P1.4 guard-deletion plant.) -/
theorem advanceCursor_some_inv {c c' : AllocCursor} {r : AllocReq} (tds : CerbTags.TagDefsMap)
    (h : advanceCursor tds c r = some c') :
    0 < CerbMem.sizeofCtype tds r.ty ∧
    freshBase c.lastAddr r.align (CerbMem.sizeofCtype tds r.ty) ≠ 0 ∧
    c' = ⟨freshBase c.lastAddr r.align (CerbMem.sizeofCtype tds r.ty),
      c.nextId + 1⟩ := by
  unfold advanceCursor at h
  split at h
  · next hc => exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  · cases h

/-- Constructor-argument form (unfolds the projections; the concrete
    unit tests rewrite with this). -/
theorem advanceCursor_mk (tds : CerbTags.TagDefsMap) (la nid al : Int) (ty : ctype) :
    advanceCursor tds ⟨la, nid⟩ ⟨al, ty⟩ =
      if 0 < CerbMem.sizeofCtype tds ty ∧
          freshBase la al (CerbMem.sizeofCtype tds ty) ≠ 0 then
        some ⟨freshBase la al (CerbMem.sizeofCtype tds ty), nid + 1⟩
      else none := rfl

@[simp] theorem PlanFits_nil (tds : CerbTags.TagDefsMap) (c : AllocCursor) :
    PlanFits tds c [] := trivial

theorem PlanFits_cons_iff (tds : CerbTags.TagDefsMap) (c : AllocCursor) (r : AllocReq)
    (rs : List AllocReq) :
    PlanFits tds c (r :: rs) ↔
      ∃ c', advanceCursor tds c r = some c' ∧ PlanFits tds c' rs := by
  constructor
  · intro h
    unfold PlanFits at h
    split at h
    · next c' hc' => exact ⟨c', hc', h⟩
    · exact h.elim
  · rintro ⟨c', hc', h⟩
    unfold PlanFits
    rw [hc']
    exact h

/-- Prefix weakening: a plan that fits still fits after dropping a
    TAIL (stopping early is always allowed; dropping the HEAD is
    not — see `planFits_order_sensitive`). -/
theorem PlanFits.prefix {c : AllocCursor} {rs rs' : List AllocReq} (tds : CerbTags.TagDefsMap)
    (h : PlanFits tds c (rs ++ rs')) : PlanFits tds c rs := by
  induction rs generalizing c with
  | nil => trivial
  | cons r rs ih =>
    rw [List.cons_append, PlanFits_cons_iff] at h
    rw [PlanFits_cons_iff]
    obtain ⟨c', hc', h⟩ := h
    exact ⟨c', hc', ih h⟩

/-! The P1.4 pure unit tests, generic over ANY 4-byte object type
(no example constants in this module — the charter's merge-row-2
constraint; the exhibits instantiate these at `intTy`). -/

/-- PLAN-ORDER SENSITIVITY: at a 4-byte type, `[align 16, align 1]`
    fits cursor 21 (16-aligned base 16, then base 12) but the SWAPPED
    plan does not (align-1 base 17, then `alignDown 13 16 = 0` — the
    out-of-memory arm). Request order is semantically binding. -/
theorem planFits_order_sensitive (tds : CerbTags.TagDefsMap) (ty : ctype)
    (h4 : CerbMem.sizeofCtype tds ty = 4) :
    PlanFits tds ⟨21, 0⟩ [⟨16, ty⟩, ⟨1, ty⟩] ∧
      ¬ PlanFits tds ⟨21, 0⟩ [⟨1, ty⟩, ⟨16, ty⟩] := by
  constructor
  · rw [PlanFits_cons_iff]
    refine ⟨⟨freshBase 21 16 (CerbMem.sizeofCtype tds ty), 0 + 1⟩, ?_, ?_⟩
    · rw [advanceCursor_mk, h4]
      exact if_pos ⟨by decide, by decide⟩
    · rw [PlanFits_cons_iff]
      refine ⟨⟨freshBase (freshBase 21 16 (CerbMem.sizeofCtype tds ty)) 1
        (CerbMem.sizeofCtype tds ty), 0 + 1 + 1⟩, ?_, PlanFits_nil tds _⟩
      rw [advanceCursor_mk, h4]
      exact if_pos ⟨by decide, by decide⟩
  · intro h
    rw [PlanFits_cons_iff] at h
    obtain ⟨c', hc', h⟩ := h
    rw [advanceCursor_mk, h4, if_pos ⟨by decide, by decide⟩] at hc'
    obtain rfl := Option.some.inj hc'
    rw [PlanFits_cons_iff] at h
    obtain ⟨c'', hc'', -⟩ := h
    rw [advanceCursor_mk, h4,
      if_neg (fun hcon => hcon.2 (by decide))] at hc''
    cases hc''

/-- INSUFFICIENT PLAN: a 4-byte request cannot fit cursor 2 (the
    fresh range would underflow to base 0 — the engine's kill arm).
    An empty or too-small capacity proves no create (the create rules
    consume `PlanFits` through `advanceCursor_some_inv`). -/
theorem planFits_insufficient (tds : CerbTags.TagDefsMap) (ty : ctype)
    (h4 : CerbMem.sizeofCtype tds ty = 4) :
    ¬ PlanFits tds ⟨2, 0⟩ [⟨1, ty⟩] := by
  intro h
  rw [PlanFits_cons_iff] at h
  obtain ⟨c', hc', -⟩ := h
  rw [advanceCursor_mk, h4,
    if_neg (fun hcon => hcon.2 (by decide))] at hc'
  cases hc'

/-- Ghost-state prerequisites: invariants + the three GenHeaps
    (bytes, allocation metadata, allocator cursor). -/
class SpikeGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  byte_pre : genHeapPreS Int CerbMem.AbsByte GF SpikeHeapF
  meta_pre : genHeapPreS Int MetaCell GF SpikeHeapF
  cursor_pre : genHeapPreS Int AllocCursor GF SpikeHeapF

attribute [reducible, instance] SpikeGpreS.byte_pre SpikeGpreS.meta_pre
  SpikeGpreS.cursor_pre

/-- The bundled ghost names (mirror of HeapLangGS, three heaps). The
    heap fields are NOT registered as bare `genHeapGS` instances (the
    three heaps share the key type; resolution goes through the named
    wrappers below). -/
class SpikeGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [invGS : InvGS_gen hlc GF]
  byteGS : genHeapGS Int CerbMem.AbsByte GF SpikeHeapF
  metaGS : genHeapGS Int MetaCell GF SpikeHeapF
  cursorGS : genHeapGS Int AllocCursor GF SpikeHeapF

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- Byte-heap ownership: one byte of one allocation's range. -/
abbrev byteOwn [SpikeGS hlc GF] (k : Int) (dq : DFrac)
    (b : CerbMem.AbsByte) : IProp GF :=
  pointsTo (G := SpikeGS.byteGS) k dq b

/-- Metadata ownership: the allocation's base address and type. -/
abbrev metaOwn [SpikeGS hlc GF] (id : Int) (dq : DFrac)
    (mc : MetaCell) : IProp GF :=
  pointsTo (G := SpikeGS.metaGS) id dq mc

/-- The allocator-cursor resource (exclusive). -/
abbrev cursorOwn [SpikeGS hlc GF] (c : AllocCursor) : IProp GF :=
  pointsTo (G := SpikeGS.cursorGS) 0 (.own 1) c

abbrev byteInterp [SpikeGS hlc GF] (mb : SpikeHeapF CerbMem.AbsByte) : IProp GF :=
  genHeapInterp (G := SpikeGS.byteGS) mb

abbrev metaInterp [SpikeGS hlc GF] (mm : SpikeHeapF MetaCell) : IProp GF :=
  genHeapInterp (G := SpikeGS.metaGS) mm

abbrev cursorInterp [SpikeGS hlc GF] (mk : SpikeHeapF AllocCursor) : IProp GF :=
  genHeapInterp (G := SpikeGS.cursorGS) mk

/-- Consecutive byte-range ownership (the untyped content of a view;
    per-byte separation is what makes subrange split/join REAL ∗). -/
def bytesOwn [SpikeGS hlc GF] (a : Int) (dq : DFrac) :
    List CerbMem.AbsByte → IProp GF
  | [] => iprop(emp)
  | b :: bs => iprop(byteOwn a dq b ∗ bytesOwn (a + 1) dq bs)

/-! ## The coupling invariant (ghost side) -/

open Iris.Std.PartialMap in
/-- The coupling invariant between the real MemState and the three
    ghost maps. Byte cells are backed by the bytemap readout; meta
    cells by live/writable/typed/non-atomic allocations, pairwise
    range-disjoint; a cursor cell (key 0, at most one) pins the
    allocator fields, and its PRESENCE carries (i) THE GLOBAL MEMORY
    WELL-FORMEDNESS INVARIANT `MemWF σ` (K0; the section above) and
    (ii) the one ghost-side bound `MemWF` cannot supply — every
    ghost-tracked BYTE sits at or above the downward cursor (byte cells
    are not tied to allocation records by this invariant). The former
    fields `cur_dead`/`cur_alloc`/`cur_meta_lt`/`cur_meta_lo` are now
    DERIVED (the theorems below) from `wf` and `metas`. A cursor-free
    ghost state makes both conditional facts vacuous: the cursor-free
    launches (`MetaByteOf.cohG`, from `Coh` alone) owe nothing new —
    the forcing fact for the conditional form is that those launches
    have no `MemWF` premise, and adding one would change the text of
    every non-allocating export ([AGENT] K0, one change at a time). -/
structure CohG (σ : Mem) (mm : SpikeHeapF MetaCell)
    (mb : SpikeHeapF CerbMem.AbsByte) (mk : SpikeHeapF AllocCursor) : Prop where
  metas : ∀ id mc, get? mm id = some mc → MetaCoh σ id mc
  metas_disj : ∀ i j mci mcj, i ≠ j → get? mm i = some mci →
    get? mm j = some mcj → metaDisjoint mci mcj
  bytes : ∀ k b, get? mb k = some b → byteAt σ k = b
  cursor_key : ∀ k c, get? mk k = some c → k = 0
  cursor : ∀ c, get? mk 0 = some c →
    c.lastAddr = σ.lastAddress ∧ c.nextId = σ.nextAllocId
  /-- the global memory well-formedness invariant, under cursor presence -/
  wf : get? mk 0 ≠ none → MemWF σ
  cur_byte_lo : get? mk 0 ≠ none → ∀ k b, get? mb k = some b →
    σ.lastAddress ≤ k
  /-- every ghost-tracked metadata cell, ALIVE OR DEAD, sits at or
      above the cursor (K1): for a live cell this is `MemWF.cursor_lo`
      through `metas`; for a dead cell `MemWF` has forgotten the record
      (`killM` erases it), so the fact that dead ranges are never reused
      — the cursor only descends — is ghost-side, exactly as
      `cur_byte_lo`. `CohG.create` needs it for `metas_disj` against
      every tracked cell. -/
  cur_meta_lo : get? mk 0 ≠ none → ∀ id mc, get? mm id = some mc →
    σ.lastAddress ≤ mc.addr

/-! Three of the four `CohG` fields K0 retired, as consequences (same
names, same shapes; `CohG.create` and the launch lemmas consume them).
The fourth, `cur_meta_lo`, is a FIELD again since K1 (dead cells). -/

/-- Fresh ids are not dead (`MemWF.dead_lt`). -/
theorem CohG.cur_dead {σ : Mem} {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
    {mk : SpikeHeapF AllocCursor} (hG : CohG σ mm mb mk)
    (hne : Iris.Std.PartialMap.get? mk 0 ≠ none) (id : Int) (hle : σ.nextAllocId ≤ id) :
    σ.deadAllocations.contains id = false :=
  (hG.wf hne).fresh_dead id hle

/-- Fresh ids are not live (`MemWF.live_lt`). -/
theorem CohG.cur_alloc {σ : Mem} {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
    {mk : SpikeHeapF AllocCursor} (hG : CohG σ mm mb mk)
    (hne : Iris.Std.PartialMap.get? mk 0 ≠ none) (id : Int) (hle : σ.nextAllocId ≤ id) :
    σ.allocations.get? id = none :=
  (hG.wf hne).fresh_alloc id hle

/-- Every ghost-tracked allocation id, alive or dead, is below the
    next id (`metas` + `MemWF.live_lt`/`MemWF.dead_lt`). -/
theorem CohG.cur_meta_lt {σ : Mem} {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
    {mk : SpikeHeapF AllocCursor} (hG : CohG σ mm mb mk)
    (hne : Iris.Std.PartialMap.get? mk 0 ≠ none) (id : Int) (mc : MetaCell)
    (hget : Iris.Std.PartialMap.get? mm id = some mc) : id < σ.nextAllocId := by
  have hm := hG.metas id mc hget
  cases ha : mc.alive with
  | true =>
    obtain ⟨-, al, hal, -⟩ := hm.live ha
    exact (hG.wf hne).live_lt id al hal
  | false =>
    obtain ⟨hdead, -⟩ := hm.dead ha
    exact (hG.wf hne).dead_lt id hdead

/-- The state interpretation: memory only (no driver state), coupled
    to the three ghost maps by CohG. -/
instance SpikeState [SpikeGS hlc GF] : StateInterp Mem Empty GF where
  stateInterp σ _ _ _ := iprop(∃ mm mb mk, ⌜CohG σ mm mb mk⌝ ∗
    metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk)

theorem stateInterp_eq [SpikeGS hlc GF] (σ : Mem) (ns : Nat)
    (κs : List Empty) (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt =
      iprop(∃ mm mb mk, ⌜CohG σ mm mb mk⌝ ∗
        metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk) := rfl

/-! ## The view stratum: typed subrange ownership -/

/-- Table-independent decode of a byte image at its type (the
    inertness fact `CellCoh.dec_indep` states through Coh; here it
    rides INSIDE the whole-cell assertion). -/
def decIndep (tds : CerbTags.TagDefsMap) (a : Int) (ty : ctype) (bs : List CerbMem.AbsByte) : Prop :=
  ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap),
    CerbMem.reconstructValue tds lum fpm a ty bs = decodeCell tds ⟨a, ty, bs⟩

/-- THE TYPED VIEW: ownership of one typed subrange of one
    allocation — metadata knowledge (id, base, allocation type) at
    fraction `dqm`, plus the range's bytes at fraction `dqb`, plus
    the in-bounds and footprint-length facts. -/
def pointsToView [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype) (off : Nat)
    (dqm dqb : DFrac) (vty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(metaOwn id dqm (objCell tds a aty true false) ∗
    ⌜off + CerbMem.sizeofCtype tds vty ≤ CerbMem.sizeofCtype tds aty ∧
      bs.length = CerbMem.sizeofCtype tds vty⌝ ∗
    bytesOwn (a + (off : Int)) dqb bs)

theorem pointsToView_iff {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap)
    (id a : Int) (aty : ctype) (off : Nat) (dqm dqb : DFrac) (vty : ctype)
    (bs : List CerbMem.AbsByte) :
    pointsToView tds (GF := GF) id a aty off dqm dqb vty bs ⊣⊢
      iprop(metaOwn id dqm (objCell tds a aty true false) ∗
        ⌜off + CerbMem.sizeofCtype tds vty ≤ CerbMem.sizeofCtype tds aty ∧
          bs.length = CerbMem.sizeofCtype tds vty⌝ ∗
        bytesOwn (a + (off : Int)) dqb bs) := .rfl

/-- Whole-allocation ownership at a ghost id: THE MAXIMAL VIEW
    (offset 0, view type = allocation type, both fractions equal)
    plus the image's decode inertness. This is what the old
    allocation-rooted ghost cell becomes. -/
def cellOwn [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (i : Int) (dq : DFrac) (c : SpikeCell) : IProp GF :=
  iprop(metaOwn i dq (metaOf tds c) ∗ bytesOwn c.addr dq c.bytes ∗
    ⌜c.bytes.length = CerbMem.sizeofCtype tds c.ty ∧
      decIndep tds c.addr c.ty c.bytes⌝)

theorem cellOwn_iff {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap)
    (i : Int) (dq : DFrac) (c : SpikeCell) :
    cellOwn tds (GF := GF) i dq c ⊣⊢
      iprop(metaOwn i dq (metaOf tds c) ∗ bytesOwn c.addr dq c.bytes ∗
        ⌜c.bytes.length = CerbMem.sizeofCtype tds c.ty ∧
          decIndep tds c.addr c.ty c.bytes⌝) := .rfl

/-- The fragment points-to: the pointer is a real `PointerValue`
    carrying its provenance id (R5 — never an address-only
    abstraction), and the whole allocation is owned at fraction dq. -/
def pointsToCell [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue) (dq : DFrac)
    (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id : Int) (a : Int),
    ⌜pv = cellPtr id a⌝ ∗ cellOwn tds id dq (SpikeCell.mk a ty bs))

theorem pointsToCell_cellOwn_iff {hlc : HasLC} {GF : BundledGFunctors}
    [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue) (dq : DFrac) (ty : ctype)
    (bs : List CerbMem.AbsByte) :
    pointsToCell tds (GF := GF) pv dq ty bs ⊣⊢
      iprop(∃ (id : Int) (a : Int),
        ⌜pv = cellPtr id a⌝ ∗ cellOwn tds id dq (SpikeCell.mk a ty bs)) := .rfl

/-- Points-to notation; the tag-definition environment is written
    explicitly (`pv ↦c[tds]{dq} ty ; bs`, `pv ↦c[tds] ty ; bs`). -/
notation:50 pv " ↦c[" tds "]{" dq "} " ty " ; " bs:50 => pointsToCell tds pv dq ty bs
notation:50 pv " ↦c[" tds "] " ty " ; " bs:50 => pointsToCell tds pv (DFrac.own 1) ty bs

/-! ## Split/join laws (the view algebra)

Byte ranges split at ∗ because the carrier is per-byte; metadata
knowledge splits fractionally (classical fractional permissions —
Boyland; the donor's `heap_mapsto`/`loc_in_bounds` factorization). -/

section ViewLaws

variable [SpikeGS hlc GF]

@[simp] theorem bytesOwn_nil (a : Int) (dq : DFrac) :
    bytesOwn (GF := GF) a dq [] = iprop(emp) := rfl

theorem bytesOwn_cons (a : Int) (dq : DFrac) (b : CerbMem.AbsByte)
    (bs : List CerbMem.AbsByte) :
    bytesOwn (GF := GF) a dq (b :: bs) =
      iprop(byteOwn a dq b ∗ bytesOwn (a + 1) dq bs) := rfl

/-- RANGE SPLIT/JOIN: consecutive byte ownership splits at any list
    decomposition — real ∗, both directions. -/
theorem bytesOwn_append (a : Int) (dq : DFrac)
    (bs₁ bs₂ : List CerbMem.AbsByte) :
    bytesOwn (GF := GF) a dq (bs₁ ++ bs₂) ⊣⊢
      iprop(bytesOwn a dq bs₁ ∗ bytesOwn (a + bs₁.length) dq bs₂) := by
  induction bs₁ generalizing a with
  | nil =>
    simp only [List.nil_append, bytesOwn_nil, List.length_nil]
    rw [show a + ((0 : Nat) : Int) = a by omega]
    exact BI.emp_sep.symm
  | cons b bs ih =>
    simp only [List.cons_append, bytesOwn_cons, List.length_cons]
    rw [show a + (((bs.length + 1 : Nat)) : Int) =
      (a + 1) + ((bs.length : Nat) : Int) by omega]
    exact (BI.sep_congr .rfl (ih (a + 1))).trans BI.sep_assoc.symm

/-- Metadata knowledge is fractional (Fractional instance of the
    ghost-map element — classical fractional permissions). -/
theorem metaOwn_fractional (id : Int) (mc : MetaCell) (q₁ q₂ : Qp) :
    metaOwn (GF := GF) id (.own (q₁ + q₂)) mc ⊣⊢
      iprop(metaOwn id (.own q₁) mc ∗ metaOwn id (.own q₂) mc) := by
  letI := SpikeGS.metaGS (hlc := hlc) (GF := GF)
  exact Fractional.fractional
    (Φ := fun q => pointsTo (G := SpikeGS.metaGS) id (.own q) mc) q₁ q₂

/-- Metadata agreement: two views of the same allocation agree on
    base and type. -/
theorem metaOwn_agree (id : Int) (dq₁ dq₂ : DFrac) (mc₁ mc₂ : MetaCell) :
    iprop(metaOwn (GF := GF) id dq₁ mc₁ ∗ metaOwn id dq₂ mc₂) ⊢
      (⌜mc₁ = mc₂⌝ : IProp GF) := by
  letI := SpikeGS.metaGS (hlc := hlc) (GF := GF)
  exact pointsTo_agree

/-- SUBRANGE SPLIT: a typed view whose footprint decomposes as two
    type footprints splits into the two typed subviews (metadata
    fraction split, byte range split at the list decomposition). -/
theorem pointsToView_split (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype) (off : Nat)
    (q₁ q₂ : Qp) (dqb : DFrac) (vty vty₁ vty₂ : ctype)
    (bs₁ bs₂ : List CerbMem.AbsByte)
    (hsz : CerbMem.sizeofCtype tds vty =
      CerbMem.sizeofCtype tds vty₁ + CerbMem.sizeofCtype tds vty₂)
    (hlen₁ : bs₁.length = CerbMem.sizeofCtype tds vty₁) :
    pointsToView tds (GF := GF) id a aty off (.own (q₁ + q₂)) dqb vty (bs₁ ++ bs₂) ⊢
      iprop(pointsToView tds id a aty off (.own q₁) dqb vty₁ bs₁ ∗
        pointsToView tds id a aty (off + CerbMem.sizeofCtype tds vty₁) (.own q₂) dqb
          vty₂ bs₂) := by
  unfold pointsToView
  iintro ⟨Hm, %hpure, Hb⟩
  obtain ⟨hbound, hlen⟩ := hpure
  have hlapp : (bs₁ ++ bs₂).length = bs₁.length + bs₂.length :=
    List.length_append
  have hlen₂ : bs₂.length = CerbMem.sizeofCtype tds vty₂ := by omega
  icases (metaOwn_fractional id (objCell tds a aty true false) q₁ q₂).1 $$ Hm
    with ⟨Hm₁, Hm₂⟩
  icases (bytesOwn_append (a + (off : Int)) dqb bs₁ bs₂).1 $$ Hb with ⟨Hb₁, Hb₂⟩
  isplitl [Hm₁ Hb₁]
  · isplitl [Hm₁]
    · iexact Hm₁
    isplit
    · ipureintro
      exact ⟨by omega, hlen₁⟩
    · iexact Hb₁
  · isplitl [Hm₂]
    · iexact Hm₂
    isplit
    · ipureintro
      exact ⟨by omega, hlen₂⟩
    · rw [show a + ((off + CerbMem.sizeofCtype tds vty₁ : Nat) : Int) =
        a + (off : Int) + ((bs₁.length : Nat) : Int) by omega]
      iexact Hb₂

/-- SUBRANGE JOIN: the converse — two adjacent typed subviews of the
    same allocation join into the containing view (fractions add,
    byte ranges concatenate). -/
theorem pointsToView_join (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype) (off : Nat)
    (q₁ q₂ : Qp) (dqb : DFrac) (vty vty₁ vty₂ : ctype)
    (bs₁ bs₂ : List CerbMem.AbsByte)
    (hsz : CerbMem.sizeofCtype tds vty =
      CerbMem.sizeofCtype tds vty₁ + CerbMem.sizeofCtype tds vty₂)
    (hbound : off + CerbMem.sizeofCtype tds vty ≤ CerbMem.sizeofCtype tds aty) :
    iprop(pointsToView tds (GF := GF) id a aty off (.own q₁) dqb vty₁ bs₁ ∗
      pointsToView tds id a aty (off + CerbMem.sizeofCtype tds vty₁) (.own q₂) dqb
        vty₂ bs₂) ⊢
      pointsToView tds id a aty off (.own (q₁ + q₂)) dqb vty (bs₁ ++ bs₂) := by
  unfold pointsToView
  iintro ⟨⟨Hm₁, %hp₁, Hb₁⟩, Hm₂, %hp₂, Hb₂⟩
  obtain ⟨hbound₁, hlen₁⟩ := hp₁
  obtain ⟨hbound₂, hlen₂⟩ := hp₂
  isplitl [Hm₁ Hm₂]
  · iapply (metaOwn_fractional id (objCell tds a aty true false) q₁ q₂).2
    isplitl [Hm₁]
    · iexact Hm₁
    · iexact Hm₂
  isplit
  · ipureintro
    refine ⟨hbound, ?_⟩
    have hlapp : (bs₁ ++ bs₂).length = bs₁.length + bs₂.length :=
      List.length_append
    omega
  · iapply (bytesOwn_append (a + (off : Int)) dqb bs₁ bs₂).2
    isplitl [Hb₁]
    · iexact Hb₁
    · rw [show a + (off : Int) + ((bs₁.length : Nat) : Int) =
        a + ((off + CerbMem.sizeofCtype tds vty₁ : Nat) : Int) by omega]
      iexact Hb₂

/-- The whole-cell ownership IS the maximal view (plus the image's
    decode-inertness fact) — both directions. -/
theorem cellOwn_view (tds : CerbTags.TagDefsMap) (i : Int) (dq : DFrac) (c : SpikeCell) :
    cellOwn tds (GF := GF) i dq c ⊣⊢
      iprop(pointsToView tds i c.addr c.ty 0 dq dq c.ty c.bytes ∗
        ⌜decIndep tds c.addr c.ty c.bytes⌝) := by
  unfold cellOwn pointsToView metaOf
  constructor
  · iintro ⟨Hm, Hb, %hpure⟩
    obtain ⟨hlen, hdec⟩ := hpure
    isplitl [Hm Hb]
    · iframe Hm
      isplit
      · ipureintro
        exact ⟨by omega, hlen⟩
      · rw [show c.addr + ((0 : Nat) : Int) = c.addr by omega]
        iexact Hb
    · ipureintro
      exact hdec
  · iintro ⟨⟨Hm, %hpure, Hb⟩, %hdec⟩
    obtain ⟨-, hlen⟩ := hpure
    iframe Hm
    isplit
    · rw [show c.addr + ((0 : Nat) : Int) = c.addr by omega]
      iexact Hb
    · ipureintro
      exact ⟨hlen, hdec⟩

end ViewLaws

/-! ## The three allocation facts (alloc arc P4.1): fractional
ranges and cells, agreement, the persistent metadata stratum, and
the provenance-preserving pointer shift (header, THE THREE
ALLOCATION FACTS). -/

section AllocFacts

variable [SpikeGS hlc GF]

open Iris.BI

/-- The fragment pointer shape is injective in both components. -/
theorem cellPtr_inj {i₁ a₁ i₂ a₂ : Int} (h : cellPtr i₁ a₁ = cellPtr i₂ a₂) :
    i₁ = i₂ ∧ a₁ = a₂ := by
  unfold cellPtr at h
  cases h
  exact ⟨rfl, rfl⟩

/-- PROVENANCE-PRESERVING POINTER SHIFT: the engine's own pointer
    arithmetic (`CerbMem.arrayShiftPtrval`, the `PVconcrete` arm) on a
    fragment pointer keeps the allocation id and advances the address
    by `k · sizeof ty` — for every non-void element type (void is the
    GNU byte-granular exception in the engine's arm). Bounds are NOT
    checked by the shift (the concrete memory model's arithmetic is
    unchecked); they are enforced at the ACCESS, by the in-bounds
    conjunct every view carries — so a shifted pointer is usable
    exactly when the sub-range it names is in bounds. The exhibits'
    per-type shift facts are instances. -/
theorem cellPtr_arrayShift (tds : CerbTags.TagDefsMap) (id a : Int) (ty : ctype)
    (k : Int) (hty : ∀ q, ty ≠ Ctype q .Void0) :
    CerbMem.arrayShiftPtrval tds (cellPtr id a) ty (CerbMem.integerIval k) =
      cellPtr id (a + k * ((CerbMem.sizeofCtype tds ty : Nat) : Int)) := by
  obtain ⟨q, t⟩ := ty
  cases t <;> first | exact absurd rfl (hty q) | rfl

/-- One byte at one address: two fractions agree on the byte. -/
theorem byteOwn_agree (k : Int) (dq₁ dq₂ : DFrac) (b₁ b₂ : CerbMem.AbsByte) :
    iprop(byteOwn (GF := GF) k dq₁ b₁ ∗ byteOwn k dq₂ b₂) ⊢
      (⌜b₁ = b₂⌝ : IProp GF) := by
  letI := SpikeGS.byteGS (hlc := hlc) (GF := GF)
  exact pointsTo_agree

/-- RANGE FRACTIONAL (Boyland fractional permissions, per byte): a
    byte range at fraction `q₁ + q₂` is the range at `q₁` next to the
    range at `q₂` — both directions. -/
theorem bytesOwn_fractional (a : Int) (q₁ q₂ : Qp) (bs : List CerbMem.AbsByte) :
    bytesOwn (GF := GF) a (.own (q₁ + q₂)) bs ⊣⊢
      iprop(bytesOwn a (.own q₁) bs ∗ bytesOwn a (.own q₂) bs) := by
  induction bs generalizing a with
  | nil =>
    simp only [bytesOwn_nil]
    exact BI.emp_sep.symm
  | cons b bs ih =>
    simp only [bytesOwn_cons]
    have hb : byteOwn (GF := GF) a (.own (q₁ + q₂)) b ⊣⊢
        iprop(byteOwn a (.own q₁) b ∗ byteOwn a (.own q₂) b) := by
      letI := SpikeGS.byteGS (hlc := hlc) (GF := GF)
      exact Fractional.fractional
        (Φ := fun q => pointsTo (G := SpikeGS.byteGS) a (.own q) b) q₁ q₂
    exact (BI.sep_congr hb (ih (a + 1))).trans BI.sep_sep_sep_comm

/-- RANGE AGREEMENT: two ranges at one address of one length agree
    bytewise. -/
theorem bytesOwn_agree (a : Int) (dq₁ dq₂ : DFrac) (bs₁ bs₂ : List CerbMem.AbsByte)
    (hlen : bs₁.length = bs₂.length) :
    iprop(bytesOwn (GF := GF) a dq₁ bs₁ ∗ bytesOwn a dq₂ bs₂) ⊢
      (⌜bs₁ = bs₂⌝ : IProp GF) := by
  induction bs₁ generalizing a bs₂ with
  | nil =>
    obtain rfl : bs₂ = [] := List.length_eq_zero_iff.mp hlen.symm
    iintro ⟨-, -⟩
    ipureintro
    rfl
  | cons b₁ bs₁ ih =>
    cases bs₂ with
    | nil => simp at hlen
    | cons b₂ bs₂ =>
      simp only [bytesOwn_cons]
      iintro ⟨⟨H₁, Hs₁⟩, H₂, Hs₂⟩
      ihave %hb : ⌜b₁ = b₂⌝ $$ [H₁ H₂]
      · iapply byteOwn_agree a dq₁ dq₂ b₁ b₂ $$ [$H₁ $H₂]
      ihave %hs : ⌜bs₁ = bs₂⌝ $$ [Hs₁ Hs₂]
      · iapply ih (a + 1) bs₂ (by simpa using hlen) $$ [$Hs₁ $Hs₂]
      ipureintro
      rw [hb, hs]

/-- VIEW FRACTIONAL: a typed view at fraction `q₁ + q₂` (metadata and
    bytes alike) is the two views at `q₁` and `q₂` — the classical
    fractional-permission law at the typed-view stratum (read-sharing
    of one range). -/
theorem pointsToView_fractional (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype)
    (off : Nat) (q₁ q₂ : Qp) (vty : ctype) (bs : List CerbMem.AbsByte) :
    pointsToView tds (GF := GF) id a aty off (.own (q₁ + q₂)) (.own (q₁ + q₂)) vty bs ⊣⊢
      iprop(pointsToView tds id a aty off (.own q₁) (.own q₁) vty bs ∗
        pointsToView tds id a aty off (.own q₂) (.own q₂) vty bs) := by
  unfold pointsToView
  constructor
  · iintro ⟨Hm, %hp, Hb⟩
    icases (metaOwn_fractional id (objCell tds a aty true false) q₁ q₂).1 $$ Hm
      with ⟨Hm₁, Hm₂⟩
    icases (bytesOwn_fractional (a + (off : Int)) q₁ q₂ bs).1 $$ Hb with ⟨Hb₁, Hb₂⟩
    isplitl [Hm₁ Hb₁]
    · isplitl [Hm₁]
      · iexact Hm₁
      isplit
      · ipureintro
        exact hp
      · iexact Hb₁
    · isplitl [Hm₂]
      · iexact Hm₂
      isplit
      · ipureintro
        exact hp
      · iexact Hb₂
  · iintro ⟨⟨Hm₁, %hp, Hb₁⟩, Hm₂, -, Hb₂⟩
    isplitl [Hm₁ Hm₂]
    · iapply (metaOwn_fractional id (objCell tds a aty true false) q₁ q₂).2
      isplitl [Hm₁]
      · iexact Hm₁
      · iexact Hm₂
    isplit
    · ipureintro
      exact hp
    · iapply (bytesOwn_fractional (a + (off : Int)) q₁ q₂ bs).2
      isplitl [Hb₁]
      · iexact Hb₁
      · iexact Hb₂

/-- METADATA/BOUNDS AGREEMENT: two views of one allocation agree on
    its base address and allocation type (hence on its size and on
    every in-bounds fact). -/
theorem pointsToView_agree (tds : CerbTags.TagDefsMap) (id a a' : Int) (aty aty' : ctype)
    (off off' : Nat) (dqm dqb dqm' dqb' : DFrac) (vty vty' : ctype)
    (bs bs' : List CerbMem.AbsByte) :
    iprop(pointsToView tds (GF := GF) id a aty off dqm dqb vty bs ∗
      pointsToView tds id a' aty' off' dqm' dqb' vty' bs') ⊢
      (⌜a = a' ∧ aty = aty'⌝ : IProp GF) := by
  unfold pointsToView
  iintro ⟨⟨Hm, -, -⟩, Hm', -, -⟩
  ihave %h : ⌜objCell tds a aty true false = objCell tds a' aty' true false⌝ $$ [Hm Hm']
  · iapply metaOwn_agree id dqm dqm' _ _ $$ [$Hm $Hm']
  ipureintro
  simp only [objCell, MetaCell.mk.injEq, Option.some.injEq] at h
  exact ⟨h.1, h.2.1⟩

/-- CELL FRACTIONAL: whole-cell ownership splits at any fraction sum. -/
theorem cellOwn_fractional (tds : CerbTags.TagDefsMap) (i : Int) (q₁ q₂ : Qp)
    (c : SpikeCell) :
    cellOwn tds (GF := GF) i (.own (q₁ + q₂)) c ⊣⊢
      iprop(cellOwn tds i (.own q₁) c ∗ cellOwn tds i (.own q₂) c) := by
  unfold cellOwn
  constructor
  · iintro ⟨Hm, Hb, %hp⟩
    icases (metaOwn_fractional i (metaOf tds c) q₁ q₂).1 $$ Hm with ⟨Hm₁, Hm₂⟩
    icases (bytesOwn_fractional c.addr q₁ q₂ c.bytes).1 $$ Hb with ⟨Hb₁, Hb₂⟩
    isplitl [Hm₁ Hb₁]
    · isplitl [Hm₁]
      · iexact Hm₁
      isplitl [Hb₁]
      · iexact Hb₁
      · ipureintro
        exact hp
    · isplitl [Hm₂]
      · iexact Hm₂
      isplitl [Hb₂]
      · iexact Hb₂
      · ipureintro
        exact hp
  · iintro ⟨⟨Hm₁, Hb₁, %hp⟩, Hm₂, Hb₂, -⟩
    isplitl [Hm₁ Hm₂]
    · iapply (metaOwn_fractional i (metaOf tds c) q₁ q₂).2
      isplitl [Hm₁]
      · iexact Hm₁
      · iexact Hm₂
    isplitl [Hb₁ Hb₂]
    · iapply (bytesOwn_fractional c.addr q₁ q₂ c.bytes).2
      isplitl [Hb₁]
      · iexact Hb₁
      · iexact Hb₂
    · ipureintro
      exact hp

/-- POINTS-TO FRACTIONAL (the textbook law): `pv ↦c{q₁+q₂} ty ; bs ⊣⊢
    pv ↦c{q₁} ty ; bs ∗ pv ↦c{q₂} ty ; bs`. -/
theorem pointsToCell_fractional (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    (q₁ q₂ : Qp) (ty : ctype) (bs : List CerbMem.AbsByte) :
    pointsToCell tds (GF := GF) pv (.own (q₁ + q₂)) ty bs ⊣⊢
      iprop(pointsToCell tds pv (.own q₁) ty bs ∗ pointsToCell tds pv (.own q₂) ty bs) := by
  unfold pointsToCell
  constructor
  · iintro ⟨%id, %a, %hpv, Hc⟩
    icases (cellOwn_fractional tds id q₁ q₂ ⟨a, ty, bs⟩).1 $$ Hc with ⟨Hc₁, Hc₂⟩
    isplitl [Hc₁]
    · iexists id, a
      isplit
      · ipureintro
        exact hpv
      · iexact Hc₁
    · iexists id, a
      isplit
      · ipureintro
        exact hpv
      · iexact Hc₂
  · iintro ⟨⟨%id₁, %a₁, %h₁, Hc₁⟩, %id₂, %a₂, %h₂, Hc₂⟩
    obtain ⟨rfl, rfl⟩ := cellPtr_inj (h₁.symm.trans h₂)
    iexists id₁, a₁
    isplit
    · ipureintro
      exact h₁
    · iapply (cellOwn_fractional tds id₁ q₁ q₂ ⟨a₁, ty, bs⟩).2
      isplitl [Hc₁]
      · iexact Hc₁
      · iexact Hc₂

/-- POINTS-TO AGREEMENT: two points-to of one pointer, at any
    fractions, agree on the type and the contents (metadata agreement
    through the views; contents through the byte ranges). -/
theorem pointsToCell_agree (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    (dq₁ dq₂ : DFrac) (ty₁ ty₂ : ctype) (bs₁ bs₂ : List CerbMem.AbsByte) :
    iprop(pointsToCell tds (GF := GF) pv dq₁ ty₁ bs₁ ∗ pointsToCell tds pv dq₂ ty₂ bs₂) ⊢
      (⌜ty₁ = ty₂ ∧ bs₁ = bs₂⌝ : IProp GF) := by
  unfold pointsToCell
  iintro ⟨⟨%id₁, %a₁, %h₁, Hc₁⟩, %id₂, %a₂, %h₂, Hc₂⟩
  obtain ⟨rfl, rfl⟩ := cellPtr_inj (h₁.symm.trans h₂)
  icases (cellOwn_view tds id₁ dq₁ ⟨a₁, ty₁, bs₁⟩).1 $$ Hc₁ with ⟨Hv₁, -⟩
  icases (cellOwn_view tds id₁ dq₂ ⟨a₁, ty₂, bs₂⟩).1 $$ Hc₂ with ⟨Hv₂, -⟩
  ihave %hty : ⌜a₁ = a₁ ∧ ty₁ = ty₂⌝ $$ [Hv₁ Hv₂]
  · iapply pointsToView_agree tds id₁ a₁ a₁ ty₁ ty₂ 0 0 dq₁ dq₁ dq₂ dq₂ ty₁ ty₂ bs₁ bs₂
      $$ [$Hv₁ $Hv₂]
  obtain ⟨-, rfl⟩ := hty
  icases (pointsToView_iff tds id₁ a₁ ty₁ 0 dq₁ dq₁ ty₁ bs₁).1 $$ Hv₁ with ⟨-, %hp₁, Hb₁⟩
  icases (pointsToView_iff tds id₁ a₁ ty₁ 0 dq₂ dq₂ ty₁ bs₂).1 $$ Hv₂ with ⟨-, %hp₂, Hb₂⟩
  ihave %hbs : ⌜bs₁ = bs₂⌝ $$ [Hb₁ Hb₂]
  · iapply bytesOwn_agree (a₁ + ((0 : Nat) : Int)) dq₁ dq₂ bs₁ bs₂ (by rw [hp₁.2, hp₂.2])
      $$ [$Hb₁ $Hb₂]
  ipureintro
  exact ⟨rfl, hbs⟩

/-- POINTS-TO COMBINE (agreement + join in one, the shape a shared
    reader recombines with): two fractions of one pointer agree and
    add up. -/
theorem pointsToCell_combine (tds : CerbTags.TagDefsMap) (pv : CerbMem.PointerValue)
    (q₁ q₂ : Qp) (ty₁ ty₂ : ctype) (bs₁ bs₂ : List CerbMem.AbsByte) :
    iprop(pointsToCell tds (GF := GF) pv (.own q₁) ty₁ bs₁ ∗
      pointsToCell tds pv (.own q₂) ty₂ bs₂) ⊢
      iprop(⌜ty₁ = ty₂ ∧ bs₁ = bs₂⌝ ∗ pointsToCell tds pv (.own (q₁ + q₂)) ty₁ bs₁) := by
  iintro ⟨H₁, H₂⟩
  ihave %h : ⌜ty₁ = ty₂ ∧ bs₁ = bs₂⌝ $$ [H₁ H₂]
  · iapply pointsToCell_agree tds pv (.own q₁) (.own q₂) ty₁ ty₂ bs₁ bs₂ $$ [$H₁ $H₂]
  obtain ⟨rfl, rfl⟩ := h
  isplit
  · ipureintro
    exact ⟨rfl, rfl⟩
  · iapply (pointsToCell_fractional tds pv q₁ q₂ ty₁ bs₁).2
    isplitl [H₁]
    · iexact H₁
    · iexact H₂

/-! ### The persistent stratum -/

/-- PERSISTENT ALLOCATION KNOWLEDGE: the allocation's id, base
    address, allocation type and size — the metadata cell at the
    DISCARDED fraction (the donor's `loc_in_bounds`/`alloc_meta`
    analogue). Persistent: metadata is immutable in this fragment, so
    the knowledge holds forever once obtained. -/
def allocMeta (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype) : IProp GF :=
  metaOwn id .discard (objCell tds a aty true false)

/-- THE PERSISTENCE LAW. -/
instance allocMeta_persistent (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype) :
    Persistent (allocMeta (GF := GF) tds id a aty) := by
  letI := SpikeGS.metaGS (hlc := hlc) (GF := GF)
  unfold allocMeta metaOwn
  infer_instance

/-- Persistent knowledge agrees (one allocation, one base, one type). -/
theorem allocMeta_agree (tds : CerbTags.TagDefsMap) (id a a' : Int) (aty aty' : ctype) :
    iprop(allocMeta (GF := GF) tds id a aty ∗ allocMeta tds id a' aty') ⊢
      (⌜a = a' ∧ aty = aty'⌝ : IProp GF) := by
  unfold allocMeta
  iintro ⟨H, H'⟩
  ihave %h : ⌜objCell tds a aty true false = objCell tds a' aty' true false⌝ $$ [H H']
  · iapply metaOwn_agree id .discard .discard _ _ $$ [$H $H']
  ipureintro
  simp only [objCell, MetaCell.mk.injEq, Option.some.injEq] at h
  exact ⟨h.1, h.2.1⟩

/-- PERSISTENT IN-BOUNDS KNOWLEDGE: `n` bytes at offset `off` of the
    allocation are inside it (the donor's `loc_in_bounds l n`). -/
def locInBounds (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype) (off n : Nat) :
    IProp GF :=
  iprop(allocMeta tds id a aty ∗ ⌜off + n ≤ CerbMem.sizeofCtype tds aty⌝)

instance locInBounds_persistent (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype)
    (off n : Nat) : Persistent (locInBounds (GF := GF) tds id a aty off n) := by
  unfold locInBounds
  infer_instance

/-- Metadata knowledge at any fraction can be made persistent — the
    fraction is given up for good (`pointsTo_persist`). -/
theorem metaOwn_persist (id : Int) (dq : DFrac) (mc : MetaCell) :
    metaOwn (GF := GF) id dq mc ⊢ iprop(|==> metaOwn id .discard mc) := by
  letI := SpikeGS.metaGS (hlc := hlc) (GF := GF)
  exact BI.wand_entails pointsTo_persist

/-- A view trades its metadata fraction for PERSISTENT metadata
    knowledge; its bytes are untouched. -/
theorem pointsToView_persist (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype)
    (off : Nat) (dqm dqb : DFrac) (vty : ctype) (bs : List CerbMem.AbsByte) :
    pointsToView tds (GF := GF) id a aty off dqm dqb vty bs ⊢
      iprop(|==> pointsToView tds id a aty off .discard dqb vty bs) := by
  unfold pointsToView
  iintro ⟨Hm, %hp, Hb⟩
  imod (metaOwn_persist id dqm _) $$ Hm with Hm
  imodintro
  isplitl [Hm]
  · iexact Hm
  isplit
  · ipureintro
    exact hp
  · iexact Hb

/-- A persistent-metadata view yields its in-bounds knowledge and
    keeps itself (the persistence law at work). -/
theorem pointsToView_locInBounds (tds : CerbTags.TagDefsMap) (id a : Int) (aty : ctype)
    (off : Nat) (dqb : DFrac) (vty : ctype) (bs : List CerbMem.AbsByte) :
    pointsToView tds (GF := GF) id a aty off .discard dqb vty bs ⊢
      iprop(locInBounds tds id a aty off (CerbMem.sizeofCtype tds vty) ∗
        pointsToView tds id a aty off .discard dqb vty bs) := by
  refine persistent_entails_right ?_
  unfold pointsToView locInBounds allocMeta
  iintro ⟨Hm, %hp, -⟩
  isplitl [Hm]
  · iexact Hm
  · ipureintro
    exact hp.1

end AllocFacts

/-! ## The abstract allocation capacity (alloc arc P1.1)

`allocCap reqs` certifies that the known finite request list `reqs`
will not hit the allocator's out-of-memory kill arm — the charter's
recommended abstract finite allocation-capacity resource, faithful
to the deterministic downward cursor while hiding it.

IMPLEMENTATION (this module and the create-rule internals only):
existential ownership of the cursor fragment plus a pure `PlanFits`
proof. CLIENT DISCIPLINE (the public abstraction): clients use ONLY
the introduction/weakening lemmas below plus the public create
rules; client-visible statements never name `AllocCursor`,
`lastAddress`/`nextAllocId`, `freshBase` or `cursorOwn` (the P1
grep test, recorded in the slice notes). -/

section AllocCap

/-- The abstract finite allocation capacity for a request plan. The
    machine bound on the hidden cursor (alloc arc P2) is what lets
    the public create rules export address-WF bounds for the fresh
    pointer (`freshBase_lt_two64`) without naming the cursor. -/
def allocCap [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (reqs : List AllocReq) : IProp GF :=
  iprop(∃ c : AllocCursor, cursorOwn c ∗
    ⌜PlanFits tds c reqs ∧ c.lastAddr ≤ 2 ^ 64⌝)

/-- Introduction (implementation/launch side): cursor ownership plus
    a fitting plan at a machine-bounded cursor. Clients receive
    `allocCap` from the allocation-aware launchers; they never build
    it. -/
theorem allocCap_intro [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (c : AllocCursor)
    (reqs : List AllocReq) (hfit : PlanFits tds c reqs)
    (hla : c.lastAddr ≤ 2 ^ 64) :
    cursorOwn (GF := GF) c ⊢ allocCap tds reqs := by
  unfold allocCap
  iintro Hc
  iexists c
  isplitl [Hc]
  · iexact Hc
  · ipureintro
    exact ⟨hfit, hla⟩

/-- Weakening: capacity for a longer plan serves any PREFIX (a
    client may stop allocating early; it may never reorder or skip
    a request — `planFits_order_sensitive`). -/
theorem allocCap_weaken [SpikeGS hlc GF] (tds : CerbTags.TagDefsMap) (reqs rest : List AllocReq) :
    allocCap tds (GF := GF) (reqs ++ rest) ⊢ allocCap tds reqs := by
  unfold allocCap
  iintro ⟨%c, Hc, %hfit⟩
  iexists c
  isplitl [Hc]
  · iexact Hc
  · ipureintro
    exact ⟨hfit.1.prefix, hfit.2⟩

end AllocCap

/-! ## Ghost extraction and update (the rule-facing interp lemmas) -/

section GhostOps

variable [SpikeGS hlc GF]

open Iris.BI Iris.Std.PartialMap

/-! Explicit-instance wrappers over the GenHeap operations. The three
heaps share the key type, so none is registered as a bare `genHeapGS`
instance; each wrapper pins its heap by a local `letI`. -/

theorem byteHeap_valid {mb : SpikeHeapF CerbMem.AbsByte} {k : Int}
    {dq : DFrac} {b : CerbMem.AbsByte} :
    iprop(byteInterp (GF := GF) mb ∗ byteOwn k dq b) ==∗
      (⌜Iris.Std.PartialMap.get? mb k = some b⌝ : IProp GF) := by
  letI := SpikeGS.byteGS (hlc := hlc) (GF := GF)
  exact genHeap_valid

theorem metaHeap_valid {mm : SpikeHeapF MetaCell} {id : Int}
    {dq : DFrac} {mc : MetaCell} :
    iprop(metaInterp (GF := GF) mm ∗ metaOwn id dq mc) ==∗
      (⌜Iris.Std.PartialMap.get? mm id = some mc⌝ : IProp GF) := by
  letI := SpikeGS.metaGS (hlc := hlc) (GF := GF)
  exact genHeap_valid

theorem cursorHeap_valid {mk : SpikeHeapF AllocCursor} {c : AllocCursor} :
    iprop(cursorInterp (GF := GF) mk ∗ cursorOwn c) ==∗
      (⌜Iris.Std.PartialMap.get? mk 0 = some c⌝ : IProp GF) := by
  letI := SpikeGS.cursorGS (hlc := hlc) (GF := GF)
  exact genHeap_valid

theorem byteHeap_update {mb : SpikeHeapF CerbMem.AbsByte} {k : Int}
    {b : CerbMem.AbsByte} (b' : CerbMem.AbsByte) :
    iprop(byteInterp (GF := GF) mb ∗ byteOwn k (.own 1) b) ==∗
      iprop(byteInterp (Iris.Std.PartialMap.insert mb k b') ∗
        byteOwn k (.own 1) b') := by
  letI := SpikeGS.byteGS (hlc := hlc) (GF := GF)
  exact genHeap_update

theorem cursorHeap_update {mk : SpikeHeapF AllocCursor} {c : AllocCursor}
    (c' : AllocCursor) :
    iprop(cursorInterp (GF := GF) mk ∗ cursorOwn c) ==∗
      iprop(cursorInterp (Iris.Std.PartialMap.insert mk 0 c') ∗
        cursorOwn c') := by
  letI := SpikeGS.cursorGS (hlc := hlc) (GF := GF)
  exact genHeap_update

theorem metaHeap_alloc {mm : SpikeHeapF MetaCell} {id : Int}
    (mc : MetaCell) (hfresh : Iris.Std.PartialMap.get? mm id = none) :
    metaInterp (GF := GF) mm ==∗
      iprop(metaInterp (Iris.Std.PartialMap.insert mm id mc) ∗
        metaOwn id (.own 1) mc) := by
  letI := SpikeGS.metaGS (hlc := hlc) (GF := GF)
  exact BI.entails_wand ((genHeap_alloc (v := mc) hfresh).trans
    (bupd_mono (BI.sep_mono .rfl BI.sep_elim_left)))

/-- Cursor-heap allocation (alloc arc P1.3 — the previously MISSING
    launch step, R-01): mint the cursor cell at key 0 from an empty
    (or 0-free) cursor heap, delivering the exclusive `cursorOwn`
    fragment. Mirror of `metaHeap_alloc`. -/
theorem cursorHeap_alloc {mk : SpikeHeapF AllocCursor} (c : AllocCursor)
    (hfresh : Iris.Std.PartialMap.get? mk 0 = none) :
    cursorInterp (GF := GF) mk ==∗
      iprop(cursorInterp (Iris.Std.PartialMap.insert mk 0 c) ∗
        cursorOwn c) := by
  letI := SpikeGS.cursorGS (hlc := hlc) (GF := GF)
  exact BI.entails_wand ((genHeap_alloc (v := c) hfresh).trans
    (bupd_mono (BI.sep_mono .rfl BI.sep_elim_left)))

theorem byteHeap_alloc_big {mb : SpikeHeapF CerbMem.AbsByte}
    (mbnew : SpikeHeapF CerbMem.AbsByte) (hdisj : mbnew ##ₘ mb) :
    byteInterp (GF := GF) mb ==∗
      iprop(byteInterp (Iris.Std.PartialMap.union mbnew mb) ∗
        ([∗map] k ↦ b ∈ mbnew, byteOwn k (.own 1) b)) := by
  exact BI.entails_wand
    ((@genHeap_alloc_big GF Int CerbMem.AbsByte SpikeHeapF _
        (SpikeGS.byteGS) _ mbnew mb hdisj).trans
      (bupd_mono (BI.sep_mono .rfl BI.sep_elim_left)))

/-- Range extraction: interp + range ownership pin every key of the
    range in the authoritative byte map. -/
theorem bytesOwn_get (mb : SpikeHeapF CerbMem.AbsByte) (a : Int)
    (dq : DFrac) (bs : List CerbMem.AbsByte) :
    iprop(byteInterp (GF := GF) mb ∗ bytesOwn a dq bs) ⊢
      (⌜∀ (j : Nat), j < bs.length →
        Iris.Std.PartialMap.get? mb (a + (j : Int)) = bs[j]?⌝ : IProp GF) := by
  induction bs generalizing a with
  | nil =>
    iintro ⟨-, -⟩
    ipureintro
    intro j hj
    simp at hj
  | cons b bs ih =>
    rw [bytesOwn_cons]
    iintro ⟨Hi, Hb, Hbs⟩
    ihave %hhead : ⌜Iris.Std.PartialMap.get? mb a = some b⌝ $$ [Hi Hb]
    · ihave >%h := byteHeap_valid $$ [$Hi $Hb]
      itrivial
    ihave %htail : ⌜∀ (j : Nat), j < bs.length →
        Iris.Std.PartialMap.get? mb ((a + 1) + (j : Int)) = bs[j]?⌝ $$ [Hi Hbs]
    · iapply (ih (a + 1)) $$ [$Hi $Hbs]
    ipureintro
    intro j hj
    cases j with
    | zero =>
      simpa using hhead
    | succ j' =>
      rw [show a + ((j' + 1 : Nat) : Int) = (a + 1) + (j' : Int) by omega]
      rw [htail j' (by simpa using hj)]
      rfl

/-- The range readout against the coupling: the range's byte image
    is exactly what the engine reads there. -/
theorem bytesOwn_read {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) (a : Int)
    (dq : DFrac) (bs : List CerbMem.AbsByte) :
    iprop(byteInterp (GF := GF) mb ∗ bytesOwn a dq bs) ⊢
      (⌜CerbMem.readBytesFrom σ a bs.length = bs⌝ : IProp GF) := by
  iintro ⟨Hi, Hb⟩
  ihave %hget : ⌜∀ (j : Nat), j < bs.length →
      Iris.Std.PartialMap.get? mb (a + (j : Int)) = bs[j]?⌝ $$ [Hi Hb]
  · iapply bytesOwn_get mb a dq bs $$ [$Hi $Hb]
  ipureintro
  apply readBytesFrom_of_byteAt
  intro i hi
  have h := hget i hi
  rw [List.getElem?_eq_getElem hi] at h
  exact hG.bytes _ _ h

/-- Range update: full range ownership updates the range wholesale
    (the store footprint IS the view's extent). -/
theorem bytesOwn_update (mb : SpikeHeapF CerbMem.AbsByte) (a : Int)
    (bs bs' : List CerbMem.AbsByte) (hlen : bs'.length = bs.length) :
    iprop(byteInterp (GF := GF) mb ∗ bytesOwn a (.own 1) bs) ==∗
      iprop(byteInterp (insertRange mb a bs') ∗
        bytesOwn a (.own 1) bs') := by
  induction bs generalizing a mb bs' with
  | nil =>
    obtain rfl : bs' = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    iintro ⟨Hi, -⟩
    imodintro
    simp only [insertRange, bytesOwn_nil]
    isplitl [Hi]
    · iexact Hi
    · ipureintro
      trivial
  | cons b bs ih =>
    cases bs' with
    | nil => simp at hlen
    | cons b' bs'' =>
      rw [bytesOwn_cons, bytesOwn_cons]
      iintro ⟨Hi, Hb, Hbs⟩
      imod (byteHeap_update b') $$ [$Hi $Hb] with ⟨Hi, Hb⟩
      imod (ih (Iris.Std.PartialMap.insert mb a b') (a + 1) bs''
        (by simpa using hlen)) $$ [$Hi $Hbs] with ⟨Hi, Hbs⟩
      imodintro
      rw [show insertRange mb a (b' :: bs'') =
        insertRange (Iris.Std.PartialMap.insert mb a b') (a + 1) bs'' from rfl]
      isplitl [Hi]
      · iexact Hi
      isplitl [Hb]
      · iexact Hb
      · iexact Hbs

/-- A fresh range map's fragment big-sep is exactly the range
    ownership. -/
theorem bigSepM_rangeMap (a : Int) (bs : List CerbMem.AbsByte) :
    iprop([∗map] k ↦ b ∈ rangeMap a bs,
        byteOwn (GF := GF) (hlc := hlc) k (.own 1) b) ⊢
      bytesOwn a (.own 1) bs := by
  induction bs generalizing a with
  | nil =>
    iintro -
    simp only [bytesOwn_nil]
    ipureintro
    trivial
  | cons b bs ih =>
    have hfresh : Iris.Std.PartialMap.get? (rangeMap (a + 1) bs) a = none := by
      rw [rangeMap_get?]
      rw [if_neg (by omega)]
    show iprop([∗map] k ↦ v ∈ Iris.Std.PartialMap.insert (rangeMap (a + 1) bs) a b,
        byteOwn k (.own 1) v) ⊢ _
    iintro H
    icases (BigSepM.bigSepM_insert (Φ := fun k v =>
        byteOwn (GF := GF) (hlc := hlc) k (.own 1) v)
        hfresh).1 $$ H with ⟨Hb, Hbs⟩
    rw [bytesOwn_cons]
    isplitl [Hb]
    · iexact Hb
    · iapply ih (a + 1) $$ Hbs

/-- Full metadata ownership is exclusive per allocation id. -/
theorem metaOwn_ne {i₁ i₂ : Int} {dq₂ : DFrac} {mc₁ mc₂ : MetaCell} :
    ⊢@{IProp GF} metaOwn (hlc := hlc) i₁ (.own 1) mc₁ -∗
      metaOwn i₂ dq₂ mc₂ -∗ ⌜i₁ ≠ i₂⌝ := by
  letI := SpikeGS.metaGS (hlc := hlc) (GF := GF)
  exact pointsTo_ne

/-- Whole-cell ownership against the coupling: the cell's full
    engine-facing backing facts (the readout workhorse — exhibits
    conclude `CellCoh` of the final state from surviving cells). -/
theorem cellOwn_cellCoh {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor} (tds : CerbTags.TagDefsMap)
    (hG : CohG σ mm mb mk) (i : Int) (dq : DFrac) (c : SpikeCell) :
    iprop(metaInterp (GF := GF) mm ∗ byteInterp mb ∗ cellOwn tds i dq c) ⊢
      (⌜CellCoh tds σ i c ∧
        Iris.Std.PartialMap.get? mm i = some (metaOf tds c)⌝ : IProp GF) := by
  iintro ⟨Hmi, Hbi, Hcell⟩
  icases (cellOwn_iff tds i dq c).mp $$ Hcell with ⟨Hm, Hb, %Hpure⟩
  obtain ⟨hlen, hdec⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm i = some (metaOf tds c)⌝ $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  ihave %Hread : ⌜CerbMem.readBytesFrom σ c.addr c.bytes.length = c.bytes⌝
      $$ [Hbi Hb]
  · iapply bytesOwn_read hG c.addr dq c.bytes $$ [$Hbi $Hb]
  ipureintro
  exact ⟨CellCoh.ofParts tds (hG.metas i _ Hgetm) hlen (hlen ▸ Hread) hdec, Hgetm⟩

end GhostOps

/-! ## Coupling preservation (pure) -/

section CohGLemmas

open Iris.Std.PartialMap CerbMem

/-- CohG survives a byte write whose every target key is
    ghost-tracked (a full-ownership range store): the byte map is
    updated wholesale, metadata and cursor ride through. -/
theorem CohG.storeRange {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) (a : Int) (bs' : List AbsByte)
    (hcover : ∀ (j : Nat), j < bs'.length →
      ∃ b, get? mb (a + (j : Int)) = some b) :
    CohG (writeBytesTo σ a bs') mm (insertRange mb a bs') mk := by
  have hnext : (writeBytesTo σ a bs').nextAllocId = σ.nextAllocId := rfl
  have hlast : (writeBytesTo σ a bs').lastAddress = σ.lastAddress := rfl
  refine ⟨?_, hG.metas_disj, ?_, hG.cursor_key, ?_, ?_, ?_, ?_⟩
  · intro id mc hget
    exact (hG.metas id mc hget).writeBytes a bs'
  · intro k b hget
    rw [insertRange_get?] at hget
    by_cases hin : a ≤ k ∧ k < a + bs'.length
    · rw [if_pos hin] at hget
      rw [byteAt_writeBytesTo_in σ a bs' k hin.1 hin.2]
      have := List.getElem?_eq_getElem
        (l := bs') (i := (k - a).toNat) (by omega)
      rw [this] at hget
      exact Option.some.inj hget
    · rw [if_neg hin] at hget
      rw [byteAt_writeBytesTo_out σ a bs' k hin]
      exact hG.bytes k b hget
  · intro c hget
    rw [hlast, hnext]
    exact hG.cursor c hget
  · intro hne
    exact (hG.wf hne).writeBytesTo a bs'
  · intro hne k b hget
    rw [hlast]
    rw [insertRange_get?] at hget
    by_cases hin : a ≤ k ∧ k < a + bs'.length
    · -- the written keys were already tracked (hcover), so the old
      -- lower bound applies to them
      obtain ⟨b₀, hb₀⟩ := hcover (k - a).toNat (by omega)
      have : a + (((k - a).toNat : Nat) : Int) = k := by omega
      rw [this] at hb₀
      exact hG.cur_byte_lo hne k b₀ hb₀
    · rw [if_neg hin] at hget
      exact hG.cur_byte_lo hne k b hget
  · intro hne id mc hget
    rw [hlast]
    exact hG.cur_meta_lo hne id mc hget

/-- CohG survives an allocation: the cursor advances downward, the
    fresh metadata and the fresh (unspecified) byte range join the
    ghost maps, everything old rides above the new cursor. -/
theorem CohG.create {σ : Mem} {mm : SpikeHeapF MetaCell}
    {mb : SpikeHeapF AbsByte} {mk : SpikeHeapF AllocCursor} (tds : CerbTags.TagDefsMap)
    (hG : CohG σ mm mb mk) (pref : prefix0) (alignN : Int) (ty : ctype)
    (hsz : 0 < sizeofCtype tds ty) (hatom : atomicTy ty = false)
    (hcur : get? mk 0 = some ⟨σ.lastAddress, σ.nextAllocId⟩)
    (hnz : freshBase σ.lastAddress alignN (sizeofCtype tds ty) ≠ 0) :
    CohG
      (writeBytesTo
        { σ with
            nextAllocId := σ.nextAllocId + 1,
            lastAddress := freshBase σ.lastAddress alignN (sizeofCtype tds ty),
            allocations := σ.allocations.insert σ.nextAllocId
              { base := freshBase σ.lastAddress alignN (sizeofCtype tds ty),
                size := (sizeofCtype tds ty : Int),
                ty := some ty,
                isReadonly := .IsWritable,
                prefix_ := pref } }
        (freshBase σ.lastAddress alignN (sizeofCtype tds ty))
        (List.replicate (sizeofCtype tds ty) undefByte))
      (Iris.Std.PartialMap.insert mm σ.nextAllocId
        (objCell tds (freshBase σ.lastAddress alignN (sizeofCtype tds ty)) ty true false))
      (Iris.Std.PartialMap.union
        (rangeMap (freshBase σ.lastAddress alignN (sizeofCtype tds ty))
          (List.replicate (sizeofCtype tds ty) undefByte)) mb)
      (Iris.Std.PartialMap.insert mk 0
        ⟨freshBase σ.lastAddress alignN (sizeofCtype tds ty),
          σ.nextAllocId + 1⟩) := by
  have hcurne : get? mk 0 ≠ none := by
    rw [hcur]
    simp
  -- abbreviations (plain lets; the goal's occurrences are definitional)
  generalize hbase_def : freshBase σ.lastAddress alignN (sizeofCtype tds ty) = base
    at hnz ⊢
  -- the fresh base sits strictly below the old cursor with the whole
  -- range: 0 < base, base + sizeof ty ≤ lastAddress
  have hbase_nonneg : 0 ≤ base := by
    rw [← hbase_def]
    exact Int.natCast_nonneg _
  have hbase_pos : 0 < base := by omega
  have htoNat_pos : 0 < (σ.lastAddress - (sizeofCtype tds ty : Int)).toNat := by
    rcases Nat.eq_zero_or_pos (σ.lastAddress - (sizeofCtype tds ty : Int)).toNat
      with hz | hpos
    · exfalso
      apply hnz
      rw [← hbase_def]
      show (alignDown (σ.lastAddress - (sizeofCtype tds ty : Int)).toNat
        (alignN.toNat.max 1) : Int) = 0
      rw [hz]
      simp [alignDown]
    · exact hpos
  have hbase_le : base + (sizeofCtype tds ty : Int) ≤ σ.lastAddress := by
    have hle : alignDown (σ.lastAddress - (sizeofCtype tds ty : Int)).toNat
        (alignN.toNat.max 1) ≤
        (σ.lastAddress - (sizeofCtype tds ty : Int)).toNat := by
      unfold alignDown
      exact Nat.div_mul_le_self _ _
    rw [← hbase_def]
    show (alignDown (σ.lastAddress - (sizeofCtype tds ty : Int)).toNat
      (alignN.toNat.max 1) : Int) + (sizeofCtype tds ty : Int) ≤ σ.lastAddress
    omega
  have hreplen : (List.replicate (sizeofCtype tds ty) undefByte).length =
    sizeofCtype tds ty := by simp
  -- the fresh range is disjoint from every tracked byte (old bytes sit
  -- at or above the OLD cursor; the fresh range ends at or below it)
  have hbyte_hi : ∀ k b, get? mb k = some b →
      base + (sizeofCtype tds ty : Int) ≤ k := by
    intro k b hget
    exact Int.le_trans hbase_le (hG.cur_byte_lo hcurne k b hget)
  have hmeta_hi : ∀ id mc, get? mm id = some mc →
      base + (sizeofCtype tds ty : Int) ≤ mc.addr := by
    intro id mc hget
    exact Int.le_trans hbase_le (hG.cur_meta_lo hcurne id mc hget)
  -- the fresh range map's readout
  have hrange_get : ∀ k,
      get? (rangeMap base (List.replicate (sizeofCtype tds ty) undefByte)) k =
      if base ≤ k ∧ k < base + (sizeofCtype tds ty : Int) then some undefByte
      else none := by
    intro k
    rw [rangeMap_get?, hreplen]
    by_cases h : base ≤ k ∧ k < base + (sizeofCtype tds ty : Int)
    · rw [if_pos h, if_pos h,
        List.getElem?_eq_getElem
          (by rw [hreplen]; omega :
            (k - base).toNat < (List.replicate (sizeofCtype tds ty) undefByte).length),
        List.getElem_replicate]
    · rw [if_neg h, if_neg h]
  -- state-side readouts of the post-allocation state
  have hdead' : (writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } }
      base (List.replicate (sizeofCtype tds ty) undefByte)).deadAllocations =
      σ.deadAllocations := rfl
  have hnext' : (writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } }
      base (List.replicate (sizeofCtype tds ty) undefByte)).nextAllocId =
      σ.nextAllocId + 1 := rfl
  have hlast' : (writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } }
      base (List.replicate (sizeofCtype tds ty) undefByte)).lastAddress =
      base := rfl
  have halloc' : (writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } }
      base (List.replicate (sizeofCtype tds ty) undefByte)).allocations =
      σ.allocations.insert σ.nextAllocId
        { base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
          isReadonly := .IsWritable, prefix_ := pref } := rfl
  have hbytemid : ∀ k, byteAt
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } } k =
      byteAt σ k := fun _ => rfl
  have hallocs_get : ∀ (id : Int),
      (σ.allocations.insert σ.nextAllocId
        ({ base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
           isReadonly := .IsWritable, prefix_ := pref } : Allocation)).get? id =
      if σ.nextAllocId = id then
        some ({ base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
                isReadonly := .IsWritable, prefix_ := pref } : Allocation)
      else σ.allocations.get? id := by
    intro id
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- metas: the fresh cell is live, writable, typed, not dynamic;
    -- the old cells see none of their three readouts change
    intro id mc hget
    by_cases hid : id = σ.nextAllocId
    · subst hid
      rw [Iris.Std.get?_insert_eq rfl] at hget
      obtain rfl : objCell tds base ty true false = mc := Option.some.inj hget
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => by simp at h,
        by simpa [atomicTyOpt] using hatom, fun h => by simp at h⟩
      · rw [hdead']
        exact hG.cur_dead hcurne _ (Int.le_refl _)
      · refine ⟨Allocation.mk base (sizeofCtype tds ty : Int) (some ty)
          .IsWritable .Unexposed pref, ?_, rfl, rfl, rfl, ⟨fun _ => rfl, fun _ => rfl⟩⟩
        rw [halloc', hallocs_get, if_pos rfl]
    · rw [Iris.Std.get?_insert_ne (fun h => hid h.symm)] at hget
      refine (hG.metas id mc hget).of_fields hdead' ?_ rfl
      rw [halloc', hallocs_get, if_neg (fun h => hid h.symm)]
  · -- metas_disj
    intro i j mci mcj hne hgi hgj
    by_cases hi : i = σ.nextAllocId
    · subst hi
      rw [Iris.Std.get?_insert_eq rfl] at hgi
      obtain rfl : objCell tds base ty true false = mci := Option.some.inj hgi
      rw [Iris.Std.get?_insert_ne hne] at hgj
      exact .inl (hmeta_hi j mcj hgj)
    · rw [Iris.Std.get?_insert_ne (fun h => hi h.symm)] at hgi
      by_cases hj : j = σ.nextAllocId
      · subst hj
        rw [Iris.Std.get?_insert_eq rfl] at hgj
        obtain rfl : objCell tds base ty true false = mcj := Option.some.inj hgj
        exact .inr (hmeta_hi i mci hgi)
      · rw [Iris.Std.get?_insert_ne (fun h => hj h.symm)] at hgj
        exact hG.metas_disj i j mci mcj hne hgi hgj
  · -- bytes
    intro k b hget
    rw [PMunion_get?, hrange_get] at hget
    by_cases hin : base ≤ k ∧ k < base + (sizeofCtype tds ty : Int)
    · rw [if_pos hin] at hget
      simp only [Option.orElse] at hget
      obtain rfl : undefByte = b := Option.some.inj hget
      rw [byteAt_writeBytesTo_in _ base (List.replicate (sizeofCtype tds ty) undefByte) k
        hin.1 (by rw [hreplen]; exact_mod_cast hin.2)]
      exact List.getElem_replicate _
    · rw [if_neg hin] at hget
      simp only [Option.orElse] at hget
      rw [byteAt_writeBytesTo_out _ base (List.replicate (sizeofCtype tds ty) undefByte) k
        (by rw [hreplen]; exact_mod_cast hin), hbytemid]
      exact hG.bytes k b hget
  · -- cursor_key
    intro k c hget
    by_cases hk : k = 0
    · exact hk
    · rw [Iris.Std.get?_insert_ne (fun h => hk h.symm)] at hget
      exact hG.cursor_key k c hget
  · -- cursor
    intro c hget
    rw [Iris.Std.get?_insert_eq rfl] at hget
    obtain rfl := Option.some.inj hget
    exact ⟨hlast'.symm, hnext'.symm⟩
  · -- wf: the global invariant survives the allocation step
    -- (`MemWF.alloc` at the fresh record, dynamic list unchanged) and
    -- the byte write
    intro _
    exact (MemWF.alloc (hG.wf hcurne)
      { base := base, size := (sizeofCtype tds ty : Int), ty := some ty,
        isReadonly := .IsWritable, prefix_ := pref } σ.dynamicAddrs
      (Int.natCast_nonneg _) hbase_le (fun _ ha => Or.inr ha)).writeBytesTo _ _
  · -- cur_byte_lo
    intro _ k b hget
    rw [hlast']
    rw [PMunion_get?, hrange_get] at hget
    by_cases hin : base ≤ k ∧ k < base + (sizeofCtype tds ty : Int)
    · exact hin.1
    · rw [if_neg hin] at hget
      simp only [Option.orElse] at hget
      exact Int.le_trans (Int.le_add_of_nonneg_right (Int.natCast_nonneg _))
        (hbyte_hi k b hget)
  · -- cur_meta_lo: the fresh cell IS the new cursor; every old cell
    -- ends at or below it
    intro _ id mc hget
    rw [hlast']
    by_cases hid : id = σ.nextAllocId
    · subst hid
      rw [Iris.Std.get?_insert_eq rfl] at hget
      obtain rfl : objCell tds base ty true false = mc := Option.some.inj hget
      exact Int.le_refl _
    · rw [Iris.Std.get?_insert_ne (fun h => hid h.symm)] at hget
      exact Int.le_trans (Int.le_add_of_nonneg_right (Int.natCast_nonneg _))
        (hmeta_hi id mc hget)

end CohGLemmas

end CerberusHeapLang
