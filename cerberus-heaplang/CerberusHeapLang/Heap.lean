/-
CerberusHeapLang.Heap — the points-to over the engine's memory
state, on iris-lean's GenHeap.

GRANULARITY (Phase 2 — the ownership split, the registered growth
step EXECUTED): the ghost carrier is the donor-shaped SPLIT (Caesium
heap/allocs; RefinedC theories/caesium/ghost_state.v is the
reference):
- a per-BYTE heap (absolute address ↦ AbsByte — the ghost fragment
  of the engine's own `bytemap`), so subrange ownership splits and
  joins at REAL ∗ (`bytesOwn`, `pointsToView`);
- a per-allocation METADATA heap (allocation id ↦ base/type — the
  provenance/metadata authority: loadM/storeM success is decided by
  the ALLOCATION table (liveness, bounds, writability, atomicity —
  CerbMem.lean:1586-1696), so byte content alone can never entail
  access success; the metadata cell carries exactly those facts and
  is the per-allocation exclusivity anchor);
- a one-cell ALLOCATOR-CURSOR heap (`AllocCursor` — the two MemState
  fields `allocateObject` reads/writes), the D26 resource: without
  it `create`'s reducibility is unprovable from footprints; with it
  the out-of-memory arm is a pure guard on owned state.
The whole-allocation `pointsToCell` is the MAXIMAL VIEW (offset 0,
view type = allocation type) plus the image's decode-inertness fact;
`SpikeCell`/`Coh`/`CellCoh` remain the PURE footprint vocabulary of
the exported engine-facing statements (`Sat`/`SemTriple`).

METADATA LIFETIME NOTE (named mover): kill/free is outside the
fragment, so metadata never dies and views may share it fractionally
without a liveness component. When kill joins the fragment, the
metadata heap gains the donor's alloc_alive/freeable split
(fractional liveness + the deallocation permission).

STATE INTERPRETATION (memory only — no driver state):
`stateInterp σ _ _ _ := ∃ mm mb mk, ⌜CohG σ mm mb mk⌝ ∗ interps`
over the real `CerbMem.MemState`. `CohG` couples: byte cells to the
bytemap readout; metadata cells to live/writable/typed/non-atomic
allocations, pairwise range-disjoint; a cursor cell (key 0) to
lastAddress/nextAllocId, its PRESENCE carrying the allocator-health
facts `wps_create` needs (fresh ids unallocated and not dead; all
ghost-tracked addresses at or above the downward-growing cursor) —
cursor-free launches owe nothing new. The union-member/
function-pointer side tables are SYMBOLIC (read-only context):
decode-inertness rides as a pure payload of `pointsToCell`
(`decIndep`; per-view decode premises on the generic rules), and
`StorableAt` carries the serialization-side analogues. For scalar
and integer-array images all of these are `rfl`.

Design records: docs/2026-08-30_spike-recon.md §5 (the original
allocation-rooted decision), docs/2026-09-01_phase2-notes.md (the
split).
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
def decodeCell (c : SpikeCell) : CerbMem.MemValue :=
  CerbMem.reconstructValue [] [] c.addr c.ty c.bytes

/-- Mirror of loadM's `isBool` (CerbMem.lean:1598). -/
def boolTy : ctype → Bool
  | Ctype _ (.Basic (.Integer .Bool0)) => true
  | _ => false

/-- Mirror of loadM's `isTrap` guard (CerbMem.lean:1598-1604): the
    _Bool trap-representation UB arm. wp_load's precondition excludes
    it (R4: UB-excluding — this is one of the NDkilled arms). -/
def cellLoadTrap (c : SpikeCell) : Bool :=
  boolTy c.ty &&
    (match decodeCell c with
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
structure StorableAt (ty : ctype) (mv : CerbMem.MemValue) : Prop where
  compat : CerbMem.ctypeMemCompatible ty (CerbMem.typeofMval mv) = true
  fpm : ∀ fpm, (CerbMem.memValueToBytes fpm mv).1 = fpm
  len : ∀ fpm, ((CerbMem.memValueToBytes fpm mv).2).length = CerbMem.sizeofCtype ty
  /-- serialization is table-independent (storeM serializes at the
      state's CURRENT funptrmap, CerbMem.lean:1632/639; scalar
      values produce the same bytes at any table). -/
  bytes_fpm : ∀ fpm, (CerbMem.memValueToBytes fpm mv).2 =
    (CerbMem.memValueToBytes [] mv).2
  /-- the stored image decodes table-independently (feeds the written
      cell's `CellCoh.dec_indep`). -/
  stored_dec : ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap)
    (addr : Int),
    CerbMem.reconstructValue lum fpm addr ty (CerbMem.memValueToBytes [] mv).2 =
      CerbMem.reconstructValue [] [] addr ty (CerbMem.memValueToBytes [] mv).2

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
structure CellCoh (σ : Mem) (id : Int) (c : SpikeCell) : Prop where
  dead : σ.deadAllocations.contains id = false
  alloc : ∃ al, σ.allocations.get? id = some al ∧ al.base = c.addr ∧
    al.size = (CerbMem.sizeofCtype c.ty : Int) ∧ al.ty = some c.ty ∧
    al.isReadonly = .IsWritable
  nonAtomic : atomicTy c.ty = false
  len : c.bytes.length = CerbMem.sizeofCtype c.ty
  bytes : CerbMem.readBytesFrom σ c.addr (CerbMem.sizeofCtype c.ty) = c.bytes
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
    CerbMem.reconstructValue lum fpm c.addr c.ty c.bytes = decodeCell c

def cellsDisjoint (c1 c2 : SpikeCell) : Prop :=
  c1.addr + (CerbMem.sizeofCtype c1.ty : Int) ≤ c2.addr ∨
  c2.addr + (CerbMem.sizeofCtype c2.ty : Int) ≤ c1.addr

open Iris.Std.PartialMap in
/-- The coupling invariant between the real MemState and the ghost
    cell map. -/
structure Coh (σ : Mem) (m : SpikeHeapF SpikeCell) : Prop where
  cells : ∀ id c, get? m id = some c → CellCoh σ id c
  disj : ∀ id1 id2 c1 c2, id1 ≠ id2 → get? m id1 = some c1 →
    get? m id2 = some c2 → cellsDisjoint c1 c2

/-! ## The memM computations under the invariant

These are the engine-unfolding facts wp_load/wp_store discharge into:
one-level applications of the real loadM/storeM (recon §5.4 seam (a)).
-/

/-- A non-atomic cell type makes the atomic-member arm
    (CerbMem.lean:1575-1585) unreachable. -/
theorem isAtomicMemberAccess_false (al : CerbMem.Allocation) (ty : ctype)
    (addr : Int) (hty : al.ty = some ty) (hatom : atomicTy ty = false) :
    CerbMem.isAtomicMemberAccess al ty addr = false := by
  unfold CerbMem.isAtomicMemberAccess
  rw [hty]
  cases ty with
  | Ctype q t => cases t <;> simp_all [atomicTy]

/-- Successful store: with a Coh-backed cell and a `StorableAt` value,
    `storeM` (CerbMem.lean:1632) takes exactly the active path and the
    state change is the byte write. Every guard the proof crosses is
    one NDkilled arm of the R4 vocabulary (recon §2.6), discharged by
    a named hypothesis. -/
theorem storeM_success (σ : Mem) (id : Int) (c : SpikeCell)
    (mv : CerbMem.MemValue) (loc : CerbLocation.Loc)
    (hcoh : CellCoh σ id c) (hst : StorableAt c.ty mv) :
    applyMemM (CerbMem.storeM loc c.ty false (cellPtr id c.addr) mv) σ =
      some (.FP .W c.addr (CerbMem.sizeofCtype c.ty),
        CerbMem.writeBytesTo σ c.addr (CerbMem.memValueToBytes [] mv).2) := by
  obtain ⟨al, hal, hbase, hsize, hty, hro⟩ := hcoh.alloc
  have hbounds : CerbMem.isInBounds al c.addr (CerbMem.sizeofCtype c.ty) = true := by
    simp [CerbMem.isInBounds, hbase, hsize]
  have hatomic := isAtomicMemberAccess_false al c.ty c.addr hty hcoh.nonAtomic
  rcases hmvb : CerbMem.memValueToBytes σ.funptrmap mv with ⟨fpm', bs'⟩
  have hfpm' : fpm' = σ.funptrmap := by
    have := hst.fpm σ.funptrmap
    rw [hmvb] at this
    exact this
  have hbs' : bs' = (CerbMem.memValueToBytes [] mv).2 := by
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
theorem loadM_success (σ : Mem) (id : Int) (c : SpikeCell)
    (loc : CerbLocation.Loc)
    (hcoh : CellCoh σ id c) (htrap : cellLoadTrap c = false) :
    applyMemM (CerbMem.loadM loc c.ty (cellPtr id c.addr)) σ =
      some ((.FP .R c.addr (CerbMem.sizeofCtype c.ty), decodeCell c), σ) := by
  obtain ⟨al, hal, hbase, hsize, hty, hro⟩ := hcoh.alloc
  have hbounds : CerbMem.isInBounds al c.addr (CerbMem.sizeofCtype c.ty) = true := by
    simp [CerbMem.isInBounds, hbase, hsize]
  have hatomic := isAtomicMemberAccess_false al c.ty c.addr hty hcoh.nonAtomic
  have hdec : CerbMem.reconstructValue σ.lastUsedUnionMembers σ.funptrmap c.addr
      c.ty (CerbMem.readBytesFrom σ c.addr (CerbMem.sizeofCtype c.ty)) =
      decodeCell c := by
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
  generalize decodeCell c = mval at htrap ⊢
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
theorem Coh.store (σ : Mem) (m : SpikeHeapF SpikeCell) (i : Int)
    (c : SpikeCell) (mv : CerbMem.MemValue)
    (hcoh : Coh σ m) (hget : Iris.Std.PartialMap.get? m i = some c)
    (hst : StorableAt c.ty mv) :
    Coh (CerbMem.writeBytesTo σ c.addr (CerbMem.memValueToBytes [] mv).2)
      (Iris.Std.PartialMap.insert m i
        ⟨c.addr, c.ty, (CerbMem.memValueToBytes [] mv).2⟩) := by
  generalize hbs : (CerbMem.memValueToBytes [] mv).2 = bs
  have hlen : bs.length = CerbMem.sizeofCtype c.ty := by
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
          (CerbMem.sizeofCtype c.ty) = bs
        rw [← hlen]
        exact readBytesFrom_writeBytesTo_self σ c.addr bs
      · intro lum fpm
        show CerbMem.reconstructValue lum fpm c.addr c.ty bs = _
        rw [← hbs]
        exact hst.stored_dec lum fpm c.addr
    · have hc := hcoh.cells j c' hold
      have hdisj := hcoh.disj _ _ c' c hne hold hget
      refine ⟨by simpa using hc.dead, ?_, hc.nonAtomic, hc.len, ?_, hc.dec_indep⟩
      · obtain ⟨al, hal, h1, h2, h3, h4⟩ := hc.alloc
        exact ⟨al, by simpa using hal, h1, h2, h3, h4⟩
      · show CerbMem.readBytesFrom (CerbMem.writeBytesTo σ c.addr bs) c'.addr
          (CerbMem.sizeofCtype c'.ty) = c'.bytes
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
theorem Coh.store_interior (σ : Mem) (m : SpikeHeapF SpikeCell) (i : Int)
    (c : SpikeCell) (off : Nat) (img : List AbsByte)
    (hcoh : Coh σ m) (hget : Iris.Std.PartialMap.get? m i = some c)
    (hbound : off + img.length ≤ sizeofCtype c.ty)
    (hdec_indep : ∀ (lum : List (Int × identifier)) (fpm : Funptrmap),
      reconstructValue lum fpm c.addr c.ty (spliceBytes off img c.bytes) =
        decodeCell ⟨c.addr, c.ty, spliceBytes off img c.bytes⟩) :
    Coh (writeBytesTo σ (c.addr + (off : Int)) img)
      (Iris.Std.PartialMap.insert m i
        ⟨c.addr, c.ty, spliceBytes off img c.bytes⟩) := by
  have hlenb : c.bytes.length = sizeofCtype c.ty := (hcoh.cells i c hget).len
  have hlen : (spliceBytes off img c.bytes).length = sizeofCtype c.ty := by
    rw [spliceBytes_length off img c.bytes (by omega)]
    exact hlenb
  have hreread : readBytesFrom
      (writeBytesTo σ (c.addr + (off : Int)) img) c.addr
      (sizeofCtype c.ty) = spliceBytes off img c.bytes :=
    readBytesFrom_write_interior σ c.addr off img (sizeofCtype c.ty)
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
          (sizeofCtype c'.ty) = c'.bytes
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

/-- Allocation metadata: everything an access needs to know about
    the backing allocation, minus the byte contents. -/
structure MetaCell where
  addr : Int
  ty : ctype

@[reducible] def metaOf (c : SpikeCell) : MetaCell := ⟨c.addr, c.ty⟩

/-- Per-allocation metadata facts in the real state: exactly
    `CellCoh` minus the byte-contents facts. -/
structure MetaCoh (σ : Mem) (id : Int) (mc : MetaCell) : Prop where
  dead : σ.deadAllocations.contains id = false
  alloc : ∃ al, σ.allocations.get? id = some al ∧ al.base = mc.addr ∧
    al.size = (sizeofCtype mc.ty : Int) ∧ al.ty = some mc.ty ∧
    al.isReadonly = .IsWritable
  nonAtomic : atomicTy mc.ty = false

theorem CellCoh.toMetaCoh {σ : Mem} {id : Int} {c : SpikeCell}
    (h : CellCoh σ id c) : MetaCoh σ id (metaOf c) :=
  ⟨h.dead, h.alloc, h.nonAtomic⟩

/-- CellCoh assembled from its split parts: metadata authority +
    length + byte-range readout + decode inertness. -/
theorem CellCoh.ofParts {σ : Mem} {id : Int} {c : SpikeCell}
    (hm : MetaCoh σ id (metaOf c))
    (hlen : c.bytes.length = sizeofCtype c.ty)
    (hread : readBytesFrom σ c.addr (sizeofCtype c.ty) = c.bytes)
    (hdec : ∀ (lum : List (Int × identifier)) (fpm : Funptrmap),
      reconstructValue lum fpm c.addr c.ty c.bytes = decodeCell c) :
    CellCoh σ id c :=
  ⟨hm.dead, hm.alloc, hm.nonAtomic, hlen, hread, hdec⟩

/-- Range-disjointness of allocation metadata (the same formula as
    `cellsDisjoint`). -/
def metaDisjoint (m1 m2 : MetaCell) : Prop :=
  m1.addr + (sizeofCtype m1.ty : Int) ≤ m2.addr ∨
  m2.addr + (sizeofCtype m2.ty : Int) ≤ m1.addr

theorem cellsDisjoint_iff_metaDisjoint (c1 c2 : SpikeCell) :
    cellsDisjoint c1 c2 ↔ metaDisjoint (metaOf c1) (metaOf c2) :=
  Iff.rfl

/-- A non-atomic ALLOCATION type makes the atomic-member arm
    unreachable at ANY accessed lvalue type (the check reads only the
    allocation's type shape). -/
theorem isAtomicMemberAccess_false' (al : Allocation) (aty lty : ctype)
    (addr : Int) (hty : al.ty = some aty) (hatom : atomicTy aty = false) :
    isAtomicMemberAccess al lty addr = false := by
  unfold isAtomicMemberAccess
  rw [hty]
  cases aty with
  | Ctype q t => cases t <;> simp_all [atomicTy]

/-- The _Bool trap-representation guard at a decoded value (mirror of
    loadM's `isTrap`, CerbMem.lean:1598-1604); `cellLoadTrap` is its
    whole-cell instance (`cellLoadTrap_eq`). -/
def loadTrapV (ty : ctype) (mv : MemValue) : Bool :=
  boolTy ty &&
    (match mv with
     | .MVinteger _ (.IV _ n) => n != 0 && n != 1
     | .MVunspecified _ => true
     | _ => false)

theorem cellLoadTrap_eq (c : SpikeCell) :
    cellLoadTrap c = loadTrapV c.ty (decodeCell c) := rfl

/-- GENERIC IN-BOUNDS TYPED LOAD (memM stratum): with allocation
    metadata backing, an in-bounds offset, the range's byte image,
    and a non-trap decode, `loadM` at the accessed type takes the
    active path, returns the decode of the range image, and leaves
    the state unchanged. Generalizes `loadM_success` (off 0, cell
    type) and the retired per-layout interior lemmas. -/
theorem loadM_at (σ : Mem) (id a : Int) (aty : ctype) (off : Nat)
    (vty : ctype) (bs : List AbsByte) (mv : MemValue)
    (loc : CerbLocation.Loc)
    (hmeta : MetaCoh σ id ⟨a, aty⟩)
    (hbound : off + sizeofCtype vty ≤ sizeofCtype aty)
    (hread : readBytesFrom σ (a + (off : Int)) (sizeofCtype vty) = bs)
    (hdec : reconstructValue σ.lastUsedUnionMembers σ.funptrmap
      (a + (off : Int)) vty bs = mv)
    (htrap : loadTrapV vty mv = false) :
    applyMemM (loadM loc vty (cellPtr id (a + (off : Int)))) σ =
      some ((.FP .R (a + (off : Int)) (sizeofCtype vty), mv), σ) := by
  obtain ⟨al, hal, hbase, hsize, hty, hro⟩ := hmeta.alloc
  have hbounds : isInBounds al (a + (off : Int)) (sizeofCtype vty) = true := by
    simp only [isInBounds, hbase, hsize]
    simp
    omega
  have hatomic := isAtomicMemberAccess_false' al aty vty (a + (off : Int))
    hty hmeta.nonAtomic
  unfold loadM applyMemM
  simp only [cellPtr, hmeta.dead, Bool.false_eq_true, if_false, hal, hbounds,
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

/-- GENERIC FULL-OWNERSHIP TYPED SUBRANGE STORE (memM stratum): with
    metadata backing and an in-bounds offset, `storeM` at the
    accessed type takes the active path and the state change is
    exactly the byte write of the serialized image at the interior
    address. Generalizes `storeM_success` and the retired per-layout
    interior lemmas; the serialization premises are the `StorableAt`
    facts at the accessed type. -/
theorem storeM_at (σ : Mem) (id a : Int) (aty : ctype) (off : Nat)
    (vty : ctype) (mv : MemValue) (loc : CerbLocation.Loc)
    (hmeta : MetaCoh σ id ⟨a, aty⟩)
    (hbound : off + sizeofCtype vty ≤ sizeofCtype aty)
    (hcompat : ctypeMemCompatible vty (typeofMval mv) = true)
    (hfpm : ∀ fpm, (memValueToBytes fpm mv).1 = fpm)
    (hbytes : ∀ fpm, (memValueToBytes fpm mv).2 =
      (memValueToBytes [] mv).2) :
    applyMemM (storeM loc vty false (cellPtr id (a + (off : Int))) mv) σ =
      some (.FP .W (a + (off : Int)) (sizeofCtype vty),
        writeBytesTo σ (a + (off : Int)) (memValueToBytes [] mv).2) := by
  obtain ⟨al, hal, hbase, hsize, hty, hro⟩ := hmeta.alloc
  have hbounds : isInBounds al (a + (off : Int)) (sizeofCtype vty) = true := by
    simp only [isInBounds, hbase, hsize]
    simp
    omega
  have hatomic := isAtomicMemberAccess_false' al aty vty (a + (off : Int))
    hty hmeta.nonAtomic
  rcases hmvb : memValueToBytes σ.funptrmap mv with ⟨fpm', bs'⟩
  have hfpm' : fpm' = σ.funptrmap := by
    have := hfpm σ.funptrmap
    rw [hmvb] at this
    exact this
  have hbs' : bs' = (memValueToBytes [] mv).2 := by
    have := hbytes σ.funptrmap
    rw [hmvb] at this
    exact this
  subst hfpm' hbs'
  unfold storeM applyMemM
  simp only [hcompat, Bool.not_true, Bool.false_eq_true, if_false, cellPtr,
    hal, hbounds, hro, hatomic, hmvb]

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
theorem freshBase_add_le (la : Int) (alignN : Int) (ty : ctype)
    (hsz : 0 < sizeofCtype ty)
    (hnz : freshBase la alignN (sizeofCtype ty) ≠ 0) :
    freshBase la alignN (sizeofCtype ty) + (sizeofCtype ty : Int) ≤ la := by
  have htoNat_pos : 0 < (la - (sizeofCtype ty : Int)).toNat := by
    rcases Nat.eq_zero_or_pos (la - (sizeofCtype ty : Int)).toNat
      with hz | hpos
    · exfalso
      apply hnz
      show (alignDown (la - (sizeofCtype ty : Int)).toNat
        (alignN.toNat.max 1) : Int) = 0
      rw [hz]
      simp [alignDown]
    · exact hpos
  have hle : alignDown (la - (sizeofCtype ty : Int)).toNat
      (alignN.toNat.max 1) ≤ (la - (sizeofCtype ty : Int)).toNat := by
    unfold alignDown
    exact Nat.div_mul_le_self _ _
  show (alignDown (la - (sizeofCtype ty : Int)).toNat
    (alignN.toNat.max 1) : Int) + (sizeofCtype ty : Int) ≤ la
  omega

/-- The fresh base is positive at a nonzero guard. -/
theorem freshBase_pos (la : Int) (alignN : Int) (ty : ctype)
    (hnz : freshBase la alignN (sizeofCtype ty) ≠ 0) :
    0 < freshBase la alignN (sizeofCtype ty) := by
  have h0 : 0 ≤ freshBase la alignN (sizeofCtype ty) :=
    Int.natCast_nonneg _
  omega

/-- allocateObject SUCCESS, symbolic state: at a nonzero fresh base
    the allocator takes the active path, mints exactly
    `cellPtr σ.nextAllocId base`, bumps the cursor, registers the
    allocation, and clears the range to unspecified bytes. The `0 <
    sizeof ty` premise pins the engine's `max 1` padding away (a real
    C object type; zero-size allocations stay outside the logic). -/
theorem allocateObject_success (σ : Mem) (pref : prefix0)
    (aprov : Provenance) (alignN : Int) (ty : ctype)
    (hsz : 0 < sizeofCtype ty)
    (hnz : freshBase σ.lastAddress alignN (sizeofCtype ty) ≠ 0) :
    applyMemM (allocateObject 0 pref (.IV aprov alignN) ty none none) σ =
      some (cellPtr σ.nextAllocId
          (freshBase σ.lastAddress alignN (sizeofCtype ty)),
        writeBytesTo
          { σ with
              nextAllocId := σ.nextAllocId + 1,
              lastAddress := freshBase σ.lastAddress alignN (sizeofCtype ty),
              allocations := σ.allocations.insert σ.nextAllocId
                { base := freshBase σ.lastAddress alignN (sizeofCtype ty),
                  size := (sizeofCtype ty : Int),
                  ty := some ty,
                  isReadonly := .IsWritable,
                  prefix_ := pref } }
          (freshBase σ.lastAddress alignN (sizeofCtype ty))
          (List.replicate (sizeofCtype ty) undefByte)) := by
  have hmax : (sizeofCtype ty).max 1 = sizeofCtype ty := Nat.max_eq_left hsz
  have hbeq : ((freshBase σ.lastAddress alignN (sizeofCtype ty) == 0) = false) :=
    int_beq_eq_false _ _ hnz
  unfold allocateObject applyMemM
  simp only [freshBase, hmax] at hbeq ⊢
  rw [hbeq]
  simp only [readonlyStatusForAlloc_none, Bool.false_eq_true, if_false]
  rfl

end Allocator

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
    MetaCoh (writeBytesTo σ a bs) id mc := by
  refine ⟨by simpa using h.dead, ?_, h.nonAtomic⟩
  obtain ⟨al, hal, h1, h2, h3, h4⟩ := h.alloc
  exact ⟨al, by simpa using hal, h1, h2, h3, h4⟩

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
    allocator fields, and its PRESENCE carries the allocator-health
    facts `wp_create` needs (fresh ids are unallocated and not dead;
    every ghost-tracked byte/metadata address sits at or above the
    downward-growing cursor). A cursor-free ghost state makes the
    `cur_*` facts vacuous: existing launches owe nothing new. -/
structure CohG (σ : Mem) (mm : SpikeHeapF MetaCell)
    (mb : SpikeHeapF CerbMem.AbsByte) (mk : SpikeHeapF AllocCursor) : Prop where
  metas : ∀ id mc, get? mm id = some mc → MetaCoh σ id mc
  metas_disj : ∀ i j mci mcj, i ≠ j → get? mm i = some mci →
    get? mm j = some mcj → metaDisjoint mci mcj
  bytes : ∀ k b, get? mb k = some b → byteAt σ k = b
  cursor_key : ∀ k c, get? mk k = some c → k = 0
  cursor : ∀ c, get? mk 0 = some c →
    c.lastAddr = σ.lastAddress ∧ c.nextId = σ.nextAllocId
  cur_dead : get? mk 0 ≠ none → ∀ id : Int, σ.nextAllocId ≤ id →
    σ.deadAllocations.contains id = false
  cur_alloc : get? mk 0 ≠ none → ∀ id : Int, σ.nextAllocId ≤ id →
    σ.allocations.get? id = none
  cur_meta_lt : get? mk 0 ≠ none → ∀ id mc, get? mm id = some mc →
    id < σ.nextAllocId
  cur_byte_lo : get? mk 0 ≠ none → ∀ k b, get? mb k = some b →
    σ.lastAddress ≤ k
  cur_meta_lo : get? mk 0 ≠ none → ∀ id mc, get? mm id = some mc →
    σ.lastAddress ≤ mc.addr

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
def decIndep (a : Int) (ty : ctype) (bs : List CerbMem.AbsByte) : Prop :=
  ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap),
    CerbMem.reconstructValue lum fpm a ty bs = decodeCell ⟨a, ty, bs⟩

/-- THE TYPED VIEW: ownership of one typed subrange of one
    allocation — metadata knowledge (id, base, allocation type) at
    fraction `dqm`, plus the range's bytes at fraction `dqb`, plus
    the in-bounds and footprint-length facts. -/
def pointsToView [SpikeGS hlc GF] (id a : Int) (aty : ctype) (off : Nat)
    (dqm dqb : DFrac) (vty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(metaOwn id dqm ⟨a, aty⟩ ∗
    ⌜off + CerbMem.sizeofCtype vty ≤ CerbMem.sizeofCtype aty ∧
      bs.length = CerbMem.sizeofCtype vty⌝ ∗
    bytesOwn (a + (off : Int)) dqb bs)

theorem pointsToView_iff {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (id a : Int) (aty : ctype) (off : Nat) (dqm dqb : DFrac) (vty : ctype)
    (bs : List CerbMem.AbsByte) :
    pointsToView (GF := GF) id a aty off dqm dqb vty bs ⊣⊢
      iprop(metaOwn id dqm ⟨a, aty⟩ ∗
        ⌜off + CerbMem.sizeofCtype vty ≤ CerbMem.sizeofCtype aty ∧
          bs.length = CerbMem.sizeofCtype vty⌝ ∗
        bytesOwn (a + (off : Int)) dqb bs) := .rfl

/-- Whole-allocation ownership at a ghost id: THE MAXIMAL VIEW
    (offset 0, view type = allocation type, both fractions equal)
    plus the image's decode inertness. This is what the old
    allocation-rooted ghost cell becomes. -/
def cellOwn [SpikeGS hlc GF] (i : Int) (dq : DFrac) (c : SpikeCell) : IProp GF :=
  iprop(metaOwn i dq (metaOf c) ∗ bytesOwn c.addr dq c.bytes ∗
    ⌜c.bytes.length = CerbMem.sizeofCtype c.ty ∧
      decIndep c.addr c.ty c.bytes⌝)

theorem cellOwn_iff {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (i : Int) (dq : DFrac) (c : SpikeCell) :
    cellOwn (GF := GF) i dq c ⊣⊢
      iprop(metaOwn i dq (metaOf c) ∗ bytesOwn c.addr dq c.bytes ∗
        ⌜c.bytes.length = CerbMem.sizeofCtype c.ty ∧
          decIndep c.addr c.ty c.bytes⌝) := .rfl

/-- The fragment points-to: the pointer is a real `PointerValue`
    carrying its provenance id (R5 — never an address-only
    abstraction), and the whole allocation is owned at fraction dq. -/
def pointsToCell [SpikeGS hlc GF] (pv : CerbMem.PointerValue) (dq : DFrac)
    (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id : Int) (a : Int),
    ⌜pv = cellPtr id a⌝ ∗ cellOwn id dq (SpikeCell.mk a ty bs))

theorem pointsToCell_cellOwn_iff {hlc : HasLC} {GF : BundledGFunctors}
    [SpikeGS hlc GF] (pv : CerbMem.PointerValue) (dq : DFrac) (ty : ctype)
    (bs : List CerbMem.AbsByte) :
    pointsToCell (GF := GF) pv dq ty bs ⊣⊢
      iprop(∃ (id : Int) (a : Int),
        ⌜pv = cellPtr id a⌝ ∗ cellOwn id dq (SpikeCell.mk a ty bs)) := .rfl

notation:50 pv " ↦c{" dq "} " ty " ; " bs:50 => pointsToCell pv dq ty bs
notation:50 pv " ↦c " ty " ; " bs:50 => pointsToCell pv (DFrac.own 1) ty bs

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
theorem pointsToView_split (id a : Int) (aty : ctype) (off : Nat)
    (q₁ q₂ : Qp) (dqb : DFrac) (vty vty₁ vty₂ : ctype)
    (bs₁ bs₂ : List CerbMem.AbsByte)
    (hsz : CerbMem.sizeofCtype vty =
      CerbMem.sizeofCtype vty₁ + CerbMem.sizeofCtype vty₂)
    (hlen₁ : bs₁.length = CerbMem.sizeofCtype vty₁) :
    pointsToView (GF := GF) id a aty off (.own (q₁ + q₂)) dqb vty (bs₁ ++ bs₂) ⊢
      iprop(pointsToView id a aty off (.own q₁) dqb vty₁ bs₁ ∗
        pointsToView id a aty (off + CerbMem.sizeofCtype vty₁) (.own q₂) dqb
          vty₂ bs₂) := by
  unfold pointsToView
  iintro ⟨Hm, %hpure, Hb⟩
  obtain ⟨hbound, hlen⟩ := hpure
  have hlapp : (bs₁ ++ bs₂).length = bs₁.length + bs₂.length :=
    List.length_append
  have hlen₂ : bs₂.length = CerbMem.sizeofCtype vty₂ := by omega
  icases (metaOwn_fractional id ⟨a, aty⟩ q₁ q₂).1 $$ Hm with ⟨Hm₁, Hm₂⟩
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
    · rw [show a + ((off + CerbMem.sizeofCtype vty₁ : Nat) : Int) =
        a + (off : Int) + ((bs₁.length : Nat) : Int) by omega]
      iexact Hb₂

/-- SUBRANGE JOIN: the converse — two adjacent typed subviews of the
    same allocation join into the containing view (fractions add,
    byte ranges concatenate). -/
theorem pointsToView_join (id a : Int) (aty : ctype) (off : Nat)
    (q₁ q₂ : Qp) (dqb : DFrac) (vty vty₁ vty₂ : ctype)
    (bs₁ bs₂ : List CerbMem.AbsByte)
    (hsz : CerbMem.sizeofCtype vty =
      CerbMem.sizeofCtype vty₁ + CerbMem.sizeofCtype vty₂)
    (hbound : off + CerbMem.sizeofCtype vty ≤ CerbMem.sizeofCtype aty) :
    iprop(pointsToView (GF := GF) id a aty off (.own q₁) dqb vty₁ bs₁ ∗
      pointsToView id a aty (off + CerbMem.sizeofCtype vty₁) (.own q₂) dqb
        vty₂ bs₂) ⊢
      pointsToView id a aty off (.own (q₁ + q₂)) dqb vty (bs₁ ++ bs₂) := by
  unfold pointsToView
  iintro ⟨⟨Hm₁, %hp₁, Hb₁⟩, Hm₂, %hp₂, Hb₂⟩
  obtain ⟨hbound₁, hlen₁⟩ := hp₁
  obtain ⟨hbound₂, hlen₂⟩ := hp₂
  isplitl [Hm₁ Hm₂]
  · iapply (metaOwn_fractional id ⟨a, aty⟩ q₁ q₂).2
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
        a + ((off + CerbMem.sizeofCtype vty₁ : Nat) : Int) by omega]
      iexact Hb₂

/-- The whole-cell ownership IS the maximal view (plus the image's
    decode-inertness fact) — both directions. -/
theorem cellOwn_view (i : Int) (dq : DFrac) (c : SpikeCell) :
    cellOwn (GF := GF) i dq c ⊣⊢
      iprop(pointsToView i c.addr c.ty 0 dq dq c.ty c.bytes ∗
        ⌜decIndep c.addr c.ty c.bytes⌝) := by
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
    {mb : SpikeHeapF CerbMem.AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) (i : Int) (dq : DFrac) (c : SpikeCell) :
    iprop(metaInterp (GF := GF) mm ∗ byteInterp mb ∗ cellOwn i dq c) ⊢
      (⌜CellCoh σ i c ∧
        Iris.Std.PartialMap.get? mm i = some (metaOf c)⌝ : IProp GF) := by
  iintro ⟨Hmi, Hbi, Hcell⟩
  icases (cellOwn_iff i dq c).mp $$ Hcell with ⟨Hm, Hb, %Hpure⟩
  obtain ⟨hlen, hdec⟩ := Hpure
  ihave %Hgetm : ⌜Iris.Std.PartialMap.get? mm i = some (metaOf c)⌝ $$ [Hmi Hm]
  · ihave >%h := metaHeap_valid $$ [$Hmi $Hm]
    itrivial
  ihave %Hread : ⌜CerbMem.readBytesFrom σ c.addr c.bytes.length = c.bytes⌝
      $$ [Hbi Hb]
  · iapply bytesOwn_read hG c.addr dq c.bytes $$ [$Hbi $Hb]
  ipureintro
  exact ⟨CellCoh.ofParts (hG.metas i _ Hgetm) hlen (hlen ▸ Hread) hdec, Hgetm⟩

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
  refine ⟨?_, hG.metas_disj, ?_, hG.cursor_key, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro hne id hle
    rw [hnext] at hle
    simpa using hG.cur_dead hne id hle
  · intro hne id hle
    rw [hnext] at hle
    simpa using hG.cur_alloc hne id hle
  · intro hne id mc hget
    rw [hnext]
    exact hG.cur_meta_lt hne id mc hget
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
    {mb : SpikeHeapF AbsByte} {mk : SpikeHeapF AllocCursor}
    (hG : CohG σ mm mb mk) (pref : prefix0) (alignN : Int) (ty : ctype)
    (hsz : 0 < sizeofCtype ty) (hatom : atomicTy ty = false)
    (hcur : get? mk 0 = some ⟨σ.lastAddress, σ.nextAllocId⟩)
    (hnz : freshBase σ.lastAddress alignN (sizeofCtype ty) ≠ 0) :
    CohG
      (writeBytesTo
        { σ with
            nextAllocId := σ.nextAllocId + 1,
            lastAddress := freshBase σ.lastAddress alignN (sizeofCtype ty),
            allocations := σ.allocations.insert σ.nextAllocId
              { base := freshBase σ.lastAddress alignN (sizeofCtype ty),
                size := (sizeofCtype ty : Int),
                ty := some ty,
                isReadonly := .IsWritable,
                prefix_ := pref } }
        (freshBase σ.lastAddress alignN (sizeofCtype ty))
        (List.replicate (sizeofCtype ty) undefByte))
      (Iris.Std.PartialMap.insert mm σ.nextAllocId
        ⟨freshBase σ.lastAddress alignN (sizeofCtype ty), ty⟩)
      (Iris.Std.PartialMap.union
        (rangeMap (freshBase σ.lastAddress alignN (sizeofCtype ty))
          (List.replicate (sizeofCtype ty) undefByte)) mb)
      (Iris.Std.PartialMap.insert mk 0
        ⟨freshBase σ.lastAddress alignN (sizeofCtype ty),
          σ.nextAllocId + 1⟩) := by
  have hcurne : get? mk 0 ≠ none := by
    rw [hcur]
    simp
  -- abbreviations (plain lets; the goal's occurrences are definitional)
  generalize hbase_def : freshBase σ.lastAddress alignN (sizeofCtype ty) = base
    at hnz ⊢
  -- the fresh base sits strictly below the old cursor with the whole
  -- range: 0 < base, base + sizeof ty ≤ lastAddress
  have hbase_nonneg : 0 ≤ base := by
    rw [← hbase_def]
    exact Int.natCast_nonneg _
  have hbase_pos : 0 < base := by omega
  have htoNat_pos : 0 < (σ.lastAddress - (sizeofCtype ty : Int)).toNat := by
    rcases Nat.eq_zero_or_pos (σ.lastAddress - (sizeofCtype ty : Int)).toNat
      with hz | hpos
    · exfalso
      apply hnz
      rw [← hbase_def]
      show (alignDown (σ.lastAddress - (sizeofCtype ty : Int)).toNat
        (alignN.toNat.max 1) : Int) = 0
      rw [hz]
      simp [alignDown]
    · exact hpos
  have hbase_le : base + (sizeofCtype ty : Int) ≤ σ.lastAddress := by
    have hle : alignDown (σ.lastAddress - (sizeofCtype ty : Int)).toNat
        (alignN.toNat.max 1) ≤
        (σ.lastAddress - (sizeofCtype ty : Int)).toNat := by
      unfold alignDown
      exact Nat.div_mul_le_self _ _
    rw [← hbase_def]
    show (alignDown (σ.lastAddress - (sizeofCtype ty : Int)).toNat
      (alignN.toNat.max 1) : Int) + (sizeofCtype ty : Int) ≤ σ.lastAddress
    omega
  have hreplen : (List.replicate (sizeofCtype ty) undefByte).length =
    sizeofCtype ty := by simp
  -- the fresh range is disjoint from every tracked byte (old bytes sit
  -- at or above the OLD cursor; the fresh range ends at or below it)
  have hbyte_hi : ∀ k b, get? mb k = some b →
      base + (sizeofCtype ty : Int) ≤ k := by
    intro k b hget
    exact Int.le_trans hbase_le (hG.cur_byte_lo hcurne k b hget)
  have hmeta_hi : ∀ id mc, get? mm id = some mc →
      base + (sizeofCtype ty : Int) ≤ mc.addr := by
    intro id mc hget
    exact Int.le_trans hbase_le (hG.cur_meta_lo hcurne id mc hget)
  have hmeta_lt : ∀ id mc, get? mm id = some mc → id < σ.nextAllocId :=
    hG.cur_meta_lt hcurne
  -- the fresh range map's readout
  have hrange_get : ∀ k,
      get? (rangeMap base (List.replicate (sizeofCtype ty) undefByte)) k =
      if base ≤ k ∧ k < base + (sizeofCtype ty : Int) then some undefByte
      else none := by
    intro k
    rw [rangeMap_get?, hreplen]
    by_cases h : base ≤ k ∧ k < base + (sizeofCtype ty : Int)
    · rw [if_pos h, if_pos h,
        List.getElem?_eq_getElem
          (by rw [hreplen]; omega :
            (k - base).toNat < (List.replicate (sizeofCtype ty) undefByte).length),
        List.getElem_replicate]
    · rw [if_neg h, if_neg h]
  -- state-side readouts of the post-allocation state
  have hdead' : (writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } }
      base (List.replicate (sizeofCtype ty) undefByte)).deadAllocations =
      σ.deadAllocations := rfl
  have hnext' : (writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } }
      base (List.replicate (sizeofCtype ty) undefByte)).nextAllocId =
      σ.nextAllocId + 1 := rfl
  have hlast' : (writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } }
      base (List.replicate (sizeofCtype ty) undefByte)).lastAddress =
      base := rfl
  have halloc' : (writeBytesTo
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } }
      base (List.replicate (sizeofCtype ty) undefByte)).allocations =
      σ.allocations.insert σ.nextAllocId
        { base := base, size := (sizeofCtype ty : Int), ty := some ty,
          isReadonly := .IsWritable, prefix_ := pref } := rfl
  have hbytemid : ∀ k, byteAt
      { σ with
          nextAllocId := σ.nextAllocId + 1,
          lastAddress := base,
          allocations := σ.allocations.insert σ.nextAllocId
            { base := base, size := (sizeofCtype ty : Int), ty := some ty,
              isReadonly := .IsWritable, prefix_ := pref } } k =
      byteAt σ k := fun _ => rfl
  have hallocs_get : ∀ (id : Int),
      (σ.allocations.insert σ.nextAllocId
        ({ base := base, size := (sizeofCtype ty : Int), ty := some ty,
           isReadonly := .IsWritable, prefix_ := pref } : Allocation)).get? id =
      if σ.nextAllocId = id then
        some ({ base := base, size := (sizeofCtype ty : Int), ty := some ty,
                isReadonly := .IsWritable, prefix_ := pref } : Allocation)
      else σ.allocations.get? id := by
    intro id
    simp [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- metas
    intro id mc hget
    by_cases hid : id = σ.nextAllocId
    · subst hid
      rw [Iris.Std.get?_insert_eq rfl] at hget
      obtain rfl : (⟨base, ty⟩ : MetaCell) = mc := Option.some.inj hget
      refine ⟨?_, ?_, hatom⟩
      · rw [hdead']
        exact hG.cur_dead hcurne _ (Int.le_refl _)
      · refine ⟨Allocation.mk base (sizeofCtype ty : Int) (some ty)
          .IsWritable .Unexposed pref, ?_, rfl, rfl, rfl, rfl⟩
        rw [halloc', hallocs_get, if_pos rfl]
    · rw [Iris.Std.get?_insert_ne (fun h => hid h.symm)] at hget
      have hold := hG.metas id mc hget
      refine ⟨?_, ?_, hold.nonAtomic⟩
      · rw [hdead']
        exact hold.dead
      · obtain ⟨al, hal, h1, h2, h3, h4⟩ := hold.alloc
        refine ⟨al, ?_, h1, h2, h3, h4⟩
        rw [halloc', hallocs_get, if_neg (fun h => hid h.symm)]
        exact hal
  · -- metas_disj
    intro i j mci mcj hne hgi hgj
    by_cases hi : i = σ.nextAllocId
    · subst hi
      rw [Iris.Std.get?_insert_eq rfl] at hgi
      obtain rfl : (⟨base, ty⟩ : MetaCell) = mci := Option.some.inj hgi
      rw [Iris.Std.get?_insert_ne hne] at hgj
      exact .inl (hmeta_hi j mcj hgj)
    · rw [Iris.Std.get?_insert_ne (fun h => hi h.symm)] at hgi
      by_cases hj : j = σ.nextAllocId
      · subst hj
        rw [Iris.Std.get?_insert_eq rfl] at hgj
        obtain rfl : (⟨base, ty⟩ : MetaCell) = mcj := Option.some.inj hgj
        exact .inr (hmeta_hi i mci hgi)
      · rw [Iris.Std.get?_insert_ne (fun h => hj h.symm)] at hgj
        exact hG.metas_disj i j mci mcj hne hgi hgj
  · -- bytes
    intro k b hget
    rw [PMunion_get?, hrange_get] at hget
    by_cases hin : base ≤ k ∧ k < base + (sizeofCtype ty : Int)
    · rw [if_pos hin] at hget
      simp only [Option.orElse] at hget
      obtain rfl : undefByte = b := Option.some.inj hget
      rw [byteAt_writeBytesTo_in _ base (List.replicate (sizeofCtype ty) undefByte) k
        hin.1 (by rw [hreplen]; exact_mod_cast hin.2)]
      exact List.getElem_replicate _
    · rw [if_neg hin] at hget
      simp only [Option.orElse] at hget
      rw [byteAt_writeBytesTo_out _ base (List.replicate (sizeofCtype ty) undefByte) k
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
  · -- cur_dead
    intro _ id hle
    rw [hnext'] at hle
    rw [hdead']
    -- NOTE: omega inexplicably fails on several trivially-true Int
    -- goals in this proof context (recorded in the phase notes);
    -- the explicit Int-order lemmas are used instead.
    exact hG.cur_dead hcurne id
      (Int.le_of_lt (Int.lt_of_lt_of_le (Int.lt_succ _) hle))
  · -- cur_alloc
    intro _ id hle
    rw [hnext'] at hle
    have hlt : σ.nextAllocId < id :=
      Int.lt_of_lt_of_le (Int.lt_succ _) hle
    rw [halloc', hallocs_get, if_neg (Int.ne_of_lt hlt)]
    exact hG.cur_alloc hcurne id (Int.le_of_lt hlt)
  · -- cur_meta_lt
    intro _ id mc hget
    rw [hnext']
    by_cases hid : id = σ.nextAllocId
    · subst hid
      exact Int.lt_succ _
    · rw [Iris.Std.get?_insert_ne (fun h => hid h.symm)] at hget
      exact Int.lt_trans (hmeta_lt id mc hget) (Int.lt_succ _)
  · -- cur_byte_lo
    intro _ k b hget
    rw [hlast']
    rw [PMunion_get?, hrange_get] at hget
    by_cases hin : base ≤ k ∧ k < base + (sizeofCtype ty : Int)
    · exact hin.1
    · rw [if_neg hin] at hget
      simp only [Option.orElse] at hget
      exact Int.le_trans (Int.le_add_of_nonneg_right (Int.natCast_nonneg _))
        (hbyte_hi k b hget)
  · -- cur_meta_lo
    intro _ id mc hget
    rw [hlast']
    by_cases hid : id = σ.nextAllocId
    · subst hid
      rw [Iris.Std.get?_insert_eq rfl] at hget
      obtain rfl : (⟨base, ty⟩ : MetaCell) = mc := Option.some.inj hget
      exact Int.le_refl _
    · rw [Iris.Std.get?_insert_ne (fun h => hid h.symm)] at hget
      exact Int.le_trans (Int.le_add_of_nonneg_right (Int.natCast_nonneg _))
        (hmeta_hi id mc hget)

end CohGLemmas

end CerberusHeapLang
