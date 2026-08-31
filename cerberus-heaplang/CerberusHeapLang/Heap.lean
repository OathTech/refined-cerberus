/-
CerberusHeapLang.Heap — spike artifact 2: the points-to over the
engine's memory state, on iris-lean's GenHeap.

GRANULARITY DECISION (recon §5.2, recorded reasoning): the ghost
carrier is ALLOCATION-ROOTED — one ghost cell per allocation id,
holding (base address, C type, byte list). Why:
- loadM/storeM success is decided by the ALLOCATION table (liveness,
  bounds, writability, atomicity — CerbMem.lean:1586-1696), so a
  byte-only points-to cannot entail access success (the allocation
  facts would need a second ghost heap anyway);
- the value payload is the BYTE list (mirror-true to `bytemap`),
  which is exactly the donor's Caesium `l ↦ v : list mbyte` shape;
  value-level claims are stated OVER the bytes by encoding
  predicates (recon §2.8) — the ty_deref/ty_ref factorization (R2)
  grows on this without change;
- per-byte splitting of one allocation (struct fields) is the
  registered growth step: split into a per-byte heap + a
  per-allocation metadata heap. CHANGED-SHAPE, not blocking.

STATE INTERPRETATION (memory only — no driver state; recon §5.1):
`stateInterp σ _ _ _ := ∃ m, ⌜Coh σ m⌝ ∗ genHeapInterp m` over the
real `CerbMem.MemState`. `Coh` is the coupling invariant: every ghost
cell is backed by a live, writable, in-bounds, non-atomic allocation
whose bytemap slice IS the cell's byte list; cells are pairwise
disjoint. The union-member/function-pointer side tables are SYMBOLIC
(read-only context, arbitrary and returned verbatim): each cell
carries an INERTNESS premise (`CellCoh.dec_indep`) saying its decode
ignores both tables — exactly what loadM's reconstruction reads them
for — and `StorableAt` carries the serialization-side analogues.
For scalar cells all of these are `rfl`. ([USER 2026-08-30]: the
de-pin; the full-build shape is ghost ownership of the tables.)
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
  have hself : ({ σ with funptrmap := σ.funptrmap } : Mem) = σ := rfl
  unfold CerbMem.storeM applyMemM
  simp only [hst.compat, Bool.not_true, Bool.false_eq_true, if_false, cellPtr,
    hal, hbounds, hro, hatomic, hmvb, hself]

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

/-! ## Ghost state -/

/-- Ghost-state prerequisites: invariants + one GenHeap of spike
    cells (mirror of HeapLangGpreS, PrimitiveLaws.lean:28-33, minus
    prophecies). -/
class SpikeGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  heap_pre : genHeapPreS Int SpikeCell GF SpikeHeapF

attribute [reducible, instance] SpikeGpreS.heap_pre

/-- The bundled ghost names (mirror of HeapLangGS,
    PrimitiveLaws.lean:59-67). -/
class SpikeGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [invGS : InvGS_gen hlc GF]
  heap : genHeapGS Int SpikeCell GF SpikeHeapF

attribute [reducible, instance] SpikeGS.heap

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The state interpretation: memory only (no driver state), coupled
    to the ghost cell map by Coh. -/
instance SpikeState [SpikeGS hlc GF] : StateInterp Mem Empty GF where
  stateInterp σ _ _ _ := iprop(∃ m, ⌜Coh σ m⌝ ∗ genHeapInterp m)

theorem stateInterp_eq [SpikeGS hlc GF] (σ : Mem) (ns : Nat)
    (κs : List Empty) (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt =
      iprop(∃ m, ⌜Coh σ m⌝ ∗ genHeapInterp m) := rfl

/-- The fragment points-to: the pointer is a real `PointerValue`
    carrying its provenance id (R5 — never an address-only
    abstraction), and the cell is owned at fraction dq. -/
def pointsToCell [SpikeGS hlc GF] (pv : CerbMem.PointerValue) (dq : DFrac)
    (ty : ctype) (bs : List CerbMem.AbsByte) : IProp GF :=
  iprop(∃ (id : Int) (a : Int),
    ⌜pv = cellPtr id a⌝ ∗ pointsTo id dq (SpikeCell.mk a ty bs))

notation:50 pv " ↦c{" dq "} " ty " ; " bs:50 => pointsToCell pv dq ty bs
notation:50 pv " ↦c " ty " ; " bs:50 => pointsToCell pv (DFrac.own 1) ty bs

end CerberusHeapLang
