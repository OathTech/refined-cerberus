/-
CerberusHeapLang.TreeRotExhibit — THE SECOND CLIENT (foundations
Phase 4, audit F-06 item 6): a STRUCTURALLY DIFFERENT linked
structure — binary tree nodes — with an in-place ROTATION certified
through the generic layer. The audit's accident-detector: "test that
list accidents have not become logic laws".

THE NODE (the [USER 2026-08-31] one-allocation ruling, extended):
ONE allocation per tree node, THREE long-width fields — the value at
offset 0, the LEFT child pointer at offset 8, the RIGHT child
pointer at offset 16. Allocation type `long[3]` (`treeTy`, 24
bytes); intra-node field access is in-allocation arithmetic
(`array_shift(p, long, 1)` / `array_shift(p, long, 2)`), children
are LOADED pointers with their own provenance — exactly the list
exhibit's discipline at a different layout and a BRANCHING
recursion (two sub-structures per node, not one).

THE PROGRAM (authored Core, straight-line — the classic right
rotation at the root; x is bound once so every operand is a symbol):

    lets x = pure(px) in
    lets Specified(y) = load(tree*, array_shift(x, long, 1)) in
    lets Specified(b) = load(tree*, array_shift(y, long, 2)) in
    lets _ = store(tree*, array_shift(x, long, 1), b) in
    lets _ = store(tree*, array_shift(y, long, 2), x) in
    pure(y)

rotating   node x vx (node y vy a b) c   into
           node y vy a (node x vx b c)   — two next-field writes,
zero allocation, every node keeping its own value.

ZERO CORE-LOGIC EDITS (fresh-client discipline, audit acceptance
test 2 replayed at Phase 4): no WP/WPS/WPT lifting rule, no state-
interpretation opening (readouts go through the core
`cells_readout`), no new memM seam. Every memory rule used is a
one-line client instance of the generic typed-subrange rules
(`wps_load_cell_at`/`wps_store_cell_at` + total forms); the
byte-level pointer-image algebra is REUSED from the list exhibit
(the images are layout-independent); the splice algebra is the core
`spliceBytes_slice_below/self/above` at this layout's offsets —
including the ABOVE case the two-field list node never exercised.

THE EXPORTS (the flagship shape, mirrored): `tree_rotate_certified`
(partial) and `tree_rotate_certified_total` (unconditional `.done`
at the derived straight-line budget 19) state: from a seeded tree
footprint `m₀` next to an ARBITRARY disjoint frame `R`, the engine
delivers the left child's pointer heading a final footprint `Q` with
`SeedTree Q py (rotated tree)` — the SAME allocations (the literal
footprint-equality conjunct; the rotated tree's id list is a
permutation of the original's), each node its own value — with `R`
returned VERBATIM. SpikeGF-concrete: no ghost-functor binder.
-/
import CerberusHeapLang.ListRevExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## The tree-node layout (LP64, the engine's own sizes) -/

/-- The tree-node type: ONE allocation, three long-width fields
    (`long[3]`) — value at 0, left at 8, right at 16. -/
def treeTy : ctype := Ctype [] (.Array0 longTy (some 3))

/-- Pointer-to-tree-node — the type every child load/store uses. -/
def treePtrTy : ctype := Ctype [] (.Pointer no_qualifiers treeTy)

/-- THE NULL at the tree-node type (the engine's own null,
    CerbMem.lean:843). -/
def nullTree : CerbMem.PointerValue := CerbMem.nullPtrval treeTy

theorem treeTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds treeTy = 24 := rfl
theorem treePtrTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds treePtrTy = 8 := rfl

theorem treeTy_nonatomic : atomicTy treeTy = false := rfl

/-- The `long[3]` decode is an array of integer decodes — table-
    independent (the same inertness argument as the list node's). -/
theorem treeTy_dec_indep {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (addr : Int) (bs : List CerbMem.AbsByte) :
    CerbMem.reconstructValue tds lum fpm addr treeTy bs =
      CerbMem.reconstructValue tds [] [] addr treeTy bs := rfl

/-- Two long-element shifts of a fragment pointer (the engine's own
    arithmetic — the right-child field). -/
theorem arrayShift_cellPtr_long_two {tds : CerbTags.TagDefsMap} (id p : Int) :
    CerbMem.arrayShiftPtrval tds (cellPtr id p) longTy (CerbMem.integerIval 2) =
      cellPtr id (p + 16) := by
  rw [cellPtr_arrayShift tds id p longTy 2 (fun _ h => by unfold longTy at h; cases h),
    longTy_size]
  exact congrArg (cellPtr id) (by omega)

theorem evalArrayShift_long_two (id a : Int) :
    evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id a))) (ivVal 2) =
      some (Vobject (OVpointer (cellPtr id (a + 16)))) := by
  show some (Vobject (OVpointer (CerbMem.arrayShiftPtrval fmapEmpty (cellPtr id a)
    longTy (CerbMem.integerIval 2)))) = _
  rw [arrayShift_cellPtr_long_two]

/-! ## Stored child-pointer images and their round trips at the
tree-pointer view type (the byte-level image algebra is REUSED from
the list exhibit — pointer serialization is layout-independent) -/

/-- The serialized image of a stored tree-node pointer. -/
def trPtrImg (pv : CerbMem.PointerValue) : List CerbMem.AbsByte :=
  imgOf fmapEmpty (CerbMem.pointerMval treeTy pv)

theorem trPtrImg_cell (id a : Int) :
    trPtrImg (cellPtr id a) = ptrImg (cellPtr id a) := rfl

theorem trPtrImg_null : trPtrImg nullTree = ptrImg nullNode := rfl

theorem trPtrImg_cell_length (id a : Int) :
    (trPtrImg (cellPtr id a)).length = 8 := by
  rw [trPtrImg_cell]
  exact ptrImg_cell_length id a

theorem trPtrImg_null_length : (trPtrImg nullTree).length = 8 := rfl

/-- THE NULL ROUND TRIP at `tree*` (table- and address-independent —
    the list exhibit's `reconstruct_ptrImg_null` at this pointee). -/
theorem reconstruct_trImg_null {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (addr : Int) :
    CerbMem.reconstructValue tds lum fpm addr treePtrTy (trPtrImg nullTree) =
      .MVpointer treeTy nullTree := rfl

/-- THE CONCRETE-POINTER ROUND TRIP at `tree*` (transliteration of
    the list exhibit's `reconstruct_ptrImg_cell`; the byte-level
    facts `bytesToInt_ptrImg_cell` / `splitBytesProv_ptrImg_cell_fst`
    are reused as-is). -/
theorem reconstruct_trImg_cell {tds : CerbTags.TagDefsMap} (id a : Int) (h0 : 0 < a) (h1 : a < 2 ^ 64)
    (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (addr : Int) :
    CerbMem.reconstructValue tds lum fpm addr treePtrTy (trPtrImg (cellPtr id a)) =
      .MVpointer treeTy (cellPtr id a) := by
  have hb := bytesToInt_ptrImg_cell id a (by omega) h1
  have hsp := splitBytesProv_ptrImg_cell_fst id a (by omega)
  rw [trPtrImg_cell]
  rw [show CerbMem.reconstructValue =
    CerbMem.reconstructValue_lemFuel lemDefaultFuel from rfl,
    show lemDefaultFuel = 999999 + 1 from rfl]
  unfold CerbMem.reconstructValue_lemFuel treePtrTy treeTy
  dsimp only
  rw [hb]
  rcases hpair : CerbMem.splitBytesProv (ptrImg (cellPtr id a)) with ⟨pv, vd⟩
  have hpv : pv = .Prov_some id := by
    rw [← hsp, hpair]
  subst hpv
  split
  · rename_i heq
    exact absurd (Option.some.inj heq) (by omega)
  · rename_i x1 ptrAddr hne heq
    obtain rfl : a = ptrAddr := Option.some.inj heq
    dsimp only
    rw [show ((a.toNat : Int)) = a by omega]
    rfl
  · rename_i heq
    exact absurd heq (by simp)

/-! ## Field decode predicates (the value field REUSES the list
exhibit's `nodeValDec` — "first 8 bytes decode as this long" is
layout-independent; the child fields decode at `tree*`) -/

/-- An 8-byte slice at offset `off` decodes — by the ENGINE's
    decoder — as the child pointer `q` at the tree-pointer type. -/
def treePtrDec (tds : CerbTags.TagDefsMap) (bs : List CerbMem.AbsByte) (off : Nat)
    (q : CerbMem.PointerValue) : Prop :=
  ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (ad : Int),
    CerbMem.reconstructValue tds lum fpm ad treePtrTy ((bs.drop off).take 8) =
      .MVpointer treeTy q

theorem treePtrDec_img_cell (id a : Int) (h0 : 0 < a) (h1 : a < 2 ^ 64)
    (bs : List CerbMem.AbsByte) (off : Nat)
    (himg : (bs.drop off).take 8 = trPtrImg (cellPtr id a)) :
    treePtrDec fmapEmpty bs off (cellPtr id a) := by
  intro lum fpm ad
  rw [himg]
  exact reconstruct_trImg_cell id a h0 h1 lum fpm ad

theorem treePtrDec_img_null (bs : List CerbMem.AbsByte) (off : Nat)
    (himg : (bs.drop off).take 8 = trPtrImg nullTree) :
    treePtrDec fmapEmpty bs off nullTree := by
  intro lum fpm ad
  rw [himg]
  exact reconstruct_trImg_null lum fpm ad

/-! ## Storable facts for stored child pointers -/

theorem tree_ptr_encodes (pv : CerbMem.PointerValue) :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ treePtrTy)) (ptrVal pv) =
      some (CerbMem.pointerMval treeTy pv) := rfl

theorem tree_ptr_compat (pv : CerbMem.PointerValue) :
    CerbMem.ctypeMemCompatible treePtrTy
      (CerbMem.typeofMval (CerbMem.pointerMval treeTy pv)) = true := rfl

theorem tree_ptr_img {tds : CerbTags.TagDefsMap} (pv : CerbMem.PointerValue) :
    (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval treeTy pv)).2 =
      trPtrImg pv := rfl

/-- The store kit at the two shapes a tree root can have (the list
    exhibit's `node_store_kit`, at the tree layout, offset-generic:
    the decode-back component serves BOTH child fields). -/
theorem tree_store_kit {tds : CerbTags.TagDefsMap} (pv : CerbMem.PointerValue)
    (hshape : pv = nullTree ∨ ∃ id aN : Int, pv = cellPtr id aN ∧
      0 < aN ∧ aN < 2 ^ 64) :
    (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval treeTy pv)).2.length
        = 8 ∧
    (∀ fpm, (CerbMem.memValueToBytes tds fpm
      (CerbMem.pointerMval treeTy pv)).1 = fpm) ∧
    (∀ fpm, (CerbMem.memValueToBytes tds fpm
        (CerbMem.pointerMval treeTy pv)).2 =
      (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval treeTy pv)).2) ∧
    (∀ (bs' : List CerbMem.AbsByte) (off : Nat), (bs'.drop off).take 8 =
        (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval treeTy pv)).2 →
      treePtrDec tds bs' off pv) := by
  rcases hshape with rfl | ⟨id, aN, rfl, h0, h1⟩
  · exact ⟨rfl, fun _ => rfl, fun _ => rfl,
      fun bs' off himg => treePtrDec_img_null bs' off himg⟩
  · refine ⟨?_, fun _ => rfl, fun _ => rfl,
      fun bs' off himg => treePtrDec_img_cell id aN h0 h1 bs' off himg⟩
    rw [tree_ptr_img]
    exact trPtrImg_cell_length id aN

/-! ## THE PREDICATE: `isTree p t` (structural recursion on the
identity-indexed tree — allocation id + value per node, TWO
sub-structures per node) -/

/-- The mathematical tree of node identities: each node carries its
    ALLOCATION ID and its value. -/
inductive NodeTree : Type where
  | leaf : NodeTree
  | node (id v : Int) (l r : NodeTree) : NodeTree

/-- The tree's allocation-id list (preorder). -/
def NodeTree.ids : NodeTree → List Int
  | .leaf => []
  | .node id _ l r => id :: (l.ids ++ r.ids)

section IsTree

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- THE REPRESENTATION PREDICATE: one ∗-composed ghost cell per
    node, ∃-bound child pointers, machine-address WF per node —
    the list predicate's discipline at branching recursion. -/
def isTree : CerbMem.PointerValue → NodeTree → IProp GF
  | p, .leaf => iprop(⌜p = nullTree⌝)
  | p, .node id v l r => iprop(∃ (aN : Int)
      (ql qr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 24 ∧
        nodeValDec fmapEmpty bs v ∧ treePtrDec fmapEmpty bs 8 ql ∧ treePtrDec fmapEmpty bs 16 qr⌝ ∗
      cellOwn fmapEmpty id (.own 1) (SpikeCell.mk aN treeTy bs) ∗
      isTree ql l ∗ isTree qr r)

@[simp] theorem isTree_leaf (p : CerbMem.PointerValue) :
    isTree (GF := GF) p .leaf = iprop(⌜p = nullTree⌝) := rfl

theorem isTree_node (p : CerbMem.PointerValue) (id v : Int)
    (l r : NodeTree) :
    isTree (GF := GF) p (.node id v l r) = iprop(∃ (aN : Int)
      (ql qr : CerbMem.PointerValue) (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 24 ∧
        nodeValDec fmapEmpty bs v ∧ treePtrDec fmapEmpty bs 8 ql ∧ treePtrDec fmapEmpty bs 16 qr⌝ ∗
      cellOwn fmapEmpty id (.own 1) (SpikeCell.mk aN treeTy bs) ∗
      isTree ql l ∗ isTree qr r) := rfl

theorem isTree_leaf_intro : ⊢ isTree (GF := GF) nullTree .leaf := by
  rw [isTree_leaf]
  ipureintro
  rfl

/-- Node introduction (the node's cell ∗ both subtrees). -/
theorem isTree_node_intro (id aN : Int) (ql qr : CerbMem.PointerValue)
    (bs : List CerbMem.AbsByte) (v : Int) (l r : NodeTree)
    (h0 : 0 < aN) (h1 : aN < 2 ^ 64) (hlen : bs.length = 24)
    (hval : nodeValDec fmapEmpty bs v) (hql : treePtrDec fmapEmpty bs 8 ql)
    (hqr : treePtrDec fmapEmpty bs 16 qr) :
    iprop(cellOwn fmapEmpty (GF := GF) id (.own 1) (SpikeCell.mk aN treeTy bs) ∗
        isTree ql l ∗ isTree qr r) ⊢
      isTree (cellPtr id aN) (.node id v l r) := by
  rw [isTree_node]
  iintro ⟨Hpt, HL, HR⟩
  iexists aN, ql, qr, bs
  isplit
  · ipureintro
    exact ⟨rfl, h0, h1, hlen, hval, hql, hqr⟩
  isplitl [Hpt]
  · iexact Hpt
  isplitl [HL]
  · iexact HL
  · iexact HR

/-- The shape of a tree root (extracted non-destructively). -/
theorem isTree_shape (p : CerbMem.PointerValue) (t : NodeTree) :
    isTree (GF := GF) p t ⊢
      iprop(⌜p = nullTree ∨ ∃ id aN : Int, p = cellPtr id aN ∧ 0 < aN ∧
        aN < 2 ^ 64⌝ ∗ isTree p t) := by
  cases t with
  | leaf =>
    rw [isTree_leaf]
    iintro %h
    isplit
    · ipureintro
      exact .inl h
    · ipureintro
      exact h
  | node id v l r =>
    rw [isTree_node]
    iintro ⟨%aN, %ql, %qr, %bs, %hfacts, Hpt, HL, HR⟩
    obtain ⟨hp, h0, h1, hlen, hval, hql, hqr⟩ := hfacts
    isplit
    · ipureintro
      exact .inr ⟨id, aN, hp, h0, h1⟩
    iexists aN, ql, qr, bs
    isplit
    · ipureintro
      exact ⟨hp, h0, h1, hlen, hval, hql, hqr⟩
    isplitl [Hpt]
    · iexact Hpt
    isplitl [HL]
    · iexact HL
    · iexact HR

end IsTree

/-! ## Seeding: a pure tree description of the initial cell map -/

open Iris.Std.PartialMap in
/-- The seeded tree, as a pure fact about a cell map: one disjoint
    singleton per node AT THE NODE'S ALLOCATION ID, decode facts per
    field, two disjoint sub-maps per node. -/
def SeedTree : CellMap → CerbMem.PointerValue → NodeTree → Prop
  | m, p, .leaf => m = (∅ : CellMap) ∧ p = nullTree
  | m, p, .node id v l r => ∃ (aN : Int) (ql qr : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte) (ml mr : CellMap),
      p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 24 ∧
      nodeValDec fmapEmpty bs v ∧ treePtrDec fmapEmpty bs 8 ql ∧ treePtrDec fmapEmpty bs 16 qr ∧
      ((singleton id (SpikeCell.mk aN treeTy bs) : CellMap)) ##ₘ
        (union ml mr) ∧
      ml ##ₘ mr ∧
      m = union (singleton id (SpikeCell.mk aN treeTy bs)) (union ml mr) ∧
      SeedTree ml ql l ∧ SeedTree mr qr r

open Iris.Std.PartialMap in
theorem get?_union_isSome (m₁ m₂ : CellMap) (k : Int) :
    (get? (union m₁ m₂) k).isSome ↔
      (get? m₁ k).isSome ∨ (get? m₂ k).isSome := by
  rw [get?_union' m₁ m₂ k]
  cases h : get? m₁ k with
  | some c => simp [Option.orElse]
  | none => simp [Option.orElse]

open Iris.Std.PartialMap in
theorem get?_singleton_isSome (i : Int) (x : SpikeCell) (k : Int) :
    (get? ((singleton i x) : CellMap) k).isSome ↔ k = i := by
  by_cases h : i = k
  · subst h
    rw [Iris.Std.LawfulPartialMap.get?_singleton_eq rfl]
    simp
  · rw [Iris.Std.LawfulPartialMap.get?_singleton_ne h]
    simp
    exact fun hk => h hk.symm

open Iris.Std.PartialMap in
/-- THE FOOTPRINT LAW: a seeded tree's cell map is defined at
    EXACTLY the tree's allocation ids. -/
theorem SeedTree.footprint :
    ∀ (t : NodeTree) (m : CellMap) (p : CerbMem.PointerValue),
      SeedTree m p t →
      ∀ k, (get? m k).isSome ↔ k ∈ t.ids
  | .leaf, m, p, hseed, k => by
    obtain ⟨rfl, -⟩ := hseed
    rw [Iris.Std.LawfulPartialMap.get?_empty]
    simp [NodeTree.ids]
  | .node id v l r, m, p, hseed, k => by
    obtain ⟨aN, ql, qr, bs, ml, mr, -, -, -, -, -, -, -, -, -, rfl,
      hl, hr⟩ := hseed
    have ihl := SeedTree.footprint l ml ql hl k
    have ihr := SeedTree.footprint r mr qr hr k
    rw [get?_union_isSome, get?_singleton_isSome, get?_union_isSome,
      ihl, ihr]
    simp [NodeTree.ids]

section SeedTreeIris

variable {hlc : HasLC} {GF : BundledGFunctors}

open Iris.Std.PartialMap in
/-- Seeding: the initial footprint's big-sep IS the tree predicate. -/
theorem seedTree_isTree [SpikeGS hlc GF] :
    ∀ (t : NodeTree) (m : CellMap) (p : CerbMem.PointerValue),
    SeedTree m p t →
    iprop(([∗map] i ↦ c ∈ m, cellOwn fmapEmpty (GF := GF) i (.own 1) c)) ⊢
      isTree p t
  | .leaf, m, p, hseed => by
    obtain ⟨rfl, rfl⟩ := hseed
    rw [isTree_leaf]
    iintro -
    ipureintro
    rfl
  | .node id v l r, m, p, hseed => by
    obtain ⟨aN, ql, qr, bs, ml, mr, hp, h0, h1, hlen, hval, hql, hqr,
      hd1, hd2, rfl, hl, hr⟩ := hseed
    subst hp
    iintro Hm
    icases (BigSepM.bigSepM_union hd1).1 $$ Hm with ⟨H1, Hrest⟩
    icases (BigSepM.bigSepM_union hd2).1 $$ Hrest with ⟨Hml, Hmr⟩
    iapply isTree_node_intro id aN ql qr bs v l r h0 h1 hlen hval hql hqr
    isplitl [H1]
    · iapply (BigSepM.bigSepM_singleton).1 $$ H1
    isplitl [Hml]
    · iapply seedTree_isTree l ml ql hl $$ Hml
    · iapply seedTree_isTree r mr qr hr $$ Hmr

open Iris.Std.PartialMap in
/-- The readout companion: an `isTree` footprint RE-MATERIALIZES as
    a cell map with a pure `SeedTree` description — all
    disjointnesses forced by ownership validity. -/
theorem isTree_to_cells [SpikeGS .hasLC GF] :
    ∀ (t : NodeTree) (p : CerbMem.PointerValue),
    isTree (hlc := .hasLC) (GF := GF) p t ⊢
      iprop(∃ m : CellMap, ⌜SeedTree m p t⌝ ∗
        ([∗map] i ↦ c ∈ m, cellOwn fmapEmpty (hlc := .hasLC) i (.own 1) c))
  | .leaf, p => by
    rw [isTree_leaf]
    iintro %h
    iexists (∅ : CellMap)
    isplit
    · ipureintro
      exact ⟨rfl, h⟩
    · iapply BigSepM.bigSepM_empty
      itrivial
  | .node id v l r, p => by
    rw [isTree_node]
    iintro ⟨%aN, %ql, %qr, %bs, %hfacts, Hpt, HL, HR⟩
    obtain ⟨rfl, h0, h1, hlen, hval, hql, hqr⟩ := hfacts
    ihave HLC := isTree_to_cells l ql $$ HL
    icases HLC with ⟨%ml, %hml, Hml⟩
    ihave HRC := isTree_to_cells r qr $$ HR
    icases HRC with ⟨%mr, %hmr, Hmr⟩
    ihave %hd2 : ⌜ml ##ₘ mr⌝ $$ [Hml Hmr]
    · iapply bigSepM_own_disjoint fmapEmpty ml mr
      isplitl [Hml]
      · iexact Hml
      · iexact Hmr
    ihave Hlr : iprop(([∗map] i ↦ c ∈ (union ml mr : CellMap),
        cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)) $$ [Hml Hmr]
    · iapply (BigSepM.bigSepM_union hd2).2
      isplitl [Hml]
      · iexact Hml
      · iexact Hmr
    ihave H1 : iprop(([∗map] i ↦ c ∈ ((singleton id
        (SpikeCell.mk aN treeTy bs)) : CellMap),
        cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)) $$ [Hpt]
    · iapply (BigSepM.bigSepM_singleton
        (Φ := fun (i : Int) (c : SpikeCell) =>
          cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)
        (i := id) (x := SpikeCell.mk aN treeTy bs)).2
      iexact Hpt
    ihave %hd1 : ⌜((singleton id (SpikeCell.mk aN treeTy bs)) : CellMap) ##ₘ
        (union ml mr)⌝ $$ [H1 Hlr]
    · iapply bigSepM_own_disjoint fmapEmpty _ (union ml mr)
      isplitl [H1]
      · iexact H1
      · iexact Hlr
    iexists (union (singleton id (SpikeCell.mk aN treeTy bs)) (union ml mr))
    isplit
    · ipureintro
      exact ⟨aN, ql, qr, bs, ml, mr, rfl, h0, h1, hlen, hval, hql, hqr,
        hd1, hd2, rfl, hml, hmr⟩
    iapply (BigSepM.bigSepM_union hd1).2
    isplitl [H1]
    · iexact H1
    · iexact Hlr

end SeedTreeIris

/-! ## THE PROGRAM (authored Core, straight-line) -/

def trXSym : sym := Symbol "" 501 SD_None
def trYSym : sym := Symbol "" 502 SD_None
def trBSym : sym := Symbol "" 503 SD_None

/-- The field addresses: one resp. two long-element shifts of a
    bound symbol. -/
def trShift1 (s : sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEarray_shift (Pexpr [] () (PEsym s)) longTy
    (Pexpr [] () (PEval (ivVal 1))))

def trShift2 (s : sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEarray_shift (Pexpr [] () (PEsym s)) longTy
    (Pexpr [] () (PEval (ivVal 2))))

/-- Everything after the x binding. -/
def trRest (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (ybty bbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (specPat [] [] trYSym ybty)
    (loadOpRedex loc ann treePtrTy (trShift1 trXSym) mo)
    (Expr [] (Esseq (specPat [] [] trBSym bbty)
      (loadOpRedex loc ann treePtrTy (trShift2 trYSym) mo)
      (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
        (storeOpRedex loc ann treePtrTy (trShift1 trXSym)
          (Pexpr [] () (PEsym trBSym)) mo)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (storeOpRedex loc ann treePtrTy (trShift2 trYSym)
            (Pexpr [] () (PEsym trXSym)) mo)
          (Expr [] (Epure (Pexpr [] () (PEsym trYSym)))))))))))

/-- The whole rotation program. -/
def trProg (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (xbty ybty bbty ubty : core_base_type)
    (px : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Esseq (symPat [] trXSym xbty)
    (Expr [] (Epure (Pexpr [] () (PEval (ptrVal px)))))
    (trRest loc ann mo ybty bbty ubty))

/-- Cone membership: sym-binder over a value, two Specified-binder
    loads, two wildcard stores, PEsym exit — all through the one
    unified cone. ZERO new constructors. -/
theorem trProg_frag (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (xbty ybty bbty ubty : core_base_type)
    (px : CerbMem.PointerValue)
    (hlib : CerbLocation.isLibraryLocation loc = false) :
    Frag (trProg loc ann mo xbty ybty bbty ubty px) := by
  refine .sseq_sym (.val_pure _)
    (.sseq_spec
      (.load_op hlib rfl
        (.arrayShift [] longTy (.sym _ _) (.val _ _))
        (by rw [show peDepth (trShift1 trXSym) = 2 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega))
      (.sseq_spec
        (.load_op hlib rfl
          (.arrayShift [] longTy (.sym _ _) (.val _ _))
          (by rw [show peDepth (trShift2 trYSym) = 2 from rfl,
            show lemDefaultFuel = 999999 + 1 from rfl]; omega))
        (.sseq
          (.store_op hlib rfl
            (.arrayShift [] longTy (.sym _ _) (.val _ _)) (.sym _ _)
            (by rw [show peDepth (trShift1 trXSym) = 2 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega)
            (by rw [show peDepth (Pexpr ([] : List annot) ()
                (PEsym trBSym)) = 1 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega))
          (.sseq
            (.store_op hlib rfl
              (.arrayShift [] longTy (.sym _ _) (.val _ _)) (.sym _ _)
              (by rw [show peDepth (trShift2 trYSym) = 2 from rfl,
                show lemDefaultFuel = 999999 + 1 from rfl]; omega)
              (by rw [show peDepth (Pexpr ([] : List annot) ()
                  (PEsym trXSym)) = 1 from rfl,
                show lemDefaultFuel = 999999 + 1 from rfl]; omega))
            .pure_sym))))

/-! ## Frames and lookups -/

def trF1 (vx : value) : Fmap sym value := envAdd trXSym vx fmapEmpty
def trF2 (vy vx : value) : Fmap sym value := envAdd trYSym vy (trF1 vx)
def trF3 (vb vy vx : value) : Fmap sym value := envAdd trBSym vb (trF2 vy vx)

theorem trF1_symFrame (vx : value) : SymFrame (trF1 vx) :=
  symFrame_empty.add _ _

theorem trF2_symFrame (vy vx : value) : SymFrame (trF2 vy vx) :=
  (trF1_symFrame vx).add _ _

theorem trF3_symFrame (vb vy vx : value) : SymFrame (trF3 vb vy vx) :=
  (trF2_symFrame vy vx).add _ _

theorem trF1_lookup_x (vx : value) :
    fmapLookupBy symCmpK trXSym (trF1 vx) = some vx := by
  unfold trF1
  rw [envAdd_lookup symFrame_empty symCmpK, if_pos (by decide +kernel)]

theorem trF2_lookup_y (vy vx : value) :
    fmapLookupBy symCmpK trYSym (trF2 vy vx) = some vy := by
  unfold trF2
  rw [envAdd_lookup (trF1_symFrame vx) symCmpK, if_pos (by decide +kernel)]

theorem trF2_lookup_x (vy vx : value) :
    fmapLookupBy symCmpK trXSym (trF2 vy vx) = some vx := by
  unfold trF2
  rw [envAdd_lookup (trF1_symFrame vx) symCmpK, if_neg (by decide +kernel),
    trF1_lookup_x]

theorem trF3_lookup_b (vb vy vx : value) :
    fmapLookupBy symCmpK trBSym (trF3 vb vy vx) = some vb := by
  unfold trF3
  rw [envAdd_lookup (trF2_symFrame vy vx) symCmpK,
    if_pos (by decide +kernel)]

theorem trF3_lookup_y (vb vy vx : value) :
    fmapLookupBy symCmpK trYSym (trF3 vb vy vx) = some vy := by
  unfold trF3
  rw [envAdd_lookup (trF2_symFrame vy vx) symCmpK,
    if_neg (by decide +kernel), trF2_lookup_y]

theorem trF3_lookup_x (vb vy vx : value) :
    fmapLookupBy symCmpK trXSym (trF3 vb vy vx) = some vx := by
  unfold trF3
  rw [envAdd_lookup (trF2_symFrame vy vx) symCmpK,
    if_neg (by decide +kernel), trF2_lookup_x]

/-! ## Binding computations -/

theorem trBindX (xbty : core_base_type) (vx : value) :
    update_env (symPat [] trXSym xbty) vx
        (fmapEmpty :: ([] : List (Fmap sym value))) =
      trF1 vx :: [] := by
  rw [update_env_cons]
  show update_env_aux (mk_sym_pat trXSym xbty) vx fmapEmpty ::
    ([] : List (Fmap sym value)) = _
  rw [update_env_aux_sym]
  rfl

theorem trBindY (ybty : core_base_type) (ov : object_value) (vx : value) :
    update_env (specPat [] [] trYSym ybty) (Vloaded (LVspecified ov))
        (trF1 vx :: ([] : List (Fmap sym value))) =
      trF2 (Vobject ov) vx :: [] := by
  rw [update_env_spec]
  rfl

theorem trBindB (bbty : core_base_type) (ov : object_value) (vy vx : value) :
    update_env (specPat [] [] trBSym bbty) (Vloaded (LVspecified ov))
        (trF2 vy vx :: ([] : List (Fmap sym value))) =
      trF3 (Vobject ov) vy vx :: [] := by
  rw [update_env_spec]
  rfl

/-! ## Evaluation facts at the bound frames -/

theorem tr_shift1_eval_F1 (id aX : Int) :
    evalPexpr fmapEmpty fmapEmpty (trF1 (ptrVal (cellPtr id aX)) :: [])
      (trShift1 trXSym) = some (ptrVal (cellPtr id (aX + 8))) := by
  unfold trShift1
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (trF1 (ptrVal (cellPtr id aX)) :: [])
      (Pexpr [] () (PEsym trXSym)) = some (ptrVal (cellPtr id aX)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (trF1_lookup_x _) []]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id aX))) (ivVal 1) = _
  exact evalArrayShift_long_one id aX

theorem tr_shift2_eval_F2 (id aY : Int) (vx : value) :
    evalPexpr fmapEmpty fmapEmpty (trF2 (ptrVal (cellPtr id aY)) vx :: [])
      (trShift2 trYSym) = some (ptrVal (cellPtr id (aY + 16))) := by
  unfold trShift2
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (trF2 (ptrVal (cellPtr id aY)) vx :: [])
      (Pexpr [] () (PEsym trYSym)) = some (ptrVal (cellPtr id aY)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (trF2_lookup_y _ _) []]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id aY))) (ivVal 2) = _
  exact evalArrayShift_long_two id aY

theorem tr_shift1_eval_F3 (vb vy : value) (id aX : Int) :
    evalPexpr fmapEmpty fmapEmpty (trF3 vb vy (ptrVal (cellPtr id aX)) :: [])
      (trShift1 trXSym) = some (ptrVal (cellPtr id (aX + 8))) := by
  unfold trShift1
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (trF3 vb vy (ptrVal (cellPtr id aX)) :: [])
      (Pexpr [] () (PEsym trXSym)) = some (ptrVal (cellPtr id aX)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (trF3_lookup_x _ _ _) []]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id aX))) (ivVal 1) = _
  exact evalArrayShift_long_one id aX

theorem tr_shift2_eval_F3 (vb vx : value) (id aY : Int) :
    evalPexpr fmapEmpty fmapEmpty (trF3 vb (ptrVal (cellPtr id aY)) vx :: [])
      (trShift2 trYSym) = some (ptrVal (cellPtr id (aY + 16))) := by
  unfold trShift2
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (trF3 vb (ptrVal (cellPtr id aY)) vx :: [])
      (Pexpr [] () (PEsym trYSym)) = some (ptrVal (cellPtr id aY)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (trF3_lookup_y _ _ _) []]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id aY))) (ivVal 2) = _
  exact evalArrayShift_long_two id aY

theorem tr_b_eval_F3 (vb vy vx : value) :
    evalPexpr fmapEmpty fmapEmpty (trF3 vb vy vx :: [])
      (Pexpr [] () (PEsym trBSym)) = some vb := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (trF3_lookup_b _ _ _) []

theorem tr_x_eval_F3 (vb vy vx : value) :
    evalPexpr fmapEmpty fmapEmpty (trF3 vb vy vx :: [])
      (Pexpr [] () (PEsym trXSym)) = some vx := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (trF3_lookup_x _ _ _) []

theorem tr_y_eval_F3 (vb vy vx : value) :
    evalPexpr fmapEmpty fmapEmpty (trF3 vb vy vx :: [])
      (Pexpr [] () (PEsym trYSym)) = some vy := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (trF3_lookup_y _ _ _) []

/-! ## The tree-node field access rules — CLIENT INSTANCES of the
generic typed-subrange rules (fresh-client discipline: no lifting
proof in this module) -/

section TreeClients

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpec GF}

/-- TREE `tree*`-FIELD LOAD — `wps_load_cell_at` at view type
    `treePtrTy`. -/
theorem wps_load_tree_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (mo : memory_order)
    (dq : DFrac) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {mv : CerbMem.MemValue}
    (hbound : off + 8 ≤ CerbMem.sizeofCtype M.tagDefs treeTy)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      treePtrTy ((bs.drop off).take 8) = mv) :
    iprop(cellOwn M.tagDefs (GF := GF) id dq (SpikeCell.mk a treeTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id dq (SpikeCell.mk a treeTy bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann treePtrTy (cellPtr id (a + (off : Int))) mo)
        ρ :=
  wps_load_cell_at loc ann id a treeTy off treePtrTy mo dq bs ρ
    (by rw [treePtrTy_size]; exact hbound)
    (by rw [treePtrTy_size]; exact hdec) rfl

/-- TREE `tree*`-FIELD STORE — `wps_store_cell_at` at view type
    `treePtrTy`; whole-cell inertness is `treeTy_dec_indep`. -/
theorem wps_store_tree_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (cv : value) (mo : memory_order)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ treePtrTy)) cv =
      some mv)
    (hbound : off + 8 ≤ CerbMem.sizeofCtype M.tagDefs treeTy)
    (hlen : (CerbMem.memValueToBytes M.tagDefs [] mv).2.length = 8)
    (hcompat : CerbMem.ctypeMemCompatible treePtrTy (CerbMem.typeofMval mv) =
      true)
    (hfpm : ∀ fpm, (CerbMem.memValueToBytes M.tagDefs fpm mv).1 = fpm)
    (hbytes : ∀ fpm, (CerbMem.memValueToBytes M.tagDefs fpm mv).2 =
      (CerbMem.memValueToBytes M.tagDefs [] mv).2) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a treeTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a treeTy
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann treePtrTy (cellPtr id (a + (off : Int)))
        cv mo) ρ :=
  wps_store_cell_at loc ann id a treeTy off treePtrTy cv mo bs ρ hmv
    (by rw [treePtrTy_size]; exact hbound)
    ⟨hcompat, hfpm, hbytes, by rw [treePtrTy_size]; exact hlen⟩
    (fun lum fpm => treeTy_dec_indep lum fpm a _)

end TreeClients

section TreeClientsT

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpecT GF}

/-- Total form of the tree-field load (cost 3 ≤ k). -/
theorem wpt_load_tree_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (mo : memory_order)
    (dq : DFrac) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {mv : CerbMem.MemValue} {k : Nat} (hk : 3 ≤ k)
    (hbound : off + 8 ≤ CerbMem.sizeofCtype M.tagDefs treeTy)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      treePtrTy ((bs.drop off).take 8) = mv) :
    iprop(cellOwn M.tagDefs (GF := GF) id dq (SpikeCell.mk a treeTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id dq (SpikeCell.mk a treeTy bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wpt M Ls k Ψ (loadExpr loc ann treePtrTy (cellPtr id (a + (off : Int))) mo)
        ρ :=
  wpt_load_cell_at loc ann id a treeTy off treePtrTy mo dq bs ρ hk
    (by rw [treePtrTy_size]; exact hbound)
    (by rw [treePtrTy_size]; exact hdec) rfl

/-- Total form of the tree-field store (cost 3 ≤ k). -/
theorem wpt_store_tree_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (cv : value) (mo : memory_order)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ treePtrTy)) cv =
      some mv)
    (hbound : off + 8 ≤ CerbMem.sizeofCtype M.tagDefs treeTy)
    (hlen : (CerbMem.memValueToBytes M.tagDefs [] mv).2.length = 8)
    (hcompat : CerbMem.ctypeMemCompatible treePtrTy (CerbMem.typeofMval mv) =
      true)
    (hfpm : ∀ fpm, (CerbMem.memValueToBytes M.tagDefs fpm mv).1 = fpm)
    (hbytes : ∀ fpm, (CerbMem.memValueToBytes M.tagDefs fpm mv).2 =
      (CerbMem.memValueToBytes M.tagDefs [] mv).2) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a treeTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a treeTy
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wpt M Ls k Ψ (storeExpr loc ann treePtrTy (cellPtr id (a + (off : Int)))
        cv mo) ρ :=
  wpt_store_cell_at loc ann id a treeTy off treePtrTy cv mo bs ρ hk hmv
    (by rw [treePtrTy_size]; exact hbound)
    ⟨hcompat, hfpm, hbytes, by rw [treePtrTy_size]; exact hlen⟩
    (fun lum fpm => treeTy_dec_indep lum fpm a _)

end TreeClientsT

/-! ## Splice slices at the tree layout (below / self / ABOVE — the
above case is new relative to the two-field list node) -/

theorem trSplice8_val (img bs : List CerbMem.AbsByte)
    (himg : img.length = 8) (hbs : bs.length = 24) :
    ((spliceBytes 8 img bs).drop 0).take 8 = (bs.drop 0).take 8 :=
  spliceBytes_slice_below 8 img bs (by omega) 0 8 (by omega)

theorem trSplice8_self (img bs : List CerbMem.AbsByte)
    (himg : img.length = 8) (hbs : bs.length = 24) :
    ((spliceBytes 8 img bs).drop 8).take 8 = img := by
  have h := spliceBytes_slice_self 8 img bs (by omega)
  rw [himg] at h
  exact h

theorem trSplice8_right (img bs : List CerbMem.AbsByte)
    (himg : img.length = 8) (hbs : bs.length = 24) :
    ((spliceBytes 8 img bs).drop 16).take 8 = (bs.drop 16).take 8 :=
  spliceBytes_slice_above 8 img bs (by omega) 16 8 (by omega)

theorem trSplice16_val (img bs : List CerbMem.AbsByte)
    (himg : img.length = 8) (hbs : bs.length = 24) :
    ((spliceBytes 16 img bs).drop 0).take 8 = (bs.drop 0).take 8 :=
  spliceBytes_slice_below 16 img bs (by omega) 0 8 (by omega)

theorem trSplice16_left (img bs : List CerbMem.AbsByte)
    (himg : img.length = 8) (hbs : bs.length = 24) :
    ((spliceBytes 16 img bs).drop 8).take 8 = (bs.drop 8).take 8 :=
  spliceBytes_slice_below 16 img bs (by omega) 8 8 (by omega)

theorem trSplice16_self (img bs : List CerbMem.AbsByte)
    (himg : img.length = 8) (hbs : bs.length = 24) :
    ((spliceBytes 16 img bs).drop 16).take 8 = img := by
  have h := spliceBytes_slice_self 16 img bs (by omega)
  rw [himg] at h
  exact h

/-! ## THE DERIVATION (textbook, straight-line: every construct by
its small rule; the two subtree assertions and the frame ride by ∗
alone — no invariant, no labels) -/

section TrIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {Ls : LabelSpec GF}
variable (loc : CerbLocation.Loc) (ann : core_run_annotation)
  (mo : memory_order) (xbty ybty bbty ubty : core_base_type)

/-- The rotation postcondition: the delivered value is the left
    child's pointer, now heading the rotated tree. UNFRAMED (alloc arc
    P4.2): the frame is added by the generic frame rules
    (`wps_sound_frame` in `tr_wp_readout`; `tree_rotate_wpt_frame`). -/
abbrev trPost (t' : NodeTree) :
    SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(∃ p' : CerbMem.PointerValue, ⌜w.val = ptrVal p'⌝ ∗
    isTree p' t')

/-- The rotation at the statement layer:
    `{ isTree px (node x vx (node y vy a b) c) }
       rotate-right
     { ret py. isTree py (node y vy a (node x vx b c)) }`. -/
theorem tree_rotate_wps
    (idx idy vx vy : Int) (ta tb tc : NodeTree)
    (px : CerbMem.PointerValue) :
    isTree (GF := GF) px (.node idx vx (.node idy vy ta tb) tc) ⊢
      wps spikeCtx Ls
        (trPost (.node idy vy ta (.node idx vx tb tc)))
        (trProg loc ann mo xbty ybty bbty ubty px)
        [fmapEmpty] := by
  iintro HX
  rw [isTree_node]
  icases HX with ⟨%aX, %qL, %qR, %bsx, %hfx, HptX, HY, Hc⟩
  obtain ⟨rfl, h0x, h1x, hlenx, hvalx, hLx, hRx⟩ := hfx
  rw [isTree_node]
  icases HY with ⟨%aY, %qa, %qb, %bsy, %hfy, HptY, Ha, Hb⟩
  obtain ⟨rfl, h0y, h1y, hleny, hvaly, hLy, hRy⟩ := hfy
  -- b's shape (for the first store's kit), non-destructively
  ihave Hb2 := isTree_shape qb tb $$ Hb
  icases Hb2 with ⟨%hshapeb, Hb⟩
  have kitB := tree_store_kit (tds := fmapEmpty) qb hshapeb
  obtain ⟨kBlen, kBfpm, kBbytes, kBdec⟩ := kitB
  have kitX := tree_store_kit (tds := fmapEmpty) (cellPtr idx aX)
    (.inr ⟨idx, aX, rfl, h0x, h1x⟩)
  obtain ⟨kXlen, kXfpm, kXbytes, kXdec⟩ := kitX
  rw [show trProg loc ann mo xbty ybty bbty ubty (cellPtr idx aX) =
    Expr [] (Esseq (symPat [] trXSym xbty)
      (Expr [] (Epure (Pexpr [] () (PEval (ptrVal (cellPtr idx aX))))))
      (trRest loc ann mo ybty bbty ubty)) from rfl]
  iapply wps_seq_sym
  rw [show Expr ([] : List annot)
      (Epure (Pexpr [] () (PEval (ptrVal (cellPtr idx aX))))) =
    ofVal (.pure (ptrVal (cellPtr idx aX))) from rfl]
  iapply wps_ofVal (.pure (ptrVal (cellPtr idx aX))) [fmapEmpty]
  iexists (ptrVal (cellPtr idx aX))
  isplit
  · ipureintro
    rfl
  rw [trBindX]
  -- y := x->left
  rw [show trRest loc ann mo ybty bbty ubty =
    Expr [] (Esseq (specPat [] [] trYSym ybty)
      (loadOpRedex loc ann treePtrTy (trShift1 trXSym) mo)
      (Expr [] (Esseq (specPat [] [] trBSym bbty)
        (loadOpRedex loc ann treePtrTy (trShift2 trYSym) mo)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (storeOpRedex loc ann treePtrTy (trShift1 trXSym)
            (Pexpr [] () (PEsym trBSym)) mo)
          (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
            (storeOpRedex loc ann treePtrTy (trShift2 trYSym)
              (Pexpr [] () (PEsym trXSym)) mo)
            (Expr [] (Epure (Pexpr [] () (PEsym trYSym))))))))))) from rfl]
  iapply wps_seq_spec
  iapply wps_load_eval loc ann treePtrTy (trShift1 trXSym) mo _
    rfl (tr_shift1_eval_F1 idx aX)
  rw [show cellPtr idx (aX + 8) = cellPtr idx (aX + ((8 : Nat) : Int))
    from rfl]
  iapply wps_load_tree_field (M := spikeCtx) loc ann idx aX 8 mo (.own 1) bsx _
    (by rw [treeTy_size]; omega)
    (fun lum fpm => hLx lum fpm _)
  isplitl [HptX]
  · iexact HptX
  iintro %fp1 HptX
  iexists (OVpointer (cellPtr idy aY))
  isplit
  · ipureintro
    show (valueFromMemValue (.MVpointer treeTy (cellPtr idy aY))).2 = _
    rw [valueFromMemValue_ptr]
  rw [trBindY]
  rw [show trF2 (Vobject (OVpointer (cellPtr idy aY)))
        (ptrVal (cellPtr idx aX)) =
      trF2 (ptrVal (cellPtr idy aY)) (ptrVal (cellPtr idx aX)) from rfl]
  -- b := y->right
  iapply wps_seq_spec
  iapply wps_load_eval loc ann treePtrTy (trShift2 trYSym) mo _
    rfl (tr_shift2_eval_F2 idy aY _)
  rw [show cellPtr idy (aY + 16) = cellPtr idy (aY + ((16 : Nat) : Int))
    from rfl]
  iapply wps_load_tree_field (M := spikeCtx) loc ann idy aY 16 mo (.own 1) bsy _
    (by rw [treeTy_size]; omega)
    (fun lum fpm => hRy lum fpm _)
  isplitl [HptY]
  · iexact HptY
  iintro %fp2 HptY
  iexists (OVpointer qb)
  isplit
  · ipureintro
    show (valueFromMemValue (.MVpointer treeTy qb)).2 = _
    rw [valueFromMemValue_ptr]
  rw [trBindB]
  rw [show trF3 (Vobject (OVpointer qb)) (ptrVal (cellPtr idy aY))
        (ptrVal (cellPtr idx aX)) =
      trF3 (ptrVal qb) (ptrVal (cellPtr idy aY))
        (ptrVal (cellPtr idx aX)) from rfl]
  -- x->left := b
  iapply wps_seq
  iapply wps_store_eval loc ann treePtrTy _ _ mo _
    rfl (tr_shift1_eval_F3 _ _ idx aX)
    (tr_b_eval_F3 _ _ _)
  rw [show cellPtr idx (aX + 8) = cellPtr idx (aX + ((8 : Nat) : Int))
    from rfl]
  iapply wps_store_tree_field (M := spikeCtx) loc ann idx aX 8 (ptrVal qb) mo bsx _
    (tree_ptr_encodes qb) (by rw [treeTy_size]; omega) kBlen
    (tree_ptr_compat qb) kBfpm kBbytes
  isplitl [HptX]
  · iexact HptX
  iintro %fp3 HptX
  -- y->right := x
  iapply wps_seq
  iapply wps_store_eval loc ann treePtrTy _ _ mo _
    rfl (tr_shift2_eval_F3 _ _ idy aY)
    (tr_x_eval_F3 _ _ _)
  rw [show cellPtr idy (aY + 16) = cellPtr idy (aY + ((16 : Nat) : Int))
    from rfl]
  iapply wps_store_tree_field (M := spikeCtx) loc ann idy aY 16 (ptrVal (cellPtr idx aX))
    mo bsy _
    (tree_ptr_encodes (cellPtr idx aX)) (by rw [treeTy_size]; omega) kXlen
    (tree_ptr_compat (cellPtr idx aX)) kXfpm kXbytes
  isplitl [HptY]
  · iexact HptY
  iintro %fp4 HptY
  -- pure(y): reassemble the rotated tree
  iapply wps_pure (Pexpr [] () (PEsym trYSym)) _ rfl (tr_y_eval_F3 _ _ _)
  iexists (cellPtr idy aY)
  isplit
  · ipureintro
    rfl
  · -- isTree (cellPtr idy aY) (node idy vy ta (node idx vx tb tc))
    iapply isTree_node_intro idy aY qa (cellPtr idx aX)
      (spliceBytes 16 (CerbMem.memValueToBytes spikeCtx.tagDefs []
        (CerbMem.pointerMval treeTy (cellPtr idx aX))).2 bsy)
      vy ta (.node idx vx tb tc) h0y h1y
      (by rw [spliceBytes_length _ _ _ (by rw [kXlen, hleny]; omega)]
          exact hleny)
      (by intro lum fpm ad
          rw [show ((spliceBytes 16 (CerbMem.memValueToBytes spikeCtx.tagDefs []
              (CerbMem.pointerMval treeTy (cellPtr idx aX))).2 bsy).drop
                0).take 8 =
            (bsy.drop 0).take 8 from trSplice16_val _ bsy kXlen hleny]
          exact hvaly lum fpm ad)
      (by intro lum fpm ad
          rw [show ((spliceBytes 16 (CerbMem.memValueToBytes spikeCtx.tagDefs []
              (CerbMem.pointerMval treeTy (cellPtr idx aX))).2 bsy).drop
                8).take 8 =
            (bsy.drop 8).take 8 from trSplice16_left _ bsy kXlen hleny]
          exact hLy lum fpm ad)
      (kXdec _ 16 (trSplice16_self _ bsy kXlen hleny))
    isplitl [HptY]
    · iexact HptY
    isplitl [Ha]
    · iexact Ha
    · -- the rotated right subtree: x now holds b on its left
      iapply isTree_node_intro idx aX qb qR
        (spliceBytes 8 (CerbMem.memValueToBytes spikeCtx.tagDefs []
          (CerbMem.pointerMval treeTy qb)).2 bsx)
        vx tb tc h0x h1x
        (by rw [spliceBytes_length _ _ _ (by rw [kBlen, hlenx]; omega)]
            exact hlenx)
        (by intro lum fpm ad
            rw [show ((spliceBytes 8 (CerbMem.memValueToBytes spikeCtx.tagDefs []
                (CerbMem.pointerMval treeTy qb)).2 bsx).drop 0).take 8 =
              (bsx.drop 0).take 8 from trSplice8_val _ bsx kBlen hlenx]
            exact hvalx lum fpm ad)
        (kBdec _ 8 (trSplice8_self _ bsx kBlen hlenx))
        (by intro lum fpm ad
            rw [show ((spliceBytes 8 (CerbMem.memValueToBytes spikeCtx.tagDefs []
                (CerbMem.pointerMval treeTy qb)).2 bsx).drop 16).take 8 =
              (bsx.drop 16).take 8 from trSplice8_right _ bsx kBlen hlenx]
            exact hRx lum fpm ad)
      isplitl [HptX]
      · iexact HptX
      isplitl [Hb]
      · iexact Hb
      · iexact Hc

/-- Vacuous block specifications (straight-line profile) — at ANY
    postcondition. -/
theorem tr_blockSpecs (Ψ : SpikeVal → EnvStack → IProp GF) :
    ⊢ blockSpecs (GF := GF) spikeCtx (fun _ _ _ => iprop(False)) Ψ :=
  blockSpecs_intro fun l _ _ _ _ _ hl => (spikeCtx_labels_none l hl).elim

end TrIris

/-! ## The readout and the engine exports (the flagship shape) -/

section TrLaunch

open Iris.Std.PartialMap

variable {GF : BundledGFunctors}
variable (loc : CerbLocation.Loc) (ann : core_run_annotation)
  (mo : memory_order) (xbty ybty bbty ubty : core_base_type)

/-- The rotation readout — through the core `cells_readout` (no
    state-interpretation opening in this module). -/
theorem trPost_readout [SpikeGS .hasLC GF] (t' : NodeTree) (R : CellMap) :
    ∀ (w : SpikeVal) (ρ' : EnvStack),
    iprop(trPost (hlc := .hasLC) (GF := GF) t' w ρ' ∗ lrCellFrame R) ⊢
      readoutPost (fun v σ' => ∃ Q : CellMap,
        (∃ p' : CerbMem.PointerValue, v = ptrVal p' ∧ SeedTree Q p' t') ∧
        Q ##ₘ R ∧ Coh fmapEmpty σ' (union Q R)) w ρ' := by
  intro w ρ'
  iintro ⟨⟨%p', %hval, HT⟩, HF⟩
  ihave HC := isTree_to_cells t' p' $$ HT
  icases HC with ⟨%Q, %hQ, HQ⟩
  iapply cells_readout fmapEmpty (fun v Q => ∃ p' : CerbMem.PointerValue,
      v = ptrVal p' ∧ SeedTree Q p' t') R w.val
  isplitl [HQ]
  · iexists Q
    isplit
    · ipureintro
      exact ⟨p', hval, hQ⟩
    · iexact HQ
  · iexact HF

/-- The base-WP face (the launch shape `spike_engine_adequacy`
    consumes) — through THE WHOLE-LOOP FRAME RULE `wps_sound_frame`
    (alloc arc P4.2): the unframed rotation proof plus the cell frame
    collapse to the base WP with the frame in the postcondition. -/
theorem tr_wp_readout [SpikeGS .hasLC GF]
    (idx idy vx vy : Int) (ta tb tc : NodeTree)
    (px : CerbMem.PointerValue) (R : CellMap) :
    iprop(isTree (hlc := .hasLC) (GF := GF) px
        (.node idx vx (.node idy vy ta tb) tc) ∗ lrCellFrame R) ⊢
      WP (⟨trProg loc ann mo xbty ybty bbty ubty px, spikeEnv,
            spikeCtx⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns' : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns' κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜∃ Q : CellMap, (∃ p' : CerbMem.PointerValue,
                CoreRVal.val w = ptrVal p' ∧
                SeedTree Q p' (.node idy vy ta (.node idx vx tb tc))) ∧
              Q ##ₘ R ∧ Coh spikeCtx.tagDefs σ' (union Q R)⌝) }} := by
  refine (BI.sep_mono (tree_rotate_wps (Ls := fun _ _ _ => iprop(False)) loc ann mo
    xbty ybty bbty ubty idx idy vx vy ta tb tc px) .rfl).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((tr_blockSpecs (trPost (NodeTree.node idy vy ta (NodeTree.node idx vx tb tc)))).trans
      (wps_sound_frame (lrCellFrame R) (trProg loc ann mo xbty ybty bbty ubty px) spikeEnv))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  refine wp_mono fun w => ?_
  exact trPost_readout
    (NodeTree.node idy vy ta (NodeTree.node idx vx tb tc)) R w.w w.ρ

/-- The rotated id list is a PERMUTATION of the original — here in
    the membership form the footprint conjunct consumes. -/
theorem rotate_ids_mem (idx idy vx vy : Int) (ta tb tc : NodeTree)
    (k : Int) :
    k ∈ (NodeTree.node idy vy ta (.node idx vx tb tc)).ids ↔
      k ∈ (NodeTree.node idx vx (.node idy vy ta tb) tc).ids := by
  simp only [NodeTree.ids, List.mem_cons, List.mem_append]
  constructor
  · rintro (rfl | h | rfl | h | h)
    · exact .inr (.inl (.inl rfl))
    · exact .inr (.inl (.inr (.inl h)))
    · exact .inl rfl
    · exact .inr (.inl (.inr (.inr h)))
    · exact .inr (.inr h)
  · rintro (rfl | (rfl | h | h) | h)
    · exact .inr (.inr (.inl rfl))
    · exact .inl rfl
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))

end TrLaunch

section TrDrive

open Iris.Std.PartialMap

variable (loc : CerbLocation.Loc) (ann : core_run_annotation)
  (mo : memory_order) (xbty ybty bbty ubty : core_base_type)

theorem trProg_esize (px : CerbMem.PointerValue) :
    esize (trProg loc ann mo xbty ybty bbty ubty px) = 6 := rfl

/-- TREE ROTATION, END TO END (the second client at the flagship
    shape — audit F-06 item 6): driving the REAL engine on the
    right rotation, from ANY memory satisfying the seeded tree
    `m₀` next to an ARBITRARY disjoint frame footprint `R`:
    never killed, never derailed, and any delivered value is the
    left child's pointer heading a final footprint `Q` seeded as
    the ROTATED tree — the SAME allocations (footprint equality
    stated on the maps; the rotated id list is a permutation of the
    original), each node its own value — with `R` returned VERBATIM.
    ZERO core-logic edits were made for this module. -/
theorem tree_rotate_certified (sbty : core_base_type)
    (idx idy vx vy : Int) (ta tb tc : NodeTree)
    (px : CerbMem.PointerValue)
    (m₀ : CellMap)
    (hseed : SeedTree m₀ px (.node idx vx (.node idy vy ta tb) tc))
    (R : CellMap) (hR : m₀ ##ₘ R)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem) (hcoh : Sat fmapEmpty σ₀ (union m₀ R))
    (n : Nat) (aids : Nat → Nat)
    (hfuel : 6 + n ≤ lemDefaultFuel) :
    let prog := trProg loc ann mo xbty ybty bbty ubty px
    (∀ r, drive aids n (spikeThread prog) σ₀ ≠ .killed r) ∧
    (drive aids n (spikeThread prog) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      drive aids n (spikeThread prog) σ₀ = .done v σ' →
      ∃ (py : CerbMem.PointerValue) (Q : CellMap),
        v = ptrVal py ∧
        SeedTree Q py (.node idy vy ta (.node idx vx tb tc)) ∧
        (∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome) ∧
        Q ##ₘ R ∧
        Sat fmapEmpty σ' (union Q R)) := by
  intro prog
  have h := spike_engine_adequacy (GF := SpikeGF)
    prog σ₀ (union m₀ R)
    (trProg_frag loc ann mo xbty ybty bbty ubty px hlib) hcoh
    (fun v σ' => ∃ Q : CellMap, (∃ p' : CerbMem.PointerValue,
        v = ptrVal p' ∧
        SeedTree Q p' (.node idy vy ta (.node idx vx tb tc))) ∧
      Q ##ₘ R ∧ Coh fmapEmpty σ' (union Q R))
    (by
      intro inst
      refine ((BigSepM.bigSepM_union hR).1.trans
        (BI.sep_mono (seedTree_isTree _ m₀ px hseed) .rfl)).trans ?_
      exact tr_wp_readout loc ann mo xbty ybty bbty ubty
        idx idy vx vy ta tb tc px R)
    n aids
    (by rw [trProg_esize]; exact hfuel)
  refine ⟨h.1, h.2.1, fun v σ' hdone => ?_⟩
  obtain ⟨Q, ⟨py, rfl, hQseed⟩, hdisj, hsat⟩ := h.2.2 v σ' hdone
  refine ⟨py, Q, rfl, hQseed, fun k => ?_, hdisj, hsat⟩
  rw [SeedTree.footprint _ Q py hQseed k,
    SeedTree.footprint _ m₀ px hseed k]
  exact rotate_ids_mem idx idy vx vy ta tb tc k

end TrDrive

/-! ## THE TOTAL LANE: the same textbook derivation at the total
judgment — straight-line, so the budget is the CONSTANT 19
(1 x-bind + 4 + 4 per load + 4 + 4 per store + 2 exit). -/

section TrTotal

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {Ls : LabelSpecT GF}
variable (loc : CerbLocation.Loc) (ann : core_run_annotation)
  (mo : memory_order) (xbty ybty bbty ubty : core_base_type)

/-- The rotation meets the constant budget 19 (UNFRAMED; the frame by
    `tree_rotate_wpt_frame`). -/
theorem tree_rotate_wpt
    (idx idy vx vy : Int) (ta tb tc : NodeTree)
    (px : CerbMem.PointerValue) :
    isTree (GF := GF) px (.node idx vx (.node idy vy ta tb) tc) ⊢
      wpt spikeCtx Ls 19
        (trPost (.node idy vy ta (.node idx vx tb tc)))
        (trProg loc ann mo xbty ybty bbty ubty px)
        [fmapEmpty] := by
  iintro HX
  rw [isTree_node]
  icases HX with ⟨%aX, %qL, %qR, %bsx, %hfx, HptX, HY, Hc⟩
  obtain ⟨rfl, h0x, h1x, hlenx, hvalx, hLx, hRx⟩ := hfx
  rw [isTree_node]
  icases HY with ⟨%aY, %qa, %qb, %bsy, %hfy, HptY, Ha, Hb⟩
  obtain ⟨rfl, h0y, h1y, hleny, hvaly, hLy, hRy⟩ := hfy
  ihave Hb2 := isTree_shape qb tb $$ Hb
  icases Hb2 with ⟨%hshapeb, Hb⟩
  have kitB := tree_store_kit (tds := fmapEmpty) qb hshapeb
  obtain ⟨kBlen, kBfpm, kBbytes, kBdec⟩ := kitB
  have kitX := tree_store_kit (tds := fmapEmpty) (cellPtr idx aX)
    (.inr ⟨idx, aX, rfl, h0x, h1x⟩)
  obtain ⟨kXlen, kXfpm, kXbytes, kXdec⟩ := kitX
  rw [show trProg loc ann mo xbty ybty bbty ubty (cellPtr idx aX) =
    Expr [] (Esseq (symPat [] trXSym xbty)
      (Expr [] (Epure (Pexpr [] () (PEval (ptrVal (cellPtr idx aX))))))
      (trRest loc ann mo ybty bbty ubty)) from rfl,
    show (19 : Nat) = 1 + 18 from rfl]
  iapply wpt_seq_sym
  rw [show Expr ([] : List annot)
      (Epure (Pexpr [] () (PEval (ptrVal (cellPtr idx aX))))) =
    ofVal (.pure (ptrVal (cellPtr idx aX))) from rfl]
  iapply wpt_ofVal (.pure (ptrVal (cellPtr idx aX))) [fmapEmpty]
    (by simp [deliveryCost])
  iexists (ptrVal (cellPtr idx aX))
  isplit
  · ipureintro
    rfl
  rw [trBindX]
  rw [show trRest loc ann mo ybty bbty ubty =
    Expr [] (Esseq (specPat [] [] trYSym ybty)
      (loadOpRedex loc ann treePtrTy (trShift1 trXSym) mo)
      (Expr [] (Esseq (specPat [] [] trBSym bbty)
        (loadOpRedex loc ann treePtrTy (trShift2 trYSym) mo)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (storeOpRedex loc ann treePtrTy (trShift1 trXSym)
            (Pexpr [] () (PEsym trBSym)) mo)
          (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
            (storeOpRedex loc ann treePtrTy (trShift2 trYSym)
              (Pexpr [] () (PEsym trXSym)) mo)
            (Expr [] (Epure (Pexpr [] () (PEsym trYSym))))))))))) from rfl,
    show (18 : Nat) = 4 + 14 from rfl]
  iapply wpt_seq_spec
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval loc ann treePtrTy (trShift1 trXSym) mo _
    rfl (tr_shift1_eval_F1 idx aX)
  rw [show cellPtr idx (aX + 8) = cellPtr idx (aX + ((8 : Nat) : Int))
    from rfl]
  iapply wpt_load_tree_field (M := spikeCtx) loc ann idx aX 8 mo (.own 1) bsx _
    (by omega) (by rw [treeTy_size]; omega)
    (fun lum fpm => hLx lum fpm _)
  isplitl [HptX]
  · iexact HptX
  iintro %fp1 HptX
  iexists (OVpointer (cellPtr idy aY))
  isplit
  · ipureintro
    show (valueFromMemValue (.MVpointer treeTy (cellPtr idy aY))).2 = _
    rw [valueFromMemValue_ptr]
  rw [trBindY]
  rw [show trF2 (Vobject (OVpointer (cellPtr idy aY)))
        (ptrVal (cellPtr idx aX)) =
      trF2 (ptrVal (cellPtr idy aY)) (ptrVal (cellPtr idx aX)) from rfl]
  rw [show (14 : Nat) = 4 + 10 from rfl]
  iapply wpt_seq_spec
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_load_eval loc ann treePtrTy (trShift2 trYSym) mo _
    rfl (tr_shift2_eval_F2 idy aY _)
  rw [show cellPtr idy (aY + 16) = cellPtr idy (aY + ((16 : Nat) : Int))
    from rfl]
  iapply wpt_load_tree_field (M := spikeCtx) loc ann idy aY 16 mo (.own 1) bsy _
    (by omega) (by rw [treeTy_size]; omega)
    (fun lum fpm => hRy lum fpm _)
  isplitl [HptY]
  · iexact HptY
  iintro %fp2 HptY
  iexists (OVpointer qb)
  isplit
  · ipureintro
    show (valueFromMemValue (.MVpointer treeTy qb)).2 = _
    rw [valueFromMemValue_ptr]
  rw [trBindB]
  rw [show trF3 (Vobject (OVpointer qb)) (ptrVal (cellPtr idy aY))
        (ptrVal (cellPtr idx aX)) =
      trF3 (ptrVal qb) (ptrVal (cellPtr idy aY))
        (ptrVal (cellPtr idx aX)) from rfl]
  rw [show (10 : Nat) = 4 + 6 from rfl]
  iapply wpt_seq
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval loc ann treePtrTy _ _ mo _
    rfl (tr_shift1_eval_F3 _ _ idx aX)
    (tr_b_eval_F3 _ _ _)
  rw [show cellPtr idx (aX + 8) = cellPtr idx (aX + ((8 : Nat) : Int))
    from rfl]
  iapply wpt_store_tree_field (M := spikeCtx) loc ann idx aX 8 (ptrVal qb) mo bsx _
    (by omega)
    (tree_ptr_encodes qb) (by rw [treeTy_size]; omega) kBlen
    (tree_ptr_compat qb) kBfpm kBbytes
  isplitl [HptX]
  · iexact HptX
  iintro %fp3 HptX
  rw [show (6 : Nat) = 4 + 2 from rfl]
  iapply wpt_seq
  rw [show (4 : Nat) = 3 + 1 from rfl]
  iapply wpt_store_eval loc ann treePtrTy _ _ mo _
    rfl (tr_shift2_eval_F3 _ _ idy aY)
    (tr_x_eval_F3 _ _ _)
  rw [show cellPtr idy (aY + 16) = cellPtr idy (aY + ((16 : Nat) : Int))
    from rfl]
  iapply wpt_store_tree_field (M := spikeCtx) loc ann idy aY 16 (ptrVal (cellPtr idx aX))
    mo bsy _
    (by omega)
    (tree_ptr_encodes (cellPtr idx aX)) (by rw [treeTy_size]; omega) kXlen
    (tree_ptr_compat (cellPtr idx aX)) kXfpm kXbytes
  isplitl [HptY]
  · iexact HptY
  iintro %fp4 HptY
  iapply wpt_pure (Pexpr [] () (PEsym trYSym)) _ (by omega) rfl
    (tr_y_eval_F3 _ _ _)
  iexists (cellPtr idy aY)
  isplit
  · ipureintro
    rfl
  · iapply isTree_node_intro idy aY qa (cellPtr idx aX)
      (spliceBytes 16 (CerbMem.memValueToBytes spikeCtx.tagDefs []
        (CerbMem.pointerMval treeTy (cellPtr idx aX))).2 bsy)
      vy ta (.node idx vx tb tc) h0y h1y
      (by rw [spliceBytes_length _ _ _ (by rw [kXlen, hleny]; omega)]
          exact hleny)
      (by intro lum fpm ad
          rw [show ((spliceBytes 16 (CerbMem.memValueToBytes spikeCtx.tagDefs []
              (CerbMem.pointerMval treeTy (cellPtr idx aX))).2 bsy).drop
                0).take 8 =
            (bsy.drop 0).take 8 from trSplice16_val _ bsy kXlen hleny]
          exact hvaly lum fpm ad)
      (by intro lum fpm ad
          rw [show ((spliceBytes 16 (CerbMem.memValueToBytes spikeCtx.tagDefs []
              (CerbMem.pointerMval treeTy (cellPtr idx aX))).2 bsy).drop
                8).take 8 =
            (bsy.drop 8).take 8 from trSplice16_left _ bsy kXlen hleny]
          exact hLy lum fpm ad)
      (kXdec _ 16 (trSplice16_self _ bsy kXlen hleny))
    isplitl [HptY]
    · iexact HptY
    isplitl [Ha]
    · iexact Ha
    · iapply isTree_node_intro idx aX qb qR
        (spliceBytes 8 (CerbMem.memValueToBytes spikeCtx.tagDefs []
          (CerbMem.pointerMval treeTy qb)).2 bsx)
        vx tb tc h0x h1x
        (by rw [spliceBytes_length _ _ _ (by rw [kBlen, hlenx]; omega)]
            exact hlenx)
        (by intro lum fpm ad
            rw [show ((spliceBytes 8 (CerbMem.memValueToBytes spikeCtx.tagDefs []
                (CerbMem.pointerMval treeTy qb)).2 bsx).drop 0).take 8 =
              (bsx.drop 0).take 8 from trSplice8_val _ bsx kBlen hlenx]
            exact hvalx lum fpm ad)
        (kBdec _ 8 (trSplice8_self _ bsx kBlen hlenx))
        (by intro lum fpm ad
            rw [show ((spliceBytes 8 (CerbMem.memValueToBytes spikeCtx.tagDefs []
                (CerbMem.pointerMval treeTy qb)).2 bsx).drop 16).take 8 =
              (bsx.drop 16).take 8 from trSplice8_right _ bsx kBlen hlenx]
            exact hRx lum fpm ad)
      isplitl [HptX]
      · iexact HptX
      isplitl [Hb]
      · iexact Hb
      · iexact Hc

/-- The framed total judgment, by the generic `wpt_frame` (value
    channel; straight-line). -/
theorem tree_rotate_wpt_frame (RF : IProp GF)
    (idx idy vx vy : Int) (ta tb tc : NodeTree)
    (px : CerbMem.PointerValue) :
    iprop(isTree (GF := GF) px
        (.node idx vx (.node idy vy ta tb) tc) ∗ RF) ⊢
      wpt spikeCtx Ls 19
        (fun w ρ' => iprop(trPost (.node idy vy ta (.node idx vx tb tc)) w ρ' ∗ RF))
        (trProg loc ann mo xbty ybty bbty ubty px)
        [fmapEmpty] :=
  (BI.sep_mono (tree_rotate_wpt (Ls := Ls) loc ann mo xbty ybty bbty ubty
    idx idy vx vy ta tb tc px) .rfl).trans (wpt_frame RF _ _ _)

end TrTotal

section TrTotalExport

open Iris.Std.PartialMap

variable (loc : CerbLocation.Loc) (ann : core_run_annotation)
  (mo : memory_order) (xbty ybty bbty ubty : core_base_type)

theorem trProg_pot (px : CerbMem.PointerValue) :
    pot (trProg loc ann mo xbty ybty bbty ubty px) ≤ lemDefaultFuel := by
  rw [show pot (trProg loc ann mo xbty ybty bbty ubty px) = 7 from rfl,
    show lemDefaultFuel = 999999 + 1 from rfl]
  omega

/-- TREE ROTATION, THE UNCONDITIONAL TOTAL ENGINE EQUATION: the
    engine's drive at the constant fuel 19 DELIVERS the rotated
    tree — same allocations, frame verbatim, no fuel hypotheses, no
    partiality. Straight-line totality through the same generic
    simulation the loops use. -/
theorem tree_rotate_certified_total (idx idy vx vy : Int)
    (ta tb tc : NodeTree) (px : CerbMem.PointerValue)
    (m₀ : CellMap)
    (hseed : SeedTree m₀ px (.node idx vx (.node idy vy ta tb) tc))
    (R : CellMap) (hR : m₀ ##ₘ R)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem) (hcoh : Sat fmapEmpty σ₀ (union m₀ R)) (aids : Nat → Nat) :
    ∃ (py : CerbMem.PointerValue) (Q : CellMap) (σ' : Mem),
      drive aids 19
        (spikeThread (trProg loc ann mo xbty ybty bbty ubty px)) σ₀ =
          .done (ptrVal py) σ' ∧
      SeedTree Q py (.node idy vy ta (.node idx vx tb tc)) ∧
      (∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome) ∧
      Q ##ₘ R ∧
      Sat fmapEmpty σ' (union Q R) := by
  obtain ⟨v, σ', hdone, ⟨Q, ⟨py, rfl, hQseed⟩, hdisj, hsat⟩, -⟩ :=
    wpt_engine_boundU (GF := SpikeGF) (M := spikeCtx) spikeCtx_wf
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun _ _ _ _ => iprop(False))
      (trProg loc ann mo xbty ybty bbty ubty px)
      fmapEmpty [] σ₀ (union m₀ R)
      (trProg_frag loc ann mo xbty ybty bbty ubty px hlib)
      (trProg_pot loc ann mo xbty ybty bbty ubty px)
      hcoh
      (fun v σ' => ∃ Q : CellMap, (∃ p' : CerbMem.PointerValue,
          v = ptrVal p' ∧
          SeedTree Q p' (.node idy vy ta (.node idx vx tb tc))) ∧
        Q ##ₘ R ∧ Coh fmapEmpty σ' (union Q R))
      19
      (by
        intro inst
        refine ((BigSepM.bigSepM_union hR).1.trans
          (BI.sep_mono (seedTree_isTree _ m₀ px hseed) .rfl)).trans ?_
        refine .trans BI.emp_sep.2 (BI.sep_mono ?_ ?_)
        · exact (blockSpecsT_intro fun l _ _ _ _ _ _ hl =>
            (spikeCtx_labels_none l hl).elim)
        · exact (tree_rotate_wpt_frame (Ls := fun _ _ _ _ => iprop(False))
              loc ann mo xbty ybty bbty ubty (lrCellFrame R)
              idx idy vx vy ta tb tc px).trans
            (wpt_mono (trPost_readout
              (NodeTree.node idy vy ta (NodeTree.node idx vx tb tc)) R)
              _ _ _))
      aids
  refine ⟨py, Q, σ', hdone, hQseed, fun k => ?_, hdisj, hsat⟩
  rw [SeedTree.footprint _ Q py hQseed k,
    SeedTree.footprint _ m₀ px hseed k]
  exact rotate_ids_mem idx idy vx vy ta tb tc k

end TrTotalExport

/-! ## Satisfiability witness (the demo-seed discipline: the
hypotheses of the exported theorems are exhibitable, so the general
theorems are not vacuously true) -/

/-- A concrete 2-node tree: root (id 1, value 10) with left child
    (id 2, value 20); engine-serialized byte images, every decode
    fact `rfl`. -/
def trDemoBytesRoot : List CerbMem.AbsByte :=
  valImg 10 ++ trPtrImg (cellPtr 2 8192) ++ trPtrImg nullTree

def trDemoBytesLeft : List CerbMem.AbsByte :=
  valImg 20 ++ trPtrImg nullTree ++ trPtrImg nullTree

def trDemoT : NodeTree := .node 1 10 (.node 2 20 .leaf .leaf) .leaf

open Iris.Std.PartialMap in
def trDemoM : CellMap :=
  union (singleton 1 (SpikeCell.mk 4096 treeTy trDemoBytesRoot))
    (union
      (union (singleton 2 (SpikeCell.mk 8192 treeTy trDemoBytesLeft))
        (union (∅ : CellMap) (∅ : CellMap)))
      (∅ : CellMap))

open Iris.Std.PartialMap in
theorem trDemo_seed : SeedTree trDemoM (cellPtr 1 4096) trDemoT := by
  refine ⟨4096, cellPtr 2 8192, nullTree, trDemoBytesRoot,
    union (singleton 2 (SpikeCell.mk 8192 treeTy trDemoBytesLeft))
      (union (∅ : CellMap) (∅ : CellMap)), (∅ : CellMap),
    rfl, by omega, by omega, rfl,
    (fun lum fpm ad => rfl), (fun lum fpm ad => rfl),
    (fun lum fpm ad => rfl), ?_, ?_, rfl, ?_, ⟨rfl, rfl⟩⟩
  · intro k hk
    obtain ⟨h1, h2⟩ := hk
    have hk1 : k = 1 := by
      by_cases h : (1 : Int) = k
      · omega
      · rw [Iris.Std.LawfulPartialMap.get?_singleton_ne h] at h1
        cases h1
    subst hk1
    rw [get?_union', get?_union',
      Iris.Std.LawfulPartialMap.get?_singleton_ne (by omega),
      get?_union',
      Iris.Std.LawfulPartialMap.get?_empty] at h2
    cases h2
  · intro k hk
    obtain ⟨h1, h2⟩ := hk
    rw [Iris.Std.LawfulPartialMap.get?_empty] at h2
    cases h2
  · refine ⟨8192, nullTree, nullTree, trDemoBytesLeft, (∅ : CellMap),
      (∅ : CellMap),
      rfl, by omega, by omega, rfl,
      (fun lum fpm ad => rfl), (fun lum fpm ad => rfl),
      (fun lum fpm ad => rfl), ?_, ?_, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · intro k hk
      obtain ⟨h1, h2⟩ := hk
      rw [get?_union', Iris.Std.LawfulPartialMap.get?_empty] at h2
      cases h2
    · intro k hk
      obtain ⟨h1, h2⟩ := hk
      rw [Iris.Std.LawfulPartialMap.get?_empty] at h2
      cases h2

end CerberusHeapLang
