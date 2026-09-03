/-
CerberusHeapLang.ListRevExhibit — THE CANONICAL EXHIBIT: in-place
linked-list reversal, the flagship demonstration of the
Reynolds/O'Hearn tradition on the real engine.

THE PROGRAM (authored Core, in-place reversal — the classic
three-pointer loop):

    save loop: (prev : ptr := NULL(node), cur : ptr := head) in
      lets b = memop(PtrEq, [cur, NULL(node)]) in
      if b then pure(prev)
      else
        lets Specified(n) = load(node*, array_shift(cur, long, 1)) in
        lets _ = store(node*, array_shift(cur, long, 1), prev) in
        run loop(cur, n)

THE NODE (the [USER 2026-08-31] one-allocation ruling — see
ArrayExhibit.lean's provenance forcing fact — extended to nodes):
ONE allocation per node, TWO long-width fields inside it — the value
at offset 0, the next pointer at offset 8 (= the engine's own
`targetPtrSize`, CerbMem.lean:253; LP64 `sizeof(long) = 8`). The
node's allocation type is `array of 2 signed longs` (`nodeTy`), so
intra-node field access is ARITHMETIC WITHIN THE ALLOCATION
(`array_shift(cur, long, 1)` — provenance preserved,
`arrayShiftPtrval`, CerbMem.lean:1127-1142), while inter-node
traversal is by LOADED pointers, each reconstructed from its own
stored bytes WITH ITS OWN PROVENANCE (`splitBytesProv`,
CerbMem.lean:517 — the pointer-load provenance policy).

THE NULL ENCODING (honest, the engine's): the null pointer is
`nullPtrval nodeTy = PV Prov_none (PVnull nodeTy)` (CerbMem.lean:843).
A stored null serializes to eight ZERO bytes at Prov_none with no
copy offsets (repr, CerbMem.lean:581-585 / impl_mem.ml:1165-1167)
and a pointer-typed load of those bytes reconstructs exactly
`PV Prov_none (PVnull pointee)` (abst's `some 0` arm,
CerbMem.lean:688-692 / impl_mem.ml:1005-1019) — the round trip is a
theorem here (`nodeNextDec_null_img`). The null TEST is the engine's
own `PtrEq` memop (Step.lean `Step.memop_ptreq`; the eqPtrval null
arms, Heap.lean).

THE PREDICATE `isList p ns` (foundations Phase 4, audit F-06 — the
IDENTITY-INDEXED form): plain structural recursion on the list of
NODES `ns : List (Int × Int)` — each node is its ALLOCATION ID (the
phase-2 metadata heap's authority: the exclusivity anchor
`allocateObject` mints) paired with its value; one ∗-composed ghost
cell per node; the nil case ties to the null encoding; the cons case
∃-binds the next pointer with the node's cell ∗ the tail.
Machine-address WF (`0 < a < 2^64`) is carried per node — real
addresses (what `allocateObject` mints and what the 8-byte
serialization round-trips).

THE PROOF: textbook-compositional — `blockSpecs_intro` with the
invariant `isList prev reversed ∗ isList cur rest` and
`ns = reversed.reverse ++ rest` (UNFRAMED — alloc arc P4.2: an
arbitrary frame is added afterwards by the generic statement frame
rule `wps_frame_labels`/`blockSpecs_frame`, which carries it across
every back edge through the framed label context `frameLs`),
each program construct discharged by its small axiom or rule
(`wps_seq_sym` + `wps_memop_eval` + `wps_memop_ptreq`, `wps_if_*`,
`wps_seq_spec` + `wps_load_eval` + the node-field load client rule,
`wps_seq` + `wps_store_eval` + the node-field STORE client rule,
`wps_run`); no monolithic unfolding.

THE FLAGSHIP (Phase 4 statement — audit F-06's exit criterion
verbatim: "the public theorem literally states same-footprint,
in-place reversal plus termination and frame preservation"):
`list_reverse_certified` (partial, any budget) and
`list_reverse_certified_total` (unconditional `.done` at the DERIVED
bound `13·|ns| + 7`). Both flagships are stated with the `SemTripleU`
rest-quantifier shape at the proc-carrying context:
an ARBITRARY disjoint frame footprint `R` rides next to the seeded
chain `m₀` and is returned VERBATIM (`Sat σ' (Q ∪ R)`); the
delivered pointer heads a chain `SeedChain Q p' ns.reverse` — the
SAME allocation ids, in exactly reversed order, each node still
carrying its own value (in-place in the literal sense: only the
next fields moved); and the footprint equality
`∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome` is a stated conjunct
(no allocation, no leak — the node set is preserved; the id list
`ns.reverse.map .1` is by construction a permutation — the reversal
— of `ns.map .1`). Statements are SpikeGF-concrete: no ghost-functor
binder (the census's one machinery-shaped hypothesis) remains on any
flagship. The 2026-08-31 pre-Phase-4 forms (values-only `ChainAt`
conclusion, no identity, no frame) are RETIRED — subsumed, see
docs/2026-09-01_phase4-notes.md for the old→new itemization; the
id-indexed `ChainAt` remains as demoted corollary vocabulary
(`seedChain_chainAt`, consumed by the demo).
-/
import CerberusHeapLang.ArrayExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## The node layout (LP64, the engine's own sizes) -/

/-- `signed long` — the node field width (8 bytes in LP64,
    CerberusImpl.sizeof_ity). -/
def longTy : ctype := Ctype [] (.Basic (.Integer (.Signed .Long)))

/-- The node type: ONE allocation, two long-width fields
    (`long[2]`) — value at offset 0, next pointer at offset 8. -/
def nodeTy : ctype := Ctype [] (.Array0 longTy (some 2))

/-- Pointer-to-node — the type every next-field load/store uses. -/
def nodePtrTy : ctype := Ctype [] (.Pointer no_qualifiers nodeTy)

/-- THE NULL: the engine's null pointer at the node type
    (CerbMem.lean:843). -/
def nullNode : CerbMem.PointerValue := CerbMem.nullPtrval nodeTy

theorem longTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds longTy = 8 := rfl
theorem nodeTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds nodeTy = 16 := rfl

/-- The node type has positive size (the public create rules' `hsz`). -/
theorem nodeTy_size_pos {tds : CerbTags.TagDefsMap} : 0 < CerbMem.sizeofCtype tds nodeTy := by
  rw [nodeTy_size]
  decide
theorem nodePtrTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds nodePtrTy = 8 := rfl

/-- One long-element shift of a fragment pointer — the ENGINE's own
    arithmetic (`arrayShiftPtrval` at the concrete shape: provenance
    PRESERVED, address advanced by `sizeof(long) = 8`). -/
theorem arrayShift_cellPtr_long {tds : CerbTags.TagDefsMap} (id p : Int) :
    CerbMem.arrayShiftPtrval tds (cellPtr id p) longTy (CerbMem.integerIval 1) =
      cellPtr id (p + 8) := by
  rw [cellPtr_arrayShift tds id p longTy 1 (fun _ h => by unfold longTy at h; cases h),
    longTy_size]
  exact congrArg (cellPtr id) (by omega)

theorem evalArrayShift_long_one (id a : Int) :
    evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id a))) (ivVal 1) =
      some (Vobject (OVpointer (cellPtr id (a + 8)))) := by
  show some (Vobject (OVpointer (CerbMem.arrayShiftPtrval fmapEmpty (cellPtr id a)
    longTy (CerbMem.integerIval 1)))) = _
  rw [arrayShift_cellPtr_long]

/-! ## The stored pointer images (the engine's own serialization,
repr — CerbMem.lean:578-603) and their decode round trips -/

/-- The serialized image of a stored value, at the empty funptrmap
    (the fragment's stores are funptrmap-neutral). -/
def imgOf (tds : CerbTags.TagDefsMap) (mv : CerbMem.MemValue) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] mv).2

/-- The stored NEXT images: a concrete node pointer / the null. -/
def ptrImg (pv : CerbMem.PointerValue) : List CerbMem.AbsByte :=
  imgOf fmapEmpty (CerbMem.pointerMval nodeTy pv)

theorem ptrImg_cell (id a : Int) :
    ptrImg (cellPtr id a) =
      ((CerbMem.intToBytes a 8).zip
        (List.range (CerbMem.intToBytes a 8).length)).map
        (fun (v, i) =>
          { prov := .Prov_some id, copyOffset := some (i : Int), value := v }) := rfl

theorem ptrImg_cell_length (id a : Int) : (ptrImg (cellPtr id a)).length = 8 := by
  rw [ptrImg_cell]
  simp [intToBytes_length]

theorem ptrImg_null_length : (ptrImg nullNode).length = 8 := rfl

/-! ## Phase 2 (F-04): the per-layout interior memM seams and the
byte-splice machinery formerly here are RETIRED/moved — the generic
typed-subrange seams (`loadM_at`/`storeM_at`) and the splice algebra
(`spliceBytes*`, `readBytesFrom_write_interior`, `Coh.store_interior`)
live in Heap.lean; the node-field WPS rules below are CLIENT
instances of the generic `wps_load_cell_at`/`wps_store_cell_at`. -/

/-! ## Decode round trips (the engine's own abst,
CerbMem.lean:677-708) -/

/-- The serialized concrete-pointer image, spelled byte by byte. -/
theorem ptrImg_cell_explicit (id a : Int) (h0 : 0 ≤ a) :
    ptrImg (cellPtr id a) =
      [⟨.Prov_some id, some 0, some ((a >>> ((0 * 8 : Nat))).toNat % 256).toUInt8⟩,
       ⟨.Prov_some id, some 1, some ((a >>> ((1 * 8 : Nat))).toNat % 256).toUInt8⟩,
       ⟨.Prov_some id, some 2, some ((a >>> ((2 * 8 : Nat))).toNat % 256).toUInt8⟩,
       ⟨.Prov_some id, some 3, some ((a >>> ((3 * 8 : Nat))).toNat % 256).toUInt8⟩,
       ⟨.Prov_some id, some 4, some ((a >>> ((4 * 8 : Nat))).toNat % 256).toUInt8⟩,
       ⟨.Prov_some id, some 5, some ((a >>> ((5 * 8 : Nat))).toNat % 256).toUInt8⟩,
       ⟨.Prov_some id, some 6, some ((a >>> ((6 * 8 : Nat))).toNat % 256).toUInt8⟩,
       ⟨.Prov_some id, some 7, some ((a >>> ((7 * 8 : Nat))).toNat % 256).toUInt8⟩] := by
  rw [ptrImg_cell, intToBytes_nonneg a 8 h0]
  simp only [List.length_map, List.length_range]
  simp [List.range_succ]

/-- The 8-byte little-endian round trip on machine addresses. -/
theorem bytesToInt_ptrImg_cell (id a : Int) (h0 : 0 ≤ a) (h1 : a < 2 ^ 64) :
    CerbMem.bytesToInt (ptrImg (cellPtr id a)) false = some a := by
  rw [ptrImg_cell_explicit id a h0, bytesToInt_of_all_some _ (by rfl)]
  simp only [bytesToInt_go_cons, bytesToInt_go_nil]
  congr 1
  obtain ⟨A, rfl⟩ : ∃ A : Nat, a = (A : Int) := ⟨a.toNat, by omega⟩
  simp only [Int.shiftLeft_eq]
  simp only [Nat.reduceMul, Int.reducePow]
  have h64 : A < 72057594037927936 * 256 := by
    have h2 : (2 : Nat) ^ 64 = 72057594037927936 * 256 := rfl
    omega
  show 0 + (((A >>> (0*8)) % 256 % 256 : Nat) : Int) * 1 +
      (((A >>> (1*8)) % 256 % 256 : Nat) : Int) * 256 +
      (((A >>> (2*8)) % 256 % 256 : Nat) : Int) * 65536 +
      (((A >>> (3*8)) % 256 % 256 : Nat) : Int) * 16777216 +
      (((A >>> (4*8)) % 256 % 256 : Nat) : Int) * 4294967296 +
      (((A >>> (5*8)) % 256 % 256 : Nat) : Int) * 1099511627776 +
      (((A >>> (6*8)) % 256 % 256 : Nat) : Int) * 281474976710656 +
      (((A >>> (7*8)) % 256 % 256 : Nat) : Int) * 72057594037927936 =
      ((A : Nat) : Int)
  simp only [Nat.shiftRight_eq_div_pow]
  rw [show (2:Nat) ^ (0 * 8) = 1 from rfl, show (2:Nat) ^ (1 * 8) = 256 from rfl,
    show (2:Nat) ^ (2 * 8) = 65536 from rfl,
    show (2:Nat) ^ (3 * 8) = 16777216 from rfl,
    show (2:Nat) ^ (4 * 8) = 4294967296 from rfl,
    show (2:Nat) ^ (5 * 8) = 1099511627776 from rfl,
    show (2:Nat) ^ (6 * 8) = 281474976710656 from rfl,
    show (2:Nat) ^ (7 * 8) = 72057594037927936 from rfl]
  omega

/-! ## The decode facts (abst on the fragment's images) -/

/-- The delivered value of a pointer mem-value (the load readout —
    Core_aux.valueFromMemValue's pointer arm). -/
theorem valueFromMemValue_ptr (t : ctype) (pv : CerbMem.PointerValue) :
    (valueFromMemValue (.MVpointer t pv)).2 =
      Vloaded (LVspecified (OVpointer pv)) := rfl

/-- THE NULL ROUND TRIP: a stored null (eight zero bytes at
    Prov_none — repr, CerbMem.lean:581-585) reloads at `node*` as
    exactly the null pointer (abst's `some 0` arm,
    CerbMem.lean:688-692). Table- and address-independent. -/
theorem reconstruct_ptrImg_null {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (addr : Int) :
    CerbMem.reconstructValue tds lum fpm addr nodePtrTy (ptrImg nullNode) =
      .MVpointer nodeTy nullNode := rfl

/-- The first-component of the pointer-load provenance policy at the
    stored concrete-pointer image: the bytes' SHARED provenance
    (splitBytesProv, CerbMem.lean:517). -/
theorem splitBytesProv_ptrImg_cell_fst (id a : Int) (h0 : 0 ≤ a) :
    (CerbMem.splitBytesProv (ptrImg (cellPtr id a))).1 =
      .Prov_some id := by
  rw [ptrImg_cell_explicit id a h0]
  unfold CerbMem.splitBytesProv
  simp [provenance_beq_refl]

/-- THE CONCRETE-POINTER ROUND TRIP: a stored node pointer reloads
    at `node*` as exactly itself — same address (the 8-byte
    little-endian round trip), same provenance (the shared-provenance
    policy: LOADED POINTERS CARRY THEIR OWN PROVENANCE). Machine-
    address WF (`0 < a < 2^64`) is the honest premise: these are the
    addresses `allocateObject` mints. -/
theorem reconstruct_ptrImg_cell {tds : CerbTags.TagDefsMap} (id a : Int) (h0 : 0 < a) (h1 : a < 2 ^ 64)
    (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (addr : Int) :
    CerbMem.reconstructValue tds lum fpm addr nodePtrTy (ptrImg (cellPtr id a)) =
      .MVpointer nodeTy (cellPtr id a) := by
  have hb := bytesToInt_ptrImg_cell id a (by omega) h1
  have hsp := splitBytesProv_ptrImg_cell_fst id a (by omega)
  rw [show CerbMem.reconstructValue =
    CerbMem.reconstructValue_lemFuel lemDefaultFuel from rfl,
    show lemDefaultFuel = 999999 + 1 from rfl]
  unfold CerbMem.reconstructValue_lemFuel nodePtrTy nodeTy
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

/-! ## Splice slices — LAYOUT INSTANCES of the generic splice algebra
(Heap.lean `spliceBytes_slice_below`/`_self`) at the node layout. -/

theorem spliceBytes_value_slice (img bs : List CerbMem.AbsByte)
    (himg : img.length = 8) (hbs : bs.length = 16) :
    ((spliceBytes 8 img bs).drop 0).take 8 = (bs.drop 0).take 8 :=
  spliceBytes_slice_below 8 img bs (by omega) 0 8 (by omega)

theorem spliceBytes_next_slice (img bs : List CerbMem.AbsByte)
    (himg : img.length = 8) (hbs : bs.length = 16) :
    ((spliceBytes 8 img bs).drop 8).take 8 = img := by
  have h := spliceBytes_slice_self 8 img bs (by omega)
  rw [himg] at h
  exact h

/-- The node type's decode is TABLE-INDEPENDENT for any bytes: the
    `long[2]` decode is an array of integer decodes, and the integer
    arm never consults the union-member or function-pointer tables
    (reconstructValue, CerbMem.lean:652 — the tables enter only union
    and pointer-to-function arms). -/
theorem nodeTy_dec_indep {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (addr : Int) (bs : List CerbMem.AbsByte) :
    CerbMem.reconstructValue tds lum fpm addr nodeTy bs =
      CerbMem.reconstructValue tds [] [] addr nodeTy bs := rfl

/-! ## The node-field access rules — CLIENT INSTANCES of the generic
typed-subrange rules (F-04: no WP/WPS lifting proof lives in this
module; the layout enters only through `nodeTy`/`nodePtrTy` sizes,
the field offset, and the decode facts). -/

section NodeClients

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}

/-- NODE `node*`-FIELD LOAD — `wps_load_cell_at` at view type
    `nodePtrTy` (the old example-local lifting rule, re-derived as a
    one-line client). -/
theorem wps_load_node_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (mo : memory_order)
    (dq : DFrac) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {mv : CerbMem.MemValue}
    (hbound : off + 8 ≤ CerbMem.sizeofCtype M.tagDefs nodeTy)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      nodePtrTy ((bs.drop off).take 8) = mv) :
    iprop(cellOwn M.tagDefs (GF := GF) id dq (SpikeCell.mk a nodeTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id dq (SpikeCell.mk a nodeTy bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M p Ls Θ Ψ (loadExpr loc ann nodePtrTy (cellPtr id (a + (off : Int))) mo)
        ρ :=
  wps_load_cell_at loc ann id a nodeTy off nodePtrTy mo dq bs ρ
    (by rw [nodePtrTy_size]; exact hbound)
    (by rw [nodePtrTy_size]; exact hdec) rfl

/-- NODE `node*`-FIELD STORE — `wps_store_cell_at` at view type
    `nodePtrTy`; the spliced image's whole-cell inertness is
    `nodeTy_dec_indep` (any bytes), so the client owes only the
    serialization facts of the stored pointer. -/
theorem wps_store_node_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (cv : value) (mo : memory_order)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ nodePtrTy)) cv =
      some mv)
    (hbound : off + 8 ≤ CerbMem.sizeofCtype M.tagDefs nodeTy)
    (hlen : (CerbMem.memValueToBytes M.tagDefs [] mv).2.length = 8)
    (hcompat : CerbMem.ctypeMemCompatible nodePtrTy (CerbMem.typeofMval mv) =
      true)
    (hfpm : ∀ fpm, (CerbMem.memValueToBytes M.tagDefs fpm mv).1 = fpm)
    (hbytes : ∀ fpm, (CerbMem.memValueToBytes M.tagDefs fpm mv).2 =
      (CerbMem.memValueToBytes M.tagDefs [] mv).2) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a nodeTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a nodeTy
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M p Ls Θ Ψ (storeExpr loc ann nodePtrTy (cellPtr id (a + (off : Int)))
        cv mo) ρ :=
  wps_store_cell_at loc ann id a nodeTy off nodePtrTy cv mo bs ρ hmv
    (by rw [nodePtrTy_size]; exact hbound)
    ⟨hcompat, hfpm, hbytes, by rw [nodePtrTy_size]; exact hlen⟩
    (fun lum fpm => nodeTy_dec_indep lum fpm a _)

end NodeClients

/-! ## THE PREDICATE: `isList p ns` (structural recursion on the
IDENTITY-INDEXED node list — allocation id × value; ∗-composed node
cells; the nil case IS the null encoding) -/

/-- The value field's decode fact (offset 0, `signed long`). Pure,
    table- and address-independent (the integer arm reads neither). -/
def nodeValDec (tds : CerbTags.TagDefsMap) (bs : List CerbMem.AbsByte) (v : Int) : Prop :=
  ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (ad : Int),
    CerbMem.reconstructValue tds lum fpm ad longTy ((bs.drop 0).take 8) =
      .MVinteger (.Signed .Long) (CerbMem.integerIval v)

/-- The next field's decode fact (offset 8, `node*`). -/
def nodeNextDec (tds : CerbTags.TagDefsMap) (bs : List CerbMem.AbsByte) (q : CerbMem.PointerValue) : Prop :=
  ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (ad : Int),
    CerbMem.reconstructValue tds lum fpm ad nodePtrTy ((bs.drop 8).take 8) =
      .MVpointer nodeTy q

/-- The stored images' next-field decode facts (the round trips). -/
theorem nodeNextDec_ptrImg_cell (id a : Int) (h0 : 0 < a) (h1 : a < 2 ^ 64)
    (bs : List CerbMem.AbsByte) (himg : (bs.drop 8).take 8 = ptrImg (cellPtr id a)) :
    nodeNextDec fmapEmpty bs (cellPtr id a) := by
  intro lum fpm ad
  rw [himg]
  exact reconstruct_ptrImg_cell id a h0 h1 lum fpm ad

theorem nodeNextDec_ptrImg_null (bs : List CerbMem.AbsByte)
    (himg : (bs.drop 8).take 8 = ptrImg nullNode) :
    nodeNextDec fmapEmpty bs nullNode := by
  intro lum fpm ad
  rw [himg]
  exact reconstruct_ptrImg_null lum fpm ad

section IsList

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- THE REPRESENTATION PREDICATE, IDENTITY-INDEXED (Phase 4, audit
    F-06): the node list carries each node's ALLOCATION ID (`.1` —
    the metadata heap's authority) with its value (`.2`). Plain
    structural recursion; the nil case ties to the null encoding;
    the cons case ∃-binds the next pointer with the node's cell ∗
    the tail; machine-address WF per node. The head pointer's
    provenance id IS the head node's id — identity is pinned, not
    existential. -/
def isList : CerbMem.PointerValue → List (Int × Int) → IProp GF
  | p, [] => iprop(⌜p = nullNode⌝)
  | p, nd :: ns => iprop(∃ (aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr nd.1 aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
        nodeValDec fmapEmpty bs nd.2 ∧ nodeNextDec fmapEmpty bs q⌝ ∗
      cellOwn fmapEmpty nd.1 (.own 1) (SpikeCell.mk aN nodeTy bs) ∗ isList q ns)

@[simp] theorem isList_nil (p : CerbMem.PointerValue) :
    isList (GF := GF) p [] = iprop(⌜p = nullNode⌝) := rfl

theorem isList_cons (p : CerbMem.PointerValue) (nd : Int × Int)
    (ns : List (Int × Int)) :
    isList (GF := GF) p (nd :: ns) = iprop(∃ (aN : Int)
      (q : CerbMem.PointerValue) (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr nd.1 aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
        nodeValDec fmapEmpty bs nd.2 ∧ nodeNextDec fmapEmpty bs q⌝ ∗
      cellOwn fmapEmpty nd.1 (.own 1) (SpikeCell.mk aN nodeTy bs) ∗ isList q ns) := rfl

/-- Nil introduction. -/
theorem isList_nil_intro : ⊢ isList (GF := GF) nullNode [] := by
  rw [isList_nil]
  ipureintro
  rfl

/-- Cons introduction (the node's cell ∗ the tail). -/
theorem isList_cons_intro (id aN : Int) (q : CerbMem.PointerValue)
    (bs : List CerbMem.AbsByte) (v : Int) (ns : List (Int × Int))
    (h0 : 0 < aN) (h1 : aN < 2 ^ 64) (hlen : bs.length = 16)
    (hval : nodeValDec fmapEmpty bs v) (hnext : nodeNextDec fmapEmpty bs q) :
    iprop(cellOwn fmapEmpty (GF := GF) id (.own 1) (SpikeCell.mk aN nodeTy bs) ∗
        isList q ns) ⊢
      isList (cellPtr id aN) ((id, v) :: ns) := by
  rw [isList_cons]
  iintro ⟨Hpt, HL⟩
  iexists aN, q, bs
  isplit
  · ipureintro
    exact ⟨rfl, h0, h1, hlen, hval, hnext⟩
  isplitl [Hpt]
  · iexact Hpt
  · iexact HL

end IsList

/-! ## THE PROGRAM (authored Core) -/

def lrBSym : sym := Symbol "" 401 SD_None
def lrPrevSym : sym := Symbol "" 402 SD_None
def lrCurSym : sym := Symbol "" 403 SD_None
def lrNSym : sym := Symbol "" 404 SD_None
def lrLoopSym : sym := Symbol "" 405 SD_None
def lrProcSym : sym := Symbol "" 406 SD_None

/-- Pointer values as Core values. -/
def ptrVal (pv : CerbMem.PointerValue) : value := Vobject (OVpointer pv)

/-- THE NULL LITERAL the program tests against. -/
def nullVal : value := ptrVal nullNode

/-- The null test: `memop(PtrEq, [cur, NULL(node)])` — the engine's
    own pointer-equality memop. -/
def lrMemopE : CoreExpr :=
  memopRedex PtrEq [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEval nullVal)]

/-- The next-field address: `array_shift(s, long, 1)` — intra-node
    arithmetic (offset 8 within the node allocation). -/
def lrShiftPe (s : sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEarray_shift (Pexpr [] () (PEsym s)) longTy
    (Pexpr [] () (PEval (ivVal 1))))

/-- `load(node*, array_shift(cur, long, 1))` — n := cur->next. -/
def lrLoadE (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) : CoreExpr :=
  loadOpRedex loc ann nodePtrTy (lrShiftPe lrCurSym) mo

/-- `store(node*, array_shift(cur, long, 1), prev)` —
    cur->next := prev. -/
def lrStoreE (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) : CoreExpr :=
  storeOpRedex loc ann nodePtrTy (lrShiftPe lrCurSym)
    (Pexpr [] () (PEsym lrPrevSym)) mo

/-- The exit: `pure(prev)`. -/
def lrExitPe : generic_pexpr Unit sym := Pexpr [] () (PEsym lrPrevSym)

/-- The else branch: load next, store prev into the next field, jump
    with (cur, n). -/
def lrElse (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (nbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (specPat [] [] lrNSym nbty)
    (lrLoadE loc ann mo)
    (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
      (lrStoreE loc ann mo)
      (Expr [] (Erun ra lrLoopSym
        [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEsym lrNSym)])))))

/-- The registered loop body. -/
def lrBody (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (bbty nbty ubty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (symPat [] lrBSym bbty)
    lrMemopE
    (Expr [] (Eif (Pexpr [] () (PEsym lrBSym))
      (Expr [] (Epure lrExitPe))
      (lrElse loc ann ra mo nbty ubty))))

/-- The save-parameter list (`prev := NULL, cur := head`). -/
def lrParams (pbty cbty : core_base_type) (head : CerbMem.PointerValue) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(lrPrevSym, ((pbty, none), Pexpr [] () (PEval nullVal))),
   (lrCurSym, ((cbty, none), Pexpr [] () (PEval (ptrVal head))))]

/-- The whole program. -/
def lrProg (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (sbty pbty cbty bbty nbty ubty : core_base_type)
    (head : CerbMem.PointerValue) : CoreExpr :=
  Expr [] (Esave (lrLoopSym, sbty) (lrParams pbty cbty head)
    (lrBody loc ann ra mo bbty nbty ubty))

/-- The label map. -/
def lrQ (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (pbty cbty bbty nbty ubty : core_base_type) : LabelMap :=
  fmapAddBy symCmpL lrLoopSym
    ([(lrPrevSym, pbty), (lrCurSym, cbty)], lrBody loc ann ra mo bbty nbty ubty)
    fmapEmpty

/-- The run state carrying the two-level `labeled` tie. -/
def lrRS (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
    (mo : memory_order) (pbty cbty bbty nbty ubty : core_base_type) :
    core_run_state :=
  { spikeRunState with
      labeled := fmapAddBy symCmpL lrProcSym
        (lrQ loc ann ra mo pbty cbty bbty nbty ubty) fmapEmpty }

section LrFacts

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (pbty cbty bbty nbty ubty : core_base_type)

theorem lrQ_lookup :
    lookupLabel (lrQ loc ann ra mo pbty cbty bbty nbty ubty) lrLoopSym =
      some ([(lrPrevSym, pbty), (lrCurSym, cbty)],
        lrBody loc ann ra mo bbty nbty ubty) := by
  unfold lookupLabel lrQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem lrQ_inv {l : sym} {params : List (sym × core_base_type)}
    {cont : CoreExpr}
    (h : lookupLabel (lrQ loc ann ra mo pbty cbty bbty nbty ubty) l =
      some (params, cont)) :
    params = [(lrPrevSym, pbty), (lrCurSym, cbty)] ∧
      cont = lrBody loc ann ra mo bbty nbty ubty := by
  unfold lookupLabel lrQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem lrRS_labeledAt :
    LabeledAt (lrRS loc ann ra mo pbty cbty bbty nbty ubty) lrProcSym
      (lrQ loc ann ra mo pbty cbty bbty nbty ubty) := by
  unfold LabeledAt lrRS
  show fmapLookupBy _ _ (fmapAddBy symCmpL lrProcSym _ fmapEmpty) = _
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

end LrFacts

/-! ## Frames and lookups (SymFrame + the lookup law) -/

/-- The frame after the loop bindings (prev, cur). -/
def lrFrame (vp vc : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd lrCurSym vc (envAdd lrPrevSym vp f)

/-- ... after additionally binding the null-test boolean. -/
def lrFrameB (vb vp vc : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd lrBSym vb (lrFrame vp vc f)

/-- ... after additionally binding the loaded next pointer. -/
def lrFrameN (vn vb vp vc : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd lrNSym vn (lrFrameB vb vp vc f)

theorem lrFrame_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vp vc : value) : SymFrame (lrFrame vp vc f) :=
  (hf.add _ _).add _ _

theorem lrFrameB_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vb vp vc : value) : SymFrame (lrFrameB vb vp vc f) :=
  (lrFrame_symFrame hf _ _).add _ _

theorem lrFrameN_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vn vb vp vc : value) : SymFrame (lrFrameN vn vb vp vc f) :=
  (lrFrameB_symFrame hf _ _ _).add _ _

section LrLookups

variable {f : Fmap sym value} (hf : SymFrame f) (vn vb vp vc : value)

include hf

theorem lrFrame_lookup_prev :
    fmapLookupBy symCmpK lrPrevSym (lrFrame vp vc f) = some vp := by
  unfold lrFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

theorem lrFrame_lookup_cur :
    fmapLookupBy symCmpK lrCurSym (lrFrame vp vc f) = some vc := by
  unfold lrFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK, if_pos (by decide +kernel)]

theorem lrFrameB_lookup_b :
    fmapLookupBy symCmpK lrBSym (lrFrameB vb vp vc f) = some vb := by
  unfold lrFrameB
  rw [envAdd_lookup (lrFrame_symFrame hf _ _) symCmpK,
    if_pos (by decide +kernel)]

theorem lrFrameB_lookup_prev :
    fmapLookupBy symCmpK lrPrevSym (lrFrameB vb vp vc f) = some vp := by
  unfold lrFrameB
  rw [envAdd_lookup (lrFrame_symFrame hf _ _) symCmpK,
    if_neg (by decide +kernel), lrFrame_lookup_prev hf]

theorem lrFrameB_lookup_cur :
    fmapLookupBy symCmpK lrCurSym (lrFrameB vb vp vc f) = some vc := by
  unfold lrFrameB
  rw [envAdd_lookup (lrFrame_symFrame hf _ _) symCmpK,
    if_neg (by decide +kernel), lrFrame_lookup_cur hf]

theorem lrFrameN_lookup_n :
    fmapLookupBy symCmpK lrNSym (lrFrameN vn vb vp vc f) = some vn := by
  unfold lrFrameN
  rw [envAdd_lookup (lrFrameB_symFrame hf _ _ _) symCmpK,
    if_pos (by decide +kernel)]

theorem lrFrameN_lookup_prev :
    fmapLookupBy symCmpK lrPrevSym (lrFrameN vn vb vp vc f) = some vp := by
  unfold lrFrameN
  rw [envAdd_lookup (lrFrameB_symFrame hf _ _ _) symCmpK,
    if_neg (by decide +kernel), lrFrameB_lookup_prev hf]

theorem lrFrameN_lookup_cur :
    fmapLookupBy symCmpK lrCurSym (lrFrameN vn vb vp vc f) = some vc := by
  unfold lrFrameN
  rw [envAdd_lookup (lrFrameB_symFrame hf _ _ _) symCmpK,
    if_neg (by decide +kernel), lrFrameB_lookup_cur hf]

end LrLookups

/-! ## Binding computations -/

theorem bindSave_lr (pbty cbty : core_base_type)
    (head : CerbMem.PointerValue) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindSaveParams (lrParams pbty cbty head)
        [nullVal, ptrVal head] (f :: rest) =
      lrFrame nullVal (ptrVal head) f :: rest := by
  show update_env (mk_sym_pat lrCurSym cbty) (ptrVal head)
    (update_env (mk_sym_pat lrPrevSym pbty) nullVal (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym]
  rfl

theorem bindArgs_lr (pbty cbty : core_base_type)
    (v1 v2 : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(lrPrevSym, pbty), (lrCurSym, cbty)]
        [v1, v2] (f :: rest) =
      lrFrame v1 v2 f :: rest := by
  show update_env (mk_sym_pat lrCurSym cbty) v2
    (update_env (mk_sym_pat lrPrevSym pbty) v1 (f :: rest)) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym]
  rfl

/-- The sym-binder bind of the memop boolean. -/
theorem bindSym_lr (bbty : core_base_type) (vb vp vc : value)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    update_env (symPat [] lrBSym bbty) vb (lrFrame vp vc f :: rest) =
      lrFrameB vb vp vc f :: rest := by
  rw [update_env_cons]
  show update_env_aux (mk_sym_pat lrBSym bbty) vb (lrFrame vp vc f) :: rest = _
  rw [update_env_aux_sym]
  rfl

/-! ## Evaluation facts at the bound frames -/

section LrEval

variable {f : Fmap sym value} (hf : SymFrame f)
  (rest : List (Fmap sym value))

/-- The memop's operand list is NOT all-values (the cur operand is a
    symbol) — the EVAL premise. -/
theorem lr_memop_operands_nonvalue :
    valueFromPexprs [Pexpr ([] : List annot) () (PEsym lrCurSym),
      Pexpr [] () (PEval nullVal)] = none := rfl

include hf

theorem lr_cur_eval (vp vc : value) :
    evalPexpr fmapEmpty fmapEmpty (lrFrame vp vc f :: rest)
      (Pexpr [] () (PEsym lrCurSym)) = some vc := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (lrFrame_lookup_cur hf _ _) rest

theorem lr_guard_eval (vb vp vc : value) :
    evalPexpr fmapEmpty fmapEmpty (lrFrameB vb vp vc f :: rest)
      (Pexpr [] () (PEsym lrBSym)) = some vb := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (lrFrameB_lookup_b hf _ _ _) rest

theorem lr_exit_eval (vb vp vc : value) :
    evalPexpr fmapEmpty fmapEmpty (lrFrameB vb vp vc f :: rest) lrExitPe = some vp := by
  show evalPexpr fmapEmpty fmapEmpty _ (Pexpr [] () (PEsym lrPrevSym)) = _
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (lrFrameB_lookup_prev hf _ _ _) rest

/-- The load's shifted pointer operand: `array_shift(cur, long, 1)`
    at a node pointer — the engine's own arithmetic, +8 within the
    allocation. -/
theorem lr_shift_eval_B (vb vp : value) (id aN : Int) :
    evalPexpr fmapEmpty fmapEmpty (lrFrameB vb vp (ptrVal (cellPtr id aN)) f :: rest)
      (lrShiftPe lrCurSym) = some (ptrVal (cellPtr id (aN + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (lrFrameB vb vp (ptrVal (cellPtr id aN)) f :: rest)
      (Pexpr [] () (PEsym lrCurSym)) = some (ptrVal (cellPtr id aN)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrFrameB_lookup_cur hf _ _ _) rest]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id aN))) (ivVal 1) = _
  exact evalArrayShift_long_one id aN

/-- The store's shifted pointer operand, after n is bound. -/
theorem lr_shift_eval_N (vn vb vp : value) (id aN : Int) :
    evalPexpr fmapEmpty fmapEmpty (lrFrameN vn vb vp (ptrVal (cellPtr id aN)) f :: rest)
      (lrShiftPe lrCurSym) = some (ptrVal (cellPtr id (aN + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty fmapEmpty (lrFrameN vn vb vp (ptrVal (cellPtr id aN)) f :: rest)
      (Pexpr [] () (PEsym lrCurSym)) = some (ptrVal (cellPtr id aN)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrFrameN_lookup_cur hf _ _ _ _) rest]
  show evalArrayShift fmapEmpty longTy (Vobject (OVpointer (cellPtr id aN))) (ivVal 1) = _
  exact evalArrayShift_long_one id aN

theorem lr_store_value_eval (vn vb vp vc : value) :
    evalPexpr fmapEmpty fmapEmpty (lrFrameN vn vb vp vc f :: rest)
      (Pexpr [] () (PEsym lrPrevSym)) = some vp := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (lrFrameN_lookup_prev hf _ _ _ _) rest

theorem lr_args_eval (vn vb vp vc : value) :
    evalPexprs fmapEmpty fmapEmpty (lrFrameN vn vb vp vc f :: rest)
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEsym lrNSym)] =
      some [vc, vn] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (lrFrameN vn vb vp vc f :: rest)
      (Pexpr ([] : List annot) () (PEsym lrCurSym)) = some vc from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrFrameN_lookup_cur hf _ _ _ _) rest]
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty fmapEmpty (lrFrameN vn vb vp vc f :: rest)
      (Pexpr ([] : List annot) () (PEsym lrNSym)) = some vn from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrFrameN_lookup_n hf _ _ _ _) rest]
  rfl

end LrEval

/-! ## Storable facts for the stored next values -/

theorem node_ptr_encodes (pv : CerbMem.PointerValue) :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ nodePtrTy)) (ptrVal pv) =
      some (CerbMem.pointerMval nodeTy pv) := rfl

theorem node_ptr_compat (pv : CerbMem.PointerValue) :
    CerbMem.ctypeMemCompatible nodePtrTy
      (CerbMem.typeofMval (CerbMem.pointerMval nodeTy pv)) = true := rfl

theorem node_ptr_img_cell {tds : CerbTags.TagDefsMap} (id a : Int) :
    (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval nodeTy (cellPtr id a))).2 =
      ptrImg (cellPtr id a) := rfl

theorem node_ptr_img_null {tds : CerbTags.TagDefsMap} :
    (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval nodeTy nullNode)).2 =
      ptrImg nullNode := rfl

theorem node_ptr_fpm_cell {tds : CerbTags.TagDefsMap} (id a : Int) (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes tds fpm
      (CerbMem.pointerMval nodeTy (cellPtr id a))).1 = fpm := rfl

theorem node_ptr_fpm_null {tds : CerbTags.TagDefsMap} (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes tds fpm (CerbMem.pointerMval nodeTy nullNode)).1 =
      fpm := rfl

theorem node_ptr_bytes_cell {tds : CerbTags.TagDefsMap} (id a : Int) (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes tds fpm
        (CerbMem.pointerMval nodeTy (cellPtr id a))).2 =
      (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval nodeTy (cellPtr id a))).2
      := rfl

theorem node_ptr_bytes_null {tds : CerbTags.TagDefsMap} (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes tds fpm (CerbMem.pointerMval nodeTy nullNode)).2 =
      (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval nodeTy nullNode)).2
      := rfl

/-! ## The engine-level chain predicate (identity-indexed; DEMOTED
COROLLARY VOCABULARY since Phase 4 — the flagship conclusions speak
`SeedChain` + `Sat` directly; `ChainAt` remains as the per-node
CellCoh readout, derivable by `seedChain_chainAt`, consumed by the
demo) -/

def ChainAt (σ : Mem) : CerbMem.PointerValue → List (Int × Int) → Prop
  | p, [] => p = nullNode
  | p, nd :: ns => ∃ (aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte), p = cellPtr nd.1 aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧
      CellCoh fmapEmpty σ nd.1 ⟨aN, nodeTy, bs⟩ ∧ bs.length = 16 ∧
      nodeValDec fmapEmpty bs nd.2 ∧ nodeNextDec fmapEmpty bs q ∧ ChainAt σ q ns

/-- The shape of a list head (extracted non-destructively). -/
theorem isList_shape {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (p : CerbMem.PointerValue) (ws : List (Int × Int)) :
    isList (GF := GF) p ws ⊢
      iprop(⌜p = nullNode ∨ ∃ id aN : Int, p = cellPtr id aN ∧ 0 < aN ∧
        aN < 2 ^ 64⌝ ∗ isList p ws) := by
  cases ws with
  | nil =>
    rw [isList_nil]
    iintro %h
    isplit
    · ipureintro
      exact .inl h
    · ipureintro
      exact h
  | cons nd ns =>
    rw [isList_cons]
    iintro ⟨%aN, %q, %bs, %hfacts, Hpt, HT⟩
    obtain ⟨hp, h0, h1, hlen, hval, hnext⟩ := hfacts
    isplit
    · ipureintro
      exact .inr ⟨nd.1, aN, hp, h0, h1⟩
    iexists aN, q, bs
    isplit
    · ipureintro
      exact ⟨hp, h0, h1, hlen, hval, hnext⟩
    isplitl [Hpt]
    · iexact Hpt
    · iexact HT

/-- The store kit: everything the interior store axiom needs about
    the stored next value, at the two shapes a list head can have. -/
theorem node_store_kit {tds : CerbTags.TagDefsMap} (pPrev : CerbMem.PointerValue)
    (hshape : pPrev = nullNode ∨ ∃ id aN : Int, pPrev = cellPtr id aN ∧
      0 < aN ∧ aN < 2 ^ 64) :
    (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval nodeTy pPrev)).2.length
        = 8 ∧
    (∀ fpm, (CerbMem.memValueToBytes tds fpm
      (CerbMem.pointerMval nodeTy pPrev)).1 = fpm) ∧
    (∀ fpm, (CerbMem.memValueToBytes tds fpm
        (CerbMem.pointerMval nodeTy pPrev)).2 =
      (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval nodeTy pPrev)).2) ∧
    (∀ bs' : List CerbMem.AbsByte, (bs'.drop 8).take 8 =
        (CerbMem.memValueToBytes tds [] (CerbMem.pointerMval nodeTy pPrev)).2 →
      nodeNextDec tds bs' pPrev) := by
  rcases hshape with rfl | ⟨id, aN, rfl, h0, h1⟩
  · exact ⟨rfl, fun _ => rfl, fun _ => rfl,
      fun bs' himg => nodeNextDec_ptrImg_null bs' himg⟩
  · refine ⟨?_, fun _ => rfl, fun _ => rfl,
      fun bs' himg => nodeNextDec_ptrImg_cell id aN h0 h1 bs' himg⟩
    rw [node_ptr_img_cell]
    exact ptrImg_cell_length id aN

/-! ## THE INVARIANT AND THE TEXTBOOK PROOF -/

section LrIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (pbty cbty bbty nbty ubty : core_base_type)
  (ns : List (Int × Int))
-- S1b: the wps judgment is indexed by the MACHINE CONTEXT; the
-- exhibit works at the jump-profile instance `procCtx rs` (entry control
-- `procCtl p`: empty stack, in procedure `p`; calls arc C1) with the
-- label map tied by the honest `LabeledAt` link (`procCtx_labels`).
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (lrQ loc ann ra mo pbty cbty bbty nbty ubty))

/-- The postcondition: the delivered value is a pointer satisfying
    `isList · ns.reverse` — the SAME nodes (ids and their own
    values), relinked in exactly reversed order. UNFRAMED (alloc arc
    P4.2): an arbitrary frame is added by the generic statement frame
    rule (`lr_wps_frame` below), not threaded by hand. -/
abbrev lrPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(∃ p' : CerbMem.PointerValue, ⌜w.val = ptrVal p'⌝ ∗
    isList p' ns.reverse)

/-- THE LOOP INVARIANT: `isList prev reversed ∗ isList cur rest` with
    `ns = reversed.reverse ++ rest`, over any reachable frame. UNFRAMED
    (alloc arc P4.2, R-05): the frame that crosses a back edge is
    supplied by `frameLs` — the label-context frame rule
    (`wps_frame_labels`/`blockSpecs_frame`, Wps.lean) — so the
    invariant states only what the loop is about. -/
abbrev lrLs : LabelSpec GF := fun _ args ρ =>
  iprop(∃ (revd rest' : List (Int × Int)) (pPrev pCur : CerbMem.PointerValue)
      (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ptrVal pPrev, ptrVal pCur] ∧ ns = revd.reverse ++ rest' ∧
      ρ = f :: renv ∧ SymFrame f⌝ ∗
    isList pPrev revd ∗ isList pCur rest')

include hQ

/-- The loop body verifies at any invariant frame — the TEXTBOOK
    derivation: each construct by its small axiom or rule, glued by
    the sequencing rules; the frame is carried by ∗ alone. -/
theorem lr_body_wps (revd rest' : List (Int × Int))
    (pPrev pCur : CerbMem.PointerValue) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hxs : ns = revd.reverse ++ rest') :
    iprop(isList (GF := GF) pPrev revd ∗ isList pCur rest') ⊢
      wps (procCtx rs) (some p) (lrLs ns) emptyProcSpec
        (lrPost ns) (lrBody loc ann ra mo bbty nbty ubty)
        (lrFrame (ptrVal pPrev) (ptrVal pCur) f :: renv) := by
  rw [show lrBody loc ann ra mo bbty nbty ubty =
    Expr [] (Esseq (symPat [] lrBSym bbty) lrMemopE
      (Expr [] (Eif (Pexpr [] () (PEsym lrBSym))
        (Expr [] (Epure lrExitPe))
        (lrElse loc ann ra mo nbty ubty)))) from rfl]
  iintro ⟨HP, HC⟩
  cases rest' with
  | nil =>
    -- cur == NULL: the test answers true, the exit delivers prev,
    -- and ns.reverse = reversed.
    rw [isList_nil]
    icases HC with %hnull
    subst hnull
    iapply wps_seq_sym
    rw [show lrMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEval nullVal)] from rfl]
    iapply wps_memop_eval PtrEq _ _ _
      lr_memop_operands_nonvalue (lr_cur_eval hf renv _ _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal nullNode)),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer nullNode))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wps_memop_ptreq nullNode nullNode _
      (fun σ => eqPtrval_null_null nodeTy nodeTy σ)
    iexists (boolValue true)
    isplit
    · ipureintro
      rfl
    rw [bindSym_lr]
    iapply wps_if_true [] (Pexpr [] () (PEsym lrBSym)) _ _ _
      (by rw [procCtx_extern, lr_guard_eval hf renv (boolValue true) _ _]; rfl)
    iapply wps_pure lrExitPe _ rfl (lr_exit_eval hf renv _ _ _)
    iexists pPrev
    isplit
    · ipureintro
      rfl
    rw [show ns.reverse = revd by rw [hxs]; simp]
    iexact HP
  | cons nd vs =>
    -- cur is a node: test false; load next; store prev into the
    -- next field; jump with (cur, n).
    rw [isList_cons]
    icases HC with ⟨%aN, %q, %bs, %hfacts, Hpt, HT⟩
    obtain ⟨rfl, h0, h1, hlen, hval, hnext⟩ := hfacts
    -- prev's shape (for the store kit), non-destructively
    ihave HP2 := isList_shape pPrev revd $$ HP
    icases HP2 with ⟨%hshape, HP⟩
    have kit := node_store_kit (tds := fmapEmpty) pPrev hshape
    obtain ⟨klen, kfpm, kbytes, knext⟩ := kit
    iapply wps_seq_sym
    rw [show lrMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEval nullVal)] from rfl]
    iapply wps_memop_eval PtrEq _ _ _
      lr_memop_operands_nonvalue (lr_cur_eval hf renv _ _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal (cellPtr nd.1 aN))),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer (cellPtr nd.1 aN)))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wps_memop_ptreq (cellPtr nd.1 aN) nullNode _
      (fun σ => eqPtrval_cell_null nd.1 aN nodeTy σ)
    iexists (boolValue false)
    isplit
    · ipureintro
      rfl
    rw [bindSym_lr]
    iapply wps_if_false [] (Pexpr [] () (PEsym lrBSym)) _ _ _
      (by rw [procCtx_extern, lr_guard_eval hf renv (boolValue false) _ _]; rfl)
    rw [show lrElse loc ann ra mo nbty ubty =
      Expr [] (Esseq (specPat [] [] lrNSym nbty)
        (lrLoadE loc ann mo)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (lrStoreE loc ann mo)
          (Expr [] (Erun ra lrLoopSym
            [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEsym lrNSym)])))))
      from rfl]
    iapply wps_seq_spec
    rw [show lrLoadE loc ann mo =
      loadOpRedex loc ann nodePtrTy (lrShiftPe lrCurSym) mo from rfl]
    iapply wps_load_eval loc ann nodePtrTy (lrShiftPe lrCurSym) mo _
      rfl (lr_shift_eval_B hf renv _ _ nd.1 aN)
    rw [show cellPtr nd.1 (aN + 8) = cellPtr nd.1 (aN + ((8 : Nat) : Int))
      from rfl]
    iapply wps_load_node_field (M := procCtx rs) (p := some p) (Θ := emptyProcSpec) loc ann nd.1 aN 8 mo (.own 1) bs _
      (by rw [nodeTy_size]; omega)
      (fun lum fpm => hnext lum fpm _)
    isplitl [Hpt]
    · iexact Hpt
    iintro %fp Hpt
    iexists (OVpointer q)
    isplit
    · ipureintro
      show (valueFromMemValue (.MVpointer nodeTy q)).2 = _
      rw [valueFromMemValue_ptr]
    rw [update_env_spec]
    rw [show envAdd lrNSym (Vobject (OVpointer q))
        (lrFrameB (boolValue false) (ptrVal pPrev) (ptrVal (cellPtr nd.1 aN)) f) =
      lrFrameN (ptrVal q) (boolValue false) (ptrVal pPrev)
        (ptrVal (cellPtr nd.1 aN)) f from rfl]
    iapply wps_seq
    rw [show lrStoreE loc ann mo = storeOpRedex loc ann nodePtrTy
      (lrShiftPe lrCurSym) (Pexpr [] () (PEsym lrPrevSym)) mo from rfl]
    iapply wps_store_eval loc ann nodePtrTy _ _ mo _
      rfl (lr_shift_eval_N hf renv _ _ _ nd.1 aN)
      (lr_store_value_eval hf renv _ _ _ _)
    rw [show cellPtr nd.1 (aN + 8) = cellPtr nd.1 (aN + ((8 : Nat) : Int))
      from rfl]
    iapply wps_store_node_field loc ann nd.1 aN 8 (ptrVal pPrev) mo bs _
      (node_ptr_encodes pPrev) (by rw [nodeTy_size]; omega) klen
      (node_ptr_compat pPrev) kfpm kbytes
    isplitl [Hpt]
    · iexact Hpt
    iintro %fp2 Hpt
    iapply wps_run [] ra lrLoopSym
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEsym lrNSym)] _ _
      (by rw [procCtx_labels hQ]
          exact lrQ_lookup loc ann ra mo pbty cbty bbty nbty ubty)
      (lr_args_eval hf renv _ _ _ _)
    iexists (nd :: revd), vs, (cellPtr nd.1 aN), q,
      (lrFrameN (ptrVal q) (boolValue false) (ptrVal pPrev)
        (ptrVal (cellPtr nd.1 aN)) f), renv
    isplit
    · ipureintro
      refine ⟨rfl, ?_, rfl, lrFrameN_symFrame hf _ _ _ _⟩
      rw [hxs]
      simp
    isplitl [Hpt HP]
    · -- the RE-POINTED node: cur's cell now holds prev in its next
      -- field; its value slice is untouched — the SAME allocation
      -- (id nd.1) joins the reversed prefix carrying its own value.
      iapply isList_cons_intro nd.1 aN pPrev _ nd.2 revd h0 h1
        (by rw [spliceBytes_length _ _ _ (by rw [klen, hlen]; omega)]
            exact hlen)
        (by intro lum fpm ad
            rw [show ((spliceBytes 8 (CerbMem.memValueToBytes (procCtx rs).tagDefs []
                (CerbMem.pointerMval nodeTy pPrev)).2 bs).drop 0).take 8 =
              (bs.drop 0).take 8 from
              spliceBytes_value_slice _ bs klen hlen]
            exact hval lum fpm ad)
        (knext _ (spliceBytes_next_slice _ bs klen hlen))
      isplitl [Hpt]
      · iexact Hpt
      · iexact HP
    · iexact HT

/-- THE BLOCK SPECIFICATION (per-label invariant rule — no Löb). -/
theorem lr_blockSpecs :
    ⊢ blockSpecs (GF := GF) (procCtx rs) (some p)
      (lrLs ns) emptyProcSpec (lrPost ns) := by
  refine blockSpecs_intro fun l params cont args env0 envs hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := lrQ_inv loc ann ra mo pbty cbty bbty nbty ubty hl
  iintro ⟨%revd, %rest', %pPrev, %pCur, %f, %renv, %hpure, HP, HC⟩
  obtain ⟨rfl, hxs, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = env0 ∧ renv = envs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_lr]
  iapply lr_body_wps loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ
    revd rest' pPrev pCur f renv hf hxs
  isplitl [HP]
  · iexact HP
  · iexact HC

/-- The whole program's statement WP from the entry env: prev = NULL
    (`isList nullNode []` — the empty reversed part), cur = head
    (`isList head ns`). -/
theorem lr_wps (sbty : core_base_type) (head : CerbMem.PointerValue) :
    isList (GF := GF) head ns ⊢
      wps (procCtx rs) (some p) (lrLs ns) emptyProcSpec (lrPost ns)
        (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
        [fmapEmpty] := by
  rw [show lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head =
    Expr [] (Esave (lrLoopSym, sbty) (lrParams pbty cbty head)
      (lrBody loc ann ra mo bbty nbty ubty)) from rfl]
  iintro HL
  iapply wps_save [] (lrLoopSym, sbty) _ _ fmapEmpty []
    (cvals := [nullVal, ptrVal head]) rfl
  rw [bindSave_lr]
  rw [show lrFrame nullVal (ptrVal head) fmapEmpty =
    lrFrame (ptrVal nullNode) (ptrVal head) fmapEmpty from rfl]
  iapply lr_body_wps loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ [] ns
    nullNode head fmapEmpty [] symFrame_empty (by simp)
  isplitr [HL]
  · exact isList_nil_intro
  · iexact HL

/-! ### The arbitrary-frame theorems, by the GENERIC statement frame
rule (alloc arc P4.2, R-05): the framed block specifications and the
framed whole-program judgment are `blockSpecs_frame` /
`wps_frame_labels` applied to the UNFRAMED proofs above — the frame
`RF` is not threaded through any label predicate by hand. -/

/-- The block specifications at the framed label context. -/
theorem lr_blockSpecs_frame (RF : IProp GF) :
    ⊢ blockSpecs (GF := GF) (procCtx rs) (some p) (frameLs RF (lrLs ns)) emptyProcSpec
      (fun w ρ' => iprop(lrPost ns w ρ' ∗ RF)) :=
  (lr_blockSpecs loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ).trans
    (blockSpecs_frame RF)

/-- `{ isList head ns ∗ RF } reverse { ret p'. isList p' ns.reverse ∗ RF }`
    at the statement layer — the frame carried across every back edge
    by the framed label context. -/
theorem lr_wps_frame (RF : IProp GF) (sbty : core_base_type)
    (head : CerbMem.PointerValue) :
    iprop(isList (GF := GF) head ns ∗ RF) ⊢
      wps (procCtx rs) (some p) (frameLs RF (lrLs ns)) emptyProcSpec
        (fun w ρ' => iprop(lrPost ns w ρ' ∗ RF))
        (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
        [fmapEmpty] := by
  iintro ⟨HL, HF⟩
  ihave HW := lr_wps loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ sbty head $$ HL
  iapply wps_frame_labels RF _ _ $$ HW HF

end LrIris

/-! ## The certified cone membership and the engine theorem -/

section LrDrive

open Iris.Std.PartialMap

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (pbty cbty bbty nbty ubty : core_base_type)

/-- The label body is in the certified cone. -/
theorem lrBody_fragJ :
    Frag (lrBody loc ann ra mo bbty nbty ubty) := by
  have hb : BareHead (memopRedex PtrEq
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEval nullVal)]) :=
    .memop_op rfl (.sym _ _) (.val _ _)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym lrCurSym)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEval nullVal)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
  refine .sseq_sym hb hb.frag
    (.if_ (PePure.of_isPePure rfl) (by
        rw [show peDepth (Pexpr ([] : List annot) () (PEsym lrBSym)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      .pure_sym
      (.sseq_spec
        (.load_op rfl
          (.arrayShift [] longTy (.sym _ _) (.val _ _))
          (by rw [show peDepth (lrShiftPe lrCurSym) = 2 from rfl,
            show lemDefaultFuel = 999999 + 1 from rfl]; omega))
        (.sseq
          (.store_op rfl
            (.arrayShift [] longTy (.sym _ _) (.val _ _)) (.sym _ _)
            (by rw [show peDepth (lrShiftPe lrCurSym) = 2 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega)
            (by rw [show peDepth (Pexpr ([] : List annot) ()
                (PEsym lrPrevSym)) = 1 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega))
          (.run (PePure.all_of_isPePure rfl) (by
            intro pe hpe
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
            rcases hpe with rfl | rfl <;>
              (rw [show lemDefaultFuel = 999999 + 1 from rfl]
               first
                | (rw [show peDepth (Pexpr ([] : List annot) ()
                    (PEsym lrCurSym)) = 1 from rfl]; omega)
                | (rw [show peDepth (Pexpr ([] : List annot) ()
                    (PEsym lrNSym)) = 1 from rfl]; omega)))))))

/-! ## Seeding: a pure chain description of the initial cell map
(IDENTITY-INDEXED since Phase 4: the map's keys ARE the chain's
allocation-id list — `SeedChain.footprint`) -/

/-- The seeded input chain, as a pure fact about the initial cell
    map: one disjoint singleton per node AT THE NODE'S ALLOCATION ID,
    decode facts per field, the last next-image null. -/
def SeedChain : SpikeHeapF SpikeCell → CerbMem.PointerValue →
    List (Int × Int) → Prop
  | m, p, [] => m = (∅ : SpikeHeapF SpikeCell) ∧ p = nullNode
  | m, p, nd :: ns => ∃ (aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte) (m' : SpikeHeapF SpikeCell),
      p = cellPtr nd.1 aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
      nodeValDec fmapEmpty bs nd.2 ∧ nodeNextDec fmapEmpty bs q ∧
      ((Iris.Std.PartialMap.singleton nd.1 (SpikeCell.mk aN nodeTy bs) :
        SpikeHeapF SpikeCell)) ##ₘ m' ∧
      m = Iris.Std.PartialMap.union
        (Iris.Std.PartialMap.singleton nd.1 (SpikeCell.mk aN nodeTy bs)) m' ∧
      SeedChain m' q ns

/-- `get?` over the (term-level) union — the Iris lemma at the
    union spelling `SeedChain` uses. -/
theorem get?_union' (m₁ m₂ : SpikeHeapF SpikeCell) (k : Int) :
    Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union m₁ m₂) k =
      (Iris.Std.PartialMap.get? m₁ k).orElse
        (fun _ => Iris.Std.PartialMap.get? m₂ k) :=
  Iris.Std.LawfulPartialMap.get?_union

/-- Lookup in the right component of a disjoint union. -/
theorem get?_union_right {s m' : SpikeHeapF SpikeCell} (hdisj : s ##ₘ m')
    {i : Int} {c : SpikeCell} (hg : Iris.Std.PartialMap.get? m' i = some c) :
    Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union s m') i = some c := by
  have hs : Iris.Std.PartialMap.get? s i = none := by
    rcases (Iris.Std.PartialMap.disjoint_iff s m').mp hdisj i with h | h
    · exact h
    · rw [h] at hg
      cases hg
  rw [get?_union', hs]
  exact hg

/-- THE FOOTPRINT LAW (Phase 4, F-06 — "same footprint" is literal):
    a seeded chain's cell map is defined at EXACTLY the chain's
    allocation ids. -/
theorem SeedChain.footprint :
    ∀ (ns : List (Int × Int)) (m : SpikeHeapF SpikeCell)
      (p : CerbMem.PointerValue), SeedChain m p ns →
      ∀ k, (Iris.Std.PartialMap.get? m k).isSome ↔ k ∈ ns.map Prod.fst
  | [], m, p, hseed, k => by
    obtain ⟨rfl, -⟩ := hseed
    rw [Iris.Std.LawfulPartialMap.get?_empty]
    simp
  | nd :: ns, m, p, hseed, k => by
    obtain ⟨aN, q, bs, m', -, -, -, -, -, -, hdisj, rfl, hseed'⟩ := hseed
    have ih := SeedChain.footprint ns m' q hseed' k
    by_cases hk : nd.1 = k
    · subst hk
      rw [get?_union', Iris.Std.LawfulPartialMap.get?_singleton_eq rfl]
      simp
    · rw [get?_union', Iris.Std.LawfulPartialMap.get?_singleton_ne hk]
      simp only [List.map_cons, List.mem_cons]
      rw [show (Option.none.orElse fun _ =>
        Iris.Std.PartialMap.get? m' k) = Iris.Std.PartialMap.get? m' k
        from rfl]
      constructor
      · intro h
        exact .inr (ih.mp h)
      · rintro (rfl | h)
        · exact absurd rfl hk
        · exact ih.mpr h

/-- The DEMOTED corollary bridge: a seeded chain carried by a
    satisfying memory reads out as the per-node `CellCoh` chain
    (`ChainAt`) — the pre-Phase-4 conclusion vocabulary, now a pure
    consequence of the flagship's `SeedChain` + `Sat` conclusion. -/
theorem seedChain_chainAt (σ : Mem) :
    ∀ (ns : List (Int × Int)) (m : SpikeHeapF SpikeCell)
      (p : CerbMem.PointerValue), SeedChain m p ns → Coh fmapEmpty σ m →
      ChainAt σ p ns
  | [], m, p, hseed, _ => hseed.2
  | nd :: ns, m, p, hseed, hcoh => by
    obtain ⟨aN, q, bs, m', hp, h0, h1, hlen, hval, hnext, hdisj, rfl,
      hseed'⟩ := hseed
    have hget : Iris.Std.PartialMap.get?
        (Iris.Std.PartialMap.union
          (Iris.Std.PartialMap.singleton nd.1 (SpikeCell.mk aN nodeTy bs)) m')
        nd.1 = some (SpikeCell.mk aN nodeTy bs) := by
      rw [get?_union', Iris.Std.LawfulPartialMap.get?_singleton_eq rfl]
      rfl
    have hcoh' : Coh fmapEmpty σ m' :=
      ⟨fun i c hg => hcoh.cells i c (get?_union_right hdisj hg),
       fun i j ci cj hne hgi hgj => hcoh.disj i j ci cj hne
         (get?_union_right hdisj hgi) (get?_union_right hdisj hgj)⟩
    exact ⟨aN, q, bs, hp, h0, h1, hcoh.cells nd.1 _ hget, hlen, hval, hnext,
      seedChain_chainAt σ ns m' q hseed' hcoh'⟩

/-- Seeding: the initial footprint's big-sep IS the list predicate. -/
theorem seedChain_isList {hlc : HasLC} {GF : BundledGFunctors}
    [SpikeGS hlc GF] :
    ∀ (ws : List (Int × Int)) (m : SpikeHeapF SpikeCell)
      (p : CerbMem.PointerValue),
    SeedChain m p ws →
    iprop(([∗map] i ↦ c ∈ m, cellOwn fmapEmpty (GF := GF) i (.own 1) c)) ⊢
      isList p ws := by
  intro ws
  induction ws with
  | nil =>
    intro m p hseed
    obtain ⟨rfl, rfl⟩ := hseed
    rw [isList_nil]
    iintro -
    ipureintro
    rfl
  | cons nd ns ih =>
    intro m p hseed
    obtain ⟨aN, q, bs, m', hp, h0, h1, hlen, hval, hnext, hdisj, rfl,
      hseed'⟩ := hseed
    subst hp
    iintro Hm
    icases (BigSepM.bigSepM_union hdisj).1 $$ Hm with ⟨H1, Hrest⟩
    iapply isList_cons_intro nd.1 aN q bs nd.2 ns h0 h1 hlen hval hnext
    isplitl [H1]
    · iapply (BigSepM.bigSepM_singleton).1 $$ H1
    · iapply ih m' q hseed' $$ Hrest

/-- The readout companion of `seedChain_isList` (Phase 4): an
    `isList` footprint RE-MATERIALIZES as a cell map with a pure
    `SeedChain` description — the disjointness of the collected
    singletons is forced by ownership validity
    (`bigSepM_own_disjoint`), so no allocation can have been
    duplicated or invented. -/
theorem isList_to_cells {GF : BundledGFunctors} [SpikeGS .hasLC GF] :
    ∀ (ws : List (Int × Int)) (p : CerbMem.PointerValue),
    isList (hlc := .hasLC) (GF := GF) p ws ⊢
      iprop(∃ m : SpikeHeapF SpikeCell, ⌜SeedChain m p ws⌝ ∗
        ([∗map] i ↦ c ∈ m, cellOwn fmapEmpty (hlc := .hasLC) i (.own 1) c))
  | [], p => by
    rw [isList_nil]
    iintro %h
    iexists (∅ : SpikeHeapF SpikeCell)
    isplit
    · ipureintro
      exact ⟨rfl, h⟩
    · iapply BigSepM.bigSepM_empty
      itrivial
  | nd :: ns, p => by
    rw [isList_cons]
    iintro ⟨%aN, %q, %bs, %hfacts, Hpt, HT⟩
    obtain ⟨rfl, h0, h1, hlen, hval, hnext⟩ := hfacts
    ihave HTC := isList_to_cells ns q $$ HT
    icases HTC with ⟨%m', %hseed', Hm'⟩
    ihave H1 : iprop(([∗map] i ↦ c ∈ ((Iris.Std.PartialMap.singleton nd.1
        (SpikeCell.mk aN nodeTy bs)) : SpikeHeapF SpikeCell),
        cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)) $$ [Hpt]
    · iapply (BigSepM.bigSepM_singleton
        (Φ := fun (i : Int) (c : SpikeCell) =>
          cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)
        (i := nd.1) (x := SpikeCell.mk aN nodeTy bs)).2
      iexact Hpt
    ihave %hdisj : ⌜((Iris.Std.PartialMap.singleton nd.1
        (SpikeCell.mk aN nodeTy bs)) : SpikeHeapF SpikeCell) ##ₘ m'⌝
        $$ [H1 Hm']
    · iapply bigSepM_own_disjoint fmapEmpty _ m'
      isplitl [H1]
      · iexact H1
      · iexact Hm'
    iexists (Iris.Std.PartialMap.union
      (Iris.Std.PartialMap.singleton nd.1 (SpikeCell.mk aN nodeTy bs)) m')
    isplit
    · ipureintro
      exact ⟨aN, q, bs, m', rfl, h0, h1, hlen, hval, hnext, hdisj, rfl,
        hseed'⟩
    iapply (BigSepM.bigSepM_union hdisj).2
    isplitl [H1]
    · iexact H1
    · iexact Hm'

/-- The bigsep frame the launches thread through the loop invariant
    (the `RF` instance every engine-facing export uses). -/
abbrev lrCellFrame {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (R : CellMap) : IProp GF :=
  iprop(([∗map] i ↦ c ∈ R, cellOwn fmapEmpty (hlc := .hasLC) i (.own 1) c))

/-- THE READOUT (Phase 4 — through the core `cells_readout`, which
    owns the one state-interpretation open): the loop postcondition
    with a cell-map frame entails the engine-facing conclusion — a
    delivered pointer, a final footprint `Q` seeded as the REVERSED
    chain (same ids, own values), disjointness from and preservation
    of the frame `R`. Both lanes (partial WP and total judgment)
    consume this one lemma. -/
theorem lrPost_readout {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (ns : List (Int × Int)) (R : CellMap) :
    ∀ (w : SpikeVal) (ρ' : EnvStack),
    iprop(lrPost (hlc := .hasLC) (GF := GF) ns w ρ' ∗ lrCellFrame R) ⊢
      readoutPost (fun v σ' => ∃ Q : CellMap,
        (∃ p' : CerbMem.PointerValue, v = ptrVal p' ∧
          SeedChain Q p' ns.reverse) ∧ Q ##ₘ R ∧
        Coh fmapEmpty σ' (Iris.Std.PartialMap.union Q R)) w ρ' := by
  intro w ρ'
  iintro ⟨⟨%p', %hval, HL⟩, HF⟩
  ihave HC := isList_to_cells ns.reverse p' $$ HL
  icases HC with ⟨%Q, %hQ, HQ⟩
  iapply cells_readout fmapEmpty (fun v Q => ∃ p' : CerbMem.PointerValue,
      v = ptrVal p' ∧ SeedChain Q p' ns.reverse) R w.val
  isplitl [HQ]
  · iexists Q
    isplit
    · ipureintro
      exact ⟨p', hval, hQ⟩
    · iexact HQ
  · iexact HF

/-- The base-WP face with the engine readout (the launch shape
    `engine_adequacyU` consumes). -/
theorem lr_wp_readout {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (ns : List (Int × Int)) (p : sym) (rs : core_run_state)
    (hQ : LabeledAt rs p (lrQ loc ann ra mo pbty cbty bbty nbty ubty))
    (sbty : core_base_type) (head : CerbMem.PointerValue) (R : CellMap) :
    iprop(isList (hlc := .hasLC) (GF := GF) head ns ∗ lrCellFrame R) ⊢
      WP (⟨lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head,
            [fmapEmpty], procCtl p, procCtx rs⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns' : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns' κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜∃ Q : CellMap, (∃ p' : CerbMem.PointerValue,
                CoreRVal.val w = ptrVal p' ∧ SeedChain Q p' ns.reverse) ∧
              Q ##ₘ R ∧ Coh (procCtx rs).tagDefs σ' (Iris.Std.PartialMap.union Q R)⌝) }} := by
  refine (lr_wps_frame loc ann ra mo pbty cbty bbty nbty ubty ns
    p rs hQ (lrCellFrame R) sbty head).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((lr_blockSpecs_frame loc ann ra mo pbty cbty bbty nbty ubty ns
      p rs hQ (lrCellFrame R)).trans
      (wps_sound_empty (ctl := procCtl p) rfl (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
        [fmapEmpty]))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  refine wp_mono fun w => ?_
  exact lrPost_readout ns R w.w w.ρ

/-- LIST-REVERSE, END TO END — THE FLAGSHIP AT FULL STRENGTH
    (foundations Phase 4; audit F-06's exit criterion): driving the
    REAL engine ({step_ctx → sequential discharge} at the
    proc-carrying thread, labels tied through
    `core_run_state.labeled`) on the authored in-place reversal,
    from ANY memory that satisfies the seeded input chain `m₀`
    TOGETHER WITH an arbitrary disjoint frame footprint `R` (the
    `SemTripleU` rest-quantifier, at the proc-carrying context):
    - the engine never kills, never derails, and
    - any delivered value is a POINTER `p'` heading a final
      footprint `Q` with `SeedChain Q p' ns.reverse` — IN-PLACE,
      SAME-FOOTPRINT REVERSAL in the literal sense: the final chain
      visits EXACTLY the original allocation ids in reversed order
      (`ns.reverse.map .1 = (ns.map .1).reverse` — a permutation of
      the original node set by construction), each node still
      carrying its own value; the stated footprint equality
      `∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome` pins the node
      SET on the actual maps (nothing allocated, nothing leaked);
    - THE FRAME `R` IS RETURNED VERBATIM: `Sat σ' (Q ∪ R)` — every
      allocation outside the chain is untouched.
    Partial correctness at EVERY drive length; the TOTAL form below
    delivers at the derived budget.
    SpikeGF-concrete: no ghost-functor binder in the statement. -/
theorem list_reverse_certified
    (sbty : core_base_type) (ns : List (Int × Int))
    (head : CerbMem.PointerValue)
    (m₀ : CellMap) (hseed : SeedChain m₀ head ns)
    (R : CellMap) (hR : m₀ ##ₘ R)
    (σ₀ : Mem) (hcoh : Sat fmapEmpty σ₀ (Iris.Std.PartialMap.union m₀ R))
    (nsteps : Nat) (aids : Nat → Nat) :
    let prog := lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head
    let rs := lrRS loc ann ra mo pbty cbty bbty nbty ubty
    (∀ r, driveU (procCtx rs) aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveU (procCtx rs) aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveU (procCtx rs) aids nsteps
        (procThread lrProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      ∃ (p' : CerbMem.PointerValue) (Q : CellMap),
        v = ptrVal p' ∧
        SeedChain Q p' ns.reverse ∧
        (∀ k, (Iris.Std.PartialMap.get? Q k).isSome ↔
          (Iris.Std.PartialMap.get? m₀ k).isSome) ∧
        Q ##ₘ R ∧
        Sat fmapEmpty σ' (Iris.Std.PartialMap.union Q R)) := by
  intro prog rs
  have hlbl : (procCtx rs).labelsAt (procCtl lrProcSym).proc = _ :=
    procCtx_labels (lrRS_labeledAt loc ann ra mo pbty cbty bbty nbty ubty)
  have h := engine_adequacyU (GF := SpikeGF)
    (M := procCtx rs) (procCtx_wf _) (ctl := procCtl lrProcSym) rfl
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := lrQ_inv loc ann ra mo pbty cbty bbty nbty ubty hl
      exact lrBody_fragJ loc ann ra mo bbty nbty ubty)
    (fun l params cont hl => by
      rw [hlbl] at hl
      obtain ⟨-, rfl⟩ := lrQ_inv loc ann ra mo pbty cbty bbty nbty ubty hl
      exact Nat.le_trans (lrBody_fragJ loc ann ra mo bbty nbty ubty).pot_le_two
        (by rw [show esize (lrBody loc ann ra mo bbty nbty ubty) = 5 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    (procCtx_fragProcs _)
    prog fmapEmpty [] σ₀ (Iris.Std.PartialMap.union m₀ R)
    (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl) (lrBody_fragJ loc ann ra mo bbty nbty ubty))
    (Nat.le_trans (Frag.pot_le_two (e := prog) (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl)
        (lrBody_fragJ loc ann ra mo bbty nbty ubty)))
      (by rw [show esize prog = 6 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    hcoh
    (fun v σ' => ∃ Q : CellMap, (∃ p' : CerbMem.PointerValue,
        v = ptrVal p' ∧ SeedChain Q p' ns.reverse) ∧ Q ##ₘ R ∧
      Coh fmapEmpty σ' (Iris.Std.PartialMap.union Q R))
    (by
      intro inst
      refine ((BigSepM.bigSepM_union hR).1.trans
        (BI.sep_mono (seedChain_isList ns m₀ head hseed) .rfl)).trans ?_
      exact lr_wp_readout loc ann ra mo pbty cbty bbty nbty ubty ns
        lrProcSym rs (lrRS_labeledAt loc ann ra mo pbty cbty bbty nbty ubty)
        sbty head R)
    nsteps aids
  refine ⟨h.1, h.2.1, fun v σ' hdone => ?_⟩
  obtain ⟨Q, ⟨p', rfl, hQseed⟩, hdisj, hsat⟩ := h.2.2 v σ' hdone
  refine ⟨p', Q, rfl, hQseed, fun k => ?_, hdisj, hsat⟩
  rw [SeedChain.footprint ns.reverse Q p' hQseed k,
    SeedChain.footprint ns m₀ head hseed k]
  simp

/-! ## THE CONCRETE DEMONSTRATION: a seeded 3-node list [1, 2, 3]
(engine-serialized byte images; every decode fact discharges by
`rfl` — the executable face of the exhibit) -/

/-- A stored long-value image (the engine's own serialization). -/
def valImg (v : Int) : List CerbMem.AbsByte :=
  imgOf fmapEmpty (CerbMem.integerValueMval (.Signed .Long) (CerbMem.integerIval v))

/-- A node image: value long at offset 0, next pointer at offset 8. -/
def demoBytes (v : Int) (next : CerbMem.PointerValue) : List CerbMem.AbsByte :=
  valImg v ++ ptrImg next

def demoHead : CerbMem.PointerValue := cellPtr 1 4096

def demoCell1 : SpikeCell := ⟨4096, nodeTy, demoBytes 1 (cellPtr 2 8192)⟩
def demoCell2 : SpikeCell := ⟨8192, nodeTy, demoBytes 2 (cellPtr 3 12288)⟩
def demoCell3 : SpikeCell := ⟨12288, nodeTy, demoBytes 3 nullNode⟩

open Iris.Std.PartialMap in
def demoM : SpikeHeapF SpikeCell :=
  union (singleton 1 demoCell1)
    (union (singleton 2 demoCell2)
      (union (singleton 3 demoCell3) (∅ : SpikeHeapF SpikeCell)))

/-- The demo's node list: (allocation id, value) per node. -/
def demoNs : List (Int × Int) := [(1, 1), (2, 2), (3, 3)]

open Iris.Std.PartialMap in
theorem demo_seed : SeedChain demoM demoHead demoNs := by
  refine ⟨4096, cellPtr 2 8192, demoBytes 1 (cellPtr 2 8192),
    union (singleton 2 demoCell2)
      (union (singleton 3 demoCell3) (∅ : SpikeHeapF SpikeCell)),
    rfl, by omega, by omega, rfl,
    (fun lum fpm ad => rfl), (fun lum fpm ad => rfl), ?_, rfl, ?_⟩
  · intro k hk
    obtain ⟨h1, h2⟩ := hk
    have hk1 : k = 1 := by
      by_cases h : (1 : Int) = k
      · omega
      · rw [Iris.Std.LawfulPartialMap.get?_singleton_ne h] at h1
        cases h1
    subst hk1
    rw [get?_union',
      Iris.Std.LawfulPartialMap.get?_singleton_ne (by omega),
      get?_union',
      Iris.Std.LawfulPartialMap.get?_singleton_ne (by omega),
      Iris.Std.LawfulPartialMap.get?_empty] at h2
    cases h2
  refine ⟨8192, cellPtr 3 12288, demoBytes 2 (cellPtr 3 12288),
    union (singleton 3 demoCell3) (∅ : SpikeHeapF SpikeCell),
    rfl, by omega, by omega, rfl,
    (fun lum fpm ad => rfl), (fun lum fpm ad => rfl), ?_, rfl, ?_⟩
  · intro k hk
    obtain ⟨h1, h2⟩ := hk
    have hk2 : k = 2 := by
      by_cases h : (2 : Int) = k
      · omega
      · rw [Iris.Std.LawfulPartialMap.get?_singleton_ne h] at h1
        cases h1
    subst hk2
    rw [get?_union',
      Iris.Std.LawfulPartialMap.get?_singleton_ne (by omega),
      Iris.Std.LawfulPartialMap.get?_empty] at h2
    cases h2
  refine ⟨12288, nullNode, demoBytes 3 nullNode,
    (∅ : SpikeHeapF SpikeCell),
    rfl, by omega, by omega, rfl,
    (fun lum fpm ad => rfl), (fun lum fpm ad => rfl), ?_, rfl, ⟨rfl, rfl⟩⟩
  · intro k hk
    obtain ⟨h1, h2⟩ := hk
    rw [Iris.Std.LawfulPartialMap.get?_empty] at h2
    cases h2

/-- THE DEMONSTRATION INSTANCE: reversing the seeded 3-node list
    (ids 1, 2, 3 carrying values 1, 2, 3) next to an arbitrary
    disjoint frame — the delivered pointer heads the SAME three
    allocations relinked as [(3,3), (2,2), (1,1)], the frame is
    returned verbatim, and the demoted `ChainAt` readout of the
    final memory is included (via `seedChain_chainAt`). -/
theorem list_reverse_demo (sbty : core_base_type)
    (R : CellMap) (hR : demoM ##ₘ R)
    (σ₀ : Mem) (hcoh : Sat fmapEmpty σ₀ (Iris.Std.PartialMap.union demoM R))
    (nsteps : Nat) (aids : Nat → Nat) :
    let prog := lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty demoHead
    let rs := lrRS loc ann ra mo pbty cbty bbty nbty ubty
    (∀ r, driveU (procCtx rs) aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveU (procCtx rs) aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveU (procCtx rs) aids nsteps
        (procThread lrProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      ∃ (p' : CerbMem.PointerValue) (Q : CellMap),
        v = ptrVal p' ∧
        SeedChain Q p' [(3, 3), (2, 2), (1, 1)] ∧
        (∀ k, (Iris.Std.PartialMap.get? Q k).isSome ↔
          (Iris.Std.PartialMap.get? demoM k).isSome) ∧
        Q ##ₘ R ∧
        Sat fmapEmpty σ' (Iris.Std.PartialMap.union Q R) ∧
        ChainAt σ' p' [(3, 3), (2, 2), (1, 1)]) := by
  intro prog rs
  have h := list_reverse_certified loc ann ra mo pbty cbty bbty nbty ubty
    sbty demoNs demoHead demoM demo_seed R hR σ₀ hcoh nsteps aids
  refine ⟨h.1, h.2.1, fun v σ' hdone => ?_⟩
  obtain ⟨p', Q, hval, hQSeed, hfoot, hdisj, hsat⟩ := h.2.2 v σ' hdone
  have hrev : demoNs.reverse = [(3, 3), (2, 2), (1, 1)] := rfl
  rw [hrev] at hQSeed
  exact ⟨p', Q, hval, hQSeed, hfoot, hdisj, hsat,
    seedChain_chainAt σ' _ Q p' hQSeed (Sat.union_left hsat)⟩

end LrDrive

/-! ## THE TOTAL LANE (foundations Phase 3 — the registered residual
CLOSES): total list reversal through the total statement judgment.
The variant is the REMAINING CHAIN LENGTH — a heap-resident measure,
pinned by the invariant through the variant-indexed label context
(`lrLsT`: `m = lrCost rest'.length`); the back edge discharges the
judgment's mandatory decrease by arithmetic on the derived
per-iteration cost. THE DERIVED BOUND: `lrCost r = 13·r + 6` per
label entry (memop-eval 1 + PtrEq 2 + sym-beta prepaid; if 1;
load-eval 1 + node load 3; spec-beta + wrapper prepaid; store-eval 1
+ node store 3; wild-beta + wrapper prepaid; jump 1 — the two annot
wrappers each reserve one unit for their eventual merge, of which
the engine spends one, so the budget is one unit per iteration above
the engine's true 12), program bound `13·|ns| + 7`. The 2026-08-31
listrev notes had ESTIMATED ~11·|ns| + 6 before the wrapper-merge
step and the nested-wrapper merge were counted; the derived bound
here is proved, unconditional, and delivered by the GENERIC
simulation (`wpt_engine_boundU`) — zero Step constructors, zero
per-step drive equations, per the audit's acceptance criterion. -/

/-- The derived per-label-entry step budget at remaining length r. -/
def lrCost : Nat → Nat
  | 0 => 6
  | r + 1 => 13 + lrCost r

theorem lrCost_eq (r : Nat) : lrCost r = 13 * r + 6 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [show lrCost (r + 1) = 13 + lrCost r from rfl, ih]
    omega

section NodeClientsT

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {p : Option sym} {Ls : LabelSpecT GF} {Θ : ProcSpecT GF}

/-- NODE `node*`-FIELD LOAD, total form — `wpt_load_cell_at` at view
    type `nodePtrTy` (client instance, cost 3 ≤ k). -/
theorem wpt_load_node_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (mo : memory_order)
    (dq : DFrac) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {mv : CerbMem.MemValue} {k : Nat} (hk : 3 ≤ k)
    (hbound : off + 8 ≤ CerbMem.sizeofCtype M.tagDefs nodeTy)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue M.tagDefs lum fpm (a + (off : Int))
      nodePtrTy ((bs.drop off).take 8) = mv) :
    iprop(cellOwn M.tagDefs (GF := GF) id dq (SpikeCell.mk a nodeTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id dq (SpikeCell.mk a nodeTy bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wpt M p Ls Θ k Ψ (loadExpr loc ann nodePtrTy (cellPtr id (a + (off : Int))) mo)
        ρ :=
  wpt_load_cell_at loc ann id a nodeTy off nodePtrTy mo dq bs ρ hk
    (by rw [nodePtrTy_size]; exact hbound)
    (by rw [nodePtrTy_size]; exact hdec) rfl

/-- NODE `node*`-FIELD STORE, total form — `wpt_store_cell_at` at
    view type `nodePtrTy` (client instance, cost 3 ≤ k). -/
theorem wpt_store_node_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (cv : value) (mo : memory_order)
    (bs : List CerbMem.AbsByte) (ρ : EnvStack) {mv : CerbMem.MemValue}
    {k : Nat} (hk : 3 ≤ k)
    (hmv : memValueFromValue M.tagDefs (Ctype [] (unatomic_ nodePtrTy)) cv =
      some mv)
    (hbound : off + 8 ≤ CerbMem.sizeofCtype M.tagDefs nodeTy)
    (hlen : (CerbMem.memValueToBytes M.tagDefs [] mv).2.length = 8)
    (hcompat : CerbMem.ctypeMemCompatible nodePtrTy (CerbMem.typeofMval mv) =
      true)
    (hfpm : ∀ fpm, (CerbMem.memValueToBytes M.tagDefs fpm mv).1 = fpm)
    (hbytes : ∀ fpm, (CerbMem.memValueToBytes M.tagDefs fpm mv).2 =
      (CerbMem.memValueToBytes M.tagDefs [] mv).2) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a nodeTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a nodeTy
          (spliceBytes off (CerbMem.memValueToBytes M.tagDefs [] mv).2 bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wpt M p Ls Θ k Ψ (storeExpr loc ann nodePtrTy (cellPtr id (a + (off : Int)))
        cv mo) ρ :=
  wpt_store_cell_at loc ann id a nodeTy off nodePtrTy cv mo bs ρ hk hmv
    (by rw [nodePtrTy_size]; exact hbound)
    ⟨hcompat, hfpm, hbytes, by rw [nodePtrTy_size]; exact hlen⟩
    (fun lum fpm => nodeTy_dec_indep lum fpm a _)

end NodeClientsT

section LrTotal

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (pbty cbty bbty nbty ubty : core_base_type)
  (ns : List (Int × Int))
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (lrQ loc ann ra mo pbty cbty bbty nbty ubty))

/-- The variant-indexed label context: the partial invariant
    (UNFRAMED, alloc arc P4.2 — the frame comes by `frameLsT`) plus
    the variant pin `m = lrCost rest'.length` (the heap-resident
    measure enters through the invariant — the length of the chain
    the second argument heads). -/
abbrev lrLsT : LabelSpecT GF := fun _ m args ρ =>
  iprop(∃ (revd rest' : List (Int × Int)) (pPrev pCur : CerbMem.PointerValue)
      (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ptrVal pPrev, ptrVal pCur] ∧ ns = revd.reverse ++ rest' ∧
      m = lrCost rest'.length ∧ ρ = f :: renv ∧ SymFrame f⌝ ∗
    isList pPrev revd ∗ isList pCur rest')

include hQ

/-- The loop body meets its variant budget at any invariant frame —
    the same textbook derivation as `lr_body_wps`, at the total
    stratum with the budget arithmetic. -/
theorem lr_body_wpt (revd rest' : List (Int × Int))
    (pPrev pCur : CerbMem.PointerValue) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hxs : ns = revd.reverse ++ rest') :
    iprop(isList (GF := GF) pPrev revd ∗ isList pCur rest') ⊢
      wpt (procCtx rs) (some p) (lrLsT ns) emptyProcSpecT (lrCost rest'.length)
        (lrPost ns) (lrBody loc ann ra mo bbty nbty ubty)
        (lrFrame (ptrVal pPrev) (ptrVal pCur) f :: renv) := by
  rw [show lrBody loc ann ra mo bbty nbty ubty =
    Expr [] (Esseq (symPat [] lrBSym bbty) lrMemopE
      (Expr [] (Eif (Pexpr [] () (PEsym lrBSym))
        (Expr [] (Epure lrExitPe))
        (lrElse loc ann ra mo nbty ubty)))) from rfl]
  iintro ⟨HP, HC⟩
  cases rest' with
  | nil =>
    -- cur == NULL: exit in 6 = 3 (null test) + 3 (guard + PURE +
    -- delivery)
    rw [isList_nil]
    icases HC with %hnull
    subst hnull
    rw [show lrCost ([] : List (Int × Int)).length = 3 + 3 from rfl]
    iapply wpt_seq_sym
    rw [show lrMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEval nullVal)] from rfl,
      show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_memop_eval PtrEq _ _ _
      lr_memop_operands_nonvalue (lr_cur_eval hf renv _ _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal nullNode)),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer nullNode))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wpt_memop_ptreq nullNode nullNode _ (by omega)
      (fun σ => eqPtrval_null_null nodeTy nodeTy σ)
    iexists (boolValue true)
    isplit
    · ipureintro
      rfl
    rw [bindSym_lr]
    rw [show (2 + 1 : Nat) = 2 + 1 from rfl]
    iapply wpt_if_true [] (Pexpr [] () (PEsym lrBSym)) _ _ _
      (by rw [procCtx_extern, lr_guard_eval hf renv (boolValue true) _ _]; rfl)
    iapply wpt_pure lrExitPe _ (by omega) rfl (lr_exit_eval hf renv _ _ _)
    iexists pPrev
    isplit
    · ipureintro
      rfl
    rw [show ns.reverse = revd by rw [hxs]; simp]
    iexact HP
  | cons nd vs =>
    -- cur is a node: 13 + lrCost |vs| = 3 (null test) + 1 (if) +
    -- 4 (load) + 4 (store) + 1 (jump) + the target's budget
    rw [isList_cons]
    icases HC with ⟨%aN, %q, %bs, %hfacts, Hpt, HT⟩
    obtain ⟨rfl, h0, h1, hlen, hval, hnext⟩ := hfacts
    ihave HP2 := isList_shape pPrev revd $$ HP
    icases HP2 with ⟨%hshape, HP⟩
    have kit := node_store_kit (tds := fmapEmpty) pPrev hshape
    obtain ⟨klen, kfpm, kbytes, knext⟩ := kit
    rw [show lrCost (nd :: vs).length = 3 + (10 + lrCost vs.length) from by
      rw [show (nd :: vs).length = vs.length + 1 from rfl,
        show lrCost (vs.length + 1) = 13 + lrCost vs.length from rfl]
      omega]
    iapply wpt_seq_sym
    rw [show lrMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEval nullVal)] from rfl,
      show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_memop_eval PtrEq _ _ _
      lr_memop_operands_nonvalue (lr_cur_eval hf renv _ _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal (cellPtr nd.1 aN))),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer (cellPtr nd.1 aN)))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wpt_memop_ptreq (cellPtr nd.1 aN) nullNode _ (by omega)
      (fun σ => eqPtrval_cell_null nd.1 aN nodeTy σ)
    iexists (boolValue false)
    isplit
    · ipureintro
      rfl
    rw [bindSym_lr]
    rw [show 10 + lrCost vs.length = (9 + lrCost vs.length) + 1 by omega]
    iapply wpt_if_false [] (Pexpr [] () (PEsym lrBSym)) _ _ _
      (by rw [procCtx_extern, lr_guard_eval hf renv (boolValue false) _ _]; rfl)
    rw [show lrElse loc ann ra mo nbty ubty =
      Expr [] (Esseq (specPat [] [] lrNSym nbty)
        (lrLoadE loc ann mo)
        (Expr [] (Esseq (Pattern [] (CaseBase (none, ubty)))
          (lrStoreE loc ann mo)
          (Expr [] (Erun ra lrLoopSym
            [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEsym lrNSym)])))))
      from rfl,
      show 9 + lrCost vs.length = 4 + (5 + lrCost vs.length) by omega]
    iapply wpt_seq_spec
    rw [show lrLoadE loc ann mo =
      loadOpRedex loc ann nodePtrTy (lrShiftPe lrCurSym) mo from rfl,
      show (4 : Nat) = 3 + 1 from rfl]
    iapply wpt_load_eval loc ann nodePtrTy (lrShiftPe lrCurSym) mo _
      rfl (lr_shift_eval_B hf renv _ _ nd.1 aN)
    rw [show cellPtr nd.1 (aN + 8) = cellPtr nd.1 (aN + ((8 : Nat) : Int))
      from rfl]
    iapply wpt_load_node_field (M := procCtx rs) (p := some p) (Θ := emptyProcSpecT) loc ann nd.1 aN 8 mo (.own 1) bs _
      (by omega)
      (by rw [nodeTy_size]; omega)
      (fun lum fpm => hnext lum fpm _)
    isplitl [Hpt]
    · iexact Hpt
    iintro %fp Hpt
    iexists (OVpointer q)
    isplit
    · ipureintro
      show (valueFromMemValue (.MVpointer nodeTy q)).2 = _
      rw [valueFromMemValue_ptr]
    rw [update_env_spec]
    rw [show envAdd lrNSym (Vobject (OVpointer q))
        (lrFrameB (boolValue false) (ptrVal pPrev) (ptrVal (cellPtr nd.1 aN)) f) =
      lrFrameN (ptrVal q) (boolValue false) (ptrVal pPrev)
        (ptrVal (cellPtr nd.1 aN)) f from rfl]
    rw [show 5 + lrCost vs.length = 4 + (1 + lrCost vs.length) by omega]
    iapply wpt_seq
    rw [show lrStoreE loc ann mo = storeOpRedex loc ann nodePtrTy
      (lrShiftPe lrCurSym) (Pexpr [] () (PEsym lrPrevSym)) mo from rfl,
      show (4 : Nat) = 3 + 1 from rfl]
    iapply wpt_store_eval loc ann nodePtrTy _ _ mo _
      rfl (lr_shift_eval_N hf renv _ _ _ nd.1 aN)
      (lr_store_value_eval hf renv _ _ _ _)
    rw [show cellPtr nd.1 (aN + 8) = cellPtr nd.1 (aN + ((8 : Nat) : Int))
      from rfl]
    iapply wpt_store_node_field loc ann nd.1 aN 8 (ptrVal pPrev) mo bs _
      (by omega)
      (node_ptr_encodes pPrev) (by rw [nodeTy_size]; omega) klen
      (node_ptr_compat pPrev) kfpm kbytes
    isplitl [Hpt]
    · iexact Hpt
    iintro %fp2 Hpt
    iapply wpt_run [] ra lrLoopSym
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEsym lrNSym)] _ _
      (lrCost vs.length)
      (by rw [procCtx_labels hQ]
          exact lrQ_lookup loc ann ra mo pbty cbty bbty nbty ubty)
      (lr_args_eval hf renv _ _ _ _)
      (by omega)
    iexists (nd :: revd), vs, (cellPtr nd.1 aN), q,
      (lrFrameN (ptrVal q) (boolValue false) (ptrVal pPrev)
        (ptrVal (cellPtr nd.1 aN)) f), renv
    isplit
    · ipureintro
      refine ⟨rfl, ?_, rfl, rfl, lrFrameN_symFrame hf _ _ _ _⟩
      rw [hxs]
      simp
    isplitl [Hpt HP]
    · iapply isList_cons_intro nd.1 aN pPrev _ nd.2 revd h0 h1
        (by rw [spliceBytes_length _ _ _ (by rw [klen, hlen]; omega)]
            exact hlen)
        (by intro lum fpm ad
            rw [show ((spliceBytes 8 (CerbMem.memValueToBytes (procCtx rs).tagDefs []
                (CerbMem.pointerMval nodeTy pPrev)).2 bs).drop 0).take 8 =
              (bs.drop 0).take 8 from
              spliceBytes_value_slice _ bs klen hlen]
            exact hval lum fpm ad)
        (knext _ (spliceBytes_next_slice _ bs klen hlen))
      isplitl [Hpt]
      · iexact Hpt
      · iexact HP
    · iexact HT

/-- The body at the FRAMED label context (`wpt_frame_labels` on the
    unframed body — what a consumer that wraps the label context, like
    the production reversal, instantiates). -/
theorem lr_body_wpt_frame (RF : IProp GF) (revd rest' : List (Int × Int))
    (pPrev pCur : CerbMem.PointerValue) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hxs : ns = revd.reverse ++ rest') :
    iprop((isList (GF := GF) pPrev revd ∗ isList pCur rest') ∗ RF) ⊢
      wpt (procCtx rs) (some p) (frameLsT RF (lrLsT ns)) emptyProcSpecT (lrCost rest'.length)
        (fun w ρ' => iprop(lrPost ns w ρ' ∗ RF)) (lrBody loc ann ra mo bbty nbty ubty)
        (lrFrame (ptrVal pPrev) (ptrVal pCur) f :: renv) :=
  (BI.sep_mono ((lr_body_wpt loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ
      revd rest' pPrev pCur f renv hf hxs).trans (wpt_frame_labels RF _ _ _)) .rfl).trans
    BI.wand_elim_left

/-- THE TOTAL BLOCK SPECIFICATION for the reversal loop. -/
theorem lr_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (procCtx rs) (some p)
      (lrLsT ns) emptyProcSpecT (lrPost ns) := by
  refine blockSpecsT_intro fun l params cont args env0 envs m hl => ?_
  rw [procCtx_labels hQ] at hl
  obtain ⟨rfl, rfl⟩ := lrQ_inv loc ann ra mo pbty cbty bbty nbty ubty hl
  iintro ⟨%revd, %rest', %pPrev, %pCur, %f, %renv, %hpure, HP, HC⟩
  obtain ⟨rfl, hxs, rfl, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = env0 ∧ renv = envs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_lr]
  iapply lr_body_wpt loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ
    revd rest' pPrev pCur f renv hf hxs
  isplitl [HP]
  · iexact HP
  · iexact HC

/-- The whole program's total judgment at budget `lrCost |ns| + 1`. -/
theorem lr_wpt (sbty : core_base_type) (head : CerbMem.PointerValue) :
    isList (GF := GF) head ns ⊢
      wpt (procCtx rs) (some p) (lrLsT ns) emptyProcSpecT (lrCost ns.length + 1) (lrPost ns)
        (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
        [fmapEmpty] := by
  rw [show lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head =
    Expr [] (Esave (lrLoopSym, sbty) (lrParams pbty cbty head)
      (lrBody loc ann ra mo bbty nbty ubty)) from rfl]
  iintro HL
  iapply wpt_save_vals [] (lrLoopSym, sbty) _ _ fmapEmpty []
    (cvals := [nullVal, ptrVal head]) rfl
  rw [bindSave_lr]
  rw [show lrFrame nullVal (ptrVal head) fmapEmpty =
    lrFrame (ptrVal nullNode) (ptrVal head) fmapEmpty from rfl]
  iapply lr_body_wpt loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ [] ns
    nullNode head fmapEmpty [] symFrame_empty (by simp)
  isplitr [HL]
  · exact isList_nil_intro
  · iexact HL

/-- The total block specifications at the framed label context
    (`blockSpecsT_frame` on the unframed proof). -/
theorem lr_blockSpecsT_frame (RF : IProp GF) :
    ⊢ blockSpecsT (GF := GF) (procCtx rs) (some p) (frameLsT RF (lrLsT ns)) emptyProcSpecT
      (fun w ρ' => iprop(lrPost ns w ρ' ∗ RF)) :=
  (lr_blockSpecsT loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ).trans
    (blockSpecsT_frame RF)

/-- The framed total judgment (`wpt_frame_labels` on the unframed
    proof): the frame rides through every back edge, the budget is
    untouched. -/
theorem lr_wpt_frame (RF : IProp GF) (sbty : core_base_type)
    (head : CerbMem.PointerValue) :
    iprop(isList (GF := GF) head ns ∗ RF) ⊢
      wpt (procCtx rs) (some p) (frameLsT RF (lrLsT ns)) emptyProcSpecT (lrCost ns.length + 1)
        (fun w ρ' => iprop(lrPost ns w ρ' ∗ RF))
        (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
        [fmapEmpty] := by
  iintro ⟨HL, HF⟩
  ihave HW := lr_wpt loc ann ra mo pbty cbty bbty nbty ubty ns p rs hQ sbty head $$ HL
  iapply wpt_frame_labels RF _ _ _ $$ HW HF

end LrTotal

section LrTotalExport

open Iris.Std.PartialMap

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (pbty cbty bbty nbty ubty : core_base_type)

theorem lrProg_pot (sbty : core_base_type) (head : CerbMem.PointerValue) :
    pot (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head) = 7 := rfl

theorem lrBody_pot : pot (lrBody loc ann ra mo bbty nbty ubty) = 6 := rfl

/-- LIST-REVERSE, THE UNCONDITIONAL TOTAL ENGINE EQUATION — THE
    FLAGSHIP AT FULL STRENGTH (foundations Phase 4; audit F-06's
    exit criterion: same-footprint, in-place reversal + TERMINATION
    + frame preservation, in one statement, no fuel hypotheses):
    from any memory satisfying the seeded chain `m₀` next to an
    ARBITRARY disjoint frame footprint `R`, the engine's `driveU` at
    the DERIVED bound `13·|ns| + 7` (13 per iteration + 6 exit + 1
    entry) DELIVERS a pointer `p'` heading a final footprint `Q`
    with `SeedChain Q p' ns.reverse` — the SAME allocation ids in
    exactly reversed order, each node carrying its own value — the
    footprint equality `∀ k, (get? Q k).isSome ↔ (get? m₀ k).isSome`
    stated on the maps, and the frame `R` returned VERBATIM
    (`Sat σ' (Q ∪ R)`). A corollary of the total judgment through
    the generic simulation: zero Step constructors, zero per-step drive-equation
    chains. SpikeGF-concrete: no ghost-functor binder. -/
theorem list_reverse_certified_total (sbty : core_base_type)
    (ns : List (Int × Int)) (head : CerbMem.PointerValue)
    (m₀ : CellMap) (hseed : SeedChain m₀ head ns)
    (R : CellMap) (hR : m₀ ##ₘ R)
    (σ₀ : Mem) (hcoh : Sat fmapEmpty σ₀ (Iris.Std.PartialMap.union m₀ R))
    (aids : Nat → Nat) :
    ∃ (p' : CerbMem.PointerValue) (Q : CellMap) (σ' : Mem),
      driveU (procCtx (lrRS loc ann ra mo pbty cbty bbty nbty ubty)) aids
        (13 * ns.length + 7)
        (procThread lrProcSym
          (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
          [fmapEmpty]) σ₀ = .done (ptrVal p') σ' ∧
      SeedChain Q p' ns.reverse ∧
      (∀ k, (Iris.Std.PartialMap.get? Q k).isSome ↔
        (Iris.Std.PartialMap.get? m₀ k).isSome) ∧
      Q ##ₘ R ∧
      Sat fmapEmpty σ' (Iris.Std.PartialMap.union Q R) := by
  have hQ := lrRS_labeledAt loc ann ra mo pbty cbty bbty nbty ubty
  have hk : lrCost ns.length + 1 = 13 * ns.length + 7 := by
    rw [lrCost_eq]
  rw [← hk]
  have hlbl := procCtx_labels hQ
  obtain ⟨v, σ', hdone, ⟨Q, ⟨p', rfl, hQseed⟩, hdisj, hsat⟩, -⟩ :=
    wpt_engine_boundU (GF := SpikeGF)
      (M := procCtx (lrRS loc ann ra mo pbty cbty bbty nbty ubty)) (ctl := procCtl lrProcSym)
      (procCtx_wf _) rfl
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := lrQ_inv loc ann ra mo pbty cbty bbty nbty ubty hl
        exact lrBody_fragJ loc ann ra mo bbty nbty ubty)
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := lrQ_inv loc ann ra mo pbty cbty bbty nbty ubty hl
        rw [lrBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (frameLsT (lrCellFrame R) (lrLsT ns))
      (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
      fmapEmpty [] σ₀ (Iris.Std.PartialMap.union m₀ R)
      (.save (saveParams_pure_of_vals rfl) (saveParams_depth_of_vals rfl) (lrBody_fragJ loc ann ra mo bbty nbty ubty))
      (by rw [lrProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      hcoh
      (fun v σ' => ∃ Q : CellMap, (∃ p' : CerbMem.PointerValue,
          v = ptrVal p' ∧ SeedChain Q p' ns.reverse) ∧ Q ##ₘ R ∧
        Coh fmapEmpty σ' (Iris.Std.PartialMap.union Q R))
      (lrCost ns.length + 1)
      (by
        intro inst
        refine ((BigSepM.bigSepM_union hR).1.trans
          (BI.sep_mono (seedChain_isList ns m₀ head hseed) .rfl)).trans ?_
        refine .trans BI.emp_sep.2 (BI.sep_mono ?_ ?_)
        · exact (lr_blockSpecsT_frame loc ann ra mo pbty cbty bbty nbty ubty ns
            lrProcSym (lrRS loc ann ra mo pbty cbty bbty nbty ubty) hQ
            (lrCellFrame R)).trans
            (blockSpecsT_mono (lrPost_readout ns R))
        · exact (lr_wpt_frame loc ann ra mo pbty cbty bbty nbty ubty ns
              lrProcSym (lrRS loc ann ra mo pbty cbty bbty nbty ubty) hQ
              (lrCellFrame R) sbty head).trans
              (wpt_mono (lrPost_readout ns R) _ _ _))
      aids
  refine ⟨p', Q, σ', hdone, hQseed, fun k => ?_, hdisj, hsat⟩
  rw [SeedChain.footprint ns.reverse Q p' hQseed k,
    SeedChain.footprint ns m₀ head hseed k]
  simp

end LrTotalExport


end CerberusHeapLang
