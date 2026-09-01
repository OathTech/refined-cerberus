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

THE PREDICATE `isList p xs`: plain structural recursion on the
mathematical list (no step-indexing); one ∗-composed ghost cell per
node; the nil case ties to the null encoding; the cons case ∃-binds
the next pointer with the node's cell ∗ the tail. Machine-address
WF (`0 < a < 2^64`) is carried per node — real addresses (what
`allocateObject` mints and what the 8-byte serialization round-trips).

THE PROOF: textbook-compositional — `blockSpecs_intro` with the
invariant `isList prev reversed ∗ isList cur rest` and
`xs = reversed.reverse ++ rest`, each program construct discharged
by its small axiom or rule (`wps_seq_sym` + `wps_memop_eval` +
`wps_memop_ptreq`, `wps_if_*`, `wps_seq_spec` + `wps_load_eval` +
the interior load axiom, `wps_seq` + `wps_store_eval` + the interior
STORE axiom, `wps_run`); no monolithic unfolding. Certified through
the engine lane (`driveJ`, like fib): `list_reverse_certified` (the
general seeded-chain statement) + `list_reverse_demo` (the concrete
3-node instance). REGISTERED RESIDUAL: the TOTAL export at the
variant's step bound is NOT delivered — unlike fib's state-free
drive lane, each iteration's
steps depend on `applyMemM` success at the current memory, so the
unconditional bound needs a pure drive-invariant lane threading
ChainAt-style heap facts through the 11-steps-per-iteration chain
(the named mover; the bound would be 11·|xs| + 6). Record:
docs/2026-08-31_listrev-notes.md §Findings.
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

theorem longTy_size : CerbMem.sizeofCtype longTy = 8 := rfl
theorem nodeTy_size : CerbMem.sizeofCtype nodeTy = 16 := rfl
theorem nodePtrTy_size : CerbMem.sizeofCtype nodePtrTy = 8 := rfl

/-- One long-element shift of a fragment pointer — the ENGINE's own
    arithmetic (`arrayShiftPtrval` at the concrete shape: provenance
    PRESERVED, address advanced by `sizeof(long) = 8`). -/
theorem arrayShift_cellPtr_long (id p : Int) :
    CerbMem.arrayShiftPtrval (cellPtr id p) longTy (CerbMem.integerIval 1) =
      cellPtr id (p + 8) := by
  show CerbMem.PointerValue.PV (.Prov_some id)
    (.PVconcrete none (p + 1 * Int.ofNat (CerbMem.sizeofCtype longTy))) =
    CerbMem.PointerValue.PV (.Prov_some id) (.PVconcrete none (p + 8))
  rw [show p + 1 * Int.ofNat (CerbMem.sizeofCtype longTy) = p + 8 by
    rw [longTy_size]
    rw [show Int.ofNat 8 = (8 : Int) from rfl]
    omega]

theorem evalArrayShift_long_one (id a : Int) :
    evalArrayShift longTy (Vobject (OVpointer (cellPtr id a))) (ivVal 1) =
      some (Vobject (OVpointer (cellPtr id (a + 8)))) := by
  show some (Vobject (OVpointer (CerbMem.arrayShiftPtrval (cellPtr id a)
    longTy (CerbMem.integerIval 1)))) = _
  rw [arrayShift_cellPtr_long]

/-! ## The stored pointer images (the engine's own serialization,
repr — CerbMem.lean:578-603) and their decode round trips -/

/-- The serialized image of a stored value, at the empty funptrmap
    (the fragment's stores are funptrmap-neutral). -/
def imgOf (mv : CerbMem.MemValue) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes [] mv).2

/-- The stored NEXT images: a concrete node pointer / the null. -/
def ptrImg (pv : CerbMem.PointerValue) : List CerbMem.AbsByte :=
  imgOf (CerbMem.pointerMval nodeTy pv)

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
theorem reconstruct_ptrImg_null (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (addr : Int) :
    CerbMem.reconstructValue lum fpm addr nodePtrTy (ptrImg nullNode) =
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
theorem reconstruct_ptrImg_cell (id a : Int) (h0 : 0 < a) (h1 : a < 2 ^ 64)
    (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (addr : Int) :
    CerbMem.reconstructValue lum fpm addr nodePtrTy (ptrImg (cellPtr id a)) =
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
theorem nodeTy_dec_indep (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (addr : Int) (bs : List CerbMem.AbsByte) :
    CerbMem.reconstructValue lum fpm addr nodeTy bs =
      CerbMem.reconstructValue [] [] addr nodeTy bs := rfl

/-! ## The node-field access rules — CLIENT INSTANCES of the generic
typed-subrange rules (F-04: no WP/WPS lifting proof lives in this
module; the layout enters only through `nodeTy`/`nodePtrTy` sizes,
the field offset, and the decode facts). -/

section NodeClients

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpec GF}

/-- NODE `node*`-FIELD LOAD — `wps_load_cell_at` at view type
    `nodePtrTy` (the old example-local lifting rule, re-derived as a
    one-line client). -/
theorem wps_load_node_field {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (id a : Int) (off : Nat) (mo : memory_order)
    (dq : DFrac) (bs : List CerbMem.AbsByte) (ρ : EnvStack)
    {mv : CerbMem.MemValue}
    (hbound : off + 8 ≤ CerbMem.sizeofCtype nodeTy)
    (hdec : ∀ lum fpm, CerbMem.reconstructValue lum fpm (a + (off : Int))
      nodePtrTy ((bs.drop off).take 8) = mv) :
    iprop(cellOwn (GF := GF) id dq (SpikeCell.mk a nodeTy bs) ∗
      (∀ fp, cellOwn id dq (SpikeCell.mk a nodeTy bs) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] ((valueFromMemValue mv).2)) ρ)) ⊢
      wps M Ls Ψ (loadExpr loc ann nodePtrTy (cellPtr id (a + (off : Int))) mo)
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
    (hbound : off + 8 ≤ CerbMem.sizeofCtype nodeTy)
    (hlen : (CerbMem.memValueToBytes [] mv).2.length = 8)
    (hcompat : CerbMem.ctypeMemCompatible nodePtrTy (CerbMem.typeofMval mv) =
      true)
    (hfpm : ∀ fpm, (CerbMem.memValueToBytes fpm mv).1 = fpm)
    (hbytes : ∀ fpm, (CerbMem.memValueToBytes fpm mv).2 =
      (CerbMem.memValueToBytes [] mv).2) :
    iprop(cellOwn (GF := GF) id (.own 1) (SpikeCell.mk a nodeTy bs) ∗
      (∀ fp, cellOwn id (.own 1) (SpikeCell.mk a nodeTy
          (spliceBytes off (CerbMem.memValueToBytes [] mv).2 bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann nodePtrTy (cellPtr id (a + (off : Int)))
        cv mo) ρ :=
  wps_store_cell_at loc ann id a nodeTy off nodePtrTy cv mo bs ρ hmv
    (by rw [nodePtrTy_size]; exact hbound) hcompat hfpm hbytes
    (by rw [nodePtrTy_size]; exact hlen)
    (fun lum fpm => nodeTy_dec_indep lum fpm a _)

end NodeClients

/-! ## THE PREDICATE: `isList p xs` (structural recursion on the
mathematical list; ∗-composed node cells; the nil case IS the null
encoding) -/

/-- The value field's decode fact (offset 0, `signed long`). Pure,
    table- and address-independent (the integer arm reads neither). -/
def nodeValDec (bs : List CerbMem.AbsByte) (v : Int) : Prop :=
  ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (ad : Int),
    CerbMem.reconstructValue lum fpm ad longTy ((bs.drop 0).take 8) =
      .MVinteger (.Signed .Long) (CerbMem.integerIval v)

/-- The next field's decode fact (offset 8, `node*`). -/
def nodeNextDec (bs : List CerbMem.AbsByte) (q : CerbMem.PointerValue) : Prop :=
  ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap) (ad : Int),
    CerbMem.reconstructValue lum fpm ad nodePtrTy ((bs.drop 8).take 8) =
      .MVpointer nodeTy q

/-- The stored images' next-field decode facts (the round trips). -/
theorem nodeNextDec_ptrImg_cell (id a : Int) (h0 : 0 < a) (h1 : a < 2 ^ 64)
    (bs : List CerbMem.AbsByte) (himg : (bs.drop 8).take 8 = ptrImg (cellPtr id a)) :
    nodeNextDec bs (cellPtr id a) := by
  intro lum fpm ad
  rw [himg]
  exact reconstruct_ptrImg_cell id a h0 h1 lum fpm ad

theorem nodeNextDec_ptrImg_null (bs : List CerbMem.AbsByte)
    (himg : (bs.drop 8).take 8 = ptrImg nullNode) :
    nodeNextDec bs nullNode := by
  intro lum fpm ad
  rw [himg]
  exact reconstruct_ptrImg_null lum fpm ad

section IsList

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- THE REPRESENTATION PREDICATE (plain structural recursion; the
    nil case ties to the null encoding; the cons case ∃-binds the
    next pointer with the node's cell ∗ the tail; machine-address WF
    per node). -/
def isList : CerbMem.PointerValue → List Int → IProp GF
  | p, [] => iprop(⌜p = nullNode⌝)
  | p, v :: vs => iprop(∃ (id aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
        nodeValDec bs v ∧ nodeNextDec bs q⌝ ∗
      cellOwn id (.own 1) (SpikeCell.mk aN nodeTy bs) ∗ isList q vs)

@[simp] theorem isList_nil (p : CerbMem.PointerValue) :
    isList (GF := GF) p [] = iprop(⌜p = nullNode⌝) := rfl

theorem isList_cons (p : CerbMem.PointerValue) (v : Int) (vs : List Int) :
    isList (GF := GF) p (v :: vs) = iprop(∃ (id aN : Int)
      (q : CerbMem.PointerValue) (bs : List CerbMem.AbsByte),
      ⌜p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
        nodeValDec bs v ∧ nodeNextDec bs q⌝ ∗
      cellOwn id (.own 1) (SpikeCell.mk aN nodeTy bs) ∗ isList q vs) := rfl

/-- Nil introduction. -/
theorem isList_nil_intro : ⊢ isList (GF := GF) nullNode [] := by
  rw [isList_nil]
  ipureintro
  rfl

/-- Cons introduction (the node's cell ∗ the tail). -/
theorem isList_cons_intro (id aN : Int) (q : CerbMem.PointerValue)
    (bs : List CerbMem.AbsByte) (v : Int) (vs : List Int)
    (h0 : 0 < aN) (h1 : aN < 2 ^ 64) (hlen : bs.length = 16)
    (hval : nodeValDec bs v) (hnext : nodeNextDec bs q) :
    iprop(cellOwn (GF := GF) id (.own 1) (SpikeCell.mk aN nodeTy bs) ∗
        isList q vs) ⊢
      isList (cellPtr id aN) (v :: vs) := by
  rw [isList_cons]
  iintro ⟨Hpt, HL⟩
  iexists id, aN, q, bs
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
    evalPexpr fmapEmpty (lrFrame vp vc f :: rest)
      (Pexpr [] () (PEsym lrCurSym)) = some vc := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (lrFrame_lookup_cur hf _ _) rest

theorem lr_guard_eval (vb vp vc : value) :
    evalPexpr fmapEmpty (lrFrameB vb vp vc f :: rest)
      (Pexpr [] () (PEsym lrBSym)) = some vb := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (lrFrameB_lookup_b hf _ _ _) rest

theorem lr_exit_eval (vb vp vc : value) :
    evalPexpr fmapEmpty (lrFrameB vb vp vc f :: rest) lrExitPe = some vp := by
  show evalPexpr fmapEmpty _ (Pexpr [] () (PEsym lrPrevSym)) = _
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (lrFrameB_lookup_prev hf _ _ _) rest

/-- The load's shifted pointer operand: `array_shift(cur, long, 1)`
    at a node pointer — the engine's own arithmetic, +8 within the
    allocation. -/
theorem lr_shift_eval_B (vb vp : value) (id aN : Int) :
    evalPexpr fmapEmpty (lrFrameB vb vp (ptrVal (cellPtr id aN)) f :: rest)
      (lrShiftPe lrCurSym) = some (ptrVal (cellPtr id (aN + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty (lrFrameB vb vp (ptrVal (cellPtr id aN)) f :: rest)
      (Pexpr [] () (PEsym lrCurSym)) = some (ptrVal (cellPtr id aN)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrFrameB_lookup_cur hf _ _ _) rest]
  show evalArrayShift longTy (Vobject (OVpointer (cellPtr id aN))) (ivVal 1) = _
  exact evalArrayShift_long_one id aN

/-- The store's shifted pointer operand, after n is bound. -/
theorem lr_shift_eval_N (vn vb vp : value) (id aN : Int) :
    evalPexpr fmapEmpty (lrFrameN vn vb vp (ptrVal (cellPtr id aN)) f :: rest)
      (lrShiftPe lrCurSym) = some (ptrVal (cellPtr id (aN + 8))) := by
  unfold lrShiftPe
  rw [evalPexpr_array_shift]
  rw [show evalPexpr fmapEmpty (lrFrameN vn vb vp (ptrVal (cellPtr id aN)) f :: rest)
      (Pexpr [] () (PEsym lrCurSym)) = some (ptrVal (cellPtr id aN)) from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrFrameN_lookup_cur hf _ _ _ _) rest]
  show evalArrayShift longTy (Vobject (OVpointer (cellPtr id aN))) (ivVal 1) = _
  exact evalArrayShift_long_one id aN

theorem lr_store_value_eval (vn vb vp vc : value) :
    evalPexpr fmapEmpty (lrFrameN vn vb vp vc f :: rest)
      (Pexpr [] () (PEsym lrPrevSym)) = some vp := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (lrFrameN_lookup_prev hf _ _ _ _) rest

theorem lr_args_eval (vn vb vp vc : value) :
    evalPexprs fmapEmpty (lrFrameN vn vb vp vc f :: rest)
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEsym lrNSym)] =
      some [vc, vn] := by
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty (lrFrameN vn vb vp vc f :: rest)
      (Pexpr ([] : List annot) () (PEsym lrCurSym)) = some vc from by
    rw [evalPexpr_sym_empty]
    exact lookup_env_head (lrFrameN_lookup_cur hf _ _ _ _) rest]
  rw [evalPexprs_cons]
  rw [show evalPexpr fmapEmpty (lrFrameN vn vb vp vc f :: rest)
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

theorem node_ptr_img_cell (id a : Int) :
    (CerbMem.memValueToBytes [] (CerbMem.pointerMval nodeTy (cellPtr id a))).2 =
      ptrImg (cellPtr id a) := rfl

theorem node_ptr_img_null :
    (CerbMem.memValueToBytes [] (CerbMem.pointerMval nodeTy nullNode)).2 =
      ptrImg nullNode := rfl

theorem node_ptr_fpm_cell (id a : Int) (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes fpm
      (CerbMem.pointerMval nodeTy (cellPtr id a))).1 = fpm := rfl

theorem node_ptr_fpm_null (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes fpm (CerbMem.pointerMval nodeTy nullNode)).1 =
      fpm := rfl

theorem node_ptr_bytes_cell (id a : Int) (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes fpm
        (CerbMem.pointerMval nodeTy (cellPtr id a))).2 =
      (CerbMem.memValueToBytes [] (CerbMem.pointerMval nodeTy (cellPtr id a))).2
      := rfl

theorem node_ptr_bytes_null (fpm : CerbMem.Funptrmap) :
    (CerbMem.memValueToBytes fpm (CerbMem.pointerMval nodeTy nullNode)).2 =
      (CerbMem.memValueToBytes [] (CerbMem.pointerMval nodeTy nullNode)).2
      := rfl

/-! ## The engine-level chain predicate (the conclusion's vocabulary:
CellCoh facts about the FINAL MemState, no Iris) -/

def ChainAt (σ : Mem) : CerbMem.PointerValue → List Int → Prop
  | p, [] => p = nullNode
  | p, v :: vs => ∃ (id aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte), p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧
      CellCoh σ id ⟨aN, nodeTy, bs⟩ ∧ bs.length = 16 ∧
      nodeValDec bs v ∧ nodeNextDec bs q ∧ ChainAt σ q vs

/-- The readout: an `isList` footprint against the final coupling
    yields the pure engine-level chain (per-node `cellOwn_cellCoh`). -/
theorem isList_readout {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (σ : Mem) {mm : SpikeHeapF MetaCell} {mb : SpikeHeapF CerbMem.AbsByte}
    {mk : SpikeHeapF AllocCursor} (hG : CohG σ mm mb mk) :
    ∀ (ws : List Int) (p : CerbMem.PointerValue),
    iprop(isList (GF := GF) p ws ∗ metaInterp mm ∗ byteInterp mb) ⊢
      (⌜ChainAt σ p ws⌝ : IProp GF) := by
  intro ws
  induction ws with
  | nil =>
    intro p
    rw [isList_nil]
    iintro ⟨%h, -, -⟩
    ipureintro
    exact h
  | cons v vs ih =>
    intro p
    rw [isList_cons]
    iintro ⟨⟨%id, %aN, %q, %bs, %hfacts, Hpt, HT⟩, Hmi, Hbi⟩
    obtain ⟨rfl, h0, h1, hlen, hval, hnext⟩ := hfacts
    ihave %Hcc : ⌜CellCoh σ id ⟨aN, nodeTy, bs⟩ ∧
        Iris.Std.PartialMap.get? mm id =
          some (metaOf (⟨aN, nodeTy, bs⟩ : SpikeCell))⌝ $$ [Hmi Hbi Hpt]
    · iapply cellOwn_cellCoh hG id (.own 1) ⟨aN, nodeTy, bs⟩
        $$ [$Hmi $Hbi $Hpt]
    ihave %htail := ih q $$ [HT Hmi Hbi]
    · isplitl [HT]
      · iexact HT
      isplitl [Hmi]
      · iexact Hmi
      · iexact Hbi
    ipureintro
    exact ⟨id, aN, q, bs, rfl, h0, h1, Hcc.1, hlen, hval,
      hnext, htail⟩

/-- The shape of a list head (extracted non-destructively). -/
theorem isList_shape {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (p : CerbMem.PointerValue) (ws : List Int) :
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
  | cons v vs =>
    rw [isList_cons]
    iintro ⟨%id, %aN, %q, %bs, %hfacts, Hpt, HT⟩
    obtain ⟨hp, h0, h1, hlen, hval, hnext⟩ := hfacts
    isplit
    · ipureintro
      exact .inr ⟨id, aN, hp, h0, h1⟩
    iexists id, aN, q, bs
    isplit
    · ipureintro
      exact ⟨hp, h0, h1, hlen, hval, hnext⟩
    isplitl [Hpt]
    · iexact Hpt
    · iexact HT

/-- The store kit: everything the interior store axiom needs about
    the stored next value, at the two shapes a list head can have. -/
theorem node_store_kit (pPrev : CerbMem.PointerValue)
    (hshape : pPrev = nullNode ∨ ∃ id aN : Int, pPrev = cellPtr id aN ∧
      0 < aN ∧ aN < 2 ^ 64) :
    (CerbMem.memValueToBytes [] (CerbMem.pointerMval nodeTy pPrev)).2.length
        = 8 ∧
    (∀ fpm, (CerbMem.memValueToBytes fpm
      (CerbMem.pointerMval nodeTy pPrev)).1 = fpm) ∧
    (∀ fpm, (CerbMem.memValueToBytes fpm
        (CerbMem.pointerMval nodeTy pPrev)).2 =
      (CerbMem.memValueToBytes [] (CerbMem.pointerMval nodeTy pPrev)).2) ∧
    (∀ bs' : List CerbMem.AbsByte, (bs'.drop 8).take 8 =
        (CerbMem.memValueToBytes [] (CerbMem.pointerMval nodeTy pPrev)).2 →
      nodeNextDec bs' pPrev) := by
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
  (xs : List Int)
-- S1b: the wps judgment is indexed by the MACHINE CONTEXT; the
-- exhibit works at the jump-profile instance `procCtx p rs` with the
-- label map tied by the honest `LabeledAt` link (`procCtx_labels`).
variable (p : sym) (rs : core_run_state)
  (hQ : LabeledAt rs p (lrQ loc ann ra mo pbty cbty bbty nbty ubty))

/-- The postcondition: the delivered value is a pointer satisfying
    `isList · xs.reverse`. -/
abbrev lrPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(∃ p' : CerbMem.PointerValue, ⌜w.val = ptrVal p'⌝ ∗
    isList p' xs.reverse)

/-- THE LOOP INVARIANT: `isList prev reversed ∗ isList cur rest`
    with `xs = reversed.reverse ++ rest`, over any reachable frame. -/
abbrev lrLs : LabelSpec GF := fun _ args ρ =>
  iprop(∃ (revd rest' : List Int) (pPrev pCur : CerbMem.PointerValue)
      (f : Fmap sym value) (renv : List (Fmap sym value)),
    ⌜args = [ptrVal pPrev, ptrVal pCur] ∧ xs = revd.reverse ++ rest' ∧
      ρ = f :: renv ∧ SymFrame f⌝ ∗
    isList pPrev revd ∗ isList pCur rest')

include hQ

/-- The loop body verifies at any invariant frame — the TEXTBOOK
    derivation: each construct by its small axiom or rule, glued by
    the sequencing rules; the frame is carried by ∗ alone. -/
theorem lr_body_wps (revd rest' : List Int)
    (pPrev pCur : CerbMem.PointerValue) (f : Fmap sym value)
    (renv : List (Fmap sym value)) (hf : SymFrame f)
    (hxs : xs = revd.reverse ++ rest') :
    iprop(isList (GF := GF) pPrev revd ∗ isList pCur rest') ⊢
      wps (procCtx p rs) (lrLs xs)
        (lrPost xs) (lrBody loc ann ra mo bbty nbty ubty)
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
    -- and xs.reverse = reversed.
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
    rw [show xs.reverse = revd by rw [hxs]; simp]
    iexact HP
  | cons v vs =>
    -- cur is a node: test false; load next; store prev into the
    -- next field; jump with (cur, n).
    rw [isList_cons]
    icases HC with ⟨%id, %aN, %q, %bs, %hfacts, Hpt, HT⟩
    obtain ⟨rfl, h0, h1, hlen, hval, hnext⟩ := hfacts
    -- prev's shape (for the store kit), non-destructively
    ihave HP2 := isList_shape pPrev revd $$ HP
    icases HP2 with ⟨%hshape, HP⟩
    have kit := node_store_kit pPrev hshape
    obtain ⟨klen, kfpm, kbytes, knext⟩ := kit
    iapply wps_seq_sym
    rw [show lrMemopE = memopRedex PtrEq
      [Pexpr [] () (PEsym lrCurSym), Pexpr [] () (PEval nullVal)] from rfl]
    iapply wps_memop_eval PtrEq _ _ _
      lr_memop_operands_nonvalue (lr_cur_eval hf renv _ _) rfl
    rw [show memopRedex PtrEq [Pexpr [] () (PEval (ptrVal (cellPtr id aN))),
        Pexpr [] () (PEval nullVal)] =
      memopPtrEqVals (Vobject (OVpointer (cellPtr id aN)))
        (Vobject (OVpointer nullNode)) from rfl]
    iapply wps_memop_ptreq (cellPtr id aN) nullNode _
      (fun σ => eqPtrval_cell_null id aN nodeTy σ)
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
      rfl (lr_shift_eval_B hf renv _ _ id aN)
    rw [show cellPtr id (aN + 8) = cellPtr id (aN + ((8 : Nat) : Int))
      from rfl]
    iapply wps_load_node_field loc ann id aN 8 mo (.own 1) bs _
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
        (lrFrameB (boolValue false) (ptrVal pPrev) (ptrVal (cellPtr id aN)) f) =
      lrFrameN (ptrVal q) (boolValue false) (ptrVal pPrev)
        (ptrVal (cellPtr id aN)) f from rfl]
    iapply wps_seq
    rw [show lrStoreE loc ann mo = storeOpRedex loc ann nodePtrTy
      (lrShiftPe lrCurSym) (Pexpr [] () (PEsym lrPrevSym)) mo from rfl]
    iapply wps_store_eval loc ann nodePtrTy _ _ mo _
      rfl rfl (lr_shift_eval_N hf renv _ _ _ id aN)
      (lr_store_value_eval hf renv _ _ _ _)
    rw [show cellPtr id (aN + 8) = cellPtr id (aN + ((8 : Nat) : Int))
      from rfl]
    iapply wps_store_node_field loc ann id aN 8 (ptrVal pPrev) mo bs _
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
    iexists (v :: revd), vs, (cellPtr id aN), q,
      (lrFrameN (ptrVal q) (boolValue false) (ptrVal pPrev)
        (ptrVal (cellPtr id aN)) f), renv
    isplit
    · ipureintro
      refine ⟨rfl, ?_, rfl, lrFrameN_symFrame hf _ _ _ _⟩
      rw [hxs]
      simp
    isplitl [Hpt HP]
    · -- the RE-POINTED node: cur's cell now holds prev in its next
      -- field; its value slice is untouched.
      iapply isList_cons_intro id aN pPrev _ v revd h0 h1
        (by rw [spliceBytes_length _ _ _ (by rw [klen, hlen]; omega)]
            exact hlen)
        (by intro lum fpm ad
            rw [show ((spliceBytes 8 (CerbMem.memValueToBytes []
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
    ⊢ blockSpecs (GF := GF) (procCtx p rs)
      (lrLs xs) (lrPost xs) := by
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
  iapply lr_body_wps loc ann ra mo pbty cbty bbty nbty ubty xs p rs hQ
    revd rest' pPrev pCur f renv hf hxs
  isplitl [HP]
  · iexact HP
  · iexact HC

/-- The whole program's statement WP from the entry env: prev = NULL
    (`isList nullNode []` — the empty reversed part), cur = head
    (`isList head xs`). -/
theorem lr_wps (sbty : core_base_type) (head : CerbMem.PointerValue) :
    isList (GF := GF) head xs ⊢
      wps (procCtx p rs) (lrLs xs) (lrPost xs)
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
  iapply lr_body_wps loc ann ra mo pbty cbty bbty nbty ubty xs p rs hQ [] xs
    nullNode head fmapEmpty [] symFrame_empty (by simp)
  isplitr [HL]
  · exact isList_nil_intro
  · iexact HL

/-- The base-WP face with the engine readout: the delivered value is
    a pointer whose final-heap chain is `xs.reverse`. -/
theorem lr_wp_readout (sbty : core_base_type) (head : CerbMem.PointerValue) :
    isList (GF := GF) head xs ⊢
      WP (⟨lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head,
            [fmapEmpty], procCtx p rs⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜∃ p' : CerbMem.PointerValue, CoreRVal.val w = ptrVal p' ∧
              ChainAt σ' p' xs.reverse⌝) }} := by
  refine (lr_wps loc ann ra mo pbty cbty bbty nbty ubty xs p rs hQ sbty
    head).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((lr_blockSpecs loc ann ra mo pbty cbty bbty nbty ubty xs p rs hQ).trans
      (wps_sound (lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head)
        [fmapEmpty]))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  refine wp_mono fun w => ?_
  iintro ⟨%p', %hval, HL⟩ %σ' %ns %κs %nt Hσ
  icases (stateInterp_iff σ' ns κs nt).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  ihave %hchain : ⌜ChainAt σ' p' xs.reverse⌝ $$ [HL Hmi Hbi]
  · iapply isList_readout σ' HG xs.reverse p'
    isplitl [HL]
    · iexact HL
    isplitl [Hmi]
    · iexact Hmi
    · iexact Hbi
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact ⟨p', hval, hchain⟩

end LrIris

/-! ## The certified cone membership and the engine theorem -/

section LrDrive

open Iris.Std.PartialMap

variable (loc : CerbLocation.Loc) (ann ra : core_run_annotation)
  (mo : memory_order) (pbty cbty bbty nbty ubty : core_base_type)

/-- The label body is in the certified cone. -/
theorem lrBody_fragJ (hlib : CerbLocation.isLibraryLocation loc = false) :
    Frag (lrBody loc ann ra mo bbty nbty ubty) := by
  refine .sseq_sym
    (.memop_op rfl (.sym _ _) (.val _ _)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEsym lrCurSym)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (by rw [show peDepth (Pexpr ([] : List annot) () (PEval nullVal)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    (.if_ (by
        rw [show peDepth (Pexpr ([] : List annot) () (PEsym lrBSym)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      .pure_sym
      (.sseq_spec
        (.load_op hlib rfl
          (.arrayShift [] longTy (.sym _ _) (.val _ _))
          (by rw [show peDepth (lrShiftPe lrCurSym) = 2 from rfl,
            show lemDefaultFuel = 999999 + 1 from rfl]; omega))
        (.sseq
          (.store_op hlib rfl rfl
            (.arrayShift [] longTy (.sym _ _) (.val _ _)) (.sym _ _)
            (by rw [show peDepth (lrShiftPe lrCurSym) = 2 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega)
            (by rw [show peDepth (Pexpr ([] : List annot) ()
                (PEsym lrPrevSym)) = 1 from rfl,
              show lemDefaultFuel = 999999 + 1 from rfl]; omega))
          (.run (by
            intro pe hpe
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
            rcases hpe with rfl | rfl <;>
              (rw [show lemDefaultFuel = 999999 + 1 from rfl]
               first
                | (rw [show peDepth (Pexpr ([] : List annot) ()
                    (PEsym lrCurSym)) = 1 from rfl]; omega)
                | (rw [show peDepth (Pexpr ([] : List annot) ()
                    (PEsym lrNSym)) = 1 from rfl]; omega)))))))

/-! ## Seeding: a pure chain description of the initial cell map -/

/-- The seeded input chain, as a pure fact about the initial cell
    map: one disjoint singleton per node, decode facts per field,
    the last next-image null. -/
def SeedChain : SpikeHeapF SpikeCell → CerbMem.PointerValue → List Int → Prop
  | m, p, [] => m = (∅ : SpikeHeapF SpikeCell) ∧ p = nullNode
  | m, p, v :: vs => ∃ (id aN : Int) (q : CerbMem.PointerValue)
      (bs : List CerbMem.AbsByte) (m' : SpikeHeapF SpikeCell),
      p = cellPtr id aN ∧ 0 < aN ∧ aN < 2 ^ 64 ∧ bs.length = 16 ∧
      nodeValDec bs v ∧ nodeNextDec bs q ∧
      ((Iris.Std.PartialMap.singleton id (SpikeCell.mk aN nodeTy bs) :
        SpikeHeapF SpikeCell)) ##ₘ m' ∧
      m = Iris.Std.PartialMap.union
        (Iris.Std.PartialMap.singleton id (SpikeCell.mk aN nodeTy bs)) m' ∧
      SeedChain m' q vs

/-- Seeding: the initial footprint's big-sep IS the list predicate. -/
theorem seedChain_isList {hlc : HasLC} {GF : BundledGFunctors}
    [SpikeGS hlc GF] :
    ∀ (ws : List Int) (m : SpikeHeapF SpikeCell) (p : CerbMem.PointerValue),
    SeedChain m p ws →
    iprop(([∗map] i ↦ c ∈ m, cellOwn (GF := GF) i (.own 1) c)) ⊢
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
  | cons v vs ih =>
    intro m p hseed
    obtain ⟨id, aN, q, bs, m', hp, h0, h1, hlen, hval, hnext, hdisj, rfl,
      hseed'⟩ := hseed
    subst hp
    iintro Hm
    icases (BigSepM.bigSepM_union hdisj).1 $$ Hm with ⟨H1, Hrest⟩
    iapply isList_cons_intro id aN q bs v vs h0 h1 hlen hval hnext
    isplitl [H1]
    · iapply (BigSepM.bigSepM_singleton).1 $$ H1
    · iapply ih m' q hseed' $$ Hrest

/-- LIST-REVERSE, END TO END: driving the REAL engine ({step_ctx →
    sequential discharge} at the proc-carrying thread, labels tied
    through `core_run_state.labeled`) on the authored in-place
    reversal, from any memory carrying a seeded input chain: the
    engine never kills, never derails, and any delivered value is a
    POINTER whose final-heap chain is `xs.reverse` — the reversed
    list, in place (`ChainAt`: per-node CellCoh + field decode facts
    about the FINAL MemState). Partial correctness; fuel hypotheses
    are the engine's own budgets (interim in-budget form). -/
theorem list_reverse_certified {GF : BundledGFunctors} [SpikeGpreS GF]
    (sbty : core_base_type) (xs : List Int) (head : CerbMem.PointerValue)
    (m₀ : SpikeHeapF SpikeCell) (hseed : SeedChain m₀ head xs)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem) (hcoh : Coh σ₀ m₀)
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 6 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 5 + nsteps ≤ lemDefaultFuel) :
    let prog := lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty head
    let rs := lrRS loc ann ra mo pbty cbty bbty nbty ubty
    (∀ r, driveJ rs aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread lrProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      ∃ p' : CerbMem.PointerValue, v = ptrVal p' ∧
        ChainAt σ' p' xs.reverse) := by
  intro prog rs
  refine engine_adequacyJ (GF := GF)
    (lrRS_labeledAt loc ann ra mo pbty cbty bbty nbty ubty)
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := lrQ_inv loc ann ra mo pbty cbty bbty nbty ubty hl
      exact lrBody_fragJ loc ann ra mo bbty nbty ubty hlib)
    prog fmapEmpty [] σ₀ m₀
    (.save (lrBody_fragJ loc ann ra mo bbty nbty ubty hlib)) hcoh
    (fun v σ' => ∃ p' : CerbMem.PointerValue, v = ptrVal p' ∧
      ChainAt σ' p' xs.reverse)
    ?_ nsteps aids
    (by rw [show esize prog = 6 from rfl]; omega)
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := lrQ_inv loc ann ra mo pbty cbty bbty nbty ubty hl
      rw [show esize (lrBody loc ann ra mo bbty nbty ubty) = 5 from rfl]
      omega)
  intro inst
  exact (seedChain_isList xs m₀ head hseed).trans
    (lr_wp_readout loc ann ra mo pbty cbty bbty nbty ubty xs lrProcSym rs
      (lrRS_labeledAt loc ann ra mo pbty cbty bbty nbty ubty) sbty head)

/-! ## THE CONCRETE DEMONSTRATION: a seeded 3-node list [1, 2, 3]
(engine-serialized byte images; every decode fact discharges by
`rfl` — the executable face of the exhibit) -/

/-- A stored long-value image (the engine's own serialization). -/
def valImg (v : Int) : List CerbMem.AbsByte :=
  imgOf (CerbMem.integerValueMval (.Signed .Long) (CerbMem.integerIval v))

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

/-- `get?` over the (term-level) union — the Iris lemma at the
    union spelling `SeedChain` uses. -/
theorem get?_union' (m₁ m₂ : SpikeHeapF SpikeCell) (k : Int) :
    Iris.Std.PartialMap.get? (Iris.Std.PartialMap.union m₁ m₂) k =
      (Iris.Std.PartialMap.get? m₁ k).orElse
        (fun _ => Iris.Std.PartialMap.get? m₂ k) :=
  Iris.Std.LawfulPartialMap.get?_union

open Iris.Std.PartialMap in
theorem demo_seed : SeedChain demoM demoHead [1, 2, 3] := by
  refine ⟨1, 4096, cellPtr 2 8192, demoBytes 1 (cellPtr 2 8192),
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
  refine ⟨2, 8192, cellPtr 3 12288, demoBytes 2 (cellPtr 3 12288),
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
  refine ⟨3, 12288, nullNode, demoBytes 3 nullNode,
    (∅ : SpikeHeapF SpikeCell),
    rfl, by omega, by omega, rfl,
    (fun lum fpm ad => rfl), (fun lum fpm ad => rfl), ?_, rfl, ⟨rfl, rfl⟩⟩
  · intro k hk
    obtain ⟨h1, h2⟩ := hk
    rw [Iris.Std.LawfulPartialMap.get?_empty] at h2
    cases h2

/-- THE DEMONSTRATION INSTANCE: reversing the seeded 3-node list
    [1, 2, 3] — any delivered value is a pointer whose final-heap
    chain is [3, 2, 1]. -/
theorem list_reverse_demo {GF : BundledGFunctors} [SpikeGpreS GF]
    (sbty : core_base_type)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem) (hcoh : Coh σ₀ demoM)
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 6 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 5 + nsteps ≤ lemDefaultFuel) :
    let prog := lrProg loc ann ra mo sbty pbty cbty bbty nbty ubty demoHead
    let rs := lrRS loc ann ra mo pbty cbty bbty nbty ubty
    (∀ r, driveJ rs aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread lrProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread lrProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      ∃ p' : CerbMem.PointerValue, v = ptrVal p' ∧
        ChainAt σ' p' [3, 2, 1]) :=
  list_reverse_certified (GF := GF) loc ann ra mo pbty cbty bbty nbty ubty sbty
    [1, 2, 3] demoHead demoM demo_seed hlib σ₀ hcoh nsteps aids hfuel hfuel2

end LrDrive


end CerberusHeapLang
