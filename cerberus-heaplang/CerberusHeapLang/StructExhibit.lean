/-
CerberusHeapLang.StructExhibit — THE FRESH-CLIENT TEST (foundations
Phase 2, the audit's acceptance test 2).

A two-field struct update: layout `{ int x @ 0; int y @ 8 }` inside
one 16-byte allocation (`int[4]` — field widths 4, offsets 0/8 with
a padding gap: a DIFFERENT layout from both prior clients — the
array exhibit iterates 4-byte elements contiguously, the list nodes
are two 8-byte fields). The program stores both fields through
INTERIOR typed stores and is certified end-to-end against the
engine's drive.

THE POINT: this module contains ZERO core-logic content — no
WP/WPS lifting proof, no state-interpretation opening, no new memM
seam. Every rule used is a one-line instance of the generic
typed-subrange rules (`wps_store_cell_at`), the readout goes through
the core `cellOwn_cellCoh`, and the byte algebra is the core splice
laws at this layout's offsets. Recreating the proof for another
layout changes only the offsets, sizes, and decode facts (audit
Phase-2 exit criterion).

Also here: THE ALLOCATION CLIENT (`struct_create_store_wps` +
`struct_create_store_adequacy`) — allocate a fresh struct and
initialize its x field. CONVERTED at alloc arc P2 (charter items
1-2): the client consumes the PUBLIC `wps_create` from the abstract
capacity `allocCap [⟨align, structTy⟩]` (no cursor vocabulary; the
program BINDS the fresh pointer with `lets p = create(...)` and
stores through the bound symbol), and the adequacy theorem launches
it against the real engine from the production cold-start memory
through `spike_engine_adequacy_alloc`/`launchResources` — the
partial-lane allocation consumer of the R-01 closure test.
-/
import CerberusHeapLang.API
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.ProdEntry

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic

/-! ## The layout -/

/-- The struct's allocation type: one 16-byte object (`int[4]` — the
    two fields live at element offsets 0 and 2; elements 1 and 3 are
    padding). -/
def structTy : ctype := Ctype [] (.Array0 intTy (some 4))

theorem structTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds structTy = 16 := rfl

theorem structTy_nonatomic : atomicTy structTy = false := rfl

/-- The int-array decode never consults the union-member or
    function-pointer tables (the layout's inertness fact — the same
    shape as the list exhibit's `nodeTy_dec_indep`). -/
theorem structTy_dec_indep {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (addr : Int) (bs : List CerbMem.AbsByte) :
    CerbMem.reconstructValue tds lum fpm addr structTy bs =
      CerbMem.reconstructValue tds [] [] addr structTy bs := rfl

theorem structTy_decIndep {tds : CerbTags.TagDefsMap} (a : Int) (bs : List CerbMem.AbsByte) :
    decIndep tds a structTy bs :=
  fun lum fpm => structTy_dec_indep lum fpm a bs

/-- Field offsets. -/
def fieldX : Nat := 0
def fieldY : Nat := 8

theorem fiveBytes_len {tds : CerbTags.TagDefsMap} : (fiveBytes tds).length = 4 := rfl
theorem sixBytes_len {tds : CerbTags.TagDefsMap} : (sixBytes tds).length = 4 := rfl

/-! ## The program: store both fields (interior typed stores) -/

/-- `lets _ = store(int, &s.x, 5) in store(int, &s.y, 6)` — the
    field pointers are interior pointers of the ONE allocation. -/
def progS (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type) (id a : Int) : CoreExpr :=
  sseqExpr bty
    (storeExpr loc ann intTy (cellPtr id (a + ((fieldX : Nat) : Int)))
      fiveVal mo)
    (storeExpr loc ann intTy (cellPtr id (a + ((fieldY : Nat) : Int)))
      sixVal mo')

/-- Cone membership: two canonical stores under strong sequencing. -/
theorem progS_frag (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type) (id a : Int)
    (hlib : CerbLocation.isLibraryLocation loc = false) :
    Frag (progS loc ann mo mo' bty id a) :=
  Frag.sseq (.store hlib) (.store hlib)

/-! ## The client field rules — one-line instances of the generic
typed-subrange store -/

section StructIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpec GF}

/-- FIELD-X STORE: `wps_store_cell_at` at offset 0, view type `int`,
    stored value 5. A client lemma — every premise is a closed
    layout/serialization fact. -/
theorem wps_struct_x_store {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (id a : Int) (bs : List CerbMem.AbsByte)
    (ρ : EnvStack) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a structTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a structTy
          (spliceBytes fieldX (fiveBytes M.tagDefs) bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann intTy
        (cellPtr id (a + ((fieldX : Nat) : Int))) fiveVal mo) ρ :=
  wps_store_cell_at loc ann id a structTy fieldX intTy fiveVal mo bs ρ
    five_encodes (by rw [structTy_size, show CerbMem.sizeofCtype M.tagDefs intTy = 4 from rfl]; decide)
    (five_storable M.tagDefs).compat (five_storable M.tagDefs).fpm (five_storable M.tagDefs).bytes_fpm
    ((five_storable M.tagDefs).len []) (structTy_decIndep a _)

/-- FIELD-Y STORE: the same generic rule at offset 8, stored value 6. -/
theorem wps_struct_y_store {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (id a : Int) (bs : List CerbMem.AbsByte)
    (ρ : EnvStack) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a structTy bs) ∗
      (∀ fp, cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a structTy
          (spliceBytes fieldY (sixBytes M.tagDefs) bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann intTy
        (cellPtr id (a + ((fieldY : Nat) : Int))) sixVal mo) ρ :=
  wps_store_cell_at loc ann id a structTy fieldY intTy sixVal mo bs ρ
    six_encodes (by rw [structTy_size, show CerbMem.sizeofCtype M.tagDefs intTy = 4 from rfl]; decide)
    (six_storable M.tagDefs).compat (six_storable M.tagDefs).fpm (six_storable M.tagDefs).bytes_fpm
    ((six_storable M.tagDefs).len []) (structTy_decIndep a _)

/-- The whole program at the statement layer: both fields updated,
    the allocation's image doubly spliced. -/
theorem struct_wps (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type) (id a : Int)
    (bs : List CerbMem.AbsByte) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) :
    iprop(cellOwn M.tagDefs (GF := GF) id (.own 1) (SpikeCell.mk a structTy bs)) ⊢
      wps M Ls
        (fun _ _ => iprop(cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a structTy
          (spliceBytes fieldY (sixBytes M.tagDefs) (spliceBytes fieldX (fiveBytes M.tagDefs) bs)))))
        (progS loc ann mo mo' bty id a) (ev0 :: evs) := by
  iintro Hs
  rw [show progS loc ann mo mo' bty id a =
    Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
      (storeExpr loc ann intTy (cellPtr id (a + ((fieldX : Nat) : Int)))
        fiveVal mo)
      (storeExpr loc ann intTy (cellPtr id (a + ((fieldY : Nat) : Int)))
        sixVal mo')) from rfl]
  iapply wps_seq
  iapply wps_struct_x_store loc ann mo id a bs (ev0 :: evs)
  isplitl [Hs]
  · iexact Hs
  iintro %fp Hs
  iapply wps_struct_y_store loc ann mo' id a
    (spliceBytes fieldX (fiveBytes M.tagDefs) bs) (ev0 :: evs)
  isplitl [Hs]
  · iexact Hs
  iintro %fp' Hs
  iexact Hs

/-- Vacuous block specifications (no labels at the straight-line
    profile). -/
theorem struct_blockSpecs (id a : Int) (bs : List CerbMem.AbsByte) :
    ⊢ blockSpecs (GF := GF) spikeCtx (fun _ _ _ => iprop(False))
      (fun _ _ => iprop(cellOwn spikeCtx.tagDefs (hlc := hlc) id (.own 1) (SpikeCell.mk a structTy
        (spliceBytes fieldY (sixBytes spikeCtx.tagDefs) (spliceBytes fieldX (fiveBytes spikeCtx.tagDefs) bs))))) :=
  blockSpecs_intro fun l _ _ _ _ _ hl => (spikeCtx_labels_none l hl).elim

end StructIris

section StructReadout

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]

/-- The base-WP face with the engine readout: the final memory holds
    the doubly-spliced image at the allocation. -/
theorem struct_wp_readout (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (mo mo' : memory_order)
    (bty : core_base_type) (id a : Int) (bs : List CerbMem.AbsByte) :
    iprop(cellOwn spikeCtx.tagDefs (hlc := .hasLC) (GF := GF) id (.own 1)
        (SpikeCell.mk a structTy bs)) ⊢
      WP (⟨progS loc ann mo mo' bty id a, spikeEnv, spikeCtx⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CellCoh spikeCtx.tagDefs σ' id ⟨a, structTy,
              spliceBytes fieldY (sixBytes spikeCtx.tagDefs)
                (spliceBytes fieldX (fiveBytes spikeCtx.tagDefs) bs)⟩⌝) }} := by
  refine (struct_wps (M := spikeCtx) (Ls := fun _ _ _ => iprop(False))
    loc ann mo mo' bty id a bs fmapEmpty []).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((struct_blockSpecs id a bs).trans
      (wps_sound (progS loc ann mo mo' bty id a) spikeEnv))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  refine wp_mono fun w => ?_
  -- alloc arc P4.1: the PUBLIC single-cell readout (`cellOwn_readout`,
  -- Adequacy.lean) — no state-interpretation opening in this module.
  exact cellOwn_readout spikeCtx.tagDefs id (.own 1)
    ⟨a, structTy, spliceBytes fieldY (sixBytes spikeCtx.tagDefs)
      (spliceBytes fieldX (fiveBytes spikeCtx.tagDefs) bs)⟩

end StructReadout

/-! ## THE ACCEPTANCE THEOREM (engine vocabulary only) -/

open Iris.Std.PartialMap in
/-- STRUCT UPDATE, END TO END: driving the REAL engine on the
    two-field update, from any memory carrying the seeded struct
    cell: never killed, never derailed, and any completed run's
    final memory reads back BOTH fields updated — 5's image at the x
    field, 6's image at the y field (interior typed stores through
    ONE allocation; the padding gap and the rest of the frame ride
    untouched inside the spliced image). ZERO core-logic edits were
    made for this module (audit Phase-2 acceptance test 2). -/
theorem struct_update_certified {GF : BundledGFunctors} [SpikeGpreS GF]
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type)
    (id a : Int) (bs : List CerbMem.AbsByte)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem)
    (hcoh : Coh fmapEmpty σ₀ ((Iris.Std.PartialMap.singleton id
      (SpikeCell.mk a structTy bs)) : SpikeHeapF SpikeCell))
    (n : Nat) (aids : Nat → Nat)
    (hfuel : 2 + n ≤ lemDefaultFuel) :
    (∀ r, drive aids n (spikeThread (progS loc ann mo mo' bty id a)) σ₀ ≠
      .killed r) ∧
    (drive aids n (spikeThread (progS loc ann mo mo' bty id a)) σ₀ ≠
      .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      drive aids n (spikeThread (progS loc ann mo mo' bty id a)) σ₀ =
        .done v σ' →
      CerbMem.readBytesFrom σ' (a + ((fieldX : Nat) : Int)) 4 = (fiveBytes fmapEmpty) ∧
      CerbMem.readBytesFrom σ' (a + ((fieldY : Nat) : Int)) 4 = (sixBytes fmapEmpty)) := by
  have hbs : bs.length = 16 := by
    have h := (hcoh.cells id _ (Iris.Std.LawfulPartialMap.get?_singleton_eq rfl)).len
    rw [structTy_size] at h
    exact h
  have hres := spike_engine_adequacy (GF := GF)
    (progS loc ann mo mo' bty id a) σ₀
    (Iris.Std.PartialMap.singleton id (SpikeCell.mk a structTy bs))
    (progS_frag loc ann mo mo' bty id a hlib) hcoh
    (fun _ σ' => CellCoh fmapEmpty σ' id ⟨a, structTy,
      spliceBytes fieldY (sixBytes fmapEmpty) (spliceBytes fieldX (fiveBytes fmapEmpty) bs)⟩)
    (by
      intro inst
      refine (BigSepM.bigSepM_singleton).1.trans ?_
      refine (struct_wp_readout loc ann mo mo' bty id a bs).trans ?_
      refine wp_mono fun w => ?_
      iintro H
      iexact H)
    n aids
    (by rw [show esize (progS loc ann mo mo' bty id a) = 2 from rfl]
        exact hfuel)
  refine ⟨hres.1, hres.2.1, fun v σ' hd => ?_⟩
  have hcc := hres.2.2 v σ' hd
  -- read the two field slices back out of the spliced image
  have hlen1 : (spliceBytes fieldX (fiveBytes fmapEmpty) bs).length = 16 := by
    rw [spliceBytes_length fieldX (fiveBytes fmapEmpty) bs (by rw [fiveBytes_len, hbs]; decide)]
    exact hbs
  have hlen2 : (spliceBytes fieldY (sixBytes fmapEmpty)
      (spliceBytes fieldX (fiveBytes fmapEmpty) bs)).length = 16 := by
    rw [spliceBytes_length fieldY (sixBytes fmapEmpty) _
      (by rw [sixBytes_len, hlen1]; decide)]
    exact hlen1
  have hread : CerbMem.readBytesFrom σ' a 16 =
      spliceBytes fieldY (sixBytes fmapEmpty) (spliceBytes fieldX (fiveBytes fmapEmpty) bs) := by
    have h := hcc.bytes
    rw [structTy_size] at h
    exact h
  have hx : CerbMem.readBytesFrom σ' (a + ((fieldX : Nat) : Int)) 4 =
      (fiveBytes fmapEmpty) := by
    rw [readBytesFrom_sub σ' a 16 _ hread fieldX 4 (by decide)]
    rw [spliceBytes_slice_below fieldY (sixBytes fmapEmpty) _
      (by rw [sixBytes_len, hlen1]; decide) fieldX 4 (by decide)]
    exact spliceBytes_slice_self fieldX (fiveBytes fmapEmpty) bs
      (by rw [fiveBytes_len, hbs]; decide)
  have hy : CerbMem.readBytesFrom σ' (a + ((fieldY : Nat) : Int)) 4 =
      (sixBytes fmapEmpty) := by
    rw [readBytesFrom_sub σ' a 16 _ hread fieldY 4 (by decide)]
    exact spliceBytes_slice_self fieldY (sixBytes fmapEmpty)
      (spliceBytes fieldX (fiveBytes fmapEmpty) bs)
      (by rw [sixBytes_len, hlen1]; decide)
  exact ⟨hx, hy⟩

/-! ## THE VIEW AND FRACTION CLIENTS (alloc arc P4.1 — the R-06 closure)

Every advertised law of the view algebra with a compiling consumer:
- `struct_wps_views`: the SAME two-field update, proved through
  DISJOINT TYPED FIELD VIEWS — the whole-struct view is split into
  the x field, the padding, the y field and the tail
  (`pointsToView_split`, three times: `int[4] = int ⊕ int[3]`,
  `int[3] = int ⊕ int[2]`, `int[2] = int ⊕ int`), each field is
  updated THROUGH ITS OWN VIEW by the generic full-ownership store
  (`wps_store_at`), and the four views are REJOINED into the
  whole-struct view (`pointsToView_join`, three times). Metadata
  fractions halve at each split and add back at each join; no
  splice algebra appears (the byte image is literally the
  concatenation of the field images). `struct_wps_views_cell` is
  the same statement at the whole-cell bundle (`cellOwn_view`).
- `struct_x_read_frac_wps`: a READ at ANY fraction `q` of the x
  field's view (a proper fraction when `q < 1`): the load delivers
  the decode and returns the view at the same fraction
  (`wps_load_at` at fractions).
- `struct_x_read_shared_wps`: THE SHARED READER — the full view is
  split into two halves (`pointsToView_fractional`), one half is
  lent to the read, the halves are rejoined: the whole comes back.
- `cell_read_shared_wps`: TWO READERS, ONE POINTER, at the
  points-to bundle — each holds a half of the pointer with ITS OWN
  account of the contents; the load goes through the first; the
  halves recombine into full ownership, AGREEMENT
  (`pointsToCell_combine`) forcing the accounts to coincide.
- `struct_x_read_persist_wps`: READ, THEN KEEP THE BOUNDS FOREVER —
  after the read the client trades its metadata fraction for
  PERSISTENT allocation knowledge (`pointsToView_persist`, a ghost
  update inside the statement logic through `wps_fupd`) and hands
  out the in-bounds fact `locInBounds` alongside the view
  (`pointsToView_locInBounds` — the persistence law at work). -/

section StructViews

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpec GF}

/-- The intermediate view types of the split: the struct minus its
    first field (`int[3]`, 12 bytes) and the last two fields
    (`int[2]`, 8 bytes). -/
def int3Ty : ctype := Ctype [] (.Array0 intTy (some 3))
def int2Ty : ctype := Ctype [] (.Array0 intTy (some 2))

theorem int3Ty_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds int3Ty = 12 := rfl
theorem int2Ty_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds int2Ty = 8 := rfl
theorem intTy_size' {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds intTy = 4 := rfl

/-- The five image decodes back to `fiveMval` at any address and any
    side tables (the table- and address-independent int decode). -/
theorem five_reconstruct {tds : CerbTags.TagDefsMap} (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (ad : Int) :
    CerbMem.reconstructValue tds lum fpm ad intTy (fiveBytes tds) = fiveMval := rfl

theorem five_fromMemValue : (valueFromMemValue fiveMval).2 = fiveVal := rfl

theorem five_loadTrap : loadTrapV intTy fiveMval = false := rfl

/-- THE VIEW CLIENT: split → update through the field views → join. -/
theorem struct_wps_views (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type) (id a : Int)
    (b0 b1 b2 b3 : List CerbMem.AbsByte)
    (h0 : b0.length = 4) (h1 : b1.length = 4) (h2 : b2.length = 4)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    pointsToView M.tagDefs (GF := GF) id a structTy 0 (.own 1) (.own 1) structTy
        (b0 ++ (b1 ++ (b2 ++ b3))) ⊢
      wps M Ls
        (fun _ _ => pointsToView M.tagDefs id a structTy 0 (.own 1) (.own 1) structTy
          (fiveBytes M.tagDefs ++ (b1 ++ (sixBytes M.tagDefs ++ b3))))
        (progS loc ann mo mo' bty id a) (ev0 :: evs) := by
  -- THE SPLITS (Lean-level instances of `pointsToView_split`; the
  -- fraction arithmetic is `Qp.half_add_half`).
  have s1 : pointsToView M.tagDefs (GF := GF) id a structTy 0 (.own 1) (.own 1) structTy
        (b0 ++ (b1 ++ (b2 ++ b3))) ⊢
      iprop(pointsToView M.tagDefs id a structTy 0 (.own (Qp.half 1)) (.own 1) intTy b0 ∗
        pointsToView M.tagDefs id a structTy 4 (.own (Qp.half 1)) (.own 1) int3Ty
          (b1 ++ (b2 ++ b3))) := by
    have := pointsToView_split M.tagDefs (GF := GF) id a structTy 0 (Qp.half 1) (Qp.half 1)
      (.own 1) structTy intTy int3Ty b0 (b1 ++ (b2 ++ b3))
      (by rw [structTy_size, intTy_size', int3Ty_size]) h0
    rw [Qp.half_add_half, show 0 + CerbMem.sizeofCtype M.tagDefs intTy = 4 from rfl] at this
    exact this
  have s2 : pointsToView M.tagDefs (GF := GF) id a structTy 4 (.own (Qp.half 1)) (.own 1) int3Ty
        (b1 ++ (b2 ++ b3)) ⊢
      iprop(pointsToView M.tagDefs id a structTy 4 (.own (Qp.half (Qp.half 1))) (.own 1)
          intTy b1 ∗
        pointsToView M.tagDefs id a structTy 8 (.own (Qp.half (Qp.half 1))) (.own 1) int2Ty
          (b2 ++ b3)) := by
    have := pointsToView_split M.tagDefs (GF := GF) id a structTy 4 (Qp.half (Qp.half 1))
      (Qp.half (Qp.half 1)) (.own 1) int3Ty intTy int2Ty b1 (b2 ++ b3)
      (by rw [int3Ty_size, intTy_size', int2Ty_size]) h1
    rw [Qp.half_add_half, show 4 + CerbMem.sizeofCtype M.tagDefs intTy = 8 from rfl] at this
    exact this
  have s3 : pointsToView M.tagDefs (GF := GF) id a structTy 8 (.own (Qp.half (Qp.half 1)))
        (.own 1) int2Ty (b2 ++ b3) ⊢
      iprop(pointsToView M.tagDefs id a structTy 8 (.own (Qp.half (Qp.half (Qp.half 1))))
          (.own 1) intTy b2 ∗
        pointsToView M.tagDefs id a structTy 12 (.own (Qp.half (Qp.half (Qp.half 1))))
          (.own 1) intTy b3) := by
    have := pointsToView_split M.tagDefs (GF := GF) id a structTy 8
      (Qp.half (Qp.half (Qp.half 1))) (Qp.half (Qp.half (Qp.half 1))) (.own 1) int2Ty intTy
      intTy b2 b3 (by rw [int2Ty_size, intTy_size']) h2
    rw [Qp.half_add_half, show 8 + CerbMem.sizeofCtype M.tagDefs intTy = 12 from rfl] at this
    exact this
  -- THE JOINS (instances of `pointsToView_join`, fractions adding back).
  have j3 : iprop(pointsToView M.tagDefs (GF := GF) id a structTy 8
          (.own (Qp.half (Qp.half (Qp.half 1)))) (.own 1) intTy
          (CerbMem.memValueToBytes M.tagDefs [] sixMval).2 ∗
        pointsToView M.tagDefs id a structTy 12 (.own (Qp.half (Qp.half (Qp.half 1))))
          (.own 1) intTy b3) ⊢
      pointsToView M.tagDefs id a structTy 8 (.own (Qp.half (Qp.half 1))) (.own 1) int2Ty
        ((CerbMem.memValueToBytes M.tagDefs [] sixMval).2 ++ b3) := by
    have := pointsToView_join M.tagDefs (GF := GF) id a structTy 8
      (Qp.half (Qp.half (Qp.half 1))) (Qp.half (Qp.half (Qp.half 1))) (.own 1) int2Ty intTy
      intTy (CerbMem.memValueToBytes M.tagDefs [] sixMval).2 b3 (by rw [int2Ty_size, intTy_size'])
      (by rw [int2Ty_size, structTy_size]; decide)
    rw [Qp.half_add_half, show 8 + CerbMem.sizeofCtype M.tagDefs intTy = 12 from rfl] at this
    exact this
  have j2 : iprop(pointsToView M.tagDefs (GF := GF) id a structTy 4
          (.own (Qp.half (Qp.half 1))) (.own 1) intTy b1 ∗
        pointsToView M.tagDefs id a structTy 8 (.own (Qp.half (Qp.half 1))) (.own 1) int2Ty
          ((CerbMem.memValueToBytes M.tagDefs [] sixMval).2 ++ b3)) ⊢
      pointsToView M.tagDefs id a structTy 4 (.own (Qp.half 1)) (.own 1) int3Ty
        (b1 ++ ((CerbMem.memValueToBytes M.tagDefs [] sixMval).2 ++ b3)) := by
    have := pointsToView_join M.tagDefs (GF := GF) id a structTy 4 (Qp.half (Qp.half 1))
      (Qp.half (Qp.half 1)) (.own 1) int3Ty intTy int2Ty b1
      ((CerbMem.memValueToBytes M.tagDefs [] sixMval).2 ++ b3)
      (by rw [int3Ty_size, intTy_size', int2Ty_size])
      (by rw [int3Ty_size, structTy_size]; decide)
    rw [Qp.half_add_half, show 4 + CerbMem.sizeofCtype M.tagDefs intTy = 8 from rfl] at this
    exact this
  have j1 : iprop(pointsToView M.tagDefs (GF := GF) id a structTy 0 (.own (Qp.half 1)) (.own 1)
          intTy (CerbMem.memValueToBytes M.tagDefs [] fiveMval).2 ∗
        pointsToView M.tagDefs id a structTy 4 (.own (Qp.half 1)) (.own 1) int3Ty
          (b1 ++ ((CerbMem.memValueToBytes M.tagDefs [] sixMval).2 ++ b3))) ⊢
      pointsToView M.tagDefs id a structTy 0 (.own 1) (.own 1) structTy
        ((CerbMem.memValueToBytes M.tagDefs [] fiveMval).2 ++
          (b1 ++ ((CerbMem.memValueToBytes M.tagDefs [] sixMval).2 ++ b3))) := by
    have := pointsToView_join M.tagDefs (GF := GF) id a structTy 0 (Qp.half 1) (Qp.half 1)
      (.own 1) structTy intTy int3Ty (CerbMem.memValueToBytes M.tagDefs [] fiveMval).2
      (b1 ++ ((CerbMem.memValueToBytes M.tagDefs [] sixMval).2 ++ b3))
      (by rw [structTy_size, intTy_size', int3Ty_size]) (by rw [structTy_size]; decide)
    rw [Qp.half_add_half, show 0 + CerbMem.sizeofCtype M.tagDefs intTy = 4 from rfl] at this
    exact this
  -- THE PROGRAM, through the field views.
  iintro Hs
  icases s1 $$ Hs with ⟨Hx, Hr⟩
  icases s2 $$ Hr with ⟨Hp, Hr2⟩
  icases s3 $$ Hr2 with ⟨Hy, Ht⟩
  -- the field offsets are the literal view offsets (`fieldX = 0`,
  -- `fieldY = 8`, by `rfl`); the images are the serializations.
  rw [show progS loc ann mo mo' bty id a =
    Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
      (storeExpr loc ann intTy (cellPtr id (a + ((0 : Nat) : Int)))
        fiveVal mo)
      (storeExpr loc ann intTy (cellPtr id (a + ((8 : Nat) : Int)))
        sixVal mo')) from rfl]
  iapply wps_seq
  iapply wps_store_at loc ann id a structTy 0 intTy fiveVal mo (.own (Qp.half 1)) b0
    (ev0 :: evs) five_encodes (five_storable M.tagDefs).compat (five_storable M.tagDefs).fpm
    (five_storable M.tagDefs).bytes_fpm ((five_storable M.tagDefs).len [])
  isplitl [Hx]
  · iexact Hx
  iintro %fp Hx
  iapply wps_store_at loc ann id a structTy 8 intTy sixVal mo'
    (.own (Qp.half (Qp.half (Qp.half 1)))) b2 (ev0 :: evs) six_encodes
    (six_storable M.tagDefs).compat (six_storable M.tagDefs).fpm
    (six_storable M.tagDefs).bytes_fpm ((six_storable M.tagDefs).len [])
  isplitl [Hy]
  · iexact Hy
  iintro %fp' Hy
  unfold fiveBytes sixBytes
  iapply j1
  isplitl [Hx]
  · iexact Hx
  iapply j2
  isplitl [Hp]
  · iexact Hp
  iapply j3
  isplitl [Hy]
  · iexact Hy
  · iexact Ht

/-- The view client at the whole-cell bundle: `cellOwn_view` in and
    out (the image's decode inertness is the layout's `rfl` fact). -/
theorem struct_wps_views_cell (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type) (id a : Int)
    (b0 b1 b2 b3 : List CerbMem.AbsByte)
    (h0 : b0.length = 4) (h1 : b1.length = 4) (h2 : b2.length = 4)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    cellOwn M.tagDefs (GF := GF) id (.own 1)
        (SpikeCell.mk a structTy (b0 ++ (b1 ++ (b2 ++ b3)))) ⊢
      wps M Ls
        (fun _ _ => cellOwn M.tagDefs id (.own 1) (SpikeCell.mk a structTy
          (fiveBytes M.tagDefs ++ (b1 ++ (sixBytes M.tagDefs ++ b3)))))
        (progS loc ann mo mo' bty id a) (ev0 :: evs) := by
  iintro Hc
  icases (cellOwn_view M.tagDefs id (.own 1) _).1 $$ Hc with ⟨Hv, -⟩
  ihave HW := struct_wps_views loc ann mo mo' bty id a b0 b1 b2 b3 h0 h1 h2 ev0 evs $$ Hv
  iapply wps_wand _ _ $$ HW
  iintro %w %ρ' Hv'
  iapply (cellOwn_view M.tagDefs id (.own 1) _).2
  isplitl [Hv']
  · iexact Hv'
  · ipureintro
    exact structTy_decIndep a _

/-- FRACTIONAL READ: the x field (holding 5) read through its view at
    ANY fraction `q` — the load delivers 5 and the view comes back at
    the same fraction. -/
theorem struct_x_read_frac_wps (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (id a : Int) (q : Qp) (ρ : EnvStack) :
    pointsToView M.tagDefs (GF := GF) id a structTy fieldX (.own q) (.own q) intTy
        (fiveBytes M.tagDefs) ⊢
      wps M Ls
        (fun w _ => iprop(⌜∃ fp, w = SpikeVal.annot [DA_pos [] fp] fiveVal⌝ ∗
          pointsToView M.tagDefs id a structTy fieldX (.own q) (.own q) intTy
            (fiveBytes M.tagDefs)))
        (loadExpr loc ann intTy (cellPtr id (a + ((fieldX : Nat) : Int))) mo) ρ := by
  iintro Hv
  iapply wps_load_at loc ann id a structTy fieldX intTy mo (.own q) (.own q)
    (fiveBytes M.tagDefs) ρ (fun lum fpm => five_reconstruct lum fpm _) five_loadTrap
  isplitl [Hv]
  · iexact Hv
  iintro %fp Hv
  isplit
  · ipureintro
    exact ⟨fp, rfl⟩
  · iexact Hv

/-- THE SHARED READER: the full x-field view splits into two halves,
    one half is lent to the read, and the halves rejoin. -/
theorem struct_x_read_shared_wps (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (id a : Int) (ρ : EnvStack) :
    pointsToView M.tagDefs (GF := GF) id a structTy fieldX (.own 1) (.own 1) intTy
        (fiveBytes M.tagDefs) ⊢
      wps M Ls
        (fun w _ => iprop(⌜∃ fp, w = SpikeVal.annot [DA_pos [] fp] fiveVal⌝ ∗
          pointsToView M.tagDefs id a structTy fieldX (.own 1) (.own 1) intTy
            (fiveBytes M.tagDefs)))
        (loadExpr loc ann intTy (cellPtr id (a + ((fieldX : Nat) : Int))) mo) ρ := by
  have hsplit : pointsToView M.tagDefs (GF := GF) id a structTy fieldX (.own 1) (.own 1) intTy
        (fiveBytes M.tagDefs) ⊣⊢
      iprop(pointsToView M.tagDefs id a structTy fieldX (.own (Qp.half 1)) (.own (Qp.half 1))
          intTy (fiveBytes M.tagDefs) ∗
        pointsToView M.tagDefs id a structTy fieldX (.own (Qp.half 1)) (.own (Qp.half 1))
          intTy (fiveBytes M.tagDefs)) := by
    have := pointsToView_fractional M.tagDefs (GF := GF) id a structTy fieldX (Qp.half 1)
      (Qp.half 1) intTy (fiveBytes M.tagDefs)
    rw [Qp.half_add_half] at this
    exact this
  refine hsplit.1.trans ?_
  refine (BI.sep_mono (struct_x_read_frac_wps (Ls := Ls) loc ann mo id a (Qp.half 1) ρ)
    .rfl).trans ?_
  refine (wps_frame _ _).trans ?_
  iintro H
  iapply (wps_wand _ _) $$ H
  iintro %w %ρ' ⟨⟨%hw, Hv₁⟩, Hv₂⟩
  isplit
  · ipureintro
    exact hw
  · iapply hsplit.2
    isplitl [Hv₁]
    · iexact Hv₁
    · iexact Hv₂

/-- TWO READERS, ONE POINTER: each holds half of `pv` with its own
    account of the contents (`bs`, `bs'`); the load goes through the
    first; recombining forces the accounts to agree and returns full
    ownership. -/
theorem cell_read_shared_wps (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (pv : CerbMem.PointerValue) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ρ : EnvStack)
    (htrap : cellLoadTrap M.tagDefs ⟨addrOf pv, intTy, bs⟩ = false) :
    iprop(pointsToCell M.tagDefs (GF := GF) pv (.own (Qp.half 1)) intTy bs ∗
      pointsToCell M.tagDefs pv (.own (Qp.half 1)) intTy bs') ⊢
      wps M Ls
        (fun w _ => iprop(⌜∃ fp, w = SpikeVal.annot [DA_pos [] fp]
            (loadedVal M.tagDefs pv intTy bs)⌝ ∗
          pointsToCell M.tagDefs pv (.own 1) intTy bs))
        (loadExpr loc ann intTy pv mo) ρ := by
  have hc : iprop(pointsToCell M.tagDefs (GF := GF) pv (.own (Qp.half 1)) intTy bs ∗
        pointsToCell M.tagDefs pv (.own (Qp.half 1)) intTy bs') ⊢
      pointsToCell M.tagDefs pv (.own 1) intTy bs := by
    refine (pointsToCell_combine M.tagDefs pv (Qp.half 1) (Qp.half 1) intTy intTy bs bs').trans
      ?_
    rw [Qp.half_add_half]
    exact BI.sep_elim_right
  iintro ⟨H₁, H₂⟩
  iapply wps_load loc ann intTy pv mo (.own (Qp.half 1)) bs ρ htrap
  isplitl [H₁]
  · iexact H₁
  iintro %fp H₁
  isplit
  · ipureintro
    exact ⟨fp, rfl⟩
  · iapply hc
    isplitl [H₁]
    · iexact H₁
    · iexact H₂

/-- READ, THEN KEEP THE BOUNDS FOREVER: after the read the metadata
    fraction is traded for persistent allocation knowledge, and the
    in-bounds fact is handed out next to the (persistent-metadata)
    view. -/
theorem struct_x_read_persist_wps (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (id a : Int) (q : Qp) (dqb : DFrac) (ρ : EnvStack) :
    pointsToView M.tagDefs (GF := GF) id a structTy fieldX (.own q) dqb intTy
        (fiveBytes M.tagDefs) ⊢
      wps M Ls
        (fun w _ => iprop(⌜∃ fp, w = SpikeVal.annot [DA_pos [] fp] fiveVal⌝ ∗
          locInBounds M.tagDefs id a structTy fieldX (CerbMem.sizeofCtype M.tagDefs intTy) ∗
          pointsToView M.tagDefs id a structTy fieldX .discard dqb intTy
            (fiveBytes M.tagDefs)))
        (loadExpr loc ann intTy (cellPtr id (a + ((fieldX : Nat) : Int))) mo) ρ := by
  iintro Hv
  iapply wps_fupd
  iapply wps_load_at loc ann id a structTy fieldX intTy mo (.own q) dqb
    (fiveBytes M.tagDefs) ρ (fun lum fpm => five_reconstruct lum fpm _) five_loadTrap
  isplitl [Hv]
  · iexact Hv
  iintro %fp Hv
  imod (pointsToView_persist M.tagDefs id a structTy fieldX (.own q) dqb intTy
    (fiveBytes M.tagDefs)) $$ Hv with Hv
  imodintro
  isplit
  · ipureintro
    exact ⟨fp, rfl⟩
  · iapply pointsToView_locInBounds M.tagDefs id a structTy fieldX dqb intTy
      (fiveBytes M.tagDefs) $$ Hv

end StructViews

/-! ## THE ALLOCATION CLIENT (alloc arc P2, charter items 1-2)

The self-contained allocate-then-initialize program, proved through
the PUBLIC create rule from the abstract capacity `allocCap` alone —
no cursor vocabulary anywhere (the fresh pointer is bound by the
program's own `lets p = create(...)`, and the store goes through the
bound symbol) — and exported to the engine through the
allocation-aware launcher (`spike_engine_adequacy_alloc`): the
partial-lane allocation consumer the re-audit's R-01 acceptance test
names. NO operational proof terms in this section (no `Step.*`,
`engineSteps_*`, `driveJ_step`, `driverDone_step`). -/

section CreateConsumer

/-- The bound fresh-pointer symbol / the bound stored-value symbol
    (the store rule's operands must be non-values, so the constant
    rides through a binding too). -/
def structPSym : sym := Symbol "" 501 SD_None
def structVSym : sym := Symbol "" 502 SD_None

/-- `lets p = create(align, struct) in lets v = 5 in
    store(int, p, v)` — the x field (offset 0) of the fresh struct,
    initialized through the BOUND pointer. -/
def progCreateInit (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (pref : prefix0)
    (mo : memory_order) (pbty vbty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (symPat [] structPSym pbty)
    (createExpr loc ann (.IV aprov alignN) structTy pref)
    (Expr [] (Esseq (symPat [] structVSym vbty)
      (ofVal (.pure fiveVal))
      (storeOpRedex loc ann intTy (Pexpr [] () (PEsym structPSym))
        (Pexpr [] () (PEsym structVSym)) mo))))

/-- Cone membership. -/
theorem progCreateInit_frag (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (aprov : CerbMem.Provenance)
    (alignN : Int) (pref : prefix0) (mo : memory_order)
    (pbty vbty : core_base_type)
    (hlib : CerbLocation.isLibraryLocation loc = false) :
    Frag (progCreateInit loc ann aprov alignN pref mo pbty vbty) :=
  .sseq_sym (.create hlib)
    (.sseq_sym (frag_ofVal (.pure fiveVal))
      (.store_op hlib rfl rfl (.sym [] structPSym) (.sym [] structVSym)
        (by rw [show peDepth (Pexpr ([] : List annot) ()
            (PEsym structPSym)) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)
        (by rw [show peDepth (Pexpr ([] : List annot) ()
            (PEsym structVSym)) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)))

section CreateIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpec GF}

/-- The head frame after the two binds. -/
abbrev structFrame (p : CerbMem.PointerValue) (f : Fmap sym value) :
    Fmap sym value :=
  envAdd structVSym fiveVal (envAdd structPSym (Vobject (OVpointer p)) f)

theorem structFrame_lookup_p {f : Fmap sym value} (hf : SymFrame f)
    (p : CerbMem.PointerValue) :
    fmapLookupBy symCmpK structPSym (structFrame p f) =
      some (Vobject (OVpointer p)) := by
  unfold structFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup hf symCmpK, if_pos (by decide +kernel)]

theorem structFrame_lookup_v {f : Fmap sym value} (hf : SymFrame f)
    (p : CerbMem.PointerValue) :
    fmapLookupBy symCmpK structVSym (structFrame p f) = some fiveVal := by
  unfold structFrame
  rw [envAdd_lookup (hf.add _ _) symCmpK, if_pos (by decide +kernel)]

/-- ALLOCATE-THEN-INITIALIZE, THE PUBLIC-RULE CLIENT (charter P2 item
    1): from the abstract capacity `allocCap [⟨align, structTy⟩]`
    ALONE, the whole program verifies — the create through the PUBLIC
    `wps_create` (existential pointer, no cursor vocabulary), the
    x-field store through the generic typed-subrange rule at the
    program-bound pointer. The postcondition returns the initialized
    fresh struct (existential pointer) and the spent capacity. -/
theorem struct_create_store_wps
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (pref : prefix0)
    (mo : memory_order) (pbty vbty : core_base_type)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hf : SymFrame ev0) (hex : M.extern = fmapEmpty) :
    iprop(allocCap M.tagDefs (GF := GF) [⟨alignN, structTy⟩]) ⊢
      wps M Ls
        (fun w _ => iprop(∃ p : CerbMem.PointerValue,
          ⌜w.val = Vunit⌝ ∗
          pointsToCell M.tagDefs p (.own 1) structTy
            (spliceBytes fieldX (fiveBytes M.tagDefs)
              (List.replicate (CerbMem.sizeofCtype M.tagDefs structTy) undefByte)) ∗
          allocCap M.tagDefs []))
        (progCreateInit loc ann aprov alignN pref mo pbty vbty)
        (ev0 :: evs) := by
  iintro Hcap
  rw [show progCreateInit loc ann aprov alignN pref mo pbty vbty =
    Expr [] (Esseq (symPat [] structPSym pbty)
      (createExpr loc ann (.IV aprov alignN) structTy pref)
      (Expr [] (Esseq (symPat [] structVSym vbty)
        (ofVal (.pure fiveVal))
        (storeOpRedex loc ann intTy (Pexpr [] () (PEsym structPSym))
          (Pexpr [] () (PEsym structVSym)) mo)))) from rfl]
  iapply wps_seq_sym
  iapply wps_create loc ann aprov ⟨alignN, structTy⟩ [] pref (ev0 :: evs)
    structTy_nonatomic (fun a => structTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p ⟨Hpt, Hcap, -⟩
  iexists (Vobject (OVpointer p))
  isplit
  · ipureintro
    rfl
  rw [update_env_sym structPSym pbty]
  iapply wps_seq_sym
  iapply wps_ofVal (.pure fiveVal)
  iexists fiveVal
  isplit
  · ipureintro
    rfl
  rw [update_env_sym structVSym vbty]
  icases (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  iapply wps_store_eval loc ann intTy _ _ mo _ rfl rfl
    (pv := p) (cv := fiveVal)
    (by rw [hex, evalPexpr_sym_empty]
        exact lookup_env_head (structFrame_lookup_p hf p) evs)
    (by rw [hex, evalPexpr_sym_empty]
        exact lookup_env_head (structFrame_lookup_v hf p) evs)
  rw [hpv, show (cellPtr id a) = cellPtr id (a + ((fieldX : Nat) : Int))
    from congrArg (cellPtr id) (by unfold fieldX; omega)]
  iapply wps_struct_x_store loc ann mo id a
    (List.replicate (CerbMem.sizeofCtype M.tagDefs structTy) undefByte) _
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp Hcell
  iexists p
  isplit
  · ipureintro
    rfl
  isplitl [Hcell]
  · iapply (pointsToCell_cellOwn_iff M.tagDefs _ _ _ _).mpr
    iexists id, a
    isplit
    · ipureintro
      exact hpv
    · iexact Hcell
  · iexact Hcap

end CreateIris

/-! ## THE ADEQUACY CONSUMER (charter P2 item 2 — the gap from a
local entailment to an engine-facing theorem CLOSES): the program at
the production cold-start memory, launched through the
allocation-aware launcher. -/

/-- The one-struct plan fits the production cold-start cursor
    (closed allocator arithmetic — the boundary evaluation of the
    concrete plan). -/
theorem struct_plan_fits :
    PlanFits fmapEmpty ⟨prodMem₀.lastAddress, prodMem₀.nextAllocId⟩
      [⟨8, structTy⟩] := by
  rw [prodMem₀_lastAddress, prodMem₀_nextAllocId, PlanFits_cons_iff]
  refine ⟨⟨freshBase errnoAddr 8 (CerbMem.sizeofCtype fmapEmpty structTy), 1 + 1⟩,
    ?_, PlanFits_nil fmapEmpty _⟩
  rw [advanceCursor_mk, structTy_size]
  exact if_pos ⟨by decide, by decide⟩

/-- ALLOCATE-THEN-INITIALIZE AT THE ENGINE (the R-01 partial-lane
    closure consumer; since P6.1 THE CONSUMER OF THE ALLOCATING
    PROJECTION `project_triple_alloc`): driving the REAL engine on the
    self-contained program from the production cold-start memory —
    launched through `project_triple_alloc`/`launchResources` with the
    one-request plan (`prodMem₀_launchCoh` supplies `LaunchCoh` at the
    empty footprint), verified ONLY through the public `wps_create` +
    the generic store rule — never kills, never derails, and any
    delivered value is unit with the final memory holding the
    initialized fresh struct (existential allocation id/address: the
    logic binds the pointer, the engine picks it). The statement is
    the `MemTripleU_alloc` body at `spikeCtx`, footprint `∅`, frame
    `∅`, unfolded; its post is discharged from the projected
    pure-consequence obligation by the `*_consequence` lemmas. -/
theorem struct_create_store_adequacy {GF : BundledGFunctors} [SpikeGpreS GF]
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (pref : prefix0) (mo : memory_order) (pbty vbty : core_base_type)
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (n : Nat) (aids : Nat → Nat) (hfuel : 3 + n ≤ lemDefaultFuel) :
    (∀ r, drive aids n (spikeThread
        (progCreateInit loc ann .Prov_none 8 pref mo pbty vbty)) prodMem₀ ≠
      .killed r) ∧
    (drive aids n (spikeThread
        (progCreateInit loc ann .Prov_none 8 pref mo pbty vbty)) prodMem₀ ≠
      .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      drive aids n (spikeThread
          (progCreateInit loc ann .Prov_none 8 pref mo pbty vbty)) prodMem₀ =
        .done v σ' →
      v = Vunit ∧ ∃ i a : Int, CellCoh fmapEmpty σ' i ⟨a, structTy,
        spliceBytes fieldX (fiveBytes fmapEmpty)
          (List.replicate (CerbMem.sizeofCtype fmapEmpty structTy) undefByte)⟩) := by
  -- the allocating projection at the spike profile: footprint ∅, plan
  -- [⟨8, structTy⟩], the Iris post = `struct_create_store_wps`'s post
  have h := project_triple_alloc (GF := GF) (M := spikeCtx) spikeCtx_wf
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
    (progCreateInit_frag loc ann .Prov_none 8 pref mo pbty vbty hlib)
    fmapEmpty [] (∅ : CellMap) [⟨8, structTy⟩]
    (fun w => iprop(∃ p : CerbMem.PointerValue,
      ⌜w.w.val = Vunit⌝ ∗
      pointsToCell fmapEmpty (GF := GF) p (.own 1) structTy
        (spliceBytes fieldX (fiveBytes fmapEmpty)
          (List.replicate (CerbMem.sizeofCtype fmapEmpty structTy) undefByte)) ∗
      allocCap fmapEmpty []))
    ?_
    (∅ : CellMap) (Iris.Std.LawfulPartialMap.disjoint_empty_right _) prodMem₀
    (by rw [show Iris.Std.PartialMap.union (∅ : CellMap) (∅ : CellMap) = ∅ from
          Iris.Std.LawfulPartialMap.union_empty_right]
        exact prodMem₀_launchCoh [⟨8, structTy⟩] struct_plan_fits)
    n aids
    (by rw [show esize (progCreateInit loc ann .Prov_none 8 pref mo
        pbty vbty) = 3 from rfl]
        exact hfuel)
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
  · refine ⟨h.1, h.2.1, fun v σ' hd => h.2.2 v σ' hd _ ?_⟩
    -- the pure-consequence obligation: the frame is empty, the post's
    -- points-to reads out through `pointsToCell_consequence`
    intro _ w hw mm mb mk hG
    subst hw
    refine .trans (BI.sep_mono .rfl
      (BI.sep_mono (BigSepM.bigSepM_empty).1 .rfl)) ?_
    refine .trans (BI.sep_mono .rfl BI.emp_sep.1) ?_
    refine (exists_consequence fun p => sep_consequence (pure_consequence _)
      (sep_consequence (pointsToCell_consequence hG fmapEmpty p (.own 1) structTy _)
        (BI.pure_intro True.intro))).trans ?_
    exact BI.pure_mono fun ⟨_, hval, ⟨id, a, _, hcc⟩, _⟩ => ⟨hval, id, a, hcc⟩
  · -- the Iris triple: `struct_create_store_wps` collapsed by `wps_sound`
    intro inst
    iintro ⟨-, Hcap⟩
    ihave HW := struct_create_store_wps (M := spikeCtx)
      (Ls := fun _ _ _ => iprop(False)) loc ann .Prov_none 8 pref mo
      pbty vbty fmapEmpty [] symFrame_empty rfl $$ Hcap
    ihave HWP : _ $$ [HW]
    · refine BI.emp_sep.2.trans (.trans (BI.sep_mono
        ((blockSpecs_intro fun l _ _ _ _ _ hl =>
          (spikeCtx_labels_none l hl).elim).trans
          (wps_sound (progCreateInit loc ann .Prov_none 8 pref mo pbty vbty)
            spikeEnv))
        .rfl) BI.wand_elim_left)
    iexact HWP

end CreateConsumer

end CerberusHeapLang
