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

Also here: THE ALLOCATION CLIENT (`struct_create_store_wps`) —
`wps_create` consumed by an ordinary client: allocate a fresh
struct through the allocator-cursor resource and initialize its x
field (no cold-start hoisting, the allocation happens mid-derivation
on ghost-owned cursor arithmetic). SCOPE (2026-09-01 re-audit,
R-01): this is a LOCAL wps-level entailment whose premise ASSUMES
`cursorOwn` — no adequacy launcher grants that resource, so this
client does not reach an engine-facing (adequacy) theorem; the
launchable public allocation rule and its adequacy consumer are
alloc arc P1/P2.
-/
import CerberusHeapLang.Adequacy
import CerberusHeapLang.Wps

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic

/-! ## The layout -/

/-- The struct's allocation type: one 16-byte object (`int[4]` — the
    two fields live at element offsets 0 and 2; elements 1 and 3 are
    padding). -/
def structTy : ctype := Ctype [] (.Array0 intTy (some 4))

theorem structTy_size : CerbMem.sizeofCtype structTy = 16 := rfl

theorem structTy_nonatomic : atomicTy structTy = false := rfl

/-- The int-array decode never consults the union-member or
    function-pointer tables (the layout's inertness fact — the same
    shape as the list exhibit's `nodeTy_dec_indep`). -/
theorem structTy_dec_indep (lum : List (Int × identifier))
    (fpm : CerbMem.Funptrmap) (addr : Int) (bs : List CerbMem.AbsByte) :
    CerbMem.reconstructValue lum fpm addr structTy bs =
      CerbMem.reconstructValue [] [] addr structTy bs := rfl

theorem structTy_decIndep (a : Int) (bs : List CerbMem.AbsByte) :
    decIndep a structTy bs :=
  fun lum fpm => structTy_dec_indep lum fpm a bs

/-- Field offsets. -/
def fieldX : Nat := 0
def fieldY : Nat := 8

theorem fiveBytes_len : fiveBytes.length = 4 := rfl
theorem sixBytes_len : sixBytes.length = 4 := rfl

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
    iprop(cellOwn (GF := GF) id (.own 1) (SpikeCell.mk a structTy bs) ∗
      (∀ fp, cellOwn id (.own 1) (SpikeCell.mk a structTy
          (spliceBytes fieldX fiveBytes bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann intTy
        (cellPtr id (a + ((fieldX : Nat) : Int))) fiveVal mo) ρ :=
  wps_store_cell_at loc ann id a structTy fieldX intTy fiveVal mo bs ρ
    five_encodes (by rw [structTy_size]; decide)
    five_storable.compat five_storable.fpm five_storable.bytes_fpm
    (five_storable.len []) (structTy_decIndep a _)

/-- FIELD-Y STORE: the same generic rule at offset 8, stored value 6. -/
theorem wps_struct_y_store {Ψ : SpikeVal → EnvStack → IProp GF}
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo : memory_order) (id a : Int) (bs : List CerbMem.AbsByte)
    (ρ : EnvStack) :
    iprop(cellOwn (GF := GF) id (.own 1) (SpikeCell.mk a structTy bs) ∗
      (∀ fp, cellOwn id (.own 1) (SpikeCell.mk a structTy
          (spliceBytes fieldY sixBytes bs)) -∗
        Ψ (SpikeVal.annot [DA_pos [] fp] Vunit) ρ)) ⊢
      wps M Ls Ψ (storeExpr loc ann intTy
        (cellPtr id (a + ((fieldY : Nat) : Int))) sixVal mo) ρ :=
  wps_store_cell_at loc ann id a structTy fieldY intTy sixVal mo bs ρ
    six_encodes (by rw [structTy_size]; decide)
    six_storable.compat six_storable.fpm six_storable.bytes_fpm
    (six_storable.len []) (structTy_decIndep a _)

/-- The whole program at the statement layer: both fields updated,
    the allocation's image doubly spliced. -/
theorem struct_wps (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type) (id a : Int)
    (bs : List CerbMem.AbsByte) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) :
    iprop(cellOwn (GF := GF) id (.own 1) (SpikeCell.mk a structTy bs)) ⊢
      wps M Ls
        (fun _ _ => iprop(cellOwn id (.own 1) (SpikeCell.mk a structTy
          (spliceBytes fieldY sixBytes (spliceBytes fieldX fiveBytes bs)))))
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
    (spliceBytes fieldX fiveBytes bs) (ev0 :: evs)
  isplitl [Hs]
  · iexact Hs
  iintro %fp' Hs
  iexact Hs

/-- Vacuous block specifications (no labels at the straight-line
    profile). -/
theorem struct_blockSpecs (id a : Int) (bs : List CerbMem.AbsByte) :
    ⊢ blockSpecs (GF := GF) spikeCtx (fun _ _ _ => iprop(False))
      (fun _ _ => iprop(cellOwn (hlc := hlc) id (.own 1) (SpikeCell.mk a structTy
        (spliceBytes fieldY sixBytes (spliceBytes fieldX fiveBytes bs))))) :=
  blockSpecs_intro fun l _ _ _ _ _ hl => (spikeCtx_labels_none l hl).elim

end StructIris

section StructReadout

variable {GF : BundledGFunctors} [SpikeGS .hasLC GF]

/-- The base-WP face with the engine readout: the final memory holds
    the doubly-spliced image at the allocation. -/
theorem struct_wp_readout (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (mo mo' : memory_order)
    (bty : core_base_type) (id a : Int) (bs : List CerbMem.AbsByte) :
    iprop(cellOwn (hlc := .hasLC) (GF := GF) id (.own 1)
        (SpikeCell.mk a structTy bs)) ⊢
      WP (⟨progS loc ann mo mo' bty id a, spikeEnv, spikeCtx⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CellCoh σ' id ⟨a, structTy,
              spliceBytes fieldY sixBytes
                (spliceBytes fieldX fiveBytes bs)⟩⌝) }} := by
  refine (struct_wps (M := spikeCtx) (Ls := fun _ _ _ => iprop(False))
    loc ann mo mo' bty id a bs fmapEmpty []).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((struct_blockSpecs id a bs).trans
      (wps_sound (progS loc ann mo mo' bty id a) spikeEnv))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  refine wp_mono fun w => ?_
  -- Phase-4 tidy: the state-interpretation open/close lives in the
  -- core combinator; this module supplies only the coupling-
  -- conditional extraction (cellOwn_cellCoh).
  exact stateInterp_readout (fun σ' mm mb mk HG => by
    iintro ⟨Hs, Hmi, Hbi⟩
    ihave %Hcc : ⌜CellCoh σ' id ⟨a, structTy,
        spliceBytes fieldY sixBytes (spliceBytes fieldX fiveBytes bs)⟩ ∧
        Iris.Std.PartialMap.get? mm id = some (metaOf
          (⟨a, structTy, spliceBytes fieldY sixBytes
            (spliceBytes fieldX fiveBytes bs)⟩ : SpikeCell))⌝ $$ [Hmi Hbi Hs]
    · iapply cellOwn_cellCoh HG id (.own 1)
        ⟨a, structTy, spliceBytes fieldY sixBytes
          (spliceBytes fieldX fiveBytes bs)⟩ $$ [$Hmi $Hbi $Hs]
    ipureintro
    exact Hcc.1)

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
    (hcoh : Coh σ₀ ((Iris.Std.PartialMap.singleton id
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
      CerbMem.readBytesFrom σ' (a + ((fieldX : Nat) : Int)) 4 = fiveBytes ∧
      CerbMem.readBytesFrom σ' (a + ((fieldY : Nat) : Int)) 4 = sixBytes) := by
  have hbs : bs.length = 16 := by
    have h := (hcoh.cells id _ (Iris.Std.LawfulPartialMap.get?_singleton_eq rfl)).len
    rw [structTy_size] at h
    exact h
  have hres := spike_engine_adequacy (GF := GF)
    (progS loc ann mo mo' bty id a) σ₀
    (Iris.Std.PartialMap.singleton id (SpikeCell.mk a structTy bs))
    (progS_frag loc ann mo mo' bty id a hlib) hcoh
    (fun _ σ' => CellCoh σ' id ⟨a, structTy,
      spliceBytes fieldY sixBytes (spliceBytes fieldX fiveBytes bs)⟩)
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
  have hlen1 : (spliceBytes fieldX fiveBytes bs).length = 16 := by
    rw [spliceBytes_length fieldX fiveBytes bs (by rw [fiveBytes_len, hbs]; decide)]
    exact hbs
  have hlen2 : (spliceBytes fieldY sixBytes
      (spliceBytes fieldX fiveBytes bs)).length = 16 := by
    rw [spliceBytes_length fieldY sixBytes _
      (by rw [sixBytes_len, hlen1]; decide)]
    exact hlen1
  have hread : CerbMem.readBytesFrom σ' a 16 =
      spliceBytes fieldY sixBytes (spliceBytes fieldX fiveBytes bs) := by
    have h := hcc.bytes
    rw [structTy_size] at h
    exact h
  have hx : CerbMem.readBytesFrom σ' (a + ((fieldX : Nat) : Int)) 4 =
      fiveBytes := by
    rw [readBytesFrom_sub σ' a 16 _ hread fieldX 4 (by decide)]
    rw [spliceBytes_slice_below fieldY sixBytes _
      (by rw [sixBytes_len, hlen1]; decide) fieldX 4 (by decide)]
    exact spliceBytes_slice_self fieldX fiveBytes bs
      (by rw [fiveBytes_len, hbs]; decide)
  have hy : CerbMem.readBytesFrom σ' (a + ((fieldY : Nat) : Int)) 4 =
      sixBytes := by
    rw [readBytesFrom_sub σ' a 16 _ hread fieldY 4 (by decide)]
    exact spliceBytes_slice_self fieldY sixBytes
      (spliceBytes fieldX fiveBytes bs)
      (by rw [sixBytes_len, hlen1]; decide)
  exact ⟨hx, hy⟩

/-! ## THE ALLOCATION CLIENT (local — see the module header)

`create` used mid-derivation as an ordinary rule: the program
allocates a fresh struct and initializes its x field. The fresh
pointer is the CLOSED FORM of the allocator arithmetic
(`cellPtr nid (freshBase la align 16)`) — ownership of the
allocator-cursor resource is exactly what makes the address
well-defined, and the out-of-memory arm is excluded by the pure
`hnz` guard on owned state (no cold-start hoisting). LOCAL ONLY
(R-01): the `cursorOwn` premise is granted by no adequacy launcher,
so this theorem ends at `wps` — it is not an adequacy consumer. -/

section CreateConsumer

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpec GF}

/-- `lets _ = create(align, struct) in store(int, &fresh.x, 5)`. -/
def progCreateInit (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (pref : prefix0)
    (mo : memory_order) (bty : core_base_type) (la nid : Int) : CoreExpr :=
  sseqExpr bty
    (createExpr loc ann (.IV aprov alignN) structTy pref)
    (storeExpr loc ann intTy
      (cellPtr nid (freshBase la alignN (CerbMem.sizeofCtype structTy) +
        ((fieldX : Nat) : Int))) fiveVal mo)

/-- ALLOCATE-THEN-INITIALIZE: from cursor ownership alone, the fresh
    struct materializes (unspecified bytes), its x field is
    initialized through the generic subrange store, and the cursor
    advances. Every create premise is pure allocator arithmetic on
    owned state. -/
theorem struct_create_store_wps
    (loc : CerbLocation.Loc) (ann : core_run_annotation)
    (aprov : CerbMem.Provenance) (alignN : Int) (pref : prefix0)
    (mo : memory_order) (bty : core_base_type) (la nid : Int)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hnz : freshBase la alignN (CerbMem.sizeofCtype structTy) ≠ 0) :
    iprop(cursorOwn (GF := GF) ⟨la, nid⟩) ⊢
      wps M Ls
        (fun _ _ => iprop(
          cellOwn nid (.own 1) (SpikeCell.mk
            (freshBase la alignN (CerbMem.sizeofCtype structTy)) structTy
            (spliceBytes fieldX fiveBytes
              (List.replicate (CerbMem.sizeofCtype structTy) undefByte))) ∗
          cursorOwn ⟨freshBase la alignN (CerbMem.sizeofCtype structTy),
            nid + 1⟩))
        (progCreateInit loc ann aprov alignN pref mo bty la nid)
        (ev0 :: evs) := by
  iintro Hc
  rw [show progCreateInit loc ann aprov alignN pref mo bty la nid =
    Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
      (createExpr loc ann (.IV aprov alignN) structTy pref)
      (storeExpr loc ann intTy
        (cellPtr nid (freshBase la alignN (CerbMem.sizeofCtype structTy) +
          ((fieldX : Nat) : Int))) fiveVal mo)) from rfl]
  iapply wps_seq
  iapply wps_create loc ann aprov alignN structTy pref la nid (ev0 :: evs)
    (by rw [structTy_size]; decide) structTy_nonatomic hnz
    (structTy_decIndep _ _)
  isplitl [Hc]
  · iexact Hc
  iintro ⟨Hpt, Hc⟩
  icases (pointsToCell_cellOwn_iff _ _ _ _).mp $$ Hpt
    with ⟨%id', %a', %hpv, Hcell⟩
  obtain ⟨rfl, rfl⟩ : nid = id' ∧
      freshBase la alignN (CerbMem.sizeofCtype structTy) = a' := by
    unfold cellPtr at hpv
    injection hpv with h1 h2
    injection h1 with h1
    injection h2 with _ h2
    exact ⟨h1, h2⟩
  iapply wps_store_cell_at loc ann nid
    (freshBase la alignN (CerbMem.sizeofCtype structTy)) structTy fieldX
    intTy fiveVal mo
    (List.replicate (CerbMem.sizeofCtype structTy) undefByte) (ev0 :: evs)
    five_encodes (by rw [structTy_size]; decide)
    five_storable.compat five_storable.fpm five_storable.bytes_fpm
    (five_storable.len []) (structTy_decIndep _ _)
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp Hcell
  rw [show (fiveBytes : List CerbMem.AbsByte) =
    (CerbMem.memValueToBytes [] fiveMval).2 from rfl]
  isplitl [Hcell]
  · iexact Hcell
  · iexact Hc

end CreateConsumer

end CerberusHeapLang
