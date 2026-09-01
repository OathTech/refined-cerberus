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
import CerberusHeapLang.Adequacy
import CerberusHeapLang.Wps
import CerberusHeapLang.EnvLaws
import CerberusHeapLang.ProdEntry

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
    iprop(allocCap (GF := GF) [⟨alignN, structTy⟩]) ⊢
      wps M Ls
        (fun w _ => iprop(∃ p : CerbMem.PointerValue,
          ⌜w.val = Vunit⌝ ∗
          pointsToCell p (.own 1) structTy
            (spliceBytes fieldX fiveBytes
              (List.replicate (CerbMem.sizeofCtype structTy) undefByte)) ∗
          allocCap []))
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
  icases (pointsToCell_cellOwn_iff _ _ _ _).mp $$ Hpt
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
    (List.replicate (CerbMem.sizeofCtype structTy) undefByte) _
  isplitl [Hcell]
  · iexact Hcell
  iintro %fp Hcell
  iexists p
  isplit
  · ipureintro
    rfl
  isplitl [Hcell]
  · iapply (pointsToCell_cellOwn_iff _ _ _ _).mpr
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
    PlanFits ⟨prodMem₀.lastAddress, prodMem₀.nextAllocId⟩
      [⟨8, structTy⟩] := by
  rw [prodMem₀_lastAddress, prodMem₀_nextAllocId, PlanFits_cons_iff]
  refine ⟨⟨freshBase errnoAddr 8 (CerbMem.sizeofCtype structTy), 1 + 1⟩,
    ?_, PlanFits_nil _⟩
  rw [advanceCursor_mk, structTy_size]
  exact if_pos ⟨by decide, by decide⟩

/-- ALLOCATE-THEN-INITIALIZE AT THE ENGINE (the R-01 partial-lane
    closure consumer): driving the REAL engine on the self-contained
    program from the production cold-start memory — launched through
    `spike_engine_adequacy_alloc`/`launchResources` with the
    one-request plan, verified ONLY through the public `wps_create` +
    the generic store rule — never kills, never derails, and any
    delivered value is unit with the final memory holding the
    initialized fresh struct (existential allocation id/address: the
    logic binds the pointer, the engine picks it). -/
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
      v = Vunit ∧ ∃ i a : Int, CellCoh σ' i ⟨a, structTy,
        spliceBytes fieldX fiveBytes
          (List.replicate (CerbMem.sizeofCtype structTy) undefByte)⟩) := by
  refine spike_engine_adequacy_alloc (GF := GF)
    (progCreateInit loc ann .Prov_none 8 pref mo pbty vbty)
    prodMem₀ (∅ : SpikeHeapF SpikeCell) [⟨8, structTy⟩]
    (progCreateInit_frag loc ann .Prov_none 8 pref mo pbty vbty hlib)
    (prodMem₀_launchCoh [⟨8, structTy⟩] struct_plan_fits)
    (fun v σ' => v = Vunit ∧ ∃ i a : Int, CellCoh σ' i ⟨a, structTy,
      spliceBytes fieldX fiveBytes
        (List.replicate (CerbMem.sizeofCtype structTy) undefByte)⟩)
    ?_ n aids
    (by rw [show esize (progCreateInit loc ann .Prov_none 8 pref mo
        pbty vbty) = 3 from rfl]
        exact hfuel)
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
  iapply wp_mono _ $$ HWP
  iintro %w ⟨%p, %hval, Hpt, -⟩
  icases (pointsToCell_cellOwn_iff _ _ _ _).mp $$ Hpt
    with ⟨%id, %a, %hpv, Hcell⟩
  iintro %σ2 %ns2 %κs2 %nt2 Hσ
  icases (stateInterp_iff σ2 ns2 κs2 nt2).mp $$ Hσ
    with ⟨%mm, %mb, %mk, %HG, Hmi, Hbi, Hki⟩
  ihave %Hcc : ⌜CellCoh σ2 id ⟨a, structTy,
      spliceBytes fieldX fiveBytes
        (List.replicate (CerbMem.sizeofCtype structTy) undefByte)⟩ ∧
      Iris.Std.PartialMap.get? mm id = some (metaOf
        (⟨a, structTy, spliceBytes fieldX fiveBytes
          (List.replicate (CerbMem.sizeofCtype structTy) undefByte)⟩ :
          SpikeCell))⌝ $$ [Hmi Hbi Hcell]
  · iapply cellOwn_cellCoh HG id (.own 1)
      ⟨a, structTy, spliceBytes fieldX fiveBytes
        (List.replicate (CerbMem.sizeofCtype structTy) undefByte)⟩
      $$ [$Hmi $Hbi $Hcell]
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact ⟨hval, id, a, Hcc.1⟩

end CreateConsumer

end CerberusHeapLang
