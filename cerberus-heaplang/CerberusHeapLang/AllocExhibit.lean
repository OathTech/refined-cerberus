/-
CerberusHeapLang.AllocExhibit — the PUBLIC allocation rules' local
consumers, and the smallest allocating program driven to the engine
from the production cold-start memory.

Contents:

- `alloc_two_creates_wps` — partial-judgment local consumer: TWO
  creates consume a two-element plan IN ORDER; the head request is
  consumed first and `allocCap` shrinks head-first at each step.
- `alloc_create_wpt` — total-judgment local consumer at the minimal
  budget `k = 2` (the rule `wpt_create`'s cost bound `2 ≤ k`, applied
  at exactly 2).
- `alloc_create_launch_smoke` — from the production cold-start memory
  `prodMem₀` (empty footprint, one errno allocation, plan `[⟨4, int⟩]`),
  a single `create` driven through `wpt_engine_boundU_alloc` DELIVERS
  at drive length exactly 2 — an unconditional engine `.done` equation
  whose proof consumes `wpt_create` and `launchResources` (deleting
  either breaks it). The delivered value is a pointer. Engine
  vocabulary only in the statement (GF discharged at the
  satisfiability witness `SpikeGF`).

The whole-program allocating exports — `struct_create_store_adequacy`
(StructExhibit.lean) at the drive, `exhibitA_prod`,
`counter_loop_certified_production` and
`list_reverse_certified_production` (ProdExhibit.lean,
ProdLoopExhibit.lean) on the shipped pipeline — go through the same
public rules (`wps_create`/`wpt_create`) and launchers.

Every create premise here is a closed layout fact of `intTy` (4-byte
scalar int; decode-inertness is `rfl` at every address). NO
operational proof terms: no `Step.*`, no per-step drive equations in
any proof body of this module.
-/
import CerberusHeapLang.API
import CerberusHeapLang.Examples.Layout
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.Exhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic

/-! ## intTy layout facts (closed, rfl) -/

theorem intTy_size {tds : CerbTags.TagDefsMap} : CerbMem.sizeofCtype tds intTy = 4 := rfl

theorem intTy_nonatomic : atomicTy intTy = false := rfl

/-- The scalar-int decode never consults the union-member or
    function-pointer tables — at ANY address and image (the
    address-independent inertness shape the public create rules
    take). -/
theorem intTy_decIndep {tds : CerbTags.TagDefsMap} (a : Int) (bs : List CerbMem.AbsByte) :
    decIndep tds a intTy bs := fun _ _ => rfl

/-- The unspecified fresh image of one int cell. -/
abbrev intUndefBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  List.replicate (CerbMem.sizeofCtype tds intTy) undefByte

/-! ## Local consumers (partial and total lanes) -/

section AllocIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- TWO CREATES CONSUME A TWO-ELEMENT PLAN IN ORDER (partial
    judgment): from capacity for
    `[⟨al₁,int⟩, ⟨al₂,int⟩]` alone, the sequenced pair of creates
    delivers TWO separately-owned fresh cells and the SPENT capacity
    `allocCap []`. The first create consumes the head request
    (returning `allocCap [⟨al₂,int⟩]` mid-derivation), the second
    consumes the rest — order is the plan's order. -/
theorem alloc_two_creates_wps {M : MachineCtx} {Ls : LabelSpec GF}
    (al₁ al₂ : Int) (pref₁ pref₂ : prefix0) (bty : core_base_type)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    iprop(allocCap M.tagDefs (GF := GF) [⟨al₁, intTy⟩, ⟨al₂, intTy⟩]) ⊢
      wps M Ls
        (fun _ _ => iprop(∃ p₁ p₂ : CerbMem.PointerValue,
          pointsToCell M.tagDefs p₁ (.own 1) intTy (intUndefBytes M.tagDefs) ∗
          pointsToCell M.tagDefs p₂ (.own 1) intTy (intUndefBytes M.tagDefs) ∗
          allocCap M.tagDefs []))
        (sseqExpr bty
          (createExpr loc0 empty_annotation (.IV .Prov_none al₁) intTy pref₁)
          (createExpr loc0 empty_annotation (.IV .Prov_none al₂) intTy pref₂))
        (ev0 :: evs) := by
  iintro Hcap
  rw [show sseqExpr bty
      (createExpr loc0 empty_annotation (.IV .Prov_none al₁) intTy pref₁)
      (createExpr loc0 empty_annotation (.IV .Prov_none al₂) intTy pref₂) =
    Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
      (createExpr loc0 empty_annotation (.IV .Prov_none al₁) intTy pref₁)
      (createExpr loc0 empty_annotation (.IV .Prov_none al₂) intTy pref₂))
    from rfl]
  iapply wps_seq
  iapply wps_create loc0 empty_annotation .Prov_none ⟨al₁, intTy⟩
    [⟨al₂, intTy⟩] pref₁ (ev0 :: evs) intTy_nonatomic
    (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p₁ ⟨Hpt₁, Hcap, -⟩
  iapply wps_create loc0 empty_annotation .Prov_none ⟨al₂, intTy⟩
    [] pref₂ (ev0 :: evs) intTy_nonatomic
    (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p₂ ⟨Hpt₂, Hcap, -⟩
  iexists p₁, p₂
  isplitl [Hpt₁]
  · iexact Hpt₁
  isplitl [Hpt₂]
  · iexact Hpt₂
  · iexact Hcap

/-- Total-judgment local consumer at the minimal budget: one create
    from a one-request plan, at `k = 2` exactly (1 create step + 1
    pure-value delivery — `wpt_create`'s cost bound). -/
theorem alloc_create_wpt {M : MachineCtx} {Ls : LabelSpecT GF}
    (al : Int) (pref : prefix0) (ρ : EnvStack) :
    iprop(allocCap M.tagDefs (GF := GF) [⟨al, intTy⟩]) ⊢
      wpt M Ls 2
        (fun _ _ => iprop(∃ p : CerbMem.PointerValue,
          pointsToCell M.tagDefs p (.own 1) intTy (intUndefBytes M.tagDefs) ∗ allocCap M.tagDefs []))
        (createExpr loc0 empty_annotation (.IV .Prov_none al) intTy pref)
        ρ := by
  iintro Hcap
  iapply wpt_create loc0 empty_annotation .Prov_none ⟨al, intTy⟩ [] pref ρ
    (Nat.le_refl 2) intTy_nonatomic (fun a => intTy_decIndep a _)
  isplitl [Hcap]
  · iexact Hcap
  iintro %p ⟨Hpt, Hcap, -⟩
  iexists p
  isplitl [Hpt]
  · iexact Hpt
  · iexact Hcap

end AllocIris

/-! ## The launcher smoke: the chain closes at the engine -/

/-- The one-request plan fits the production cold-start cursor
    `⟨errnoAddr, 1⟩` (closed allocator arithmetic). -/
theorem prod_one_int_plan_fits :
    PlanFits fmapEmpty ⟨prodMem₀.lastAddress, prodMem₀.nextAllocId⟩
      [⟨4, intTy⟩] := by
  rw [prodMem₀_lastAddress, prodMem₀_nextAllocId, PlanFits_cons_iff]
  refine ⟨⟨freshBase errnoAddr 4 (CerbMem.sizeofCtype fmapEmpty intTy), 1 + 1⟩,
    ?_, PlanFits_nil fmapEmpty _⟩
  rw [advanceCursor_mk, intTy_size]
  exact if_pos ⟨by decide, by decide⟩

/-- THE SMALLEST ALLOCATING PROGRAM AT THE ENGINE: a bare `create`
    at the production cold-start memory, proved ONLY through the
    public `wpt_create` and launched ONLY through
    `wpt_engine_boundU_alloc`/`launchResources`, DELIVERS at drive
    length exactly 2 — the engine's own `driveU` returns `.done` with
    a pointer value. Engine vocabulary only. -/
theorem alloc_create_launch_smoke (pref : prefix0) (aids : Nat → Nat) :
    ∃ v σ', driveU spikeCtx aids 2
        (spikeCtx.thread
          (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy pref)
          (fmapEmpty :: []))
        prodMem₀ = .done v σ' ∧
      ∃ pv : CerbMem.PointerValue, v = Vobject (OVpointer pv) := by
  obtain ⟨v, σ', h1, h2, -⟩ :=
    wpt_engine_boundU_alloc (GF := SpikeGF) (M := spikeCtx) spikeCtx_wf
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
      (fun _ _ _ _ => iprop(False))
      (createExpr loc0 empty_annotation (.IV .Prov_none 4) intTy pref)
      fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell) [⟨4, intTy⟩]
      (Frag.create loc0_lib)
      (by rw [show pot (createExpr loc0 empty_annotation (.IV .Prov_none 4)
          intTy pref) = 2 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]
          omega)
      (prodMem₀_launchCoh [⟨4, intTy⟩] prod_one_int_plan_fits)
      (fun v _ => ∃ pv : CerbMem.PointerValue, v = Vobject (OVpointer pv))
      2
      (by
        intro inst
        iintro ⟨-, Hcap⟩
        isplitr [Hcap]
        · iapply blockSpecsT_intro fun l _ _ _ _ _ _ hl =>
            (spikeCtx_labels_none l hl).elim
        · iapply wpt_create loc0 empty_annotation .Prov_none ⟨4, intTy⟩ []
            pref (fmapEmpty :: []) (Nat.le_refl 2) intTy_nonatomic
            (fun a => intTy_decIndep a _)
          isplitl [Hcap]
          · iexact Hcap
          iintro %p ⟨-, -, -⟩
          iintro %σ' %ns %κs %nt Hσ
          iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
          ipureintro
          exact ⟨p, rfl⟩)
      aids
  exact ⟨v, σ', h1, h2⟩

end CerberusHeapLang
