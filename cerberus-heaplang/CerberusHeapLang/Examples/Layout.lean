/-
CerberusHeapLang.Examples.Layout — EXAMPLE SUPPORT: the concrete
layout constants and the canned exhibit-shape lemmas the exhibits
share. NOT part of the logic.

Alloc arc P5 (R-07 of the 2026-09-01 skeptical re-audit: "production
modules contain example constants"): everything here used to live at
the tail of `Rules.lean` (`intTy`, the 5/6/7 values with their memory
values, byte images, encoding and storability facts, the two triple-
level exhibits `exhibit`/`exhibitC_triple` and the anti-frame negative
transcript) and of `Wps.lean` (`wps_exhibit_store_frame`,
`wps_exhibit_seq_stores`). Rule modules now contain rules and their
supporting lemmas only; the statements below are UNCHANGED by the
move (the P5 signature snapshot is the record).

Import direction: this module sits ABOVE the rule modules (it imports
`Wps`) and BELOW the exhibits (which import it, directly or through
`CerberusHeapLang.API` + this module). No rule or adequacy module may
import it — the import-direction speedbump in `scripts/test_unit.sh`
greps for exactly that.

Contents:
- `intTy` — signed int, the probe type every scalar exhibit uses.
- `sevenVal`/`sevenMval`/`sevenBytes`, `seven_encodes`, `seven_storable`
  (and the same for five and six): the Core value `Specified(n)`, its
  memory value, its byte image (the engine's own serialization), the
  encoding equation and the `StorableAt` side condition — all `rfl`.
- `exhibit` — {x ↦ - ∗ y ↦ a} store(x,7) {x ↦ 7 ∗ y ↦ a} by FRAME on
  the store small axiom ([USER 2026-08-30], the go order), and the
  anti-frame negative test as a verbatim transcript.
- `exhibitC_triple` — disjoint sequential stores glued by `triple_seq`.
- `wps_exhibit_store_frame`, `wps_exhibit_seq_stores` — the same two
  shapes at the statement stratum, any label context.
-/
import CerberusHeapLang.Wps

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

variable {hlc : HasLC} {GF : BundledGFunctors}

/-! ## The exhibit -/

/-- signed int (the recon's probe type). -/
def intTy : ctype := Ctype [] (.Basic (.Integer (.Signed .Int_)))

-- Phase 2 (F-04): the int-specific interior load engine seam
-- (`loadM_interior_int`) is RETIRED — the generic typed-subrange seam
-- `loadM_at` (Heap.lean) covers every accessed type and offset.

/-- The Core value `Specified(7) : loaded integer`. -/
def sevenVal : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval 7)))

/-- Its memory value. -/
def sevenMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 7)

/-- Its byte image (the engine's own serialization). -/
def sevenBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] sevenMval).2

theorem seven_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) sevenVal =
      some sevenMval := rfl

theorem seven_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy sevenMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- THE EXHIBIT ([USER 2026-08-30], the go order):

      {x ↦ - ∗ y ↦ a} store(x, 7) {x ↦ 7 ∗ y ↦ a}

    derived COMPOSITIONALLY: FRAME on the store small axiom, then
    CONSEQUENCE to forget the return value. `y`'s cell is entirely
    arbitrary (any type, any bytes) and untouched. -/
theorem exhibit [SpikeGS hlc GF] (x y : CerbMem.PointerValue)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) :
    triple (GF := GF)
      iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy bs ∗ pointsToCell spikeCtx.tagDefs y (.own 1) ty' bs')
      (storeExpr loc ann intTy x sevenVal mo)
      (fun _ => iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (sevenBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) ty' bs')) := by
  -- 1. the small axiom, instantiated at 7/int
  have hax : triple (GF := GF) (pointsToCell spikeCtx.tagDefs x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun w => iprop(∃ fp,
        ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, spikeEnv, spikeCtx⟩ : CoreRVal)⌝ ∗
        pointsToCell spikeCtx.tagDefs x (.own 1) intTy (sevenBytes spikeCtx.tagDefs))) :=
    wp_store loc ann intTy x sevenVal mo sevenMval bs spikeEnv seven_encodes
      (seven_storable _)
  -- 2. FRAME with y's cell
  have hfr := triple_frame (R := pointsToCell spikeCtx.tagDefs y (.own 1) ty' bs') hax
  -- 3. CONSEQUENCE: drop the return-value information
  refine triple_conseq .rfl ?_ hfr
  intro v
  iintro ⟨⟨%fp, %hw, Hx⟩, Hy⟩
  iframe

/-! ## The anti-frame sanity check (negative test — locality is real)

A failing example cannot be committed compiling, so the test is
recorded as its verbatim transcript (re-runnable; also in the slice
notes; env-plumbed 2026-08-31 at the S1 migration — the stuck goal is
unchanged in substance: exactly the missing y-cell). Claiming y's
cell in the postcondition WITHOUT owning it in the precondition
leaves the derivation stuck on exactly the missing cell, with an
EMPTY spatial context after the x-cell is consumed:

```
example {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (x y : CerbMem.PointerValue) (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) :
    triple (GF := GF) (pointsToCell x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun _ => iprop(pointsToCell x (.own 1) intTy (sevenBytes spikeCtx.tagDefs) ∗
        pointsToCell y (.own 1) ty' bs')) := by
  have hax : triple (GF := GF) (pointsToCell x (.own 1) intTy bs)
      (storeExpr loc ann intTy x sevenVal mo)
      (fun w => iprop(∃ fp,
        ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, spikeEnv, spikeCtx⟩ : CoreRVal)⌝ ∗
        pointsToCell x (.own 1) intTy (sevenBytes spikeCtx.tagDefs))) :=
    wp_store loc ann intTy x sevenVal mo sevenMval bs spikeEnv seven_encodes
      (seven_storable _)
  refine triple_conseq .rfl ?_ hax
  intro v
  iintro ⟨%fp, %hw, Hx⟩
  iframe
```

Transcript (verbatim, `lake env lean` on the above, 2026-08-30, tuple
form re-run 2026-08-31 — the final stuck goal both times):

```
error: unsolved goals
⊢
  ⊢ y ↦c ty' ; bs'
```
-/

/-! ## EXHIBIT C ([USER 2026-08-30]): disjoint sequential stores

`lets _ = store(x,5) in store(y,6)` on two distinct cells gives
NON-CONFLICTING updates:

    {x ↦ - ∗ y ↦ -} store(x,5); store(y,6) {x ↦ 5 ∗ y ↦ 6}

The PROOF DISCIPLINE is the exhibit: each leg is the store small
axiom FRAMED with the other cell (triple_frame + consequence), and
the two legs are glued by SEQ (triple_seq, itself wp_sseq over the
real Esseq). Nothing below unfolds Step/storeM/state_interp — the
derivation is exactly the compositional surface. -/

/-- The Core value `Specified(5)`, its memory value, its byte image. -/
def fiveVal : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval 5)))

def fiveMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 5)

def fiveBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] fiveMval).2

theorem five_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) fiveVal =
      some fiveMval := rfl

theorem five_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy fiveMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- The Core value `Specified(6)`, its memory value, its byte image. -/
def sixVal : value :=
  Vloaded (LVspecified (OVinteger (CerbMem.integerIval 6)))

def sixMval : CerbMem.MemValue :=
  CerbMem.integerValueMval (.Signed .Int_) (CerbMem.integerIval 6)

def sixBytes (tds : CerbTags.TagDefsMap) : List CerbMem.AbsByte :=
  (CerbMem.memValueToBytes tds [] sixMval).2

theorem six_encodes :
    memValueFromValue fmapEmpty (Ctype [] (unatomic_ intTy)) sixVal =
      some sixMval := rfl

theorem six_storable (tds : CerbTags.TagDefsMap) : StorableAt tds intTy sixMval :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- EXHIBIT C at the Iris triple level. Derivation (the point):
    1. wp_store on x, FRAMED with y's cell (+ consequence to drop
       the return-value annotation);
    2. wp_store on y, FRAMED with x's now-updated cell (+ the same);
    3. glued by triple_seq (= wp_sseq over the fragment's Esseq).
    x and y are arbitrary distinct-cell pointers — distinctness is
    never stated: the ∗ in the precondition carries it. -/
theorem exhibitC_triple [SpikeGS hlc GF] (x y : CerbMem.PointerValue)
    (loc loc' : CerbLocation.Loc) (ann ann' : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type)
    (bsx bsy : List CerbMem.AbsByte) :
    triple (GF := GF)
      iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy bsx ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)
      (sseqExpr bty (storeExpr loc ann intTy x fiveVal mo)
        (storeExpr loc' ann' intTy y sixVal mo'))
      (fun _ => iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy (sixBytes spikeCtx.tagDefs))) := by
  -- leg 1: the store small axiom on x, FRAMED with y's cell
  have hx : triple (GF := GF) (pointsToCell spikeCtx.tagDefs x (.own 1) intTy bsx)
      (storeExpr loc ann intTy x fiveVal mo)
      (fun w => iprop(∃ fp,
        ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, spikeEnv, spikeCtx⟩ : CoreRVal)⌝ ∗
        pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs))) :=
    wp_store loc ann intTy x fiveVal mo fiveMval bsx spikeEnv five_encodes
      (five_storable _)
  have h1 : triple (GF := GF)
      iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy bsx ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)
      (storeExpr loc ann intTy x fiveVal mo)
      (fun _ => iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)) := by
    refine triple_conseq .rfl ?_
      (triple_frame (R := pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy) hx)
    intro v
    iintro ⟨⟨%fp, %hw, Hx⟩, Hy⟩
    iframe
  -- leg 2: the store small axiom on y, FRAMED with x's updated cell
  have hy : triple (GF := GF) (pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)
      (storeExpr loc' ann' intTy y sixVal mo')
      (fun w => iprop(∃ fp,
        ⌜w = (⟨SpikeVal.annot [DA_pos [] fp] Vunit, spikeEnv, spikeCtx⟩ : CoreRVal)⌝ ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy (sixBytes spikeCtx.tagDefs))) :=
    wp_store loc' ann' intTy y sixVal mo' sixMval bsy spikeEnv six_encodes
      (six_storable _)
  have h2 : triple (GF := GF)
      iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy bsy)
      (storeExpr loc' ann' intTy y sixVal mo')
      (fun _ => iprop(pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs) ∗
        pointsToCell spikeCtx.tagDefs y (.own 1) intTy (sixBytes spikeCtx.tagDefs))) := by
    refine triple_conseq BI.sep_comm.1 ?_
      (triple_frame (R := pointsToCell spikeCtx.tagDefs x (.own 1) intTy (fiveBytes spikeCtx.tagDefs)) hy)
    intro v
    iintro ⟨⟨%fp, %hw, Hy⟩, Hx⟩
    iframe
  -- glue: SEQ
  exact triple_seq (.action _ _) h1 h2


/-! ## The exhibit shapes at the statement stratum -/

section WpsExhibits

variable [SpikeGS hlc GF]
variable {M : MachineCtx} {Ls : LabelSpec GF}

/-! ## Coverage preservation on the REAL fragment (probe §4, now over
Core): the corpus's two exhibit shapes on the stratified layer, for
an ARBITRARY label context (Q, Ls) — jump-free code never consults
it. Compositional discipline identical to the frozen exhibits: small
axiom + FRAME + the sequencing rule; distinctness by ∗ alone. -/

/-- Corpus shape 1 (the house `exhibit`): {x ↦ - ∗ y ↦ a} store(x,7)
    {x ↦ 7 ∗ y ↦ a}, via FRAME on the store small axiom — any label
    context, any env. -/
theorem wps_exhibit_store_frame (x y : CerbMem.PointerValue)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) (ρ : EnvStack) :
    iprop(pointsToCell M.tagDefs (GF := GF) x (.own 1) intTy bs ∗
        pointsToCell M.tagDefs y (.own 1) ty' bs') ⊢
      wps M Ls
        (fun _ _ => iprop(pointsToCell M.tagDefs x (.own 1) intTy (sevenBytes M.tagDefs) ∗
          pointsToCell M.tagDefs y (.own 1) ty' bs'))
        (storeExpr loc ann intTy x sevenVal mo) ρ := by
  iintro ⟨Hx, Hy⟩
  iapply (wps_frame
    (Ψ := fun _ _ => iprop(pointsToCell M.tagDefs (GF := GF) x (.own 1) intTy (sevenBytes M.tagDefs)))
    (R := pointsToCell M.tagDefs y (.own 1) ty' bs') _ _)
  isplitl [Hx]
  · iapply wps_store loc ann intTy x sevenVal mo sevenMval bs ρ seven_encodes
      (seven_storable _)
    isplitl [Hx]
    · iexact Hx
    iintro %fp Hx
    rw [show (sevenBytes M.tagDefs) = (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2 from rfl]
    iexact Hx
  · iexact Hy

/-- Corpus shape 2 (the house `exhibitC_triple`): two sequenced
    stores on disjoint cells, glued by the (jump-aware-shaped)
    sequencing rule — each leg the small axiom, distinctness carried
    by ∗ alone, any label context, any cons-shaped env. -/
theorem wps_exhibit_seq_stores (x y : CerbMem.PointerValue)
    (loc loc' : CerbLocation.Loc) (ann ann' : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type)
    (bsx bsy : List CerbMem.AbsByte)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    iprop(pointsToCell M.tagDefs (GF := GF) x (.own 1) intTy bsx ∗
        pointsToCell M.tagDefs y (.own 1) intTy bsy) ⊢
      wps M Ls
        (fun _ _ => iprop(pointsToCell M.tagDefs x (.own 1) intTy (fiveBytes M.tagDefs) ∗
          pointsToCell M.tagDefs y (.own 1) intTy (sixBytes M.tagDefs)))
        (sseqExpr bty (storeExpr loc ann intTy x fiveVal mo)
          (storeExpr loc' ann' intTy y sixVal mo')) (ev0 :: evs) := by
  iintro ⟨Hx, Hy⟩
  rw [show sseqExpr bty (storeExpr loc ann intTy x fiveVal mo)
      (storeExpr loc' ann' intTy y sixVal mo') =
    Expr [] (Esseq (Pattern [] (CaseBase (none, bty)))
      (storeExpr loc ann intTy x fiveVal mo)
      (storeExpr loc' ann' intTy y sixVal mo')) from rfl]
  iapply wps_seq
  iapply wps_store loc ann intTy x fiveVal mo fiveMval bsx (ev0 :: evs)
    five_encodes (five_storable _)
  isplitl [Hx]
  · iexact Hx
  iintro %fp Hx
  iapply wps_store loc' ann' intTy y sixVal mo' sixMval bsy (ev0 :: evs)
    six_encodes (six_storable _)
  isplitl [Hy]
  · iexact Hy
  iintro %fp' Hy
  rw [show (fiveBytes M.tagDefs) = (CerbMem.memValueToBytes M.tagDefs [] fiveMval).2 from rfl,
    show (sixBytes M.tagDefs) = (CerbMem.memValueToBytes M.tagDefs [] sixMval).2 from rfl]
  isplitl [Hx]
  · iexact Hx
  · iexact Hy


end WpsExhibits

end CerberusHeapLang
