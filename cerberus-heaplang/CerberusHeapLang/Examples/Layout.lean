/-
CerberusHeapLang.Examples.Layout — EXAMPLE SUPPORT: the concrete
layout constants and the canned exhibit-shape lemmas the exhibits
share. NOT part of the logic.

Alloc arc P5 (R-07 of the 2026-09-01 skeptical re-audit: "production
modules contain example constants"): everything here used to live at
the tail of `Rules.lean` (`intTy`, the 5/6/7 values with their memory
values, byte images, encoding and storability facts, the two exhibit
shapes and the anti-frame negative transcript) and of `Wps.lean`
(`wps_exhibit_store_frame`, `wps_exhibit_seq_stores`). Rule modules
now contain rules and their supporting lemmas only. QA-2
(docs/2026-09-02_qa2-notes.md): the raw-WP twins `exhibit`/
`exhibitC_triple`, pinned to the spike profile, were retired; the two
shapes below at the statement stratum (any machine context, any label
context, any environment) are the exhibits, and the anti-frame
transcript was re-recorded there.

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
- `wps_exhibit_store_frame` — {x ↦ - ∗ y ↦ a} store(x,7) {x ↦ 7 ∗ y ↦ a}
  by FRAME on the store small axiom ([USER 2026-08-30], the go order),
  and the anti-frame negative test as a verbatim transcript.
- `wps_exhibit_seq_stores` — disjoint sequential stores glued by the
  sequencing rule.
-/
import CerberusHeapLang.Wps

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

variable {hlc : HasLC} {GF : BundledGFunctors}

/-! ## The layout constants -/

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

/-! ## The values for EXHIBIT C ([USER 2026-08-30]): disjoint
sequential stores

`lets _ = store(x,5) in store(y,6)` on two distinct cells gives
NON-CONFLICTING updates:

    {x ↦ - ∗ y ↦ -} store(x,5); store(y,6) {x ↦ 5 ∗ y ↦ 6}

The PROOF DISCIPLINE is the exhibit (`wps_exhibit_seq_stores` below):
each leg is the store small axiom, the two legs are glued by the
sequencing rule, and distinctness is carried by ∗ alone. Nothing in
this module unfolds Step/storeM/state_interp — the derivation is
exactly the compositional surface. -/

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


/-! ## The two exhibit shapes, at the statement stratum -/

section WpsExhibits

variable [SpikeGS hlc GF]
variable {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}

/-! The corpus's two exhibit shapes at the label-context judgment, for
an ARBITRARY machine context, label context and environment —
jump-free code never consults the label context. Compositional
discipline: small axiom + FRAME + the sequencing rule; distinctness by
∗ alone. -/

/-- THE EXHIBIT ([USER 2026-08-30], the go order): {x ↦ - ∗ y ↦ a}
    store(x,7) {x ↦ 7 ∗ y ↦ a}, derived COMPOSITIONALLY — FRAME on the
    store small axiom, `y`'s cell entirely arbitrary (any type, any
    bytes) and untouched. -/
theorem wps_exhibit_store_frame (x y : CerbMem.PointerValue)
    (loc : CerbLocation.Loc) (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) (ρ : EnvStack) :
    iprop(pointsToCell M.tagDefs (GF := GF) x (.own 1) intTy bs ∗
        pointsToCell M.tagDefs y (.own 1) ty' bs') ⊢
      wps M p Ls Θ
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

/-! ## The anti-frame sanity check (negative test — locality is real)

A failing example cannot be committed compiling, so the test is
recorded as its verbatim transcript (re-runnable). Claiming y's cell
in the postcondition WITHOUT owning it in the precondition leaves the
derivation stuck on exactly the missing cell, with an EMPTY spatial
context after the x-cell is consumed:

```
example {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    {M : MachineCtx} {p : Option sym} {Ls : LabelSpec GF} {Θ : ProcSpec GF}
    (x y : CerbMem.PointerValue) (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (mo : memory_order)
    (bs bs' : List CerbMem.AbsByte) (ty' : ctype) (ρ : EnvStack) :
    pointsToCell M.tagDefs (GF := GF) x (.own 1) intTy bs ⊢
      wps M p Ls Θ
        (fun _ _ => iprop(pointsToCell M.tagDefs x (.own 1) intTy (sevenBytes M.tagDefs) ∗
          pointsToCell M.tagDefs y (.own 1) ty' bs'))
        (storeExpr loc ann intTy x sevenVal mo) ρ := by
  iintro Hx
  iapply wps_store loc ann intTy x sevenVal mo sevenMval bs ρ seven_encodes
    (seven_storable _)
  isplitl [Hx]
  · iexact Hx
  iintro %fp Hx
  rw [show (sevenBytes M.tagDefs) = (CerbMem.memValueToBytes M.tagDefs [] sevenMval).2 from rfl]
  iframe
```

Transcript (verbatim, `lake env lean` on the above, 2026-09-02, QA-2 —
the earlier raw-WP recordings of 2026-08-30/31 ended on the same
goal at `spikeCtx.tagDefs`):

```
error: unsolved goals
hlc : HasLC
GF : BundledGFunctors
inst✝ : SpikeGS hlc GF
M : MachineCtx
Ls : LabelSpec GF
x y : CerbMem.PointerValue
loc : CerbLocation.Loc
ann : core_run_annotation
mo : memory_order
bs bs' : List CerbMem.AbsByte
ty' : ctype
ρ : EnvStack
fp : CerbMem.Footprint
⊢ 
  ⊢ y ↦c[M.tagDefs] ty' ; bs'
```
-/

/-- EXHIBIT C ([USER 2026-08-30]): two sequenced stores on disjoint
    cells, glued by the sequencing rule — each leg the small axiom,
    distinctness carried by ∗ alone, any label context, any
    cons-shaped env. -/
theorem wps_exhibit_seq_stores (x y : CerbMem.PointerValue)
    (loc loc' : CerbLocation.Loc) (ann ann' : core_run_annotation)
    (mo mo' : memory_order) (bty : core_base_type)
    (bsx bsy : List CerbMem.AbsByte)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    iprop(pointsToCell M.tagDefs (GF := GF) x (.own 1) intTy bsx ∗
        pointsToCell M.tagDefs y (.own 1) intTy bsy) ⊢
      wps M p Ls Θ
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
