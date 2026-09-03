/-
CerberusHeapLang.TotalAdequacy — the total lane's readout vocabulary.

`readoutPost ψ` is the engine-readout postcondition shape the total
judgment is stated against when its budget is realized as driver
iterations: a readout wand that consumes the final state interpretation
and delivers the pure `ψ w.val σ'` — the total analog of the partial
lane's readout wand (Adequacy.lean, `engine_adequacy`). Its plumbing
lemmas (`readoutPost_mergeInto_annot`, `readoutPost_annot_absorb`,
`readoutPost_mono`) are what the exhibits' sequenced prefixes and
postcondition weakenings consume.

THE TOTAL ADEQUACY THEOREMS THEMSELVES are the driver lane in
ProdLoop.lean: `wpt_driver_aux` → `wpt_driver_done`/`wpt_driver_done_alloc`
(one procedure, `DriverDoneAt`) and the CPS induction `wpt_driver_cps` →
`wpt_driver_done_procs` through PCALL/RETURN (`DriverDoneCtl`), each
realizing the budget as `k + 2` iterations of the shipped driver's own
per-thread loop and consumed by ProdEntry.lean's `prod_run_eqJ`/
`prod_run_eqJ_procs` into the root-of-trust statements over
`runND ∘ drive ∘ initial_driver_state`. FUEL HONESTY WITHOUT
ACCUMULATION: each round's `esize e ≤ lemDefaultFuel` obligation is
turned by the static potential `pot` (Potential.lean) into the two
run-length-independent hypotheses `pot e₀ ≤ lemDefaultFuel` and `pot cont
≤ lemDefaultFuel` per registered body — the same two the partial
statements carry.

HISTORY (fuel-lane restatement, 2026-09-03; record
docs/2026-09-03_f1-notes.md): until then this module carried the total
lane's `driveU` simulation — `wpt_drive_aux`, `DriveDoneAt`,
`wpt_engine_boundU`/`_alloc` and the state-inert cone `stateInert`/
`StateInertLabels` — over the package loop around the engine's
`step_ctx`. That lane was deleted with the loop: its content is the
driver lane above, on the shipped driver.
-/
import CerberusHeapLang.Wpt
import CerberusHeapLang.Adequacy

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib

/-- The engine-readout postcondition shape both launch theorems
    consume (the total analog of the partial lane's readout wand). -/
abbrev readoutPost {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    (ψ : value → Mem → Prop) : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
    stateInterp σ' ns κs nt ={⊤,∅}=∗ ⌜ψ w.val σ'⌝)

/-! ## Readout plumbing for sequenced prefixes: the engine readout
only reads the ERASED value, so an annotation-merge on the sequenced
value is absorbed (the LETS-ANNOT residue of a prefix store never
reaches ψ). -/

theorem val_mergeInto_annot (ds : List dyn_annotation) (v : value)
    (u : SpikeVal) :
    (SpikeVal.mergeInto (.annot ds v) u).val = u.val := by
  cases u <;> rfl

theorem readoutPost_mergeInto_annot {GF : BundledGFunctors}
    [SpikeGS .hasLC GF] (ψ : value → Mem → Prop)
    (ds : List dyn_annotation) (v : value) :
    (fun (u : SpikeVal) (ρ' : EnvStack) =>
      readoutPost (GF := GF) ψ (SpikeVal.mergeInto (.annot ds v) u) ρ') =
    (fun (u : SpikeVal) (ρ' : EnvStack) => readoutPost (GF := GF) ψ u ρ') := by
  funext u ρ'
  unfold readoutPost
  rw [val_mergeInto_annot ds v u]

/-- The engine readout only reads the ERASED value, so a prefix
    store's annotation-merge is absorbed (element-wise face of
    `readoutPost_mergeInto_annot`, robust against the abbrev's
    unfolding under unification). -/
theorem readoutPost_annot_absorb {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (ψ : value → Mem → Prop) (ds : List dyn_annotation) (v : value)
    (u : SpikeVal) (ρ' : EnvStack) :
    readoutPost (GF := GF) ψ u ρ' ⊢
      readoutPost ψ (SpikeVal.mergeInto (.annot ds v) u) ρ' := by
  rw [congrFun (congrFun (readoutPost_mergeInto_annot ψ ds v) u) ρ']

/-- Monotonicity of the readout in the pure postcondition. -/
theorem readoutPost_mono {hlc : HasLC} {GF : BundledGFunctors}
    [SpikeGS hlc GF] {ψ ψ' : value → Mem → Prop}
    (h : ∀ v σ, ψ v σ → ψ' v σ) (w : SpikeVal) (ρ' : EnvStack) :
    readoutPost (GF := GF) ψ w ρ' ⊢ readoutPost ψ' w ρ' := by
  iintro H %σ' %ns %κs %nt Hσ
  imod H $$ %σ' %ns %κs %nt Hσ with %hp
  ipureintro
  exact h _ _ hp



end CerberusHeapLang
