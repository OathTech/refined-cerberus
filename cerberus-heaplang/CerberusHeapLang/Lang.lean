/-
CerberusHeapLang.Lang — the iris-lean `Language` instance over the
fragment's Step. This is how the package inherits iris-lean's full
mask/fupd WP without touching iris-lean itself; HeapLang's
instantiation is the template (Iris/HeapLang/Instances.lean +
PrimitiveLaws.lean:59-90).

The language expression is the runtime TUPLE `CoreRt` (Core
expression + live env stack + the live control `ctl` + the machine
context `M`) and values are `CoreRVal`; `toVal`/`ofVal` act
componentwise and the partial-bijection laws lift pointwise — with
the one control-side fact that a value is TERMINAL only at an EMPTY
call stack (`toValRt` answers `none` at `ctl.κ ≠ []`: a value under a
`Stack_cons2` is the engine's RETURN redex, C2). `primStep` runs
`Step` at the tuple's own machine context and PINS the successor's
context to it (`q.1.M = p.1.M`): the engine never writes `labeled`
on the sequential path, and nothing else in `M` is written by the
fragment. The control is NOT pinned by `primStep` — it is carried by
`Step` (written by exactly two rules, the call and the return —
`Step.ctl_cases`, calls arc C2; every other rule threads it,
`Step.ctl_eq` under its two guards). A value at a non-empty stack is
not a Language value, so `val_stuck` is `Step.toValRt_none`: at the
empty stack values do not step, at a non-empty stack the tuple is not
a value.

- Observations: `Empty` (the fragment forks no threads and emits no
  observations; every `List Empty` is `[]`).
- NO `Language.Context` instance for the Esseq frame: such an
  instance is TRUE for a jump-free relation but the global jump
  rule FALSIFIES it (a jump of e1 and of `Esseq pat e1 e2` step to
  the SAME configuration, so `Context.primStep_fill` fails). The
  sequencing rules in force (Wps.lean `wps_seq`, Wpt.lean `wpt_seq`
  — direct Löb/budget inductions over the factor structure of the
  Esseq frame) do not use one.
- The concrete ghost functor list `SpikeGF` (what the closed-program
  exports instantiate) and its `SpikeGpreS` instance; the
  `SpikeGS`/`SpikeGpreS` classes themselves are Heap.lean's.

SOUNDNESS STATUS: the WP is over Step; Step's certification against
the engine is Soundness.lean, and the engine-facing meaning lands
through Adequacy.lean (`MemTripleU` / `project_triple_pure`).
-/
import CerberusHeapLang.Heap

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.ProgramLogic

/-- Every list of `Empty` observations is empty. -/
theorem List.empty_eq_nil (l : List Empty) : l = [] := by
  cases l with
  | nil => rfl
  | cons e _ => exact e.elim

instance : Language CoreRt Mem Empty CoreRVal where
  primStep := fun p _obs q =>
    Step p.1.M (p.1.e, p.1.ρ, p.1.ctl, p.2) (q.1.e, q.1.ρ, q.1.ctl, q.2.1) ∧
      q.1.M = p.1.M ∧ q.2.2 = []
  toVal := toValRt
  ofVal := ofValRt
  coe_of_toVal_eq_some {r v} h := by
    obtain ⟨e, ρ, ⟨κ, pr, ℓ⟩, M⟩ := r
    cases κ with
    | cons pc κ => rw [toValRt_mk_cons] at h; cases h
    | nil =>
    rw [toValRt_mk] at h
    cases he : toVal e with
    | none => rw [he] at h; cases h
    | some w =>
      rw [he] at h
      cases h
      show ofValRt ⟨w, ρ, pr, ℓ, M⟩ = ⟨e, ρ, ⟨[], pr, ℓ⟩, M⟩
      rw [ofValRt_mk, ofVal_of_toVal he]
  toVal_coe v := by
    obtain ⟨w, ρ, pr, ℓ, M⟩ := v
    rw [ofValRt_mk, toValRt_mk, toVal_ofVal]
    rfl
  val_stuck {r σ obs r' σ' eₜ} h := Step.toValRt_none h.1

@[simp] theorem primStep_eq (r : CoreRt) (σ : Mem) (obs : List Empty)
    (r' : CoreRt) (σ' : Mem) (efs : List CoreRt) :
    (PrimStep.primStep (r, σ) obs (r', σ', efs) : Prop) ↔
      (Step r.M (r.e, r.ρ, r.ctl, σ) (r'.e, r'.ρ, r'.ctl, σ') ∧ r'.M = r.M ∧ efs = []) :=
  Iff.rfl

/-- Values-side sanity: `toVal` on the Language instance is the
    componentwise `toValRt`. -/
theorem language_toVal_eq (r : CoreRt) :
    ToVal.toVal (Val := CoreRVal) r = toValRt r := rfl

/-! Deliberately ABSENT: a `Language.Context` instance for the
Esseq frame. The global jump rule falsifies `Context.primStep_fill`
— the engine's `Erun` discards the frame (step_ctx's Erun arm,
Core_reduction.lean:484), so a jump of `e1` and of
`Esseq pat e1 e2` step to the SAME configuration, and a step of the
framed term is not always a framed step. Statement-level fact
recording the falsification direction: `Step.sseq_inv`'s jump
disjunct (Step.lean). Nothing in the sequencing routes uses such an
instance (header note). -/

/-! ## The Iris ghost-state instance -/

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- Mirror of HeapLang's IrisGS_gen instance
    (PrimitiveLaws.lean:82-88): no per-step later credits beyond the
    base one, trivial fork postcondition (nothing forks), and a
    step-count-insensitive state interpretation. -/
instance instIrisGS [SpikeGS hlc GF] : IrisGS_gen hlc CoreRt GF where
  invGS := SpikeGS.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    letI := @SpikeGS.invGS hlc GF _
    iintro $

/-! ## Non-vacuity witness for the ghost-state prerequisites

A concrete functor list satisfying `SpikeGpreS` (mirror of HeapLangS,
PrimitiveLaws.lean:94-126, minus prophecies). The bundled `SpikeGS`
(ghost NAMES + world satisfaction) is constructed by allocation inside
the adequacy proof, exactly as HeapLang's `heap_adequacy` does — that
construction is slice B's adequacy obligation. -/

def SpikeGF : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨_root_.Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Int (Agree (DiscreteO CerbMem.AbsByte)) SpikeHeapF),
          by infer_instance⟩
  | 5 => ⟨constOF (HeapView Int (Agree (DiscreteO MetaCell)) SpikeHeapF),
          by infer_instance⟩
  | 6 => ⟨constOF (HeapView Int (Agree (DiscreteO AllocCursor)) SpikeHeapF),
          by infer_instance⟩
  | 7 => ⟨constOF (HeapView Int (Agree (DiscreteO GName)) SpikeHeapF),
          by infer_instance⟩
  | 8 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instSpikeGpreS_SpikeGF : SpikeGpreS SpikeGF where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  byte_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 7
    · exists 8
  meta_pre := by
    constructor
    · constructor
      exists 5
    · constructor
      exists 7
    · exists 8
  cursor_pre := by
    constructor
    · constructor
      exists 6
    · constructor
      exists 7
    · exists 8

end CerberusHeapLang
