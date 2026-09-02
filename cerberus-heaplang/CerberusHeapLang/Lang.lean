/-
CerberusHeapLang.Lang — the iris-lean `Language` instance over the
fragment's Step. This is how the package inherits iris-lean's full
mask/fupd WP without touching iris-lean itself; HeapLang's
instantiation is the template (Iris/HeapLang/Instances.lean +
PrimitiveLaws.lean:59-90).

The language expression is the runtime TUPLE `CoreRt` (Core
expression + live env stack + the machine context — S1b unified)
and values are `CoreRVal`; `toVal`/`ofVal` act componentwise and
the partial-bijection laws lift pointwise. `primStep` runs `Step`
at the tuple's own label map and PINS the successor's map to it
(`q.1.M = p.1.M`): the engine never writes `labeled` on the
sequential path.

- Observations: `Empty` (the fragment forks no threads and emits no
  observations; every `List Empty` is `[]`).
- NO `Language.Context` instance for the Esseq frame: such an
  instance is TRUE for a jump-free relation but the global jump
  rule FALSIFIES it (a jump of e1 and of `Esseq pat e1 e2` step to
  the SAME configuration, so `Context.primStep_fill` fails). The
  sequencing rules in force (Wps.lean `wps_seq`, Wpt.lean `wpt_seq`
  — direct Löb/budget inductions over the factor structure of the
  Esseq frame) do not use one.

SOUNDNESS STATUS: the WP is over Step; Step's certification against
the engine is Soundness.lean, and the engine-facing meaning lands
through Adequacy.lean (SemTriple / semantic_triple_sound).
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
    Step p.1.M (p.1.e, p.1.ρ, p.2) (q.1.e, q.1.ρ, q.2.1) ∧
      q.1.M = p.1.M ∧ q.2.2 = []
  toVal := toValRt
  ofVal := ofValRt
  coe_of_toVal_eq_some {r v} h := by
    obtain ⟨e, ρ, M⟩ := r
    rw [toValRt_mk] at h
    cases he : toVal e with
    | none => rw [he] at h; cases h
    | some w =>
      rw [he] at h
      cases h
      show ofValRt ⟨w, ρ, M⟩ = ⟨e, ρ, M⟩
      rw [ofValRt_mk, ofVal_of_toVal he]
  toVal_coe v := by
    obtain ⟨w, ρ, M⟩ := v
    rw [ofValRt_mk, toValRt_mk, toVal_ofVal]
    rfl
  val_stuck {r σ obs r' σ' eₜ} h := by
    obtain ⟨e, ρ, M⟩ := r
    show toValRt ⟨e, ρ, M⟩ = none
    rw [toValRt_mk, Step.toVal_none h.1]
    rfl

@[simp] theorem primStep_eq (r : CoreRt) (σ : Mem) (obs : List Empty)
    (r' : CoreRt) (σ' : Mem) (efs : List CoreRt) :
    (PrimStep.primStep (r, σ) obs (r', σ', efs) : Prop) ↔
      (Step r.M (r.e, r.ρ, σ) (r'.e, r'.ρ, σ') ∧ r'.M = r.M ∧ efs = []) :=
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
