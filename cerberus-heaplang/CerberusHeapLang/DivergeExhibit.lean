/-
CerberusHeapLang.DivergeExhibit — THE NEGATIVE TEST of the total
lane (foundations Phase 3; the audit's exit criterion "removing the
decrease proof makes a looping example unprovable", in semantic
form).

THE PROGRAM: the self-jump loop

    loop: run loop()

whose registered body is its own back edge. Its configuration steps
to ITSELF (`dg_self_step` — the context-discarding jump with no
arguments and no state effect), so it is NOT strongly normalizing
(`dg_not_normalizing`).

THE UNPROVABILITY, semantic form (`diverge_total_unprovable`): a
total derivation for this loop — from ANY footprint's cell ownership
(any `m₀` coherent with any memory), at ANY ghost functor list, ANY
label context, ANY postcondition, ANY budget — is FALSE, not merely
unprovable: it would yield strong normalization through the total
adequacy (`wpt_strongly_normalizing`), contradicting the self-step.

WHERE A DIRECT ATTEMPT STICKS (the mandatory decrease doing its
job): to install the loop via `blockSpecsT`, the body must be
verified at EVERY variant `m` at which its precondition is claimed;
the body IS a jump redex, so its clause demands
`∃ m', ⌜1 + m' ≤ m⌝ ∗ Ls loop m' [] ρ` — at `m = 0` the arithmetic
conjunct is unsatisfiable, and no invariant choice escapes (the
jump must re-enter the same label at a strictly smaller variant,
forever). Deleting the `⌜1 + m ≤ k⌝` conjunct from `wpt.pre`'s jump
clause would make the loop derivable at any budget — and make THIS
THEOREM (and the budget inductions of `wpt_sound` /
`wpt_drive_aux`) fail to elaborate: the structural tripwire.
-/
import CerberusHeapLang.FibExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

def dgLoopSym : sym := Symbol "" 501 SD_None
def dgProcSym : sym := Symbol "" 502 SD_None

/-- The registered body: the bare self-jump. -/
def dgBody (ra : core_run_annotation) : CoreExpr :=
  Expr [] (Erun ra dgLoopSym [])

def dgQ (ra : core_run_annotation) : LabelMap :=
  fmapAddBy symCmpL dgLoopSym ([], dgBody ra) fmapEmpty

def dgRS (ra : core_run_annotation) : core_run_state :=
  { spikeRunState with
      labeled := fmapAddBy symCmpL dgProcSym (dgQ ra) fmapEmpty }

theorem dgQ_lookup (ra : core_run_annotation) :
    lookupLabel (dgQ ra) dgLoopSym = some ([], dgBody ra) := by
  unfold lookupLabel dgQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem dgRS_labeledAt (ra : core_run_annotation) :
    LabeledAt (dgRS ra) dgProcSym (dgQ ra) := by
  unfold LabeledAt dgRS
  show fmapLookupBy _ _ (fmapAddBy symCmpL dgProcSym _ fmapEmpty) = _
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

/-- THE SELF-STEP: the loop configuration steps to itself (jump,
    empty argument list, empty parameter binding, state verbatim). -/
theorem dg_self_step (ra : core_run_annotation) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (σ : Mem) :
    Step (procCtx dgProcSym (dgRS ra))
      (dgBody ra, ev0 :: evs, σ) (dgBody ra, ev0 :: evs, σ) :=
  Step.run (jumpRedex?_run [] ra dgLoopSym [])
    (by rw [procCtx_labels (dgRS_labeledAt ra)]; exact dgQ_lookup ra)
    rfl

/-- A self-related element of any relation is not accessible. -/
theorem not_acc_self {α : Type _} {r : α → α → Prop} {x : α}
    (hr : r x x) : ¬ Acc r x := by
  intro ha
  have h : ∀ y, Acc r y → y = x → False := by
    intro y ha
    induction ha with
    | intro z hz ih =>
      rintro rfl
      exact ih _ hr rfl
  exact h x ha rfl

/-- The self-jump loop is NOT strongly normalizing over the unified
    relation: it has an infinite (constant) reduction sequence. -/
theorem dg_not_normalizing (ra : core_run_annotation) (σ₀ : Mem) :
    ¬ Relation.StronglyNormalizing Language.ErasedStep
      ([(⟨dgBody ra, [fmapEmpty], procCtx dgProcSym (dgRS ra)⟩ : CoreRt)],
        σ₀) := by
  have hstep : Language.ErasedStep
      ([(⟨dgBody ra, [fmapEmpty], procCtx dgProcSym (dgRS ra)⟩ : CoreRt)], σ₀)
      ([(⟨dgBody ra, [fmapEmpty], procCtx dgProcSym (dgRS ra)⟩ : CoreRt)],
        σ₀) :=
    ⟨[], Language.Step.of_primStep
      (⟨dg_self_step ra fmapEmpty [] σ₀, rfl, rfl⟩ :
        PrimStep.primStep
          ((⟨dgBody ra, [fmapEmpty], procCtx dgProcSym (dgRS ra)⟩ : CoreRt), σ₀)
          ([] : List Empty)
          ((⟨dgBody ra, [fmapEmpty], procCtx dgProcSym (dgRS ra)⟩ : CoreRt), σ₀,
            ([] : List CoreRt)))
      (t₁ := []) (t₂ := [])⟩
  exact not_acc_self hstep

/-- THE NEGATIVE THEOREM: a total derivation for the self-jump loop
    is FALSE — from the cell ownership of any footprint `m₀` coherent
    with any memory `σ₀`, at any ghost functor list, label context,
    postcondition, and budget (header note: the stuck obligation of a
    direct attempt is the jump clause's mandatory decrease
    `∃ m', 1 + m' ≤ m` against a body that must be verified at every
    claimed variant, including m = 0). -/
theorem diverge_total_unprovable {GF : BundledGFunctors} [SpikeGpreS GF]
    (ra : core_run_annotation) (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hcoh : Coh fmapEmpty σ₀ m₀)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (Ψ : ∀ [SpikeGS .hasLC GF], SpikeVal → EnvStack → IProp GF)
    (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        iprop(blockSpecsT (procCtx dgProcSym (dgRS ra)) Ls Ψ ∗
          wpt (procCtx dgProcSym (dgRS ra)) Ls k Ψ (dgBody ra) [fmapEmpty])) :
    False :=
  dg_not_normalizing ra σ₀
    (wpt_strongly_normalizing (GF := GF) Ls Ψ (dgBody ra) [fmapEmpty]
      σ₀ m₀ hcoh k hwp)

end CerberusHeapLang
