/-
CerberusHeapLang.DivergeExhibit — THE NEGATIVE TEST of the total
lane (foundations Phase 3; the audit's exit criterion "removing the
decrease proof makes a looping example unprovable", in semantic
form).

THE PROGRAM: the self-jump loop

    loop: run loop()

whose registered body is its own back edge. Its configuration steps
to ITSELF (`dg_self_step` — the context-discarding jump with no
arguments and no state effect), so THE ENGINE'S DRIVE of it rests in
`.more` at EVERY fuel (`dg_driveU_more`: each round is the self-step,
discharged by the device lemma `outcomesU_of_step`) — it never delivers.

THE UNPROVABILITY, engine form (`diverge_total_unprovable`): a total
derivation for this loop — from ANY footprint's cell ownership (any
`m₀` coherent with any memory), at ANY ghost functor list, ANY label
context, ANY postcondition, ANY budget `k` — is FALSE, not merely
unprovable: through the total engine bound (`wpt_engine_boundU`) it
would give `driveU … k … = .done v σ'`, contradicting `.more`. (Until
the 2026-09-02 professor review this was argued through strong
normalization of the mirror relation, `wpt_strongly_normalizing`; that
theorem and the mirror-only `dg_not_normalizing` are retired — the
negative test is now a fact about the engine's execution, like every
other export.)

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

THE ONE DIRECT `Step` USE IN AN EXHIBIT, AND WHY (2026-09-02 detailed
audit, L-2): `dg_self_step` is proved by `Step.run`. A client of the
logic reasons through the public rules and never through `Step`
(API.lean, "Below the line"); this module is the NEGATIVE test, not a
client — it shows a derivation is impossible by exhibiting what the
engine actually does, and the engine's behaviour at the self-jump is
reached through the mirror step (`outcomesU_of_step` on `dg_self_step`
in `dg_driveU_more`). The narrow exception: a
NEGATIVE test may name a mirror step to reach an engine fact; a
POSITIVE exhibit may not. Mirror-level coverage witnesses live in
`Examples/MirrorCoverage.lean`.
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
    Step (procCtx (dgRS ra))
      (dgBody ra, ev0 :: evs, procCtl dgProcSym, σ) (dgBody ra, ev0 :: evs, procCtl dgProcSym, σ) :=
  Step.run (jumpRedex?_run [] ra dgLoopSym [])
    (by rw [procCtx_labels (dgRS_labeledAt ra)]; exact dgQ_lookup ra)
    rfl

/-- The registered body is in the fragment (a jump redex with no
    arguments). -/
theorem dgBody_frag (ra : core_run_annotation) : Frag (dgBody ra) :=
  Frag.run (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- The label map registers exactly the self-jump body. -/
theorem dgQ_inv (ra : core_run_annotation) {l : sym}
    {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel (dgQ ra) l = some (params, cont)) :
    params = [] ∧ cont = dgBody ra := by
  unfold lookupLabel dgQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

/-- THE ENGINE NEVER DELIVERS: driving the self-jump loop for ANY
    number of rounds rests in `.more` at the same configuration — each
    round is the self-step (`outcomesU_of_step` on `dg_self_step`). -/
theorem dg_driveU_more (ra : core_run_annotation) (σ₀ : Mem) :
    ∀ (k : Nat) (aids : Nat → Nat),
      driveU (procCtx (dgRS ra)) aids k
        ((procCtx (dgRS ra)).thread (dgBody ra) [fmapEmpty] (procCtl dgProcSym)) σ₀ =
      .more ((procCtx (dgRS ra)).thread (dgBody ra) [fmapEmpty] (procCtl dgProcSym)) σ₀
  | 0, _ => rfl
  | k + 1, aids => by
    rw [driveU_succ, stepOutcomes_thread,
      outcomesU_of_step (aids 0) (dgBody_frag ra)
        (by rw [show esize (dgBody ra) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)
        (dg_self_step ra fmapEmpty [] σ₀)]
    exact dg_driveU_more ra σ₀ k _

/-- Any postcondition weakens to the trivial engine readout. -/
theorem dg_post_to_readout {GF : BundledGFunctors} [SpikeGS .hasLC GF]
    (Ψ : SpikeVal → EnvStack → IProp GF) :
    ∀ w ρ', Ψ w ρ' ⊢ readoutPost (fun _ _ => True) w ρ' := by
  intro w ρ'
  iintro -
  iintro %σ' %ns %κs %nt -
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  trivial

/-- THE NEGATIVE THEOREM: a total derivation for the self-jump loop
    is FALSE — from the cell ownership of any footprint `m₀` coherent
    with any memory `σ₀`, at any ghost functor list, label context,
    postcondition, and budget (header note: the stuck obligation of a
    direct attempt is the jump clause's mandatory decrease
    `∃ m', 1 + m' ≤ m` against a body that must be verified at every
    claimed variant, including m = 0). Proved AT THE ENGINE: the total
    bound would deliver `.done` at fuel `k`; the engine rests in
    `.more`. -/
theorem diverge_total_unprovable {GF : BundledGFunctors} [SpikeGpreS GF]
    (ra : core_run_annotation) (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hcoh : Coh fmapEmpty σ₀ m₀)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (Ψ : ∀ [SpikeGS .hasLC GF], SpikeVal → EnvStack → IProp GF)
    (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        iprop(blockSpecsT (procCtx (dgRS ra)) (procCtl dgProcSym) Ls Ψ ∗
          wpt (procCtx (dgRS ra)) (procCtl dgProcSym) Ls k Ψ (dgBody ra) [fmapEmpty])) :
    False := by
  have hlbl := procCtx_labels (dgRS_labeledAt ra)
  obtain ⟨v, σ', hdone, -, -⟩ :=
    wpt_engine_boundU (GF := GF) (M := procCtx (dgRS ra)) (procCtx_wf _) (ctl := procCtl dgProcSym) rfl
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := dgQ_inv ra hl
        exact dgBody_frag ra)
      (fun l params cont hl => by
        rw [hlbl] at hl
        obtain ⟨-, rfl⟩ := dgQ_inv ra hl
        rw [show pot (dgBody ra) = 2 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      Ls (dgBody ra) fmapEmpty [] σ₀ m₀ (dgBody_frag ra)
      (by rw [show pot (dgBody ra) = 2 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      hcoh (fun _ _ => True) k
      (by
        intro inst
        refine hwp.trans (BI.sep_mono ?_ ?_)
        · exact blockSpecsT_mono (dg_post_to_readout Ψ)
        · exact wpt_mono (dg_post_to_readout Ψ) _ _ _)
      (fun _ => 0)
  rw [dg_driveU_more ra σ₀ k] at hdone
  cases hdone

end CerberusHeapLang
