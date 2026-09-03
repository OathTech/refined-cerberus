/-
CerberusHeapLang.DivergeExhibit — THE NEGATIVE TEST of the total
lane (foundations Phase 3; the audit's exit criterion "removing the
decrease proof makes a looping example unprovable", in semantic
form).

THE PROGRAM: the self-jump loop

    loop: run loop()

whose registered body is its own back edge. Its configuration steps
to ITSELF (`dg_self_step` — the context-discarding jump with no
arguments and no state effect), so THE SHIPPED DRIVER'S per-thread loop
on it EXHAUSTS at EVERY fuel (`dg_loop_exhausts`: each round is the
self-step, the shipped round `loop_step_frag_same`, and the out-of-fuel
arm is the kill `CerbND.fuelExhaustedKill`) — it never delivers.

THE UNPROVABILITY, engine form (`diverge_total_unprovable`): a total
derivation for this loop — from ANY footprint's cell ownership (any
`m₀` coherent with any memory), at ANY ghost functor list, ANY label
context, ANY postcondition, ANY budget `k` — is FALSE, not merely
unprovable: through the total driver lane (`wpt_driver_done`, ProdLoop)
it would make the shipped loop return PROGRAM-DONE within `k + 2`
iterations from a driver state holding the thread, contradicting the
exhaustion. (Until the 2026-09-02 professor review this was argued
through strong normalization of the mirror relation,
`wpt_strongly_normalizing`; that theorem and the mirror-only
`dg_not_normalizing` are retired; until the fuel-lane restatement of
2026-09-03 the contradiction was against the package loop `driveU`.)

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
`wpt_driver_aux`) fail to elaborate: the structural tripwire.

THE ONE DIRECT `Step` USE IN AN EXHIBIT, AND WHY (2026-09-02 detailed
audit, L-2): `dg_self_step` is proved by `Step.run`. A client of the
logic reasons through the public rules and never through `Step`
(API.lean, "Below the line"); this module is the NEGATIVE test, not a
client — it shows a derivation is impossible by exhibiting what the
engine actually does, and the engine's behaviour at the self-jump is
reached through the mirror step (the shipped round `loop_step_frag_same`
on `dg_self_step` in `dg_loop_exhausts`). The narrow exception: a
NEGATIVE test may name a mirror step to reach an engine fact; a
POSITIVE exhibit may not. Mirror-level coverage witnesses live in
`Examples/MirrorCoverage.lean`.
-/
import CerberusHeapLang.FibExhibit
import CerberusHeapLang.ProdLoop

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

/-- THE SHIPPED LOOP NEVER DELIVERS: from any driver state holding the
    proc-carrying thread at the self-jump body, with the label tie at the
    current procedure, the production driver's per-thread loop EXHAUSTS
    at EVERY fuel — each round is the self-step (the shipped round
    `loop_step_frag_same` on `dg_self_step`), so the run never reaches
    PROGRAM-DONE and the out-of-fuel kill `CerbND.fuelExhaustedKill` is
    the loop's only value. -/
theorem dg_loop_exhausts (ra : core_run_annotation) :
    ∀ (fl : Nat) (dst : driver_state) (acc : Fmap thread_id (List core_step2)),
      dst.core_state0.thread_states =
        [(0, (none, procThread dgProcSym (dgBody ra) [fmapEmpty]))] →
      dst.core_extern = fmapEmpty →
      LabeledAt dst.core_run_state0 dgProcSym (dgQ ra) →
      ∃ dst' : driver_state,
        runOne (drive_nonmemory_steps_aux2_lemFuel fl fmapEmpty acc [0]) dst =
          (NDkilled CerbND.fuelExhaustedKill, dst')
  | 0, dst, acc, _, _, _ => ⟨dst, loop_zero_exhausts _ _ _ _⟩
  | fl + 1, dst, acc, hth, hext, hQd => by
    obtain ⟨rs', tr, ctr, hlbl, hrun⟩ :=
      loop_step_frag_same (th₀ := procThread dgProcSym (dgBody ra) [fmapEmpty])
        rfl rfl (procCtx_labels (dgRS_labeledAt ra)) rfl fl acc hth hext hQd (dgBody_frag ra)
        (by rw [show esize (dgBody ra) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)
        (dg_self_step ra fmapEmpty [] dst.layout_state)
    rw [hrun]
    exact dg_loop_exhausts ra fl _ acc
      (by rw [update_thread_state_single _ _ _ hth]; rfl) hext
      (by show LabeledAt rs' dgProcSym (dgQ ra)
          unfold LabeledAt
          rw [hlbl]
          exact hQd)

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
    driver lane would make the shipped loop deliver PROGRAM-DONE within
    `k + 2` iterations from a driver state holding the thread; the loop
    exhausts instead (`dg_loop_exhausts`). -/
theorem diverge_total_unprovable {GF : BundledGFunctors} [SpikeGpreS GF]
    (ra : core_run_annotation) (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hcoh : Coh fmapEmpty σ₀ m₀)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (Ψ : ∀ [SpikeGS .hasLC GF], SpikeVal → EnvStack → IProp GF)
    (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn fmapEmpty (hlc := .hasLC) (GF := GF) i (.own 1) c)) ⊢
        iprop(blockSpecsT (procCtx (dgRS ra)) (some dgProcSym) Ls emptyProcSpecT Ψ ∗
          wpt (procCtx (dgRS ra)) (some dgProcSym) Ls emptyProcSpecT k Ψ (dgBody ra) [fmapEmpty])) :
    False := by
  have hlbl := procCtx_labels (dgRS_labeledAt ra)
  have hdd :=
    wpt_driver_done (GF := GF) (M₀ := procCtx (dgRS ra)) (ctl := procCtl dgProcSym) rfl rfl hlbl
      rfl (th₀ := procThread dgProcSym (dgBody ra) [fmapEmpty]) rfl rfl rfl
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
  -- a driver state holding the thread at σ₀, with the tied run state
  let dst : driver_state :=
    { (default : driver_state) with
        core_state0 := { (default : driver_state).core_state0 with
          thread_states := [(0, (none, procThread dgProcSym (dgBody ra) [fmapEmpty]))] },
        layout_state := σ₀, core_run_state0 := dgRS ra, core_extern := fmapEmpty }
  obtain ⟨v, σf, ρf, rs', tr, ctr, -, hrun⟩ :=
    hdd dst fmapEmpty (k + 2) rfl rfl rfl (dgRS_labeledAt ra) (Nat.le_refl _)
  obtain ⟨dst', hkill⟩ := dg_loop_exhausts ra (k + 2) dst fmapEmpty rfl rfl (dgRS_labeledAt ra)
  rw [hrun] at hkill
  cases hkill

end CerberusHeapLang
