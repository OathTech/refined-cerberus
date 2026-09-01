/-
CerberusHeapLang.WseqExhibit — the Ewseq (wildcard) DRIFT-TEST
consumer regression (foundations arc Phase 1 / S1b; design record §8
item 8 / arc plan Phase 1 item 7: "one NEW non-example construct
passed through the generic route").

The program: `letw _ = pure(v1) in pure(v2)` — a weak-sequencing
node at the wildcard pattern whose first step is the engine's
LETW-PURE TAU (one_step0 Ewseq bare-value arm, Core_reduction.lean:
353) and whose delivered value is the CONTINUATION's value. The
theorem chain is the WP LANE end to end: `wps_wseq` (the drift
rule) → `wps_sound` → `spike_engine_adequacy` — concluding, engine
vocabulary only: the drive never kills, never derails, and any
delivered value IS v2.

DRIFT-TEST RECORD: this construct entered through the GENERIC route
only — relation rules (Step.wseq_pure/wseq_annot/wseq_ctx) + cone
membership (Frag.wseq) + decomposition (Decomp.wseq) + the match
arms of `engine_step_matchU`; the Rules/Wps/Adequacy strata and the
Language instance needed ZERO changes, and the capability-manifest
generator FAILED CLOSED on the extended constructor lists until its
row landed (the gate demonstration the arc plan prescribes).
-/
import CerberusHeapLang.Adequacy
import CerberusHeapLang.Wps

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open scoped Iris.Std.PartialMap

/-! ## The program -/

/-- `letw _ = pure(v1) in pure(v2)` (the canonical LETW-PURE redex —
    `Frag.wseq` over two value injections). -/
def wseqProg (v1 v2 : value) : CoreExpr :=
  Expr [] (Ewseq (Pattern [] (CaseBase (none, BTy_unit)))
    (ofVal (.pure v1)) (ofVal (.pure v2)))

/-- Cone membership through the generic constructors alone. -/
theorem wseqProg_frag (v1 v2 : value) : Frag (wseqProg v1 v2) :=
  .wseq (frag_ofVal (.pure v1)) (frag_ofVal (.pure v2))

/-! ## The WP lane -/

section WseqIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- The trivial label specification (the spike profile registers no
    labels). -/
def wseqLs : LabelSpec GF := fun _ _ _ => iprop(True)

/-- The statement-WP derivation AT ANY MACHINE CONTEXT: one
    application of the drift rule `wps_wseq`, then the value channel
    twice (the bound value is discarded by the wildcard —
    `SpikeVal.mergeInto (.pure v1)` is the identity). -/
theorem wseqProg_wps (M : MachineCtx) (Ls : LabelSpec GF) (v1 v2 : value)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) :
    ⊢ wps (GF := GF) M Ls (fun w _ => iprop(⌜w.val = v2⌝))
        (wseqProg v1 v2) (ev0 :: evs) := by
  refine .trans ?_ (wps_wseq [] [] BTy_unit
    (ofVal (.pure v1)) (ofVal (.pure v2)) ev0 evs)
  refine .trans ?_ (wps_ofVal (.pure v1) (ev0 :: evs))
  refine .trans ?_ (wps_ofVal (.pure v2) (ev0 :: evs))
  exact BI.pure_intro rfl

/-- Vacuous block specifications at the spike profile. -/
theorem wseq_blockSpecs (v2 : value) :
    ⊢ blockSpecs (GF := GF) spikeCtx wseqLs
      (fun w _ => iprop(⌜w.val = v2⌝)) :=
  blockSpecs_intro fun l _ _ _ _ _ hl => (spikeCtx_labels_none l hl).elim

/-- The base-WP face with the engine readout at the spike profile
    (the `case_wp_readout` collapse shape). -/
theorem wseq_wp_readout (v1 v2 : value) :
    ⊢ WP (⟨wseqProg v1 v2, spikeEnv, spikeCtx⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CoreRVal.val w = v2⌝) }} := by
  refine (wseqProg_wps spikeCtx wseqLs v1 v2 fmapEmpty []).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((wseq_blockSpecs v2).trans (wps_sound (wseqProg v1 v2) spikeEnv))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  refine wp_mono fun w => ?_
  iintro %hval %σ' %ns %κs %nt Hσ
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact hval

end WseqIris

/-! ## THE CONSUMER REGRESSION (engine vocabulary only) -/

/-- THE ADEQUACY-LEVEL DRIFT-TEST REGRESSION (the manifest's Ewseq
    consumer cell): driving THE ENGINE on `letw _ = pure(v1) in
    pure(v2)`, from ANY memory state: never killed, never stuck, and
    any delivered value IS v2 — the value fact flows from the proved
    WP through `spike_engine_adequacy`, not by evaluation. Step 1 of
    any such run is the engine's LETW-PURE TAU (`Step.wseq_pure` is
    the only rule that fires). -/
theorem wseq_certified {GF : BundledGFunctors} [SpikeGpreS GF] (v1 v2 : value)
    (σ₀ : Mem) (n : Nat) (aids : Nat → Nat)
    (hfuel : 2 + n ≤ lemDefaultFuel) :
    (∀ r, drive aids n (spikeThread (wseqProg v1 v2)) σ₀ ≠ .killed r) ∧
    (drive aids n (spikeThread (wseqProg v1 v2)) σ₀ ≠ .stuck) ∧
    (∀ (v' : value) (σ' : Mem),
      drive aids n (spikeThread (wseqProg v1 v2)) σ₀ = .done v' σ' →
      v' = v2) := by
  refine spike_engine_adequacy (GF := GF) (wseqProg v1 v2) σ₀ ∅
    (wseqProg_frag v1 v2)
    (Coh.mk
      (fun _ c hget => absurd (hget.symm.trans
        (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) _))
        (Option.some_ne_none c))
      (fun _ _ c1 _ _ hget _ => absurd (hget.symm.trans
        (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) _))
        (Option.some_ne_none c1)))
    (fun v' _ => v' = v2)
    ?_ n aids
    (by rw [show esize (wseqProg v1 v2) = 2 from rfl]; exact hfuel)
  intro inst
  exact (BigSepM.bigSepM_empty).1.trans (wseq_wp_readout v1 v2)

end CerberusHeapLang
