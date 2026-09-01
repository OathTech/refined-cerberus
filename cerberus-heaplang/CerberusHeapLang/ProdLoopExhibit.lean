/-
CerberusHeapLang.ProdLoopExhibit — THE PRODUCTION LOOP THEOREMS
(Phase 5; audit F-05 closed): loop programs certified as equations
about the SHIPPED pipeline

  CerbND.runND (Driver.drive tagDefs false file args)
               (initial_driver_state file fs)

from the COLD START — `initial_driver_state` (Driver.lean:435), the
production state constructor, nothing hand-built in the quantifiers.
The execution function in every public statement here is the shipped
runner: no package `drive`/`driveJ` appears in any statement (the
drive-lane theorems remain as lemmas in their exhibit modules).

BOUNDARY MODULE: the statements quantify over the shipped initial
state, whose `initial_core_run_state` draws sym_supply through the
declared temporal boundary axiom `runEffectful` (see Audit.lean —
provenance, mover, planned upstream retirement). Every theorem here
carries exactly trio + runEffectful, pinned in Audit.lean.

THE PIPELINE THEOREM (`prod_run_eqJ`): `drive_after_setup` (the
ProdEntry cold-start prefix: spawn, main lookup, errno block, park) +
`wpt_driver_done`'s DriverDoneAt (ProdLoop — the total judgment
driving the driver's own per-thread loop, jump rounds included) +
`driver2_done`/`finalize_done` (DriverCollapse). The label map the
driver reads is EXACTLY what the shipped registration computes
(`collect_labeled_continuations_NEW` over the synthetic file — the
ProdEntry registration ties), so nothing is hand-built in the label
plumbing either.
-/
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.ProdLoop

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List
open Iris Iris.BI Iris.ProgramLogic

/-! ## THE PRODUCTION RUN EQUATION FOR REGISTERED-LOOP PROGRAMS -/

/-- The production pipeline on a synthetic one-procedure file whose
    program's registered label map (the SHIPPED registration,
    `collect_labeled_continuations_NEW`) ties at `mainSym`, given the
    driver-delivery fact from the cold-start memory: `runND` of the
    SHIPPED driver from the PRODUCTION initial state is EXACTLY ONE
    Active execution, whose result value and final memory satisfy ψ.
    Total-lane composition: `hdd` comes from `wpt_driver_done`, so no
    termination hypothesis remains — only the in-budget bound on the
    certified step count (fuel honesty, D19). -/
theorem prod_run_eqJ (e : CoreExpr) {Q : LabelMap}
    (hQe : LabeledAt (initial_core_run_state
      (collect_labeled_continuations_NEW (prodFile e))) mainSym Q)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneAt mainSym Q (prodThread e) e [fmapEmpty] prodMem₀ ψ k)
    (hfl : k + 2 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND (_root_.drive fmapEmpty false (prodFile e) args)
          (initial_driver_state (prodFile e) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      ψ dres.dres_core_value dst'.layout_state ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  obtain ⟨v, σfin, ρfin, rs', tr, ctr, hψ, hloop⟩ :=
    hdd (prodEntryState e fs) fmapEmpty lemDefaultFuel rfl rfl rfl hQe hfl
  have hdrv2 := driver2_done 999999 fmapEmpty (prodEntryState e fs) _
    (prodThread e)
    { prodThread e with arena := ofVal (.pure v), env := ρfin }
    v rfl hloop rfl
  have hrun := drive_after_setup e fs args _ hdrv2
  refine ⟨_, _, runND_active hrun, ?_, rfl, rfl, rfl⟩
  rw [finalize_done fmapEmpty _ _
    { { prodThread e with arena := ofVal (.pure v), env := ρfin } with
        stack0 := Stack_empty, arena := mk_value_e v } v rfl rfl]
  exact hψ

/-! ## FIB ON THE SHIPPED PIPELINE — the first production loop
theorem (audit acceptance test 6: "at least one loop theorem
concludes directly about the shipped runND (Driver.drive ...)
computation"). -/

/-- FIB, PRODUCTION FORM: running the SHIPPED pipeline cold on the
    synthetic one-procedure file wrapping the authored iterative-fib
    loop program is EXACTLY ONE Active execution delivering
    `fib n` — a back-edge loop through the production scheduler, the
    label map computed by the shipped registration, termination from
    the total statement judgment (no step-count hypothesis; the one
    bound is the engine's own fuel budget, `lemDefaultFuel = 10^6`).
    No package drive/driveJ in the statement: the execution function
    is the shipped runner. -/
theorem fib_certified_production (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) (hn : 0 ≤ n)
    (hfuel : 2 * n.toNat + 6 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFile (fibProg ra n sbty ibty abty bbty)) args)
          (initial_driver_state
            (prodFile (fibProg ra n sbty ibty abty bbty)) fs) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = ivVal (fibSpec n.toNat) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have hQprod := fib_labeledAt_production ra n sbty ibty abty bbty
  have h := prod_run_eqJ (fibProg ra n sbty ibty abty bbty) hQprod
    (fun v _ => v = ivVal (fibSpec n.toNat)) (2 * n.toNat + 4)
    (wpt_driver_done (GF := SpikeGF)
      (M₀ := procCtx mainSym (initial_core_run_state
        (collect_labeled_continuations_NEW
          (prodFile (fibProg ra n sbty ibty abty bbty)))))
      rfl rfl (procCtx_labels hQprod) rfl rfl
      (fun l params cont hl => by
        rw [procCtx_labels hQprod] at hl
        obtain ⟨-, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
        exact fibBody_fragJ ra n)
      (fun l params cont hl => by
        rw [procCtx_labels hQprod] at hl
        obtain ⟨-, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
        rw [fibBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]
        omega)
      (fibLsT n)
      (fibProg ra n sbty ibty abty bbty) fmapEmpty []
      prodMem₀ (∅ : SpikeHeapF SpikeCell)
      (.save (fibBody_fragJ ra n))
      (by rw [fibProg_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (coh_empty prodMem₀)
      (fun v _ => v = ivVal (fibSpec n.toNat)) (2 * n.toNat + 4)
      (by
        intro inst
        refine .trans (BigSepM.bigSepM_empty).1 ?_
        refine .trans BI.emp_sep.2 (BI.sep_mono ?_ ?_)
        · exact (fib_blockSpecsT ra n ibty abty bbty mainSym _
            hQprod).trans
            (blockSpecsT_mono (fibPost_to_readout n))
        · exact (fib_wpt ra n ibty abty bbty mainSym _
            hQprod hn sbty).trans
            (wpt_mono (fibPost_to_readout n) _ _ _)))
    (by omega) fs args
  obtain ⟨dres, dst', heq, hval, hbl, hout, herr⟩ := h
  exact ⟨dres, dst', heq, hval, hbl, hout, herr⟩

end CerberusHeapLang
