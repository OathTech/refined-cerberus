/-
CerberusHeapLang.CaseExhibit — the `Ecase` (VALUE scrutinee) consumer:
an adequacy-level theorem whose program executes the rule.

The program: `case v of x => pure(x) end` — a value scrutinee with a
BINDER pattern, so the engine's substitution TAU genuinely fires
(`select_case` binds `x := v` through `subst_sym_expr`). The theorem
chain: `wps_case_value` (the logic rule) → `wps_sound` (the Löb-tied
collapse, block specifications vacuous at `spikeCtx`) →
`engine_adequacy` — concluding, in engine vocabulary only
(`DriverSafeCtl`): from any driver state holding the case program, the
shipped driver's per-thread loop at every iteration counter exhausts or
delivers, under the stated ambient-fuel bound,
never kills otherwise, never derails, and any delivered value IS the
scrutinee (`case_certified`). The TOTAL twin `caseProg_wpt` (H1b,
2026-09-04) is the same derivation at the total judgment, budget 2, with
the engine readout as its postcondition — the consumer of
`wpt_case_value` (KNOWN-OPEN-ITEMS B13); like every seeded/no-procedure
exhibit it has no shipped-loop total form (B1's deferred class).

ON THE BRANCH PREMISES. `Frag.case_value` retains explicit membership
for every original and selected branch. This exhibit's original branch
is a symbol read, so its membership requires positive ambient fuel;
selection substitutes the value and yields a value injection. Arbitrary
substitution does not preserve every syntactic fragment constructor.
The structural size premise is separate: the measured substitution
wrapper preserves expression size, and the general branch-size theorem
is available. This one-branch example discharges both selected-branch
premises directly through `caseProg_select`.
-/
import CerberusHeapLang.API

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open scoped Iris.Std.PartialMap

/-! ## The program -/

/-- The case binder (the exhibit sym convention: fresh concrete id). -/
def caseXSym : sym := Symbol "" 104 SD_None

/-- The single branch: `x => pure(x)` at the plain-symbol binder. -/
def caseBranch : CoreExpr := Expr [] (Epure (Pexpr [] () (PEsym caseXSym)))

/-- `case v of x => pure(x) end` (the canonical case-redex spelling —
    `Frag.case_value`'s range). -/
def caseProg (v : value) : CoreExpr :=
  caseRedex [] (Pexpr [] () (PEval v))
    [(symPat [] caseXSym BTy_unit, caseBranch)]

/-- The selection COMPUTES: the binder pattern matches any value and
    binds `x := v`; `subst_sym_expr` rewrites the branch's `PEsym x`
    to `PEval v` — the substituted branch is the canonical value
    injection. (The engine's own `select_case`/`match_pattern`/
    `subst_sym_expr`, Core_aux.lean; one `rfl`.) -/
theorem caseProg_select (v : value) :
    select_case subst_sym_expr v
      [(symPat [] caseXSym BTy_unit, caseBranch)] =
      some (ofVal (.pure v)) := rfl

/-- Membership retains the original symbol-read branch and discharges
    selected-branch closure by the substitution equation. -/
theorem caseProg_frag [LemFuel] (hfuel : 0 < LemFuel.fuel) (v : value) : Frag (caseProg v) := by
  refine .case_value (fun q hq => ?_) (fun e' hsel => ?_) (fun e' hsel => ?_)
  · -- E5: every alternative's body is in the cone (`pure(x)`, a symbol read)
    rw [List.mem_singleton] at hq
    subst hq
    exact .pure_op rfl (.sym [] caseXSym) (peDepth_sym_le [] caseXSym hfuel)
  · rw [caseProg_select] at hsel
    obtain rfl : ofVal (.pure v) = e' := Option.some.inj hsel
    exact frag_ofVal _
  · rw [caseProg_select] at hsel
    obtain rfl : ofVal (.pure v) = e' := Option.some.inj hsel
    exact Nat.le_succ 1

/-! ## The WP lane -/

section CaseIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]

/-- The trivial label specification (the spike profile registers no
    labels; the block specifications below are vacuous). -/
def caseLs : LabelSpec GF := fun _ _ _ => iprop(True)

/-- The statement-WP derivation AT ANY MACHINE CONTEXT and any label
    specification: one application of the case rule, then the value
    channel. The postcondition: the delivered value is the
    scrutinee. -/
theorem caseProg_wps [LemFuel] (M : MachineCtx) (p : Option sym) (Ls : LabelSpec GF) (Θ : ProcSpec GF) (v : value)
    (ρ : EnvStack) :
    ⊢ wps (GF := GF) M p Ls Θ (fun w _ => iprop(⌜w.val = v⌝)) (caseProg v) ρ := by
  refine .trans ?_ (wps_case_value [] (Pexpr [] () (PEval v))
    [(symPat [] caseXSym BTy_unit, caseBranch)] ρ
    (valueFromPexpr_val [] v) (caseProg_select v))
  refine .trans ?_ (wps_ofVal (.pure v) ρ)
  exact BI.pure_intro rfl

/-- THE TOTAL TWIN (hygiene slice H1b, 2026-09-04; KNOWN-OPEN-ITEMS B13 —
    the consumer of `wpt_case_value`): the same derivation at the total
    judgment, budget 2 = the substitution TAU (`wpt_case_value`, `+ 1`) +
    the bare value's delivery (`wpt_ofVal`, `deliveryCost (.pure v) = 1`),
    at any machine context, label specification and table; the
    postcondition is the engine readout `readoutPost` (the total lane's
    shape), obtained through the public `stateInterp_readout`/
    `pure_consequence` alone. -/
theorem caseProg_wpt [LemFuel] (M : MachineCtx) (p : Option sym) (Ls : LabelSpecT GF) (Θ : ProcSpecT GF)
    (v : value) (ρ : EnvStack) :
    ⊢ wpt (GF := GF) M p Ls Θ 2 (readoutPost (fun v' _ => v' = v)) (caseProg v) ρ := by
  refine .trans ?_ (wpt_mono (Ψ₁ := fun w _ => iprop(⌜w.val = v⌝))
    (fun _ _ => stateInterp_readout fun _ _ _ _ _ => pure_consequence _) 2 (caseProg v) ρ)
  refine .trans ?_ (wpt_case_value [] (Pexpr [] () (PEval v))
    [(symPat [] caseXSym BTy_unit, caseBranch)] ρ
    (valueFromPexpr_val [] v) (caseProg_select v))
  refine .trans ?_ (wpt_ofVal (.pure v) ρ (Nat.le_refl 1))
  exact BI.pure_intro rfl

/-- Vacuous block specifications at the spike profile (no labels are
    registered — the lookup premise is unsatisfiable). -/
theorem case_blockSpecs [LemFuel] (v : value) :
    ⊢ blockSpecs (GF := GF) spikeCtx none caseLs emptyProcSpec
      (fun w _ => iprop(⌜w.val = v⌝)) :=
  blockSpecs_intro fun l _ _ _ _ _ hl => (spikeCtx_labels_none l hl).elim

/-- The base-WP face with the engine readout, at the spike profile
    (the `fib_wp_readout` collapse shape: block specifications +
    `wps_sound`, then the pure readout under the mask change). -/
theorem case_wp_readout [LemFuel] (v : value) :
    ⊢ WP (⟨caseProg v, spikeEnv, spikeCtl, spikeCtx⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CoreRVal.val w = v⌝) }} := by
  refine (caseProg_wps spikeCtx none caseLs emptyProcSpec v spikeEnv).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((case_blockSpecs v).trans (wps_sound_empty (ctl := spikeCtl) rfl (Nat.zero_le _) (caseProg v) spikeEnv))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  exact wp_mono fun w => stateInterp_readout fun _ _ _ _ _ => pure_consequence _

end CaseIris

/-! ## THE CONSUMER REGRESSION (engine vocabulary only) -/

/-- THE ADEQUACY-LEVEL CASE REGRESSION (the manifest's Ecase consumer
    cell; F-01 acceptance): driving THE ENGINE ({step_ctx →
    sequential discharge} at the straight-line launch profile) on
    `case v of x => pure(x) end`, from ANY memory state: the shipped
    loop at every iteration counter exhausts or delivers, with ambient fuel
    at least two, never kills otherwise,
    never gets stuck, and any delivered value IS the scrutinee — the
    value fact flows from the proved WP through `engine_adequacy`, not
    by evaluation. The program's first reduction is the engine's Ecase
    substitution TAU (`Step.case_value` is the only rule that fires). -/
theorem case_certified [LemFuel] (hfuel : 2 ≤ LemFuel.fuel) {GF : BundledGFunctors} [SpikeGpreS GF] (v : value) (σ₀ : Mem) :
    DriverSafeCtl spikeCtx (spikeThread (caseProg v)) (caseProg v) spikeEnv spikeCtl σ₀
      (fun v' _ => v' = v) := by
  refine engine_adequacy (hfuel := hfuel) (GF := GF) (M := spikeCtx) rfl rfl (ctl := spikeCtl) rfl
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
    spikeCtx_fragProcs
    (caseProg v) fmapEmpty [] σ₀ ∅ (caseProg_frag (by omega) v)
    (Coh.mk
      (fun _ c hget => absurd (hget.symm.trans
        (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) _))
        (Option.some_ne_none c))
      (fun _ _ c1 _ _ hget _ => absurd (hget.symm.trans
        (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) _))
        (Option.some_ne_none c1)))
    (fun v' _ => v' = v)
    ?_ (th₀ := spikeThread (caseProg v))
  intro inst
  exact (BigSepM.bigSepM_empty).1.trans (case_wp_readout v)

end CerberusHeapLang
