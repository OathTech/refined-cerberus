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
shipped driver's per-thread loop at every fuel exhausts or delivers,
never kills otherwise, never derails, and any delivered value IS the
scrutinee (`case_certified`). The TOTAL twin `caseProg_wpt` (H1b,
2026-09-04) is the same derivation at the total judgment, budget 2, with
the engine readout as its postcondition — the consumer of
`wpt_case_value` (KNOWN-OPEN-ITEMS B13); like every seeded/no-procedure
exhibit it has no shipped-loop total form (B1's deferred class).

ON THE BRANCH PREMISES. `Frag.case_value` carries branch closure as
EXPLICIT per-branch premises (`hbr`: the selected branch is in `Frag`;
`hbsz`: its `esize` is bounded by the case node's), not via a generic
`Frag e → Frag (subst_sym_expr x v e)` closure lemma — that statement
is FALSE on this fragment: several constructor premises are
value-shape-sensitive (`valueFromPexpr pe = none` on the
operand-evaluation shapes), and substitution can turn a not-yet-value
operand (`PEsym x`) into a value (`PEval v`) whose redex spelling
leaves the constructor's range. `hbsz` is carried rather than proved:
the equation that would discharge it is `esize (subst_sym_expr x v e)
= esize e` (with its mutual twin for `esizeAlts`) — true because
`esize` inspects only expression constructors and `subst_sym_expr`
substitutes only into pure expressions — and the obstacle is that the
engine's `subst_sym_expr` is `subst_sym_expr_lemFuel lemDefaultFuel`,
a fuel-indexed recursion over the whole generated Core AST, so the
proof is a fuel-indexed induction over that mutual recursion (README,
"Registered divergences and limitations"). Here both premises are
discharged by computing the substituted branch (`caseProg_select` is
`rfl`).
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
  caseRedex (Pexpr [] () (PEval v))
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

/-- Cone membership: the branch premises discharged by computation
    (see the header note on why they are premises, not a closure
    lemma). -/
theorem caseProg_frag (v : value) : Frag (caseProg v) := by
  refine .case_value (fun e' hsel => ?_) (fun e' hsel => ?_) <;>
    rw [caseProg_select] at hsel
  · obtain rfl : ofVal (.pure v) = e' := Option.some.inj hsel
    exact frag_ofVal _
  · obtain rfl : ofVal (.pure v) = e' := Option.some.inj hsel
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
theorem caseProg_wps (M : MachineCtx) (p : Option sym) (Ls : LabelSpec GF) (Θ : ProcSpec GF) (v : value)
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
theorem caseProg_wpt (M : MachineCtx) (p : Option sym) (Ls : LabelSpecT GF) (Θ : ProcSpecT GF)
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
theorem case_blockSpecs (v : value) :
    ⊢ blockSpecs (GF := GF) spikeCtx none caseLs emptyProcSpec
      (fun w _ => iprop(⌜w.val = v⌝)) :=
  blockSpecs_intro fun l _ _ _ _ _ hl => (spikeCtx_labels_none l hl).elim

/-- The base-WP face with the engine readout, at the spike profile
    (the `fib_wp_readout` collapse shape: block specifications +
    `wps_sound`, then the pure readout under the mask change). -/
theorem case_wp_readout (v : value) :
    ⊢ WP (⟨caseProg v, spikeEnv, spikeCtl, spikeCtx⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CoreRVal.val w = v⌝) }} := by
  refine (caseProg_wps spikeCtx none caseLs emptyProcSpec v spikeEnv).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((case_blockSpecs v).trans (wps_sound_empty (ctl := spikeCtl) rfl (caseProg v) spikeEnv))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  exact wp_mono fun w => stateInterp_readout fun _ _ _ _ _ => pure_consequence _

end CaseIris

/-! ## THE CONSUMER REGRESSION (engine vocabulary only) -/

/-- THE ADEQUACY-LEVEL CASE REGRESSION (the manifest's Ecase consumer
    cell; F-01 acceptance): driving THE ENGINE ({step_ctx →
    sequential discharge} at the straight-line launch profile) on
    `case v of x => pure(x) end`, from ANY memory state: the shipped
    loop at every fuel exhausts or delivers, never kills otherwise,
    never gets stuck, and any delivered value IS the scrutinee — the
    value fact flows from the proved WP through `engine_adequacy`, not
    by evaluation. Step 1 of any such run is the engine's Ecase
    substitution TAU (`Step.case_value` is the only rule that fires). -/
theorem case_certified {GF : BundledGFunctors} [SpikeGpreS GF] (v : value) (σ₀ : Mem) :
    DriverSafeCtl spikeCtx (spikeThread (caseProg v)) (caseProg v) spikeEnv spikeCtl σ₀
      (fun v' _ => v' = v) := by
  refine engine_adequacy (GF := GF) (M := spikeCtx) rfl rfl (ctl := spikeCtl) rfl
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
    (fun l params cont hl => (spikeCtx_labels_none l hl).elim)
    spikeCtx_fragProcs
    (caseProg v) fmapEmpty [] σ₀ ∅ (caseProg_frag v)
    (Nat.le_trans (caseProg_frag v).pot_le_two
      (by rw [show esize (caseProg v) = 2 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    (Coh.mk
      (fun _ c hget => absurd (hget.symm.trans
        (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) _))
        (Option.some_ne_none c))
      (fun _ _ c1 _ _ hget _ => absurd (hget.symm.trans
        (Iris.Std.LawfulPartialMap.get?_empty (M := SpikeHeapF) _))
        (Option.some_ne_none c1)))
    (fun v' _ => v' = v)
    ?_ (th₀ := spikeThread (caseProg v)) rfl
  intro inst
  exact (BigSepM.bigSepM_empty).1.trans (case_wp_readout v)

end CerberusHeapLang
