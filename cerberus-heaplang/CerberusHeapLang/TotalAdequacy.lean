/-
CerberusHeapLang.TotalAdequacy — the two halves of total
correctness, separated exactly as the 2026-08-31 audit ordered
(F-02, remediation item 2):

1. THE LOGICAL HALF: `wpt_strongly_normalizing` — the pinned Iris
   `TotalAdequacy` (`twp_total`) consumed AS-IS over the unified
   relation: a proved total statement judgment (collapsed into TWP
   by `wpt_sound`) plus the seeded footprint yields STRONG
   NORMALIZATION of the Iris thread-pool relation at the launched
   configuration — termination as a logical fact, no fuel, no
   engine vocabulary.

2. THE COST HALF: `wpt_drive_aux` / `wpt_engine_boundU/J` — THE
   GENERIC MEASURE→DRIVE-FUEL SIMULATION: the SAME judgment's budget
   is realized as concrete `driveU`/`driveJ` fuel. From
   `wpt … k … e ρ` plus the seeded footprint, the engine's drive AT
   FUEL k DELIVERS: `driveU M aids k (M.thread e ρ) σ = .done v σ'`
   with the postcondition readout — the unconditional total
   equations the exhibits export (fib at 2·n+4; list-reverse at its
   derived bound), with ZERO example-level Step constructors: the
   simulation is proved once, here, by induction on the budget with
   `engine_step_matchU` discharging one engine step per budget unit.

FUEL HONESTY WITHOUT ACCUMULATION (what keeps the exported total
equations unconditional in the loop count): the per-step
`engine_step_matchU` obligation is `esize e ≤ lemDefaultFuel` for
the CURRENT term only. The generic `esize` growth bound (≤ +1 per
step, `Frag.esize_step_bound`) would force a fuel hypothesis
coupled to the run length; instead this module installs a
STEP-MONOTONE SIZE POTENTIAL `pot` (a classical potential/ranking
function on terms: value leaves 1, redex leaves 2 — a leaf's
rewrite into its annotated value is prepaid — compounds
structural): `Frag.pot_step_bound` shows `pot` never increases
along non-jump cone steps and resets to the target body at jumps,
so the static hypotheses `pot e₀ ≤ lemDefaultFuel` and
`pot cont ≤ lemDefaultFuel` per label body bound `esize` at every
reachable term (`Frag.esize_le_pot`), independent of the run
length.

THE STATE-INERT CONE: programs built without memory actions
(`stateInert` — no Eaction/Ememop/Ecase) preserve the memory state
step by step (`Frag.stateInert_step`), so their total equations pin
the final state to the initial one — fib's exported equation keeps
its verbatim `.done (fib n) σ₀` shape through the generic theorem.
-/
import CerberusHeapLang.Wpt
import CerberusHeapLang.Adequacy

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib

/-! ## The size potential -/

/-- The step-monotone size potential (header note): like `esize`,
    but value leaves cost 1, all other leaves 2 (a redex leaf's
    rewrite into an annotated value is prepaid), and a case node
    prices its branches at twice their `esize` (the substituted
    branch is bounded through `Frag.pot_le_two`). -/
def pot : CoreExpr → Nat
  | Expr _ (Esseq _ e1 e2) => 1 + max (pot e1) (pot e2)
  | Expr _ (Ewseq _ e1 e2) => 1 + max (pot e1) (pot e2)
  | Expr _ (Eannot _ b) => 1 + pot b
  | Expr _ (Eif _ e2 e3) => 1 + max (pot e2) (pot e3)
  | Expr _ (Esave _ _ body) => 1 + pot body
  | Expr _ (Ecase _ pats) => 2 * (1 + esizeAlts pats)
  | Expr _ (Epure (Pexpr _ _ (PEval _))) => 1
  | _ => 2

@[simp] theorem pot_sseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    pot (Expr a (Esseq pat e1 e2)) = 1 + max (pot e1) (pot e2) := rfl

@[simp] theorem pot_wseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    pot (Expr a (Ewseq pat e1 e2)) = 1 + max (pot e1) (pot e2) := rfl

@[simp] theorem pot_annot {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} : pot (Expr a (Eannot ds b)) = 1 + pot b := rfl

@[simp] theorem pot_if {a : List annot} {g : generic_pexpr Unit sym}
    {e2 e3 : CoreExpr} :
    pot (Expr a (Eif g e2 e3)) = 1 + max (pot e2) (pot e3) := rfl

@[simp] theorem pot_save {a : List annot} {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} :
    pot (Expr a (Esave sb ps body)) = 1 + pot body := rfl

@[simp] theorem pot_case {a : List annot} {pe : generic_pexpr Unit sym}
    {pats : List (pattern × CoreExpr)} :
    pot (Expr a (Ecase pe pats)) = 2 * (1 + esizeAlts pats) := rfl

@[simp] theorem pot_pure_val {a pb : List annot} {v : value} :
    pot (Expr a (Epure (Pexpr pb () (PEval v)))) = 1 := rfl

@[simp] theorem pot_pure_sym {a pb : List annot} {x : sym} :
    pot (Expr a (Epure (Pexpr pb () (PEsym x)))) = 2 := rfl

@[simp] theorem pot_action {a : List annot}
    {p : generic_paction core_run_annotation Unit sym} :
    pot (Expr a (Eaction p)) = 2 := rfl

@[simp] theorem pot_memop {a : List annot} {mop : memop}
    {pes : List (generic_pexpr Unit sym)} :
    pot (Expr a (Ememop mop pes)) = 2 := rfl

@[simp] theorem pot_run {a : List annot} {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)} :
    pot (Expr a (Erun ra l pes)) = 2 := rfl

@[simp] theorem pot_ofVal_pure {v : value} : pot (ofVal (.pure v)) = 1 := rfl

@[simp] theorem pot_ofVal_annot {ds : List dyn_annotation} {v : value} :
    pot (ofVal (.annot ds v)) = 2 := rfl

/-- `esize` is bounded by the potential on the cone. -/
theorem Frag.esize_le_pot {e : CoreExpr} (hf : Frag e) : esize e ≤ pot e := by
  induction hf with
  | val_pure v => simp [esize, pot]
  | store hlib => simp [esize, pot, storeRedex]
  | load hlib => simp [esize, pot, loadRedex]
  | create hlib => simp [esize, pot, createRedex]
  | sseq hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | annot hfb ihb => simp only [esize_annot, pot_annot]; omega
  | save hb ih =>
    simp only [show ∀ sb ps b, esize (saveRedex sb ps b) = 1 + esize b
        from fun _ _ _ => rfl,
      show ∀ sb ps b, pot (saveRedex sb ps b) = 1 + pot b
        from fun _ _ _ => rfl]
    omega
  | if_ hdg hf2 hf3 ih2 ih3 =>
    simp only [show ∀ g e2 e3, esize (ifRedex g e2 e3) =
        1 + max (esize e2) (esize e3) from fun _ _ _ => rfl,
      show ∀ g e2 e3, pot (ifRedex g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ => rfl]
    omega
  | run hdep => simp [esize, pot, runRedex]
  | sseq_spec hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | pure_sym => simp [esize, pot, pureRedex]
  | load_op hlib hnv2 hp2 hd2 => simp [esize, pot, loadOpRedex]
  | sseq_sym hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | memop_vals v1 v2 => simp [esize, pot, memopPtrEqVals, memopRedex]
  | memop_op hnv hp1 hp2 hd1 hd2 => simp [esize, pot, memopRedex]
  | store_op hlib hnv2 hnv3 hp2 hp3 hd2 hd3 => simp [esize, pot, storeOpRedex]
  | case_value hbr hbsz =>
    simp only [show ∀ pe pats, esize (caseRedex pe pats) = 1 + esizeAlts pats
        from fun _ _ => rfl,
      show ∀ b cval pats, pot (caseRedex (Pexpr b () (PEval cval)) pats) =
        2 * (1 + esizeAlts pats) from fun _ _ _ => rfl]
    omega
  | wseq hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega

/-- The potential is at most twice `esize` on the cone (feeds the
    case-branch reset bound). -/
theorem Frag.pot_le_two {e : CoreExpr} (hf : Frag e) : pot e ≤ 2 * esize e := by
  induction hf with
  | val_pure v => simp [esize, pot]
  | store hlib => simp [esize, pot, storeRedex]
  | load hlib => simp [esize, pot, loadRedex]
  | create hlib => simp [esize, pot, createRedex]
  | sseq hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | annot hfb ihb => simp only [esize_annot, pot_annot]; omega
  | save hb ih =>
    simp only [show ∀ sb ps b, esize (saveRedex sb ps b) = 1 + esize b
        from fun _ _ _ => rfl,
      show ∀ sb ps b, pot (saveRedex sb ps b) = 1 + pot b
        from fun _ _ _ => rfl]
    omega
  | if_ hdg hf2 hf3 ih2 ih3 =>
    simp only [show ∀ g e2 e3, esize (ifRedex g e2 e3) =
        1 + max (esize e2) (esize e3) from fun _ _ _ => rfl,
      show ∀ g e2 e3, pot (ifRedex g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ => rfl]
    omega
  | run hdep => simp [esize, pot, runRedex]
  | sseq_spec hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | pure_sym => simp [esize, pot, pureRedex]
  | load_op hlib hnv2 hp2 hd2 => simp [esize, pot, loadOpRedex]
  | sseq_sym hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | memop_vals v1 v2 => simp [esize, pot, memopPtrEqVals, memopRedex]
  | memop_op hnv hp1 hp2 hd1 hd2 => simp [esize, pot, memopRedex]
  | store_op hlib hnv2 hnv3 hp2 hp3 hd2 hd3 => simp [esize, pot, storeOpRedex]
  | case_value hbr hbsz =>
    simp only [show ∀ pe pats, esize (caseRedex pe pats) = 1 + esizeAlts pats
        from fun _ _ => rfl,
      show ∀ b cval pats, pot (caseRedex (Pexpr b () (PEval cval)) pats) =
        2 * (1 + esizeAlts pats) from fun _ _ _ => rfl]
    omega
  | wseq hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega

/-- THE POTENTIAL IS STEP-MONOTONE on the cone (jumps reset to the
    registered continuation — the second disjunct, exactly
    `Frag.esize_step_bound`'s). This is what makes the drive-fuel
    simulation's per-step `esize ≤ lemDefaultFuel` obligations
    STATIC — no fuel accumulation over the run length. -/
theorem Frag.pot_step_bound {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : Frag e) (hs : Step M (e, ρ, σ) (e', ρ', σ')) :
    pot e' ≤ pot e ∨
    ∃ l pes params cont, jumpRedex? e = some (l, pes) ∧
      lookupLabel M.labels l = some (params, cont) ∧ e' = cont := by
  induction hf generalizing e' ρ' σ' with
  | val_pure v => exact (Step.val_elim (w := .pure v) hs).elim
  | store hlib =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [pot, storeRedex]
  | load hlib =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [pot, loadRedex]
  | create hlib =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [pot, createRedex]
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds', v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ih1 hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_sseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [pot_sseq]
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rw [he1]
      left
      simp only [pot_sseq, pot_annot, pot_ofVal_annot]
      omega
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [pot_sseq]
      omega
  | wseq hf1 hf2 ih1 ih2 =>
    rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds', v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ih1 hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_wseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [pot_wseq]
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rw [he1]
      left
      simp only [pot_wseq, pot_annot, pot_ofVal_annot]
      omega
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_wseq, hj], hl, h1⟩
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ihb hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_annot]
        omega
      · rw [hnj] at hj1
        cases hj1
    · subst hb
      obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [pot_annot]
      omega
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_annot_of_not_root _ _ hg, hj], hl, h1⟩
  | save hb ih =>
    obtain ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ := hs.save_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp only [show ∀ sb ps b, pot (saveRedex sb ps b) = 1 + pot b
      from fun _ _ _ => rfl]
    omega
  | if_ hdg hf2 hf3 ih2 ih3 =>
    rcases hs.if_inv with ⟨-, hout⟩ | ⟨-, hout⟩ <;>
      (obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout)
    · subst h1
      left
      simp only [show ∀ g e2 e3, pot (ifRedex g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ => rfl]
      omega
    · subst h1
      left
      simp only [show ∀ g e2 e3, pot (ifRedex g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ => rfl]
      omega
  | run hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    exact .inr ⟨_, _, params, cont, rfl, hl, h1⟩
  | sseq_spec hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ih1 hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_sseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (specPat_ne_base hpat.symm).elim
    · exact (specPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [pot_sseq]
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rw [he1]
      left
      simp only [pot_sseq, pot_annot, pot_ofVal_annot]
      omega
    · exact (symPat_ne_spec hpat).elim
  | pure_sym =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [pot, pureRedex]
  | load_op hlib hnv2 hp2 hd2 =>
    obtain ⟨pv, -, hout⟩ := hs.load_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [pot, loadOpRedex]
  | sseq_sym hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      rcases ih1 hstep with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_sseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [pot_sseq]
      omega
  | memop_vals v1 v2 =>
    rw [show memopPtrEqVals v1 v2 = Expr [] (Ememop PtrEq
      [Pexpr [] () (PEval v1), Pexpr [] () (PEval v2)]) from rfl] at hs
    cases hs with
    | run hj hl hvs => simp at hj
    | memop_ptreq h1 h2 hmem =>
      left
      simp [pot, memopPtrEqVals, memopRedex]
    | memop_eval hnv hv1 hv2 =>
      rw [valueFromPexprs_pair, valueFromPexpr_val, valueFromPexpr_val] at hnv
      cases hnv
  | memop_op hnv hp1 hp2 hpd1 hpd2 =>
    obtain ⟨v1, v2, hv1, hv2, hout⟩ := hs.memop_op_inv hnv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [pot, memopRedex]
  | store_op hlib hnv2 hnv3 hp2 hp3 hpd2 hpd3 =>
    obtain ⟨pv, cv, hv2', hv3', -, hout⟩ := hs.store_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [pot, storeOpRedex]
  | case_value hbr hbsz =>
    obtain ⟨cval', e'', hv, hsel, hout⟩ := hs.case_inv
    obtain rfl : _ = cval' := Option.some.inj (valueFromPexpr_val _ _ ▸ hv)
    obtain ⟨h1, -, -⟩ : e' = e'' ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    have h2e := (hbr e' hsel).pot_le_two
    have hsz := hbsz e' hsel
    simp only [show ∀ pe pats, esize (caseRedex pe pats) = 1 + esizeAlts pats
        from fun _ _ => rfl] at hsz
    simp only [show ∀ b cval pats,
      pot (caseRedex (Pexpr b () (PEval cval)) pats) =
        2 * (1 + esizeAlts pats) from fun _ _ _ => rfl]
    omega

/-! ## The state-inert cone (memory-action-free programs preserve
the memory state — what lets fib's exported total equation pin its
final state) -/

/-- Syntactically memory-inert: no actions, no memops, no case (the
    conservative closure the fib-class exhibits need; memops and
    loads are individually state-preserving but excluded to keep the
    predicate one-directional and small). -/
def stateInert : CoreExpr → Bool
  | Expr _ (Esseq _ e1 e2) => stateInert e1 && stateInert e2
  | Expr _ (Ewseq _ e1 e2) => stateInert e1 && stateInert e2
  | Expr _ (Eannot _ b) => stateInert b
  | Expr _ (Eif _ e2 e3) => stateInert e2 && stateInert e3
  | Expr _ (Esave _ _ body) => stateInert body
  | Expr _ (Eaction _) => false
  | Expr _ (Ememop _ _) => false
  | Expr _ (Ecase _ _) => false
  | _ => true

/-- Every registered label body is state-inert. -/
def StateInertLabels (M : MachineCtx) : Prop :=
  ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
    stateInert cont = true

/-- State-inert cone steps preserve the memory state, and inertness
    is preserved (or the step is the jump, which also preserves the
    state). -/
theorem Frag.stateInert_step {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : Frag e) (hin : stateInert e = true)
    (hs : Step M (e, ρ, σ) (e', ρ', σ')) :
    σ' = σ ∧ (stateInert e' = true ∨
      ∃ l pes params cont, jumpRedex? e = some (l, pes) ∧
        lookupLabel M.labels l = some (params, cont) ∧ e' = cont) := by
  induction hf generalizing e' ρ' σ' with
  | val_pure v => exact (Step.val_elim (w := .pure v) hs).elim
  | store hlib => simp [stateInert, storeRedex] at hin
  | load hlib => simp [stateInert, loadRedex] at hin
  | create hlib => simp [stateInert, createRedex] at hin
  | sseq hf1 hf2 ih1 ih2 =>
    obtain ⟨hin1, hin2⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, Bool.and_eq_true] using hin
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds', v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ih1 hin1 hstep
      rcases hin' with hin1' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by
          simp [stateInert, Bool.and_eq_true, hin1', hin2])⟩
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl (by simpa [stateInert] using hin2)⟩
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_sseq, hj], hl, h1⟩⟩
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
  | wseq hf1 hf2 ih1 ih2 =>
    obtain ⟨hin1, hin2⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, Bool.and_eq_true] using hin
    rcases hs.wseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, ds', v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ih1 hin1 hstep
      rcases hin' with hin1' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by
          simp [stateInert, Bool.and_eq_true, hin1', hin2])⟩
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl (by simpa [stateInert] using hin2)⟩
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_wseq, hj], hl, h1⟩⟩
  | annot hfb ihb =>
    rename_i ds0 b0
    have hinb : stateInert b0 = true := by simpa [stateInert] using hin
    rcases hs.annot_inv with ⟨hg, hnj, b', ρ'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ihb hinb hstep
      rcases hin' with hinb' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by simpa [stateInert] using hinb')⟩
      · rw [hnj] at hj1
        cases hj1
    · subst hb
      obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      refine ⟨h3, .inl ?_⟩
      have : stateInert c = true := by simpa [stateInert] using hinb
      simpa [stateInert] using this
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_annot_of_not_root _ _ hg, hj], hl, h1⟩⟩
  | save hb ih =>
    obtain ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ := hs.save_inv
    obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact ⟨h3, .inl (by simpa [stateInert, saveRedex] using hin)⟩
  | if_ hdg hf2 hf3 ih2 ih3 =>
    obtain ⟨hin2, hin3⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, ifRedex, Bool.and_eq_true] using hin
    rcases hs.if_inv with ⟨-, hout⟩ | ⟨-, hout⟩ <;>
      (obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout)
    · subst h1
      exact ⟨h3, .inl hin2⟩
    · subst h1
      exact ⟨h3, .inl hin3⟩
  | run hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    exact ⟨h3, .inr ⟨_, _, params, cont, rfl, hl, h1⟩⟩
  | sseq_spec hf1 hf2 ih1 ih2 =>
    obtain ⟨hin1, hin2⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, Bool.and_eq_true] using hin
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ih1 hin1 hstep
      rcases hin' with hin1' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by
          simp [stateInert, Bool.and_eq_true, hin1', hin2])⟩
      · rw [hnj] at hj1
        cases hj1
    · exact (specPat_ne_base hpat.symm).elim
    · exact (specPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_sseq, hj], hl, h1⟩⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl (by simpa [stateInert] using hin2)⟩
    · exact (symPat_ne_spec hpat).elim
  | pure_sym =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv
    obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    exact ⟨h3, .inl rfl⟩
  | load_op hlib hnv2 hp2 hd2 => simp [stateInert, loadOpRedex] at hin
  | sseq_sym hf1 hf2 ih1 ih2 =>
    obtain ⟨hin1, hin2⟩ : stateInert _ = true ∧ stateInert _ = true := by
      simpa [stateInert, Bool.and_eq_true] using hin
    rcases hs.sseq_inv with ⟨e1', ρ'', σ'', hnj, hstep, hout⟩ |
        ⟨_, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, hpat, _, _, hout⟩
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = ρ'' ∧ σ' = σ'' := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      obtain ⟨hσ'', hin'⟩ := ih1 hin1 hstep
      rcases hin' with hin1' | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · exact ⟨h3.trans hσ'', .inl (by
          simp [stateInert, Bool.and_eq_true, hin1', hin2])⟩
      · rw [hnj] at hj1
        cases hj1
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, h3⟩ : e' = cont ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      exact ⟨h3, .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_sseq, hj], hl, h1⟩⟩
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨h1, -, h3⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      exact ⟨h3, .inl hin2⟩
  | memop_vals v1 v2 => simp [stateInert, memopPtrEqVals, memopRedex] at hin
  | memop_op hnv hp1 hp2 hpd1 hpd2 => simp [stateInert, memopRedex] at hin
  | store_op hlib hnv2 hnv3 hp2 hp3 hpd2 hpd3 =>
    simp [stateInert, storeOpRedex] at hin
  | case_value hbr hbsz =>
    simp [stateInert, caseRedex] at hin

/-! ## THE GENERIC MEASURE→DRIVE-FUEL SIMULATION (the cost half) -/

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


/-- The simulation's pure conclusion: the drive at fuel k DELIVERS,
    the delivered value and final state satisfy the readout, and on
    the state-inert cone the final state is the initial one. -/
abbrev DriveDoneAt (M : MachineCtx) (aids : Nat → Nat) (k : Nat) (e : CoreExpr)
    (ρ : EnvStack) (σ : Mem) (ψ : value → Mem → Prop) : Prop :=
  ∃ v σ', driveU M aids k (M.thread e ρ) σ = .done v σ' ∧ ψ v σ' ∧
    (stateInert e = true ∧ StateInertLabels M → σ' = σ)

/-- THE SIMULATION (audit F-02, the cost half): the total statement
    judgment's budget IS drive fuel — one engine step
    (`engine_step_matchU`) per budget unit, the delivery protocol
    prepaid by the value clause, jumps prepaid by the mandatory
    decrease. Strong induction on the budget; no Löb, no
    step-indexing, no per-example Step chains ever again. -/
theorem wpt_drive_aux {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : LabelSpecT GF) (ψ : value → Mem → Prop) :
    ∀ (k : Nat) (e : CoreExpr) (ev0 : Fmap sym value)
      (evs : List (Fmap sym value)) (σ : Mem) (ns nt : Nat) (aids : Nat → Nat),
      Frag e → pot e ≤ lemDefaultFuel →
      iprop(stateInterp (GF := GF) σ ns ([] : List Empty) nt ∗
          blockSpecsT M Ls (readoutPost ψ) ∗
          wpt M Ls k (readoutPost ψ) e (ev0 :: evs)) ⊢
        iprop(|={⊤|}=> ⌜DriveDoneAt M aids k e (ev0 :: evs) σ ψ⌝) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
  intro e ev0 evs σ ns nt aids hfrag hpot
  cases htv : toVal e with
  | some w =>
    have he := ofVal_of_toVal htv
    subst he
    rw [wpt_val_eq k (toVal_ofVal w)]
    iintro ⟨Hσ, -, ⟨%hc, Hpost⟩⟩
    imod Hpost with Hpost
    imod Hpost $$ %σ %ns %([] : List Empty) %nt Hσ with %hψ
    ipureintro
    cases w with
    | pure v =>
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
        have hc' : 1 ≤ k := by simpa [deliveryCost] using hc
        omega⟩
      refine ⟨v, σ, ?_, hψ, fun _ => rfl⟩
      rw [driveU_succ, stepOutcomes_thread, outcomesU_done hwf]
    | annot ds v =>
      obtain ⟨k'', rfl⟩ : ∃ k'', k = k'' + 2 := ⟨k - 2, by
        have hc' : 2 ≤ k := by simpa [deliveryCost] using hc
        omega⟩
      refine ⟨v, σ, ?_, hψ, fun _ => rfl⟩
      rw [show k'' + 2 = (k'' + 1) + 1 from rfl,
        show driveU M aids (k'' + 1 + 1)
            (M.thread (ofVal (.annot ds v)) (ev0 :: evs)) σ =
          driveU M (fun i => aids (i + 1)) (k'' + 1)
            (M.thread (ofVal (.pure v)) (ev0 :: evs)) σ from by
          rw [driveU_succ, stepOutcomes_thread, outcomesU_remove_annot],
        driveU_succ, stepOutcomes_thread, outcomesU_done hwf]
  | none =>
    cases hjr : jumpRedex? e with
    | some lp =>
      obtain ⟨l, pes⟩ := lp
      rw [wpt_jump_eq k htv hjr]
      iintro ⟨Hσ, #HB, HJ⟩
      imod HJ with ⟨%params, %cont, %vs, %ev0', %evs', %m, %hρ, %hl, %hvs,
        %hμ, HLs⟩
      obtain ⟨rfl, rfl⟩ : ev0 = ev0' ∧ evs = evs' := by
        injection hρ with h1 h2
        exact ⟨h1, h2⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hs : Step M (e, ev0 :: evs, σ)
          (cont, bindArgs params vs (ev0 :: evs), σ) :=
        Step.run_of_jumpRedex hjr hl hvs
      obtain ⟨ev0'', hbind⟩ := Step.env_cons hs
      ihave Hwpt := HB $$ %l %params %cont %vs %ev0 %evs %m %hl HLs
      ihave Hwpt' : wpt M Ls k' (readoutPost ψ) cont
          (bindArgs params vs (ev0 :: evs)) $$ [Hwpt]
      · iapply wpt_mono_k (show m ≤ k' by omega) cont _ $$ Hwpt
      rw [hbind]
      have hstep_eq : driveU M aids (k' + 1) (M.thread e (ev0 :: evs)) σ =
          driveU M (fun i => aids (i + 1)) k'
            (M.thread cont (ev0'' :: evs)) σ := by
        rw [driveU_succ, stepOutcomes_thread,
          engine_step_matchU (aids 0) hfrag
            (Nat.le_trans hfrag.esize_le_pot hpot) hs, hbind]
      have hf : DriveDoneAt M (fun i => aids (i + 1)) k' cont
            (ev0'' :: evs) σ ψ →
          DriveDoneAt M aids (k' + 1) e (ev0 :: evs) σ ψ := by
        rintro ⟨v, σ', hdone, hψ, hin⟩
        refine ⟨v, σ', ?_, hψ, ?_⟩
        · rw [hstep_eq]
          exact hdone
        · rintro ⟨hinE, hinL⟩
          exact hin ⟨hinL l params cont hl, hinL⟩
      iapply fupd_finally_mono (pure_mono hf)
      iapply IH k' (Nat.lt_succ_self k') cont ev0'' evs σ ns nt
        (fun i => aids (i + 1)) (hQf l params cont hl)
        (hQpot l params cont hl) $$ [$Hσ $HB $Hwpt']
    | none =>
      cases k with
      | zero =>
        rw [wpt_zero_step_eq htv hjr]
        iintro ⟨-, -, %hf⟩
        exact hf.elim
      | succ k' =>
        rw [wpt_step_eq k' htv hjr]
        iintro ⟨Hσ, #HB, H⟩
        imod H $$ %σ %ns %([] : List Empty) %nt Hσ with ⟨%hred, Hwand⟩
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs, hM, hnil⟩ := hps
        subst hnil
        obtain ⟨re, rρ, rM⟩ := r'
        simp only at hs hM
        obtain rfl : M = rM := hM.symm
        obtain ⟨ev0', rfl⟩ := Step.env_cons hs
        imod Hwand $$ %(⟨re, ev0' :: evs, M⟩ : CoreRt) %σ' %([] : List CoreRt)
          %(⟨hs, rfl, rfl⟩ :
            ((⟨e, ev0 :: evs, M⟩ : CoreRt), σ) -<([] : List Empty)>->
              ((⟨re, ev0' :: evs, M⟩ : CoreRt), σ', []))
          with ⟨Hσ', Hwpt⟩
        have hfrag' : Frag re := hfrag.step hQf hs
        have hpot' : pot re ≤ lemDefaultFuel := by
          rcases Frag.pot_step_bound hfrag hs with hle |
              ⟨l0, pes0, params0, cont0, hj0, hl0, rfl⟩
          · omega
          · rw [hjr] at hj0
            cases hj0
        have hstep_eq : driveU M aids (k' + 1) (M.thread e (ev0 :: evs)) σ =
            driveU M (fun i => aids (i + 1)) k'
              (M.thread re (ev0' :: evs)) σ' := by
          rw [driveU_succ, stepOutcomes_thread,
            engine_step_matchU (aids 0) hfrag
              (Nat.le_trans hfrag.esize_le_pot hpot) hs]
        have hf : DriveDoneAt M (fun i => aids (i + 1)) k' re
              (ev0' :: evs) σ' ψ →
            DriveDoneAt M aids (k' + 1) e (ev0 :: evs) σ ψ := by
          rintro ⟨v, σ'', hdone, hψ, hin⟩
          refine ⟨v, σ'', ?_, hψ, ?_⟩
          · rw [hstep_eq]
            exact hdone
          · rintro ⟨hinE, hinL⟩
            obtain ⟨hσeq, hin'⟩ := hfrag.stateInert_step hinE hs
            rcases hin' with hinE' | ⟨l0, pes0, _, _, hj0, -, -⟩
            · rw [hin ⟨hinE', hinL⟩, hσeq]
            · rw [hjr] at hj0
              cases hj0
        iapply fupd_finally_mono (pure_mono hf)
        iapply IH k' (Nat.lt_succ_self k') re ev0' evs σ' (ns + 1) nt
          (fun i => aids (i + 1)) hfrag' hpot' $$ [$Hσ' $HB $Hwpt]

/-! ## The launch: pure engine conclusions from a SpikeGpreS functor
list (the total analog of `engine_adequacyU`/`engine_adequacyJ`) -/

/-- THE TOTAL ENGINE BOUND at any machine context (the cost half's
    engine face): a proved total judgment at budget k plus the
    seeded footprint implies the drive AT FUEL k delivers a value
    satisfying ψ — an unconditional `.done` equation, no partiality;
    state pinned on the state-inert cone. -/
theorem wpt_engine_boundU {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel) (hcoh : Coh M.tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c)) ⊢
        iprop(blockSpecsT M Ls (readoutPost ψ) ∗
          wpt M Ls k (readoutPost ψ) e₀ (ev00 :: evs0)))
    (aids : Nat → Nat) :
    ∃ v σ', driveU M aids k (M.thread e₀ (ev00 :: evs0)) σ₀ = .done v σ' ∧
      ψ v σ' ∧ (stateInert e₀ = true ∧ StateInertLabels M → σ' = σ₀) := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine (fupd_finally_soundness .hasLC 0 ⊤ _ ?_)
  iintro %Hinv Hcred
  letI : InvGS_gen .hasLC GF := Hinv
  icases Hcred with -
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk }
  imod (spikeCells_alloc M.tagDefs σ₀ m₀ hcoh) $$ [$Hmi $Hbi]
    with ⟨%mm, %mb, %hmbo, Hmi, Hbi, Hcells⟩
  ihave HW := hwp $$ Hcells
  icases HW with ⟨HB, Hwpt⟩
  ihave Hσ : stateInterp (GF := GF) σ₀ 0 ([] : List Empty) 0 $$ [Hmi Hbi Hki]
  · rw [stateInterp_eq]
    iexists mm, mb, (∅ : SpikeHeapF AllocCursor)
    isplit
    · ipureintro
      exact hmbo.cohG hcoh
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  iapply wpt_drive_aux hwf hQf hQpot Ls ψ k e₀ ev00 evs0 σ₀ 0 0 aids
    hfrag hpot $$ [$Hσ $HB $Hwpt]

/-- THE TOTAL ENGINE BOUND AT THE JUMP PROFILE (the driveJ instance —
    the lane the loop exhibits export through). -/
theorem wpt_engine_boundJ {GF : BundledGFunctors} [SpikeGpreS GF]
    {Q : LabelMap} {p : sym} {rs : core_run_state} (hQ : LabeledAt rs p Q)
    (hQf : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel) (hcoh : Coh (procCtx p rs).tagDefs σ₀ m₀)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn (procCtx p rs).tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c)) ⊢
        iprop(blockSpecsT (procCtx p rs) Ls (readoutPost ψ) ∗
          wpt (procCtx p rs) Ls k (readoutPost ψ) e₀ (ev00 :: evs0)))
    (aids : Nat → Nat) :
    ∃ v σ', driveJ rs aids k (procThread p e₀ (ev00 :: evs0)) σ₀ = .done v σ' ∧
      ψ v σ' ∧ (stateInert e₀ = true ∧
        (∀ l params cont, lookupLabel Q l = some (params, cont) →
          stateInert cont = true) → σ' = σ₀) := by
  have hlbl : (procCtx p rs).labels = Q := procCtx_labels hQ
  have h := wpt_engine_boundU (M := procCtx p rs) (procCtx_wf p rs)
    (fun l params cont hl => hQf l params cont (by rwa [hlbl] at hl))
    (fun l params cont hl => hQpot l params cont (by rwa [hlbl] at hl))
    Ls e₀ ev00 evs0 σ₀ m₀ hfrag hpot hcoh ψ k hwp aids
  rw [show (procCtx p rs).thread e₀ (ev00 :: evs0) =
    procThread p e₀ (ev00 :: evs0) from rfl,
    driveU_procCtx p rs k aids _ σ₀] at h
  obtain ⟨v, σ', h1, h2, h3⟩ := h
  refine ⟨v, σ', h1, h2, fun hin => h3 ⟨hin.1, ?_⟩⟩
  intro l params cont hl
  exact hin.2 l params cont (by rwa [hlbl] at hl)

/-- ALLOCATION-AWARE total engine bound (alloc arc P1.3): as
    `wpt_engine_boundU`, but launched through the one shared
    `launchResources` helper — the client's total proof receives the
    footprint cells AND `allocCap reqs`; the cursor ghost heap is
    launched NONEMPTY at the real `⟨lastAddress, nextAllocId⟩`. The
    cursor-free launcher above remains for no-allocation programs
    (charter P1.3's incremental-migration allowance). -/
theorem wpt_engine_boundU_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx} (hwf : M.SeqWF)
    (hQf : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel M.labels l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell) (reqs : List AllocReq)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel)
    (hl : LaunchCoh M.tagDefs σ₀ m₀ reqs)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c) ∗ allocCap M.tagDefs reqs) ⊢
        iprop(blockSpecsT M Ls (readoutPost ψ) ∗
          wpt M Ls k (readoutPost ψ) e₀ (ev00 :: evs0)))
    (aids : Nat → Nat) :
    ∃ v σ', driveU M aids k (M.thread e₀ (ev00 :: evs0)) σ₀ = .done v σ' ∧
      ψ v σ' ∧ (stateInert e₀ = true ∧ StateInertLabels M → σ' = σ₀) := by
  refine pure_soundness (PROP := IProp GF) ?_
  refine (fupd_finally_soundness .hasLC 0 ⊤ _ ?_)
  iintro %Hinv Hcred
  letI : InvGS_gen .hasLC GF := Hinv
  icases Hcred with -
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk }
  imod (launchResources M.tagDefs σ₀ m₀ reqs hl) $$ [$Hmi $Hbi $Hki]
    with ⟨Hσ, Hcells, Hcap⟩
  ihave HW := hwp $$ [$Hcells $Hcap]
  icases HW with ⟨HB, Hwpt⟩
  iapply wpt_drive_aux hwf hQf hQpot Ls ψ k e₀ ev00 evs0 σ₀ 0 0 aids
    hfrag hpot $$ [$Hσ $HB $Hwpt]

/-- The jump-profile instance of the allocation-aware total bound
    (mirror of `wpt_engine_boundJ`). -/
theorem wpt_engine_boundJ_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {Q : LabelMap} {p : sym} {rs : core_run_state} (hQ : LabeledAt rs p Q)
    (hQf : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      Frag cont)
    (hQpot : ∀ l params cont, lookupLabel Q l = some (params, cont) →
      pot cont ≤ lemDefaultFuel)
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (e₀ : CoreExpr) (ev00 : Fmap sym value) (evs0 : List (Fmap sym value))
    (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell) (reqs : List AllocReq)
    (hfrag : Frag e₀) (hpot : pot e₀ ≤ lemDefaultFuel)
    (hl : LaunchCoh (procCtx p rs).tagDefs σ₀ m₀ reqs)
    (ψ : value → Mem → Prop) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn (procCtx p rs).tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c) ∗ allocCap (procCtx p rs).tagDefs reqs) ⊢
        iprop(blockSpecsT (procCtx p rs) Ls (readoutPost ψ) ∗
          wpt (procCtx p rs) Ls k (readoutPost ψ) e₀ (ev00 :: evs0)))
    (aids : Nat → Nat) :
    ∃ v σ', driveJ rs aids k (procThread p e₀ (ev00 :: evs0)) σ₀ = .done v σ' ∧
      ψ v σ' ∧ (stateInert e₀ = true ∧
        (∀ l params cont, lookupLabel Q l = some (params, cont) →
          stateInert cont = true) → σ' = σ₀) := by
  have hlbl : (procCtx p rs).labels = Q := procCtx_labels hQ
  have h := wpt_engine_boundU_alloc (M := procCtx p rs) (procCtx_wf p rs)
    (fun l params cont hlk => hQf l params cont (by rwa [hlbl] at hlk))
    (fun l params cont hlk => hQpot l params cont (by rwa [hlbl] at hlk))
    Ls e₀ ev00 evs0 σ₀ m₀ reqs hfrag hpot hl ψ k hwp aids
  rw [show (procCtx p rs).thread e₀ (ev00 :: evs0) =
    procThread p e₀ (ev00 :: evs0) from rfl,
    driveU_procCtx p rs k aids _ σ₀] at h
  obtain ⟨v, σ', h1, h2, h3⟩ := h
  refine ⟨v, σ', h1, h2, fun hin => h3 ⟨hin.1, ?_⟩⟩
  intro l params cont hlk
  exact hin.2 l params cont (by rwa [hlbl] at hlk)

/-! ## The logical half: Iris TotalAdequacy consumed as-is -/

/-- TERMINATION OVER THE UNIFIED RELATION (the logical half): a
    proved total judgment plus the seeded footprint implies STRONG
    NORMALIZATION of the Iris thread-pool relation at the launched
    configuration — the pinned `twp_total` consumed as-is (`wpt`
    collapses into TWP by `wpt_sound`). No fuel, no engine
    vocabulary: termination as a fact about the one derived
    relation the Language instance runs on. -/
theorem wpt_strongly_normalizing {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx}
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (Ψ : ∀ [SpikeGS .hasLC GF], SpikeVal → EnvStack → IProp GF)
    (e₀ : CoreExpr) (ρ₀ : EnvStack) (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (hcoh : Coh M.tagDefs σ₀ m₀) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c)) ⊢
        iprop(blockSpecsT M Ls Ψ ∗ wpt M Ls k Ψ e₀ ρ₀)) :
    Relation.StronglyNormalizing Language.ErasedStep
      ([(⟨e₀, ρ₀, M⟩ : CoreRt)], σ₀) := by
  refine twp_total (hlc := .hasLC) (GF := GF) Stuckness.NotStuck _ σ₀
    (fun _ => iprop(True)) 0 0 ?_
  intro instInv
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk }
  imod (spikeCells_alloc M.tagDefs σ₀ m₀ hcoh) $$ [$Hmi $Hbi]
    with ⟨%mm, %mb, %hmbo, Hmi, Hbi, Hcells⟩
  imodintro
  iexists fun (σ' : Mem) (_ : Nat) (_ : List Empty) (_ : Nat) =>
    iprop(∃ mm mb mk, ⌜CohG σ' mm mb mk⌝ ∗
      metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk)
  iexists fun _ => 0
  iexists fun _ => iprop(True)
  iexists fun _ _ _ _ => fupd_intro
  dsimp only
  isplitl [Hmi Hbi Hki]
  · iexists mm, mb, (∅ : SpikeHeapF AllocCursor)
    isplit
    · ipureintro
      exact hmbo.cohG hcoh
    isplitl [Hmi]
    · iexact Hmi
    isplitl [Hbi]
    · iexact Hbi
    · iexact Hki
  · iintro Hcred
    icases Hcred with -
    ihave HW := hwp $$ Hcells
    icases HW with ⟨HB, Hwpt⟩
    iapply twp.mono (fun v => BI.true_intro)
    iapply wpt_sound k e₀ ρ₀ $$ HB Hwpt

/-- ALLOCATION-AWARE strong normalization (alloc arc P1.3): as
    `wpt_strongly_normalizing`, launched through `launchResources` —
    the total proof may allocate (it receives `allocCap reqs`; the
    cursor ghost heap is launched nonempty). -/
theorem wpt_strongly_normalizing_alloc {GF : BundledGFunctors} [SpikeGpreS GF]
    {M : MachineCtx}
    (Ls : ∀ [SpikeGS .hasLC GF], LabelSpecT GF)
    (Ψ : ∀ [SpikeGS .hasLC GF], SpikeVal → EnvStack → IProp GF)
    (e₀ : CoreExpr) (ρ₀ : EnvStack) (σ₀ : Mem) (m₀ : SpikeHeapF SpikeCell)
    (reqs : List AllocReq) (hl : LaunchCoh M.tagDefs σ₀ m₀ reqs) (k : Nat)
    (hwp : ∀ [SpikeGS .hasLC GF],
      iprop(([∗map] i ↦ c ∈ m₀, cellOwn M.tagDefs (hlc := .hasLC) (GF := GF) i
          (.own 1) c) ∗ allocCap M.tagDefs reqs) ⊢
        iprop(blockSpecsT M Ls Ψ ∗ wpt M Ls k Ψ e₀ ρ₀)) :
    Relation.StronglyNormalizing Language.ErasedStep
      ([(⟨e₀, ρ₀, M⟩ : CoreRt)], σ₀) := by
  refine twp_total (hlc := .hasLC) (GF := GF) Stuckness.NotStuck _ σ₀
    (fun _ => iprop(True)) 0 0 ?_
  intro instInv
  imod (genHeap_init (L := Int) (V := MetaCell) (H := SpikeHeapF)
    (∅ : SpikeHeapF MetaCell)) with ⟨%Gm, Hmi, -, -⟩
  imod (genHeap_init (L := Int) (V := CerbMem.AbsByte) (H := SpikeHeapF)
    (∅ : SpikeHeapF CerbMem.AbsByte)) with ⟨%Gb, Hbi, -, -⟩
  imod (genHeap_init (L := Int) (V := AllocCursor) (H := SpikeHeapF)
    (∅ : SpikeHeapF AllocCursor)) with ⟨%Gk, Hki, -, -⟩
  letI instGS : SpikeGS .hasLC GF :=
    { byteGS := Gb, metaGS := Gm, cursorGS := Gk }
  imod (launchResources M.tagDefs σ₀ m₀ reqs hl) $$ [$Hmi $Hbi $Hki]
    with ⟨Hσ, Hcells, Hcap⟩
  imodintro
  iexists fun (σ' : Mem) (_ : Nat) (_ : List Empty) (_ : Nat) =>
    iprop(∃ mm mb mk, ⌜CohG σ' mm mb mk⌝ ∗
      metaInterp mm ∗ byteInterp mb ∗ cursorInterp mk)
  iexists fun _ => 0
  iexists fun _ => iprop(True)
  iexists fun _ _ _ _ => fupd_intro
  dsimp only
  isplitl [Hσ]
  · iexact Hσ
  · iintro Hcred
    icases Hcred with -
    ihave HW := hwp $$ [$Hcells $Hcap]
    icases HW with ⟨HB, Hwpt⟩
    iapply twp.mono (fun v => BI.true_intro)
    iapply wpt_sound k e₀ ρ₀ $$ HB Hwpt

end CerberusHeapLang
