/-
CerberusHeapLang.Potential — the step-monotone size potential `pot`
on fragment terms: the STATIC fuel bound both adequacy theorems carry.

The engine's `get_ctx` is fuel-bounded (budget `lemDefaultFuel`,
Soundness.lean header "FUEL HONESTY") and its exhaustion leaf is
opaque, so every per-step engine equation — the device lemma
`outcomesU_of_step` the `driveU` lanes consume, `loop_step_frag` the
production collapse consumes, the certification `engine_step_matchU` —
carries `esize e ≤ lemDefaultFuel` for the CURRENT term. The generic
growth bound `Frag.esize_step_bound` (≤ +1 per step) would couple a
drive statement's fuel premise to the run length. This module installs
the classical remedy: a potential/ranking function on terms — value
leaves 1, redex leaves 2 (a leaf's rewrite into its annotated value is
prepaid), compounds structural, case nodes priced at twice their
branch size — such that

  * `Frag.esize_le_pot`   : `esize e ≤ pot e`, and
  * `Frag.pot_step_bound` : along a fragment step `pot` never
    increases, except at a jump, where it resets to the registered
    body's own potential.

So the two STATIC premises `pot e₀ ≤ lemDefaultFuel` and
`pot cont ≤ lemDefaultFuel` (per registered label body) bound `esize`
at every reachable term, independent of the run length. Both the
partial drive classification (Adequacy.lean, `drive_classifyU`) and
the total budget simulation (TotalAdequacy.lean, `wpt_drive_aux`)
consume exactly these; `Frag.pot_le_two` (`pot e ≤ 2 * esize e`) is
how the exhibits discharge them from a closed `esize`.
-/
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

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
  | store => simp [esize, pot, storeRedex]
  | load => simp [esize, pot, loadRedex]
  | create => simp [esize, pot, createRedex]
  | kill hstatic => simp [esize, pot, killRedex]
  | kill_op hstatic hnvK hpK hdK => simp [esize, pot, killOpRedex]
  | sseq hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | annot hfb ihb => simp only [esize_annot, pot_annot]; omega
  | save hp hd hb ih =>
    simp only [show ∀ sb ps b, esize (saveRedex sb ps b) = 1 + esize b
        from fun _ _ _ => rfl,
      show ∀ sb ps b, pot (saveRedex sb ps b) = 1 + pot b
        from fun _ _ _ => rfl]
    omega
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    simp only [show ∀ g e2 e3, esize (ifRedex g e2 e3) =
        1 + max (esize e2) (esize e3) from fun _ _ _ => rfl,
      show ∀ g e2 e3, pot (ifRedex g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ => rfl]
    omega
  | run hpes hdep => simp [esize, pot, runRedex]
  | sseq_spec hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | pure_sym => simp [esize, pot, pureRedex]
  | load_op hnv2 hp2 hd2 => simp [esize, pot, loadOpRedex]
  | sseq_sym hb hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | memop_vals v1 v2 => simp [esize, pot, memopPtrEqVals, memopRedex]
  | memop_op hnv hp1 hp2 hd1 hd2 => simp [esize, pot, memopRedex]
  | store_op hnv hp2 hp3 hd2 hd3 => simp [esize, pot, storeOpRedex]
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
  | store => simp [esize, pot, storeRedex]
  | load => simp [esize, pot, loadRedex]
  | create => simp [esize, pot, createRedex]
  | kill hstatic => simp [esize, pot, killRedex]
  | kill_op hstatic hnvK hpK hdK => simp [esize, pot, killOpRedex]
  | sseq hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | annot hfb ihb => simp only [esize_annot, pot_annot]; omega
  | save hp hd hb ih =>
    simp only [show ∀ sb ps b, esize (saveRedex sb ps b) = 1 + esize b
        from fun _ _ _ => rfl,
      show ∀ sb ps b, pot (saveRedex sb ps b) = 1 + pot b
        from fun _ _ _ => rfl]
    omega
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    simp only [show ∀ g e2 e3, esize (ifRedex g e2 e3) =
        1 + max (esize e2) (esize e3) from fun _ _ _ => rfl,
      show ∀ g e2 e3, pot (ifRedex g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ => rfl]
    omega
  | run hpes hdep => simp [esize, pot, runRedex]
  | sseq_spec hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | pure_sym => simp [esize, pot, pureRedex]
  | load_op hnv2 hp2 hd2 => simp [esize, pot, loadOpRedex]
  | sseq_sym hb hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | memop_vals v1 v2 => simp [esize, pot, memopPtrEqVals, memopRedex]
  | memop_op hnv hp1 hp2 hd1 hd2 => simp [esize, pot, memopRedex]
  | store_op hnv hp2 hp3 hd2 hd3 => simp [esize, pot, storeOpRedex]
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
  | store =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [pot, storeRedex]
  | load =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [pot, loadRedex]
  | create =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [pot, createRedex]
  | kill hstatic =>
    obtain ⟨σ'', hmem, hout⟩ := hs.kill_inv
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ'' := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [pot, killRedex]
  | kill_op hstatic hnvK hpK hdK =>
    obtain ⟨pv, -, hout⟩ := hs.kill_op_inv hnvK
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left; simp [pot, killOpRedex]
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
  | @save sb ps body hp hd hb ih =>
    rcases hs.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
        ⟨cvals, hnv, hvals, hout⟩
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = _ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      simp only [show ∀ sb ps b, pot (saveRedex sb ps b) = 1 + pot b
        from fun _ _ _ => rfl]
      omega
    · obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
        simpa [Prod.mk.injEq] using hout
      subst h1
      left
      rw [show pot (Expr [] (Esave sb (saveParamsWithValues ps cvals) body)) =
          1 + pot body from rfl,
        show pot (saveRedex sb ps body) = 1 + pot body from rfl]
      omega
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
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
  | run hpes hdep =>
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
  | load_op hnv2 hp2 hd2 =>
    obtain ⟨pv, -, hout⟩ := hs.load_op_inv hnv2
    obtain ⟨h1, -, -⟩ : e' = _ ∧ ρ' = ρ ∧ σ' = σ := by
      simpa [Prod.mk.injEq] using hout
    subst h1
    left
    simp [pot, loadOpRedex]
  | sseq_sym hb hf1 hf2 ih1 ih2 =>
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
  | store_op hnv hp2 hp3 hpd2 hpd3 =>
    obtain ⟨pv, cv, hv2', hv3', hout⟩ := hs.store_op_inv hnv
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

end CerberusHeapLang
