/-
CerberusHeapLang.Potential — the step-monotone size potential `pot`
on fragment terms: the STATIC fuel bound both adequacy theorems carry.

The engine's `get_ctx` is fuel-bounded (budget `lemDefaultFuel`,
Soundness.lean header "FUEL HONESTY") and its exhaustion leaf is
opaque, so every per-step engine equation — the shipped round
`loop_step_frag` both driver lanes consume, the certification
`engine_step_matchU` — carries `esize e ≤ lemDefaultFuel` for the CURRENT term. The generic
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
partial fuel induction (Adequacy.lean, `drive_safe_aux`) and the total
budget inductions (ProdLoop.lean, `wpt_driver_aux`/`wpt_driver_cps`)
consume exactly these; `Frag.pot_le_two` (`pot e ≤ 2 * esize e`) is
how the exhibits discharge them from a closed `esize`.
-/
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

/-! ## The size potential -/

mutual
/-- The step-monotone size potential (header note): like `esize`,
    but value leaves cost 1, all other leaves 2 (a redex leaf's
    rewrite into an annotated value is prepaid), and a case node
    prices its branches at twice their `esize` (the substituted
    branch is bounded through `Frag.pot_le_two`). -/
def pot : CoreExpr → Nat
  | Expr _ (Esseq _ e1 e2) => 1 + max (pot e1) (pot e2)
  | Expr _ (Ewseq _ e1 e2) => 1 + max (pot e1) (pot e2)
  | Expr _ (Eannot _ b) => 1 + pot b
  | Expr _ (Ebound b) => 1 + pot b
  | Expr _ (Eif _ e2 e3) => 1 + max (pot e2) (pot e3)
  | Expr _ (Esave _ _ body) => 1 + pot body
  | Expr _ (Ecase _ pats) => 2 * (1 + esizeAlts pats)
  | Expr _ (Eunseq es) => 1 + potList es
  | Expr _ (Epure (Pexpr _ _ (PEval _))) => 1
  | _ => 2
/-- E4: the potential of an `unseq`'s components — one unit per component
    (the completion round rewrites the node into the annotated tuple,
    which costs 2, so a one-component `unseq` still decreases) plus the
    components' potentials (a component's step decreases its own). -/
def potList : List CoreExpr → Nat
  | [] => 0
  | e :: rest => 1 + pot e + potList rest
end

@[simp] theorem pot_sseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    pot (Expr a (Esseq pat e1 e2)) = 1 + max (pot e1) (pot e2) := rfl

@[simp] theorem pot_wseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    pot (Expr a (Ewseq pat e1 e2)) = 1 + max (pot e1) (pot e2) := rfl

@[simp] theorem pot_annot {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} : pot (Expr a (Eannot ds b)) = 1 + pot b := rfl

@[simp] theorem pot_bound {a : List annot} {b : CoreExpr} :
    pot (Expr a (Ebound b)) = 1 + pot b := rfl

@[simp] theorem pot_unseq {a : List annot} {es : List CoreExpr} :
    pot (Expr a (Eunseq es)) = 1 + potList es := rfl

@[simp] theorem potList_nil : potList [] = 0 := rfl
@[simp] theorem potList_cons (e : CoreExpr) (es : List CoreExpr) :
    potList (e :: es) = 1 + pot e + potList es := rfl

theorem potList_append (es1 es2 : List CoreExpr) :
    potList (es1 ++ es2) = potList es1 + potList es2 := by
  induction es1 with
  | nil => simp
  | cons e es ih => simp [ih]; omega

theorem pot_pos (e : CoreExpr) : 1 ≤ pot e := by
  rcases e with ⟨a, e_⟩
  cases e_ <;> first
    | (simp only [pot]; omega)
    | exact Nat.le_succ _
    | (rename_i pe
       rcases pe with ⟨b, u, p⟩
       cases p <;> first | exact Nat.le_refl _ | exact Nat.le_succ _)

theorem esizeList_le_potList_of {es : List CoreExpr} (h : ∀ e ∈ es, esize e ≤ pot e) :
    esizeList es ≤ potList es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have := h e (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp; omega

theorem potList_le_two_of {es : List CoreExpr} (h : ∀ e ∈ es, pot e ≤ 2 * esize e) :
    potList es ≤ 2 * esizeList es := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have := h e (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp; omega

/-- A component's potential decrease is the list's. -/
theorem potList_append_cons_le {e e' : CoreExpr} (es1 es2 : List CoreExpr) (h : pot e' ≤ pot e) :
    potList (es1 ++ e' :: es2) ≤ potList (es1 ++ e :: es2) := by
  rw [potList_append, potList_append, potList_cons, potList_cons]; omega

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

/-- E2: a pure node at a NON-value operand costs 2 (the redex leaf). -/
theorem pot_pure_of_nv {a : List annot} {pe : generic_pexpr Unit sym}
    (hnv : valueFromPexpr pe = none) : pot (Expr a (Epure pe)) = 2 := by
  rcases pe with ⟨b, u, p⟩
  cases u
  cases p <;> first | rfl | (rw [valueFromPexpr_val] at hnv; cases hnv)

@[simp] theorem pot_action {a : List annot}
    {p : generic_paction core_run_annotation Unit sym} :
    pot (Expr a (Eaction p)) = 2 := rfl

@[simp] theorem pot_memop {a : List annot} {mop : memop}
    {pes : List (generic_pexpr Unit sym)} :
    pot (Expr a (Ememop mop pes)) = 2 := rfl

@[simp] theorem pot_run {a : List annot} {ra : core_run_annotation} {l : sym}
    {pes : List (generic_pexpr Unit sym)} :
    pot (Expr a (Erun ra l pes)) = 2 := rfl

@[simp] theorem pot_ofValA_pure {a b : List annot} {v : value} :
    pot (ofValA (.pure a b v)) = 1 := rfl

@[simp] theorem pot_ofValA_annot {a a2 b : List annot} {ds : List dyn_annotation} {v : value} :
    pot (ofValA (.annot a a2 b ds v)) = 2 := rfl

@[simp] theorem pot_ofVal_pure {v : value} : pot (ofVal (.pure v)) = 1 := rfl

@[simp] theorem pot_ofVal_annot {ds : List dyn_annotation} {v : value} :
    pot (ofVal (.annot ds v)) = 2 := rfl

/-- `esize` is bounded by the potential on the cone. -/
theorem Frag.esize_le_pot {e : CoreExpr} (hf : Frag e) : esize e ≤ pot e := by
  induction hf with
  | call hpes hdep => simp [esize, pot, callRedex]
  | val_pure v => simp [esize, pot]
  | store => simp [esize, pot, storeRedex]
  | load => simp [esize, pot, loadRedex]
  | create => simp [esize, pot, createRedex]
  | kill => simp [esize, pot, killRedex]
  | kill_op hnvK hpK hdK => simp [esize, pot, killOpRedex]
  | alloc => simp [esize, pot, allocRedex]
  | alloc_op hnvA hp1 hp2 hd1 hd2 => simp [esize, pot, allocOpRedex]
  | create_op hnvC hp1 hp2 hd1 hd2 => simp [createOpRedex]
  | sseq hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | annot hfb ihb => simp only [esize_annot, pot_annot]; omega
  | bound hfb ihb => simp only [esize_bound, pot_bound]; omega
  | save hp hd hb ih =>
    simp only [show ∀ an sb ps b, esize (saveRedex an sb ps b) = 1 + esize b
        from fun _ _ _ _ => rfl,
      show ∀ an sb ps b, pot (saveRedex an sb ps b) = 1 + pot b
        from fun _ _ _ _ => rfl]
    omega
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    simp only [show ∀ an g e2 e3, esize (ifRedex an g e2 e3) =
        1 + max (esize e2) (esize e3) from fun _ _ _ _ => rfl,
      show ∀ an g e2 e3, pot (ifRedex an g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ _ => rfl]
    omega
  | run hpes hdep => simp [esize, pot, runRedex]
  | sseq_spec hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | pure_op hnv hp hdp => rw [pureRedex, pot_pure_of_nv hnv, esize_pure]; omega
  | load_op hnv2 hp2 hd2 => simp [esize, pot, loadOpRedex]
  | sseq_sym hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | sseq_tuple hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | wseq_tuple hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega
  | wseq_sym hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega
  | memop_vals v1 v2 => simp [esize, pot, memopPtrEqVals, memopRedex]
  | memop_op hnv hp1 hp2 hd1 hd2 => simp [esize, pot, memopRedex]
  | store_op hnv hp2 hp3 hd2 hd3 => simp [esize, pot, storeOpRedex]
  | case_value hbr hbsz =>
    simp only [show ∀ an pe pats, esize (caseRedex an pe pats) = 1 + esizeAlts pats
        from fun _ _ _ => rfl,
      show ∀ an b cval pats, pot (caseRedex an (Pexpr b () (PEval cval)) pats) =
        2 * (1 + esizeAlts pats) from fun _ _ _ _ => rfl]
    omega
  | wseq hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega
  | unseq hne hcc hf ih =>
    simp only [esize_unseq, pot_unseq]
    have := esizeList_le_potList_of ih
    omega

/-- The potential is at most twice `esize` on the cone (feeds the
    case-branch reset bound). -/
theorem Frag.pot_le_two {e : CoreExpr} (hf : Frag e) : pot e ≤ 2 * esize e := by
  induction hf with
  | call hpes hdep => simp [esize, pot, callRedex]
  | val_pure v => simp [esize, pot]
  | store => simp [esize, pot, storeRedex]
  | load => simp [esize, pot, loadRedex]
  | create => simp [esize, pot, createRedex]
  | kill => simp [esize, pot, killRedex]
  | kill_op hnvK hpK hdK => simp [esize, pot, killOpRedex]
  | alloc => simp [esize, pot, allocRedex]
  | alloc_op hnvA hp1 hp2 hd1 hd2 => simp [esize, pot, allocOpRedex]
  | create_op hnvC hp1 hp2 hd1 hd2 => simp [createOpRedex]
  | sseq hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | annot hfb ihb => simp only [esize_annot, pot_annot]; omega
  | bound hfb ihb => simp only [esize_bound, pot_bound]; omega
  | save hp hd hb ih =>
    simp only [show ∀ an sb ps b, esize (saveRedex an sb ps b) = 1 + esize b
        from fun _ _ _ _ => rfl,
      show ∀ an sb ps b, pot (saveRedex an sb ps b) = 1 + pot b
        from fun _ _ _ _ => rfl]
    omega
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    simp only [show ∀ an g e2 e3, esize (ifRedex an g e2 e3) =
        1 + max (esize e2) (esize e3) from fun _ _ _ _ => rfl,
      show ∀ an g e2 e3, pot (ifRedex an g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ _ => rfl]
    omega
  | run hpes hdep => simp [esize, pot, runRedex]
  | sseq_spec hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | pure_op hnv hp hdp => rw [pureRedex, pot_pure_of_nv hnv, esize_pure]; omega
  | load_op hnv2 hp2 hd2 => simp [esize, pot, loadOpRedex]
  | sseq_sym hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | sseq_tuple hf1 hf2 ih1 ih2 => simp only [esize_sseq, pot_sseq]; omega
  | wseq_tuple hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega
  | wseq_sym hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega
  | memop_vals v1 v2 => simp [esize, pot, memopPtrEqVals, memopRedex]
  | memop_op hnv hp1 hp2 hd1 hd2 => simp [esize, pot, memopRedex]
  | store_op hnv hp2 hp3 hd2 hd3 => simp [esize, pot, storeOpRedex]
  | case_value hbr hbsz =>
    simp only [show ∀ an pe pats, esize (caseRedex an pe pats) = 1 + esizeAlts pats
        from fun _ _ _ => rfl,
      show ∀ an b cval pats, pot (caseRedex an (Pexpr b () (PEval cval)) pats) =
        2 * (1 + esizeAlts pats) from fun _ _ _ _ => rfl]
    omega
  | wseq hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega
  | unseq hne hcc hf ih =>
    simp only [esize_unseq, pot_unseq]
    have := potList_le_two_of ih
    omega

/-- THE POTENTIAL IS STEP-MONOTONE on the cone (jumps reset to the
    registered continuation — the second disjunct). This is what makes
    the drive-fuel simulation's per-step `esize ≤ lemDefaultFuel`
    obligations STATIC — no fuel accumulation over the run length. E1:
    stated at a kept call stack (`hκ` — the control-preserving rounds;
    CALL and RETURN leave the expression's own cone). -/
theorem Frag.pot_step_bound {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {ctl ctl' : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : Frag e) (hs : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) :
    pot e' ≤ pot e ∨
    ∃ l pes params cont, jumpRedex? e = some (l, pes) ∧
      lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧ e' = cont := by
  induction hf generalizing e' ρ' ctl' σ' with
  | call hpes hdep => exact (Step.call_ne_same_κ (callRedex?_callRedex _ _ _ _) hs hκ).elim
  | val_pure v => exact (Step.pure_val_elim hs hκ).elim
  | store =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.store_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, storeRedex]
  | load =>
    obtain ⟨fp, mval, σ'', hmem, hout⟩ := hs.load_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, loadRedex]
  | create =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.create_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, createRedex]
  | create_op hnvC hp1 hp2 hd1 hd2 =>
    obtain ⟨al, ty, -, -, hout⟩ := hs.create_op_inv hnvC
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, createOpRedex]
  | kill =>
    obtain ⟨σ'', hmem, hout⟩ := hs.kill_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, killRedex]
  | kill_op hnvK hpK hdK =>
    obtain ⟨pv, -, hout⟩ := hs.kill_op_inv hnvK
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, killOpRedex]
  | alloc =>
    obtain ⟨pv, σ'', hmem, hout⟩ := hs.alloc_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, allocRedex]
  | alloc_op hnvA hp1 hp2 hd1 hd2 =>
    obtain ⟨al, sz, -, -, hout⟩ := hs.alloc_op_inv hnvA
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, allocOpRedex]
  | sseq hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, _, _, _, ds', v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih1 hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_sseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_sseq]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      rw [he1]
      left
      simp only [pot_sseq, pot_annot, ofValA, pot_pure_val]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · exact (specPat_ne_base hpat).elim
    · exact (specPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · exact (symPat_ne_base hpat).elim
    · exact (tuplePat_ne_base hpatT1).elim
    · exact (tuplePat_ne_base hpatT2).elim
    · exact (hcall.ne_same_κ hκ).elim
  | wseq hf1 hf2 ih1 ih2 =>
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, _, he1, _, hout⟩ | ⟨_, _, _, _, _, ds', v, _, _, _, he1, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpatS1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpatS2, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih1 hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_wseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_wseq]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      rw [he1]
      left
      simp only [pot_wseq, pot_annot, ofValA, pot_pure_val]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_wseq, hj], hl, h1⟩
    · exact (symPat_ne_base hpatS1).elim
    · exact (symPat_ne_base hpatS2).elim
    · exact (tuplePat_ne_base hpatT1).elim
    · exact (tuplePat_ne_base hpatT2).elim
    · exact (hcall.ne_same_κ hκ).elim
  | annot hfb ihb =>
    rcases hs.annot_inv with ⟨hg, hnj, hnc', hnv', b', ρ'', ctl'', σ'', hstep, hout⟩ |
        ⟨a2, ds2, c, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hg, hj, _, hl, _, hout⟩ |
        ⟨-, hcall⟩ | ⟨a2, b1, v', pc', κ', hb', -, hout'⟩
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ihb hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_annot]
        omega
      · rw [hnj] at hj1
        cases hj1
    · subst hb
      obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_annot]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont,
        by rw [jumpRedex?_annot_of_not_root _ _ hg, hj], hl, h1⟩
    · exact (hcall.ne_same_κ hκ).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout'
      subst h1
      left
      simp only [pot_annot, ofValA, pot_pure_val]
      omega
  | bound hfb ihb =>
    rcases hs.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨a1, b1, v, hb, hout⟩ | ⟨a1, a2, b1, ds, v, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ihb hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_bound]
        omega
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_bound, ofValA, pot_pure_val]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_bound, ofValA, pot_pure_val]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_bound, hj], hl, h1⟩
    · exact (hcall.ne_same_κ hκ).elim
  | @save an sb ps body hp hd hb ih =>
    rcases hs.save_inv with ⟨cvals, ev0', evs', hρeq, hvals, hout⟩ |
        ⟨cvals, hnv, hvals, hout⟩
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [show ∀ an sb ps b, pot (saveRedex an sb ps b) = 1 + pot b
        from fun _ _ _ _ => rfl]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      rw [show pot (Expr an (Esave sb (saveParamsWithValues ps cvals) body)) =
          1 + pot body from rfl,
        show pot (saveRedex an sb ps body) = 1 + pot body from rfl]
      omega
  | if_ hpg hdg hf2 hf3 ih2 ih3 =>
    rcases hs.if_inv with ⟨-, hout⟩ | ⟨-, hout⟩ <;>
      obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    · subst h1
      left
      simp only [show ∀ an g e2 e3, pot (ifRedex an g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ _ => rfl]
      omega
    · subst h1
      left
      simp only [show ∀ an g e2 e3, pot (ifRedex an g e2 e3) =
        1 + max (pot e2) (pot e3) from fun _ _ _ _ => rfl]
      omega
  | run hpes hdep =>
    obtain ⟨params, cont, vs, ev0', evs', hρeq, hl, hvs, hout⟩ :=
      hs.jump_inv (by rfl)
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    exact .inr ⟨_, _, params, cont, rfl, hl, h1⟩
  | sseq_spec hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih1 hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_sseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (specPat_ne_base hpat.symm).elim
    · exact (specPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_sseq]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      rw [he1]
      left
      simp only [pot_sseq, pot_annot, ofValA, pot_pure_val]
      omega
    · exact (symPat_ne_spec hpat).elim
    · exact (symPat_ne_spec hpat).elim
    · exact (specPat_ne_tuple hpatT1).elim
    · exact (specPat_ne_tuple hpatT2).elim
    · exact (hcall.ne_same_κ hκ).elim
  | pure_op hnv hp hdp =>
    obtain ⟨v, -, -, hout⟩ := hs.pure_inv hnv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left
    rw [pot_pure_val, pureRedex, pot_pure_of_nv hnv]
    omega
  | load_op hnv2 hp2 hd2 =>
    obtain ⟨pv, -, hout⟩ := hs.load_op_inv hnv2
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left
    simp [pot, loadOpRedex]
  | sseq_sym hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpatT1, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpatT2, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih1 hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_sseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · exact (symPat_ne_spec hpat.symm).elim
    · exact (symPat_ne_spec hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_sseq]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      rw [he1]
      left
      simp only [pot_sseq, pot_annot, ofValA, pot_pure_val]
      omega
    · exact (symPat_ne_tuple hpatT1).elim
    · exact (symPat_ne_tuple hpatT2).elim
    · exact (hcall.ne_same_κ hκ).elim
  | sseq_tuple hf1 hf2 ih1 ih2 =>
    rcases hs.sseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, he1, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih1 hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_sseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (tuplePat_ne_base hpat.symm).elim
    · exact (tuplePat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_sseq, hj], hl, h1⟩
    · exact (specPat_ne_tuple hpat.symm).elim
    · exact (specPat_ne_tuple hpat.symm).elim
    · exact (symPat_ne_tuple hpat.symm).elim
    · exact (symPat_ne_tuple hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_sseq]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      rw [he1]
      left
      simp only [pot_sseq, pot_annot, ofValA, pot_pure_val]
      omega
    · exact (hcall.ne_same_κ hκ).elim
  | wseq_tuple hf1 hf2 ih1 ih2 =>
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, he1, _, hout⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih1 hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_wseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (tuplePat_ne_base hpat.symm).elim
    · exact (tuplePat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_wseq, hj], hl, h1⟩
    · exact (symPat_ne_tuple hpat.symm).elim
    · exact (symPat_ne_tuple hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_wseq]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      rw [he1]
      left
      simp only [pot_wseq, pot_annot, ofValA, pot_pure_val]
      omega
    · exact (hcall.ne_same_κ hκ).elim
  | wseq_sym hf1 hf2 ih1 ih2 =>
    rcases hs.wseq_inv with ⟨e1', ρ'', ctl'', σ'', hnj, hnc', hnv', hstep, hout⟩ |
        ⟨_, _, _, _, v, _, _, hpat, _, _, hout⟩ |
        ⟨_, _, _, _, _, ds', v, _, _, hpat, _, _, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he1, _, hout⟩ |
        ⟨_, _, _, _, _, _, _, hpat, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpat, _, _, _⟩ |
        hcall
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih1 hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_wseq]
        omega
      · rw [hnj] at hj1
        cases hj1
    · exact (symPat_ne_base hpat.symm).elim
    · exact (symPat_ne_base hpat.symm).elim
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, by rw [jumpRedex?_wseq, hj], hl, h1⟩
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      simp only [pot_wseq]
      omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      rw [he1]
      left
      simp only [pot_wseq, pot_annot, ofValA, pot_pure_val]
      omega
    · exact (symPat_ne_tuple hpat).elim
    · exact (symPat_ne_tuple hpat).elim
    · exact (hcall.ne_same_κ hκ).elim
  | memop_vals v1 v2 =>
    obtain ⟨pv1, pv2, b, σ'', -, -, -, hout⟩ := hs.memop_vals_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left
    simp [pot, memopPtrEqVals, memopRedex]
  | memop_op hnv hp1 hp2 hpd1 hpd2 =>
    obtain ⟨v1, v2, hv1, hv2, hout⟩ := hs.memop_op_inv hnv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left
    simp [pot, memopRedex]
  | store_op hnv hp2 hp3 hpd2 hpd3 =>
    obtain ⟨pv, cv, hv2', hv3', hout⟩ := hs.store_op_inv hnv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left
    simp [pot, storeOpRedex]
  | case_value hbr hbsz =>
    obtain ⟨e'', hsel, hout⟩ := hs.case_value_inv (valueFromPexpr_val _ _)
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left
    have h2e := (hbr e' hsel).pot_le_two
    have hsz := hbsz e' hsel
    simp only [show ∀ an pe pats, esize (caseRedex an pe pats) = 1 + esizeAlts pats
        from fun _ _ _ => rfl] at hsz
    simp only [show ∀ an b cval pats,
      pot (caseRedex an (Pexpr b () (PEval cval)) pats) =
        2 * (1 + esizeAlts pats) from fun _ _ _ _ => rfl]
    omega
  | @unseq an es hne hcc hf ih =>
    rcases hs.unseq_inv with
        ⟨es1, e0, es2, e0', ρ'', ctl'', σ'', rfl, hv2, -, hnj, hnc', hnv', hstep, hout⟩ |
        ⟨ws, fps, cvals, rfl, hcol, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨es1, e0, es2, rfl, hnv', hv2, hcall⟩
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih e0 (by simp) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
      · left
        simp only [pot_unseq]
        have := potList_append_cons_le es1 es2 hle
        omega
      · rw [hnj] at hj1
        cases hj1
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left
      cases ws with
      | nil => exact absurd rfl hne
      | cons w ws =>
        simp only [pot_unseq, pot_annot, pot_pure_val, List.map_cons, potList_cons]
        have := pot_pos (ofValA w)
        omega
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      exact .inr ⟨l, pes, params, cont, hj, hl, h1⟩
    · exact (hcall.ne_same_κ hκ).elim

end CerberusHeapLang
