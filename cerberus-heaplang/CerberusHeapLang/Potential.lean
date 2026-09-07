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
prepaid), the NEGATIVE action leaf 10 (E5: its rewrite at the enclosing
`bound` adds a binder, a two-component `unseq`, the excluded action and a
symbol read around the re-plugged `pure(Unit)`), compounds ADDITIVE (E5:
the sum of the children plus one — the classical size; E4's `max` form
could not absorb a rewrite that nests the continuation deeper), case
nodes the sum of their branches plus two — such that

  * `Frag.esize_le_pot`   : `esize e ≤ pot e`, and
  * `Frag.pot_step_bound` : along a fragment step `pot` never
    increases, except at a jump, where it resets to the registered
    body's own potential.

So the two STATIC premises `pot e₀ ≤ lemDefaultFuel` and
`pot cont ≤ lemDefaultFuel` (per registered label body) bound `esize`
at every reachable term, independent of the run length. Both the
partial fuel induction (Adequacy.lean, `drive_safe_aux`) and the total
budget inductions (ProdLoop.lean, `wpt_driver_aux`/`wpt_driver_cps`)
consume exactly these; the exhibits discharge them by computing `pot` on
the closed program term (`t1Main_pot`'s pattern). E5 RETIRED
`Frag.pot_le_two` (`pot e ≤ 2 * esize e`): false for the additive
potential (a chain of `n` sequenced leaves has `esize` ≈ n and `pot` ≈ 3n).
-/
import CerberusHeapLang.Soundness

set_option autoImplicit false

namespace CerberusHeapLang

/-! ## The size potential -/

mutual
/-- The step-monotone size potential (header note): like `esize`,
    but value leaves cost 1, the negative action 10 (E5), all other
    leaves 2 (a redex leaf's rewrite into an annotated value is prepaid),
    compounds are additive (E5), and a case node prices its branches at
    their summed potential plus two (the selected branch is a branch with
    values substituted, `pot_subst`, E5). -/
def pot : CoreExpr → Nat
  | Expr _ (Esseq _ e1 e2) => 1 + pot e1 + pot e2
  | Expr _ (Ewseq _ e1 e2) => 1 + pot e1 + pot e2
  | Expr _ (Eannot _ b) => 1 + pot b
  | Expr _ (Ebound b) => 1 + pot b
  | Expr _ (Eif _ e2 e3) => 1 + pot e2 + pot e3
  | Expr _ (Esave _ _ body) => 1 + pot body
  | Expr _ (Ecase _ pats) => 2 + potAlts pats
  | Expr _ (Eunseq es) => 2 + potList es
  | Expr _ (Elet _ _ e2) => 1 + pot e2
  | Expr _ (End es) => 1 + potList es
  | Expr _ (Epar es) => 1 + potList es
  | Expr _ (Epure (Pexpr _ _ (PEval _))) => 1
  | Expr _ (Eaction (Paction polarity.Neg0 _)) => 10
  | _ => 2
/-- E4: the potential of an `unseq`'s components — one unit per component
    (the completion round rewrites the node into the annotated tuple,
    which costs 2, so a one-component `unseq` still decreases) plus the
    components' potentials (a component's step decreases its own). -/
def potList : List CoreExpr → Nat
  | [] => 0
  | e :: rest => 1 + pot e + potList rest
/-- E5: the potential of a `case`'s alternatives — the SUM of the branch
    potentials (the selected branch's potential is its own, `pot_subst`). -/
def potAlts : List (pattern × CoreExpr) → Nat
  | [] => 0
  | (_, e) :: rest => pot e + potAlts rest
end

@[simp] theorem potAlts_nil : potAlts [] = 0 := rfl
@[simp] theorem potAlts_cons (q : pattern × CoreExpr) (rest : List (pattern × CoreExpr)) :
    potAlts (q :: rest) = pot q.2 + potAlts rest := by
  obtain ⟨pq, eq⟩ := q; rfl

theorem pot_le_potAlts_of_mem {q : pattern × CoreExpr} {pats : List (pattern × CoreExpr)}
    (h : q ∈ pats) : pot q.2 ≤ potAlts pats := by
  induction pats with
  | nil => cases h
  | cons r rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [potAlts_cons]; omega
    · have := ih h; simp only [potAlts_cons]; omega

@[simp] theorem pot_sseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    pot (Expr a (Esseq pat e1 e2)) = 1 + pot e1 + pot e2 := rfl

@[simp] theorem pot_wseq {a : List annot} {pat : pattern} {e1 e2 : CoreExpr} :
    pot (Expr a (Ewseq pat e1 e2)) = 1 + pot e1 + pot e2 := rfl

@[simp] theorem pot_annot {a : List annot} {ds : List dyn_annotation}
    {b : CoreExpr} : pot (Expr a (Eannot ds b)) = 1 + pot b := rfl

@[simp] theorem pot_bound {a : List annot} {b : CoreExpr} :
    pot (Expr a (Ebound b)) = 1 + pot b := rfl

@[simp] theorem pot_unseq {a : List annot} {es : List CoreExpr} :
    pot (Expr a (Eunseq es)) = 2 + potList es := rfl

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
    | (rename_i pact
       obtain ⟨pol, act⟩ := pact
       cases pol
       · exact Nat.le_succ _
       · show 1 ≤ 10; omega)

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
    pot (Expr a (Eif g e2 e3)) = 1 + pot e2 + pot e3 := rfl

@[simp] theorem pot_save {a : List annot} {sb : sym × core_base_type}
    {ps : List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    {body : CoreExpr} :
    pot (Expr a (Esave sb ps body)) = 1 + pot body := rfl

@[simp] theorem pot_case {a : List annot} {pe : generic_pexpr Unit sym}
    {pats : List (pattern × CoreExpr)} :
    pot (Expr a (Ecase pe pats)) = 2 + potAlts pats := rfl

@[simp] theorem pot_let {a : List annot} {pat : pattern} {pe : generic_pexpr Unit sym}
    {e2 : CoreExpr} : pot (Expr a (Elet pat pe e2)) = 1 + pot e2 := rfl

@[simp] theorem pot_nd {a : List annot} {es : List CoreExpr} :
    pot (Expr a (End es)) = 1 + potList es := rfl

/-- E5: the NEGATIVE action's potential — 10, exactly what the rewrite costs
    above the re-plugged `pure(Unit)`: `bound(ctxA[neg])` against `bound(let
    weak (_, s) = unseq(Eexcluded n act, ctxA'[pure(Unit)]) in pure(s))` — the
    binder 1, the `unseq` node 2, the excluded component 1 + 2, the plugged
    component 1 + its `pure(Unit)` 1, the tail `pure(s)` 2 (`pot_negRewrite_le`). -/
@[simp] theorem pot_neg {a : List annot} {act : CoreAction} :
    pot (Expr a (Eaction (Paction polarity.Neg0 act))) = 10 := rfl

@[simp] theorem pot_excluded {a : List annot} {n : Nat} {act : CoreAction} :
    pot (Expr a (Eexcluded n act)) = 2 := rfl

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

@[simp] theorem pot_action_pos {a : List annot}
    {act : CoreAction} :
    pot (Expr a (Eaction (Paction polarity.Pos act))) = 2 := rfl

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
theorem esizeAlts_le_potAlts_of {pats : List (pattern × CoreExpr)}
    (h : ∀ q ∈ pats, esize q.2 ≤ pot q.2) : esizeAlts pats ≤ potAlts pats := by
  induction pats with
  | nil => simp [esizeAlts]
  | cons q rest ih =>
    obtain ⟨pq, eq⟩ := q
    have h1 := h (pq, eq) (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only at h1
    simp only [esizeAlts, potAlts_cons]
    exact Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_add_right _ _), Nat.le_trans h2 (Nat.le_add_left _ _)⟩

mutual
/-- E5: `esize ≤ pot` for EVERY term (the fragment-free form of
    `Frag.esize_le_pot`, the size invariant of `wps_bound`/`wpt_bound`'s
    static premises): every leaf costs at least 1 (`pot_pos`), every
    compound node's `pot` dominates its `esize` arm-wise (max ≤ sum). -/
theorem esize_le_pot : ∀ e : CoreExpr, esize e ≤ pot e
  | Expr a (Esseq pat e1 e2) => by
      have h1 := esize_le_pot e1
      have h2 := esize_le_pot e2
      have hm : max (esize e1) (esize e2) ≤ pot e1 + pot e2 :=
        Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_add_right _ _), Nat.le_trans h2 (Nat.le_add_left _ _)⟩
      rw [esize_sseq, pot_sseq]; omega
  | Expr a (Ewseq pat e1 e2) => by
      have h1 := esize_le_pot e1
      have h2 := esize_le_pot e2
      have hm : max (esize e1) (esize e2) ≤ pot e1 + pot e2 :=
        Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_add_right _ _), Nat.le_trans h2 (Nat.le_add_left _ _)⟩
      rw [esize_wseq, pot_wseq]; omega
  | Expr a (Eif g e2 e3) => by
      have h1 := esize_le_pot e2
      have h2 := esize_le_pot e3
      have hm : max (esize e2) (esize e3) ≤ pot e2 + pot e3 :=
        Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_add_right _ _), Nat.le_trans h2 (Nat.le_add_left _ _)⟩
      rw [show esize (Expr a (Eif g e2 e3)) = 1 + max (esize e2) (esize e3) from rfl, pot_if]; omega
  | Expr a (Eannot ds b) => by
      have h := esize_le_pot b
      rw [esize_annot, pot_annot]; omega
  | Expr a (Ebound b) => by
      have h := esize_le_pot b
      rw [esize_bound, pot_bound]; omega
  | Expr a (Esave sb ps body) => by
      have h := esize_le_pot body
      rw [show esize (Expr a (Esave sb ps body)) = 1 + esize body from rfl, pot_save]; omega
  | Expr a (Ecase pe pats) => by
      have h := esizeAlts_le_potAlts pats
      rw [show esize (Expr a (Ecase pe pats)) = 1 + esizeAlts pats from rfl, pot_case]; omega
  | Expr a (Eunseq es) => by
      have h := esizeList_le_potList es
      rw [esize_unseq, pot_unseq]; omega
  | Expr a (Elet pat pe e2) => by
      have h := esize_le_pot e2
      rw [show esize (Expr a (Elet pat pe e2)) = 1 + esize e2 from rfl, pot_let]; omega
  | Expr a (End es) => by
      have h := esizeList_le_potList es
      rw [show esize (Expr a (End es)) = 1 + esizeList es from rfl, pot_nd]; omega
  | Expr a (Epar es) => by
      have h := esizeList_le_potList es
      rw [show esize (Expr a (Epar es)) = 1 + esizeList es from rfl,
        show pot (Expr a (Epar es)) = 1 + potList es from rfl]; omega
  | Expr a (Epure _) => pot_pos _
  | Expr a (Ememop _ _) => pot_pos _
  | Expr a (Eaction _) => pot_pos _
  | Expr a (Eccall _ _ _ _) => pot_pos _
  | Expr a (Eproc _ _ _) => pot_pos _
  | Expr a (Erun _ _ _) => pot_pos _
  | Expr a (Ewait _) => pot_pos _
  | Expr a (Eexcluded _ _) => pot_pos _
theorem esizeList_le_potList : ∀ es : List CoreExpr, esizeList es ≤ potList es
  | [] => Nat.le_refl 0
  | e :: es => by
      have h1 := esize_le_pot e
      have h2 := esizeList_le_potList es
      simp only [esizeList, potList_cons]; omega
theorem esizeAlts_le_potAlts : ∀ pats : List (pattern × CoreExpr), esizeAlts pats ≤ potAlts pats
  | [] => Nat.le_refl 0
  | (pq, e) :: rest => by
      have h1 := esize_le_pot e
      have h2 := esizeAlts_le_potAlts rest
      simp only [esizeAlts, potAlts_cons]
      exact Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_add_right _ _), Nat.le_trans h2 (Nat.le_add_left _ _)⟩
end

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
        1 + pot e2 + pot e3 from fun _ _ _ _ => rfl]
    have hm : max (esize _) (esize _) ≤ pot _ + pot _ :=
      Nat.max_le.mpr ⟨Nat.le_trans ih2 (Nat.le_add_right _ _), Nat.le_trans ih3 (Nat.le_add_left _ _)⟩
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
  | case_value hall hbr hbsz ih _ =>
    simp only [show ∀ an pe pats, esize (caseRedex an pe pats) = 1 + esizeAlts pats
        from fun _ _ _ => rfl,
      show ∀ an pe pats, pot (caseRedex an pe pats) = 2 + potAlts pats from fun _ _ _ => rfl]
    have := esizeAlts_le_potAlts_of ih
    omega
  | wseq hf1 hf2 ih1 ih2 => simp only [esize_wseq, pot_wseq]; omega
  | unseq hne hcc hf ih =>
    simp only [esize_unseq, pot_unseq]
    have := esizeList_le_potList_of ih
    omega
  | neg_store_op _ _ _ _ _ => simp [esize, pot, negStoreRedex, negActRedex]
  | neg_store => simp [esize, pot, negActRedex]
  | excluded_store => simp [esize, pot, excludedStoreRedex]
  | excluded_store_op _ _ _ _ _ => simp [esize, pot, excludedStoreOpRedex]
  | case_op _ _ _ hall hbr hbsz ih _ =>
    simp only [show ∀ an pe pats, esize (caseRedex an pe pats) = 1 + esizeAlts pats
        from fun _ _ _ => rfl,
      show ∀ an pe pats, pot (caseRedex an pe pats) = 2 + potAlts pats from fun _ _ _ => rfl]
    have := esizeAlts_le_potAlts_of ih
    omega
  | nd h2 hall ih =>
    simp only [show ∀ an es, esize (ndRedex an es) = 1 + esizeList es from fun _ _ => rfl,
      show ∀ an es, pot (ndRedex an es) = 1 + potList es from fun _ _ => rfl]
    have := esizeList_le_potList_of ih
    omega

/-! ## E5: the substitution and plugging equations of the potential -/

theorem potAlts_map_subst_le {g : pattern × CoreExpr → CoreExpr}
    (pats : List (pattern × CoreExpr))
    (h : ∀ q ∈ pats, pot (g q) ≤ pot q.2) :
    potAlts (pats.map (fun q => (q.1, g q))) ≤ potAlts pats := by
  induction pats with
  | nil => exact Nat.le_refl _
  | cons q rest ih =>
    obtain ⟨pq, eq⟩ := q
    simp only [List.map_cons, potAlts_cons]
    have h1 := h (pq, eq) (List.mem_cons_self ..)
    have h2 := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only at h1
    omega

theorem potList_map_le {f : CoreExpr → CoreExpr} (es : List CoreExpr)
    (h : ∀ e ∈ es, pot (f e) ≤ pot e) :
    potList (es.map f) ≤ potList es := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e rest ih =>
    simp only [List.map_cons, potList_cons]
    have := h e (List.mem_cons_self ..)
    have := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    omega

/-- A pure node's potential is at most 2 (a value leaf 1, a redex leaf 2). -/
theorem pot_pure_le_two {a : List annot} (pe : generic_pexpr Unit sym) :
    pot (Expr a (Epure pe)) ≤ 2 := by
  rcases pe with ⟨b, u, p⟩
  cases u
  cases p <;> first | exact Nat.le_succ _ | exact Nat.le_refl _

/-- `pot` reads the expression skeleton (values inside pure expressions are
    leaves): substitution does not increase it — a `pure(x)` may become a
    `pure(v)` (2 → 1) — at a fuel covering the depth (`esize_subst`'s twin).
    The negative-action leaf is preserved: `subst_sym_paction` keeps the
    polarity (Core_aux.lean:516). -/
theorem pot_subst_lemFuel :
    ∀ (n : Nat) (e : CoreExpr) (x : sym) (v : value), esize e ≤ n →
      pot (subst_sym_expr_lemFuel n x v e) ≤ pot e := by
  intro n
  induction n with
  | zero => intro e x v h; have := esize_pos e; omega
  | succ n ih =>
    intro e x v hn
    rcases e with ⟨a, e_⟩
    cases e_ with
    | Esseq pat e1 e2 =>
      rw [esize_sseq] at hn
      simp only [subst_sym_expr_lemFuel, pot_sseq]
      have h1 := ih e1 x v (by omega)
      split
      · omega
      · have h2 := ih e2 x v (by omega); omega
    | Ewseq pat e1 e2 =>
      rw [esize_wseq] at hn
      simp only [subst_sym_expr_lemFuel, pot_wseq]
      have h1 := ih e1 x v (by omega)
      split
      · omega
      · have h2 := ih e2 x v (by omega); omega
    | Eif g e2 e3 =>
      rw [show esize (Expr a (Eif g e2 e3)) = 1 + max (esize e2) (esize e3) from rfl] at hn
      simp only [subst_sym_expr_lemFuel, pot_if]
      have h2 := ih e2 x v (by omega)
      have h3 := ih e3 x v (by omega)
      omega
    | Eannot ds b =>
      rw [esize_annot] at hn
      simp only [subst_sym_expr_lemFuel, pot_annot]
      have := ih b x v (by omega); omega
    | Ebound b =>
      rw [esize_bound] at hn
      simp only [subst_sym_expr_lemFuel, pot_bound]
      have := ih b x v (by omega); omega
    | Esave sb ps body =>
      rw [show esize (Expr a (Esave sb ps body)) = 1 + esize body from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      split
      · exact Nat.le_refl _
      · show 1 + pot (subst_sym_expr_lemFuel n x v body) ≤ 1 + pot body
        have := ih body x v (by omega); omega
    | Eunseq es =>
      rw [esize_unseq] at hn
      simp only [subst_sym_expr_lemFuel, pot_unseq]
      have := potList_map_le (f := subst_sym_expr_lemFuel n x v) es
        (fun e he => ih e x v (by have := esize_le_esizeList_of_mem he; omega))
      omega
    | Ecase pe pats =>
      rw [show esize (Expr a (Ecase pe pats)) = 1 + esizeAlts pats from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      show 2 + potAlts (List.map _ pats) ≤ 2 + potAlts pats
      have hq' : ∀ q ∈ pats,
          pot (if in_pattern x q.1 then q.2 else subst_sym_expr_lemFuel n x v q.2) ≤ pot q.2 := by
        intro q hq
        have := esize_le_esizeAlts_of_mem hq
        split
        · exact Nat.le_refl _
        · exact ih q.2 x v (by omega)
      exact Nat.add_le_add_left (potAlts_map_subst_le pats hq') 2
    | Elet pat pe e2 =>
      rw [show esize (Expr a (Elet pat pe e2)) = 1 + esize e2 from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      split
      · exact Nat.le_refl _
      · show 1 + pot (subst_sym_expr_lemFuel n x v e2) ≤ 1 + pot e2
        have := ih e2 x v (by omega); omega
    | End es =>
      rw [show esize (Expr a (End es)) = 1 + esizeList es from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      show 1 + potList (List.map _ es) ≤ 1 + potList es
      have := potList_map_le (f := subst_sym_expr_lemFuel n x v) es
        (fun e he => ih e x v (by have := esize_le_esizeList_of_mem he; omega))
      omega
    | Epar es =>
      rw [show esize (Expr a (Epar es)) = 1 + esizeList es from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      show 1 + potList (List.map _ es) ≤ 1 + potList es
      have := potList_map_le (f := subst_sym_expr_lemFuel n x v) es
        (fun e he => ih e x v (by have := esize_le_esizeList_of_mem he; omega))
      omega
    | Epure pe =>
      rcases pe with ⟨b, u, pe_⟩
      cases u
      cases pe_ with
      | PEval v0 => exact Nat.le_refl _
      | _ => exact Nat.le_trans (pot_pure_le_two _) (Nat.le_refl _)
    | Ememop _ _ => exact Nat.le_refl _
    | Eaction pact =>
      obtain ⟨pol, act⟩ := pact
      cases pol <;> exact Nat.le_refl _
    | Eccall _ _ _ _ => exact Nat.le_refl _
    | Eproc _ _ _ => exact Nat.le_refl _
    | Erun _ _ _ => exact Nat.le_refl _
    | Ewait _ => exact Nat.le_refl _
    | Eexcluded _ _ => exact Nat.le_refl _

theorem pot_subst {e : CoreExpr} (x : sym) (v : value) (h : esize e ≤ lemDefaultFuel) :
    pot (subst_sym_expr x v e) ≤ pot e :=
  pot_subst_lemFuel lemDefaultFuel e x v h

theorem pot_subst_fold {br : CoreExpr} (binds : List (sym × value))
    (h : esize br ≤ lemDefaultFuel) :
    pot (substFold br binds) ≤ pot br := by
  induction binds with
  | nil => exact Nat.le_refl _
  | cons p rest ih =>
    obtain ⟨s0, cv⟩ := p
    rw [substFold_cons]
    exact Nat.le_trans (pot_subst s0 cv (by rw [esize_subst_fold rest h]; exact h)) ih

/-- The potential is additive in the plugged term: replacing the hole's
    content changes the total by exactly the difference (the frames' own
    weights do not depend on the hole). -/
theorem pot_apply_ctx_plug (ctx : context) (r z : CoreExpr) :
    pot (apply_ctx ctx z) + pot r = pot (apply_ctx ctx r) + pot z := by
  induction ctx with
  | CTX => simp only [apply_ctx]; omega
  | Cunseq a es1 c es2 ih =>
    simp only [apply_ctx, pot_unseq, potList_append, potList_cons]; omega
  | Cwseq a pat c e2 ih => simp only [apply_ctx, pot_wseq]; omega
  | Csseq a pat c e2 ih => simp only [apply_ctx, pot_sseq]; omega
  | Cannot a xs c ih => simp only [apply_ctx, pot_annot]; omega
  | Cbound a c ih => simp only [apply_ctx, pot_bound]; omega

/-- `add_exclusion` touches only dynamic annotations. -/
theorem pot_apply_ctx_excl (n : Nat) (ctx : context) (z : CoreExpr) :
    pot (apply_ctx (add_exclusion n ctx) z) = pot (apply_ctx ctx z) := by
  induction ctx with
  | CTX => rfl
  | Cunseq a es1 c es2 ih => simp only [add_exclusion, apply_ctx, pot_unseq, potList_append, potList_cons, ih]
  | Cwseq a pat c e2 ih => simp only [add_exclusion, apply_ctx, pot_wseq, ih]
  | Csseq a pat c e2 ih => simp only [add_exclusion, apply_ctx, pot_sseq, ih]
  | Cannot a xs c ih => simp only [add_exclusion, apply_ctx, pot_annot, ih]
  | Cbound a c ih => simp only [add_exclusion, apply_ctx, pot_bound, ih]

/-- THE REWRITE DOES NOT INCREASE THE POTENTIAL: `bound(ctxA[neg act])` at
    the leaf weight 10 pays for `bound(negRewrite …)` exactly (equal potentials). -/
theorem pot_negRewrite_le (n : Nat) (s0 : sym) (ctxA : context) (act : CoreAction) :
    pot (negRewrite n s0 ctxA act) ≤ pot (apply_ctx ctxA (negActRedex [] act)) := by
  rw [negRewrite_eq]
  simp only [pot_wseq, pot_unseq, potList_cons, potList_nil, pot_excluded, pot_pure_sym]
  rw [pot_apply_ctx_excl]
  have := pot_apply_ctx_plug ctxA (negActRedex [] act) (Expr [] (Epure (Pexpr [] () (PEval Vunit))))
  simp only [pot_pure_val] at this
  have h9 : pot (negActRedex [] act) = 10 := rfl
  omega

/-- THE POTENTIAL IS STEP-MONOTONE on the cone (jumps reset to the
    registered continuation — the second disjunct). This is what makes
    the drive-fuel simulation's per-step `esize ≤ lemDefaultFuel`
    obligations STATIC — no fuel accumulation over the run length. E1:
    stated at a kept call stack (`hκ` — the control-preserving rounds;
    CALL and RETURN leave the expression's own cone). -/
theorem Frag.pot_step_bound {M : MachineCtx} {e : CoreExpr} {ρ : EnvStack}
    {ctl ctl' : Ctl} {σ : Mem} {e' : CoreExpr} {ρ' : EnvStack} {σ' : Mem}
    (hf : Frag e) (hsz : esize e ≤ lemDefaultFuel)
    (hs : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hκ : ctl'.κ = ctl.κ) :
    pot e' ≤ pot e ∨
    ∃ l pes params cont, jumpRedex? e = some (l, pes) ∧
      lookupLabel (M.labelsAt ctl.proc) l = some (params, cont) ∧ e' = cont := by
  induction hf generalizing e' ρ' ctl' σ' with
  | call hpes hdep => exact (Step.call_ne_same_κ (callRedex?_callRedex _ _ _ _) hs hκ).elim
  | val_pure v => exact (Step.pure_val_elim hs hκ).elim
  | neg_store_op _ _ _ _ _ => exact (Step.neg_root_elim hs).elim
  | neg_store => exact (Step.neg_root_elim hs).elim
  | excluded_store =>
    obtain ⟨mv, fp, σ'', hmv, hmem, hout⟩ := hs.excluded_store_inv
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, excludedStoreRedex]
  | excluded_store_op hnvE hp2 hp3 hd2 hd3 =>
    obtain ⟨pv, cv, -, -, hout⟩ := hs.excluded_store_op_inv hnvE
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left; simp [pot, excludedStoreOpRedex]
  | case_op hnvc hp hd hall hbr hbsz _ _ =>
    rcases hs.case_inv with ⟨cval, e'', hv, hsel, hout⟩ | ⟨cval, -, -, hout⟩
    · rw [hv] at hnvc; cases hnvc
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
      subst h1
      left; exact Nat.le_refl _
  | nd h2 hall _ => exact (Step.nd_root_elim hs).elim
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
      rcases ih1 (by first | (rw [esize_sseq] at hsz; omega) | (rw [esize_wseq] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
      rcases ih1 (by first | (rw [esize_sseq] at hsz; omega) | (rw [esize_wseq] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
      rcases ihb (by first | (rw [esize_annot] at hsz; omega) | (rw [esize_bound] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
  | @bound an b hfb ihb =>
    rcases hs.bound_inv with ⟨b', ρ'', ctl'', σ'', hnj, hnc', hnn', hnv', hstep, hout⟩ |
        ⟨a1, b1, v, hb, hout⟩ | ⟨a1, a2, b1, ds, v, hb, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        hcall | ⟨ctxA0, a0, act0, hn0, hss0, hout0⟩
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ihb (by first | (rw [esize_annot] at hsz; omega) | (rw [esize_bound] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
    · obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout0
      subst h1
      left
      simp only [pot_bound]
      have hle := pot_negRewrite_le ctl.sup.excl (fresh_given_int ctl.sup.sym) ctxA0 act0
      have hb : b = apply_ctx ctxA0 (negActRedex a0 act0) := negRedex?_apply_ctx_eq hn0
      have hplug := pot_apply_ctx_plug ctxA0 (negActRedex a0 act0) (negActRedex [] act0)
      have h9 : pot (negActRedex [] act0) = 10 := rfl
      have h9' : pot (negActRedex a0 act0) = 10 := rfl
      rw [hb]
      omega
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
        1 + pot e2 + pot e3 from fun _ _ _ _ => rfl]
      omega
    · subst h1
      left
      simp only [show ∀ an g e2 e3, pot (ifRedex an g e2 e3) =
        1 + pot e2 + pot e3 from fun _ _ _ _ => rfl]
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
      rcases ih1 (by first | (rw [esize_sseq] at hsz; omega) | (rw [esize_wseq] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
      rcases ih1 (by first | (rw [esize_sseq] at hsz; omega) | (rw [esize_wseq] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
      rcases ih1 (by first | (rw [esize_sseq] at hsz; omega) | (rw [esize_wseq] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
      rcases ih1 (by first | (rw [esize_sseq] at hsz; omega) | (rw [esize_wseq] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
      rcases ih1 (by first | (rw [esize_sseq] at hsz; omega) | (rw [esize_wseq] at hsz; omega)) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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
  | @case_value an b cval pats hall hbr hbsz _ _ =>
    obtain ⟨e'', hsel, hout⟩ := hs.case_value_inv (valueFromPexpr_val _ _)
    obtain ⟨h1, -, -, -⟩ := Config.mk_inj hout
    subst h1
    left
    obtain ⟨pat, br, binds, hmem, -, rfl⟩ := select_case_some hsel
    rw [show esize (caseRedex an (Pexpr b () (PEval cval)) pats) = 1 + esizeAlts pats from rfl] at hsz
    have hbsz' := esize_le_esizeAlts_of_mem hmem
    simp only at hbsz'
    have h1 := pot_subst_fold binds (br := br) (by omega)
    have h2 := pot_le_potAlts_of_mem hmem
    simp only at h2
    rw [show pot (caseRedex an (Pexpr b () (PEval cval)) pats) = 2 + potAlts pats from rfl]
    omega
  | @unseq an es hne hcc hf ih =>
    rcases hs.unseq_inv with
        ⟨es1, e0, es2, e0', ρ'', ctl'', σ'', rfl, hv2, -, hnj, hnc', hnv', hstep, hout⟩ |
        ⟨ws, fps, cvals, rfl, hcol, hout⟩ |
        ⟨l, pes, params, cont, vs, _, _, hj, _, hl, _, hout⟩ |
        ⟨es1, e0, es2, rfl, hnv', hv2, hcall⟩
    · obtain ⟨h1, -, h3, -⟩ := Config.mk_inj hout
      subst h1 h3
      rcases ih e0 (by simp) (by have := esize_le_esizeList_of_mem (x := e0) (es := es1 ++ e0 :: es2) (List.mem_append_right _ (List.mem_cons_self ..)); rw [esize_unseq] at hsz; omega) hstep hκ with hle | ⟨l, pes, params, cont, hj1, hl, rfl⟩
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

/-! ## E5: the potential is step-monotone on NEGATIVE-FREE terms without the
fragment premise (the size invariant of `wps_bound`/`wpt_bound`'s Löb
induction: the body's every stack-preserving non-jump round keeps `pot`
non-increasing, so `esize ≤ pot ≤ lemDefaultFuel` is preserved). -/

theorem Step.pot_le {M : MachineCtx} {e e' : CoreExpr} {ρ ρ' : EnvStack}
    {ctl ctl' : Ctl} {σ σ' : Mem}
    (h : Step M (e, ρ, ctl, σ) (e', ρ', ctl', σ')) (hsz : esize e ≤ lemDefaultFuel) :
    jumpRedex? e = none → callRedex? e = none → toVal e = none →
    negFree e = true → pot e' ≤ pot e := by
  generalize hcfg : (e, ρ, ctl, σ) = c at h
  generalize hcfg' : (e', ρ', ctl', σ') = c' at h
  induction h generalizing e ρ ctl σ e' ρ' ctl' σ' with
  | sseq_ctx hnj hnc hnv hs ih =>
    cases hcfg; cases hcfg'; intro _ _ _ hnf
    rw [esize_sseq] at hsz
    simp only [negFree, Bool.and_eq_true] at hnf
    have := ih (by omega) rfl rfl hnj hnc hnv hnf.1
    simp only [pot_sseq]; omega
  | wseq_ctx hnj hnc hnv hs ih =>
    cases hcfg; cases hcfg'; intro _ _ _ hnf
    rw [esize_wseq] at hsz
    simp only [negFree, Bool.and_eq_true] at hnf
    have := ih (by omega) rfl rfl hnj hnc hnv hnf.1
    simp only [pot_wseq]; omega
  | annot_ctx hnj hnc hnv hg hs ih =>
    cases hcfg; cases hcfg'; intro _ _ _ hnf
    rw [esize_annot] at hsz
    simp only [negFree] at hnf
    have := ih (by omega) rfl rfl hnj hnc hnv hnf
    simp only [pot_annot]; omega
  | bound_ctx hnj hnc hnn hnv hs ih =>
    cases hcfg; cases hcfg'; intro _ _ _ hnf
    rw [esize_bound] at hsz
    simp only [negFree] at hnf
    have := ih (by omega) rfl rfl hnj hnc hnv hnf
    simp only [pot_bound]; omega
  | @unseq_ctx a0 es1 e0 e0' es2 ρ0 ρ0' ctl0 ctl0' σ0 σ0' hv2 hcc0 hnj hnc hnv hs ih =>
    cases hcfg; cases hcfg'; intro _ _ _ hnf
    rw [esize_unseq, esizeList_append, esizeList_cons] at hsz
    have hsz' := esize_le_esizeList_of_mem (x := e0) (es := es1 ++ e0 :: es2)
      (List.mem_append_right _ (List.mem_cons_self ..))
    simp only [negFree, negFreeList_append, negFreeList_cons, Bool.and_eq_true] at hnf
    have := ih (by omega) rfl rfl hnj hnc hnv hnf.2.1
    simp only [pot_unseq, potList_append, potList_cons]; omega
  | @neg_bound an b ctxA a act ρ0 ctl0 σ0 hn hss =>
    cases hcfg; cases hcfg'; intro _ _ _ hnf
    simp only [negFree] at hnf
    rw [negRedex?_none_of_negFree hnf] at hn; cases hn
  | excluded_store h1 h2 h3 hmv hmem =>
    cases hcfg; cases hcfg'; intro _ _ _ _
    simp only [pot_excluded, pot_annot, pot_pure_val]; omega
  | excluded_store_eval hnv hv2 hv3 =>
    cases hcfg; cases hcfg'; intro _ _ _ _
    simp only [pot_excluded]; exact Nat.le_refl _
  | run hj hl hvs => cases hcfg; cases hcfg'; intro hnj; rw [hj] at hnj; cases hnj
  | call hc hvs hf hlen => cases hcfg; cases hcfg'; intro _ hnc; rw [hc] at hnc; cases hnc
  | ret => cases hcfg; cases hcfg'; intro _ _ hnv; rw [toVal_ofValA] at hnv; cases hnv
  | ret_annot => cases hcfg; cases hcfg'; intro _ _ hnv; rw [toVal_ofValA] at hnv; cases hnv
  | pure_eval hnv hv =>
    cases hcfg; cases hcfg'; intro _ _ _ _
    rw [pot_pure_of_nv hnv, pot_pure_val]; omega
  | case_value hv hsel =>
    cases hcfg; cases hcfg'; intro _ _ _ _
    obtain ⟨pat, br, binds, hmem, -, rfl⟩ := select_case_some hsel
    rw [show esize (Expr _ (Ecase _ _)) = 1 + esizeAlts _ from rfl] at hsz
    have hle := esize_le_esizeAlts_of_mem hmem
    have hp := pot_le_potAlts_of_mem hmem
    simp only at hle hp
    have hsub := pot_subst_fold binds (br := br) (by omega)
    simp only [pot_case]; omega
  | _ =>
    cases hcfg; cases hcfg'; intro _ _ _ _
    first
      | (simp only [pot_sseq, pot_wseq, pot_annot, pot_bound, pot_if, pot_save, pot_case,
          pot_unseq, potList_cons, potList_nil, pot_pure_val, pot_ofValA_pure, pot_ofValA_annot,
          pot_action_pos, pot_memop] <;> omega)
      | (simp [pot] <;> omega)

end CerberusHeapLang
