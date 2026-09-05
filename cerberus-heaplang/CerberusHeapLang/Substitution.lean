/-
Substitution preserves the covered pure-expression grammar and its depth.

E5 case branches use the engine's `subst_sym_expr` after pattern matching.
These lemmas discharge their fragment obligations uniformly for every list
of matched bindings, including the engine's truncated tuple matches.
The result is proved against the genuine fuel-indexed substitution, under
its depth bound; no evaluator or substitute semantics is introduced.
-/
import CerberusHeapLang.Soundness

set_option autoImplicit false
namespace CerberusHeapLang

theorem peDepthList_map_eq (f : generic_pexpr Unit sym → generic_pexpr Unit sym)
    (ps : List (generic_pexpr Unit sym)) (h : ∀ p ∈ ps, peDepth (f p) = peDepth p) :
    peDepthList (ps.map f) = peDepthList ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, peDepthList_cons, h p (List.mem_cons_self ..),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem peDepthAlts_map_eq
    (f : pattern × generic_pexpr Unit sym → generic_pexpr Unit sym)
    (ps : List (pattern × generic_pexpr Unit sym))
    (h : ∀ q ∈ ps, peDepth (f q) = peDepth q.2) :
    peDepthAlts (ps.map fun q => (q.1, f q)) = peDepthAlts ps := by
  induction ps with
  | nil => rfl
  | cons q ps ih =>
    rcases q with ⟨pat, p⟩
    simp only [List.map_cons, peDepthAlts_cons, h (pat, p) (List.mem_cons_self ..),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem PePure.subst_lemFuel (fuel : Nat) (pe : generic_pexpr Unit _root_.sym) (x : _root_.sym) (v : value)
    (hp : PePure pe) (hf : peDepth pe ≤ fuel) :
    PePure (subst_sym_pexpr_lemFuel fuel x v pe) ∧
      peDepth (subst_sym_pexpr_lemFuel fuel x v pe) = peDepth pe := by
  induction fuel generalizing pe with
  | zero => have := peDepth_pos pe; omega
  | succ n ih =>
    cases hp with
    | val a w => exact ⟨.val a w, rfl⟩
    | sym a s =>
      change PePure (Pexpr a () (if symbolEquality x s then PEval v else PEsym s)) ∧
        peDepth (Pexpr a () (if symbolEquality x s then PEval v else PEsym s)) = 1
      split
      · exact ⟨.val a v, rfl⟩
      · exact ⟨.sym a s, rfl⟩
    | undef a loc ub => exact ⟨.undef a loc ub, rfl⟩
    | op a op hop h1 h2 =>
      simp only [peDepth_op] at hf
      obtain ⟨hp1, hd1⟩ := ih _ h1 (by omega)
      obtain ⟨hp2, hd2⟩ := ih _ h2 (by omega)
      exact ⟨.op a op hop hp1 hp2, by simp only [subst_sym_pexpr_lemFuel, peDepth_op, hd1, hd2]⟩
    | arrayShift a ty h1 h2 =>
      simp only [peDepth_array_shift] at hf
      obtain ⟨hp1, hd1⟩ := ih _ h1 (by omega)
      obtain ⟨hp2, hd2⟩ := ih _ h2 (by omega)
      exact ⟨.arrayShift a ty hp1 hp2, by simp only [subst_sym_pexpr_lemFuel, peDepth_array_shift, hd1, hd2]⟩
    | ctorTy a c hc pb ty =>
      simp only [peDepth_ctor1, peDepth_val] at hf
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact ⟨.ctorTy a c hc pb ty, rfl⟩
    | @ctor a c hc pes hps =>
      simp only [peDepth_ctor] at hf
      have hs q (hq : q ∈ pes) := ih q (hps q hq) (by have := peDepth_le_list_of_mem hq; omega)
      refine ⟨.ctor a c hc ?_, ?_⟩
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact (hs p hp).1
      · change 1 + peDepthList (pes.map _) = 1 + peDepthList pes
        rw [peDepthList_map_eq _ pes (fun q hq => (hs q hq).2)]
    | @case_ a p pats h1 hps =>
      simp only [peDepth_case] at hf
      obtain ⟨hp1, hd1⟩ := ih _ h1 (by omega)
      have hs (q : pattern × generic_pexpr Unit _root_.sym) (hq : q ∈ pats) :
          PePure (if in_pattern x q.1 then q.2 else subst_sym_pexpr_lemFuel n x v q.2) ∧
          peDepth (if in_pattern x q.1 then q.2 else subst_sym_pexpr_lemFuel n x v q.2) = peDepth q.2 := by
        split
        · exact ⟨hps q hq, rfl⟩
        · exact ih q.2 (hps q hq) (by have := peDepth_le_alts_of_mem hq; omega)
      refine ⟨.case_ a hp1 ?_, ?_⟩
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact (hs p hp).1
      · change 1 + peDepth (subst_sym_pexpr_lemFuel n x v p) + peDepthAlts (pats.map _) = _
        rw [hd1, peDepthAlts_map_eq _ pats (fun q hq => (hs q hq).2)]
        rfl
    | not_ a hp =>
      simp only [peDepth_not] at hf
      obtain ⟨hp', hd⟩ := ih _ hp (by omega)
      exact ⟨.not_ a hp', by simp only [subst_sym_pexpr_lemFuel, peDepth_not, hd]⟩
    | if_ a h1 h2 h3 =>
      simp only [peDepth_if] at hf
      obtain ⟨hp1, hd1⟩ := ih _ h1 (by omega)
      obtain ⟨hp2, hd2⟩ := ih _ h2 (by omega)
      obtain ⟨hp3, hd3⟩ := ih _ h3 (by omega)
      exact ⟨.if_ a hp1 hp2 hp3, by simp only [subst_sym_pexpr_lemFuel, peDepth_if, hd1, hd2, hd3]⟩
    | convInt a ity hp =>
      simp only [peDepth_conv_int] at hf
      obtain ⟨hp', hd⟩ := ih _ hp (by omega)
      exact ⟨.convInt a ity hp', by simp only [subst_sym_pexpr_lemFuel, peDepth_conv_int, hd]⟩
    | wrapI a ity op h1 h2 =>
      simp only [peDepth_wrapI] at hf
      obtain ⟨hp1, hd1⟩ := ih _ h1 (by omega)
      obtain ⟨hp2, hd2⟩ := ih _ h2 (by omega)
      exact ⟨.wrapI a ity op hp1 hp2, by simp only [subst_sym_pexpr_lemFuel, peDepth_wrapI, hd1, hd2]⟩
    | catchExc a ity op h1 h2 =>
      simp only [peDepth_catch] at hf
      obtain ⟨hp1, hd1⟩ := ih _ h1 (by omega)
      obtain ⟨hp2, hd2⟩ := ih _ h2 (by omega)
      exact ⟨.catchExc a ity op hp1 hp2, by simp only [subst_sym_pexpr_lemFuel, peDepth_catch, hd1, hd2]⟩
    | isUnsigned a hp hd0 =>
      simp only [peDepth_is_unsigned] at hf
      obtain ⟨hp', hd⟩ := ih _ hp (by omega)
      exact ⟨.isUnsigned a hp' (hd.trans hd0), by simp only [subst_sym_pexpr_lemFuel, peDepth_is_unsigned, hd]⟩
    | @call a nm pes hps =>
      simp only [peDepth_call] at hf
      have hs q (hq : q ∈ pes) := ih q (hps q hq) (by have := peDepth_le_list_of_mem hq; omega)
      refine ⟨.call a nm ?_, ?_⟩
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        exact (hs p hp).1
      · change 1 + peDepthList (pes.map _) + stdBudget nm = 1 + peDepthList pes + stdBudget nm
        rw [peDepthList_map_eq _ pes (fun q hq => (hs q hq).2)]

theorem PePure.subst {pe : generic_pexpr Unit _root_.sym} (hp : PePure pe)
    (x : _root_.sym) (v : value) (hf : peDepth pe ≤ lemDefaultFuel) :
    PePure (subst_sym_pexpr x v pe) ∧ peDepth (subst_sym_pexpr x v pe) = peDepth pe :=
  hp.subst_lemFuel lemDefaultFuel pe x v hf

/-- A covered pure operand is a fragment expression whether it is already
    a value or still needs the evaluator. -/
theorem Frag.of_pePure {pe : generic_pexpr Unit sym} (an : List _root_.annot)
    (hp : PePure pe) (hf : peDepth pe ≤ lemDefaultFuel) : Frag (Expr an (Epure pe)) := by
  cases hv : valueFromPexpr pe with
  | none => exact .pure_op hv hp hf
  | some v =>
    obtain ⟨pb, rfl⟩ := valueFromPexpr_some_iff.mp hv
    exact .val_pure v

theorem subst_sym_expr_pure (x : sym) (v : value) (an : List _root_.annot)
    (pe : generic_pexpr Unit sym) :
    subst_sym_expr x v (Expr an (Epure pe) : CoreExpr) = Expr an (Epure (subst_sym_pexpr x v pe)) := rfl

/-- Arbitrary matched bindings preserve a pure branch's grammar and depth.
    This is independent of which value or pattern produced the bindings. -/
theorem substFold_pure (binds : List (sym × value)) (an : List _root_.annot)
    (pe : generic_pexpr Unit sym) (hp : PePure pe) (hf : peDepth pe ≤ lemDefaultFuel) :
    ∃ pe', substFold (Expr an (Epure pe)) binds = Expr an (Epure pe') ∧
      PePure pe' ∧ peDepth pe' = peDepth pe := by
  induction binds with
  | nil => exact ⟨pe, rfl, hp, rfl⟩
  | cons pair rest ih =>
    rcases pair with ⟨x, v⟩
    obtain ⟨p, he, hp', hd⟩ := ih
    obtain ⟨hs, hsd⟩ := hp'.subst x v (by rw [hd]; exact hf)
    exact ⟨subst_sym_pexpr x v p, by rw [substFold_cons, he, subst_sym_expr_pure],
      hs, hsd.trans hd⟩

theorem Frag.substFold_pure (binds : List (sym × value)) (an : List _root_.annot)
    (pe : generic_pexpr Unit sym) (hp : PePure pe) (hf : peDepth pe ≤ lemDefaultFuel) :
    Frag (substFold (Expr an (Epure pe)) binds) := by
  obtain ⟨p, he, hp', hd⟩ := CerberusHeapLang.substFold_pure binds an pe hp hf
  rw [he]
  exact .of_pePure an hp' (by rw [hd]; exact hf)

end CerberusHeapLang
