/-
CerberusHeapLang.Fragment — THE FRAGMENT, as a syntactic predicate.

`Frag e` says: `e` is built from the constructs the mirror `Step` covers,
with every evaluated operand in the covered pure grammar `PePure`. It
mentions no fuel: membership is decided by the shape of the term alone
(R2 [USER 2026-09-07], the landing charter docs/2026-09-07_landing-charter.md
§1: the fragment stays SYNTACTIC, the potential premise is a hypothesis on
the adequacy theorems — "match refinedC").

THE EVALUATOR BUDGET enters separately, as the syntactic MEASURE
`evalDepth e` — the largest `peDepth` of any pure operand in `e` — and the
adequacy theorems carry `evalDepth e ≤ LemFuel.fuel` (and the same bound on
every registered label body and procedure body) as HYPOTHESES. This is the
design's "potential premise against the quantified fuel"
(docs/2026-09-04_fuel-restatement-design.md §3) with the measure that
actually bounds the evaluator: the additive potential `pot` (Potential.lean)
never did — it bounded `esize` for the old `get_ctx` ceiling, which the pin's
measured `get_ctx` retired (cerberus-lean C3 manifest §1); the operand bound
was always the per-operand `peDepth` field the fragment carried at the fixed
constant `lemDefaultFuel`. [AGENT 2026-09-07, L2] — recorded in
cerberus-heaplang/docs/2026-09-07_l2-repin-notes.md.

THE PROOF DEVICE. Soundness.lean's `FragFuel [LemFuel]` is the same
inductive with the operand bounds `peDepth pe ≤ LemFuel.fuel` as fields
(the re-pin's form, demo-repin ce4d7de); the mirror-certification,
round-classification and driver-collapse proofs are written over it. The two
are related by `Frag.toFuel : Frag e → evalDepth e ≤ LemFuel.fuel → FragFuel e`
and `FragFuel.toFrag`, and at any positive ambient they coincide:
`fragFuel_iff : 1 ≤ LemFuel.fuel → (FragFuel e ↔ Frag e ∧ evalDepth e ≤ LemFuel.fuel)`.
Every export is stated over `Frag` + the depth hypothesis and proved through
the bridge; `FragFuel` appears in no exported statement (a proof device in
the sense of the 2026-09-03 standards-audit response, Audit.lean header).

THE DEPTH IS STABLE UNDER THE ENGINE'S SUBSTITUTION (`evalDepth_subst`,
`peDepth_subst`): replacing a symbol read by a value changes no operand's
`peDepth` (a read and a value both cost one pass), so a selected `case`
branch is no deeper than the alternatives — which is what lets the bridge
carry the fragment's `case` nodes without a fuel field.
-/
import CerberusHeapLang.Substitution
import Core_aux_lemMeasureProofs

set_option autoImplicit false
namespace CerberusHeapLang

/-! ## The evaluator depth of an expression -/

/-- Max `peDepth` over an operand list (0 at nil). -/
def pesDepth : List (generic_pexpr Unit sym) → Nat
  | [] => 0
  | pe :: pes => max (peDepth pe) (pesDepth pes)

/-- The evaluator depth of a memory action's operands — every operand of the
    engine's fifteen action shapes (Core.lean `generic_action_`); the
    fragment covers `Create`, `Alloc0`, `Kill`, `Store0`, `Load0`. -/
def actDepth : CoreAction → Nat
  | Action _ _ (Create pe1 pe2 _) => max (peDepth pe1) (peDepth pe2)
  | Action _ _ (CreateReadOnly pe1 pe2 pe3 _) =>
      max (peDepth pe1) (max (peDepth pe2) (peDepth pe3))
  | Action _ _ (Alloc0 pe1 pe2 _) => max (peDepth pe1) (peDepth pe2)
  | Action _ _ (Kill _ pe) => peDepth pe
  | Action _ _ (Store0 _ pe1 pe2 pe3 _) => max (peDepth pe1) (max (peDepth pe2) (peDepth pe3))
  | Action _ _ (Load0 pe1 pe2 _) => max (peDepth pe1) (peDepth pe2)
  | Action _ _ (SeqRMW _ pe1 pe2 _ pe3) => max (peDepth pe1) (max (peDepth pe2) (peDepth pe3))
  | Action _ _ (RMW0 pe1 pe2 pe3 pe4 _ _) =>
      max (max (peDepth pe1) (peDepth pe2)) (max (peDepth pe3) (peDepth pe4))
  | Action _ _ (Fence0 _) => 0
  | Action _ _ (CompareExchangeStrong pe1 pe2 pe3 pe4 _ _) =>
      max (max (peDepth pe1) (peDepth pe2)) (max (peDepth pe3) (peDepth pe4))
  | Action _ _ (CompareExchangeWeak pe1 pe2 pe3 pe4 _ _) =>
      max (max (peDepth pe1) (peDepth pe2)) (max (peDepth pe3) (peDepth pe4))
  | Action _ _ (LinuxFence _) => 0
  | Action _ _ (LinuxLoad pe1 pe2 _) => max (peDepth pe1) (peDepth pe2)
  | Action _ _ (LinuxStore pe1 pe2 pe3 _) => max (peDepth pe1) (max (peDepth pe2) (peDepth pe3))
  | Action _ _ (LinuxRMW pe1 pe2 pe3 _) => max (peDepth pe1) (max (peDepth pe2) (peDepth pe3))

mutual
/-- THE EVALUATOR DEPTH of an expression: the largest `peDepth` of any pure
    operand in it (a value costs one pass, `peDepth_val`; a symbol read one,
    `peDepth_sym`). It is the budget the pure evaluator needs on any operand
    the run may evaluate — the hypothesis `evalDepth e ≤ LemFuel.fuel` of
    every adequacy theorem (`full_eval_bridge`'s bound, Soundness.lean, taken
    over every operand at once). Purely syntactic; no fuel; computes by
    `decide` on a transcribed program. -/
def evalDepth : CoreExpr → Nat
  | Expr _ (Epure pe) => peDepth pe
  | Expr _ (Ememop _ pes) => pesDepth pes
  | Expr _ (Eaction (Paction _ act)) => actDepth act
  | Expr _ (Ecase pe pats) => max (peDepth pe) (evalDepthAlts pats)
  | Expr _ (Elet _ pe e2) => max (peDepth pe) (evalDepth e2)
  | Expr _ (Eif pe e2 e3) => max (peDepth pe) (max (evalDepth e2) (evalDepth e3))
  | Expr _ (Eccall _ pe1 pe2 pes) => max (max (peDepth pe1) (peDepth pe2)) (pesDepth pes)
  | Expr _ (Eproc _ _ pes) => pesDepth pes
  | Expr _ (Eunseq es) => evalDepthList es
  | Expr _ (Ewseq _ e1 e2) => max (evalDepth e1) (evalDepth e2)
  | Expr _ (Esseq _ e1 e2) => max (evalDepth e1) (evalDepth e2)
  | Expr _ (Ebound e) => evalDepth e
  | Expr _ (End es) => evalDepthList es
  | Expr _ (Esave _ ps e) => max (pesDepth (saveParamPexprs ps)) (evalDepth e)
  | Expr _ (Erun _ _ pes) => pesDepth pes
  | Expr _ (Epar es) => evalDepthList es
  | Expr _ (Ewait _) => 0
  | Expr _ (Eannot _ e) => evalDepth e
  | Expr _ (Eexcluded _ act) => actDepth act

/-- Max depth over a case alternative list's bodies (0 at nil). -/
def evalDepthAlts : List (pattern × CoreExpr) → Nat
  | [] => 0
  | (_, e) :: rest => max (evalDepth e) (evalDepthAlts rest)

/-- Max depth over an expression list (0 at nil). -/
def evalDepthList : List CoreExpr → Nat
  | [] => 0
  | e :: rest => max (evalDepth e) (evalDepthList rest)
end

@[simp] theorem pesDepth_nil : pesDepth [] = 0 := rfl
@[simp] theorem pesDepth_cons (pe : generic_pexpr Unit sym) (pes : List (generic_pexpr Unit sym)) :
    pesDepth (pe :: pes) = max (peDepth pe) (pesDepth pes) := rfl
@[simp] theorem evalDepthList_nil : evalDepthList [] = 0 := rfl
@[simp] theorem evalDepthList_cons (e : CoreExpr) (es : List CoreExpr) :
    evalDepthList (e :: es) = max (evalDepth e) (evalDepthList es) := rfl
@[simp] theorem evalDepthAlts_nil : evalDepthAlts [] = 0 := rfl
@[simp] theorem evalDepthAlts_cons (pat : pattern) (e : CoreExpr) (rest : List (pattern × CoreExpr)) :
    evalDepthAlts ((pat, e) :: rest) = max (evalDepth e) (evalDepthAlts rest) := rfl

@[simp] theorem evalDepth_pure (an : List _root_.annot) (pe : generic_pexpr Unit sym) :
    evalDepth (Expr an (Epure pe)) = peDepth pe := rfl
@[simp] theorem evalDepth_memop (an : List _root_.annot) (mop : memop) (pes : List (generic_pexpr Unit sym)) :
    evalDepth (Expr an (Ememop mop pes)) = pesDepth pes := rfl
@[simp] theorem evalDepth_action (an : List _root_.annot) (pol : polarity) (act : CoreAction) :
    evalDepth (Expr an (Eaction (Paction pol act))) = actDepth act := rfl
@[simp] theorem evalDepth_case (an : List _root_.annot) (pe : generic_pexpr Unit sym)
    (pats : List (pattern × CoreExpr)) :
    evalDepth (Expr an (Ecase pe pats)) = max (peDepth pe) (evalDepthAlts pats) := rfl
@[simp] theorem evalDepth_let (an : List _root_.annot) (pat : pattern) (pe : generic_pexpr Unit sym) (e2 : CoreExpr) :
    evalDepth (Expr an (Elet pat pe e2)) = max (peDepth pe) (evalDepth e2) := rfl
@[simp] theorem evalDepth_if (an : List _root_.annot) (g : generic_pexpr Unit sym) (e2 e3 : CoreExpr) :
    evalDepth (Expr an (Eif g e2 e3)) = max (peDepth g) (max (evalDepth e2) (evalDepth e3)) := rfl
@[simp] theorem evalDepth_ccall (an : List _root_.annot) (ra : core_run_annotation) (pe1 pe2 : generic_pexpr Unit sym)
    (pes : List (generic_pexpr Unit sym)) :
    evalDepth (Expr an (Eccall ra pe1 pe2 pes)) = max (max (peDepth pe1) (peDepth pe2)) (pesDepth pes) := rfl
@[simp] theorem evalDepth_proc (an : List _root_.annot) (ra : core_run_annotation) (nm : generic_name sym)
    (pes : List (generic_pexpr Unit sym)) :
    evalDepth (Expr an (Eproc ra nm pes)) = pesDepth pes := rfl
@[simp] theorem evalDepth_unseq (an : List _root_.annot) (es : List CoreExpr) :
    evalDepth (Expr an (Eunseq es)) = evalDepthList es := rfl
@[simp] theorem evalDepth_wseq (an : List _root_.annot) (pat : pattern) (e1 e2 : CoreExpr) :
    evalDepth (Expr an (Ewseq pat e1 e2)) = max (evalDepth e1) (evalDepth e2) := rfl
@[simp] theorem evalDepth_sseq (an : List _root_.annot) (pat : pattern) (e1 e2 : CoreExpr) :
    evalDepth (Expr an (Esseq pat e1 e2)) = max (evalDepth e1) (evalDepth e2) := rfl
@[simp] theorem evalDepth_bound (an : List _root_.annot) (b : CoreExpr) :
    evalDepth (Expr an (Ebound b)) = evalDepth b := rfl
@[simp] theorem evalDepth_nd (an : List _root_.annot) (es : List CoreExpr) :
    evalDepth (Expr an (End es)) = evalDepthList es := rfl
@[simp] theorem evalDepth_save (an : List _root_.annot) (sb : sym × core_base_type)
    (ps : List (sym × ((core_base_type × Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (body : CoreExpr) :
    evalDepth (Expr an (Esave sb ps body)) = max (pesDepth (saveParamPexprs ps)) (evalDepth body) := rfl
@[simp] theorem evalDepth_run (an : List _root_.annot) (ra : core_run_annotation) (l : sym)
    (pes : List (generic_pexpr Unit sym)) :
    evalDepth (Expr an (Erun ra l pes)) = pesDepth pes := rfl
@[simp] theorem evalDepth_par (an : List _root_.annot) (es : List CoreExpr) :
    evalDepth (Expr an (Epar es)) = evalDepthList es := rfl
@[simp] theorem evalDepth_wait (an : List _root_.annot) (tid : thread_id) :
    evalDepth (Expr an (Ewait tid)) = 0 := rfl
@[simp] theorem evalDepth_annot (an : List _root_.annot) (ds : List dyn_annotation) (b : CoreExpr) :
    evalDepth (Expr an (Eannot ds b)) = evalDepth b := rfl
@[simp] theorem evalDepth_excluded (an : List _root_.annot) (n : Nat) (act : CoreAction) :
    evalDepth (Expr an (Eexcluded n act)) = actDepth act := rfl

theorem peDepth_le_pesDepth_of_mem {pe : generic_pexpr Unit sym} {pes : List (generic_pexpr Unit sym)}
    (h : pe ∈ pes) : peDepth pe ≤ pesDepth pes := by
  induction pes with
  | nil => cases h
  | cons q rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem pesDepth_le_of_forall {pes : List (generic_pexpr Unit sym)} {n : Nat}
    (h : ∀ pe ∈ pes, peDepth pe ≤ n) : pesDepth pes ≤ n := by
  induction pes with
  | nil => exact Nat.zero_le _
  | cons q rest ih =>
    exact Nat.max_le.mpr ⟨h q (List.mem_cons_self ..), ih (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩

theorem evalDepth_le_evalDepthList_of_mem {e : CoreExpr} {es : List CoreExpr} (h : e ∈ es) :
    evalDepth e ≤ evalDepthList es := by
  induction es with
  | nil => cases h
  | cons q rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem evalDepthList_le_of_forall {es : List CoreExpr} {n : Nat}
    (h : ∀ e ∈ es, evalDepth e ≤ n) : evalDepthList es ≤ n := by
  induction es with
  | nil => exact Nat.zero_le _
  | cons q rest ih =>
    exact Nat.max_le.mpr ⟨h q (List.mem_cons_self ..), ih (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩

theorem evalDepth_le_evalDepthAlts_of_mem {q : pattern × CoreExpr} {pats : List (pattern × CoreExpr)}
    (h : q ∈ pats) : evalDepth q.2 ≤ evalDepthAlts pats := by
  induction pats with
  | nil => cases h
  | cons r rest ih =>
    obtain ⟨pr, er⟩ := r
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem evalDepthAlts_le_of_forall {pats : List (pattern × CoreExpr)} {n : Nat}
    (h : ∀ q ∈ pats, evalDepth q.2 ≤ n) : evalDepthAlts pats ≤ n := by
  induction pats with
  | nil => exact Nat.zero_le _
  | cons r rest ih =>
    obtain ⟨pr, er⟩ := r
    exact Nat.max_le.mpr ⟨h (pr, er) (List.mem_cons_self ..),
      ih (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩

/-! ## The depth is stable under the engine's substitution

`subst_sym_pexpr`/`subst_sym_expr` (Core_aux.lean; MEASURED at the pin, so
their wrappers are fuel-free and `Core_aux_lemMeasureProofs.*_measure_sufficient`
connects them to the workers) replace a symbol read by a value: both cost one
pass, every other constructor is kept, so no operand's `peDepth` moves. The
proofs are by the worker's fuel, exactly as `esize_subst_lemFuel` and
`PePure.subst_lemFuel` (which covers the pure grammar only; this one covers
every constructor — the others cost one pass before and after). -/

theorem peDepth_subst_lemFuel (x : sym) (v : value) :
    ∀ (n : Nat) (pe : generic_pexpr Unit sym), peDepth pe ≤ n →
      peDepth (subst_sym_pexpr_lemFuel n x v pe) = peDepth pe := by
  intro n
  induction n with
  | zero => intro pe h; have := peDepth_pos pe; omega
  | succ n ih =>
    intro pe hn
    rcases pe with ⟨a, ⟨⟩, pe_⟩
    cases pe_ with
    | PEsym s =>
      change peDepth (Pexpr a () (if symbolEquality x s then PEval v else PEsym s)) = 1
      split <;> rfl
    | PEop op pe1 pe2 =>
      simp only [peDepth_op] at hn
      simp only [subst_sym_pexpr_lemFuel, peDepth_op, ih pe1 (by omega), ih pe2 (by omega)]
    | PEarray_shift pe1 ty pe2 =>
      simp only [peDepth_array_shift] at hn
      simp only [subst_sym_pexpr_lemFuel, peDepth_array_shift, ih pe1 (by omega), ih pe2 (by omega)]
    | PEctor c pes =>
      simp only [peDepth_ctor] at hn
      change 1 + peDepthList (pes.map _) = 1 + peDepthList pes
      rw [peDepthList_map_eq _ pes (fun q hq => ih q (by have := peDepth_le_list_of_mem hq; omega))]
    | PEcase p pats =>
      simp only [peDepth_case] at hn
      have hs (q : pattern × generic_pexpr Unit sym) (hq : q ∈ pats) :
          peDepth (if in_pattern x q.1 then q.2 else subst_sym_pexpr_lemFuel n x v q.2) = peDepth q.2 := by
        split
        · rfl
        · exact ih q.2 (by have := peDepth_le_alts_of_mem hq; omega)
      change 1 + peDepth (subst_sym_pexpr_lemFuel n x v p) + peDepthAlts (pats.map _) = _
      rw [ih p (by omega), peDepthAlts_map_eq _ pats hs]
      rfl
    | PEnot p =>
      simp only [peDepth_not] at hn
      simp only [subst_sym_pexpr_lemFuel, peDepth_not, ih p (by omega)]
    | PEif p1 p2 p3 =>
      simp only [peDepth_if] at hn
      simp only [subst_sym_pexpr_lemFuel, peDepth_if, ih p1 (by omega), ih p2 (by omega), ih p3 (by omega)]
    | PEconv_int ity p =>
      simp only [peDepth_conv_int] at hn
      simp only [subst_sym_pexpr_lemFuel, peDepth_conv_int, ih p (by omega)]
    | PEwrapI ity op p1 p2 =>
      simp only [peDepth_wrapI] at hn
      simp only [subst_sym_pexpr_lemFuel, peDepth_wrapI, ih p1 (by omega), ih p2 (by omega)]
    | PEcatch_exceptional_condition ity op p1 p2 =>
      simp only [peDepth_catch] at hn
      simp only [subst_sym_pexpr_lemFuel, peDepth_catch, ih p1 (by omega), ih p2 (by omega)]
    | PEis_unsigned p =>
      simp only [peDepth_is_unsigned] at hn
      simp only [subst_sym_pexpr_lemFuel, peDepth_is_unsigned, ih p (by omega)]
    | PEcall nm pes =>
      simp only [peDepth_call] at hn
      change 1 + peDepthList (pes.map _) + stdBudget nm = 1 + peDepthList pes + stdBudget nm
      rw [peDepthList_map_eq _ pes (fun q hq => ih q (by have := peDepth_le_list_of_mem hq; omega))]
    | PEimpl _ => rfl
    | PEval _ => rfl
    | PEconstrained _ => rfl
    | PEundef _ _ => rfl
    | PEerror _ _ => rfl
    | PEmember_shift _ _ _ => rfl
    | PEmemop _ _ => rfl
    | PEstruct _ _ => rfl
    | PEunion _ _ _ => rfl
    | PEcfunction _ => rfl
    | PEmemberof _ _ _ => rfl
    | PElet _ _ _ => rfl
    | PEis_scalar _ => rfl
    | PEis_integer _ => rfl
    | PEis_signed _ => rfl
    | PEbmc_assume _ => rfl
    | PEare_compatible _ _ => rfl

theorem peDepth_subst (x : sym) (v : value) (pe : generic_pexpr Unit sym) :
    peDepth (subst_sym_pexpr x v pe) = peDepth pe := by
  let fuel := max (generic_pexpr.lemSize pe) (peDepth pe)
  rw [← Core_aux_lemMeasureProofs.subst_sym_pexpr_measure_sufficient x v pe fuel (Nat.le_max_left _ _)]
  exact peDepth_subst_lemFuel x v fuel pe (Nat.le_max_right _ _)

theorem pesDepth_map_subst (x : sym) (v : value) (pes : List (generic_pexpr Unit sym)) :
    pesDepth (pes.map (subst_sym_pexpr x v)) = pesDepth pes := by
  induction pes with
  | nil => rfl
  | cons pe rest ih => simp only [List.map_cons, pesDepth_cons, peDepth_subst, ih]

/-- The shadowing test of `SeqRMW`'s update operand: substituted or not, one
    depth. -/
theorem peDepth_ite_subst (c : Prop) [Decidable c] (x : sym) (v : value) (pe : generic_pexpr Unit sym) :
    peDepth (if c then pe else subst_sym_pexpr x v pe) = peDepth pe := by
  split
  · rfl
  · exact peDepth_subst x v pe

theorem actDepth_subst (x : sym) (v : value) (act : CoreAction) :
    actDepth (subst_sym_action x v act) = actDepth act := by
  obtain ⟨loc, a, act_⟩ := act
  cases act_ <;>
    simp only [subst_sym_action, subst_sym_action_, actDepth, peDepth_subst, peDepth_ite_subst]

theorem evalDepthList_map_aux {f : CoreExpr → CoreExpr} (es : List CoreExpr)
    (h : ∀ e ∈ es, evalDepth (f e) = evalDepth e) :
    evalDepthList (es.map f) = evalDepthList es := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons, evalDepthList_cons]
    rw [h e (List.mem_cons_self ..), ih (fun r hr => h r (List.mem_cons_of_mem _ hr))]

theorem evalDepthAlts_map_subst_aux {g : pattern × CoreExpr → CoreExpr}
    (pats : List (pattern × CoreExpr))
    (h : ∀ q ∈ pats, evalDepth (g q) = evalDepth q.2) :
    evalDepthAlts (pats.map (fun q => (q.1, g q))) = evalDepthAlts pats := by
  induction pats with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨pq, eq⟩ := q
    simp only [List.map_cons, evalDepthAlts_cons]
    rw [h (pq, eq) (List.mem_cons_self ..), ih (fun r hr => h r (List.mem_cons_of_mem _ hr))]

theorem pesDepth_saveParams_map
    {g : (sym × ((core_base_type × Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) →
      (sym × ((core_base_type × Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
    (ps : List (sym × ((core_base_type × Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)))
    (h : ∀ p ∈ ps, peDepth (g p).2.2 = peDepth p.2.2) :
    pesDepth (saveParamPexprs (ps.map g)) = pesDepth (saveParamPexprs ps) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, saveParamPexprs, pesDepth_cons] at *
    rw [h p (List.mem_cons_self ..), ih (fun r hr => h r (List.mem_cons_of_mem _ hr))]

theorem evalDepth_subst_lemFuel (x : sym) (v : value) :
    ∀ (n : Nat) (e : CoreExpr), esize e ≤ n →
      evalDepth (subst_sym_expr_lemFuel n x v e) = evalDepth e := by
  intro n
  induction n with
  | zero => intro e h; have := esize_pos e; omega
  | succ n ih =>
    intro e hn
    rcases e with ⟨a, e_⟩
    cases e_ with
    | Epure pe => simp only [subst_sym_expr_lemFuel, evalDepth_pure, peDepth_subst]
    | Ememop mop pes => simp only [subst_sym_expr_lemFuel, evalDepth_memop, pesDepth_map_subst]
    | Eaction pact =>
      obtain ⟨pol, act⟩ := pact
      simp only [subst_sym_expr_lemFuel, subst_sym_paction, evalDepth_action, actDepth_subst]
    | Ecase pe pats =>
      rw [show esize (Expr a (Ecase pe pats)) = 1 + esizeAlts pats from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      have hq' : ∀ q ∈ pats,
          evalDepth (if in_pattern x q.1 then q.2 else subst_sym_expr_lemFuel n x v q.2) = evalDepth q.2 := by
        intro q hq
        have := esize_le_esizeAlts_of_mem hq
        split
        · rfl
        · exact ih q.2 (by omega)
      change max (peDepth (subst_sym_pexpr x v pe)) (evalDepthAlts (List.map _ pats)) = _
      rw [peDepth_subst, evalDepthAlts_map_subst_aux pats hq']
      rfl
    | Elet pat pe e2 =>
      rw [show esize (Expr a (Elet pat pe e2)) = 1 + esize e2 from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      split
      · change max (peDepth (subst_sym_pexpr x v pe)) (evalDepth e2) = _
        rw [peDepth_subst]
        rfl
      · change max (peDepth (subst_sym_pexpr x v pe)) (evalDepth (subst_sym_expr_lemFuel n x v e2)) = _
        rw [peDepth_subst, ih e2 (by omega)]
        rfl
    | Eif g e2 e3 =>
      rw [show esize (Expr a (Eif g e2 e3)) = 1 + max (esize e2) (esize e3) from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      change max (peDepth (subst_sym_pexpr x v g))
        (max (evalDepth (subst_sym_expr_lemFuel n x v e2)) (evalDepth (subst_sym_expr_lemFuel n x v e3))) = _
      rw [peDepth_subst, ih e2 (by omega), ih e3 (by omega)]
      rfl
    | Eccall ra pe1 pe2 pes =>
      simp only [subst_sym_expr_lemFuel, evalDepth_ccall, peDepth_subst, pesDepth_map_subst]
    | Eproc ra nm pes => simp only [subst_sym_expr_lemFuel, evalDepth_proc, pesDepth_map_subst]
    | Eunseq es =>
      rw [esize_unseq] at hn
      simp only [subst_sym_expr_lemFuel, evalDepth_unseq]
      rw [evalDepthList_map_aux es (fun e he => ih e (by have := esize_le_esizeList_of_mem he; omega))]
    | Ewseq pat e1 e2 =>
      rw [esize_wseq] at hn
      simp only [subst_sym_expr_lemFuel, evalDepth_wseq]
      rw [ih e1 (by omega)]
      split
      · rfl
      · rw [ih e2 (by omega)]
    | Esseq pat e1 e2 =>
      rw [esize_sseq] at hn
      simp only [subst_sym_expr_lemFuel, evalDepth_sseq]
      rw [ih e1 (by omega)]
      split
      · rfl
      · rw [ih e2 (by omega)]
    | Ebound b =>
      rw [esize_bound] at hn
      simp only [subst_sym_expr_lemFuel, evalDepth_bound]
      rw [ih b (by omega)]
    | End es =>
      rw [show esize (Expr a (End es)) = 1 + esizeList es from rfl] at hn
      simp only [subst_sym_expr_lemFuel, evalDepth_nd]
      rw [evalDepthList_map_aux es (fun e he => ih e (by have := esize_le_esizeList_of_mem he; omega))]
    | Esave sb ps body =>
      rw [show esize (Expr a (Esave sb ps body)) = 1 + esize body from rfl] at hn
      simp only [subst_sym_expr_lemFuel]
      split
      · change max (pesDepth (saveParamPexprs (ps.map _))) (evalDepth body) = _
        rw [pesDepth_saveParams_map ps]
        · rfl
        · intro p _
          obtain ⟨z, bTy, pe⟩ := p
          exact peDepth_subst x v pe
      · change max (pesDepth (saveParamPexprs (ps.map _))) (evalDepth (subst_sym_expr_lemFuel n x v body)) = _
        rw [pesDepth_saveParams_map ps, ih body (by omega)]
        · rfl
        · intro p _
          obtain ⟨z, bTy, pe⟩ := p
          exact peDepth_subst x v pe
    | Erun ra l pes => simp only [subst_sym_expr_lemFuel, evalDepth_run, pesDepth_map_subst]
    | Epar es =>
      rw [show esize (Expr a (Epar es)) = 1 + esizeList es from rfl] at hn
      simp only [subst_sym_expr_lemFuel, evalDepth_par]
      rw [evalDepthList_map_aux es (fun e he => ih e (by have := esize_le_esizeList_of_mem he; omega))]
    | Ewait _ => rfl
    | Eannot ds b =>
      rw [esize_annot] at hn
      simp only [subst_sym_expr_lemFuel, evalDepth_annot]
      rw [ih b (by omega)]
    | Eexcluded k act => simp only [subst_sym_expr_lemFuel, evalDepth_excluded, actDepth_subst]

theorem evalDepth_subst (x : sym) (v : value) (e : CoreExpr) :
    evalDepth (subst_sym_expr x v e) = evalDepth e :=
  evalDepth_subst_lemFuel x v (generic_expr.lemSize e) e (esize_le_lemSize e)

/-- `select_case`'s fold of substitutions keeps the depth. -/
theorem evalDepth_subst_fold {br : CoreExpr} (binds : List (sym × value)) :
    evalDepth (substFold br binds) = evalDepth br := by
  induction binds with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨s0, cv⟩ := p
    rw [substFold_cons, evalDepth_subst s0 cv, ih]

/-! ## THE FRAGMENT -/

/-- THE FRAGMENT: the terms the mirror `Step` covers, as a syntactic
    predicate — no fuel. Every evaluated operand is in the covered pure
    grammar `PePure`; the evaluator's budget for it is `evalDepth`, a
    hypothesis of the adequacy theorems, never a field here. The
    constructors, their docstrings and their engine cites are those of the
    proof device `FragFuel` (Soundness.lean) minus its `peDepth pe ≤
    LemFuel.fuel` fields and `neg_store`'s positivity; the capability
    manifest (scripts/capability_manifest.lean) classifies every constructor
    of THIS inductive. -/
inductive Frag : CoreExpr → Prop where
  | val_pure {a b : List _root_.annot} (v : value) : Frag (Expr a (Epure (Pexpr b () (PEval v))))
  /-- Store at canonical evaluated operands, at EITHER locking mode:
      `lk` is unconstrained, so the fragment ADMITS the locking store
      `Store0 true …`, whose engine success flips the allocation's
      `isReadonly` (CerbMem.lean:1687-1693). No rule of this package
      covers `lk = true` (`storeExpr` is `Store0 false`; `store_atomic`,
      `wps_store`, `wpt_store` and the subrange rules are stated at it),
      so no derivation traverses a locking store and the coupling is
      never asserted across one; any rule "over any live cell" that
      involves a store fixes `lk = false` (K1 audit N-2). The kill rules
      (K2) involve no store, so `lk` does not arise there. -/
  | store {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {lk : Bool}
      {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order} :
      Frag (storeRedex an loc ann lk ty pv cv mo)
  | load {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {ty : ctype}
      {pv : CerbMem.PointerValue} {mo : memory_order} :
      Frag (loadRedex an loc ann ty pv mo)
  | create {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align : CerbMem.IntegerValue} {ty : ctype} {pref : prefix0} :
      Frag (createRedex an loc ann align ty pref)
  /-- E1: `create` at operands in the covered grammar `PePure` that are
      not all values (the emitted `create(Ivalignof(ty), ty)`), (its evaluator budget is `evalDepth`) — the ACTION_EVAL form (step_action's Create
      `_, _` arm, Core_reduction.lean:424 region). -/
  | create_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2) :
      Frag (createOpRedex an loc ann pe1 pe2 pref)
  /-- THE KILL at the canonical evaluated pointer operand, EITHER KIND
      (kill/free arc K2 static, K3 dynamic): `kill(static ty, p)` — C's
      end of automatic storage — and `free(p)` (`Kill Dynamic0`, the
      pair of `Alloc0`). K2 carried `is_dynamic kind = false` here; K3
      LIFTED it (a strict generalization of the fragment: the mirror
      `Step.kill` was generic in the kind from the start, and
      `complete_kill` classifies every kind). The engine DISCARDS the
      `Static0 ty` payload — only `is_dynamic kind` reaches `killM`
      (Core_reduction.lean:424) — so no relation between the kill type
      and the allocation's type is a premise anywhere. The RULES are
      kind-specific: `kill_atomic` (static, over the OBJECT bundle
      `pointsToCell`) and `free_atomic` (dynamic, over the REGION bundle
      `regionOwn`); the engine-ACCEPTED cross case `kill(static ty, p)`
      at a live REGION (the dynamic check is short-circuited at
      `isDynamic = false`, CerbMem.lean:1573) is in the fragment and
      mirrored, and has NO rule — the K2 range audit's N-2, decided at
      K3 (README "Scope, exactly"). -/
  | kill {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
      {pv : CerbMem.PointerValue} :
      Frag (killRedex an loc ann kind pv)
  /-- The kill of either kind at an operand in the covered grammar
      `PePure`, (its evaluator budget is `evalDepth`) (the ACTION_EVAL form). -/
  | kill_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation} {kind : kill_kind}
      {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) (hp : PePure pe) :
      Frag (killOpRedex an loc ann kind pe)
  /-- DYNAMIC ALLOCATION at canonical evaluated INTEGER operands
      (kill/free arc K3): `alloc(al, n)` — Core's `Alloc0`, C's `malloc`
      (the region is untyped, dynamic and records the raw signed size).
      The memory well-formedness/public allocation contracts require a
      nonnegative size; membership alone does not establish that domain. -/
  | alloc {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {align size : CerbMem.IntegerValue} {pref : prefix0} :
      Frag (allocRedex an loc ann align size pref)
  /-- Dynamic allocation at operands in the covered grammar `PePure`
      that are not all values, (its evaluator budget is `evalDepth`) (the
      ACTION_EVAL form; mixed shapes included, as `store_op`). -/
  | alloc_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {pe1 pe2 : generic_pexpr Unit sym} {pref : prefix0}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2) :
      Frag (allocOpRedex an loc ann pe1 pe2 pref)
  | sseq {an pa : List _root_.annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (Pattern pa (CaseBase (none, bty))) e1 e2))
  | annot {an : List _root_.annot} {ds : List dyn_annotation} {b : CoreExpr} :
      Frag b → Frag (Expr an (Eannot ds b))
  /-- E1: `bound(e)` — the emitted wrapper around every full-expression
      statement (`Ebound`; get_ctx's Ebound arm / `Cbound` frame,
      REMOVE-BOUND at a value, core_reduction.lem:563–568, 1214–1226). -/
  | bound {an : List _root_.annot} {b : CoreExpr} :
      Frag b → Frag (Expr an (Ebound b))
  /-- Esave at ANY initializers (its evaluator budget is `evalDepth`) (the
      engine's TAU arm at value initializers, its EVAL arm otherwise —
      `Step.save`/`Step.save_eval`). `hd` is the same static
      evaluator-fuel bound `if_`/`run` carry for their pure operands;
      literal initializers satisfy it trivially
      (`saveParams_depth_of_vals`). -/
  | save {an : List _root_.annot} {sb : sym × core_base_type}
      {ps : List (sym × ((core_base_type ×
        Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym))}
      {body : CoreExpr}
      (hp : ∀ pe ∈ saveParamPexprs ps, PePure pe) :
      Frag body → Frag (saveRedex an sb ps body)
  /-- Eif at a guard in the covered operand grammar `PePure`, (its evaluator budget is `evalDepth`) (fragment closure, 2026-09-02: the operand grammar
      of every evaluating constructor is `PePure` — the mirror evaluator's
      exact domain — so an operand the mirror cannot evaluate is
      classified in the engine, `complete_if`). -/
  | if_ {an : List _root_.annot} {g : generic_pexpr Unit sym} {e2 e3 : CoreExpr}
      (hpg : PePure g) :
      Frag e2 → Frag e3 → Frag (ifRedex an g e2 e3)
  /-- Erun at arguments in `PePure`, (its evaluator budget is `evalDepth`). -/
  | run {an : List _root_.annot} {ra : core_run_annotation} {l : sym}
      {pes : List (generic_pexpr Unit sym)}
      (hpes : ∀ pe ∈ pes, PePure pe) :
      Frag (runRedex an ra l pes)
  | sseq_spec {an pa pb : List _root_.annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (specPat pa pb x bty) e1 e2))
  /-- E2: `pure(e)` at ANY operand in the covered grammar `PePure` that
      is not a value, (its evaluator budget is `evalDepth`) (one_step0's Epure EVAL
      arm; `Step.pure_eval`). Subsumes E1's plain-symbol row
      (`Frag.pure_sym`, now a theorem). -/
  | pure_op {an : List _root_.annot} {pe : generic_pexpr Unit sym}
      (hnv : valueFromPexpr pe = none) (hp : PePure pe) :
      Frag (pureRedex an pe)
  /-- E2: strong sequencing at a flat TUPLE binder, any fragment head
      (`Step.sseq_tuple_*`; a non-tuple head is the binding PANIC,
      `complete_beta_tuple`). -/
  | sseq_tuple {an pa : List _root_.annot} {ls : List TupleLeaf} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (tuplePat pa ls) e1 e2))
  /-- E2: weak sequencing at a flat tuple binder — the corpus's `let weak
      (a, b) = …` (`Step.wseq_tuple_*`). -/
  | wseq_tuple {an pa : List _root_.annot} {ls : List TupleLeaf} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Ewseq (tuplePat pa ls) e1 e2))
  /-- E2: weak sequencing at the plain-symbol binder — the corpus's `let
      weak p = pure(y) in load(…)` (`Step.wseq_sym_*`). -/
  | wseq_sym {an pa : List _root_.annot} {x : sym} {bty : core_base_type} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Ewseq (symPat pa x bty) e1 e2))
  | load_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 : generic_pexpr Unit sym} {mo : memory_order}
      (hnv2 : valueFromPexpr pe2 = none) (hp2 : PePure pe2) :
      Frag (loadOpRedex an loc ann ty pe2 mo)
  /-- Strong sequencing at the plain-symbol binder, ANY fragment head
      (E1: both LETS betas at this binder are mirrored —
      `Step.sseq_sym_pure`, `Step.sseq_sym_annot`). -/
  | sseq_sym {an pa : List _root_.annot} {x : sym} {bty : core_base_type}
      {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Esseq (symPat pa x bty) e1 e2))
  | memop_vals {an : List _root_.annot} (v1 v2 : value) :
      Frag (memopPtrEqVals an v1 v2)
  | memop_op {an : List _root_.annot} {pe1 pe2 : generic_pexpr Unit sym}
      (hnv : valueFromPexprs [pe1, pe2] = none)
      (hp1 : PePure pe1) (hp2 : PePure pe2) :
      Frag (memopRedex an PtrEq [pe1, pe2])
  | store_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hp2 : PePure pe2) (hp3 : PePure pe3) :
      Frag (storeOpRedex an loc ann ty pe2 pe3 mo)
  /-- Value-scrutinee Ecase, retaining all branches and the selected
      branch's fragment membership. The size premise is supplied by
      case_hbsz_of_branches without an ambient-fuel condition; it remains
      explicit here for the downstream size-accounting interface. -/
  | case_value {an b : List _root_.annot} {cval : value}
      {pats : List (pattern × CoreExpr)}
      (hall : ∀ q ∈ pats, Frag q.2)
      (hbr : ∀ e', select_case subst_sym_expr cval pats = some e' → Frag e')
      (hbsz : ∀ e', select_case subst_sym_expr cval pats = some e' →
        esize e' ≤ esize (caseRedex an (Pexpr b () (PEval cval)) pats)) :
      Frag (caseRedex an (Pexpr b () (PEval cval)) pats)
  /-- Weak sequencing at the wildcard pattern (the `sseq` clone). -/
  | wseq {an pa : List _root_.annot} {bty : core_base_type} {e1 e2 : CoreExpr} :
      Frag e1 → Frag e2 →
      Frag (Expr an (Ewseq (Pattern pa (CaseBase (none, bty))) e1 e2))
  /-- THE PROCEDURE CALL (calls arc C2): `Eproc` at a Core identifier,
      arguments in the covered grammar `PePure` within the evaluator's
      fuel (the engine evaluates ALL of them by `full_eval_pexpr'` in the
      PCALL round, Core_reduction.lean:484 col 18133). Any `f`: the
      unknown procedure and the arity mismatch are the engine's two
      `Illformed_program` KILLS, classified in Round.lean (`complete_call`),
      not narrowed here. The callee's BODY is not a `Frag` premise — `Frag`
      is a predicate on the expression, the body lives in the FILE — so
      adequacy through a call carries `MachineCtx.FragProcs` (Adequacy.lean:
      every procedure the file declares has a `Frag` body within the
      potential bound and `Frag` label bodies), the twin of `hQf`/`hQpot`. -/
  | call {an : List _root_.annot} {ra : core_run_annotation} {f : sym} {pes : List (generic_pexpr Unit sym)}
      (hpes : ∀ pe ∈ pes, PePure pe) :
      Frag (callRedex an ra f pes)
  /-- E4: `unseq(e_1, …, e_n)` at fragment components, at least one,
      every component `ccallFree` (no `Eccall`, no expression-level
      `case` — the sibling condition that keeps `is_unseq_with_ccall`
      false so every request under the frame is advanceable,
      docs/2026-09-05_e4-notes.md §1). The sequential driver reduces the
      LAST reducible component first (`Step.unseq_ctx`) and completes the
      node into the annotated tuple `{A_1 ++ … ++ A_n}(v_1, …, v_n)`
      (`Step.unseq_vals`); a race between the components' dynamic
      annotations is the engine's UB035 kill (`complete_unseq_vals`). -/
  | unseq {an : List _root_.annot} {es : List CoreExpr}
      (hne : es ≠ []) (hcc : ccallFreeList es = true) :
      (∀ e ∈ es, Frag e) → Frag (Expr an (Eunseq es))
  /-- E5: the emitted NEGATIVE store `neg(store(ty, p, v))` at operands in
      the covered grammar not all values (every assignment statement,
      E0 §B.9: `let weak _: unit = neg(store(ty, p, conv_loaded_int(ty, v)))`).
      The engine rewrites it at the enclosing `bound` (`Step.neg_bound`,
      core_reduction.lem:1290–1309); without a `bound` in its context the
      round is the engine's `error "TODO: NO_BOUND (Neg)"` panic
      (classified, Round.lean `complete_neg_act`). -/
  | neg_store_op {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym} {mo : memory_order}
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hp2 : PePure pe2) (hp3 : PePure pe3) :
      Frag (negStoreRedex an loc ann false ty pe2 pe3 mo)
  /-- The negative store at canonical evaluated operands. Its rewrite
      introduces a symbol-read expression (one evaluator pass: the device's
      `FragFuel.neg_store` carries `0 < LemFuel.fuel`; here `evalDepth` of
      the redex is 1, which `Frag.toFuel` turns into that positivity). -/
  | neg_store {an : List _root_.annot} {loc : CerbLocation.Loc} {ann : core_run_annotation}
      {lk : Bool} {ty : ctype} {pv : CerbMem.PointerValue} {cv : value} {mo : memory_order} :
      Frag (negActRedex an (Action loc ann
        (Store0 lk (Pexpr [] () (PEval (Vctype ty)))
                   (Pexpr [] () (PEval (Vobject (OVpointer pv))))
                   (Pexpr [] () (PEval cv)) mo)))
  /-- E5: the EXCLUDED store at canonical evaluated operands — the negative
      action's performance node after the rewrite (`Eexcluded n act`;
      `Step.excluded_store`). -/
  | excluded_store {an : List _root_.annot} {n : Nat} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {lk : Bool} {ty : ctype} {pv : CerbMem.PointerValue}
      {cv : value} {mo : memory_order} :
      Frag (excludedStoreRedex an n loc ann lk ty pv cv mo)
  /-- E5: the excluded store at operands in `PePure` not all values (the
      ACTION_EVAL form under `process_action (Just n)`; `Step.excluded_store_eval`). -/
  | excluded_store_op {an : List _root_.annot} {n : Nat} {loc : CerbLocation.Loc}
      {ann : core_run_annotation} {ty : ctype} {pe2 pe3 : generic_pexpr Unit sym}
      {mo : memory_order}
      (hnv : valueFromPexprs [pe2, pe3] = none)
      (hp2 : PePure pe2) (hp3 : PePure pe3) :
      Frag (excludedStoreOpRedex an n loc ann ty pe2 pe3 mo)
  /-- E5: expression-level `case` at a covered NON-value scrutinee (the
      corpus's `case a_510 of …`, `case (a_518, a_519) of …`): the EVAL
      "Ecase" round (`Step.case_eval`, core_reduction.lem:323–339) delivers
      the value-scrutinee node, so the branch premises are carried for
      EVERY value the scrutinee may take (`hbr`/`hbsz`, `Frag.case_value`'s
      pair quantified over `cval`; `Frag.case_op_hbsz` derives `hbsz` from
      the branches' sizes) and every branch body is in the fragment
      (`hall`, as at `case_value`). -/
  | case_op {an : List _root_.annot} {pe : generic_pexpr Unit sym}
      {pats : List (pattern × CoreExpr)}
      (hnv : valueFromPexpr pe = none) (hp : PePure pe)
      (hall : ∀ q ∈ pats, Frag q.2)
      (hbr : ∀ cval e', select_case subst_sym_expr cval pats = some e' → Frag e')
      (hbsz : ∀ cval e', select_case subst_sym_expr cval pats = some e' →
        esize e' ≤ esize (caseRedex an pe pats)) :
      Frag (caseRedex an pe pats)
  /-- E5: `nd(e_1, …, e_n)` at fragment alternatives, at least two — the
      elaborator's `Unspecified` alternative of every condition
      (`nd(pure(True), pure(False))`, translation.lem:3823/:3858). The
      engine's round is the scheduler FORK (`Step_nd2` → `ND.pick`),
      classified `ShippedRefusal.fork` (`complete_nd`); no rule. -/
  | nd {an : List _root_.annot} {es : List CoreExpr}
      (h2 : 2 ≤ es.length) (hall : ∀ e ∈ es, Frag e) : Frag (ndRedex an es)

/-! ## The bridge to the proof device -/

/-- A fragment term at an ambient at least its evaluator depth is a term of
    the proof device: every operand bound the device's fields ask for is
    `peDepth pe ≤ evalDepth e ≤ LemFuel.fuel`, and a selected `case` branch
    is no deeper than the alternatives (`evalDepth_subst_fold`). -/
theorem Frag.toFuel [LemFuel] {e : CoreExpr} (hf : Frag e) (hd : evalDepth e ≤ LemFuel.fuel) :
    FragFuel e := by
  induction hf with
  | val_pure v => exact .val_pure v
  | store => exact .store
  | load => exact .load
  | create => exact .create
  | create_op hnv hp1 hp2 =>
    simp only [createOpRedex, evalDepth_action, actDepth] at hd
    exact .create_op hnv hp1 hp2 (by omega) (by omega)
  | kill => exact .kill
  | kill_op hnv hp =>
    simp only [killOpRedex, evalDepth_action, actDepth] at hd
    exact .kill_op hnv hp hd
  | alloc => exact .alloc
  | alloc_op hnv hp1 hp2 =>
    simp only [allocOpRedex, evalDepth_action, actDepth] at hd
    exact .alloc_op hnv hp1 hp2 (by omega) (by omega)
  | sseq _ _ ih1 ih2 =>
    simp only [evalDepth_sseq] at hd
    exact .sseq (ih1 (by omega)) (ih2 (by omega))
  | annot _ ih => exact .annot (ih (by simpa only [evalDepth_annot] using hd))
  | bound _ ih => exact .bound (ih (by simpa only [evalDepth_bound] using hd))
  | save hp _ ih =>
    simp only [saveRedex, evalDepth_save] at hd
    exact .save hp (fun pe hpe => Nat.le_trans (peDepth_le_pesDepth_of_mem hpe) (by omega)) (ih (by omega))
  | if_ hpg _ _ ih2 ih3 =>
    simp only [ifRedex, evalDepth_if] at hd
    exact .if_ hpg (by omega) (ih2 (by omega)) (ih3 (by omega))
  | run hpes =>
    simp only [runRedex, evalDepth_run] at hd
    exact .run hpes (fun pe hpe => Nat.le_trans (peDepth_le_pesDepth_of_mem hpe) hd)
  | sseq_spec _ _ ih1 ih2 =>
    simp only [evalDepth_sseq] at hd
    exact .sseq_spec (ih1 (by omega)) (ih2 (by omega))
  | pure_op hnv hp =>
    simp only [pureRedex, evalDepth_pure] at hd
    exact .pure_op hnv hp hd
  | sseq_tuple _ _ ih1 ih2 =>
    simp only [evalDepth_sseq] at hd
    exact .sseq_tuple (ih1 (by omega)) (ih2 (by omega))
  | wseq_tuple _ _ ih1 ih2 =>
    simp only [evalDepth_wseq] at hd
    exact .wseq_tuple (ih1 (by omega)) (ih2 (by omega))
  | wseq_sym _ _ ih1 ih2 =>
    simp only [evalDepth_wseq] at hd
    exact .wseq_sym (ih1 (by omega)) (ih2 (by omega))
  | load_op hnv2 hp2 =>
    simp only [loadOpRedex, evalDepth_action, actDepth, peDepth_val] at hd
    exact .load_op hnv2 hp2 (by omega)
  | sseq_sym _ _ ih1 ih2 =>
    simp only [evalDepth_sseq] at hd
    exact .sseq_sym (ih1 (by omega)) (ih2 (by omega))
  | memop_vals v1 v2 => exact .memop_vals v1 v2
  | memop_op hnv hp1 hp2 =>
    simp only [memopRedex, evalDepth_memop, pesDepth_cons, pesDepth_nil] at hd
    exact .memop_op hnv hp1 hp2 (by omega) (by omega)
  | store_op hnv hp2 hp3 =>
    simp only [storeOpRedex, evalDepth_action, actDepth, peDepth_val] at hd
    exact .store_op hnv hp2 hp3 (by omega) (by omega)
  | case_value hall hbr hbsz ihall ihbr =>
    simp only [caseRedex, evalDepth_case, peDepth_val] at hd
    refine .case_value (fun q hq => ihall q hq ?_) (fun e' hsel => ihbr e' hsel ?_) hbsz
    · have := evalDepth_le_evalDepthAlts_of_mem hq
      omega
    · obtain ⟨pat, br, binds, hmem, -, rfl⟩ := select_case_some hsel
      rw [evalDepth_subst_fold]
      have := evalDepth_le_evalDepthAlts_of_mem hmem
      simp only at this
      omega
  | wseq _ _ ih1 ih2 =>
    simp only [evalDepth_wseq] at hd
    exact .wseq (ih1 (by omega)) (ih2 (by omega))
  | call hpes =>
    simp only [callRedex, evalDepth_proc] at hd
    exact .call hpes (fun pe hpe => Nat.le_trans (peDepth_le_pesDepth_of_mem hpe) hd)
  | unseq hne hcc _ ih =>
    simp only [evalDepth_unseq] at hd
    exact .unseq hne hcc (fun e he => ih e he (Nat.le_trans (evalDepth_le_evalDepthList_of_mem he) hd))
  | neg_store_op hnv hp2 hp3 =>
    simp only [negStoreRedex, negActRedex, evalDepth_action, actDepth, peDepth_val] at hd
    exact .neg_store_op hnv hp2 hp3 (by omega) (by omega)
  | neg_store =>
    simp only [negActRedex, evalDepth_action, actDepth, peDepth_val] at hd
    exact .neg_store (by omega)
  | excluded_store => exact .excluded_store
  | excluded_store_op hnv hp2 hp3 =>
    simp only [excludedStoreOpRedex, evalDepth_excluded, actDepth, peDepth_val] at hd
    exact .excluded_store_op hnv hp2 hp3 (by omega) (by omega)
  | case_op hnv hp hall hbr hbsz ihall ihbr =>
    simp only [caseRedex, evalDepth_case] at hd
    refine .case_op hnv hp (by omega) (fun q hq => ihall q hq ?_) (fun cval e' hsel => ihbr cval e' hsel ?_) hbsz
    · have := evalDepth_le_evalDepthAlts_of_mem hq
      omega
    · obtain ⟨pat, br, binds, hmem, -, rfl⟩ := select_case_some hsel
      rw [evalDepth_subst_fold]
      have := evalDepth_le_evalDepthAlts_of_mem hmem
      simp only at this
      omega
  | nd h2 _ ih =>
    simp only [ndRedex, evalDepth_nd] at hd
    exact .nd h2 (fun e he => ih e he (Nat.le_trans (evalDepth_le_evalDepthList_of_mem he) hd))

/-- The device's terms are fragment terms (drop the fields). -/
theorem FragFuel.toFrag [LemFuel] {e : CoreExpr} (hf : FragFuel e) : Frag e := by
  induction hf with
  | val_pure v => exact .val_pure v
  | store => exact .store
  | load => exact .load
  | create => exact .create
  | create_op hnv hp1 hp2 _ _ => exact .create_op hnv hp1 hp2
  | kill => exact .kill
  | kill_op hnv hp _ => exact .kill_op hnv hp
  | alloc => exact .alloc
  | alloc_op hnv hp1 hp2 _ _ => exact .alloc_op hnv hp1 hp2
  | sseq _ _ ih1 ih2 => exact .sseq ih1 ih2
  | annot _ ih => exact .annot ih
  | bound _ ih => exact .bound ih
  | save hp _ _ ih => exact .save hp ih
  | if_ hpg _ _ _ ih2 ih3 => exact .if_ hpg ih2 ih3
  | run hpes _ => exact .run hpes
  | sseq_spec _ _ ih1 ih2 => exact .sseq_spec ih1 ih2
  | pure_op hnv hp _ => exact .pure_op hnv hp
  | sseq_tuple _ _ ih1 ih2 => exact .sseq_tuple ih1 ih2
  | wseq_tuple _ _ ih1 ih2 => exact .wseq_tuple ih1 ih2
  | wseq_sym _ _ ih1 ih2 => exact .wseq_sym ih1 ih2
  | load_op hnv2 hp2 _ => exact .load_op hnv2 hp2
  | sseq_sym _ _ ih1 ih2 => exact .sseq_sym ih1 ih2
  | memop_vals v1 v2 => exact .memop_vals v1 v2
  | memop_op hnv hp1 hp2 _ _ => exact .memop_op hnv hp1 hp2
  | store_op hnv hp2 hp3 _ _ => exact .store_op hnv hp2 hp3
  | case_value _ _ hbsz ihall ihbr => exact .case_value ihall ihbr hbsz
  | wseq _ _ ih1 ih2 => exact .wseq ih1 ih2
  | call hpes _ => exact .call hpes
  | unseq hne hcc _ ih => exact .unseq hne hcc ih
  | neg_store_op hnv hp2 hp3 _ _ => exact .neg_store_op hnv hp2 hp3
  | neg_store _ => exact .neg_store
  | excluded_store => exact .excluded_store
  | excluded_store_op hnv hp2 hp3 _ _ => exact .excluded_store_op hnv hp2 hp3
  | case_op hnv hp _ _ _ hbsz ihall ihbr => exact .case_op hnv hp ihall ihbr hbsz
  | nd h2 _ ih => exact .nd h2 ih

/-- At a positive ambient the device's terms are within depth: the fields
    bound every non-value operand, values cost one pass. -/
theorem FragFuel.evalDepth_le [LemFuel] (hpos : 1 ≤ LemFuel.fuel) {e : CoreExpr} (hf : FragFuel e) :
    evalDepth e ≤ LemFuel.fuel := by
  induction hf with
  | val_pure v => simpa only [evalDepth_pure, peDepth_val] using hpos
  | store => simp only [storeRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | load => simp only [loadRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | create => simp only [createRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | create_op _ _ _ hd1 hd2 => simp only [createOpRedex, evalDepth_action, actDepth]; omega
  | kill => simp only [killRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | kill_op _ _ hd => simpa only [killOpRedex, evalDepth_action, actDepth] using hd
  | alloc => simp only [allocRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | alloc_op _ _ _ hd1 hd2 => simp only [allocOpRedex, evalDepth_action, actDepth]; omega
  | sseq _ _ ih1 ih2 => simp only [evalDepth_sseq]; omega
  | annot _ ih => simpa only [evalDepth_annot] using ih
  | bound _ ih => simpa only [evalDepth_bound] using ih
  | save _ hd _ ih =>
    simp only [saveRedex, evalDepth_save]
    exact Nat.max_le.mpr ⟨pesDepth_le_of_forall hd, ih⟩
  | if_ _ hdg _ _ ih2 ih3 => simp only [ifRedex, evalDepth_if]; omega
  | run _ hdep => simp only [runRedex, evalDepth_run]; exact pesDepth_le_of_forall hdep
  | sseq_spec _ _ ih1 ih2 => simp only [evalDepth_sseq]; omega
  | pure_op _ _ hd => simpa only [pureRedex, evalDepth_pure] using hd
  | sseq_tuple _ _ ih1 ih2 => simp only [evalDepth_sseq]; omega
  | wseq_tuple _ _ ih1 ih2 => simp only [evalDepth_wseq]; omega
  | wseq_sym _ _ ih1 ih2 => simp only [evalDepth_wseq]; omega
  | load_op _ _ hd2 => simp only [loadOpRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | sseq_sym _ _ ih1 ih2 => simp only [evalDepth_sseq]; omega
  | memop_vals _ _ =>
    simp only [memopPtrEqVals, memopRedex, evalDepth_memop, pesDepth_cons, pesDepth_nil, peDepth_val]
    omega
  | memop_op _ _ _ hd1 hd2 =>
    simp only [memopRedex, evalDepth_memop, pesDepth_cons, pesDepth_nil]
    omega
  | store_op _ _ _ hd2 hd3 => simp only [storeOpRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | case_value _ _ _ ihall _ =>
    simp only [caseRedex, evalDepth_case, peDepth_val]
    exact Nat.max_le.mpr ⟨hpos, evalDepthAlts_le_of_forall ihall⟩
  | wseq _ _ ih1 ih2 => simp only [evalDepth_wseq]; omega
  | call _ hdep => simp only [callRedex, evalDepth_proc]; exact pesDepth_le_of_forall hdep
  | unseq _ _ _ ih => simp only [evalDepth_unseq]; exact evalDepthList_le_of_forall ih
  | neg_store_op _ _ _ hd2 hd3 =>
    simp only [negStoreRedex, negActRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | neg_store _ => simp only [negActRedex, evalDepth_action, actDepth, peDepth_val]; omega
  | excluded_store => simp only [excludedStoreRedex, evalDepth_excluded, actDepth, peDepth_val]; omega
  | excluded_store_op _ _ _ hd2 hd3 =>
    simp only [excludedStoreOpRedex, evalDepth_excluded, actDepth, peDepth_val]; omega
  | case_op _ _ hd _ _ _ ihall _ =>
    simp only [caseRedex, evalDepth_case]
    exact Nat.max_le.mpr ⟨hd, evalDepthAlts_le_of_forall ihall⟩
  | nd _ _ ih => simp only [ndRedex, evalDepth_nd]; exact evalDepthList_le_of_forall ih

/-- THE CHARACTERIZATION OF THE DEVICE: at any positive ambient, `FragFuel`
    is exactly the syntactic fragment within depth. -/
theorem fragFuel_iff [LemFuel] (hpos : 1 ≤ LemFuel.fuel) (e : CoreExpr) :
    FragFuel e ↔ Frag e ∧ evalDepth e ≤ LemFuel.fuel :=
  ⟨fun h => ⟨h.toFrag, h.evalDepth_le hpos⟩, fun h => h.1.toFuel h.2⟩

/-! ## The fragment's structural lemmas (the device's, transported at the
term's own depth) -/

theorem frag_ofValA (w : SpikeValA) : Frag (ofValA w) := by
  cases w with
  | pure a b v => exact .val_pure v
  | annot a a2 b ds v => exact .annot (.val_pure v)

theorem frag_ofVal (w : SpikeVal) : Frag (ofVal w) := frag_ofValA w.canon

theorem Frag.pure_sym {an pb : List _root_.annot} {x : sym} :
    Frag (pureRedex an (Pexpr pb () (PEsym x))) :=
  .pure_op rfl (.sym pb x)

theorem Frag.sseq_inv_any {an : List _root_.annot} {pat : pattern} {e1 e2 : CoreExpr}
    (hf : Frag (Expr an (Esseq pat e1 e2))) : Frag e1 ∧ Frag e2 := by
  cases hf <;> exact ⟨‹_›, ‹_›⟩

theorem Frag.wseq_inv_any {an : List _root_.annot} {pat : pattern} {e1 e2 : CoreExpr}
    (hf : Frag (Expr an (Ewseq pat e1 e2))) : Frag e1 ∧ Frag e2 := by
  cases hf <;> exact ⟨‹_›, ‹_›⟩

theorem Frag.annot_inv {an : List _root_.annot} {ds : List dyn_annotation} {b : CoreExpr}
    (hf : Frag (Expr an (Eannot ds b))) : Frag b := by
  cases hf; assumption

theorem Frag.bound_inv {an : List _root_.annot} {b : CoreExpr}
    (hf : Frag (Expr an (Ebound b))) : Frag b := by
  cases hf; assumption

theorem Frag.unseq_inv {an : List _root_.annot} {es : List CoreExpr}
    (hf : Frag (Expr an (Eunseq es))) : es ≠ [] ∧ ccallFreeList es = true ∧ ∀ e ∈ es, Frag e := by
  cases hf; exact ⟨‹_›, ‹_›, ‹_›⟩

theorem Frag.ccallFree {e : CoreExpr} (hf : Frag e) : ccallFree e = true := by
  letI : LemFuel := ⟨evalDepth e⟩
  exact (hf.toFuel (Nat.le_refl _)).ccallFree

theorem Frag.decomp {e : CoreExpr} (hf : Frag e) (hnv : toVal e = none) :
    ∃ ctx r, Decomp e ctx r ∧ Frag r := by
  letI : LemFuel := ⟨evalDepth e⟩
  obtain ⟨ctx, r, hd, hfr⟩ := (hf.toFuel (Nat.le_refl _)).decomp hnv
  exact ⟨ctx, r, hd, hfr.toFrag⟩

theorem Frag.replug {e : CoreExpr} {ctx : context} {r : CoreExpr}
    (hd : Decomp e ctx r) (hf : Frag e) (n : Nat) {z : CoreExpr} (hz : Frag z) :
    Frag (apply_ctx (add_exclusion n ctx) z) := by
  letI : LemFuel := ⟨max (evalDepth e) (evalDepth z)⟩
  exact (FragFuel.replug hd (hf.toFuel (Nat.le_max_left _ _)) n (hz.toFuel (Nat.le_max_right _ _))).toFrag

theorem Frag.of_negRedex {b : CoreExpr} {ctxA : context} {a : List _root_.annot} {act : CoreAction}
    (hf : Frag b) (hn : negRedex? b = some (ctxA, a, act)) :
    Decomp b ctxA (negActRedex a act) ∧ Frag (negActRedex a act) := by
  letI : LemFuel := ⟨evalDepth b⟩
  obtain ⟨hd, hfr⟩ := (hf.toFuel (Nat.le_refl _)).of_negRedex hn
  exact ⟨hd, hfr.toFrag⟩

theorem Frag.excluded_of_neg {an : List _root_.annot} {act : CoreAction}
    (hf : Frag (negActRedex an act)) (n : Nat) : Frag (Expr [] (Eexcluded n act)) := by
  cases hf with
  | neg_store_op hnv hp2 hp3 => exact .excluded_store_op hnv hp2 hp3
  | neg_store => exact .excluded_store

theorem Frag.negRewrite_frag {b : CoreExpr} {ctxA : context} {a : List _root_.annot}
    {act : CoreAction} (hf : Frag b) (hn : negRedex? b = some (ctxA, a, act)) (n : Nat) (s0 : sym) :
    Frag (negRewrite n s0 ctxA act) := by
  letI : LemFuel := ⟨evalDepth b + 1⟩
  exact (FragFuel.negRewrite_frag (hf.toFuel (Nat.le_succ _)) hn n s0).toFrag

/-- A covered pure operand is a fragment expression whether it is already a
    value or still needs the evaluator (no depth premise: the fragment is
    syntactic; the depth is the adequacy hypothesis). -/
theorem Frag.of_pePure {pe : generic_pexpr Unit sym} (an : List _root_.annot)
    (hp : PePure pe) : Frag (Expr an (Epure pe)) := by
  cases hv : valueFromPexpr pe with
  | none => exact .pure_op hv hp
  | some v =>
    obtain ⟨pb, rfl⟩ := valueFromPexpr_some_iff.mp hv
    exact .val_pure v

theorem Frag.substFold_pure (binds : List (sym × value)) (an : List _root_.annot)
    (pe : generic_pexpr Unit sym) (hp : PePure pe) :
    Frag (substFold (Expr an (Epure pe)) binds) := by
  obtain ⟨p, he, hp', -⟩ := CerberusHeapLang.substFold_pure binds an pe hp
  rw [he]
  exact .of_pePure an hp'

end CerberusHeapLang
