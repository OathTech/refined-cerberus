/-
Fragment witnesses for the E5 emitted corpus, separate from the program
proofs. Membership includes every syntactic branch, including alternatives
the certified run will not take. Substitution.lean handles selected pure
branches for every possible scrutinee value. The witnesses are fuel-free
(the fragment is syntactic since the L2 re-pin, R2): the operand-pass budget
a certified run needs is the measure `evalDepth`, discharged at the
production theorems. These membership facts do not certify production
execution or minimal budgets.
-/
import CerberusHeapLang.Examples.CorpusE0
import CerberusHeapLang.Substitution

set_option autoImplicit false
namespace CerberusHeapLang.CorpusE0

theorem t5Load_frag (x : sym) (n c1 c2 : Nat) : Frag (t5Load x n c1 c2) :=
  .wseq_sym (Frag.of_pePure _ (.sym _ _))
    (.load_op rfl (.sym [] _))

theorem t5Gt_frag : Frag t5Gt := by
  refine .wseq_tuple (ls := [([], some (t5a 518), lint), ([], some (t5a 519), lint)]) ?_ ?_
  · refine .unseq (by simp) rfl ?_
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (t5Load_frag) xSym 517 39 40
    · obtain rfl := List.mem_singleton.mp he
      exact Frag.of_pePure _ (specInt_pePure 2)
  · refine .case_op rfl (PePure.of_isPePure rfl) ?_ ?_ ?_
    · intro q hq
      simp only [t5GtPats, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        exact Frag.of_pePure _ (PePure.of_isPePure rfl)
    · intro v e' hsel
      obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
      simp only [t5GtPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl)
    · exact case_hbsz_of_branches

theorem t5Cond_frag : Frag t5Cond := by
  refine .bound (.wseq_tuple
    (ls := [([], some (t5a 512), lint), ([], some (t5a 513), lint)]) ?_ ?_)
  · refine .unseq (by simp) rfl ?_
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (t5Gt_frag)
    · obtain rfl := List.mem_singleton.mp he
      exact Frag.of_pePure _ (specInt_pePure 0)
  · exact Frag.of_pePure _ (PePure.of_isPePure rfl)

theorem t5Bool_frag : Frag t5Bool := by
  refine .case_op rfl (PePure.of_isPePure rfl) ?_ ?_ ?_
  · intro q hq
    simp only [t5BoolPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)
    · refine .nd (by decide) ?_
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .val_pure _
  · intro v e' hsel
    obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
    simp only [t5BoolPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl)
    · have he (bs : List (sym × value)) : substFold (Expr [] (End [t5Pure (Pexpr [] () (PEval Vtrue)),
          t5Pure (Pexpr [] () (PEval Vfalse))])) bs =
          Expr [] (End [t5Pure (Pexpr [] () (PEval Vtrue)),
            t5Pure (Pexpr [] () (PEval Vfalse))]) := by
        induction bs with
        | nil => rfl
        | cons pair rest ih =>
          rcases pair with ⟨s, v⟩
          rw [substFold_cons, ih]
          rfl
      rw [he binds]
      refine .nd (by decide) ?_
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .val_pure _
  · exact case_hbsz_of_branches

theorem t5AssignBlock_frag (start n m : Nat) (v : Int) : Frag (t5AssignBlock start n m v) := by
  refine .sseq (.sseq (.bound (.wseq_tuple
    (ls := [([], some (t5a n), ptrTy), ([], some (t5a m), lint)]) ?_ ?_)) (.val_pure _)) (.val_pure _)
  · refine .unseq (by simp) rfl ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Frag.of_pePure _ (.sym _ _)
    · exact Frag.of_pePure _ (specInt_pePure v)
  · refine .wseq ?_ ?_
    · exact .neg_store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)

theorem t5Main_frag : Frag t5Main := by
  refine .sseq_sym ?_ ?_
  · exact .create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
  refine .sseq_sym ?_ ?_
  · exact .create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
  refine .sseq_sym ?_ ?_
  · exact .bound (Frag.of_pePure _ (specInt_pePure 3))
  refine .sseq ?_ ?_
  · exact .store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
  refine .sseq ?_ ?_
  · exact .store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
  refine .sseq ?_ ?_
  · exact .sseq_sym (t5Cond_frag) (.sseq_sym (t5Bool_frag)
      (.if_ (PePure.of_isPePure rfl)
        (t5AssignBlock_frag 48 523 524 1) (t5AssignBlock_frag 64 525 526 0)))
  refine .sseq_sym (.bound (t5Load_frag t5rSym 527 80 81)) ?_
  refine .sseq ?_ ?_
  · exact .kill_op rfl (PePure.of_isPePure rfl)
  refine .sseq ?_ ?_
  · exact .kill_op rfl (PePure.of_isPePure rfl)
  refine .sseq ?_ ?_
  · refine .run ?_
    · intro pe hpe
      obtain rfl := List.mem_singleton.mp hpe
      exact PePure.of_isPePure rfl
  refine .sseq ?_ ?_
  · exact .kill_op rfl (PePure.of_isPePure rfl)
  refine .sseq ?_ ?_
  · exact .kill_op rfl (PePure.of_isPePure rfl)
  refine .sseq (.val_pure _) ?_
  refine .save ?_ (Frag.of_pePure _ (.sym _ _))
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact specInt_pePure 0

/-! The switch's selected branch contains control flow and saves. Its
    single specified-pattern binding is characterized explicitly; no
    assumption restricts the scrutinee to the reachable integer 2. -/

theorem t6Load_frag (x : sym) (n c1 c2 : Nat) : Frag (t6Load x n c1 c2) :=
  .wseq_sym (Frag.of_pePure _ (.sym _ _))
    (.load_op rfl (.sym [] _))

theorem t6AssignStmt_frag (start n m : Nat) (v : Int) : Frag (t6AssignStmt start n m v) := by
  refine .sseq (.bound (.wseq_tuple
    (ls := [([], some (t6a n), ptrTy), ([], some (t6a m), lint)]) ?_ ?_)) (.val_pure _)
  · refine .unseq (by simp) rfl ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Frag.of_pePure _ (.sym _ _)
    · exact Frag.of_pePure _ (specInt_pePure v)
  · refine .wseq ?_ ?_
    · exact .neg_store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)

theorem t6Run_frag (an : List annot) (l : sym) : Frag (t6Run an l) := by
  refine .run ?_
  · intro pe hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact .sym _ _

theorem t6Save_frag (an : List annot) (l : sym) (body : CoreExpr) (hb : Frag body) :
    Frag (t6Save an l body) := by
  refine .save ?_ hb
  · intro pe hpe
    change pe ∈ [psym t6xSym, psym t6rSym] at hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact .sym _ _

theorem t6Cases_frag : Frag t6Cases := by
  refine .sseq ?_ (.val_pure _)
  refine .sseq (t6Save_frag _ _ _ (t6AssignStmt_frag 60 523 524 10)) ?_
  refine .sseq (t6Run_frag _ _) ?_
  refine .sseq (t6Save_frag _ _ _ (t6AssignStmt_frag 83 525 526 20)) ?_
  refine .sseq (t6Run_frag _ _) ?_
  exact .sseq (t6Save_frag _ _ _ (t6AssignStmt_frag 107 527 528 30))
    (.sseq (t6Run_frag _ _) (.val_pure _))

theorem t6Dispatch_frag : Frag t6Dispatch := by
  refine .sseq (.if_ (PePure.of_isPePure rfl) (t6Run_frag _ _) (.val_pure _)) ?_
  refine .sseq (.if_ (PePure.of_isPePure rfl) (t6Run_frag _ _) (.val_pure _)) ?_
  exact .sseq (t6Run_frag _ _) (.sseq (t6Run_frag _ _) (t6Cases_frag))

theorem t6SpecifiedBranch_frag (pe : generic_pexpr Unit sym)
    (hp : PePure (Pexpr [] () (PEcall (Sym convIntSym) [intCty, pe]))) :
    Frag (t6SpecifiedBranch pe) :=
  .sseq_sym (Frag.of_pePure _ hp) t6Dispatch_frag

theorem t6Switch_select (v : value) :
    select_case subst_sym_expr v t6SwitchPats =
      match v with
      | Vloaded (LVspecified o) => some (t6SpecifiedBranch (Pexpr [] () (PEval (Vobject o))))
      | Vloaded (LVunspecified _) => some (t5Pure (Pexpr [] () (PEundef (t6Reg 39 123) UB036_exceptional_condition)))
      | _ => none := by
  cases v <;> try rfl
  rename_i lv
  cases lv <;> rfl

theorem t6Switch_frag : Frag t6Switch := by
  refine .sseq_sym (.bound (t6Load_frag _ _ _ _)) (.case_op rfl (.sym _ _) ?_ ?_ ?_)
  · intro q hq
    simp only [t6SwitchPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (t6SpecifiedBranch_frag) _ (PePure.of_isPePure rfl)
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)
  · intro v e' hsel
    rw [t6Switch_select] at hsel
    cases v <;> try cases hsel
    rename_i lv
    cases lv with
    | LVspecified o =>
      cases hsel
      exact (t6SpecifiedBranch_frag) _ (PePure.of_isPePure rfl)
    | LVunspecified ty =>
      cases hsel
      exact Frag.of_pePure _ (PePure.of_isPePure rfl)
  · exact case_hbsz_of_branches

theorem t6Return_frag : Frag t6Return := by
  refine .sseq_sym (.bound (t6Load_frag _ _ _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _)) ?_
  refine .sseq (.run ?_) ?_
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact PePure.of_isPePure rfl
  refine .sseq (.kill_op rfl (.sym _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _)) ?_
  refine .sseq (.val_pure _) (.save ?_ (Frag.of_pePure _ (.sym _ _)))
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact specInt_pePure 0

theorem t6Main_frag : Frag t6Main := by
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)) ?_
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)) ?_
  refine .sseq_sym (.bound (Frag.of_pePure _ (specInt_pePure 2))) ?_
  refine .sseq (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl)) ?_
  refine .sseq_sym (.bound (Frag.of_pePure _ (specInt_pePure 0))) ?_
  refine .sseq (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl)) ?_
  exact .sseq (t6Switch_frag) (.sseq (t6Save_frag _ _ _ (.val_pure _))
    (.sseq (.val_pure _) (t6Return_frag)))

/-! t4: membership is compositional over the nested truth conversions,
    short-circuit branch and both effectful assignment right-hand sides. -/

theorem t4Load_frag (x : sym) (n c1 c2 : Nat) : Frag (t4Load x n c1 c2) :=
  .wseq_sym (Frag.of_pePure _ (.sym _ _))
    (.load_op rfl (.sym [] _))

theorem t4Lt_frag (x : sym) (tmp n m p q start : Nat) (k : Int) :
    Frag (t4Lt x tmp n m p q start k) := by
  refine .wseq_tuple (ls := [([], some (t5a n), lint), ([], some (t5a m), lint)]) ?_ ?_
  · refine .unseq (by simp) rfl ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (t4Load_frag) _ _ _ _
    · exact Frag.of_pePure _ (specInt_pePure k)
  · refine .case_op rfl (PePure.of_isPePure rfl) ?_ ?_ ?_
    · intro br hbr
      simp only [t4LtPats, List.mem_cons, List.not_mem_nil, or_false] at hbr
      rcases hbr with rfl | rfl <;>
        exact Frag.of_pePure _ (PePure.of_isPePure rfl)
    · intro v e' hsel
      obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
      simp only [t4LtPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl)
    · exact case_hbsz_of_branches

theorem t4Truth_frag (loc : CerbLocation.Loc) (n m p q : Nat) (negate : Bool)
    (e : CoreExpr) (he : Frag e) (hc : ccallFree e = true) :
    Frag (t4Truth loc n m p q negate e) := by
  refine .wseq_tuple (ls := [([], some (t5a n), lint), ([], some (t5a m), lint)]) ?_ ?_
  · refine .unseq (by simp) ?_ ?_
    · change (ccallFree e && (true && true)) = true
      rw [hc]
      rfl
    · intro e' he'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      rcases he' with rfl | rfl
      · exact he
      · exact Frag.of_pePure _ (specInt_pePure 0)
  · cases negate <;> exact Frag.of_pePure _ (PePure.of_isPePure rfl)

theorem t4Left_frag : Frag t4Left :=
  (t4Truth_frag) _ _ _ _ _ _ _ (t4Truth_frag _ _ _ _ _ _ _ (t4Lt_frag _ _ _ _ _ _ _ _) rfl) rfl

theorem t4Right_frag : Frag t4Right :=
  (t4Truth_frag) _ _ _ _ _ _ _ (t4Lt_frag _ _ _ _ _ _ _ _) rfl

theorem t4AndSpecified_frag (pe : generic_pexpr Unit sym) (hp : PePure pe) :
    Frag (t4AndSpecified pe) := by
  refine .if_ (.op _ _ rfl hp (.val _ _)) ?_ ?_
  · exact .sseq_sym (Frag.of_pePure _ (specInt_pePure 0))
      (Frag.of_pePure _ (PePure.of_isPePure rfl))
  · exact .sseq_sym (t4Right_frag)
      (Frag.of_pePure _ (PePure.of_isPePure rfl))

theorem t4And_select (v : value) :
    select_case subst_sym_expr v t4AndPats =
      match v with
      | Vloaded (LVspecified o) => some (t4AndSpecified (Pexpr [] () (PEval (Vobject o))))
      | Vloaded (LVunspecified _) => some (t5Pure (Pexpr [] ()
          (PEundef (t4RegP 46 60 52) (UB_CERB004_unspecified UB_unspec_conditional))))
      | _ => none := by
  cases v <;> try rfl
  rename_i lv
  cases lv <;> rfl

theorem t4And_frag : Frag t4And := by
  refine .sseq_sym (t4Left_frag) (.case_op rfl (.sym _ _) ?_ ?_ ?_)
  · intro br hbr
    simp only [t4AndPats, List.mem_cons, List.not_mem_nil, or_false] at hbr
    rcases hbr with rfl | rfl
    · exact t4AndSpecified_frag _ (.sym _ _)
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)
  · intro v e' hsel
    rw [t4And_select] at hsel
    cases v <;> try cases hsel
    rename_i lv
    cases lv with
    | LVspecified o =>
      cases hsel
      exact t4AndSpecified_frag _ (.val _ _)
    | LVunspecified ty =>
      cases hsel
      exact Frag.of_pePure _ (PePure.of_isPePure rfl)
  · exact case_hbsz_of_branches

theorem t4Cond_frag : Frag t4Cond :=
  .bound (t4Truth_frag _ _ _ _ _ _ _ (t4And_frag) rfl)

theorem t4Bool_frag : Frag t4Bool := by
  refine .case_op rfl (.sym _ _) ?_ ?_ ?_
  · intro q hq
    simp only [t4BoolPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl)
    · refine .nd (by decide) ?_
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .val_pure _
  · intro v e' hsel
    obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
    simp only [t4BoolPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl)
    · have he (bs : List (sym × value)) : substFold (Expr [] (End [t5Pure (Pexpr [] () (PEval Vtrue)),
          t5Pure (Pexpr [] () (PEval Vfalse))])) bs =
          Expr [] (End [t5Pure (Pexpr [] () (PEval Vtrue)),
            t5Pure (Pexpr [] () (PEval Vfalse))]) := by
        induction bs with
        | nil => rfl
        | cons pair rest ih =>
          rcases pair with ⟨s, v⟩
          rw [substFold_cons, ih]
          rfl
      rw [he binds]
      refine .nd (by decide) ?_
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .val_pure _
  · exact case_hbsz_of_branches

theorem t4Add_frag (loc : CerbLocation.Loc) (n m p q : Nat) (e1 e2 : CoreExpr)
    (h1 : Frag e1) (h2 : Frag e2) (hc1 : ccallFree e1 = true) (hc2 : ccallFree e2 = true) :
    Frag (t4Add loc n m p q e1 e2) := by
  refine .wseq_tuple (ls := [([], some (t5a n), lint), ([], some (t5a m), lint)]) ?_ ?_
  · refine .unseq (by simp) ?_ ?_
    · change (ccallFree e1 && (ccallFree e2 && true)) = true
      rw [hc1, hc2]
      rfl
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact h1
      · exact h2
  · exact Frag.of_pePure _ (PePure.of_isPePure rfl)

theorem t4Assign_frag (x : sym) (start n m : Nat) (rhs : CoreExpr)
    (hr : Frag rhs) (hc : ccallFree rhs = true) : Frag (t4Assign x start n m rhs) := by
  refine .sseq (.bound (.wseq_tuple
    (ls := [([], some (t5a n), ptrTy), ([], some (t5a m), lint)]) ?_ ?_)) (.val_pure _)
  · refine .unseq (by simp) ?_ ?_
    · change (true && (ccallFree rhs && true)) = true
      rw [hc]
      rfl
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact Frag.of_pePure _ (.sym _ _)
      · exact hr
  · exact .wseq
      (.neg_store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl))
      (Frag.of_pePure _ (PePure.of_isPePure rfl))

theorem t4Save_frag (l : sym) (body : CoreExpr) (hb : Frag body) : Frag (t4Save l body) := by
  refine .save ?_ hb
  · intro pe hpe
    change pe ∈ [psym t4iSym, psym t4sSym] at hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact .sym _ _

theorem t4Body_frag : Frag t4Body := by
  refine .sseq (.sseq (.sseq ?_ (.sseq ?_ (.val_pure _)))
    (.sseq (t4Save_frag _ _ (.val_pure _)) (.val_pure _))) ?_
  · exact (t4Assign_frag) _ _ _ _ _
      (t4Add_frag _ _ _ _ _ _ _ (t4Load_frag _ _ _ _) (t4Load_frag _ _ _ _) rfl rfl) rfl
  · exact (t4Assign_frag) _ _ _ _ _
      (t4Add_frag _ _ _ _ _ _ _ (t4Load_frag _ _ _ _)
        (Frag.of_pePure _ (specInt_pePure 1)) rfl rfl) rfl
  · refine .run ?_
    · intro pe hpe
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      rcases hpe with rfl | rfl <;> exact .sym _ _

theorem t4While_frag : Frag t4While :=
  (t4Save_frag) _ _ (.sseq_sym (t4Cond_frag) (.sseq_sym (t4Bool_frag)
    (.if_ (.sym _ _) (t4Body_frag) (.val_pure _))))

theorem t4Return_frag : Frag t4Return := by
  refine .sseq_sym (.bound (t4Load_frag _ _ _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _)) ?_
  refine .sseq (.run ?_) ?_
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact PePure.of_isPePure rfl
  refine .sseq (.kill_op rfl (.sym _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _)) ?_
  refine .sseq (.val_pure _) (.save ?_ (Frag.of_pePure _ (.sym _ _)))
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact specInt_pePure 0

theorem t4Main_frag : Frag t4Main := by
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)) ?_
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)) ?_
  refine .sseq_sym (.bound (Frag.of_pePure _ (specInt_pePure 0))) ?_
  refine .sseq (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl)) ?_
  refine .sseq_sym (.bound (Frag.of_pePure _ (specInt_pePure 0))) ?_
  refine .sseq (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl)) ?_
  exact .sseq (.sseq (t4While_frag) (.sseq (t4Save_frag _ _ (.val_pure _)) (.val_pure _))) (t4Return_frag)

end CerberusHeapLang.CorpusE0
