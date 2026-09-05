/-
Fragment witnesses for the E5 emitted corpus, separate from the program
proofs. Membership includes every syntactic branch, including alternatives
the certified run will not take. Substitution.lean handles selected pure
branches for every possible scrutinee value.
-/
import CerberusHeapLang.Examples.CorpusE0
import CerberusHeapLang.Substitution

set_option autoImplicit false
namespace CerberusHeapLang.CorpusE0

theorem t5Load_frag (x : sym) (n c1 c2 : Nat) : Frag (t5Load x n c1 c2) :=
  .wseq_sym (Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _))
    (.load_op rfl (.sym [] _) (peDepth_sym_le [] _))

theorem t5Gt_frag : Frag t5Gt := by
  refine .wseq_tuple (ls := [([], some (t5a 518), lint), ([], some (t5a 519), lint)]) ?_ ?_
  · refine .unseq (by simp) rfl ?_
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact t5Load_frag xSym 517 39 40
    · obtain rfl := List.mem_singleton.mp he
      exact Frag.of_pePure _ (specInt_pePure 2) (depLe (by decide))
  · refine .case_op rfl (PePure.of_isPePure rfl) (depLe (by decide)) ?_ ?_ ?_
    · intro q hq
      simp only [t5GtPats, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe40 (by decide))
    · intro v e' hsel
      obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
      simp only [t5GtPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl) (depLe40 (by decide))
    · apply case_hbsz_of_branches
      intro q hq
      simp only [t5GtPats, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl

theorem t5Cond_frag : Frag t5Cond := by
  refine .bound (.wseq_tuple
    (ls := [([], some (t5a 512), lint), ([], some (t5a 513), lint)]) ?_ ?_)
  · refine .unseq (by simp) rfl ?_
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact t5Gt_frag
    · obtain rfl := List.mem_singleton.mp he
      exact Frag.of_pePure _ (specInt_pePure 0) (depLe (by decide))
  · exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe40 (by decide))

theorem t5Bool_frag : Frag t5Bool := by
  refine .case_op rfl (PePure.of_isPePure rfl) (depLe (by decide)) ?_ ?_ ?_
  · intro q hq
    simp only [t5BoolPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe (by decide))
    · refine .nd (by decide) ?_
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .val_pure _
  · intro v e' hsel
    obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
    simp only [t5BoolPats, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl) (depLe (by decide))
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
  · apply case_hbsz_of_branches
    intro q hq
    simp only [t5BoolPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl

theorem t5AssignBlock_frag (start n m : Nat) (v : Int) : Frag (t5AssignBlock start n m v) := by
  refine .sseq (.sseq (.bound (.wseq_tuple
    (ls := [([], some (t5a n), ptrTy), ([], some (t5a m), lint)]) ?_ ?_)) (.val_pure _)) (.val_pure _)
  · refine .unseq (by simp) rfl ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _)
    · exact Frag.of_pePure _ (specInt_pePure v) (depLe (Nat.le_of_ble_eq_true rfl))
  · refine .wseq ?_ ?_
    · exact .neg_store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
        (depLe (Nat.le_of_ble_eq_true rfl)) (depLe40 (Nat.le_of_ble_eq_true rfl))
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe40 (Nat.le_of_ble_eq_true rfl))

theorem t5Main_frag : Frag t5Main := by
  refine .sseq_sym ?_ ?_
  · exact .create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
      (depLe (by decide)) (depLe (by decide))
  refine .sseq_sym ?_ ?_
  · exact .create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
      (depLe (by decide)) (depLe (by decide))
  refine .sseq_sym ?_ ?_
  · exact .bound (Frag.of_pePure _ (specInt_pePure 3) (depLe (by decide)))
  refine .sseq ?_ ?_
  · exact .store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
      (depLe (by decide)) (depLe40 (by decide))
  refine .sseq ?_ ?_
  · exact .store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
      (depLe (by decide)) (depLe (by decide))
  refine .sseq ?_ ?_
  · exact .sseq_sym t5Cond_frag (.sseq_sym t5Bool_frag
      (.if_ (PePure.of_isPePure rfl) (depLe (by decide))
        (t5AssignBlock_frag 48 523 524 1) (t5AssignBlock_frag 64 525 526 0)))
  refine .sseq_sym (.bound (t5Load_frag t5rSym 527 80 81)) ?_
  refine .sseq ?_ ?_
  · exact .kill_op rfl (PePure.of_isPePure rfl) (depLe (by decide))
  refine .sseq ?_ ?_
  · exact .kill_op rfl (PePure.of_isPePure rfl) (depLe (by decide))
  refine .sseq ?_ ?_
  · refine .run ?_ ?_
    · intro pe hpe
      obtain rfl := List.mem_singleton.mp hpe
      exact PePure.of_isPePure rfl
    · intro pe hpe
      obtain rfl := List.mem_singleton.mp hpe
      exact depLe40 (by decide)
  refine .sseq ?_ ?_
  · exact .kill_op rfl (PePure.of_isPePure rfl) (depLe (by decide))
  refine .sseq ?_ ?_
  · exact .kill_op rfl (PePure.of_isPePure rfl) (depLe (by decide))
  refine .sseq (.val_pure _) ?_
  refine .save ?_ ?_ (Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _))
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact specInt_pePure 0
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact depLe (by decide)

/-! The switch's selected branch contains control flow and saves. Its
    single specified-pattern binding is characterized explicitly; no
    assumption restricts the scrutinee to the reachable integer 2. -/

theorem t6Load_frag (x : sym) (n c1 c2 : Nat) : Frag (t6Load x n c1 c2) :=
  .wseq_sym (Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _))
    (.load_op rfl (.sym [] _) (peDepth_sym_le [] _))

theorem t6AssignStmt_frag (start n m : Nat) (v : Int) : Frag (t6AssignStmt start n m v) := by
  refine .sseq (.bound (.wseq_tuple
    (ls := [([], some (t6a n), ptrTy), ([], some (t6a m), lint)]) ?_ ?_)) (.val_pure _)
  · refine .unseq (by simp) rfl ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _)
    · exact Frag.of_pePure _ (specInt_pePure v) (depLe (Nat.le_of_ble_eq_true rfl))
  · refine .wseq ?_ ?_
    · exact .neg_store_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
        (depLe (Nat.le_of_ble_eq_true rfl)) (depLe40 (Nat.le_of_ble_eq_true rfl))
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe40 (Nat.le_of_ble_eq_true rfl))

theorem t6Run_frag (an : List annot) (l : sym) : Frag (t6Run an l) := by
  refine .run ?_ ?_
  · intro pe hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact .sym _ _
  · intro pe hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact peDepth_sym_le _ _

theorem t6Save_frag (an : List annot) (l : sym) (body : CoreExpr) (hb : Frag body) :
    Frag (t6Save an l body) := by
  refine .save ?_ ?_ hb
  · intro pe hpe
    change pe ∈ [psym t6xSym, psym t6rSym] at hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact .sym _ _
  · intro pe hpe
    change pe ∈ [psym t6xSym, psym t6rSym] at hpe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
    rcases hpe with rfl | rfl <;> exact peDepth_sym_le _ _

theorem t6Cases_frag : Frag t6Cases := by
  refine .sseq ?_ (.val_pure _)
  refine .sseq (t6Save_frag _ _ _ (t6AssignStmt_frag 60 523 524 10)) ?_
  refine .sseq (t6Run_frag _ _) ?_
  refine .sseq (t6Save_frag _ _ _ (t6AssignStmt_frag 83 525 526 20)) ?_
  refine .sseq (t6Run_frag _ _) ?_
  exact .sseq (t6Save_frag _ _ _ (t6AssignStmt_frag 107 527 528 30))
    (.sseq (t6Run_frag _ _) (.val_pure _))

theorem t6Dispatch_frag : Frag t6Dispatch := by
  refine .sseq (.if_ (PePure.of_isPePure rfl) (depLe (by decide)) (t6Run_frag _ _) (.val_pure _)) ?_
  refine .sseq (.if_ (PePure.of_isPePure rfl) (depLe (by decide)) (t6Run_frag _ _) (.val_pure _)) ?_
  exact .sseq (t6Run_frag _ _) (.sseq (t6Run_frag _ _) t6Cases_frag)

theorem t6SpecifiedBranch_frag (pe : generic_pexpr Unit sym)
    (hp : PePure (Pexpr [] () (PEcall (Sym convIntSym) [intCty, pe])))
    (hd : peDepth (Pexpr [] () (PEcall (Sym convIntSym) [intCty, pe])) ≤ lemDefaultFuel) :
    Frag (t6SpecifiedBranch pe) :=
  .sseq_sym (Frag.of_pePure _ hp hd) t6Dispatch_frag

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
  refine .sseq_sym (.bound (t6Load_frag _ _ _ _)) (.case_op rfl (.sym _ _) (peDepth_sym_le _ _) ?_ ?_ ?_)
  · intro q hq
    simp only [t6SwitchPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact t6SpecifiedBranch_frag _ (PePure.of_isPePure rfl) (depLe40 (by decide))
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe (by decide))
  · intro v e' hsel
    rw [t6Switch_select] at hsel
    cases v <;> try cases hsel
    rename_i lv
    cases lv with
    | LVspecified o =>
      cases hsel
      exact t6SpecifiedBranch_frag _ (PePure.of_isPePure rfl) (depLe40 (Nat.le_of_ble_eq_true rfl))
    | LVunspecified ty =>
      cases hsel
      exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe (by decide))
  · apply case_hbsz_of_branches
    intro q hq
    simp only [t6SwitchPats, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl

theorem t6Return_frag : Frag t6Return := by
  refine .sseq_sym (.bound (t6Load_frag _ _ _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _) (peDepth_sym_le _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _) (peDepth_sym_le _ _)) ?_
  refine .sseq (.run ?_ ?_) ?_
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact PePure.of_isPePure rfl
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact depLe40 (by decide)
  refine .sseq (.kill_op rfl (.sym _ _) (peDepth_sym_le _ _)) ?_
  refine .sseq (.kill_op rfl (.sym _ _) (peDepth_sym_le _ _)) ?_
  refine .sseq (.val_pure _) (.save ?_ ?_ (Frag.of_pePure _ (.sym _ _) (peDepth_sym_le _ _)))
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact specInt_pePure 0
  · intro pe hpe
    obtain rfl := List.mem_singleton.mp hpe
    exact depLe (by decide)

theorem t6Main_frag : Frag t6Main := by
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
    (depLe (by decide)) (depLe (by decide))) ?_
  refine .sseq_sym (.create_op rfl (PePure.of_isPePure rfl) (PePure.of_isPePure rfl)
    (depLe (by decide)) (depLe (by decide))) ?_
  refine .sseq_sym (.bound (Frag.of_pePure _ (specInt_pePure 2) (depLe (by decide)))) ?_
  refine .sseq (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl)
    (peDepth_sym_le _ _) (depLe40 (by decide))) ?_
  refine .sseq_sym (.bound (Frag.of_pePure _ (specInt_pePure 0) (depLe (by decide)))) ?_
  refine .sseq (.store_op rfl (.sym _ _) (PePure.of_isPePure rfl)
    (peDepth_sym_le _ _) (depLe40 (by decide))) ?_
  exact .sseq t6Switch_frag (.sseq (t6Save_frag _ _ _ (.val_pure _))
    (.sseq (.val_pure _) t6Return_frag))

end CerberusHeapLang.CorpusE0
