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
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe40 (by decide))
    · intro v e' hsel
      obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact Frag.substFold_pure binds _ _ (PePure.of_isPePure rfl) (depLe40 (by decide))
    · apply case_hbsz_of_branches
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
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
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Frag.of_pePure _ (PePure.of_isPePure rfl) (depLe (by decide))
    · refine .nd (by decide) ?_
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .val_pure _
  · intro v e' hsel
    obtain ⟨pat, br, binds, hmem, _, rfl⟩ := select_case_some hsel
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
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
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
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

end CerberusHeapLang.CorpusE0
