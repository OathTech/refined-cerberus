/- Focused re-pin inspection, 2026-09-06 [AGENT].
All declared theorems in retained t4 and the malloc-list client.
This does not replace the exhaustive package audit or full-file validation.
Run from cerberus-heaplang via ../scripts/capped lake env lean <this file>.
-/
import CerberusHeapLang.CorpusT4Exhibit
import CerberusHeapLang.MallocListExhibit

set_option autoImplicit false

-- CorpusT4Exhibit
#print axioms CerberusHeapLang.wpt_t4Load
#print axioms CerberusHeapLang.t4a_ne
#print axioms CerberusHeapLang.t4Lt_eval
#print axioms CerberusHeapLang.wpt_t4Lt
#print axioms CerberusHeapLang.t4TruthBranch_eval
#print axioms CerberusHeapLang.wpt_t4Truth
#print axioms CerberusHeapLang.wpt_t4Left
#print axioms CerberusHeapLang.wpt_t4Right
#print axioms CerberusHeapLang.t4SourceFrame.add
#print axioms CerberusHeapLang.wpt_t4And
#print axioms CerberusHeapLang.wpt_t4Cond
#print axioms CerberusHeapLang.t4Bool_select
#print axioms CerberusHeapLang.t4BoolBranch_eval
#print axioms CerberusHeapLang.wpt_t4Bool
#print axioms CerberusHeapLang.t4Q_while
#print axioms CerberusHeapLang.t4Q_continue
#print axioms CerberusHeapLang.t4Q_break
#print axioms CerberusHeapLang.t4Q_ret
#print axioms CerberusHeapLang.t4Q_eq
#print axioms CerberusHeapLang.t4Q_lookup
#print axioms CerberusHeapLang.t4Q_cont
#print axioms CerberusHeapLang.t4LoopContext_frag
#print axioms CerberusHeapLang.t4Q_frag
#print axioms CerberusHeapLang.collect_new_t4Main
#print axioms CerberusHeapLang.t4Main_labeledAt
#print axioms CerberusHeapLang.wpt_t4Add
#print axioms CerberusHeapLang.wpt_t4AddSI
#print axioms CerberusHeapLang.wpt_t4AddI1
#print axioms CerberusHeapLang.t4SourceFrame.fresh
#print axioms CerberusHeapLang.wpt_t4Assign
#print axioms CerberusHeapLang.wpt_t4AssignS
#print axioms CerberusHeapLang.wpt_t4AssignI
#print axioms CerberusHeapLang.t4SourceFrame.params
#print axioms CerberusHeapLang.t4PtrParams_bindArgs
#print axioms CerberusHeapLang.t4PtrInits_bindSaveParams
#print axioms CerberusHeapLang.t4PtrArgs_eval
#print axioms CerberusHeapLang.wpt_t4Save
#print axioms CerberusHeapLang.wpt_t4Body
#print axioms CerberusHeapLang.t4Sum_succ
#print axioms CerberusHeapLang.t4Index_cases
#print axioms CerberusHeapLang.t4Sum_le
#print axioms CerberusHeapLang.t4Guard
#print axioms CerberusHeapLang.t4Index_loaded
#print axioms CerberusHeapLang.t4Sum_loaded
#print axioms CerberusHeapLang.t4Budget_succ
#print axioms CerberusHeapLang.t4RetParams_bindArgs
#print axioms CerberusHeapLang.t4Kill_eq
#print axioms CerberusHeapLang.wpt_t4Return
#print axioms CerberusHeapLang.wpt_t4LoopTest
#print axioms CerberusHeapLang.wpt_t4LoopStep
#print axioms CerberusHeapLang.wpt_t4WhileCont
#print axioms CerberusHeapLang.t4_blockSpecsT
#print axioms CerberusHeapLang.wpt_t4WhileEntry
#print axioms CerberusHeapLang.t4_wpt
#print axioms CerberusHeapLang.t4_certified_production

-- MallocListExhibit
#print axioms CerberusHeapLang.mlQ_lookup
#print axioms CerberusHeapLang.mlQ_inv
#print axioms CerberusHeapLang.mlRS_labeledAt
#print axioms CerberusHeapLang.mlFrame_symFrame
#print axioms CerberusHeapLang.mlFrameQ_symFrame
#print axioms CerberusHeapLang.mlFrameB_symFrame
#print axioms CerberusHeapLang.mlFrameN_symFrame
#print axioms CerberusHeapLang.mlFrame_lookup_p
#print axioms CerberusHeapLang.mlFrame_lookup_i
#print axioms CerberusHeapLang.mlFrameQ_lookup_q
#print axioms CerberusHeapLang.mlFrameQ_lookup_i
#print axioms CerberusHeapLang.mlFrameQ_lookup_p
#print axioms CerberusHeapLang.mlFrameB_lookup_b
#print axioms CerberusHeapLang.mlFrameB_lookup_p
#print axioms CerberusHeapLang.mlFrameN_lookup_n
#print axioms CerberusHeapLang.mlFrameN_lookup_p
#print axioms CerberusHeapLang.bindSave_ml
#print axioms CerberusHeapLang.bindArgs_ml
#print axioms CerberusHeapLang.bindSym_ml
#print axioms CerberusHeapLang.ml_memop_operands_nonvalue
#print axioms CerberusHeapLang.ml_guard_eval
#print axioms CerberusHeapLang.ml_p_eval
#print axioms CerberusHeapLang.ml_q_eval
#print axioms CerberusHeapLang.ml_i_eval_Q
#print axioms CerberusHeapLang.ml_p_eval_Q
#print axioms CerberusHeapLang.ml_shift_q_eval
#print axioms CerberusHeapLang.ml_args_build_eval
#print axioms CerberusHeapLang.ml_b_eval
#print axioms CerberusHeapLang.ml_shift_p_eval_B
#print axioms CerberusHeapLang.ml_p_eval_N
#print axioms CerberusHeapLang.ml_args_free_eval
#print axioms CerberusHeapLang.longMval_encodes
#print axioms CerberusHeapLang.longMval_compat
#print axioms CerberusHeapLang.longMval_fpm
#print axioms CerberusHeapLang.longMval_bytes_fpm
#print axioms CerberusHeapLang.longMval_img_length
#print axioms CerberusHeapLang.longMval_storable
#print axioms CerberusHeapLang.nodePtr_storable
#print axioms CerberusHeapLang.nodePtr_img_length
#print axioms CerberusHeapLang.nodePtr_reconstruct
#print axioms CerberusHeapLang.mlBuilt_inner_len
#print axioms CerberusHeapLang.mlBuilt_len
#print axioms CerberusHeapLang.mlBuilt_nextDec
#print axioms CerberusHeapLang.regionOwn_alloc16
#print axioms CerberusHeapLang.isRegionList_cons
#print axioms CerberusHeapLang.isRegionList_nil_intro
#print axioms CerberusHeapLang.isRegionList_cons_intro
#print axioms CerberusHeapLang.isRegionList_wf
#print axioms CerberusHeapLang.regionOwn_isRegionList_ne
#print axioms CerberusHeapLang.deadRegions_cons
#print axioms CerberusHeapLang.regionOwn_deadRegions_ne
#print axioms CerberusHeapLang.mlBody_frag
#print axioms CerberusHeapLang.mlBody_pot
#print axioms CerberusHeapLang.mlProg_pot
#print axioms CerberusHeapLang.mlParams_depth
#print axioms CerberusHeapLang.ml_body_wps
#print axioms CerberusHeapLang.ml_blockSpecs
#print axioms CerberusHeapLang.ml_wps
#print axioms CerberusHeapLang.mlPost_readout
#print axioms CerberusHeapLang.ml_body_wpt
#print axioms CerberusHeapLang.ml_blockSpecsT
#print axioms CerberusHeapLang.ml_wpt
#print axioms CerberusHeapLang.ml_blockSpecsT_readout
#print axioms CerberusHeapLang.ml_wpt_readout
#print axioms CerberusHeapLang.mlProg_size
#print axioms CerberusHeapLang.col_mlProg
#print axioms CerberusHeapLang.collect_new_ml
#print axioms CerberusHeapLang.ml_labeledAt
#print axioms CerberusHeapLang.ml_budget_bridge
#print axioms CerberusHeapLang.ml_counter_bound
#print axioms CerberusHeapLang.malloc_list_certified_production

-- Selected public, representation, registration and production contracts.
#check CerberusHeapLang.t4Q_eq
#check CerberusHeapLang.t4Q_lookup
#check CerberusHeapLang.t4Q_frag
#check CerberusHeapLang.wpt_t4Assign
#check CerberusHeapLang.wpt_t4Body
#check CerberusHeapLang.wpt_t4LoopStep
#check CerberusHeapLang.t4_blockSpecsT
#check CerberusHeapLang.t4_wpt
#check CerberusHeapLang.t4_certified_production
#check CerberusHeapLang.longMval_img_length
#check CerberusHeapLang.longMval_storable
#check CerberusHeapLang.nodePtr_storable
#check CerberusHeapLang.mlBuilt_len
#check CerberusHeapLang.mlBuilt_nextDec
#check CerberusHeapLang.mlBody_frag
#check CerberusHeapLang.mlParams_depth
#check CerberusHeapLang.ml_body_wps
#check CerberusHeapLang.ml_wps
#check CerberusHeapLang.ml_blockSpecs
#check CerberusHeapLang.ml_body_wpt
#check CerberusHeapLang.ml_wpt
#check CerberusHeapLang.ml_blockSpecsT
#check CerberusHeapLang.ml_wpt_readout
#check CerberusHeapLang.mlProg_size
#check CerberusHeapLang.col_mlProg
#check CerberusHeapLang.ml_counter_bound
#check CerberusHeapLang.malloc_list_certified_production
