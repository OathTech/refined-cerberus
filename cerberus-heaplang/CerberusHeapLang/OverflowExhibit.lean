/-
CerberusHeapLang.OverflowExhibit — THE NEGATIVE EXHIBIT OF E3: `x + 1` at
`x = INT_MAX` has the UB036 kill as its only outcome.

`progCE3 n` (EmittedCExhibit.lean) is `int x = n; return x + 1;` in the
emitted shape; `exhibitC_prod_e3` certifies the run at `n = 3`. At
`n = 2147483647` the C `+` overflows: the elaborator's
`catch_exceptional_condition_add('signed int', __conv_int__(…), …)` is
the engine's `mk_call_catch_exceptional_condition` (core_eval.lem:99–105:
`mk_iop` then the range check, `Nothing` out of range) — the sum is out
of `int`'s range, so the evaluator's `PEcatch_exceptional_condition` arm
(core_eval.lem:839–853) raises `undef loc [UB036_exceptional_condition]`
at ITS `loc` argument, the thread's `current_loc` (what `one_step0` passes
in) — NOT the `undef` arm's own location `ecAddLoc`, which the `case`
never reaches.

WHAT IS PROVED (kernel-only, over the shipped engine):
* `overflow_evalClass` — the classifier's verdict at the `+` node with
  `b1 ↦ Specified(INT_MAX), b2 ↦ Specified(1)`: `.undef loc [UB036]`
  (IntRules.lean `evalClass_cAdd_overflow`).
* `overflow_step_ctx` — the engine's `step_ctx` at a thread whose arena is
  the residual program at that round (`progCE3_atAdd`) is the ONE
  with-runstate EVAL step whose monad FAILS with that undef
  (`step_ctx_pure_op_fail`, the classifier bridge).
* `overflow_driver2_killed` — the genuine `driver2_lemFuel` worker at
  every positive outer counter (`Nat.succ fl`), with the caller's ambient
  `LemFuel.fuel ≥ 8` used throughout evaluator and per-thread execution,
  from any driver state whose single thread is at that round is
  `NDkilled (Undef0 loc [UB036])` — the round's only outcome
  (`loop_step_withrs_eval_killed`, `driver2_killed`).
* `overflow_driver2_killed_frame` — the same at the CONCRETE environment
  frame the positive derivation reaches at that round (`frBK`).

WHAT IS NOT PROVED, and why (docs/2026-09-05_e3-notes.md §6, [AGENT]): the
whole-run statement `runND (drive … (prodFileLib stdlibE3 [] (progCE3
2147483647)) …) = [(Killed dst (Undef0 …), [], dst)]` from the INITIAL
driver state. Its prefix (create / store / load / two pure rounds) needs
the concrete memory states after each action spelled out (`errno_alloc_eq`
style), and the kernel cannot evaluate the shipped driver as a whole
(`decide +kernel` on the run's status was measured NOT to reduce, §6). The
whole-run fact was MEASURED by compiled evaluation (`#eval`, recorded
verbatim in §6: `killed undef ubs=1 ub036=true
loc=exhibitC.c:1:36-exhibitC.c:1:41 out=[]`); it is a measurement, not a
theorem of this module. The theorems above are the driver-level kill at
the round the measurement kills at. They require ambient fuel at least
eight (the addition's operand-depth bound) and every positive outer
counter. At outer counter zero the driver exhausts; no specific-UB claim
is made for smaller ambient budgets. The context traversal uses the
shipped structural measure independently of the ambient instance. The
quoted whole-run measurement is historical, not remeasured on this pin.

Module class: negative-test (a statement of what the pipeline REFUSES).
-/
import CerberusHeapLang.EmittedCExhibit
import CerberusHeapLang.Round

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-- `INT_MAX` of the gcc impl (`CerbMem.maxIval (Signed Int_)`,
    IntRules.lean `int_max_eq`). -/
def intMaxC : Int := 2147483647

/-- The tail of `progCE3` after the `a3` binder (kill; run; kill; pure; save). -/
def progCE3_tail : CoreExpr :=
  Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (killOpRedex [] (ecLoc 1 0 1 54) empty_annotation (Static0 intTy) (psymC xSymC))
  (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [] (Erun empty_annotation retSymC [convLoadedIntC a3SymC]))
  (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (killOpRedex [] (ecLoc 1 0 1 54) empty_annotation (Static0 intTy) (psymC xSymC))
  (Expr [] (Esseq (Pattern [] (CaseBase (none, BTy_unit)))
    (Expr [] (Epure (Pexpr [] () (PEval Vunit))))
  (Expr [Aloc (ecLoc 1 0 1 54), Astmt]
    (Esave (retSymC, lintC) [(rSymC, ((lintC, none), lintPe 0))]
      (Expr [] (Epure (psymC rSymC))))))))))))

/-- THE RESIDUAL PROGRAM AT THE `+` ROUND: after the binders `x`, `a1`,
    the store, `a2` and the weak tuple `(b1, b2)` have been reduced (each a
    beta of its `let`), the arena is the `a3` binder whose head is
    `bound(pure(<the + node>))` — the redex is the pure node through
    `Csseq`/`Cbound`. (The `Ewseq` wrapper vanished with its beta; its
    `Aloc` was written to the thread's `current_loc` — the kill's location.) -/
def progCE3_atAdd : CoreExpr :=
  Expr [Aloc (ecLoc 1 28 1 42), Astmt] (Esseq (symPat [] a3SymC lintC)
    (Expr [Astd "§6.5#2"] (Ebound
      (Expr [] (Epure (cAddPe b1SymC b2SymC v1SymC v2SymC ecAddLoc)))))
    progCE3_tail)

theorem progCE3_atAdd_decomp :
    Decomp progCE3_atAdd (Csseq [Aloc (ecLoc 1 28 1 42), Astmt] (symPat [] a3SymC lintC)
        (Cbound [Astd "§6.5#2"] CTX) progCE3_tail)
      (pureRedex [] (cAddPe b1SymC b2SymC v1SymC v2SymC ecAddLoc)) :=
  Decomp.sseq_sym (Decomp.bound (Decomp.root (Redex.pure_e rfl)))

/-- The selected branch of the `+` at `(Specified(INT_MAX), Specified(1))`. -/
theorem cAdd_select_max1 :
    select_case subst_sym_pexpr (Vtuple [lint intMaxC, lint 1]) (cAddPats v1SymC v2SymC ecAddLoc) =
      some (cAddBranch intMaxC 1) := rfl

/-- THE CLASSIFIER'S VERDICT: the `+` node at `b1 ↦ Specified(INT_MAX)`,
    `b2 ↦ Specified(1)` is the undef `UB036_exceptional_condition` at the
    classifier's location argument (the thread's `current_loc`). -/
theorem overflow_evalClass [LemFuel] {tds : CerbTags.TagDefsMap} {ext : Fmap sym sym}
    {file : generic_file Unit core_run_annotation} {ρ : EnvStack} (loc : CerbLocation.Loc)
    (hb1 : evalPexpr tds ext file ρ (stdSym b1SymC) = some (lint intMaxC))
    (hb2 : evalPexpr tds ext file ρ (stdSym b2SymC) = some (lint 1)) :
    evalClass tds loc ext file ρ (cAddPe b1SymC b2SymC v1SymC v2SymC ecAddLoc) =
      EvalOut.undef loc [UB036_exceptional_condition] :=
  evalClass_cAdd_overflow loc hb1 hb2 cAdd_select_max1 (by decide) (by decide) (by decide)
    (by decide) (Or.inr (by decide))

/-- THE ENGINE'S STEP at the round: `step_ctx` at a thread whose arena is
    `progCE3_atAdd` and whose environment binds `b1`, `b2` as above is the
    single with-runstate EVAL step whose monad fails with the undef at the
    thread's `current_loc` (through `one_step0`'s PURE arm and the
    classifier bridge, `step_ctx_pure_op_fail`). -/
theorem overflow_step_ctx [LemFuel] (hfuel : 8 ≤ LemFuel.fuel) (tds : Fmap sym (CerbLocation.Loc × tag_definition)) (σ : Mem)
    (file : generic_file Unit core_run_annotation) (ext : Fmap sym sym)
    (tid : Nat) (parent : Option Nat) (th : thread_state)
    (harena : th.arena = progCE3_atAdd)
    (hb1 : evalPexpr tds ext file th.env (stdSym b1SymC) = some (lint intMaxC))
    (hb2 : evalPexpr tds ext file th.env (stdSym b2SymC) = some (lint 1)) :
    ∃ (s : String) (m : core_runM thread_state),
      step_ctx tds σ file ext tid (parent, th) =
        [Step_with_runstate2 (RSK_eval s) m] ∧
      ∀ rs, m rs = (EvalFail.undef th.current_loc [UB036_exceptional_condition]).run
        thread_state core_run_state rs := by
  obtain ⟨s, m, post, hsteps, hm⟩ := step_ctx_pure_op_fail progCE3_atAdd_decomp
    rfl (PePure.of_isPePure rfl) (by rw [peDepth_cAddPe]; exact hfuel) tds σ file ext tid parent th harena
    (by rw [overflow_evalClass th.current_loc hb1 hb2]; rfl)
  -- E4: the engine's step list is a SINGLETON here — no `unseq` frame is
  -- open at the `+` round (`ctxNoUnseq`, the pre-E4 singleton reading)
  refine ⟨s, m, step_ctx_singleton_of_root ?_ hsteps, hm⟩
  rw [harena]
  unfold get_ctx
  rw [progCE3_atAdd_decomp.get_ctx_single rfl _
    (Nat.le_succ_of_le (esize_le_lemSize progCE3_atAdd))]
  rfl

/-- With ambient fuel at least eight, the genuine driver worker kills
    at the round for every positive outer counter (`Nat.succ fl`);
    outer counter zero exhausts. From any driver
    state whose single thread is at the `+` round (arena `progCE3_atAdd`,
    `b1 ↦ Specified(INT_MAX)`, `b2 ↦ Specified(1)`), `driver2` is exactly
    `NDkilled (Undef0 current_loc [UB036_exceptional_condition])`. -/
theorem overflow_driver2_killed [LemFuel] (hfuel : 8 ≤ LemFuel.fuel) (fl : Nat) (dst : driver_state) (th : thread_state)
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (harena : th.arena = progCE3_atAdd)
    (hb1 : evalPexpr fmapEmpty dst.core_extern dst.core_file th.env (stdSym b1SymC) =
      some (lint intMaxC))
    (hb2 : evalPexpr fmapEmpty dst.core_extern dst.core_file th.env (stdSym b2SymC) =
      some (lint 1)) :
    ∃ dstK : driver_state,
      runOne (driver2_lemFuel (Nat.succ fl) fmapEmpty false) dst =
        (NDkilled (Undef0 th.current_loc [UB036_exceptional_condition]), dstK) := by
  obtain ⟨s, m, hsteps, hm⟩ := overflow_step_ctx (hfuel := hfuel) fmapEmpty dst.layout_state dst.core_file
    dst.core_extern 0 none th harena hb1 hb2
  obtain ⟨dstK, hloop⟩ := loop_step_withrs_eval_killed (by omega)
    (LemFuel.fuel - 1) fmapEmpty fmapEmpty hth hsteps (hm _)
  rw [show Nat.succ (LemFuel.fuel - 1) = LemFuel.fuel from by omega] at hloop
  exact ⟨dstK, driver2_killed (by omega) fl fmapEmpty dst dstK th _ hth hloop⟩

/-! ## The concrete frame of the round -/

/-- The environment frame the run reaches at the `+` round when `x` holds
    `INT_MAX` (the frames of EmittedCExhibit.lean at `n = INT_MAX`). -/
abbrev frBK (px : CerbMem.PointerValue) (f : Fmap sym value) : Fmap sym value :=
  envAdd b1SymC (lint intMaxC) (envAdd b2SymC (lint 1) (envAdd a2SymC (lint intMaxC)
    (envAdd pSymC (Vobject (OVpointer px)) (envAdd a1SymC (lint intMaxC) (frXC px f)))))

theorem frBK_symFrame {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    SymFrame (envAdd b2SymC (lint 1) (envAdd a2SymC (lint intMaxC)
      (envAdd pSymC (Vobject (OVpointer px)) (envAdd a1SymC (lint intMaxC) (frXC px f))))) :=
  (((((hf.add _ _).add _ _).add _ _).add _ _).add _ _)

theorem frBK_lookup_b1 {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK b1SymC (frBK px f) = some (lint intMaxC) := by
  unfold frBK
  rw [envAdd_lookup (frBK_symFrame hf px) symCmpK, if_pos (by decide +kernel)]

theorem frBK_lookup_b2 {f : Fmap sym value} (hf : SymFrame f) (px : CerbMem.PointerValue) :
    fmapLookupBy symCmpK b2SymC (frBK px f) = some (lint 1) := by
  unfold frBK
  rw [envAdd_lookup (frBK_symFrame hf px) symCmpK, if_neg (by decide +kernel),
    envAdd_lookup ((((hf.add _ _).add _ _).add _ _).add _ _) symCmpK, if_pos (by decide +kernel)]

/-- The symbol operand at a frame whose lookup is known, at an empty
    extern map (the production pipeline's). -/
theorem symK_eval [LemFuel] {tds : CerbTags.TagDefsMap} {file : generic_file Unit core_run_annotation}
    {x : sym} {f : Fmap sym value} {v : value} (evs : List (Fmap sym value))
    (hl : fmapLookupBy symCmpK x f = some v) :
    evalPexpr tds fmapEmpty file (f :: evs) (stdSym x) = some v := by
  exact symC_eval (M := { spikeCtx with tagDefs := tds, file := file })
    (resolveExtern_id_of_empty rfl) evs hl

/-- THE NEGATIVE EXHIBIT AT THE CONCRETE FRAME: the genuine driver, at
    every positive outer counter and ambient fuel at least eight, from
    a state whose thread is at the `+` round with the
    frame `frBK` (any allocation `px`, any symbol-keyed base frame) and the
    production extern map, is exactly the UB036 kill. -/
theorem overflow_driver2_killed_frame [LemFuel] (hfuel : 8 ≤ LemFuel.fuel) (fl : Nat) (dst : driver_state) (th : thread_state)
    (px : CerbMem.PointerValue) (ev0 : Fmap sym value) (evs : List (Fmap sym value))
    (hf : SymFrame ev0)
    (hth : dst.core_state0.thread_states = [(0, (none, th))])
    (hext : dst.core_extern = fmapEmpty)
    (harena : th.arena = progCE3_atAdd) (henv : th.env = frBK px ev0 :: evs) :
    ∃ dstK : driver_state,
      runOne (driver2_lemFuel (Nat.succ fl) fmapEmpty false) dst =
        (NDkilled (Undef0 th.current_loc [UB036_exceptional_condition]), dstK) :=
  overflow_driver2_killed (hfuel := hfuel) fl dst th hth harena
    (by rw [hext, henv]; exact symK_eval evs (frBK_lookup_b1 hf px))
    (by rw [hext, henv]; exact symK_eval evs (frBK_lookup_b2 hf px))

end CerberusHeapLang
