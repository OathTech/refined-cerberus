/-
CerberusHeapLang.EvenOddExhibit — MUTUAL RECURSION through the specification
table (hygiene slice H1b, 2026-09-04, docs/2026-09-04_h1-notes.md; the item
KNOWN-OPEN-ITEMS B8 / ARCHITECTURE §7 carried since the calls arc: "mutual
recursion — the rule admits it, `procSpecs` assumes the table for every
procedure — no exhibit").

THE PROGRAM (Core), three procedures on the synthetic file `prodFileWith`:

  proc odd  (n : integer) : eff integer := if n < 1 then pure(0) else even(n - 1)
  proc even (n : integer) : eff integer := if n < 1 then pure(1) else odd(n - 1)
  proc main () := even(n₀)

`even` calls `odd`, `odd` calls `even`: neither body is verifiable alone;
Hoare's rule for recursive procedures (`procSpecs_intro`/`procSpecsT_intro`)
verifies each body ONCE assuming the table for EVERY procedure — the table is
what makes the two bodies' proofs independent of each other. THE
SPECIFICATION IS SYMBOL-DEPENDENT for the first time (`eoSpec`, `eoSpecT`):
at every symbol `{⌜0 ≤ n⌝} ·(n) {ret. ⌜ret = ivVal (if symOrd g oddSym = .eq
then n % 2 else 1 - n % 2)⌝}` — 1 for even, 0 for odd, at `odd`; the
complement at every other symbol (`even`; `main`, arity 0, is unreachable
under it exactly as in FibRecExhibit). The total table adds the activation's
budget `3 * n + 2 ≤ m` (per activation: the guard round, then either the
value's delivery or the call round + the callee + the returned value's
delivery — three rounds beside the callee). `main` costs `3 * n + 4`.

The calls are at the ROOT of each body's else branch (`wps_call_root`/
`wpt_call_root`): the callee's returned value IS the caller's value. The
file's `funs` map is a THREE-entry `symAdd` chain (`main` over `odd` over
`even`), read by `symAdd_lookup` (its `SymMap` premise by `SymMap.add`) and
`symAdd_lookup_two`; the shipped registration on the file computes to three
EMPTY fibers (no `save` anywhere), so every derived label map is `fmapEmpty`.

WHAT IS EXPORTED: partial — `eoOddBody_wps`/`eoEvenBody_wps`,
`eoCtx_procSpecs`, `eoMain_wps`, `eo_wp_readout`, and THE CLOSED PARTIAL
FORM `even_odd_certified` (every `n ≥ 0`, every `drive_lemFuel` fuel:
exhaustion or `Active` delivering `1 - n % 2`); total — the `_wpt` twins,
`eoCtx_procSpecsT`, `eoMain_wpt`, and THE PRODUCTION STATEMENT
`even_odd_certified_production` (the shipped pipeline cold on the
three-procedure file, EXACTLY ONE Active execution delivering `1 - n % 2`,
in-budget bound `3 * n + 6 ≤ CerbFuel.driverFuel`) — the ninth closed
shipped-driver statement, the first over a THREE-procedure file and the first
whose PCALL/RETURN rounds alternate between two procedures. Both fall out of
the existing N-procedure entry (`prodFileWith`, `prod_run_eqJ_procs`,
`prod_run_safe_procs`) with no new machinery; every statement here is
trio-exact and pinned in Audit.lean.
-/
import CerberusHeapLang.API
import CerberusHeapLang.FibRecExhibit
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.ProdLoop

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open scoped Iris.Std.PartialMap
open Lem_Basic_classes Lem_Map Lem_Maybe Lem_List

/-! ## The program -/

/-- The procedure `even`. -/
def eoEvenSym : sym := Symbol "" 801 SD_None
/-- The procedure `odd`. -/
def eoOddSym : sym := Symbol "" 802 SD_None
/-- The parameter `n` (both procedures). -/
def eoNSym : sym := Symbol "" 803 SD_None

/-- The guard `n < 1`. -/
def eoGuard : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpLt (Pexpr [] () (PEsym eoNSym)) (Pexpr [] () (PEval (ivVal 1))))
/-- The argument `n - 1`. -/
def eoDec : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym eoNSym)) (Pexpr [] () (PEval (ivVal 1))))

/-- `even`'s body: `if n < 1 then pure(1) else odd(n - 1)`. -/
def eoEvenBody (ra : core_run_annotation) : CoreExpr :=
  Expr [] (Eif eoGuard (ofVal (.pure (ivVal 1))) (callRedex ra eoOddSym [eoDec]))

/-- `odd`'s body: `if n < 1 then pure(0) else even(n - 1)`. -/
def eoOddBody (ra : core_run_annotation) : CoreExpr :=
  Expr [] (Eif eoGuard (ofVal (.pure (ivVal 0))) (callRedex ra eoEvenSym [eoDec]))

/-- `main`: `even(n)`. -/
def eoMain (ra : core_run_annotation) (n : Int) : CoreExpr :=
  callRedex ra eoEvenSym [Pexpr [] () (PEval (ivVal n))]

/-- The declared procedures: `odd`, then `even` (the order fixes the `funs`
    chain: `main` over `odd` over `even`). -/
def eoProcs (ra : core_run_annotation) (nbty : core_base_type) :
    List (sym × List (sym × core_base_type) × CoreExpr) :=
  [(eoOddSym, [(eoNSym, nbty)], eoOddBody ra), (eoEvenSym, [(eoNSym, nbty)], eoEvenBody ra)]

section EoFile

variable (ra : core_run_annotation) (n : Int) (nbty : core_base_type)

/-- The synthetic three-procedure file. -/
abbrev eoFile : file core_run_annotation := prodFileWith (eoProcs ra nbty) (eoMain ra n)

/-! ### `call_proc`'s lookups on the file -/

theorem eoFile_funs :
    (eoFile ra n nbty).funs =
      symAdd mainSym (mainDecl (eoMain ra n))
        (symAdd eoOddSym (Proc CerbLocation.unknown none BTy_unit [(eoNSym, nbty)] (eoOddBody ra))
          (symAdd eoEvenSym (Proc CerbLocation.unknown none BTy_unit [(eoNSym, nbty)] (eoEvenBody ra))
            fmapEmpty)) := rfl

theorem eoFile_lookup_main :
    lookupProc (eoFile ra n nbty) fmapEmpty mainSym = some ([], eoMain ra n) :=
  prodFileWith_lookup_main _ _

theorem eoFile_lookup_odd :
    lookupProc (eoFile ra n nbty) fmapEmpty eoOddSym = some ([(eoNSym, nbty)], eoOddBody ra) := by
  unfold lookupProc
  rw [show fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) eoOddSym
      (eoFile ra n nbty).stdlib = none from rfl]
  rw [resolveExtern_id_of_empty rfl, eoFile_funs, symAdd_lookup ((symMap_empty.add _ _).add _ _),
    if_neg (by decide +kernel), symAdd_lookup_two, if_pos (by decide +kernel)]

theorem eoFile_lookup_even :
    lookupProc (eoFile ra n nbty) fmapEmpty eoEvenSym = some ([(eoNSym, nbty)], eoEvenBody ra) := by
  unfold lookupProc
  rw [show fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) eoEvenSym
      (eoFile ra n nbty).stdlib = none from rfl]
  rw [resolveExtern_id_of_empty rfl, eoFile_funs, symAdd_lookup ((symMap_empty.add _ _).add _ _),
    if_neg (by decide +kernel), symAdd_lookup_two, if_neg (by decide +kernel),
    if_pos (by decide +kernel)]

/-- Every procedure the file declares is `main`, `odd` or `even`, with the
    comparator verdicts that selected it (what the symbol-dependent
    specification reads). -/
theorem eoFile_lookup_inv {g : sym} {params : List (sym × core_base_type)} {body : CoreExpr}
    (h : lookupProc (eoFile ra n nbty) fmapEmpty g = some (params, body)) :
    (symOrd g mainSym = .eq ∧ params = [] ∧ body = eoMain ra n) ∨
    (symOrd g eoOddSym = .eq ∧ params = [(eoNSym, nbty)] ∧ body = eoOddBody ra) ∨
    (symOrd g eoOddSym ≠ .eq ∧ symOrd g eoEvenSym = .eq ∧ params = [(eoNSym, nbty)] ∧
      body = eoEvenBody ra) := by
  unfold lookupProc at h
  rw [show fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) g
      (eoFile ra n nbty).stdlib = none from rfl] at h
  rw [resolveExtern_id_of_empty rfl, eoFile_funs, symAdd_lookup ((symMap_empty.add _ _).add _ _),
    symAdd_lookup_two] at h
  by_cases h0 : symOrd g mainSym = .eq
  · rw [if_pos h0] at h
    obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
    exact .inl ⟨h0, hp.symm, hb.symm⟩
  · rw [if_neg h0] at h
    by_cases h1 : symOrd g eoOddSym = .eq
    · rw [if_pos h1] at h
      obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
      exact .inr (.inl ⟨h1, hp.symm, hb.symm⟩)
    · rw [if_neg h1] at h
      by_cases h2 : symOrd g eoEvenSym = .eq
      · rw [if_pos h2] at h
        obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
        exact .inr (.inr ⟨h1, h2, hp.symm, hb.symm⟩)
      · rw [if_neg h2] at h
        cases h

/-! ### The shipped registration, computed: three EMPTY fibers -/

theorem collect_saves_eoEven : collect_saves (eoEvenBody ra) = fmapEmpty := rfl
theorem collect_saves_eoOdd : collect_saves (eoOddBody ra) = fmapEmpty := rfl
theorem collect_saves_eoMain : collect_saves (eoMain ra n) = fmapEmpty := rfl

/-- THE REGISTRATION on the three-procedure file, COMPUTED (measured, not
    assumed: of the six insertion orders exactly this one is `rfl` — `main`
    innermost, then `odd`, `even` outermost; every fiber empty). -/
theorem collect_new_eo :
    collect_labeled_continuations_NEW (eoFile ra n nbty) =
      symAdd eoEvenSym fmapEmpty (symAdd eoOddSym fmapEmpty (symAdd mainSym fmapEmpty fmapEmpty)) :=
  rfl

/-- The production initial run state of the file. -/
abbrev eoRS (sup : Nat) : core_run_state := prodRS (eoProcs ra nbty) sup (eoMain ra n)

/-- THE PRODUCTION CONTEXT of the exhibit. -/
abbrev eoCtx (sup : Nat) : MachineCtx := prodCtx (eoFile ra n nbty) (eoRS ra n nbty sup)

/-- Every derived label fiber of the production context is EMPTY (no `save`
    in any body). -/
theorem eoCtx_labels (sup : Nat) (g : sym) :
    (eoCtx ra n nbty sup).labelsAt (some g) = fmapEmpty := by
  rw [MachineCtx.labelsAt_some, MachineCtx.resolveProc_of_extern_empty rfl]
  show (match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) g
      (eoRS ra n nbty sup).labeled with
    | some Q => Q
    | none => fmapEmpty) = fmapEmpty
  rw [prodRS_labeled, collect_new_eo, symAdd_lookup ((symMap_empty.add _ _).add _ _),
    symAdd_lookup_two]
  by_cases h2 : symOrd g eoEvenSym = .eq
  · rw [if_pos h2]
  · rw [if_neg h2]
    by_cases h1 : symOrd g eoOddSym = .eq
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h0 : symOrd g mainSym = .eq
      · rw [if_pos h0]
      · rw [if_neg h0]

/-- THE WHOLE-FILE REGISTRATION TIE at the production initial run state. -/
theorem eoCtx_labeledProcs (sup : Nat) :
    LabeledProcs (eoCtx ra n nbty sup) (eoRS ra n nbty sup).labeled := by
  refine LabeledProcs.of_fibers rfl (fun g params body hg => ?_)
  show ∃ Q, fmapLookupBy _ g (eoRS ra n nbty sup).labeled = some Q
  rw [prodRS_labeled, collect_new_eo, symAdd_lookup ((symMap_empty.add _ _).add _ _),
    symAdd_lookup_two]
  by_cases h2 : symOrd g eoEvenSym = .eq
  · rw [if_pos h2]
    exact ⟨_, rfl⟩
  · rw [if_neg h2]
    by_cases h1 : symOrd g eoOddSym = .eq
    · rw [if_pos h1]
      exact ⟨_, rfl⟩
    · rw [if_neg h1]
      rcases eoFile_lookup_inv ra n nbty hg with ⟨h0, -, -⟩ | ⟨h1', -, -⟩ | ⟨-, h2', -, -⟩
      · rw [if_pos h0]
        exact ⟨_, rfl⟩
      · exact (h1 h1').elim
      · exact (h2 h2').elim

/-! ### The fragment membership and the procedure well-formedness premise -/

theorem eoDec_pure : ∀ pe ∈ [eoDec], PePure pe := fun pe hpe => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  subst hpe
  exact PePure.of_isPePure rfl

theorem eoDec_depth : ∀ pe ∈ [eoDec], peDepth pe ≤ lemDefaultFuel := fun pe hpe => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  subst hpe
  rw [show peDepth eoDec = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
  omega

theorem eoEvenBody_frag : Frag (eoEvenBody ra) :=
  .if_ (PePure.of_isPePure rfl)
    (by rw [show peDepth eoGuard = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (.val_pure _) (.call eoDec_pure eoDec_depth)

theorem eoOddBody_frag : Frag (eoOddBody ra) :=
  .if_ (PePure.of_isPePure rfl)
    (by rw [show peDepth eoGuard = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (.val_pure _) (.call eoDec_pure eoDec_depth)

theorem eoMain_frag : Frag (eoMain ra n) :=
  .call (fun pe hpe => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      subst hpe
      exact .val _ _)
    (fun pe hpe => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      subst hpe
      rw [show peDepth (Pexpr [] () (PEval (ivVal n))) = 1 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]
      omega)

theorem eoEvenBody_pot : pot (eoEvenBody ra) = 3 := rfl
theorem eoOddBody_pot : pot (eoOddBody ra) = 3 := rfl
theorem eoMain_pot : pot (eoMain ra n) = 2 := rfl

/-- THE PROCEDURE WELL-FORMEDNESS PREMISE at the production context: the
    three bodies in the cone within the potential bound; every fiber empty. -/
theorem eoCtx_fragProcs (sup : Nat) : (eoCtx ra n nbty sup).FragProcs where
  body g params body hg := by
    rcases eoFile_lookup_inv ra n nbty hg with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · exact eoMain_frag ra n
    · exact eoOddBody_frag ra
    · exact eoEvenBody_frag ra
  potBound g params body hg := by
    rcases eoFile_lookup_inv ra n nbty hg with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩
    · rw [eoMain_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega
    · rw [eoOddBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega
    · rw [eoEvenBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega
  labels g params body _ l params' cont hl := by
    rw [eoCtx_labels, show lookupLabel fmapEmpty l = none from rfl] at hl
    cases hl

end EoFile

/-! ## Frames and evaluation facts -/

/-- The parameter frame `n ↦ n`. -/
abbrev eoF0 (n : Int) : Fmap sym value := envAdd eoNSym (ivVal n) fmapEmpty

theorem eoF0_lookup_n (n : Int) : fmapLookupBy symCmpK eoNSym (eoF0 n) = some (ivVal n) := by
  rw [envAdd_lookup symFrame_empty, if_pos (by decide +kernel)]

theorem eoN_eval (n : Int) (ρ : EnvStack) :
    evalPexpr fmapEmpty fmapEmpty (eoF0 n :: ρ) (Pexpr [] () (PEsym eoNSym)) = some (ivVal n) := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (eoF0_lookup_n n) ρ

theorem eoGuard_eval (n : Int) (ρ : EnvStack) :
    evalPexpr fmapEmpty fmapEmpty (eoF0 n :: ρ) eoGuard = some (boolValue (decide (n < 1))) := by
  unfold eoGuard
  rw [evalPexpr_op, eoN_eval]
  rfl

theorem eoDec_eval (n : Int) (ρ : EnvStack) :
    evalPexprs fmapEmpty fmapEmpty (eoF0 n :: ρ) [eoDec] = some [ivVal (n - 1)] := by
  rw [evalPexprs_cons]
  unfold eoDec
  rw [evalPexpr_op, eoN_eval]
  rfl

/-- The recursive case's values: `odd (n - 1)` is `even n`, `even (n - 1)` is
    `odd n`, at `n ≥ 1`. -/
theorem eo_parity_even {n : Int} (h : 1 ≤ n) : ivVal ((n - 1) % 2) = ivVal (1 - n % 2) := by
  rw [show (n - 1) % 2 = 1 - n % 2 by omega]

theorem eo_parity_odd {n : Int} (h : 1 ≤ n) : ivVal (1 - (n - 1) % 2) = ivVal (n % 2) := by
  rw [show 1 - (n - 1) % 2 = n % 2 by omega]

/-! ## THE SPECIFICATION TABLES -/

section EoIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (ra : core_run_annotation) (n : Int) (nbty : core_base_type) (sup : Nat)

/-- THE TABLE (partial), SYMBOL-DEPENDENT: `{⌜0 ≤ n⌝} ·(n) {ret. ⌜ret = n % 2⌝}`
    at `odd`, `{⌜0 ≤ n⌝} ·(n) {ret. ⌜ret = 1 - n % 2⌝}` at every other symbol
    (`even`; `main`, arity 0, is unreachable under it). -/
def eoSpec : ProcSpec GF := fun g vs =>
  (iprop(⌜∃ n : Int, vs = [ivVal n] ∧ 0 ≤ n⌝),
   fun ret => iprop(⌜∃ n : Int, vs = [ivVal n] ∧
     ret = ivVal (if symOrd g eoOddSym = .eq then n % 2 else 1 - n % 2)⌝))

/-- THE TOTAL TABLE: the same, with the activation's budget `3 * n + 2 ≤ m`. -/
def eoSpecT : ProcSpecT GF := fun g m vs =>
  (iprop(⌜∃ n : Int, vs = [ivVal n] ∧ 0 ≤ n ∧ 3 * n.toNat + 2 ≤ m⌝),
   fun ret => iprop(⌜∃ n : Int, vs = [ivVal n] ∧
     ret = ivVal (if symOrd g eoOddSym = .eq then n % 2 else 1 - n % 2)⌝))

/-- No label is jumped to. -/
def eoLs : LabelSpec GF := fun _ _ _ => iprop(⌜False⌝)
def eoLsT : LabelSpecT GF := fun _ _ _ _ => iprop(⌜False⌝)

/-- `main`'s postcondition: the delivered value is `1 - n % 2` (1 iff even). -/
def eoPost : SpikeVal → EnvStack → IProp GF := fun w _ => iprop(⌜w.val = ivVal (1 - n % 2)⌝)

/-- THE BODY OF `even` UNDER THE TABLE (partial), at a symbol `g` the table
    reads as `even` (`symOrd g oddSym ≠ .eq`), once, at every caller tail:
    the guard; at the base case the value `1`; otherwise the call `odd(n-1)`
    at the ROOT against the table (Hoare's rule: the table is ASSUMED for
    `odd`'s activation — the mutual knot is tied by `procSpecs_intro`). -/
theorem eoEvenBody_wps (g : sym) (hodd : symOrd g eoOddSym ≠ .eq) (vs : List value)
    (ρ : EnvStack) :
    (eoSpec (GF := GF) g vs).1 ⊢
      wps (GF := GF) (eoCtx ra n nbty sup) (some g) eoLs eoSpec
        (fun w _ => (eoSpec g vs).2 w.val) (eoEvenBody ra) (procEnv [(eoNSym, nbty)] vs :: ρ) := by
  dsimp only [eoSpec]
  iintro %hpre
  obtain ⟨n', rfl, hn'⟩ := hpre
  rw [procEnv_single]
  unfold eoEvenBody
  by_cases hlt : n' < 1
  · -- THE BASE CASE: n' = 0, the value 1
    iapply wps_if_true [] eoGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ eoGuard = _
          rw [eoGuard_eval, decide_eq_true hlt]; rfl)
    iapply wps_ofVal (.pure (ivVal 1))
    ipureintro
    refine ⟨n', rfl, ?_⟩
    rw [if_neg hodd]
    obtain rfl : n' = 0 := by omega
    rfl
  · -- THE RECURSIVE CASE: odd(n' - 1)
    iapply wps_if_false [] eoGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ eoGuard = _
          rw [eoGuard_eval, decide_eq_false hlt]; rfl)
    unfold callRedex
    iapply wps_call_root [] ra eoOddSym [eoDec] (eoF0 n' :: ρ) (vs := [ivVal (n' - 1)])
      (eoFile_lookup_odd ra n nbty) rfl (eoDec_eval n' ρ)
    dsimp only [eoSpec]
    isplitl []
    · ipureintro
      exact ⟨n' - 1, rfl, by omega⟩
    · iintro %ret %hpost
      obtain ⟨m1, hm1, hret⟩ := hpost
      obtain rfl : m1 = n' - 1 := (ivVal_inj (List.cons.inj hm1).1).symm
      rw [if_pos (by decide +kernel)] at hret
      subst hret
      rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal ((n' - 1) % 2))))) =
        ofVal (.pure (ivVal ((n' - 1) % 2))) from rfl]
      iapply wps_ofVal
      ipureintro
      refine ⟨n', rfl, ?_⟩
      rw [if_neg hodd]
      exact eo_parity_even (by omega)

/-- THE BODY OF `odd` UNDER THE TABLE (partial), at a symbol the table reads
    as `odd`: the base value `0`; otherwise `even(n - 1)`. -/
theorem eoOddBody_wps (g : sym) (hodd : symOrd g eoOddSym = .eq) (vs : List value)
    (ρ : EnvStack) :
    (eoSpec (GF := GF) g vs).1 ⊢
      wps (GF := GF) (eoCtx ra n nbty sup) (some g) eoLs eoSpec
        (fun w _ => (eoSpec g vs).2 w.val) (eoOddBody ra) (procEnv [(eoNSym, nbty)] vs :: ρ) := by
  dsimp only [eoSpec]
  iintro %hpre
  obtain ⟨n', rfl, hn'⟩ := hpre
  rw [procEnv_single]
  unfold eoOddBody
  by_cases hlt : n' < 1
  · iapply wps_if_true [] eoGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ eoGuard = _
          rw [eoGuard_eval, decide_eq_true hlt]; rfl)
    iapply wps_ofVal (.pure (ivVal 0))
    ipureintro
    refine ⟨n', rfl, ?_⟩
    rw [if_pos hodd]
    obtain rfl : n' = 0 := by omega
    rfl
  · iapply wps_if_false [] eoGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ eoGuard = _
          rw [eoGuard_eval, decide_eq_false hlt]; rfl)
    unfold callRedex
    iapply wps_call_root [] ra eoEvenSym [eoDec] (eoF0 n' :: ρ) (vs := [ivVal (n' - 1)])
      (eoFile_lookup_even ra n nbty) rfl (eoDec_eval n' ρ)
    dsimp only [eoSpec]
    isplitl []
    · ipureintro
      exact ⟨n' - 1, rfl, by omega⟩
    · iintro %ret %hpost
      obtain ⟨m1, hm1, hret⟩ := hpost
      obtain rfl : m1 = n' - 1 := (ivVal_inj (List.cons.inj hm1).1).symm
      rw [if_neg (by decide +kernel)] at hret
      subst hret
      rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (1 - (n' - 1) % 2))))) =
        ofVal (.pure (ivVal (1 - (n' - 1) % 2))) from rfl]
      iapply wps_ofVal
      ipureintro
      refine ⟨n', rfl, ?_⟩
      rw [if_pos hodd]
      exact eo_parity_odd (by omega)

/-- THE PROCEDURE SPECIFICATIONS HOLD (partial): each body once, under the
    table for BOTH; `main` is unreachable under the table (arity). -/
theorem eoCtx_procSpecs : ⊢ procSpecs (GF := GF) (eoCtx ra n nbty sup) eoSpec := by
  refine procSpecs_intro (fun _ _ => eoLs) ?_ ?_
  · intro f params body vs hf hlen
    refine blockSpecs_intro fun l params' cont vs' ev0 evs hl => ?_
    dsimp only [eoLs]
    iintro %hF
    exact hF.elim
  · intro f params body vs ρ hf hlen
    rcases eoFile_lookup_inv ra n nbty hf with ⟨-, rfl, rfl⟩ | ⟨hodd, rfl, rfl⟩ | ⟨hnodd, -, rfl, rfl⟩
    · dsimp only [eoSpec]
      iintro %hpre
      obtain ⟨x, hx, -⟩ := hpre
      subst hx
      cases hlen
    · exact eoOddBody_wps ra n nbty sup f hodd vs ρ
    · exact eoEvenBody_wps ra n nbty sup f hnodd vs ρ

/-- `main`'s (empty) block specifications. -/
theorem eo_blockSpecs :
    ⊢ blockSpecs (GF := GF) (eoCtx ra n nbty sup) (some mainSym) eoLs eoSpec (eoPost n) := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  dsimp only [eoLs]
  iintro %hF
  exact hF.elim

/-- `main` under the table: the call rule alone. -/
theorem eoMain_wps (hn : 0 ≤ n) (ρ : EnvStack) :
    ⊢ wps (GF := GF) (eoCtx ra n nbty sup) (some mainSym) eoLs eoSpec (eoPost n) (eoMain ra n) ρ := by
  unfold eoMain callRedex
  iapply wps_call_root [] ra eoEvenSym [Pexpr [] () (PEval (ivVal n))] ρ (vs := [ivVal n])
    (eoFile_lookup_even ra n nbty) rfl rfl
  dsimp only [eoSpec]
  isplitl []
  · ipureintro
    exact ⟨n, rfl, hn⟩
  · iintro %ret %hpost
    obtain ⟨m, hm, hret⟩ := hpost
    obtain rfl : n = m := ivVal_inj (List.cons.inj hm).1
    rw [if_neg (by decide +kernel)] at hret
    subst hret
    rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (1 - n % 2))))) =
      ofVal (.pure (ivVal (1 - n % 2))) from rfl]
    iapply wps_ofVal
    dsimp only [eoPost]
    ipureintro
    rfl

/-- The base-WP face with the engine readout: `wps_sound` WITH the table at
    the production entry control. -/
theorem eo_wp_readout (hn : 0 ≤ n) (ℓ : exec_location) :
    ⊢ WP (⟨eoMain ra n, [fmapEmpty], ⟨[], some mainSym, ℓ⟩, eoCtx ra n nbty sup⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CoreRVal.val w = ivVal (1 - n % 2)⌝) }} := by
  refine (eoMain_wps ra n nbty sup hn [fmapEmpty]).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((BI.emp_sep.2.trans (BI.sep_mono (eoCtx_procSpecs ra n nbty sup)
      (eo_blockSpecs ra n nbty sup))).trans
      (wps_sound (ctl := ⟨[], some mainSym, ℓ⟩) rfl (eoMain ra n) [fmapEmpty])) .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  exact wp_mono fun w => stateInterp_readout fun _ _ _ _ _ => pure_consequence _

/-! ### The total twins -/

/-- THE BODY OF `even` WITHIN ITS BUDGET `3 * n + 2`: the guard, then either
    the value's delivery (base: `1 + 1`) or the call round, the callee's
    `3 * (n - 1) + 2` and the returned value's delivery. -/
theorem eoEvenBody_wpt (g : sym) (hodd : symOrd g eoOddSym ≠ .eq) (m : Nat) (vs : List value)
    (ρ : EnvStack) :
    (eoSpecT (GF := GF) g m vs).1 ⊢
      wpt (GF := GF) (eoCtx ra n nbty sup) (some g) eoLsT eoSpecT m
        (fun w _ => (eoSpecT g m vs).2 w.val) (eoEvenBody ra) (procEnv [(eoNSym, nbty)] vs :: ρ) := by
  dsimp only [eoSpecT]
  iintro %hpre
  obtain ⟨n', rfl, hn', hm⟩ := hpre
  iapply wpt_mono_k (k := 3 * n'.toNat + 2) hm
  rw [procEnv_single]
  unfold eoEvenBody
  by_cases hlt : n' < 1
  · rw [show 3 * n'.toNat + 2 = 1 + 1 by omega]
    iapply wpt_if_true [] eoGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ eoGuard = _
          rw [eoGuard_eval, decide_eq_true hlt]; rfl)
    iapply wpt_ofVal (.pure (ivVal 1)) _ (Nat.le_refl 1)
    ipureintro
    refine ⟨n', rfl, ?_⟩
    rw [if_neg hodd]
    obtain rfl : n' = 0 := by omega
    rfl
  · rw [show 3 * n'.toNat + 2 = ((3 * (n' - 1).toNat + 2) + 2) + 1 by omega]
    iapply wpt_if_false [] eoGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ eoGuard = _
          rw [eoGuard_eval, decide_eq_false hlt]; rfl)
    unfold callRedex
    iapply wpt_call_root [] ra eoOddSym [eoDec] (eoF0 n' :: ρ) (vs := [ivVal (n' - 1)])
      (m := 3 * (n' - 1).toNat + 2) (k' := 1) (k := (3 * (n' - 1).toNat + 2) + 2)
      (eoFile_lookup_odd ra n nbty) rfl (eoDec_eval n' ρ) (by omega)
    dsimp only [eoSpecT]
    isplitl []
    · ipureintro
      exact ⟨n' - 1, rfl, by omega, Nat.le_refl _⟩
    · iintro %ret %hpost
      obtain ⟨m1, hm1, hret⟩ := hpost
      obtain rfl : m1 = n' - 1 := (ivVal_inj (List.cons.inj hm1).1).symm
      rw [if_pos (by decide +kernel)] at hret
      subst hret
      rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal ((n' - 1) % 2))))) =
        ofVal (.pure (ivVal ((n' - 1) % 2))) from rfl]
      iapply wpt_ofVal _ _ (Nat.le_refl 1)
      ipureintro
      refine ⟨n', rfl, ?_⟩
      rw [if_neg hodd]
      exact eo_parity_even (by omega)

/-- THE BODY OF `odd` WITHIN ITS BUDGET `3 * n + 2`. -/
theorem eoOddBody_wpt (g : sym) (hodd : symOrd g eoOddSym = .eq) (m : Nat) (vs : List value)
    (ρ : EnvStack) :
    (eoSpecT (GF := GF) g m vs).1 ⊢
      wpt (GF := GF) (eoCtx ra n nbty sup) (some g) eoLsT eoSpecT m
        (fun w _ => (eoSpecT g m vs).2 w.val) (eoOddBody ra) (procEnv [(eoNSym, nbty)] vs :: ρ) := by
  dsimp only [eoSpecT]
  iintro %hpre
  obtain ⟨n', rfl, hn', hm⟩ := hpre
  iapply wpt_mono_k (k := 3 * n'.toNat + 2) hm
  rw [procEnv_single]
  unfold eoOddBody
  by_cases hlt : n' < 1
  · rw [show 3 * n'.toNat + 2 = 1 + 1 by omega]
    iapply wpt_if_true [] eoGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ eoGuard = _
          rw [eoGuard_eval, decide_eq_true hlt]; rfl)
    iapply wpt_ofVal (.pure (ivVal 0)) _ (Nat.le_refl 1)
    ipureintro
    refine ⟨n', rfl, ?_⟩
    rw [if_pos hodd]
    obtain rfl : n' = 0 := by omega
    rfl
  · rw [show 3 * n'.toNat + 2 = ((3 * (n' - 1).toNat + 2) + 2) + 1 by omega]
    iapply wpt_if_false [] eoGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ eoGuard = _
          rw [eoGuard_eval, decide_eq_false hlt]; rfl)
    unfold callRedex
    iapply wpt_call_root [] ra eoEvenSym [eoDec] (eoF0 n' :: ρ) (vs := [ivVal (n' - 1)])
      (m := 3 * (n' - 1).toNat + 2) (k' := 1) (k := (3 * (n' - 1).toNat + 2) + 2)
      (eoFile_lookup_even ra n nbty) rfl (eoDec_eval n' ρ) (by omega)
    dsimp only [eoSpecT]
    isplitl []
    · ipureintro
      exact ⟨n' - 1, rfl, by omega, Nat.le_refl _⟩
    · iintro %ret %hpost
      obtain ⟨m1, hm1, hret⟩ := hpost
      obtain rfl : m1 = n' - 1 := (ivVal_inj (List.cons.inj hm1).1).symm
      rw [if_neg (by decide +kernel)] at hret
      subst hret
      rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (1 - (n' - 1) % 2))))) =
        ofVal (.pure (ivVal (1 - (n' - 1) % 2))) from rfl]
      iapply wpt_ofVal _ _ (Nat.le_refl 1)
      ipureintro
      refine ⟨n', rfl, ?_⟩
      rw [if_pos hodd]
      exact eo_parity_odd (by omega)

theorem eoCtx_procSpecsT : ⊢ procSpecsT (GF := GF) (eoCtx ra n nbty sup) eoSpecT := by
  refine procSpecsT_intro (fun _ _ _ => eoLsT) ?_ ?_
  · intro f params body m vs hf hlen
    refine blockSpecsT_intro fun l params' cont vs' ev0 evs m' hl => ?_
    dsimp only [eoLsT]
    iintro %hF
    exact hF.elim
  · intro f params body m vs ρ hf hlen
    rcases eoFile_lookup_inv ra n nbty hf with ⟨-, rfl, rfl⟩ | ⟨hodd, rfl, rfl⟩ | ⟨hnodd, -, rfl, rfl⟩
    · dsimp only [eoSpecT]
      iintro %hpre
      obtain ⟨x, hx, -⟩ := hpre
      subst hx
      cases hlen
    · exact eoOddBody_wpt ra n nbty sup f hodd m vs ρ
    · exact eoEvenBody_wpt ra n nbty sup f hnodd m vs ρ

theorem eo_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (eoCtx ra n nbty sup) (some mainSym) eoLsT eoSpecT (eoPost n) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  dsimp only [eoLsT]
  iintro %hF
  exact hF.elim

/-- `main` within budget `3 * n + 4`: the call round, the callee's
    `3 * n + 2`, the delivery of the returned value. -/
theorem eoMain_wpt (hn : 0 ≤ n) (ρ : EnvStack) :
    ⊢ wpt (GF := GF) (eoCtx ra n nbty sup) (some mainSym) eoLsT eoSpecT (3 * n.toNat + 4)
      (eoPost n) (eoMain ra n) ρ := by
  unfold eoMain callRedex
  iapply wpt_call_root [] ra eoEvenSym [Pexpr [] () (PEval (ivVal n))] ρ (vs := [ivVal n])
    (m := 3 * n.toNat + 2) (k' := 1) (k := 3 * n.toNat + 4)
    (eoFile_lookup_even ra n nbty) rfl rfl (by omega)
  dsimp only [eoSpecT]
  isplitl []
  · ipureintro
    exact ⟨n, rfl, hn, Nat.le_refl _⟩
  · iintro %ret %hpost
    obtain ⟨m, hm, hret⟩ := hpost
    obtain rfl : n = m := ivVal_inj (List.cons.inj hm).1
    rw [if_neg (by decide +kernel)] at hret
    subst hret
    rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (1 - n % 2))))) =
      ofVal (.pure (ivVal (1 - n % 2))) from rfl]
    iapply wpt_ofVal _ _ (Nat.le_refl 1)
    dsimp only [eoPost]
    ipureintro
    rfl

/-- The postcondition entails the engine readout. -/
theorem eoPost_to_readout :
    ∀ w ρ', eoPost (GF := GF) n w ρ' ⊢ readoutPost (fun v _ => v = ivVal (1 - n % 2)) w ρ' :=
  fun _ _ => stateInterp_readout fun _ _ _ _ _ => pure_consequence _

end EoIris

/-! ## The two engine statements -/

section EoEngine

variable (sup : Nat) (ra : core_run_annotation) (n : Int) (nbty : core_base_type)

/-- MUTUAL RECURSION, PARTIAL FORM ON THE SHIPPED PIPELINE: for EVERY `n ≥ 0`
    and every `fuel`, the production pipeline `CerbND.drive_lemFuel fuel` cold
    on the synthetic THREE-procedure file is EXACTLY ONE execution, either
    the fuel-exhaustion kill or an Active execution delivering `1 - n % 2`.
    `engine_adequacy` with `FragProcs` at the production context, then
    `prod_run_safe_procs`. -/
theorem even_odd_certified (hn : 0 ≤ n) (fs : CerbFS.FsState) (args : List String) (fuel : Nat) :
    ∃ (st : nd_status driver_result driver_error driver_state) (dst' : driver_state),
      CerbND.runND
          (CerbND.drive_lemFuel fuel fmapEmpty false
            (prodFileWith (eoProcs ra nbty) (eoMain ra n)) args)
          ((initial_driver_state sup (prodFileWith (eoProcs ra nbty) (eoMain ra n)) fs).1) =
        [(st, ([] : List String), dst')] ∧
      (st = nd_status.Killed dst' CerbND.fuelExhaustedKill ∨
       ∃ dres : driver_result, st = nd_status.Active dres ∧
         dres.dres_core_value = ivVal (1 - n % 2) ∧
         dres.dres_blocked = false ∧
         dres.dres_stdout = "" ∧
         dres.dres_stderr = "") := by
  have hsafe : DriverSafeCtl (eoCtx ra n nbty sup) (prodThread (eoMain ra n))
      (eoMain ra n) [fmapEmpty] prodCtl prodMem₀ (fun v _ => v = ivVal (1 - n % 2)) := by
    refine engine_adequacy (GF := SpikeGF) (M := eoCtx ra n nbty sup) rfl rfl
      (ctl := prodCtl) rfl
      (fun l params cont hl => by
        rw [show prodCtl.proc = some mainSym from rfl, eoCtx_labels,
          show lookupLabel fmapEmpty l = none from rfl] at hl
        cases hl)
      (fun l params cont hl => by
        rw [show prodCtl.proc = some mainSym from rfl, eoCtx_labels,
          show lookupLabel fmapEmpty l = none from rfl] at hl
        cases hl)
      (eoCtx_fragProcs ra n nbty sup)
      (eoMain ra n) fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell)
      (eoMain_frag ra n)
      (by rw [eoMain_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (coh_empty prodMem₀)
      (fun v _ => v = ivVal (1 - n % 2))
      ?_ (th₀ := prodThread (eoMain ra n)) rfl
    intro inst
    exact (BigSepM.bigSepM_empty).1.trans (eo_wp_readout ra n nbty sup hn _)
  obtain ⟨st, dst', heq, hor⟩ := prod_run_safe_procs sup (eoProcs ra nbty) (eoMain ra n)
    (eoCtx_labeledProcs ra n nbty sup) _ hsafe fs args fuel
  exact ⟨st, dst', heq, hor⟩

/-- MUTUAL RECURSION, PRODUCTION FORM — THE NINTH CLOSED SHIPPED-DRIVER
    STATEMENT: running the SHIPPED pipeline cold on the synthetic
    THREE-procedure file (`main` calling `even`, `even` and `odd` calling each
    other down to 0) is EXACTLY ONE Active execution delivering `1 - n % 2`
    (1 iff `n` is even), for every `n ≥ 0` whose certified round count fits
    the shipped driver's own budget (`3 * n + 6 ≤ CerbFuel.driverFuel`). The
    label map the driver reads is what the shipped registration computes on
    the three procedures (three empty fibers); every PCALL and RETURN round
    of the run is the driver's own (`loop_step_frag`), alternating between
    the two procedures; termination from the total judgment. -/
theorem even_odd_certified_production (hn : 0 ≤ n)
    (hfuel : 3 * n.toNat + 6 ≤ CerbFuel.driverFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false (prodFileWith (eoProcs ra nbty) (eoMain ra n)) args)
          ((initial_driver_state sup (prodFileWith (eoProcs ra nbty) (eoMain ra n)) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = ivVal (1 - n % 2) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have h := prod_run_eqJ_procs sup (eoProcs ra nbty) (eoMain ra n)
    (eoCtx_labeledProcs ra n nbty sup)
    (fun v _ => v = ivVal (1 - n % 2)) (3 * n.toNat + 4)
    (wpt_driver_done_procs (GF := SpikeGF) (M₀ := eoCtx ra n nbty sup) rfl rfl
      (eoCtx_fragProcs ra n nbty sup)
      (th₀ := prodThread (eoMain ra n)) rfl
      (eoFile_lookup_main ra n nbty) prodCtl.execLoc
      eoSpecT eoLsT
      (eoMain ra n) fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell) 0
      (eoMain_frag ra n)
      (by rw [eoMain_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (prodMem₀_launchCoh 0 (Nat.zero_le _))
      (fun v _ => v = ivVal (1 - n % 2)) (3 * n.toNat + 4)
      (by
        intro inst
        iintro ⟨-, -⟩
        isplitl []
        · iapply eoCtx_procSpecsT ra n nbty sup
        isplitl []
        · iapply (eo_blockSpecsT ra n nbty sup).trans (blockSpecsT_mono (eoPost_to_readout n))
          itrivial
        · iapply (eoMain_wpt ra n nbty sup hn [fmapEmpty]).trans
            (wpt_mono (eoPost_to_readout n) _ _ _)
          itrivial))
    (by omega) fs args
  exact h

end EoEngine

end CerberusHeapLang
