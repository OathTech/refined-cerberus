/-
CerberusHeapLang.FibRecExhibit — RECURSIVE FIB (calls arc C4): a
procedure calling itself, verified through the SPECIFICATION TABLE
(Hoare's rule for recursive procedures: the body assumes the table,
`procSpecs_intro`/`procSpecsT_intro` — no Löb in the client), driven
through the PROVISIONAL `driveU` lane (`fib_rec_certified`) and, THE
FLAGSHIP, through the SHIPPED PIPELINE from the cold start
(`fib_rec_certified_production`): the eighth root-of-trust statement,
the first over a MULTI-PROCEDURE file, the first whose run makes the
driver's PCALL and RETURN rounds.

THE PROGRAM (Core):

  proc fib (n : integer) : eff integer :=
    if n < 2 then pure(n)
    else lets x = fib(n - 1) in lets y = fib(n - 2) in
         save r(z := x + y) in pure(z)
  proc main () := fib(n₀)

`lets x = fib(…) in …` binds a call's result at the plain-symbol binder
(`Frag.sseq_sym` with `BareHead.call`, C4: the RETURN plugs a BARE value);
`x + y` is computed by the fragment's binder for pure computation, a
`save` at an evaluated initializer (`Frag.save`, as the C3 smoke) — its
label `r` is registered in `fib`'s fiber by the shipped registration and
never jumped to. THE SPECIFICATION, as the table entry at every symbol:
`{⌜0 ≤ n⌝} fib(n) {ret. ⌜ret = fib n⌝}` (`frSpec`); the total table
`frSpecT` adds the callee's budget `fibRounds n ≤ m`, with

  fibRounds 0 = fibRounds 1 = 3
  fibRounds (n+2) = fibRounds (n+1) + fibRounds n + 9

— per activation: the guard round (1); at the base case PURE + delivery
(2); at the recursive case the two calls (each 1 + callee + 1, the bare
returned value's delivery paying the binder's beta), the SAVE (2: its
EVAL and TAU rounds) and PURE + delivery (2) — nine rounds beside the
callees. `main` costs `fibRounds n + 2` (call + callee + the delivery of
the returned value at the empty stack), and the production statement's
in-budget bound is `fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel`
(`prod_run_eqJ_procs`'s `k + 2`); `fibRounds n + 9 = 12 · fib (n + 1)`
(`fibRounds_closed`), so `n ≤ 33` is in the shipped budget `10^8`.

`main` is unreachable under the table (arity 0 against a one-argument
precondition), exactly as in the smoke. Every statement here is
trio-exact and pinned in Audit.lean.
-/
import CerberusHeapLang.API
import CerberusHeapLang.FibExhibit
import CerberusHeapLang.ProdEntry
import CerberusHeapLang.ProdLoop

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open scoped Iris.Std.PartialMap
open Lem_Basic_classes Lem_Map Lem_Maybe Lem_List

/-! ## The program -/

/-- The procedure `fib`. -/
def frSym : sym := Symbol "" 701 SD_None
/-- Its parameter `n`. -/
def frNSym : sym := Symbol "" 702 SD_None
/-- `x = fib(n - 1)`. -/
def frXSym : sym := Symbol "" 703 SD_None
/-- `y = fib(n - 2)`. -/
def frYSym : sym := Symbol "" 704 SD_None
/-- The `save` label (never jumped to). -/
def frRSym : sym := Symbol "" 705 SD_None
/-- The `save`-bound sum `z = x + y`. -/
def frZSym : sym := Symbol "" 706 SD_None

theorem ivVal_inj {i j : Int} (h : ivVal i = ivVal j) : i = j := by
  unfold ivVal CerbMem.integerIval at h
  cases h
  rfl

/-- The guard `n < 2`. -/
def frGuard : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpLt (Pexpr [] () (PEsym frNSym)) (Pexpr [] () (PEval (ivVal 2))))
/-- The argument `n - 1`. -/
def frDec1 : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym frNSym)) (Pexpr [] () (PEval (ivVal 1))))
/-- The argument `n - 2`. -/
def frDec2 : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpSub (Pexpr [] () (PEsym frNSym)) (Pexpr [] () (PEval (ivVal 2))))
/-- The sum `x + y`. -/
def frSumPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpAdd (Pexpr [] () (PEsym frXSym)) (Pexpr [] () (PEsym frYSym)))

/-- `save r(z := x + y) in pure(z)`. -/
def frSum (sbty zbty : core_base_type) : CoreExpr :=
  saveRedex (frRSym, sbty) [(frZSym, ((zbty, none), frSumPe))]
    (pureRedex (Pexpr [] () (PEsym frZSym)))

/-- `lets y = fib(n - 2) in save …`. -/
def frInner (ra : core_run_annotation) (ybty sbty zbty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (symPat [] frYSym ybty) (callRedex ra frSym [frDec2]) (frSum sbty zbty))

/-- `lets x = fib(n - 1) in lets y = …`. -/
def frOuter (ra : core_run_annotation) (xbty ybty sbty zbty : core_base_type) : CoreExpr :=
  Expr [] (Esseq (symPat [] frXSym xbty) (callRedex ra frSym [frDec1]) (frInner ra ybty sbty zbty))

/-- THE BODY: `if n < 2 then pure(n) else lets x = fib(n - 1) in lets y =
    fib(n - 2) in save r(z := x + y) in pure(z)`. -/
def frBody (ra : core_run_annotation) (xbty ybty sbty zbty : core_base_type) : CoreExpr :=
  Expr [] (Eif frGuard (pureRedex (Pexpr [] () (PEsym frNSym))) (frOuter ra xbty ybty sbty zbty))

/-- `main`: `fib(n)`. -/
def frMain (ra : core_run_annotation) (n : Int) : CoreExpr :=
  callRedex ra frSym [Pexpr [] () (PEval (ivVal n))]

/-- The declared procedures: `fib` alone. -/
def frProcs (ra : core_run_annotation) (nbty xbty ybty sbty zbty : core_base_type) :
    List (sym × List (sym × core_base_type) × CoreExpr) :=
  [(frSym, [(frNSym, nbty)], frBody ra xbty ybty sbty zbty)]

/-- The registered label map of `fib`'s body: `r ↦ ([(z, zbty)], pure(z))`. -/
def frQ (zbty : core_base_type) : LabelMap :=
  symAdd frRSym ([(frZSym, zbty)], pureRedex (Pexpr [] () (PEsym frZSym))) fmapEmpty

section FrFile

variable (ra : core_run_annotation) (n : Int) (nbty xbty ybty sbty zbty : core_base_type)

/-- The synthetic two-procedure file. -/
abbrev frFile : file core_run_annotation :=
  prodFileWith (frProcs ra nbty xbty ybty sbty zbty) (frMain ra n)

/-! ### `call_proc`'s lookups on the file -/

theorem frFile_funs :
    (frFile ra n nbty xbty ybty sbty zbty).funs =
      symAdd mainSym (mainDecl (frMain ra n))
        (symAdd frSym (Proc CerbLocation.unknown none BTy_unit [(frNSym, nbty)]
          (frBody ra xbty ybty sbty zbty)) fmapEmpty) := rfl

theorem frFile_lookup_main :
    lookupProc (frFile ra n nbty xbty ybty sbty zbty) fmapEmpty mainSym = some ([], frMain ra n) :=
  prodFileWith_lookup_main _ _

theorem frFile_lookup_fib :
    lookupProc (frFile ra n nbty xbty ybty sbty zbty) fmapEmpty frSym =
      some ([(frNSym, nbty)], frBody ra xbty ybty sbty zbty) := by
  unfold lookupProc
  rw [show fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) frSym
      (frFile ra n nbty xbty ybty sbty zbty).stdlib = none from rfl]
  rw [resolveExtern_id_of_empty rfl, frFile_funs, symAdd_lookup_two]
  rw [if_neg (by decide +kernel), if_pos (by decide +kernel)]

/-- Every procedure the file declares is `main` or `fib` (the symbol
    compares `.eq` with the one or the other). -/
theorem frFile_lookup_inv {g : sym} {params : List (sym × core_base_type)} {body : CoreExpr}
    (h : lookupProc (frFile ra n nbty xbty ybty sbty zbty) fmapEmpty g = some (params, body)) :
    (symOrd g mainSym = .eq ∧ params = [] ∧ body = frMain ra n) ∨
    (symOrd g frSym = .eq ∧ params = [(frNSym, nbty)] ∧ body = frBody ra xbty ybty sbty zbty) := by
  unfold lookupProc at h
  rw [show fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) g
      (frFile ra n nbty xbty ybty sbty zbty).stdlib = none from rfl] at h
  rw [resolveExtern_id_of_empty rfl, frFile_funs, symAdd_lookup_two] at h
  by_cases h1 : symOrd g mainSym = .eq
  · rw [if_pos h1] at h
    obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
    exact .inl ⟨h1, hp.symm, hb.symm⟩
  · rw [if_neg h1] at h
    by_cases h2 : symOrd g frSym = .eq
    · rw [if_pos h2] at h
      obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
      exact .inr ⟨h2, hp.symm, hb.symm⟩
    · rw [if_neg h2] at h
      cases h

/-! ### The shipped registration, computed -/

/-- `collect_saves` on `fib`'s body finds the one `save`. -/
theorem collect_saves_frBody : collect_saves (frBody ra xbty ybty sbty zbty) = frQ zbty := rfl

/-- `collect_saves` on `main`'s body finds nothing. -/
theorem collect_saves_frMain : collect_saves (frMain ra n) = fmapEmpty := rfl

/-- THE REGISTRATION on the two-procedure file (the enumeration is
    newest-insert-first, so `fib`'s fiber is the outer entry). -/
theorem collect_new_fr :
    collect_labeled_continuations_NEW (frFile ra n nbty xbty ybty sbty zbty) =
      symAdd frSym (frQ zbty) (symAdd mainSym fmapEmpty fmapEmpty) := rfl

/-- The production initial run state of the file. -/
abbrev frRS (sup : Nat) : core_run_state :=
  prodRS (frProcs ra nbty xbty ybty sbty zbty) sup (frMain ra n)

/-- THE PRODUCTION CONTEXT of the exhibit. -/
abbrev frCtx (sup : Nat) : MachineCtx :=
  prodCtx (frFile ra n nbty xbty ybty sbty zbty) (frRS ra n nbty xbty ybty sbty zbty sup)

theorem frRS_lookup_fib (sup : Nat) :
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) frSym
      (frRS ra n nbty xbty ybty sbty zbty sup).labeled = some (frQ zbty) := by
  rw [prodRS_labeled, collect_new_fr, symAdd_lookup_two, if_pos (by decide +kernel)]

theorem frRS_lookup_main (sup : Nat) :
    fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) mainSym
      (frRS ra n nbty xbty ybty sbty zbty sup).labeled = some fmapEmpty := by
  rw [prodRS_labeled, collect_new_fr, symAdd_lookup_two, if_neg (by decide +kernel),
    if_pos (by decide +kernel)]

/-- The derived label fibers of the production context. -/
theorem frCtx_labels_fib (sup : Nat) :
    (frCtx ra n nbty xbty ybty sbty zbty sup).labelsAt (some frSym) = frQ zbty := by
  rw [MachineCtx.labelsAt_some, MachineCtx.resolveProc_of_extern_empty rfl, frRS_lookup_fib]

theorem frCtx_labels_main (sup : Nat) :
    (frCtx ra n nbty xbty ybty sbty zbty sup).labelsAt (some mainSym) = fmapEmpty := by
  rw [MachineCtx.labelsAt_some, MachineCtx.resolveProc_of_extern_empty rfl, frRS_lookup_main]

theorem frQ_lookup_inv {l : sym} {params : List (sym × core_base_type)} {cont : CoreExpr}
    (h : lookupLabel (frQ zbty) l = some (params, cont)) :
    params = [(frZSym, zbty)] ∧ cont = pureRedex (Pexpr [] () (PEsym frZSym)) := by
  unfold lookupLabel frQ at h
  rw [symAdd_lookup symMap_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨h1.symm, h2.symm⟩
  · cases h

/-- THE WHOLE-FILE REGISTRATION TIE at the production initial run state:
    derived from the shipped registration by computation. -/
theorem frCtx_labeledProcs (sup : Nat) :
    LabeledProcs (frCtx ra n nbty xbty ybty sbty zbty sup)
      (frRS ra n nbty xbty ybty sbty zbty sup).labeled := by
  refine LabeledProcs.of_fibers rfl (fun g params body hg => ?_)
  show ∃ Q, fmapLookupBy _ g (frRS ra n nbty xbty ybty sbty zbty sup).labeled = some Q
  rw [prodRS_labeled, collect_new_fr, symAdd_lookup_two]
  by_cases h2 : symOrd g frSym = .eq
  · rw [if_pos h2]
    exact ⟨_, rfl⟩
  · rw [if_neg h2]
    rcases frFile_lookup_inv ra n nbty xbty ybty sbty zbty hg with ⟨h1, -, -⟩ | ⟨h1, -, -⟩
    · rw [if_pos h1]
      exact ⟨_, rfl⟩
    · exact (h2 h1).elim

/-- Every derived fiber of the production context is `fib`'s or empty. -/
theorem frCtx_labels_cases (sup : Nat) (g : sym) :
    (frCtx ra n nbty xbty ybty sbty zbty sup).labelsAt (some g) = frQ zbty ∨
    (frCtx ra n nbty xbty ybty sbty zbty sup).labelsAt (some g) = fmapEmpty := by
  rw [MachineCtx.labelsAt_some, MachineCtx.resolveProc_of_extern_empty rfl]
  show (match fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) g
      (frRS ra n nbty xbty ybty sbty zbty sup).labeled with
    | some Q => Q
    | none => fmapEmpty) = frQ zbty ∨ _ = fmapEmpty
  rw [prodRS_labeled, collect_new_fr, symAdd_lookup_two]
  by_cases h2 : symOrd g frSym = .eq
  · rw [if_pos h2]
    exact .inl rfl
  · rw [if_neg h2]
    by_cases h1 : symOrd g mainSym = .eq
    · rw [if_pos h1]
      exact .inr rfl
    · rw [if_neg h1]
      exact .inr rfl

/-! ### The fragment membership and the procedure well-formedness premise -/

theorem frDec1_pure : ∀ pe ∈ [frDec1], PePure pe := fun pe hpe => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  subst hpe
  exact PePure.of_isPePure rfl

theorem frDec1_depth : ∀ pe ∈ [frDec1], peDepth pe ≤ lemDefaultFuel := fun pe hpe => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  subst hpe
  rw [show peDepth frDec1 = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
  omega

theorem frDec2_pure : ∀ pe ∈ [frDec2], PePure pe := fun pe hpe => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  subst hpe
  exact PePure.of_isPePure rfl

theorem frDec2_depth : ∀ pe ∈ [frDec2], peDepth pe ≤ lemDefaultFuel := fun pe hpe => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  subst hpe
  rw [show peDepth frDec2 = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
  omega

theorem frSum_pure : ∀ pe ∈ saveParamPexprs [(frZSym, ((zbty, none), frSumPe))], PePure pe :=
  fun pe hpe => by
    simp only [saveParamPexprs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hpe
    subst hpe
    exact PePure.of_isPePure rfl

theorem frSum_depth :
    ∀ pe ∈ saveParamPexprs [(frZSym, ((zbty, none), frSumPe))], peDepth pe ≤ lemDefaultFuel :=
  fun pe hpe => by
    simp only [saveParamPexprs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hpe
    subst hpe
    rw [show peDepth frSumPe = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
    omega

/-- `fib`'s body is in the fragment: the guard, the base case's PURE, the
    two calls bound at the plain-symbol binder (`BareHead.call`), the `save`
    and its PURE exit. -/
theorem frBody_frag : Frag (frBody ra xbty ybty sbty zbty) :=
  .if_ (PePure.of_isPePure rfl)
    (by rw [show peDepth frGuard = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    .pure_sym
    (.sseq_sym (.call frDec1_pure frDec1_depth) (.call frDec1_pure frDec1_depth)
      (.sseq_sym (.call frDec2_pure frDec2_depth) (.call frDec2_pure frDec2_depth)
        (.save (frSum_pure zbty) (frSum_depth zbty) .pure_sym)))

theorem frMain_frag : Frag (frMain ra n) :=
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

theorem frBody_pot : pot (frBody ra xbty ybty sbty zbty) = 6 := rfl
theorem frMain_pot : pot (frMain ra n) = 2 := rfl

/-- THE PROCEDURE WELL-FORMEDNESS PREMISE at the production context: both
    bodies in the cone within the potential bound; `fib`'s one label body
    (`pure(z)`) too; `main`'s fiber empty. -/
theorem frCtx_fragProcs (sup : Nat) : (frCtx ra n nbty xbty ybty sbty zbty sup).FragProcs where
  body g params body hg := by
    rcases frFile_lookup_inv ra n nbty xbty ybty sbty zbty hg with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact frMain_frag ra n
    · exact frBody_frag ra xbty ybty sbty zbty
  potBound g params body hg := by
    rcases frFile_lookup_inv ra n nbty xbty ybty sbty zbty hg with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · rw [frMain_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega
    · rw [frBody_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega
  labels g params body _ l params' cont hl := by
    rcases frCtx_labels_cases ra n nbty xbty ybty sbty zbty sup g with h | h
    · rw [h] at hl
      obtain ⟨-, rfl⟩ := frQ_lookup_inv zbty hl
      exact ⟨.pure_sym, by
        rw [show pot (pureRedex (Pexpr [] () (PEsym frZSym))) = 2 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]
        omega⟩
    · rw [h, show lookupLabel fmapEmpty l = none from rfl] at hl
      cases hl

end FrFile

/-! ## Frames and evaluation facts -/

/-- The parameter frame `n ↦ n`. -/
abbrev frF0 (n : Int) : Fmap sym value := envAdd frNSym (ivVal n) fmapEmpty
/-- … then `x ↦ a`. -/
abbrev frF1 (n a : Int) : Fmap sym value := envAdd frXSym (ivVal a) (frF0 n)
/-- … then `y ↦ b`. -/
abbrev frF2 (n a b : Int) : Fmap sym value := envAdd frYSym (ivVal b) (frF1 n a)
/-- … then the `save`-bound `z ↦ a + b`. -/
abbrev frF3 (n a b : Int) : Fmap sym value := envAdd frZSym (ivVal (a + b)) (frF2 n a b)

theorem frF0_lookup_n (n : Int) : fmapLookupBy symCmpK frNSym (frF0 n) = some (ivVal n) := by
  rw [envAdd_lookup symFrame_empty, if_pos (by decide +kernel)]

theorem frF1_lookup_n (n a : Int) : fmapLookupBy symCmpK frNSym (frF1 n a) = some (ivVal n) := by
  rw [envAdd_lookup (symFrame_empty.add _ _), if_neg (by decide +kernel), frF0_lookup_n]

theorem frF2_lookup_x (n a b : Int) : fmapLookupBy symCmpK frXSym (frF2 n a b) = some (ivVal a) := by
  rw [envAdd_lookup ((symFrame_empty.add _ _).add _ _), if_neg (by decide +kernel),
    envAdd_lookup (symFrame_empty.add _ _), if_pos (by decide +kernel)]

theorem frF2_lookup_y (n a b : Int) : fmapLookupBy symCmpK frYSym (frF2 n a b) = some (ivVal b) := by
  rw [envAdd_lookup ((symFrame_empty.add _ _).add _ _), if_pos (by decide +kernel)]

theorem frF3_lookup_z (n a b : Int) :
    fmapLookupBy symCmpK frZSym (frF3 n a b) = some (ivVal (a + b)) := by
  rw [envAdd_lookup (((symFrame_empty.add _ _).add _ _).add _ _), if_pos (by decide +kernel)]

theorem frN_eval (n : Int) (ρ : EnvStack) :
    evalPexpr fmapEmpty fmapEmpty (frF0 n :: ρ) (Pexpr [] () (PEsym frNSym)) = some (ivVal n) := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (frF0_lookup_n n) ρ

theorem frGuard_eval (n : Int) (ρ : EnvStack) :
    evalPexpr fmapEmpty fmapEmpty (frF0 n :: ρ) frGuard = some (boolValue (decide (n < 2))) := by
  unfold frGuard
  rw [evalPexpr_op, frN_eval]
  rfl

theorem frDec1_eval (n : Int) (ρ : EnvStack) :
    evalPexprs fmapEmpty fmapEmpty (frF0 n :: ρ) [frDec1] = some [ivVal (n - 1)] := by
  rw [evalPexprs_cons]
  unfold frDec1
  rw [evalPexpr_op, frN_eval]
  rfl

theorem frDec2_eval (n a : Int) (ρ : EnvStack) :
    evalPexprs fmapEmpty fmapEmpty (frF1 n a :: ρ) [frDec2] = some [ivVal (n - 2)] := by
  rw [evalPexprs_cons]
  unfold frDec2
  rw [evalPexpr_op, evalPexpr_sym_empty, lookup_env_head (frF1_lookup_n n a) ρ]
  rfl

theorem frSum_eval (zbty : core_base_type) (n a b : Int) (ρ : EnvStack) :
    evalPexprs fmapEmpty fmapEmpty (frF2 n a b :: ρ)
      (saveParamPexprs [(frZSym, ((zbty, none), frSumPe))]) = some [ivVal (a + b)] := by
  rw [show saveParamPexprs [(frZSym, ((zbty, none), frSumPe))] = [frSumPe] from rfl,
    evalPexprs_cons]
  unfold frSumPe
  rw [evalPexpr_op, evalPexpr_sym_empty, lookup_env_head (frF2_lookup_x n a b) ρ,
    evalPexpr_sym_empty, lookup_env_head (frF2_lookup_y n a b) ρ]
  rfl

theorem frZ_eval (n a b : Int) (ρ : EnvStack) :
    evalPexpr fmapEmpty fmapEmpty (frF3 n a b :: ρ) (Pexpr [] () (PEsym frZSym)) =
      some (ivVal (a + b)) := by
  rw [evalPexpr_sym_empty]
  exact lookup_env_head (frF3_lookup_z n a b) ρ

/-- The `save`'s binding lands on the third frame. -/
theorem frBind_save (zbty : core_base_type) (n a b : Int) (ρ : EnvStack) :
    bindSaveParams [(frZSym, ((zbty, none), frSumPe))] [ivVal (a + b)] (frF2 n a b :: ρ) =
      frF3 n a b :: ρ := by
  show update_env (mk_sym_pat frZSym zbty) (ivVal (a + b)) (frF2 n a b :: ρ) = _
  rw [update_env_cons, update_env_aux_sym]

/-- The base case's value is `fib n` at `n ∈ {0, 1}`. -/
theorem fibSpec_small {n : Int} (h0 : 0 ≤ n) (hlt : n < 2) : ivVal (fibSpec n.toNat) = ivVal n := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> rfl

/-- The recursive case's value: `fib (n-1) + fib (n-2) = fib n` at `n ≥ 2`. -/
theorem fibSpec_rec {n : Int} (h2 : 2 ≤ n) :
    ivVal (fibSpec (n - 1).toNat + fibSpec (n - 2).toNat) = ivVal (fibSpec n.toNat) := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, n.toNat = k + 2 := ⟨n.toNat - 2, by omega⟩
  rw [hk, show (n - 1).toNat = k + 1 by omega, show (n - 2).toNat = k by omega, fibSpec_add_two,
    Int.add_comm]

/-! ## The budget -/

/-- THE ROUND COUNT of an activation of `fib` at argument `n` (the total
    table's budget): the guard, then PURE + delivery (3) at the base case;
    the guard, the two calls at `1 + callee + 1` each, the `save` (2) and
    PURE + delivery (2) — nine rounds beside the callees — otherwise. -/
def fibRounds : Nat → Nat
  | 0 => 3
  | 1 => 3
  | n + 2 => fibRounds (n + 1) + fibRounds n + 9

@[simp] theorem fibRounds_zero : fibRounds 0 = 3 := rfl
@[simp] theorem fibRounds_one : fibRounds 1 = 3 := rfl
theorem fibRounds_add_two (n : Nat) : fibRounds (n + 2) = fibRounds (n + 1) + fibRounds n + 9 := rfl

theorem fibRounds_small {n : Int} (h0 : 0 ≤ n) (hlt : n < 2) : fibRounds n.toNat = 3 := by
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> rfl

theorem fibRounds_rec {n : Int} (h2 : 2 ≤ n) :
    fibRounds n.toNat = fibRounds (n - 1).toNat + fibRounds (n - 2).toNat + 9 := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, n.toNat = k + 2 := ⟨n.toNat - 2, by omega⟩
  rw [hk, show (n - 1).toNat = k + 1 by omega, show (n - 2).toNat = k by omega, fibRounds_add_two]

/-- THE CLOSED FORM (derived; what the in-budget hypothesis is measured
    against): `fibRounds n + 9 = 12 · fib (n + 1)`, so `fibRounds 33 =
    68434635 ≤ 10^8 − 4 < fibRounds 34`. -/
theorem fibRounds_closed (n : Nat) : (fibRounds n : Int) + 9 = 12 * fibSpec (n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n IH =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      rw [fibRounds_add_two, show k + 2 + 1 = (k + 1) + 2 from rfl, fibSpec_add_two]
      have h1 := IH (k + 1) (by omega)
      have h2 := IH k (by omega)
      omega

/-! ## THE SPECIFICATION TABLES -/

section FrIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (ra : core_run_annotation) (n : Int) (nbty xbty ybty sbty zbty : core_base_type) (sup : Nat)

/-- THE TABLE (partial): `{⌜0 ≤ n⌝} ·(n) {ret. ⌜ret = fib n⌝}` at every
    symbol — `fib`'s specification; the logical variable `n` is the
    argument value; `main` (arity 0) is unreachable under it. -/
def frSpec : ProcSpec GF := fun _ vs =>
  (iprop(⌜∃ n : Int, vs = [ivVal n] ∧ 0 ≤ n⌝),
   fun ret => iprop(⌜∃ n : Int, vs = [ivVal n] ∧ ret = ivVal (fibSpec n.toNat)⌝))

/-- THE TOTAL TABLE: the same, with the activation's budget `fibRounds n ≤ m`. -/
def frSpecT : ProcSpecT GF := fun _ m vs =>
  (iprop(⌜∃ n : Int, vs = [ivVal n] ∧ 0 ≤ n ∧ fibRounds n.toNat ≤ m⌝),
   fun ret => iprop(⌜∃ n : Int, vs = [ivVal n] ∧ ret = ivVal (fibSpec n.toNat)⌝))

/-- No label is jumped to. -/
def frLs : LabelSpec GF := fun _ _ _ => iprop(⌜False⌝)
def frLsT : LabelSpecT GF := fun _ _ _ _ => iprop(⌜False⌝)

/-- `main`'s postcondition: the delivered value is `fib n`. -/
def frPost : SpikeVal → EnvStack → IProp GF := fun w _ => iprop(⌜w.val = ivVal (fibSpec n.toNat)⌝)

/-- THE BODY OF `fib` UNDER THE TABLE (partial), once, at every caller
    tail `ρ`: the guard (`wps_if_true`/`_false`), at the base case the
    PURE exit reading `n`; at the recursive case the two calls by
    `wps_call_root` against the table (Hoare's rule: the table is
    ASSUMED for the recursive activations — no Löb here), each result
    bound at the plain-symbol binder (`wps_seq_sym`), the `save` of the
    sum (`wps_save`), the PURE exit reading `z`. -/
theorem frBody_wps (g : sym) (vs : List value) (ρ : EnvStack) :
    (frSpec (GF := GF) g vs).1 ⊢
      wps (GF := GF) (frCtx ra n nbty xbty ybty sbty zbty sup) (some g) frLs frSpec
        (fun w _ => (frSpec g vs).2 w.val) (frBody ra xbty ybty sbty zbty)
        (procEnv [(frNSym, nbty)] vs :: ρ) := by
  dsimp only [frSpec]
  iintro %hpre
  obtain ⟨n', rfl, hn'⟩ := hpre
  rw [procEnv_single]
  unfold frBody
  by_cases hlt : n' < 2
  · -- THE BASE CASE
    iapply wps_if_true [] frGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ frGuard = _
          rw [frGuard_eval, decide_eq_true hlt]; rfl)
    unfold pureRedex
    iapply wps_pure (Pexpr [] () (PEsym frNSym)) _ rfl (frN_eval n' ρ)
    ipureintro
    exact ⟨n', rfl, (fibSpec_small hn' hlt).symm⟩
  · -- THE RECURSIVE CASE
    have h2 : 2 ≤ n' := by omega
    iapply wps_if_false [] frGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ frGuard = _
          rw [frGuard_eval, decide_eq_false hlt]; rfl)
    unfold frOuter
    iapply wps_seq_sym [] [] frXSym xbty (callRedex ra frSym [frDec1]) _ (frF0 n') ρ
    unfold callRedex
    iapply wps_call_root [] ra frSym [frDec1] (frF0 n' :: ρ) (vs := [ivVal (n' - 1)])
      (frFile_lookup_fib ra n nbty xbty ybty sbty zbty) rfl (frDec1_eval n' ρ)
    dsimp only [frSpec]
    isplitl []
    · ipureintro
      exact ⟨n' - 1, rfl, by omega⟩
    · iintro %ret %hpost
      obtain ⟨m1, hm1, rfl⟩ := hpost
      obtain rfl : m1 = n' - 1 := (ivVal_inj (List.cons.inj hm1).1).symm
      rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (fibSpec (n' - 1).toNat))))) =
        ofVal (.pure (ivVal (fibSpec (n' - 1).toNat))) from rfl]
      iapply wps_ofVal
      iexists (ivVal (fibSpec (n' - 1).toNat))
      isplit
      · ipureintro; rfl
      · rw [update_env_sym]
        unfold frInner
        iapply wps_seq_sym [] [] frYSym ybty (callRedex ra frSym [frDec2]) _ (frF1 n' _) ρ
        unfold callRedex
        iapply wps_call_root [] ra frSym [frDec2] (frF1 n' _ :: ρ) (vs := [ivVal (n' - 2)])
          (frFile_lookup_fib ra n nbty xbty ybty sbty zbty) rfl (frDec2_eval n' _ ρ)
        dsimp only [frSpec]
        isplitl []
        · ipureintro
          exact ⟨n' - 2, rfl, by omega⟩
        · iintro %ret %hpost
          obtain ⟨m2, hm2, rfl⟩ := hpost
          obtain rfl : m2 = n' - 2 := (ivVal_inj (List.cons.inj hm2).1).symm
          rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (fibSpec (n' - 2).toNat))))) =
            ofVal (.pure (ivVal (fibSpec (n' - 2).toNat))) from rfl]
          iapply wps_ofVal
          iexists (ivVal (fibSpec (n' - 2).toNat))
          isplit
          · ipureintro; rfl
          · rw [update_env_sym]
            unfold frSum saveRedex
            iapply wps_save [] (frRSym, sbty) [(frZSym, ((zbty, none), frSumPe))] _ (frF2 n' _ _) ρ
              (cvals := [ivVal (fibSpec (n' - 1).toNat + fibSpec (n' - 2).toNat)])
              (frSum_eval zbty n' _ _ ρ)
            rw [frBind_save]
            unfold pureRedex
            iapply wps_pure (Pexpr [] () (PEsym frZSym)) _ rfl (frZ_eval n' _ _ ρ)
            ipureintro
            exact ⟨n', rfl, fibSpec_rec h2⟩

/-- THE PROCEDURE SPECIFICATIONS HOLD (partial): `fib`'s body once;
    `main` is unreachable under the table (arity). -/
theorem frCtx_procSpecs : ⊢ procSpecs (GF := GF) (frCtx ra n nbty xbty ybty sbty zbty sup) frSpec := by
  refine procSpecs_intro (fun _ _ => frLs) ?_ ?_
  · intro f params body vs hf hlen
    refine blockSpecs_intro fun l params' cont vs' ev0 evs hl => ?_
    dsimp only [frLs]
    iintro %hF
    exact hF.elim
  · intro f params body vs ρ hf hlen
    rcases frFile_lookup_inv ra n nbty xbty ybty sbty zbty hf with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · dsimp only [frSpec]
      iintro %hpre
      obtain ⟨x, hx, -⟩ := hpre
      subst hx
      cases hlen
    · exact frBody_wps ra n nbty xbty ybty sbty zbty sup f vs ρ

/-- `main`'s (empty) block specifications. -/
theorem fr_blockSpecs :
    ⊢ blockSpecs (GF := GF) (frCtx ra n nbty xbty ybty sbty zbty sup) (some mainSym) frLs frSpec
      (frPost n) := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  dsimp only [frLs]
  iintro %hF
  exact hF.elim

/-- `main` under the table: the call rule alone. -/
theorem frMain_wps (hn : 0 ≤ n) (ρ : EnvStack) :
    ⊢ wps (GF := GF) (frCtx ra n nbty xbty ybty sbty zbty sup) (some mainSym) frLs frSpec
      (frPost n) (frMain ra n) ρ := by
  unfold frMain callRedex
  iapply wps_call_root [] ra frSym [Pexpr [] () (PEval (ivVal n))] ρ (vs := [ivVal n])
    (frFile_lookup_fib ra n nbty xbty ybty sbty zbty) rfl rfl
  dsimp only [frSpec]
  isplitl []
  · ipureintro
    exact ⟨n, rfl, hn⟩
  · iintro %ret %hpost
    obtain ⟨m, hm, rfl⟩ := hpost
    obtain rfl : n = m := ivVal_inj (List.cons.inj hm).1
    rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (fibSpec n.toNat))))) =
      ofVal (.pure (ivVal (fibSpec n.toNat))) from rfl]
    iapply wps_ofVal
    dsimp only [frPost]
    ipureintro
    rfl

/-- The base-WP face with the engine readout: `wps_sound` WITH the table
    at the production entry control. -/
theorem fr_wp_readout (hn : 0 ≤ n) (ℓ : exec_location) :
    ⊢ WP (⟨frMain ra n, [fmapEmpty], ⟨[], some mainSym, ℓ⟩,
          frCtx ra n nbty xbty ybty sbty zbty sup⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CoreRVal.val w = ivVal (fibSpec n.toNat)⌝) }} := by
  refine (frMain_wps ra n nbty xbty ybty sbty zbty sup hn [fmapEmpty]).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((BI.emp_sep.2.trans (BI.sep_mono (frCtx_procSpecs ra n nbty xbty ybty sbty zbty sup)
      (fr_blockSpecs ra n nbty xbty ybty sbty zbty sup))).trans
      (wps_sound (ctl := ⟨[], some mainSym, ℓ⟩) rfl (frMain ra n) [fmapEmpty])) .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  exact wp_mono fun w => stateInterp_readout fun _ _ _ _ _ => pure_consequence _

/-! ### The total twins -/

/-- THE BODY OF `fib` WITHIN ITS BUDGET, once, at every caller tail:
    `fibRounds n` rounds — the partial proof with the budget split at
    each call (`wpt_call_root`: `1 + callee + 1`, the returned value's
    delivery paying the binder's beta), the `save`'s `saveEntryCost = 2`,
    PURE + delivery `2`. -/
theorem frBody_wpt (g : sym) (m : Nat) (vs : List value) (ρ : EnvStack) :
    (frSpecT (GF := GF) g m vs).1 ⊢
      wpt (GF := GF) (frCtx ra n nbty xbty ybty sbty zbty sup) (some g) frLsT frSpecT m
        (fun w _ => (frSpecT g m vs).2 w.val) (frBody ra xbty ybty sbty zbty)
        (procEnv [(frNSym, nbty)] vs :: ρ) := by
  dsimp only [frSpecT]
  iintro %hpre
  obtain ⟨n', rfl, hn', hm⟩ := hpre
  iapply wpt_mono_k (k := fibRounds n'.toNat) hm
  rw [procEnv_single]
  unfold frBody
  by_cases hlt : n' < 2
  · -- THE BASE CASE: guard + PURE + delivery = 3
    rw [fibRounds_small hn' hlt, show (3 : Nat) = 2 + 1 from rfl]
    iapply wpt_if_true [] frGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ frGuard = _
          rw [frGuard_eval, decide_eq_true hlt]; rfl)
    unfold pureRedex
    iapply wpt_pure (Pexpr [] () (PEsym frNSym)) _ (Nat.le_refl 2) rfl (frN_eval n' ρ)
    ipureintro
    exact ⟨n', rfl, (fibSpec_small hn' hlt).symm⟩
  · -- THE RECURSIVE CASE: guard + (call₁: 1 + m₁ + 1) + (call₂: 1 + m₂ + 1) + save 2 + PURE 2
    have h2 : 2 ≤ n' := by omega
    rw [fibRounds_rec h2, show fibRounds (n' - 1).toNat + fibRounds (n' - 2).toNat + 9 =
      ((fibRounds (n' - 1).toNat + 2) + ((fibRounds (n' - 2).toNat + 2) + 4)) + 1 by omega]
    iapply wpt_if_false [] frGuard _ _ _
      (by show evalPexpr fmapEmpty fmapEmpty _ frGuard = _
          rw [frGuard_eval, decide_eq_false hlt]; rfl)
    unfold frOuter
    iapply wpt_seq_sym [] [] frXSym xbty (callRedex ra frSym [frDec1]) _ (frF0 n') ρ
      (fibRounds (n' - 1).toNat + 2) ((fibRounds (n' - 2).toNat + 2) + 4)
    unfold callRedex
    iapply wpt_call_root [] ra frSym [frDec1] (frF0 n' :: ρ) (vs := [ivVal (n' - 1)])
      (m := fibRounds (n' - 1).toNat) (k' := 1)
      (frFile_lookup_fib ra n nbty xbty ybty sbty zbty) rfl (frDec1_eval n' ρ) (by omega)
    dsimp only [frSpecT]
    isplitl []
    · ipureintro
      exact ⟨n' - 1, rfl, by omega, Nat.le_refl _⟩
    · iintro %ret %hpost
      obtain ⟨m1, hm1, rfl⟩ := hpost
      obtain rfl : m1 = n' - 1 := (ivVal_inj (List.cons.inj hm1).1).symm
      rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (fibSpec (n' - 1).toNat))))) =
        ofVal (.pure (ivVal (fibSpec (n' - 1).toNat))) from rfl]
      iapply wpt_ofVal _ _ (Nat.le_refl 1)
      iexists (ivVal (fibSpec (n' - 1).toNat))
      isplit
      · ipureintro; rfl
      · rw [update_env_sym]
        unfold frInner
        iapply wpt_seq_sym [] [] frYSym ybty (callRedex ra frSym [frDec2]) _ (frF1 n' _) ρ
          (fibRounds (n' - 2).toNat + 2) 4
        unfold callRedex
        iapply wpt_call_root [] ra frSym [frDec2] (frF1 n' _ :: ρ) (vs := [ivVal (n' - 2)])
          (m := fibRounds (n' - 2).toNat) (k' := 1)
          (frFile_lookup_fib ra n nbty xbty ybty sbty zbty) rfl (frDec2_eval n' _ ρ) (by omega)
        dsimp only [frSpecT]
        isplitl []
        · ipureintro
          exact ⟨n' - 2, rfl, by omega, Nat.le_refl _⟩
        · iintro %ret %hpost
          obtain ⟨m2, hm2, rfl⟩ := hpost
          obtain rfl : m2 = n' - 2 := (ivVal_inj (List.cons.inj hm2).1).symm
          rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (fibSpec (n' - 2).toNat))))) =
            ofVal (.pure (ivVal (fibSpec (n' - 2).toNat))) from rfl]
          iapply wpt_ofVal _ _ (Nat.le_refl 1)
          iexists (ivVal (fibSpec (n' - 2).toNat))
          isplit
          · ipureintro; rfl
          · rw [update_env_sym]
            unfold frSum saveRedex
            rw [show (4 : Nat) = 2 + saveEntryCost [(frZSym, ((zbty, none), frSumPe))] from
              by rw [saveEntryCost_of_eval rfl]]
            iapply wpt_save [] (frRSym, sbty) [(frZSym, ((zbty, none), frSumPe))] _ (frF2 n' _ _) ρ
              (cvals := [ivVal (fibSpec (n' - 1).toNat + fibSpec (n' - 2).toNat)])
              (frSum_eval zbty n' _ _ ρ)
            rw [frBind_save]
            unfold pureRedex
            iapply wpt_pure (Pexpr [] () (PEsym frZSym)) _ (Nat.le_refl 2) rfl (frZ_eval n' _ _ ρ)
            ipureintro
            exact ⟨n', rfl, fibSpec_rec h2⟩

theorem frCtx_procSpecsT :
    ⊢ procSpecsT (GF := GF) (frCtx ra n nbty xbty ybty sbty zbty sup) frSpecT := by
  refine procSpecsT_intro (fun _ _ _ => frLsT) ?_ ?_
  · intro f params body m vs hf hlen
    refine blockSpecsT_intro fun l params' cont vs' ev0 evs m' hl => ?_
    dsimp only [frLsT]
    iintro %hF
    exact hF.elim
  · intro f params body m vs ρ hf hlen
    rcases frFile_lookup_inv ra n nbty xbty ybty sbty zbty hf with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · dsimp only [frSpecT]
      iintro %hpre
      obtain ⟨x, hx, -⟩ := hpre
      subst hx
      cases hlen
    · exact frBody_wpt ra n nbty xbty ybty sbty zbty sup f m vs ρ

theorem fr_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (frCtx ra n nbty xbty ybty sbty zbty sup) (some mainSym) frLsT frSpecT
      (frPost n) := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  dsimp only [frLsT]
  iintro %hF
  exact hF.elim

/-- `main` within budget `fibRounds n + 2`: the call round, the callee's
    `fibRounds n`, the delivery of the returned value. -/
theorem frMain_wpt (hn : 0 ≤ n) (ρ : EnvStack) :
    ⊢ wpt (GF := GF) (frCtx ra n nbty xbty ybty sbty zbty sup) (some mainSym) frLsT frSpecT
      (fibRounds n.toNat + 2) (frPost n) (frMain ra n) ρ := by
  unfold frMain callRedex
  iapply wpt_call_root [] ra frSym [Pexpr [] () (PEval (ivVal n))] ρ (vs := [ivVal n])
    (m := fibRounds n.toNat) (k' := 1)
    (frFile_lookup_fib ra n nbty xbty ybty sbty zbty) rfl rfl (by omega)
  dsimp only [frSpecT]
  isplitl []
  · ipureintro
    exact ⟨n, rfl, hn, Nat.le_refl _⟩
  · iintro %ret %hpost
    obtain ⟨m, hm, rfl⟩ := hpost
    obtain rfl : n = m := ivVal_inj (List.cons.inj hm).1
    rw [show Expr [] (Epure (Pexpr [] () (PEval (ivVal (fibSpec n.toNat))))) =
      ofVal (.pure (ivVal (fibSpec n.toNat))) from rfl]
    iapply wpt_ofVal _ _ (Nat.le_refl 1)
    dsimp only [frPost]
    ipureintro
    rfl

/-- The postcondition entails the engine readout. -/
theorem frPost_to_readout :
    ∀ w ρ', frPost (GF := GF) n w ρ' ⊢
      readoutPost (fun v _ => v = ivVal (fibSpec n.toNat)) w ρ' :=
  fun _ _ => stateInterp_readout fun _ _ _ _ _ => pure_consequence _

end FrIris

/-! ## The two engine statements -/

section FrEngine

variable (sup : Nat) (ra : core_run_annotation) (n : Int)
  (nbty xbty ybty sbty zbty : core_base_type)

/-- RECURSIVE FIB THROUGH THE `driveU` LANE (PROVISIONAL, as every `driveU`
    export): the package loop at the two-procedure file never kills or
    derails, and delivers `fib n` — `engine_adequacyU` with `FragProcs` at
    the production context, from any memory, at every drive length. -/
theorem fib_rec_certified (hn : 0 ≤ n) (σ₀ : Mem) (nsteps : Nat) (aids : Nat → Nat) :
    let M := frCtx ra n nbty xbty ybty sbty zbty sup
    (∀ r, driveU M aids nsteps (M.thread (frMain ra n) [fmapEmpty] prodCtl) σ₀ ≠ .killed r) ∧
    (driveU M aids nsteps (M.thread (frMain ra n) [fmapEmpty] prodCtl) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveU M aids nsteps (M.thread (frMain ra n) [fmapEmpty] prodCtl) σ₀ = .done v σ' →
      v = ivVal (fibSpec n.toNat)) := by
  intro M
  refine engine_adequacyU (GF := SpikeGF) (M := M) ⟨rfl⟩ (ctl := prodCtl) rfl
    (fun l params cont hl => by
      rw [show prodCtl.proc = some mainSym from rfl, frCtx_labels_main,
        show lookupLabel fmapEmpty l = none from rfl] at hl
      cases hl)
    (fun l params cont hl => by
      rw [show prodCtl.proc = some mainSym from rfl, frCtx_labels_main,
        show lookupLabel fmapEmpty l = none from rfl] at hl
      cases hl)
    (frCtx_fragProcs ra n nbty xbty ybty sbty zbty sup)
    (frMain ra n) fmapEmpty [] σ₀ (∅ : SpikeHeapF SpikeCell)
    (frMain_frag ra n)
    (by rw [frMain_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (coh_empty σ₀)
    (fun v _ => v = ivVal (fibSpec n.toNat))
    ?_ nsteps aids
  intro inst
  exact (BigSepM.bigSepM_empty).1.trans
    (fr_wp_readout ra n nbty xbty ybty sbty zbty sup hn _)

/-- RECURSIVE FIB, PRODUCTION FORM — THE FLAGSHIP OF THE CALLS ARC: running
    the SHIPPED pipeline cold on the synthetic TWO-PROCEDURE file (`main`
    calling `fib`, `fib` calling itself twice per activation) is EXACTLY
    ONE Active execution delivering `fib n`, for every `n ≥ 0` whose
    certified round count fits the shipped driver's own budget
    (`fibRounds n + 4 ≤ CerbFuel.driverFuel = 10^8`, i.e. `n ≤ 33`). The
    label map the driver reads is what the shipped registration computes
    on both procedures; every PCALL and RETURN round of the run is the
    driver's own (`loop_step_frag`); termination from the total judgment
    (`fibRounds`); no package drive in the statement — the execution
    function is the shipped runner. -/
theorem fib_rec_certified_production (hn : 0 ≤ n)
    (hfuel : fibRounds n.toNat + 4 ≤ CerbFuel.driverFuel)
    (fs : CerbFS.FsState) (args : List String) :
    ∃ (dres : driver_result) (dst' : driver_state),
      CerbND.runND
          (_root_.drive fmapEmpty false
            (prodFileWith (frProcs ra nbty xbty ybty sbty zbty) (frMain ra n)) args)
          ((initial_driver_state sup
            (prodFileWith (frProcs ra nbty xbty ybty sbty zbty) (frMain ra n)) fs).1) =
        [(nd_status.Active dres, ([] : List String), dst')] ∧
      dres.dres_core_value = ivVal (fibSpec n.toNat) ∧
      dres.dres_blocked = false ∧
      dres.dres_stdout = "" ∧
      dres.dres_stderr = "" := by
  have h := prod_run_eqJ_procs sup (frProcs ra nbty xbty ybty sbty zbty) (frMain ra n)
    (frCtx_labeledProcs ra n nbty xbty ybty sbty zbty sup)
    (fun v _ => v = ivVal (fibSpec n.toNat)) (fibRounds n.toNat + 2)
    (wpt_driver_done_procs (GF := SpikeGF)
      (M₀ := frCtx ra n nbty xbty ybty sbty zbty sup) rfl rfl
      (frCtx_fragProcs ra n nbty xbty ybty sbty zbty sup)
      (th₀ := prodThread (frMain ra n)) rfl
      (frFile_lookup_main ra n nbty xbty ybty sbty zbty) prodCtl.execLoc
      frSpecT frLsT
      (frMain ra n) fmapEmpty [] prodMem₀ (∅ : SpikeHeapF SpikeCell) 0
      (frMain_frag ra n)
      (by rw [frMain_pot, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (prodMem₀_launchCoh 0 (Nat.zero_le _))
      (fun v _ => v = ivVal (fibSpec n.toNat)) (fibRounds n.toNat + 2)
      (by
        intro inst
        iintro ⟨-, -⟩
        isplitl []
        · iapply frCtx_procSpecsT ra n nbty xbty ybty sbty zbty sup
        isplitl []
        · iapply (fr_blockSpecsT ra n nbty xbty ybty sbty zbty sup).trans
            (blockSpecsT_mono (frPost_to_readout n))
          itrivial
        · iapply (frMain_wpt ra n nbty xbty ybty sbty zbty sup hn [fmapEmpty]).trans
            (wpt_mono (frPost_to_readout n) _ _ _)
          itrivial))
    (by omega) fs args
  exact h

end FrEngine

end CerberusHeapLang
