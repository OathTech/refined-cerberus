/-
CerberusHeapLang.Examples.CallSmoke — the calls arc C3 SMOKE: a
two-procedure file verified through the SPECIFICATION TABLE, the call
rule and the procedure rule, collapsed with the table, and driven
through the PROVISIONAL `driveU` lane (not a client exhibit — a
structurally-forcing example that every C3 surface is consumed once).

THE PROGRAM. `main` calls `f(3)`; `f(x)` is `save ret(y := x + 1) in
pure(y)` — the fragment's binder for pure computation (`Esave` at an
evaluated initializer, `wps_save`; the pure exit is a symbol,
`Frag.pure_sym`). THE SPEC, as the table entry: `{⌜0 ≤ x⌝} f(x)
{ret. ⌜ret = x + 1⌝}` — `csSpec`, the same entry at every symbol (the
logical variable `x` is fixed by the argument value: a spec is
quantified at use); `main` cannot be called under it (its arity is 0,
the precondition demands one argument). `main`'s post: the delivered
value is `4`.

WHAT IS EXERCISED, once each: `ProcSpec`/`emptyProcSpec`,
`procSpecs_intro` (ONE body proof of `f` at every caller tail `ρ` —
`∀ ρ` costs nothing: every read of the body is a head-frame hit on the
`SymFrame` `procEnv` builds), `wps_call_root` (the caller: the table's
precondition, then the continuation at the returned value),
`wps_sound` (the collapse WITH the table), and `engine_adequacyU` with
`MachineCtx.FragProcs` discharged at a two-procedure file (the premise's
first non-vacuous instance: both bodies in `Frag` within the potential
bound, both label fibers empty). The total twins at the `wpt` level:
`procSpecsT_intro`, `wpt_call_root`, `wpt_sound` (the callee at budget
`4`: SAVE-EVAL, SAVE, PURE, the RETURN — its delivery cost; the caller
at `1 + 4 + 1`). The PRODUCTION lane (the shipped driver) through a call
needs the `exec_loc`/`current_loc` production tie — C4, with recursive
fib (`docs/2026-09-03_c3-notes.md`).
-/
import CerberusHeapLang.API

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open scoped Iris.Std.PartialMap
open Lem_Basic_classes Lem_Map

/-! ## The program -/

/-- The startup symbol. -/
def csMain : sym := Symbol "" 0 SD_None
/-- The callee. -/
def csF : sym := Symbol "" 1 SD_None
/-- `f`'s parameter. -/
def csX : sym := Symbol "" 2 SD_None
/-- The `save`-bound result. -/
def csY : sym := Symbol "" 3 SD_None
/-- The `save` label (never jumped to). -/
def csL : sym := Symbol "" 4 SD_None

/-- An integer literal (the memory model's `integerIval`, as the
    exhibits' `ivVal`). -/
def csInt (i : Int) : value := Vobject (OVinteger (CerbMem.integerIval i))

theorem csInt_inj {i j : Int} (h : csInt i = csInt j) : i = j := by
  unfold csInt CerbMem.integerIval at h
  cases h
  rfl

/-- `x + 1`. -/
def csIncPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpAdd (Pexpr [] () (PEsym csX)) (Pexpr [] () (PEval (csInt 1))))

/-- `f`'s body: `save ret(y := x + 1) in pure(y)`. -/
def csFBody (bty ybty : core_base_type) : CoreExpr :=
  saveRedex (csL, bty) [(csY, ((ybty, none), csIncPe))] (pureRedex (Pexpr [] () (PEsym csY)))

/-- `main`'s body: `f(3)`. -/
def csMainBody (ra : core_run_annotation) : CoreExpr :=
  callRedex ra csF [Pexpr [] () (PEval (csInt 3))]

/-- The two-procedure file: `main ↦ Proc … [] (f(3))`, `f ↦ Proc … [(x, bty)]
    (save ret(y := x + 1) in pure(y))`; no stdlib, no externs. -/
def csFile (ra : core_run_annotation) (bty ybty : core_base_type) :
    file core_run_annotation :=
  { main := some csMain,
    calling_convention0 := default,
    tagDefs := default,
    stdlib := fmapEmpty,
    impl0 := fmapEmpty,
    globs := [],
    funs := symAdd csMain (Proc CerbLocation.unknown none bty [] (csMainBody ra))
      (symAdd csF (Proc CerbLocation.unknown none bty [(csX, bty)] (csFBody bty ybty)) fmapEmpty),
    extern := fmapEmpty,
    funinfo := fmapEmpty,
    loop_attributes1 := default,
    visible_objects_env0 := default }

/-- The straight-line profile over the smoke file. -/
@[reducible] def csCtx (ra : core_run_annotation) (bty ybty : core_base_type) : MachineCtx :=
  { spikeCtx with file := csFile ra bty ybty }

/-! ## The file's lookups -/

/-! The two-entry lookups below read `call_proc`'s map off the file
through the β-generic `symAdd_lookup_two` (EnvLaws; C4 moved the smoke's
former local law there — the C3 range audit's H-2). -/

/-- `call_proc`'s lookup finds `f` (computed). -/
theorem csFile_lookup_f (ra : core_run_annotation) (bty ybty : core_base_type) :
    lookupProc (csFile ra bty ybty) fmapEmpty csF = some ([(csX, bty)], csFBody bty ybty) := by
  unfold lookupProc
  rw [show fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) csF
      (csFile ra bty ybty).stdlib = none from rfl]
  rw [resolveExtern_id_of_empty rfl, show (csFile ra bty ybty).funs =
      symAdd csMain (Proc CerbLocation.unknown none bty [] (csMainBody ra))
        (symAdd csF (Proc CerbLocation.unknown none bty [(csX, bty)] (csFBody bty ybty)) fmapEmpty)
      from rfl, symAdd_lookup_two]
  rw [if_neg (by decide +kernel), if_pos (by decide +kernel)]

/-- Every procedure the file declares is `main` or `f` — read off the
    two-entry map (the keys compare `.eq` only with themselves modulo the
    symbol description, which the bodies do not depend on). -/
theorem csFile_lookup_inv (ra : core_run_annotation) (bty ybty : core_base_type) {g : sym}
    {params : List (sym × core_base_type)} {body : CoreExpr}
    (h : lookupProc (csFile ra bty ybty) fmapEmpty g = some (params, body)) :
    (params = [] ∧ body = csMainBody ra) ∨ (params = [(csX, bty)] ∧ body = csFBody bty ybty) := by
  unfold lookupProc at h
  rw [show fmapLookupBy (fun (s1 : sym) (s2 : sym) => Lem_Basic_classes.ordCompare s1 s2) g
      (csFile ra bty ybty).stdlib = none from rfl] at h
  rw [resolveExtern_id_of_empty rfl, show (csFile ra bty ybty).funs =
      symAdd csMain (Proc CerbLocation.unknown none bty [] (csMainBody ra))
        (symAdd csF (Proc CerbLocation.unknown none bty [(csX, bty)] (csFBody bty ybty)) fmapEmpty)
      from rfl, symAdd_lookup_two] at h
  by_cases h1 : symOrd g csMain = .eq
  · rw [if_pos h1] at h
    obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
    exact .inl ⟨hp.symm, hb.symm⟩
  · rw [if_neg h1] at h
    by_cases h2 : symOrd g csF = .eq
    · rw [if_pos h2] at h
      obtain ⟨hp, hb⟩ := Prod.mk.inj (Option.some.inj h)
      exact .inr ⟨hp.symm, hb.symm⟩
    · rw [if_neg h2] at h
      cases h

/-- The label fibers are empty at every procedure (the frozen run
    state registers nothing). -/
theorem csCtx_labels (ra : core_run_annotation) (bty ybty : core_base_type) (g : Option sym) :
    (csCtx ra bty ybty).labelsAt g = fmapEmpty := by
  cases g with
  | none => rfl
  | some g => rfl

theorem csCtx_lookupLabel (ra : core_run_annotation) (bty ybty : core_base_type) (g : Option sym)
    (l : sym) : lookupLabel ((csCtx ra bty ybty).labelsAt g) l = none := by
  rw [csCtx_labels]; rfl

/-! ## The fragment membership (the adequacy premise, at two procedures) -/

theorem csIncPe_pure : PePure csIncPe := PePure.of_isPePure rfl

theorem csFBody_frag (bty ybty : core_base_type) : Frag (csFBody bty ybty) :=
  .save (fun pe hpe => by
      simp only [saveParamPexprs, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hpe
      subst hpe
      exact csIncPe_pure)
    (fun pe hpe => by
      simp only [saveParamPexprs, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hpe
      subst hpe
      rw [show peDepth csIncPe = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]
      omega)
    .pure_sym

theorem csMainBody_frag (ra : core_run_annotation) : Frag (csMainBody ra) :=
  .call (fun pe hpe => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      subst hpe
      exact .val _ _)
    (fun pe hpe => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
      subst hpe
      rw [show peDepth (Pexpr [] () (PEval (csInt 3))) = 1 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]
      omega)

/-- THE PROCEDURE WELL-FORMEDNESS PREMISE of the `driveU` lane at a
    two-procedure file: both bodies in the certified cone within the
    potential bound; both label fibers empty. -/
theorem csCtx_fragProcs (ra : core_run_annotation) (bty ybty : core_base_type) :
    (csCtx ra bty ybty).FragProcs where
  body f params body hf := by
    rcases csFile_lookup_inv ra bty ybty hf with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact csMainBody_frag ra
    · exact csFBody_frag bty ybty
  potBound f params body hf := by
    rcases csFile_lookup_inv ra bty ybty hf with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Nat.le_trans (Frag.pot_le_two (csMainBody_frag ra))
        (by rw [show esize (csMainBody ra) = 1 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    · exact Nat.le_trans (Frag.pot_le_two (csFBody_frag bty ybty))
        (by rw [show esize (csFBody bty ybty) = 2 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
  labels f params body _ l params' cont hl := by
    rw [csCtx_lookupLabel] at hl
    cases hl

/-! ## The specification table -/

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (ra : core_run_annotation) (bty ybty : core_base_type)

/-- THE TABLE: `{⌜0 ≤ x⌝} ·(x) {ret. ⌜ret = x + 1⌝}` at every symbol —
    `f`'s specification; the logical variable `x` is the argument value.
    `main` (arity 0) is unreachable under it: no argument list of length
    0 satisfies the precondition. -/
def csSpec : ProcSpec GF := fun _ vs =>
  (iprop(⌜∃ x : Int, vs = [csInt x] ∧ 0 ≤ x⌝),
   fun ret => iprop(⌜∃ x : Int, vs = [csInt x] ∧ ret = csInt (x + 1)⌝))

/-- The vacuous label context (no labels are jumped to). -/
def csLs : LabelSpec GF := fun _ _ _ => iprop(⌜False⌝)

/-- `main`'s postcondition: the value `4`. -/
def csPost : SpikeVal → EnvStack → IProp GF := fun w _ => iprop(⌜w.val = csInt 4⌝)

/-! ## The callee's body: one proof at every caller tail -/

theorem csFrame_lookup_x (v : value) :
    fmapLookupBy symCmpK csX (procEnv [(csX, bty)] [v]) = some v := by
  rw [procEnv_single, envAdd_lookup symFrame_empty symCmpK, if_pos (by decide +kernel)]

/-- `x + 1` evaluates at the parameter frame. -/
theorem csIncPe_eval (x : Int) (ρ : EnvStack) :
    evalPexpr fmapEmpty fmapEmpty (procEnv [(csX, bty)] [csInt x] :: ρ) csIncPe =
      some (csInt (x + 1)) := by
  unfold csIncPe
  rw [evalPexpr_op, evalPexpr_sym_empty, lookup_env_head (csFrame_lookup_x bty _) ρ]
  rfl

/-- The body of `f` under the table's precondition, at EVERY caller
    tail: SAVE (the initializer evaluated at the parameter frame), then
    the PURE exit reading the bound result. -/
theorem csF_body_wps (g : sym) (vs : List value) (ρ : EnvStack) :
    (csSpec (GF := GF) g vs).1 ⊢
      wps (GF := GF) (csCtx ra bty ybty) (some g) csLs csSpec (fun w _ => (csSpec g vs).2 w.val)
        (csFBody bty ybty) (procEnv [(csX, bty)] vs :: ρ) := by
  dsimp only [csSpec]
  iintro %hpre
  obtain ⟨x, rfl, -⟩ := hpre
  unfold csFBody saveRedex
  iapply wps_save [] (csL, bty) [(csY, ((ybty, none), csIncPe))] _ (procEnv [(csX, bty)] [csInt x]) ρ
    (cvals := [csInt (x + 1)])
    (by rw [show saveParamPexprs [(csY, ((ybty, none), csIncPe))] = [csIncPe] from rfl,
      evalPexprs_cons, csIncPe_eval]; rfl)
  have hbind : bindSaveParams [(csY, ((ybty, none), csIncPe))] [csInt (x + 1)]
      (procEnv [(csX, bty)] [csInt x] :: ρ) =
      envAdd csY (csInt (x + 1)) (procEnv [(csX, bty)] [csInt x]) :: ρ := by
    show update_env (mk_sym_pat csY ybty) (csInt (x + 1)) (procEnv [(csX, bty)] [csInt x] :: ρ) = _
    rw [update_env_cons, update_env_aux_sym]
  rw [hbind]
  unfold pureRedex
  iapply wps_pure (Pexpr [] () (PEsym csY)) _ rfl
    (by rw [evalPexpr_sym_empty]
        exact lookup_env_head (by
          rw [procEnv_single, envAdd_lookup (symFrame_empty.add _ _) symCmpK, if_pos (by decide +kernel)]) ρ)
  ipureintro
  exact ⟨x, rfl, rfl⟩

/-- THE PROCEDURE SPECIFICATIONS HOLD for the file: `f`'s body once
    (above); `main` is unreachable under the table (arity). -/
theorem csCtx_procSpecs : ⊢ procSpecs (GF := GF) (csCtx ra bty ybty) csSpec := by
  refine procSpecs_intro (fun _ _ => csLs) ?_ ?_
  · intro f params body vs hf hlen
    refine blockSpecs_intro fun l params' cont vs' ev0 evs hl => ?_
    rw [csCtx_lookupLabel] at hl
    cases hl
  · intro f params body vs ρ hf hlen
    rcases csFile_lookup_inv ra bty ybty hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `main`: no argument list of length 0 meets the precondition
      dsimp only [csSpec]
      iintro %hpre
      obtain ⟨x, hx, -⟩ := hpre
      subst hx
      cases hlen
    · -- `f`: the one body proof (at whichever symbol the entry is read at)
      exact csF_body_wps ra bty ybty f vs ρ

/-- The (vacuous) block specifications of `main`'s fiber. -/
theorem cs_blockSpecs :
    ⊢ blockSpecs (GF := GF) (csCtx ra bty ybty) (some csMain) csLs csSpec csPost := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  rw [csCtx_lookupLabel] at hl
  cases hl

/-! ## The caller: THE CALL RULE against the table -/

/-- `main`'s body under the table: the precondition at `x := 3`, then
    the continuation at the returned value `4`. No `Step`, no drive, no
    Löb — `wps_call_root` alone. -/
theorem csMain_wps (ρ : EnvStack) :
    ⊢ wps (GF := GF) (csCtx ra bty ybty) (some csMain) csLs csSpec csPost (csMainBody ra) ρ := by
  unfold csMainBody callRedex
  iapply wps_call_root [] ra csF [Pexpr [] () (PEval (csInt 3))] ρ
    (csFile_lookup_f ra bty ybty) rfl rfl
  dsimp only [csSpec]
  isplitl []
  · ipureintro
    exact ⟨3, rfl, by decide⟩
  · iintro %ret %hpost
    obtain ⟨x, hx, rfl⟩ := hpost
    obtain rfl : x = 3 := (csInt_inj (List.cons.inj hx).1).symm
    rw [show Expr [] (Epure (Pexpr [] () (PEval (csInt (3 + 1))))) =
      ofVal (.pure (csInt (3 + 1))) from rfl]
    iapply wps_ofVal
    dsimp only [csPost]
    ipureintro
    rfl

/-! ## The collapse WITH the table, and the `driveU` lane -/

/-- The base-WP face with the engine readout: `wps_sound` at the entry
    control under `procSpecs ∗ blockSpecs`. -/
theorem cs_wp_readout (ℓ : exec_location) :
    ⊢ WP (⟨csMainBody ra, [fmapEmpty], ⟨[], some csMain, ℓ⟩, csCtx ra bty ybty⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗ ⌜CoreRVal.val w = csInt 4⌝) }} := by
  refine (csMain_wps ra bty ybty [fmapEmpty]).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((BI.emp_sep.2.trans (BI.sep_mono (csCtx_procSpecs ra bty ybty) (cs_blockSpecs ra bty ybty))).trans
      (wps_sound (ctl := ⟨[], some csMain, ℓ⟩) rfl (csMainBody ra) [fmapEmpty])) .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  exact wp_mono fun w => stateInterp_readout fun _ _ _ _ _ => pure_consequence _

/-- The empty seeded footprint is coherent with any memory (the
    exhibits' `coh_empty`, restated here — Examples import the API only). -/
theorem csCoh_empty (σ : Mem) : Coh fmapEmpty σ ((∅ : SpikeHeapF SpikeCell)) := by
  refine ⟨fun i c hg => ?_, fun i j c1 c2 hne h1 h2 => ?_⟩
  · rw [Iris.Std.LawfulPartialMap.get?_empty] at hg
    cases hg
  · rw [Iris.Std.LawfulPartialMap.get?_empty] at h1
    cases h1

/-- THE `driveU` LANE THROUGH A CALL (PROVISIONAL, as every `driveU`
    export): the package loop at the two-procedure file never kills or
    derails, and delivers `4` — `engine_adequacyU` with `FragProcs`
    discharged at both procedures (the first non-vacuous instance). -/
theorem call_smoke_driveU (σ₀ : Mem) (nsteps : Nat) (aids : Nat → Nat) :
    (∀ r, driveU (csCtx ra bty ybty) aids nsteps
      ((csCtx ra bty ybty).thread (csMainBody ra) [fmapEmpty] ⟨[], some csMain, default⟩) σ₀
        ≠ .killed r) ∧
    (driveU (csCtx ra bty ybty) aids nsteps
      ((csCtx ra bty ybty).thread (csMainBody ra) [fmapEmpty] ⟨[], some csMain, default⟩) σ₀
        ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveU (csCtx ra bty ybty) aids nsteps
        ((csCtx ra bty ybty).thread (csMainBody ra) [fmapEmpty] ⟨[], some csMain, default⟩) σ₀
          = .done v σ' →
      v = csInt 4) := by
  refine engine_adequacyU (GF := SpikeGF) (M := csCtx ra bty ybty) ⟨rfl⟩
    (ctl := ⟨[], some csMain, default⟩) rfl
    (fun l params cont hl => by rw [csCtx_lookupLabel] at hl; cases hl)
    (fun l params cont hl => by rw [csCtx_lookupLabel] at hl; cases hl)
    (csCtx_fragProcs ra bty ybty)
    (csMainBody ra) fmapEmpty [] σ₀ (∅ : SpikeHeapF SpikeCell)
    (csMainBody_frag ra)
    (Nat.le_trans (Frag.pot_le_two (csMainBody_frag ra))
      (by rw [show esize (csMainBody ra) = 1 from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega))
    (csCoh_empty σ₀)
    (fun v _ => v = csInt 4)
    ?_ nsteps aids
  intro inst
  exact (BigSepM.bigSepM_empty).1.trans (cs_wp_readout ra bty ybty default)

/-! ## The total twins (the `wpt` level; the driver-level total lane
through calls is C4's) -/

/-- THE TOTAL TABLE: the same specification, with the callee's budget
    `4 ≤ m` in the precondition (SAVE-EVAL + SAVE + PURE + the RETURN
    delivery). -/
def csSpecT : ProcSpecT GF := fun _ m vs =>
  (iprop(⌜4 ≤ m ∧ ∃ x : Int, vs = [csInt x] ∧ 0 ≤ x⌝),
   fun ret => iprop(⌜∃ x : Int, vs = [csInt x] ∧ ret = csInt (x + 1)⌝))

def csLsT : LabelSpecT GF := fun _ _ _ _ => iprop(⌜False⌝)

/-- `f`'s body within budget `m ≥ 4`. -/
theorem csF_body_wpt (g : sym) (m : Nat) (vs : List value) (ρ : EnvStack) :
    (csSpecT (GF := GF) g m vs).1 ⊢
      wpt (GF := GF) (csCtx ra bty ybty) (some g) csLsT csSpecT m (fun w _ => (csSpecT g m vs).2 w.val)
        (csFBody bty ybty) (procEnv [(csX, bty)] vs :: ρ) := by
  dsimp only [csSpecT]
  iintro %hpre
  obtain ⟨hm, x, rfl, -⟩ := hpre
  iapply wpt_mono_k (k := 4) hm
  unfold csFBody saveRedex
  rw [show (4 : Nat) = 2 + saveEntryCost [(csY, ((ybty, none), csIncPe))] from
    by rw [saveEntryCost_of_eval rfl]]
  iapply wpt_save [] (csL, bty) [(csY, ((ybty, none), csIncPe))] _ (procEnv [(csX, bty)] [csInt x]) ρ
    (cvals := [csInt (x + 1)])
    (by rw [show saveParamPexprs [(csY, ((ybty, none), csIncPe))] = [csIncPe] from rfl,
      evalPexprs_cons, csIncPe_eval]; rfl)
  have hbind : bindSaveParams [(csY, ((ybty, none), csIncPe))] [csInt (x + 1)]
      (procEnv [(csX, bty)] [csInt x] :: ρ) =
      envAdd csY (csInt (x + 1)) (procEnv [(csX, bty)] [csInt x]) :: ρ := by
    show update_env (mk_sym_pat csY ybty) (csInt (x + 1)) (procEnv [(csX, bty)] [csInt x] :: ρ) = _
    rw [update_env_cons, update_env_aux_sym]
  rw [hbind]
  unfold pureRedex
  iapply wpt_pure (Pexpr [] () (PEsym csY)) _ (Nat.le_refl 2) rfl
    (by rw [evalPexpr_sym_empty]
        exact lookup_env_head (by
          rw [procEnv_single, envAdd_lookup (symFrame_empty.add _ _) symCmpK, if_pos (by decide +kernel)]) ρ)
  ipureintro
  exact ⟨x, rfl, rfl⟩

theorem csCtx_procSpecsT : ⊢ procSpecsT (GF := GF) (csCtx ra bty ybty) csSpecT := by
  refine procSpecsT_intro (fun _ _ _ => csLsT) ?_ ?_
  · intro f params body m vs hf hlen
    refine blockSpecsT_intro fun l params' cont vs' ev0 evs m' hl => ?_
    rw [csCtx_lookupLabel] at hl
    cases hl
  · intro f params body m vs ρ hf hlen
    rcases csFile_lookup_inv ra bty ybty hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · dsimp only [csSpecT]
      iintro %hpre
      obtain ⟨-, x, hx, -⟩ := hpre
      subst hx
      cases hlen
    · exact csF_body_wpt ra bty ybty f m vs ρ

theorem cs_blockSpecsT :
    ⊢ blockSpecsT (GF := GF) (csCtx ra bty ybty) (some csMain) csLsT csSpecT csPost := by
  refine blockSpecsT_intro fun l params cont vs ev0 evs m hl => ?_
  rw [csCtx_lookupLabel] at hl
  cases hl

/-- `main` within budget `6` = the call round + the callee's `4` + the
    delivery of the returned value. -/
theorem csMain_wpt (ρ : EnvStack) :
    ⊢ wpt (GF := GF) (csCtx ra bty ybty) (some csMain) csLsT csSpecT 6 csPost (csMainBody ra) ρ := by
  unfold csMainBody callRedex
  iapply wpt_call_root [] ra csF [Pexpr [] () (PEval (csInt 3))] ρ (m := 4) (k' := 1)
    (csFile_lookup_f ra bty ybty) rfl rfl (Nat.le_refl 6)
  dsimp only [csSpecT]
  isplitl []
  · ipureintro
    exact ⟨Nat.le_refl 4, 3, rfl, by decide⟩
  · iintro %ret %hpost
    obtain ⟨x, hx, rfl⟩ := hpost
    obtain rfl : x = 3 := (csInt_inj (List.cons.inj hx).1).symm
    rw [show Expr [] (Epure (Pexpr [] () (PEval (csInt (3 + 1))))) =
      ofVal (.pure (csInt (3 + 1))) from rfl]
    iapply wpt_ofVal _ _ (Nat.le_refl 1)
    dsimp only [csPost]
    ipureintro
    rfl

/-- The collapse into Iris TWP with the total table (`wpt_sound`). -/
theorem cs_twp_readout (ℓ : exec_location) :
    ⊢ WP (⟨csMainBody ra, [fmapEmpty], ⟨[], some csMain, ℓ⟩, csCtx ra bty ybty⟩ : CoreRt)
        @ Stuckness.NotStuck; ⊤ [{ w, csPost (GF := GF) w.w w.ρ }] := by
  refine (csMain_wpt ra bty ybty [fmapEmpty]).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((BI.emp_sep.2.trans (BI.sep_mono (csCtx_procSpecsT ra bty ybty) (cs_blockSpecsT ra bty ybty))).trans
      (wpt_sound (ctl := ⟨[], some csMain, ℓ⟩) rfl 6 (csMainBody ra) [fmapEmpty])) .rfl)).trans ?_
  exact BI.wand_elim_left

end CerberusHeapLang
