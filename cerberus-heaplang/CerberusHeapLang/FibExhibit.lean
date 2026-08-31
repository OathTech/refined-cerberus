/-
CerberusHeapLang.FibExhibit — phase-2 S4, ACCEPTANCE EXHIBIT 1: FIB
end-to-end (two-phase arc plan §Phase 2 + the [USER] acceptance
amendment — "fib + an array-walk exhibit").

THE PROGRAM (authored Core, iterative two-accumulator form; run
annotation quantified):

    save loop: (i : integer := 0, a : integer := 0, b : integer := 1) in
      if (i < n) then run loop(i + 1, b, a + b) else pure(a)

- Esave binds THREE parameters (the S3 exhibit's machinery at width
  3 — the env-map seam pays: no frame-shape pins, the invariant
  carries `SymFrame` + the lookup law).
- The guard `i < n` and the back-edge arguments `i+1`, `b`, `a+b`
  evaluate through the certified pure evaluator; the back edge is
  the context-discarding Erun.
- The exit `pure(a)` DELIVERS THE ACCUMULATOR through the S4 PURE
  rule (`wps_pure` / `Step.pure_eval` — one big-step engine
  evaluation of the exit expression).
- VERIFIED via the per-label invariant rule (`blockSpecs_intro`)
  with THE DATA-DEPENDENT INVARIANT `a = fib i ∧ b = fib (i+1)`
  (`fibSpec` — the Lean-side specification function), collapsed by
  `wps_sound`, EXPORTED through `engine_adequacyJ`: the engine's
  driveJ from the proc-carrying thread never kills, never derails,
  and any delivered value IS `fib n` — at ANY initial memory (the
  program touches no state; the seeded footprint is empty).
-/
import CerberusHeapLang.LoopExhibit

set_option autoImplicit false

namespace CerberusHeapLang

open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
open Lem_Basic_classes Lem_Map

/-! ## The specification function -/

/-- Lean-side fib (the exhibit's mathematical referent). -/
def fibSpec : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)

@[simp] theorem fibSpec_zero : fibSpec 0 = 0 := rfl
@[simp] theorem fibSpec_one : fibSpec 1 = 1 := rfl
theorem fibSpec_add_two (n : Nat) :
    fibSpec (n + 2) = fibSpec n + fibSpec (n + 1) := rfl

/-! ## The program -/

def fibISym : sym := Symbol "" 201 SD_None
def fibASym : sym := Symbol "" 202 SD_None
def fibBSym : sym := Symbol "" 203 SD_None
def fibLoopSym : sym := Symbol "" 204 SD_None
def fibProcSym : sym := Symbol "" 205 SD_None

/-- The guard `i < n`. -/
def fibGuard (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpLt (Pexpr [] () (PEsym fibISym))
    (Pexpr [] () (PEval (ivVal n))))

/-- Back-edge argument `i + 1`. -/
def fibIncPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpAdd (Pexpr [] () (PEsym fibISym))
    (Pexpr [] () (PEval (ivVal 1))))

/-- Back-edge argument `b`. -/
def fibBPe : generic_pexpr Unit sym := Pexpr [] () (PEsym fibBSym)

/-- Back-edge argument `a + b`. -/
def fibABPe : generic_pexpr Unit sym :=
  Pexpr [] () (PEop binop.OpAdd (Pexpr [] () (PEsym fibASym))
    (Pexpr [] () (PEsym fibBSym)))

/-- The exit expression `pure(a)`. -/
def fibExitPe : generic_pexpr Unit sym := Pexpr [] () (PEsym fibASym)

/-- The registered loop body. -/
def fibBody (ra : core_run_annotation) (n : Int) : CoreExpr :=
  Expr [] (Eif (fibGuard n)
    (Expr [] (Erun ra fibLoopSym [fibIncPe, fibBPe, fibABPe]))
    (Expr [] (Epure fibExitPe)))

/-- The save-parameter list (value initializers `0, 0, 1`). -/
def fibParams (ibty abty bbty : core_base_type) :
    List (sym × ((core_base_type ×
      Option (ctype × pass_by_value_or_pointer)) × generic_pexpr Unit sym)) :=
  [(fibISym, ((ibty, none), Pexpr [] () (PEval (ivVal 0)))),
   (fibASym, ((abty, none), Pexpr [] () (PEval (ivVal 0)))),
   (fibBSym, ((bbty, none), Pexpr [] () (PEval (ivVal 1))))]

/-- The whole program. -/
def fibProg (ra : core_run_annotation) (n : Int)
    (sbty ibty abty bbty : core_base_type) : CoreExpr :=
  Expr [] (Esave (fibLoopSym, sbty) (fibParams ibty abty bbty)
    (fibBody ra n))

/-- The label map: `loop` registered with the body (trailing-position
    save registration discipline, as in the S3 counter loop). -/
def fibQ (ra : core_run_annotation) (n : Int)
    (ibty abty bbty : core_base_type) : LabelMap :=
  fmapAddBy symCmpL fibLoopSym
    ([(fibISym, ibty), (fibASym, abty), (fibBSym, bbty)], fibBody ra n)
    fmapEmpty

/-- The run state carrying the two-level `labeled` tie. -/
def fibRS (ra : core_run_annotation) (n : Int)
    (ibty abty bbty : core_base_type) : core_run_state :=
  { spikeRunState with
      labeled := fmapAddBy symCmpL fibProcSym
        (fibQ ra n ibty abty bbty) fmapEmpty }

section FibFacts

variable (ra : core_run_annotation) (n : Int)
  (ibty abty bbty : core_base_type)

theorem fibQ_lookup :
    lookupLabel (fibQ ra n ibty abty bbty) fibLoopSym =
      some ([(fibISym, ibty), (fibASym, abty), (fibBSym, bbty)],
        fibBody ra n) := by
  unfold lookupLabel fibQ
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

theorem fibQ_inv {l : sym} {params : List (sym × core_base_type)}
    {cont : CoreExpr}
    (h : lookupLabel (fibQ ra n ibty abty bbty) l = some (params, cont)) :
    params = [(fibISym, ibty), (fibASym, abty), (fibBSym, bbty)] ∧
      cont = fibBody ra n := by
  unfold lookupLabel fibQ at h
  rw [fmapLookupBy_addBy_empty] at h
  split at h
  · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
    exact ⟨h1.symm ▸ rfl, h2.symm ▸ rfl⟩
  · cases h

theorem fibRS_labeledAt :
    LabeledAt (fibRS ra n ibty abty bbty) fibProcSym
      (fibQ ra n ibty abty bbty) := by
  unfold LabeledAt fibRS
  show fmapLookupBy _ _ (fmapAddBy symCmpL fibProcSym _ fmapEmpty) = _
  rw [fmapLookupBy_addBy_empty]
  rw [if_pos (by decide +kernel)]

end FibFacts

/-! ## The frame: three bindings over any reachable base frame
(the EnvLaws seam — SymFrame + the lookup law replace shape pins) -/

/-- The frame after binding (i, a, b). -/
def fibFrame (vi va vb : value) (f : Fmap sym value) : Fmap sym value :=
  envAdd fibBSym vb (envAdd fibASym va (envAdd fibISym vi f))

theorem fibFrame_symFrame {f : Fmap sym value} (hf : SymFrame f)
    (vi va vb : value) : SymFrame (fibFrame vi va vb f) :=
  ((hf.add _ _).add _ _).add _ _

theorem fibFrame_lookup_i {f : Fmap sym value} (hf : SymFrame f)
    (vi va vb : value) :
    fmapLookupBy symCmpK fibISym (fibFrame vi va vb f) = some vi := by
  unfold fibFrame
  rw [envAdd_lookup ((hf.add _ _).add _ _) symCmpK,
    if_neg (by decide +kernel),
    envAdd_lookup (hf.add _ _) symCmpK,
    if_neg (by decide +kernel),
    envAdd_lookup hf symCmpK,
    if_pos (by decide +kernel)]

theorem fibFrame_lookup_a {f : Fmap sym value} (hf : SymFrame f)
    (vi va vb : value) :
    fmapLookupBy symCmpK fibASym (fibFrame vi va vb f) = some va := by
  unfold fibFrame
  rw [envAdd_lookup ((hf.add _ _).add _ _) symCmpK,
    if_neg (by decide +kernel),
    envAdd_lookup (hf.add _ _) symCmpK,
    if_pos (by decide +kernel)]

theorem fibFrame_lookup_b {f : Fmap sym value} (hf : SymFrame f)
    (vi va vb : value) :
    fmapLookupBy symCmpK fibBSym (fibFrame vi va vb f) = some vb := by
  unfold fibFrame
  rw [envAdd_lookup ((hf.add _ _).add _ _) symCmpK,
    if_pos (by decide +kernel)]

/-! ## The binding computations at the concrete parameter lists -/

theorem bindSave_fib (ibty abty bbty : core_base_type)
    (f : Fmap sym value) (rest : List (Fmap sym value)) :
    bindSaveParams (fibParams ibty abty bbty)
        [ivVal 0, ivVal 0, ivVal 1] (f :: rest) =
      fibFrame (ivVal 0) (ivVal 0) (ivVal 1) f :: rest := by
  show update_env (mk_sym_pat fibBSym bbty) (ivVal 1)
    (update_env (mk_sym_pat fibASym abty) (ivVal 0)
      (update_env (mk_sym_pat fibISym ibty) (ivVal 0) (f :: rest))) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym, update_env_cons, update_env_aux_sym]
  rfl

theorem bindArgs_fib (ibty abty bbty : core_base_type)
    (v1 v2 v3 : value) (f : Fmap sym value)
    (rest : List (Fmap sym value)) :
    bindArgs [(fibISym, ibty), (fibASym, abty), (fibBSym, bbty)]
        [v1, v2, v3] (f :: rest) =
      fibFrame v1 v2 v3 f :: rest := by
  show update_env (mk_sym_pat fibBSym bbty) v3
    (update_env (mk_sym_pat fibASym abty) v2
      (update_env (mk_sym_pat fibISym ibty) v1 (f :: rest))) = _
  rw [update_env_cons, update_env_aux_sym, update_env_cons,
    update_env_aux_sym, update_env_cons, update_env_aux_sym]
  rfl

/-! ## Evaluation facts at the bound frame -/

section FibEval

variable {f : Fmap sym value} (hf : SymFrame f) (i a b : Int)
  (rest : List (Fmap sym value))

include hf

theorem fib_guard_eval (n : Int) :
    evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
        (fibGuard n) = some (boolValue (decide (i < n))) := by
  unfold fibGuard
  rw [evalPexpr_op]
  rw [show evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
      (Pexpr [] () (PEsym fibISym)) = some (ivVal i) from by
    rw [evalPexpr_sym]
    exact lookup_env_head (fibFrame_lookup_i hf _ _ _) rest]
  show evalBinop binop.OpLt (ivVal i) (ivVal n) = _
  rfl

theorem fib_args_eval :
    evalPexprs (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
        [fibIncPe, fibBPe, fibABPe] =
      some [ivVal (i + 1), ivVal b, ivVal (a + b)] := by
  have hi : evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
      (Pexpr [] () (PEsym fibISym)) = some (ivVal i) := by
    rw [evalPexpr_sym]
    exact lookup_env_head (fibFrame_lookup_i hf _ _ _) rest
  have ha : evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
      (Pexpr [] () (PEsym fibASym)) = some (ivVal a) := by
    rw [evalPexpr_sym]
    exact lookup_env_head (fibFrame_lookup_a hf _ _ _) rest
  have hb : evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
      (Pexpr [] () (PEsym fibBSym)) = some (ivVal b) := by
    rw [evalPexpr_sym]
    exact lookup_env_head (fibFrame_lookup_b hf _ _ _) rest
  rw [evalPexprs_cons]
  rw [show evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
      fibIncPe = some (ivVal (i + 1)) from by
    unfold fibIncPe
    rw [evalPexpr_op, hi]
    rfl]
  rw [evalPexprs_cons]
  rw [show evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
      fibBPe = some (ivVal b) from hb]
  rw [evalPexprs_cons]
  rw [show evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
      fibABPe = some (ivVal (a + b)) from by
    unfold fibABPe
    rw [evalPexpr_op, ha, hb]
    rfl]
  rfl

theorem fib_exit_eval :
    evalPexpr (fibFrame (ivVal i) (ivVal a) (ivVal b) f :: rest)
        fibExitPe = some (ivVal a) := by
  show evalPexpr _ (Pexpr [] () (PEsym fibASym)) = _
  rw [evalPexpr_sym]
  exact lookup_env_head (fibFrame_lookup_a hf _ _ _) rest

end FibEval

/-! ## The Iris layer: THE DATA-DEPENDENT INVARIANT -/

section FibIris

variable {hlc : HasLC} {GF : BundledGFunctors} [SpikeGS hlc GF]
variable (ra : core_run_annotation) (n : Int)
  (ibty abty bbty : core_base_type)

/-- The postcondition: the delivered value IS `fib n`. -/
abbrev fibPost : SpikeVal → EnvStack → IProp GF := fun w _ =>
  iprop(⌜w.val = ivVal (fibSpec n.toNat)⌝)

/-- THE PER-LABEL INVARIANT: the arguments are `(i, fib i,
    fib (i+1))` with `0 ≤ i ≤ n`, over ANY reachable frame
    (`SymFrame` — the EnvLaws seam; no shape pin). -/
abbrev fibLs : LabelSpec GF := fun _ vs ρ =>
  (iprop(∃ (i : Int) (f : Fmap sym value) (rest : List (Fmap sym value)),
    ⌜vs = [ivVal i, ivVal (fibSpec i.toNat), ivVal (fibSpec (i.toNat + 1))] ∧
      0 ≤ i ∧ i ≤ n ∧ ρ = f :: rest ∧ SymFrame f⌝) : IProp GF)

/-- The loop body verifies at any invariant frame. -/
theorem fib_body_wps (i : Int) (f : Fmap sym value)
    (rest : List (Fmap sym value)) (hf : SymFrame f)
    (h0 : 0 ≤ i) (hin : i ≤ n) :
    ⊢ wps (GF := GF) (fibQ ra n ibty abty bbty) (fibLs n) (fibPost n)
        (fibBody ra n)
        (fibFrame (ivVal i) (ivVal (fibSpec i.toNat))
          (ivVal (fibSpec (i.toNat + 1))) f :: rest) := by
  rw [show fibBody ra n = Expr [] (Eif (fibGuard n)
    (Expr [] (Erun ra fibLoopSym [fibIncPe, fibBPe, fibABPe]))
    (Expr [] (Epure fibExitPe))) from rfl]
  by_cases hlt : i < n
  · -- back edge at (i+1, fib(i+1), fib(i) + fib(i+1))
    iapply wps_if_true [] (fibGuard n) _ _ _
      (by rw [fib_guard_eval hf i _ _ rest n, decide_eq_true hlt]; rfl)
    iapply wps_run [] ra fibLoopSym [fibIncPe, fibBPe, fibABPe] _ _
      (fibQ_lookup ra n ibty abty bbty)
      (fib_args_eval hf i _ _ rest)
    iexists (i + 1), (fibFrame (ivVal i) (ivVal (fibSpec i.toNat))
      (ivVal (fibSpec (i.toNat + 1))) f), rest
    ipureintro
    refine ⟨?_, by omega, by omega, rfl, fibFrame_symFrame hf _ _ _⟩
    have h1 : (i + 1).toNat = i.toNat + 1 := by omega
    rw [h1, show i.toNat + 1 + 1 = i.toNat + 2 from rfl, fibSpec_add_two]
  · -- exit: i = n, deliver a = fib n
    have hz : i = n := by omega
    iapply wps_if_false [] (fibGuard n) _ _ _
      (by rw [fib_guard_eval hf i _ _ rest n,
        decide_eq_false hlt]; rfl)
    iapply wps_pure fibExitPe _ rfl (fib_exit_eval hf i _ _ rest)
    ipureintro
    show ivVal (fibSpec i.toNat) = ivVal (fibSpec n.toNat)
    rw [hz]

/-- THE BLOCK SPECIFICATION (per-label invariant rule, no Löb). -/
theorem fib_blockSpecs :
    ⊢ blockSpecs (GF := GF) (fibQ ra n ibty abty bbty) (fibLs n)
      (fibPost n) := by
  refine blockSpecs_intro fun l params cont vs ev0 evs hl => ?_
  obtain ⟨rfl, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
  iintro ⟨%i, %f, %rest, %hpure⟩
  obtain ⟨rfl, h0, hin, hρ, hf⟩ := hpure
  obtain ⟨rfl, rfl⟩ : f = ev0 ∧ rest = evs := by
    have h1 := congrArg (fun l => l.head?) hρ
    have h2 := congrArg (fun l => l.tail) hρ
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  rw [bindArgs_fib]
  exact fib_body_wps ra n ibty abty bbty i f rest hf h0 hin

/-- The whole program's statement WP from the entry env. -/
theorem fib_wps (hn : 0 ≤ n) (sbty : core_base_type) :
    ⊢ wps (GF := GF) (fibQ ra n ibty abty bbty) (fibLs n) (fibPost n)
        (fibProg ra n sbty ibty abty bbty) [fmapEmpty] := by
  rw [show fibProg ra n sbty ibty abty bbty =
    Expr [] (Esave (fibLoopSym, sbty) (fibParams ibty abty bbty)
      (fibBody ra n)) from rfl]
  iapply wps_save [] (fibLoopSym, sbty) _ _ fmapEmpty []
    (cvals := [ivVal 0, ivVal 0, ivVal 1]) rfl
  rw [bindSave_fib]
  have h := fib_body_wps (GF := GF) ra n ibty abty bbty 0 fmapEmpty []
    symFrame_empty (by omega) hn
  rw [show ((0 : Int)).toNat = 0 from rfl] at h
  exact h

/-- The base-WP face with the engine readout. -/
theorem fib_wp_readout (hn : 0 ≤ n) (sbty : core_base_type) :
    ⊢ WP (⟨fibProg ra n sbty ibty abty bbty, [fmapEmpty],
          fibQ ra n ibty abty bbty⟩ : CoreRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(∀ (σ' : Mem) (ns : Nat) (κs : List Empty) (nt : Nat),
          (stateInterp σ' ns κs nt : IProp GF) ={⊤, ∅}=∗
            ⌜CoreRVal.val w = ivVal (fibSpec n.toNat)⌝) }} := by
  refine (fib_wps ra n ibty abty bbty hn sbty).trans ?_
  refine (BI.emp_sep.2.trans (BI.sep_mono
    ((fib_blockSpecs ra n ibty abty bbty).trans
      (wps_sound (fibProg ra n sbty ibty abty bbty) [fmapEmpty]))
    .rfl)).trans ?_
  refine BI.wand_elim_left.trans ?_
  refine wp_mono fun w => ?_
  iintro %hval %σ' %ns %κs %nt Hσ
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  ipureintro
  exact hval

/-- The label bodies are in the certified cone. -/
theorem fibBody_fragJ : FragJ (fibBody ra n) := by
  refine .if_ (by
    rw [show peDepth (fibGuard n) = 2 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]
    omega) (.run ?_) .pure_sym
  intro pe hpe
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
  rcases hpe with rfl | rfl | rfl <;>
    (rw [show lemDefaultFuel = 999999 + 1 from rfl]
     first
      | (rw [show peDepth fibIncPe = 2 from rfl]; omega)
      | (rw [show peDepth fibBPe = 1 from rfl]; omega)
      | (rw [show peDepth fibABPe = 2 from rfl]; omega))

/-- The empty seeded footprint is coherent with ANY memory. -/
theorem coh_empty (σ : Mem) :
    Coh σ ((∅ : SpikeHeapF SpikeCell)) := by
  refine ⟨fun i c hg => ?_, fun i j c1 c2 hne h1 h2 => ?_⟩
  · rw [Iris.Std.LawfulPartialMap.get?_empty] at hg
    cases hg
  · rw [Iris.Std.LawfulPartialMap.get?_empty] at h1
    cases h1

end FibIris

/-! ## THE ACCEPTANCE THEOREM (engine vocabulary only in the
conclusion) -/

section FibDrive

variable (ra : core_run_annotation)
  (ibty abty bbty : core_base_type)

/-- FIB, END TO END: driving the REAL engine ({step_ctx →
    sequential discharge} at the proc-carrying thread, labels tied
    through `core_run_state.labeled`) on the authored two-accumulator
    fib loop, from ANY initial memory: the engine never kills, never
    derails, and any delivered value IS `fib n` (the Lean-side
    `fibSpec`). Partial correctness; the fuel hypotheses are the
    engine's own budgets (interim in-budget form — the
    termination-accounting export is the S4 driveJ-total theorem). -/
theorem fib_certified {GF : BundledGFunctors} [SpikeGpreS GF]
    (sbty : core_base_type) (n : Int) (hn : 0 ≤ n) (σ₀ : Mem)
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 3 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 2 + nsteps ≤ lemDefaultFuel) :
    let prog := fibProg ra n sbty ibty abty bbty
    let rs := fibRS ra n ibty abty bbty
    (∀ r, driveJ rs aids nsteps
      (procThread fibProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread fibProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread fibProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      v = ivVal (fibSpec n.toNat)) := by
  intro prog rs
  refine engine_adequacyJ (GF := GF)
    (fibRS_labeledAt ra n ibty abty bbty)
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
      exact fibBody_fragJ ra n)
    prog fmapEmpty [] σ₀ (∅ : SpikeHeapF SpikeCell)
    (.save (fibBody_fragJ ra n)) (coh_empty σ₀)
    (fun v _ => v = ivVal (fibSpec n.toNat))
    ?_ nsteps aids
    (by rw [show esize prog = 3 from rfl]; omega)
    (fun l params cont hl => by
      obtain ⟨-, rfl⟩ := fibQ_inv ra n ibty abty bbty hl
      rw [show esize (fibBody ra n) = 2 from rfl]
      omega)
  intro inst
  exact (BigSepM.bigSepM_empty).1.trans
    (fib_wp_readout ra n ibty abty bbty hn sbty)

/-! ## THE TERMINATION-ACCOUNTING EXPORT (S4 item 3): the variant's
step-bound product at the driveJ lane. The loop's variant `n − i`
prices each iteration at exactly TWO engine steps (the big-step
guard; the context-discarding jump); entry costs one (the save
TAU), the exit three (guard; the PURE evaluation; PROGRAM-DONE).
The bound `2·n + 4` discharges the in-budget hypotheses OUTRIGHT:
the theorem below is UNCONDITIONAL — no fuel hypotheses, no
partiality: driveJ at the concrete budget DELIVERS `fib n`, at any
initial memory and any action-id supply. (The general
variant-rule-to-bound theorem remains open — recorded in the slice
notes; this is the exhibit-level product, its induction measure IS
the variant.) -/

section FibTotal

/-- The loop segment: from any invariant state at counter `i`, the
    engine delivers `fib n` in exactly `2(n−i) + 3` steps. -/
theorem fib_loop_drive (n : Int) (i : Int) (h0 : 0 ≤ i) (hin : i ≤ n)
    (f : Fmap sym value) (hf : SymFrame f)
    (rest : List (Fmap sym value)) (σ : Mem) (aids : Nat → Nat) :
    driveJ (fibRS ra n ibty abty bbty) aids (2 * (n - i).toNat + 3)
      (procThread fibProcSym (fibBody ra n)
        (fibFrame (ivVal i) (ivVal (fibSpec i.toNat))
          (ivVal (fibSpec (i.toNat + 1))) f :: rest)) σ =
      .done (ivVal (fibSpec n.toNat)) σ := by
  have hQ := fibRS_labeledAt ra n ibty abty bbty
  have hszb : esize (fibBody ra n) ≤ lemDefaultFuel := by
    rw [show esize (fibBody ra n) = 2 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]
    omega
  suffices H : ∀ (k : Nat) (i : Int), 0 ≤ i → i ≤ n → (n - i).toNat = k →
      ∀ (f : Fmap sym value), SymFrame f →
      ∀ (rest : List (Fmap sym value)) (σ : Mem) (aids : Nat → Nat),
      driveJ (fibRS ra n ibty abty bbty) aids (2 * k + 3)
        (procThread fibProcSym (fibBody ra n)
          (fibFrame (ivVal i) (ivVal (fibSpec i.toNat))
            (ivVal (fibSpec (i.toNat + 1))) f :: rest)) σ =
        .done (ivVal (fibSpec n.toNat)) σ by
    have := H (n - i).toNat i h0 hin rfl f hf rest σ aids
    exact this
  intro k
  induction k with
  | zero =>
    intro i h0 hin hk f hf rest σ aids
    -- i = n: guard false, PURE exit, done
    have hz : i = n := by omega
    rw [show 2 * 0 + 3 = 0 + 1 + 1 + 1 from rfl]
    rw [driveJ_step hQ _ _ (fibBody_fragJ ra n) hszb
      (Step.if_false (g := fibGuard n)
        (e2 := Expr [] (Erun ra fibLoopSym [fibIncPe, fibBPe, fibABPe]))
        (e3 := Expr [] (Epure fibExitPe))
        (by rw [fib_guard_eval hf i _ _ rest n,
          decide_eq_false (by omega)]; rfl))]
    rw [driveJ_step hQ _ _
      (by exact FragJ.pure_sym :
        FragJ (Expr ([] : List _root_.annot) (Epure fibExitPe)))
      (by rw [show esize (Expr ([] : List _root_.annot) (Epure fibExitPe)) = 1
          from rfl, show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (Step.pure_eval rfl (fib_exit_eval hf i _ _ rest))]
    rw [show Expr ([] : List _root_.annot)
        (Epure (Pexpr [] () (PEval (ivVal (fibSpec i.toNat))))) =
      ofVal (.pure (ivVal (fibSpec i.toNat))) from rfl]
    rw [driveJ_done, hz]
  | succ k ih =>
    intro i h0 hin hk f hf rest σ aids
    -- i < n: guard true, jump, recurse at i+1
    have hlt : i < n := by omega
    rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 1 + 1 by omega]
    rw [driveJ_step hQ _ _ (fibBody_fragJ ra n) hszb
      (Step.if_true (g := fibGuard n)
        (e2 := Expr [] (Erun ra fibLoopSym [fibIncPe, fibBPe, fibABPe]))
        (e3 := Expr [] (Epure fibExitPe))
        (by rw [fib_guard_eval hf i _ _ rest n,
          decide_eq_true hlt]; rfl))]
    rw [driveJ_step hQ _ _
      (by
        refine FragJ.run ?_
        intro pe hpe
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpe
        rcases hpe with rfl | rfl | rfl <;>
          (rw [show lemDefaultFuel = 999999 + 1 from rfl]
           first
            | (rw [show peDepth fibIncPe = 2 from rfl]; omega)
            | (rw [show peDepth fibBPe = 1 from rfl]; omega)
            | (rw [show peDepth fibABPe = 2 from rfl]; omega)) :
        FragJ (Expr ([] : List _root_.annot)
          (Erun ra fibLoopSym [fibIncPe, fibBPe, fibABPe])))
      (by rw [show esize (Expr ([] : List _root_.annot)
          (Erun ra fibLoopSym [fibIncPe, fibBPe, fibABPe])) = 1 from rfl,
          show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (Step.run (by rfl) (fibQ_lookup ra n ibty abty bbty)
        (fib_args_eval hf i _ _ rest))]
    rw [bindArgs_fib]
    have harg : ivVal ((i : Int) + 1) = ivVal (i + 1) := rfl
    have hstep := ih (i + 1) (by omega) (by omega) (by omega)
      (fibFrame (ivVal i) (ivVal (fibSpec i.toNat))
        (ivVal (fibSpec (i.toNat + 1))) f)
      (fibFrame_symFrame hf _ _ _) rest σ
      (fun j => aids (j + 1 + 1))
    rw [show (i + 1).toNat = i.toNat + 1 by omega,
      show i.toNat + 1 + 1 = i.toNat + 2 from rfl, fibSpec_add_two] at hstep
    exact hstep

/-- FIB, TOTAL AND UNCONDITIONAL AT THE DRIVE LANE: at the concrete
    step budget `2·n + 4` the engine DELIVERS `fib n` — no fuel
    hypotheses, no partiality, any initial memory, any action-id
    supply. This is the termination-accounting product for the fib
    exhibit: the budget is the loop variant's step bound. -/
theorem fib_certified_total (sbty : core_base_type) (n : Int)
    (hn : 0 ≤ n) (σ₀ : Mem) (aids : Nat → Nat) :
    driveJ (fibRS ra n ibty abty bbty) aids (2 * n.toNat + 4)
      (procThread fibProcSym (fibProg ra n sbty ibty abty bbty)
        [fmapEmpty]) σ₀ =
      .done (ivVal (fibSpec n.toNat)) σ₀ := by
  have hQ := fibRS_labeledAt ra n ibty abty bbty
  rw [show 2 * n.toNat + 4 = (2 * n.toNat + 3) + 1 by omega]
  rw [show fibProg ra n sbty ibty abty bbty =
    Expr [] (Esave (fibLoopSym, sbty) (fibParams ibty abty bbty)
      (fibBody ra n)) from rfl]
  rw [driveJ_step hQ _ _
    (by exact FragJ.save (fibBody_fragJ ra n) :
      FragJ (Expr ([] : List _root_.annot)
        (Esave (fibLoopSym, sbty) (fibParams ibty abty bbty)
          (fibBody ra n))))
    (by rw [show esize (Expr ([] : List _root_.annot)
        (Esave (fibLoopSym, sbty) (fibParams ibty abty bbty)
          (fibBody ra n))) = 3 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (Step.save (cvals := [ivVal 0, ivVal 0, ivVal 1]) rfl)]
  rw [bindSave_fib]
  have h := fib_loop_drive ra ibty abty bbty n 0 (by omega) hn fmapEmpty
    symFrame_empty [] σ₀ (fun i => aids (i + 1))
  rw [show ((0 : Int)).toNat = 0 from rfl] at h
  rw [show (n - 0).toNat = n.toNat by omega] at h
  exact h

end FibTotal

end FibDrive

end CerberusHeapLang
