/-
CerberusHeapLang.Examples.MirrorCoverage — MIRROR-LEVEL COVERAGE
WITNESSES. NOT A CLIENT OF THE LOGIC.

This module holds theorems proved directly against the mirror relation
`Step` (Step.lean): regression witnesses that a construct shape the
engine dispatches is covered by a mirror rule. They are semantic
regression tests of the mirror's coverage, not program proofs — a
client of the logic imports `CerberusHeapLang.API` and reasons through
the public rules only, never through `Step` (API.lean, "Below the
line"). Consequently this module imports the semantics layer, not the
API, and no exhibit imports it.

Contents (moved here verbatim from ProdExhibit.lean, 2026-09-02
detailed audit L-2 — statements unchanged): the two MIXED operand
shapes of `store`; plus (kill/free arc K2) the kill at a symbol
operand, `kill_sym_step`; plus (calls arc C2) THE PROCEDURE CALL AND
RETURN ROUNDS at the mirror level on a two-procedure file — `main`
calls `f`, `f` returns a constant — as `engine_step_matchU` instances
(`smoke_call_round`, `smoke_ret_round`): the shipped driver's round at
the call IS `Step.call`'s successor (the callee installed, the frame
pushed, the caller's control captured) and at the callee's value IS
`Step.ret`'s (the value plugged into the captured context, the frame
popped). NOT a client of a rule — there is no call rule yet (C3). Plus
(dialect arc E1, 2026-09-05) the live-location witnesses at the MIRROR
level — `loc_update_nonlib`/`_lib`/`_none` are lemmas about `Ctl.upd`
alone and `store_located_step` is a `Step` witness; none touches the
engine — and the ENGINE-round witnesses, `engine_step_matchU` instances at
a generic machine context: the REMOVE-BOUND rounds (`bound_annot_round`,
`bound_pure_round`), the create ACTION_EVAL round at `Ivalignof`
(`create_alignof_round`) and the LETS-ANNOT round at the plain-symbol
binder (`sseq_sym_annot_round`) (the E1 range audit's R-3,
docs/2026-09-05_audit-e1-range.md). The engine's ACTION_EVAL arm for `store` fires
whenever the operand triple is NOT all values; the mirror's
`Step.store_eval` covers every such shape, and these two witnesses
pin the two mixed ones (symbol pointer / literal value, literal
pointer / symbol value) — the "not all values" premise by `rfl`. The
rule-level instances at the same shapes (`wps_store_sym_lit`,
`wpt_store_lit_sym`) stay in ProdExhibit.lean: they are proved through
the public `wps_store_eval`/`wpt_store_eval`, which is what a client
does.

The other permitted direct use of `Step` outside the semantics layer
is the NEGATIVE test `DivergeExhibit.lean` (`dg_self_step`, by
`Step.run`): a negative test shows a derivation is impossible by
exhibiting the engine's actual behaviour, and the engine's behaviour
at the self-jump is reached through the certified mirror step — the
exception is stated in that module's header.
-/
import CerberusHeapLang.Rules
import CerberusHeapLang.Round

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-! ## The mixed operand shapes of `store` (coverage witnesses at the
mirror) -/

/-- `store(ty, x, v)` — SYMBOL pointer, LITERAL value — steps. -/
theorem store_sym_lit_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {x : sym} {cv : value}
    {mo : memory_order} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {pv : CerbMem.PointerValue}
    (hx : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym x)) =
      some (Vobject (OVpointer pv))) :
    Step M (storeOpRedex [] loc ann ty (Pexpr [] () (PEsym x))
        (Pexpr [] () (PEval cv)) mo, ρ, ctl, σ)
      (storeExpr [] loc ann ty pv cv mo, ρ, ctl, σ) :=
  Step.store_eval rfl hx rfl

/-- `store(ty, p, y)` — LITERAL pointer, SYMBOL value — steps. -/
theorem store_lit_sym_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {y : sym} {mo : memory_order} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {cv : value}
    (hy : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym y)) = some cv) :
    Step M (storeOpRedex [] loc ann ty (Pexpr [] () (PEval (Vobject (OVpointer pv))))
        (Pexpr [] () (PEsym y)) mo, ρ, ctl, σ)
      (storeExpr [] loc ann ty pv cv mo, ρ, ctl, σ) :=
  Step.store_eval rfl rfl hy

/-! ## The kill ACTION_EVAL shape (kill/free arc K2): `kill(static ty, x)`
at a SYMBOL operand — the engine's `none` arm of step_action's Kill case
(the operand is not a value) is covered by `Step.kill_eval`, whose
successor is the canonical kill redex. -/

/-- `kill(static ty, x)` — SYMBOL pointer operand — steps to the
    evaluated kill. -/
theorem kill_sym_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {kind : kill_kind} {x : sym}
    {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {pv : CerbMem.PointerValue}
    (hx : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym x)) =
      some (Vobject (OVpointer pv))) :
    Step M (killOpRedex [] loc ann kind (Pexpr [] () (PEsym x)), ρ, ctl, σ)
      (killRedex [] loc ann kind pv, ρ, ctl, σ) :=
  Step.kill_eval rfl hx

/-! ## The alloc ACTION_EVAL shape (kill/free arc K3): `alloc(al, n)` at a
SYMBOL size operand and a LITERAL alignment — the engine's `_, _` arm of
step_action's Alloc0 case (the pair is not all values) is covered by
`Step.alloc_eval`, whose successor is the canonical alloc redex. -/

/-- `alloc(al, n)` — LITERAL alignment, SYMBOL size — steps to the
    evaluated alloc. -/
theorem alloc_lit_sym_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {align size : CerbMem.IntegerValue} {n : sym}
    {pref : prefix0} {ρ : EnvStack} {ctl : Ctl} {σ : Mem}
    (hn : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym n)) =
      some (Vobject (OVinteger size))) :
    Step M (allocOpRedex [] loc ann (Pexpr [] () (PEval (Vobject (OVinteger align))))
        (Pexpr [] () (PEsym n)) pref, ρ, ctl, σ)
      (allocRedex [] loc ann align size pref, ρ, ctl, σ) :=
  Step.alloc_eval rfl rfl hn

/-! ## The procedure call and return (calls arc C2): the two rounds on a
two-procedure file, at the mirror level

`smokeFile` declares `main` (body: `f()`, the call redex at the root) and
`f` (body: the constant `Vtrue`). No rule is applied — these are the
CERTIFICATION instances: `engine_step_matchU` at `Step.call` and at
`Step.ret`, i.e. the shipped driver's round at the call configuration is
the callee's body at the pushed control, and at the callee's value it is
the caller's plugged context at the popped control. -/

/-- The startup symbol of the smoke file. -/
def smokeMain : sym := Symbol "" 0 SD_None

/-- The callee. -/
def smokeF : sym := Symbol "" 1 SD_None

/-- `f`'s body: a constant. -/
def smokeFBody : CoreExpr := Expr [] (Epure (Pexpr [] () (PEval Vtrue)))

/-- The two-procedure file: `main ↦ Proc … [] (f())`, `f ↦ Proc … []
    Vtrue`; no stdlib, no externs. -/
def smokeFile (ra : core_run_annotation) : file core_run_annotation :=
  { main := some smokeMain,
    calling_convention0 := default,
    tagDefs := default,
    stdlib := fmapEmpty,
    impl0 := fmapEmpty,
    globs := [],
    funs := fmapAddBy (fun (s1 : sym) (s2 : sym) => ordCompare s1 s2) smokeF
      (Proc CerbLocation.unknown none BTy_boolean [] smokeFBody)
      (fmapAddBy (fun (s1 : sym) (s2 : sym) => ordCompare s1 s2) smokeMain
        (Proc CerbLocation.unknown none BTy_boolean [] (callRedex [] ra smokeF []))
        fmapEmpty),
    extern := fmapEmpty,
    funinfo := fmapEmpty,
    loop_attributes1 := default,
    visible_objects_env0 := default }

/-- The straight-line profile over the smoke file. -/
@[reducible] def smokeCtx (ra : core_run_annotation) : MachineCtx :=
  { spikeCtx with file := smokeFile ra }

/-- `call_proc`'s lookup finds `f` (computed). -/
theorem smokeFile_lookup_f (ra : core_run_annotation) :
    lookupProc (smokeFile ra) fmapEmpty smokeF = some ([], smokeFBody) := rfl

/-- THE CALL ROUND: at `main`'s body (the call redex at the root, `κ = []`),
    the shipped driver's round installs `f`'s body at the pushed control
    `⟨[(some main, CTX)], some f, push_exec_loc f …⟩` with the fresh empty
    frame — exactly `Step.call`'s successor. -/
theorem smoke_call_round (ra : core_run_annotation) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (ℓ : exec_location) (σ : Mem) :
    CerberusRound (smokeCtx ra) (callRedex [] ra smokeF [], ev0 :: evs, ⟨[], some smokeMain, ℓ, default, default⟩, σ)
      (smokeFBody, procEnv [] [] :: (ev0 :: evs),
       ⟨[(some smokeMain, CTX)], some smokeF, push_exec_loc smokeF default ℓ, default, default⟩, σ) :=
  engine_step_matchU (Frag.call (fun _ h => by cases h) (fun _ h => by cases h))
    (by rw [show esize (callRedex [] ra smokeF []) = 1 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (Step.call rfl rfl (smokeFile_lookup_f ra) rfl)

/-- THE RETURN ROUND: at `f`'s value under the captured frame, the shipped
    driver's round pops the frame, restores `main`, drops `f`'s env frame
    and plugs the value into the captured context — exactly `Step.ret`'s
    successor. -/
theorem smoke_ret_round (ra : core_run_annotation) (v : value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (ℓ : exec_location) (σ : Mem) :
    CerberusRound (smokeCtx ra) (ofVal (.pure v), ev0 :: evs,
        ⟨[(some smokeMain, CTX)], some smokeF, ℓ, default, default⟩, σ)
      (apply_ctx CTX (ofVal (.pure v)), evs, ⟨[], some smokeMain, ℓ, default, default⟩, σ) :=
  engine_step_matchU (frag_ofVal _)
    (by rw [show esize (ofVal (.pure v)) = 1 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    Step.ret

/-! ## E1 witnesses (dialect arc, docs/2026-09-04_e1-notes.md): the live
location, REMOVE-BOUND, the create ACTION_EVAL at `Ivalignof`, LETS-ANNOT
at the plain-symbol binder -/

/-- THE LOCATION UPDATE (Core_reduction.lean:484 `get_loc`): a general-arm
    round at a node whose first `Aloc` is a NON-library location moves the
    control's `curLoc` to it. -/
theorem loc_update_nonlib (ctl : Ctl) (l : CerbLocation.Loc)
    (hl : CerbLocation.isLibraryLocation l = false) (rest : List annot) :
    (ctl.upd (Aloc l :: rest)).curLoc = l := by
  simp only [Ctl.upd_curLoc, locUpd, get_loc, hl, Bool.false_eq_true, ↓reduceIte]

/-- … a LIBRARY location leaves it (`is_library_location`, the engine's
    filter of libcore/include/impls positions). -/
theorem loc_update_lib (ctl : Ctl) (l : CerbLocation.Loc)
    (hl : CerbLocation.isLibraryLocation l = true) (rest : List annot) :
    (ctl.upd (Aloc l :: rest)).curLoc = ctl.curLoc := by
  simp only [Ctl.upd_curLoc, locUpd, get_loc, hl, ↓reduceIte]

/-- … and a node without an `Aloc` (the `Astd`/`Astmt`/`Aexpr` residue) is
    inert on the location. -/
theorem loc_update_none (ctl : Ctl) :
    (ctl.upd [Astd "§6.5#2", Astmt, Aexpr]).curLoc = ctl.curLoc := rfl

/-- A LOCATED `store` ACTION_EVAL round: the successor control is the
    location-updated one (`Step.store_eval` at a non-empty list). -/
theorem store_located_step {M : MachineCtx} (l : CerbLocation.Loc) {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {x : sym} {cv : value}
    {mo : memory_order} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {pv : CerbMem.PointerValue}
    (hx : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym x)) =
      some (Vobject (OVpointer pv))) :
    Step M (storeOpRedex [Aloc l, Aexpr] loc ann ty (Pexpr [] () (PEsym x))
        (Pexpr [] () (PEval cv)) mo, ρ, ctl, σ)
      (storeExpr [Aloc l, Aexpr] loc ann ty pv cv mo, ρ, ctl.upd [Aloc l, Aexpr], σ) :=
  Step.store_eval rfl hx rfl

/-- REMOVE-BOUND at an ANNOTATED value: the shipped driver's round at
    `bound({A}v)` delivers `v` BARE — the dynamic annotations are dropped
    (core_reduction.lem:1214–1219) — and updates the location. -/
theorem bound_annot_round {M : MachineCtx} (a a1 a2 b1 : List annot)
    (ds : List dyn_annotation) (v : value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    CerberusRound M (Expr a (Ebound (ofValA (.annot a1 a2 b1 ds v))), ev0 :: evs, ctl, σ)
      (ofValA (.pure a2 b1 v), ev0 :: evs, ctl.upd a, σ) :=
  engine_step_matchU (Frag.bound (frag_ofValA _))
    (by rw [esize_bound, show esize (ofValA (SpikeValA.annot a1 a2 b1 ds v)) = 2 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    Step.bound_annot

/-- REMOVE-BOUND at a BARE value (core_reduction.lem:1221–1226). -/
theorem bound_pure_round {M : MachineCtx} (a a1 b1 : List annot) (v : value)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    CerberusRound M (Expr a (Ebound (ofValA (.pure a1 b1 v))), ev0 :: evs, ctl, σ)
      (ofValA (.pure a1 b1 v), ev0 :: evs, ctl.upd a, σ) :=
  engine_step_matchU (Frag.bound (frag_ofValA _))
    (by rw [esize_bound, show esize (ofValA (SpikeValA.pure a1 b1 v)) = 1 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    Step.bound_pure

/-- THE CREATE ACTION_EVAL ROUND at the emitted operands
    `create(Ivalignof(ty), ty)` (core_reduction.lem:657–661): the round
    rewrites the redex to the canonical create at the evaluator's own
    alignment constant `alignofIval M.tagDefs ty`. -/
theorem create_alignof_round {M : MachineCtx} (a : List annot) (loc : CerbLocation.Loc)
    (ann : core_run_annotation) (ty : ctype) (pref : prefix0)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    CerberusRound M
      (createOpRedex a loc ann (Pexpr [] () (PEctor Civalignof [Pexpr [] () (PEval (Vctype ty))]))
        (Pexpr [] () (PEval (Vctype ty))) pref, ev0 :: evs, ctl, σ)
      (createRedex a loc ann (CerbMem.alignofIval M.tagDefs ty) ty pref, ev0 :: evs, ctl.upd a, σ) :=
  engine_step_matchU
    (Frag.create_op rfl (.ctorTy [] Civalignof rfl [] ty) (.val [] (Vctype ty))
      (by rw [show peDepth (Pexpr ([] : List annot) ()
          (PEctor Civalignof [Pexpr [] () (PEval (Vctype ty))])) = 2 from rfl,
        show lemDefaultFuel = 999999 + 1 from rfl]; omega)
      (peDepth_val_le _ _))
    (by rw [show esize (createOpRedex a loc ann
        (Pexpr [] () (PEctor Civalignof [Pexpr [] () (PEval (Vctype ty))]))
        (Pexpr [] () (PEval (Vctype ty))) pref) = 1 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (Step.create_eval rfl (by rw [evalPexpr_tyctor, evalTyCtor_alignof]) rfl)

/-- LETS-ANNOT AT THE PLAIN-SYMBOL BINDER (core_reduction.lem's second
    LETS beta): the round binds the BARE value and re-wraps the dynamic
    annotations around the continuation — mirrored since E1
    (`Step.sseq_sym_annot`; the pre-E1 `BareHead` exclusion is retired). -/
theorem sseq_sym_annot_round {M : MachineCtx} (a pa a1 a2 b1 : List annot) (x : sym)
    (bty : core_base_type) (ds : List dyn_annotation) (v : value)
    (ev0 : Fmap sym value) (evs : List (Fmap sym value)) (ctl : Ctl) (σ : Mem) :
    CerberusRound M
      (Expr a (Esseq (symPat pa x bty) (ofValA (.annot a1 a2 b1 ds v))
        (ofValA (.pure [] [] Vunit))), ev0 :: evs, ctl, σ)
      (Expr [] (Eannot ds (ofValA (.pure [] [] Vunit))),
        update_env (symPat pa x bty) v (ev0 :: evs), ctl.upd a, σ) :=
  engine_step_matchU (Frag.sseq_sym (frag_ofValA _) (frag_ofValA _))
    (by rw [show esize (Expr a (Esseq (symPat pa x bty) (ofValA (SpikeValA.annot a1 a2 b1 ds v))
        (ofValA (SpikeValA.pure [] [] Vunit)))) = 3 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    Step.sseq_sym_annot

end CerberusHeapLang
