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
popped). NOT a client of a rule — there is no call rule yet (C3). The engine's ACTION_EVAL arm for `store` fires
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
    Step M (storeOpRedex loc ann ty (Pexpr [] () (PEsym x))
        (Pexpr [] () (PEval cv)) mo, ρ, ctl, σ)
      (storeExpr loc ann ty pv cv mo, ρ, ctl, σ) :=
  Step.store_eval rfl hx rfl

/-- `store(ty, p, y)` — LITERAL pointer, SYMBOL value — steps. -/
theorem store_lit_sym_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {y : sym} {mo : memory_order} {ρ : EnvStack} {ctl : Ctl} {σ : Mem} {cv : value}
    (hy : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym y)) = some cv) :
    Step M (storeOpRedex loc ann ty (Pexpr [] () (PEval (Vobject (OVpointer pv))))
        (Pexpr [] () (PEsym y)) mo, ρ, ctl, σ)
      (storeExpr loc ann ty pv cv mo, ρ, ctl, σ) :=
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
    Step M (killOpRedex loc ann kind (Pexpr [] () (PEsym x)), ρ, ctl, σ)
      (killRedex loc ann kind pv, ρ, ctl, σ) :=
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
    Step M (allocOpRedex loc ann (Pexpr [] () (PEval (Vobject (OVinteger align))))
        (Pexpr [] () (PEsym n)) pref, ρ, ctl, σ)
      (allocRedex loc ann align size pref, ρ, ctl, σ) :=
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
        (Proc CerbLocation.unknown none BTy_boolean [] (callRedex ra smokeF []))
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
    CerberusRound (smokeCtx ra) (callRedex ra smokeF [], ev0 :: evs, ⟨[], some smokeMain, ℓ⟩, σ)
      (smokeFBody, procEnv [] [] :: (ev0 :: evs),
       ⟨[(some smokeMain, CTX)], some smokeF, push_exec_loc smokeF default ℓ⟩, σ) :=
  engine_step_matchU (Frag.call (fun _ h => by cases h) (fun _ h => by cases h))
    (by rw [show esize (callRedex ra smokeF []) = 1 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    (Step.call rfl rfl (smokeFile_lookup_f ra) rfl)

/-- THE RETURN ROUND: at `f`'s value under the captured frame, the shipped
    driver's round pops the frame, restores `main`, drops `f`'s env frame
    and plugs the value into the captured context — exactly `Step.ret`'s
    successor. -/
theorem smoke_ret_round (ra : core_run_annotation) (v : value) (ev0 : Fmap sym value)
    (evs : List (Fmap sym value)) (ℓ : exec_location) (σ : Mem) :
    CerberusRound (smokeCtx ra) (ofVal (.pure v), ev0 :: evs,
        ⟨[(some smokeMain, CTX)], some smokeF, ℓ⟩, σ)
      (apply_ctx CTX (ofVal (.pure v)), evs, ⟨[], some smokeMain, ℓ⟩, σ) :=
  engine_step_matchU (frag_ofVal _)
    (by rw [show esize (ofVal (.pure v)) = 1 from rfl,
      show lemDefaultFuel = 999999 + 1 from rfl]; omega)
    Step.ret

end CerberusHeapLang
