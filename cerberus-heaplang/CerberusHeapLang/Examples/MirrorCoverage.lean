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
operand, `kill_sym_step`. The engine's ACTION_EVAL arm for `store` fires
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

set_option autoImplicit false

namespace CerberusHeapLang

open Lem_Basic_classes Lem_Maybe Lem_List

/-! ## The mixed operand shapes of `store` (coverage witnesses at the
mirror) -/

/-- `store(ty, x, v)` — SYMBOL pointer, LITERAL value — steps. -/
theorem store_sym_lit_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {x : sym} {cv : value}
    {mo : memory_order} {ρ : EnvStack} {σ : Mem} {pv : CerbMem.PointerValue}
    (hx : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym x)) =
      some (Vobject (OVpointer pv))) :
    Step M (storeOpRedex loc ann ty (Pexpr [] () (PEsym x))
        (Pexpr [] () (PEval cv)) mo, ρ, σ)
      (storeExpr loc ann ty pv cv mo, ρ, σ) :=
  Step.store_eval rfl hx rfl

/-- `store(ty, p, y)` — LITERAL pointer, SYMBOL value — steps. -/
theorem store_lit_sym_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {ty : ctype} {pv : CerbMem.PointerValue}
    {y : sym} {mo : memory_order} {ρ : EnvStack} {σ : Mem} {cv : value}
    (hy : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym y)) = some cv) :
    Step M (storeOpRedex loc ann ty (Pexpr [] () (PEval (Vobject (OVpointer pv))))
        (Pexpr [] () (PEsym y)) mo, ρ, σ)
      (storeExpr loc ann ty pv cv mo, ρ, σ) :=
  Step.store_eval rfl rfl hy

/-! ## The kill ACTION_EVAL shape (kill/free arc K2): `kill(static ty, x)`
at a SYMBOL operand — the engine's `none` arm of step_action's Kill case
(the operand is not a value) is covered by `Step.kill_eval`, whose
successor is the canonical kill redex. -/

/-- `kill(static ty, x)` — SYMBOL pointer operand — steps to the
    evaluated kill. -/
theorem kill_sym_step {M : MachineCtx} {loc : CerbLocation.Loc}
    {ann : core_run_annotation} {kind : kill_kind} {x : sym}
    {ρ : EnvStack} {σ : Mem} {pv : CerbMem.PointerValue}
    (hx : evalPexpr M.tagDefs M.extern ρ (Pexpr [] () (PEsym x)) =
      some (Vobject (OVpointer pv))) :
    Step M (killOpRedex loc ann kind (Pexpr [] () (PEsym x)), ρ, σ)
      (killRedex loc ann kind pv, ρ, σ) :=
  Step.kill_eval rfl hx

end CerberusHeapLang
