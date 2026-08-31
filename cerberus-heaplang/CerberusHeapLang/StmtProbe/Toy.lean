/-
CerberusHeapLang.StmtProbe.Toy — S0 probe (two-phase arc plan,
docs/2026-08-31_two-phase-arc-plan.md), part 1 of 3: the toy language.

THIS IS THE ARCHITECTURE PROBE, NOT THE CORE MIRROR. Per the S0
charter (readiness review §5.0), the toy reproduces exactly the
engine-measured SHAPE that killed the `Language.Context`/wp_bind
sequencing route (readiness §3 R1), on a 5-construct language small
enough that every inversion is hand-provable:

- expressions with values (`val`), one state-touching action family
  (`load`/`store` on an integer heap — the corpus's two actions),
  big-step guarded branching (`ifz`, mirroring Eif's big-step guard,
  readiness §2.1 item 4), BINDING sequencing (`seq`, mirroring
  Esseq with a binder — the environment is LIVE, readiness R2), and
- `run l a`: the context-DISCARDING jump. Mirrored engine facts
  (readiness §2.1 items 1-3, step_ctx's Erun arm,
  Core_reduction.lean:484):
  * the label map is STATIC — registered once, never written on the
    sequential path. Here it rides in the runtime expression tuple
    (`TRt.fn`), exactly Caesium's `to_rtstmt rf s` carrying
    `rf_fn.f_code` (deps/refinedc lifting.v:1002); steps preserve it
    by construction of `primStep`.
  * `run` evaluates its argument against the CURRENT env, rebinds
    the label's parameter (`update_env (mk_sym_pat …)` fold), and
    replaces the WHOLE expression by the registered body — no
    `apply_ctx`. The surrounding `seq` spine is thrown away.
  * jump successors are context-INDEPENDENT: `Step.jump`'s target
    `(k, bindPat px z ρ, σ)` does not mention the frame stack `K`.
    This is the fact the jump-aware sequencing proof cashes in
    (Wps.lean).
  * registered bodies are understood as sseq-EXTENDED continuations
    (m_collect_saves_aux, Core_aux.lean:843/853): a label body is
    the save body PLUS the rest of the procedure, which is what
    makes discarding the context correct. The toy takes this as the
    label-map DISCIPLINE (the demo registers such a body); the
    metatheory does not need it.

The environment sits in the language expression tuple, not the Iris
state (readiness R2's recommended shape): env updates are
deterministic and state-independent, so `Mem`-side machinery is
untouched and values carry their final env (`TRVal`).

Deliberately OUT of the toy (probe-scope minimality, arc plan S0):
save-entry steps (registration is pre-run; entry is an ordinary
EXTEND-class rule), annotations, weak sequencing, ND, fuel — none
interact with the jump kernel being probed.
-/
import Iris

set_option autoImplicit false

namespace CerberusHeapLang
namespace StmtProbe

open Iris Iris.ProgramLogic

/-! ## Syntax -/

/-- Environments: association lists over numbered binders, head wins
    (the toy image of the engine's env frame; within a procedure the
    head frame grows monotonically, readiness §2.1 item 6). -/
abbrev TEnv := List (Nat × Int)

/-- Operands ("pexprs"): evaluated BIG-STEP against the env, the
    toy image of `full_eval_pexpr` (one engine step evaluates the
    whole operand; readiness §2.1 items 4/7). -/
inductive TOp where
  | lit  (z : Int)
  | var  (x : Nat)
  | add1 (o : TOp)
  | sub1 (o : TOp)

def lookupEnv : TEnv → Nat → Option Int
  | [], _ => none
  | (y, v) :: ρ, x => if x = y then some v else lookupEnv ρ x

def evalOp (ρ : TEnv) : TOp → Option Int
  | .lit z => some z
  | .var x => lookupEnv ρ x
  | .add1 o => (evalOp ρ o).map (· + 1)
  | .sub1 o => (evalOp ρ o).map (· - 1)

inductive TExpr where
  /-- a finished computation -/
  | val   (z : Int)
  /-- read the heap cell addressed by `ℓ` -/
  | load  (ℓ : TOp)
  /-- write the value of `v` to the (live) cell addressed by `ℓ`;
      returns the written value -/
  | store (ℓ v : TOp)
  /-- branch on a big-step-evaluated guard (`Eif` shape) -/
  | ifz   (g : TOp) (e1 e2 : TExpr)
  /-- `lets px = e1 in e2` — binding strong sequencing (`Esseq`) -/
  | seq   (px : Option Nat) (e1 e2 : TExpr)
  /-- context-discarding jump to registered label `l`, rebinding the
      label's parameter to the value of `a` (`Erun` shape) -/
  | run   (l : Nat) (a : TOp)

/-- Binder patterns: `none` = wildcard, `some x` = bind `x`
    (the engine's `update_env`, Core_aux.lean:861/868). -/
def bindPat : Option Nat → Int → TEnv → TEnv
  | none, _, ρ => ρ
  | some x, z, ρ => (x, z) :: ρ

/-- The static label map: label ↦ (parameter pattern, registered
    body). A function, never written after registration — the toy
    `core_run_state.labeled` / Caesium `f_code`. -/
abbrev TFn := Nat → Option (Option Nat × TExpr)

/-- The runtime expression tuple: label map (static, donor's
    `to_rtstmt rf`), expression, environment. -/
structure TRt where
  fn : TFn
  e  : TExpr
  ρ  : TEnv

/-- Values carry the final env (exported posts may project it away)
    and the (unchanged) label map. -/
structure TRVal where
  fn : TFn
  z  : Int
  ρ  : TEnv

/-- The toy heap functor/state (house `SpikeHeapF` shape,
    Heap.lean:44 — same key type and map representation, so the
    GenHeap instances are known-good). -/
abbrev THeapF := fun (V : Type) => Std.ExtTreeMap Int V compare
abbrev THeap := THeapF Int

/-! ## Values -/

def toValE : TExpr → Option Int
  | .val z => some z
  | _ => none

@[simp] theorem toValE_val (z : Int) : toValE (.val z) = some z := rfl
@[simp] theorem toValE_load (ℓ : TOp) : toValE (.load ℓ) = none := rfl
@[simp] theorem toValE_store (ℓ v : TOp) : toValE (.store ℓ v) = none := rfl
@[simp] theorem toValE_ifz (g : TOp) (e1 e2 : TExpr) :
    toValE (.ifz g e1 e2) = none := rfl
@[simp] theorem toValE_seq (px : Option Nat) (e1 e2 : TExpr) :
    toValE (.seq px e1 e2) = none := rfl
@[simp] theorem toValE_run (l : Nat) (a : TOp) : toValE (.run l a) = none := rfl

theorem toValE_eq_some {e : TExpr} {z : Int} (h : toValE e = some z) :
    e = .val z := by
  cases e <;> simp [toValE] at h
  rw [h]

/-! ## Contexts, redex search -/

/-- Evaluation frames: only the strong-sequencing left position, as
    in the certified fragment (`Csseq`, Lang.lean:57). The head of
    the list is the OUTERMOST frame. -/
abbrev TFrame := Option Nat × TExpr

def fill : List TFrame → TExpr → TExpr
  | [], e => e
  | (px, e2) :: K, e => .seq px (fill K e) e2

@[simp] theorem fill_nil (e : TExpr) : fill [] e = e := rfl

@[simp] theorem fill_cons (px : Option Nat) (e2 : TExpr) (K : List TFrame)
    (e : TExpr) : fill ((px, e2) :: K) e = .seq px (fill K e) e2 := rfl

/-- Structural jump-redex search: the leftmost-innermost position
    through the `seq` spine. `jumpRedex? (seq px e1 e2) = jumpRedex?
    e1` is the SYNTACTIC image of the engine's context-discard: the
    jump's successor is computed from the redex alone, so the search
    result — and with it the whole jump clause of the statement WP —
    is invariant under `seq` framing. -/
def jumpRedex? : TExpr → Option (Nat × TOp)
  | .run l a => some (l, a)
  | .seq _ e1 _ => jumpRedex? e1
  | _ => none

@[simp] theorem jumpRedex?_run (l : Nat) (a : TOp) :
    jumpRedex? (.run l a) = some (l, a) := rfl

@[simp] theorem jumpRedex?_seq (px : Option Nat) (e1 e2 : TExpr) :
    jumpRedex? (.seq px e1 e2) = jumpRedex? e1 := rfl

@[simp] theorem jumpRedex?_val (z : Int) : jumpRedex? (.val z) = none := rfl
@[simp] theorem jumpRedex?_load (ℓ : TOp) : jumpRedex? (.load ℓ) = none := rfl
@[simp] theorem jumpRedex?_store (ℓ v : TOp) :
    jumpRedex? (.store ℓ v) = none := rfl
@[simp] theorem jumpRedex?_ifz (g : TOp) (e1 e2 : TExpr) :
    jumpRedex? (.ifz g e1 e2) = none := rfl

theorem jumpRedex?_fill (K : List TFrame) (e : TExpr) :
    jumpRedex? (fill K e) = jumpRedex? e := by
  induction K with
  | nil => rfl
  | cons f K ih => obtain ⟨px, e2⟩ := f; simpa using ih

/-- The completeness direction of the search: a positive result IS a
    decomposition at a `run` redex. -/
theorem jumpRedex?_some_fill {e : TExpr} {l : Nat} {a : TOp}
    (h : jumpRedex? e = some (l, a)) : ∃ K, e = fill K (.run l a) := by
  induction e with
  | val z => simp [jumpRedex?] at h
  | load ℓ => simp [jumpRedex?] at h
  | store ℓ v => simp [jumpRedex?] at h
  | ifz g e1 e2 ih1 ih2 => simp [jumpRedex?] at h
  | seq px e1 e2 ih1 ih2 =>
    obtain ⟨K, rfl⟩ := ih1 (by simpa using h)
    exact ⟨(px, e2) :: K, rfl⟩
  | run l' a' =>
    obtain ⟨rfl, rfl⟩ : l' = l ∧ a' = a := by
      simpa [jumpRedex?] using h
    exact ⟨[], rfl⟩

theorem fill_eq_val {K : List TFrame} {e : TExpr} {z : Int}
    (h : TExpr.val z = fill K e) : K = [] ∧ e = .val z := by
  cases K with
  | nil => exact ⟨rfl, h.symm⟩
  | cons f K => obtain ⟨px, e2⟩ := f; exact absurd h (by simp)

/-- A non-`seq` expression only decomposes trivially. -/
theorem fill_eq_of_ne_seq {K : List TFrame} {e e0 : TExpr}
    (h0 : ∀ px a b, e0 ≠ .seq px a b) (h : e0 = fill K e) :
    K = [] ∧ e = e0 := by
  cases K with
  | nil => exact ⟨rfl, h.symm⟩
  | cons f K =>
    obtain ⟨px, e2⟩ := f
    exact absurd (by simpa using h) (h0 px (fill K e) e2)

/-! ## The step relation -/

/-- Head steps: the context-respecting redex contractions (the toy
    image of the engine's rebuilt-redex steps; readiness §2.1 —
    Eif/actions/betas are all singleton `get_ctx` roots). `run` is
    deliberately NOT a head step: the jump is global (`Step.jump`). -/
inductive HeadStep : TExpr → TEnv → THeap → TExpr → TEnv → THeap → Prop
  | load {ℓop : TOp} {a v : Int} {ρ : TEnv} {σ : THeap}
      (hℓ : evalOp ρ ℓop = some a)
      (hget : Iris.Std.PartialMap.get? σ a = some v) :
      HeadStep (.load ℓop) ρ σ (.val v) ρ σ
  | store {ℓop vop : TOp} {a v v0 : Int} {ρ : TEnv} {σ : THeap}
      (hℓ : evalOp ρ ℓop = some a) (hv : evalOp ρ vop = some v)
      (hget : Iris.Std.PartialMap.get? σ a = some v0) :
      HeadStep (.store ℓop vop) ρ σ (.val v) ρ
        (Iris.Std.PartialMap.insert σ a v)
  | ifz_zero {g : TOp} {e1 e2 : TExpr} {ρ : TEnv} {σ : THeap}
      (hg : evalOp ρ g = some 0) :
      HeadStep (.ifz g e1 e2) ρ σ e1 ρ σ
  | ifz_nonzero {g : TOp} {e1 e2 : TExpr} {z : Int} {ρ : TEnv} {σ : THeap}
      (hg : evalOp ρ g = some z) (hz : z ≠ 0) :
      HeadStep (.ifz g e1 e2) ρ σ e2 ρ σ
  | beta {px : Option Nat} {z : Int} {e2 : TExpr} {ρ : TEnv} {σ : THeap} :
      HeadStep (.seq px (.val z) e2) ρ σ e2 (bindPat px z ρ) σ

theorem HeadStep.toValE_none {e ρ σ e' ρ' σ'} (h : HeadStep e ρ σ e' ρ' σ') :
    toValE e = none := by
  cases h <;> rfl

theorem HeadStep.jumpRedex?_none {e ρ σ e' ρ' σ'}
    (h : HeadStep e ρ σ e' ρ' σ') : jumpRedex? e = none := by
  cases h <;> rfl

/-- The step relation, parameterized by the STATIC label map (never
    changes — mirror of `labeled` written once at registration).
    Constructors use equational conclusions so that inversion by
    `cases` is clean.

    `Step.jump` is the probe's point: the successor
    `(k, bindPat px z ρ, σ)` is computed from the redex and the
    current env alone — the frame stack `K` is DISCARDED, exactly
    step_ctx's Erun arm (no `apply_ctx ctx`). -/
inductive Step (fn : TFn) : TExpr × TEnv × THeap → TExpr × TEnv × THeap → Prop
  | head {K : List TFrame} {e ρ σ e' ρ' σ'} {eK eK' : TExpr}
      (h : HeadStep e ρ σ e' ρ' σ')
      (hK : eK = fill K e) (hK' : eK' = fill K e') :
      Step fn (eK, ρ, σ) (eK', ρ', σ')
  | jump {K : List TFrame} {l : Nat} {a : TOp} {px : Option Nat} {k : TExpr}
      {z : Int} {ρ : TEnv} {σ : THeap} {eK : TExpr}
      (hl : fn l = some (px, k)) (ha : evalOp ρ a = some z)
      (hK : eK = fill K (.run l a)) :
      Step fn (eK, ρ, σ) (k, bindPat px z ρ, σ)

/-- Values do not step (feeds `Language.val_stuck`). -/
theorem step_val_elim {fn : TFn} {z : Int} {ρ : TEnv} {σ : THeap}
    {out : TExpr × TEnv × THeap} (h : Step fn (.val z, ρ, σ) out) : False := by
  cases h with
  | head h hK hK' =>
    obtain ⟨-, heq⟩ := fill_eq_val hK
    subst heq
    cases h
  | jump hl ha hK =>
    obtain ⟨-, heq⟩ := fill_eq_val hK
    cases heq

/-- Jump-redex inversion — the semantic cash-in of context
    independence: at a configuration whose redex is a registered
    jump, EVERY step is THE jump, and its successor does not depend
    on the decomposition. (Head steps are excluded because head
    redexes are never jump redexes; the frame stack drops out
    because `Step.jump`'s successor never mentions it.) -/
theorem step_jump_inv {fn : TFn} {e : TExpr} {ρ : TEnv} {σ : THeap}
    {out : TExpr × TEnv × THeap} {l : Nat} {a : TOp}
    (hj : jumpRedex? e = some (l, a))
    (h : Step fn (e, ρ, σ) out) :
    ∃ px k z, fn l = some (px, k) ∧ evalOp ρ a = some z ∧
      out = (k, bindPat px z ρ, σ) := by
  cases h with
  | head h hK hK' =>
    subst hK
    rw [jumpRedex?_fill, h.jumpRedex?_none] at hj
    cases hj
  | @jump K l' a' px k z ρ' σ' eK hl ha hK =>
    subst hK
    rw [jumpRedex?_fill, jumpRedex?_run] at hj
    obtain ⟨rfl, rfl⟩ : l' = l ∧ a' = a := by
      simpa using hj
    exact ⟨_, _, _, hl, ha, rfl⟩

/-- Reducibility at a registered jump redex. -/
theorem step_of_jumpRedex {fn : TFn} {e : TExpr} {ρ : TEnv} {σ : THeap}
    {l : Nat} {a : TOp} {px : Option Nat} {k : TExpr} {z : Int}
    (hj : jumpRedex? e = some (l, a)) (hl : fn l = some (px, k))
    (ha : evalOp ρ a = some z) :
    Step fn (e, ρ, σ) (k, bindPat px z ρ, σ) := by
  obtain ⟨K, rfl⟩ := jumpRedex?_some_fill hj
  exact Step.jump hl ha rfl

/-- THE FACTOR THEOREM WITH THE JUMP DISJUNCT (readiness R1: "the
    factor theorem gains one disjunct"): a step of `seq px e1 e2`
    is (i) the beta at a finished `e1`, (ii) a lifted step of a
    non-jump-redex `e1` leaving the frame in place, or (iii) THE
    global jump — with the `seq` frame discarded and the successor
    identical to `e1`'s own jump successor. -/
theorem step_seq_factor {fn : TFn} {px : Option Nat} {e1 e2 : TExpr}
    {ρ : TEnv} {σ : THeap} {out : TExpr × TEnv × THeap}
    (h : Step fn (.seq px e1 e2, ρ, σ) out) :
    (∃ z, e1 = .val z ∧ out = (e2, bindPat px z ρ, σ)) ∨
    (∃ e1' ρ' σ', Step fn (e1, ρ, σ) (e1', ρ', σ') ∧
      jumpRedex? e1 = none ∧ out = (.seq px e1' e2, ρ', σ')) ∨
    (∃ l a px' k z, jumpRedex? e1 = some (l, a) ∧ fn l = some (px', k) ∧
      evalOp ρ a = some z ∧ out = (k, bindPat px' z ρ, σ)) := by
  cases h with
  | @head K e0 ρ0 σ0 e' ρ' σ' eK eK' h hK hK' =>
    cases K with
    | nil =>
      simp only [fill_nil] at hK hK'
      subst hK hK'
      cases h with
      | beta => exact .inl ⟨_, rfl, rfl⟩
    | cons f K =>
      obtain ⟨pxf, e2f⟩ := f
      simp only [fill_cons, TExpr.seq.injEq] at hK
      obtain ⟨rfl, he1, rfl⟩ := hK
      subst hK'
      refine .inr (.inl ⟨fill K e', _, _, ?_, ?_, rfl⟩)
      · exact he1 ▸ Step.head h rfl rfl
      · rw [he1, jumpRedex?_fill]
        exact h.jumpRedex?_none
  | @jump K l a px' k z ρ0 σ0 eK hl ha hK =>
    cases K with
    | nil => cases hK
    | cons f K =>
      obtain ⟨pxf, e2f⟩ := f
      simp only [fill_cons, TExpr.seq.injEq] at hK
      obtain ⟨rfl, he1, rfl⟩ := hK
      refine .inr (.inr ⟨l, a, px', k, z, ?_, hl, ha, rfl⟩)
      rw [he1, jumpRedex?_fill]
      rfl

/-- The lift direction: a step of a non-jump-redex `e1` lifts
    through the `seq` frame (the readiness's "head steps DO lift"). -/
theorem Step.lift_seq {fn : TFn} {e1 : TExpr} {ρ : TEnv} {σ : THeap}
    {e1' : TExpr} {ρ' : TEnv} {σ' : THeap} (px : Option Nat) (e2 : TExpr)
    (hnj : jumpRedex? e1 = none)
    (h : Step fn (e1, ρ, σ) (e1', ρ', σ')) :
    Step fn (.seq px e1 e2, ρ, σ) (.seq px e1' e2, ρ', σ') := by
  cases h with
  | head h hK hK' =>
    subst hK hK'
    exact Step.head (K := (px, e2) :: _) h rfl rfl
  | jump hl ha hK =>
    subst hK
    rw [jumpRedex?_fill] at hnj
    cases hnj

/-! ## Top-level inversions for the non-jump redexes -/

theorem step_load_inv {fn : TFn} {ℓop : TOp} {ρ : TEnv} {σ : THeap}
    {out : TExpr × TEnv × THeap} (h : Step fn (.load ℓop, ρ, σ) out) :
    ∃ a v, evalOp ρ ℓop = some a ∧ Iris.Std.PartialMap.get? σ a = some v ∧
      out = (.val v, ρ, σ) := by
  cases h with
  | head h hK hK' =>
    obtain ⟨rfl, rfl⟩ := fill_eq_of_ne_seq (by intro _ _ _ h; cases h) hK
    subst hK'
    cases h with
    | load hℓ hget => exact ⟨_, _, hℓ, hget, rfl⟩
  | jump hl ha hK =>
    obtain ⟨-, heq⟩ := fill_eq_of_ne_seq (by intro _ _ _ h; cases h) hK
    cases heq

theorem step_store_inv {fn : TFn} {ℓop vop : TOp} {ρ : TEnv} {σ : THeap}
    {out : TExpr × TEnv × THeap} (h : Step fn (.store ℓop vop, ρ, σ) out) :
    ∃ a v v0, evalOp ρ ℓop = some a ∧ evalOp ρ vop = some v ∧
      Iris.Std.PartialMap.get? σ a = some v0 ∧
      out = (.val v, ρ, Iris.Std.PartialMap.insert σ a v) := by
  cases h with
  | head h hK hK' =>
    obtain ⟨rfl, rfl⟩ := fill_eq_of_ne_seq (by intro _ _ _ h; cases h) hK
    subst hK'
    cases h with
    | store hℓ hv hget => exact ⟨_, _, _, hℓ, hv, hget, rfl⟩
  | jump hl ha hK =>
    obtain ⟨-, heq⟩ := fill_eq_of_ne_seq (by intro _ _ _ h; cases h) hK
    cases heq

theorem step_ifz_inv {fn : TFn} {g : TOp} {e1 e2 : TExpr} {ρ : TEnv}
    {σ : THeap} {out : TExpr × TEnv × THeap}
    (h : Step fn (.ifz g e1 e2, ρ, σ) out) :
    ∃ z, evalOp ρ g = some z ∧
      ((z = 0 ∧ out = (e1, ρ, σ)) ∨ (z ≠ 0 ∧ out = (e2, ρ, σ))) := by
  cases h with
  | head h hK hK' =>
    obtain ⟨rfl, rfl⟩ := fill_eq_of_ne_seq (by intro _ _ _ h; cases h) hK
    subst hK'
    cases h with
    | ifz_zero hg => exact ⟨0, hg, .inl ⟨rfl, rfl⟩⟩
    | ifz_nonzero hg hz => exact ⟨_, hg, .inr ⟨hz, rfl⟩⟩
  | jump hl ha hK =>
    obtain ⟨-, heq⟩ := fill_eq_of_ne_seq (by intro _ _ _ h; cases h) hK
    cases heq

/-! ## The iris-lean Language instance -/

/-- Every list of `Empty` observations is empty (house lemma shape,
    Lang.lean:31). -/
theorem List.empty_eq_nil (l : List Empty) : l = [] := by
  cases l with
  | nil => rfl
  | cons e _ => exact e.elim

def toValRt (r : TRt) : Option TRVal :=
  (toValE r.e).map fun z => ⟨r.fn, z, r.ρ⟩

instance : Language TRt THeap Empty TRVal where
  primStep p _obs q :=
    Step p.1.fn (p.1.e, p.1.ρ, p.2) (q.1.e, q.1.ρ, q.2.1) ∧
      q.1.fn = p.1.fn ∧ q.2.2 = []
  toVal := toValRt
  ofVal v := ⟨v.fn, .val v.z, v.ρ⟩
  coe_of_toVal_eq_some {r v} h := by
    obtain ⟨fn, e, ρ⟩ := r
    cases e <;> cases h <;> rfl
  toVal_coe v := rfl
  val_stuck {r σ obs r' σ' eₜ} h := by
    obtain ⟨hs, -, -⟩ := h
    obtain ⟨fn, e, ρ⟩ := r
    cases e <;> first
      | rfl
      | exact absurd hs step_val_elim

@[simp] theorem probe_primStep_eq (r : TRt) (σ : THeap) (obs : List Empty)
    (r' : TRt) (σ' : THeap) (eₜ : List TRt) :
    (PrimStep.primStep (r, σ) obs (r', σ', eₜ) : Prop) ↔
      (Step r.fn (r.e, r.ρ, σ) (r'.e, r'.ρ, σ') ∧ r'.fn = r.fn ∧ eₜ = []) :=
  Iff.rfl

theorem probe_toVal_eq (r : TRt) :
    ToVal.toVal (Val := TRVal) r = toValRt r := rfl

@[simp] theorem toValRt_mk (fn : TFn) (e : TExpr) (ρ : TEnv) :
    toValRt ⟨fn, e, ρ⟩ = (toValE e).map fun z => ⟨fn, z, ρ⟩ := rfl

end StmtProbe
end CerberusHeapLang
