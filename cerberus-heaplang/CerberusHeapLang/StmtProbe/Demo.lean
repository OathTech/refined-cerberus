/-
CerberusHeapLang.StmtProbe.Demo — S0 probe, part 3 of 3: the
demonstrations the charter demands.

1. THE TOY LOOP (`demo_loop`): a label with a back-edge jump and a
   counter riding in the ENV through the jump argument (Erun's
   parameter rebinding), incrementing a heap cell each iteration —
   verified with a per-label invariant (`demoLs`) through the block
   machinery (`demo_block`/`demo_blocks` = the per-label proofs,
   `wps_sound` = the Löb tie), landing in the BASE Iris WP. Partial
   correctness: `{c ↦ v0} run loop(n) {w. w = v0+n ∗ c ↦ v0+n}`.
   The registered body is sseq-EXTENDED in the engine's sense: the
   exit branch IS the rest of the program (returns the final value),
   which is exactly why discarding the `seq` spine at the back edge
   is correct.

2. COVERAGE PRESERVATION (`probe_store_frame`,
   `probe_seq_stores`): the current corpus's exhibit shapes (store
   under FRAME, Rules.lean:615; two sequenced disjoint stores,
   Rules.lean:752) re-proved on the STRATIFIED layer with the same
   compositional discipline (small axiom + frame + seq), for an
   ARBITRARY label map and label-spec context — jump-free code needs
   no label facts, so the migration of the existing corpus is a
   re-phrasing, not a re-proof.
-/
import CerberusHeapLang.StmtProbe.Wps

set_option autoImplicit false

namespace CerberusHeapLang
namespace StmtProbe

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

variable {hlc : HasLC} {GF : BundledGFunctors}

/-! ## The corpus shapes on the stratified layer -/

/-- Corpus shape 1 (house `exhibit`): {x ↦ - ∗ y ↦ a} store(x,7)
    {x ↦ 7 ∗ y ↦ a}, via FRAME on the store small axiom — for ANY
    label context (Q, Ls). -/
theorem probe_store_frame [ProbeGS hlc GF] (Q : TFn)
    (Ls : Nat → Int → IProp GF) (x y vx vy : Int) (ρ : TEnv) :
    iprop(pointsTo (GF := GF) x (DFrac.own 1) vx ∗
        pointsTo y (DFrac.own 1) vy) ⊢
      wps Q Ls
        (fun _ _ => iprop(pointsTo x (DFrac.own 1) 7 ∗
          pointsTo y (DFrac.own 1) vy))
        (.store (.lit x) (.lit 7)) ρ := by
  iintro ⟨Hx, Hy⟩
  iapply (wps_frame
    (Ψ := fun _ _ => iprop(pointsTo (GF := GF) x (DFrac.own 1) 7))
    (R := pointsTo y (DFrac.own 1) vy) _ _)
  isplitl [Hx]
  · iapply wps_store rfl rfl
    isplitl [Hx]
    · iexact Hx
    iintro Hx
    iexact Hx
  · iexact Hy

/-- Corpus shape 2 (house `exhibitC_triple`): two sequenced stores
    on disjoint cells, glued by the (jump-aware) sequencing rule —
    each leg the small axiom, distinctness carried by ∗ alone, for
    ANY label context. -/
theorem probe_seq_stores [ProbeGS hlc GF] (Q : TFn)
    (Ls : Nat → Int → IProp GF) (x y vx vy : Int) (ρ : TEnv) :
    iprop(pointsTo (GF := GF) x (DFrac.own 1) vx ∗
        pointsTo y (DFrac.own 1) vy) ⊢
      wps Q Ls
        (fun _ _ => iprop(pointsTo x (DFrac.own 1) 5 ∗
          pointsTo y (DFrac.own 1) 6))
        (.seq none (.store (.lit x) (.lit 5)) (.store (.lit y) (.lit 6))) ρ := by
  iintro ⟨Hx, Hy⟩
  iapply wps_seq
  iapply wps_store rfl rfl
  isplitl [Hx]
  · iexact Hx
  iintro Hx
  iapply wps_store rfl rfl
  isplitl [Hy]
  · iexact Hy
  iintro Hy
  isplitl [Hx]
  · iexact Hx
  · iexact Hy

/-! ## The loop -/

def cAddr : Int := 0
def loopLbl : Nat := 0
/-- the loop counter binder (rebound by every back-edge jump) -/
def xK : Nat := 0
/-- the scratch binder for the loaded cell value -/
def yK : Nat := 1

/-- The registered body of `loopLbl` (sseq-extended: the exit branch
    returns the program's final value):

      if x = 0 then load c
      else lets y = load c in
           lets _ = store c (y+1) in
           run loop (x-1)                     -- the back edge
-/
def loopBody : TExpr :=
  .ifz (.var xK)
    (.load (.lit cAddr))
    (.seq (some yK) (.load (.lit cAddr))
      (.seq none (.store (.lit cAddr) (.add1 (.var yK)))
        (.run loopLbl (.sub1 (.var xK)))))

/-- The static label map: registered once, exactly one label. -/
def demoFn : TFn := fun l => if l = loopLbl then some (some xK, loopBody) else none

/-- The per-label invariant, indexed by the jump-argument value `x`
    (the counter): `x` iterations remain, the cell has absorbed the
    first `n - x`. -/
abbrev demoLs [ProbeGS hlc GF] (v0 n : Int) : Nat → Int → IProp GF := fun l x =>
  if l = loopLbl then
    iprop(⌜0 ≤ x ∧ x ≤ n⌝ ∗ pointsTo cAddr (DFrac.own 1) (v0 + (n - x)))
  else iprop(False)

/-- The final postcondition (env projected away, as exported posts
    do). -/
abbrev demoΨ [ProbeGS hlc GF] (v0 n : Int) : Int → TEnv → IProp GF := fun z _ =>
  iprop(⌜z = v0 + n⌝ ∗ pointsTo cAddr (DFrac.own 1) (v0 + n))

/-- THE PER-LABEL PROOF: the body preserves the invariant. Note
    what is absent: no Löb, no mutual block assumption — the
    back-edge (`wps_run`) discharges directly against the invariant
    at the decremented counter. The env is live throughout: the
    guard reads the jump-bound `x`, the store operand reads the
    `seq`-bound `y`. -/
theorem demo_block [ProbeGS hlc GF] (v0 n x : Int) (ρ' : TEnv) :
    demoLs (GF := GF) v0 n loopLbl x ⊢
      wps demoFn (demoLs v0 n) (demoΨ v0 n) loopBody (bindPat (some xK) x ρ') := by
  unfold loopBody
  dsimp only [bindPat]
  rw [show demoLs (GF := GF) v0 n loopLbl x =
    iprop(⌜0 ≤ x ∧ x ≤ n⌝ ∗ pointsTo cAddr (DFrac.own 1) (v0 + (n - x))) from
    if_pos rfl]
  iintro ⟨%hx, Hc⟩
  by_cases hx0 : x = 0
  · -- exit branch: the guard is 0; return the cell's value.
    subst hx0
    iapply wps_ifz_zero
      (show evalOp ((xK, 0) :: ρ') (.var xK) = some 0 from rfl)
    iapply wps_load
      (show evalOp ((xK, 0) :: ρ') (.lit cAddr) = some cAddr from rfl)
    isplitl [Hc]
    · iexact Hc
    iintro Hc
    rw [show v0 + (n - 0) = v0 + n from by omega]
    isplitr
    · ipureintro; rfl
    iexact Hc
  · -- loop branch: load, bump, store, jump with x-1.
    iapply wps_ifz_nonzero
      (show evalOp ((xK, x) :: ρ') (.var xK) = some x from rfl) hx0
    iapply wps_seq
    iapply wps_load
      (show evalOp ((xK, x) :: ρ') (.lit cAddr) = some cAddr from rfl)
    isplitl [Hc]
    · iexact Hc
    iintro Hc
    dsimp only [bindPat]
    iapply wps_seq
    iapply wps_store
      (show evalOp ((yK, v0 + (n - x)) :: (xK, x) :: ρ')
        (.lit cAddr) = some cAddr from rfl)
      (show evalOp ((yK, v0 + (n - x)) :: (xK, x) :: ρ')
        (.add1 (.var yK)) = some (v0 + (n - x) + 1) from rfl)
    isplitl [Hc]
    · iexact Hc
    iintro Hc
    dsimp only [bindPat]
    -- the back edge: consult the invariant at x-1.
    iapply wps_run
      (show demoFn loopLbl = some (some xK, loopBody) from rfl)
      (show evalOp ((yK, v0 + (n - x)) :: (xK, x) :: ρ')
        (.sub1 (.var xK)) = some (x - 1) from rfl)
    rw [show demoLs (GF := GF) v0 n loopLbl (x - 1) =
      iprop(⌜0 ≤ x - 1 ∧ x - 1 ≤ n⌝ ∗
        pointsTo cAddr (DFrac.own 1) (v0 + (n - (x - 1)))) from if_pos rfl]
    isplitr
    · ipureintro; omega
    rw [show v0 + (n - x) + 1 = v0 + (n - (x - 1)) from by omega]
    iexact Hc

/-- All block specs — assembled with NO Löb (`blockSpecs_intro`):
    the only label is the loop, and its proof is `demo_block`. -/
theorem demo_blocks [ProbeGS hlc GF] (v0 n : Int) :
    ⊢ blockSpecs (GF := GF) demoFn (demoLs v0 n) (demoΨ v0 n) := by
  refine blockSpecs_intro ?_
  intro l px k z ρ hQ
  by_cases hl : l = loopLbl
  · subst hl
    obtain ⟨rfl, rfl⟩ : some xK = px ∧ loopBody = k := by
      have h : some (some xK, loopBody) = some (px, k) := hQ
      obtain h := Option.some.inj h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact demo_block v0 n z ρ
  · exact absurd hQ (by simp [demoFn, hl])

/-- THE TOY-LOOP THEOREM (partial correctness, base Iris WP):

      {c ↦ v0} run loop(n) {w. ⌜w = v0 + n⌝ ∗ c ↦ v0 + n}   (0 ≤ n)

    Derivation: `wps_run` consults the invariant at the entry
    argument `n` (n iterations remain, cell untouched);
    `demo_blocks` supplies the per-label proofs; `wps_sound` — the
    one Löb induction — lands the statement WP in the base WP. -/
theorem demo_loop [ProbeGS hlc GF] (v0 n : Int) (hn : 0 ≤ n) (ρ : TEnv) :
    pointsTo (GF := GF) cAddr (DFrac.own 1) v0 ⊢
      WP (⟨demoFn, .run loopLbl (.lit n), ρ⟩ : TRt) @ Stuckness.NotStuck; ⊤
        {{ w, iprop(⌜w.z = v0 + n⌝ ∗ pointsTo cAddr (DFrac.own 1) (v0 + n)) }} := by
  icases (demo_blocks (GF := GF) v0 n) with #HB
  iintro Hc
  iapply (wps_sound (Q := demoFn) (Ls := demoLs v0 n) (Ψ := demoΨ v0 n)
    (.run loopLbl (.lit n)) ρ) $$ HB
  iapply wps_run
    (show demoFn loopLbl = some (some xK, loopBody) from rfl)
    (show evalOp ρ (.lit n) = some n from rfl)
  rw [show demoLs (GF := GF) v0 n loopLbl n =
    iprop(⌜0 ≤ n ∧ n ≤ n⌝ ∗ pointsTo cAddr (DFrac.own 1) (v0 + (n - n))) from
    if_pos rfl]
  isplitr
  · ipureintro; omega
  rw [show v0 + (n - n) = v0 from by omega]
  iexact Hc

end StmtProbe
end CerberusHeapLang
