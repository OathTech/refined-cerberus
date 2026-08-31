/-
CerberusHeapLang.StmtProbe.Wps — S0 probe, part 2 of 3: the
statement-stratified WP over the toy, and the jump-aware sequencing
lemma (the arc's kill-criterion kernel).

THE SHAPE, AND WHY IT IS NOT THE DONOR'S LITERAL ONE (the probe's
central finding — recorded in full in
docs/2026-08-31_s0-probe-report.md):

The donor's `stmt_wp` (deps/refinedc lifting.v:1002) is a CPS
wrapper over the base WP: `∀ Φ rf, ⌜Q = rf.f_code⌝ -∗ (Return
channel) -∗ WP (to_rtstmt rf s) {{Φ}}`. That shape ports
`wps_goto`/`wps_block_rec` fine — but its SEQUENCING never has to
compose a jump-capable subterm, because Caesium's statement grammar
is syntactically continuation-passing (`Assign … s` carries its own
continuation; `Goto` only ever sits at statement tail position).
Core's `Esseq` binds an arbitrary jump-capable subexpression
(readiness review §2.1: `run while_…` sits UNDER the sseq spine), and
there the single-Φ CPS wrapper is unusable: composing `seq px e1 e2`
needs e1's exits split into "finished with a value → continue with
e2" vs "jumped → the label's registered continuation covers the rest
of the program", and one Φ cannot serve both channels (the value
channel needs Φ' = the bind-post, the jump channel needs Φ' = the
final post; the wrapper's WP of e1-standalone runs THROUGH a jump to
the program's real end, conflating e1's own values with program
values). The failed shape and its two dead instantiations are
recorded in the probe report.

The shape that works is the classical LABEL-CONTEXT statement logic
(de Bruin 1981-style label-assumption Hoare logic; the standard
judgment of unstructured-control-flow program logics), realized as a
GUARDED FIXPOINT over the toy step relation via iris-lean's public
Banach machinery (`fixpoint`/`OFE.Contractive`,
Iris/Algebra/OFE.lean:1834 — the same machinery `wp` itself is built
from; nothing inside iris-lean is touched, which is the S0 kill
criterion's boundary). `wps Q Ls Ψ e ρ` has three clauses:

- VALUE:      `|={⊤}=> Ψ z ρ` — the donor's Return/Ψ channel;
- JUMP REDEX: the registered-label lookup facts ∗ `Ls l z` — the
  jump consults the per-label precondition and the tracking STOPS
  (`wps_goto`'s role, but placed in the judgment: this is what
  dissolves the CPS clash);
- STEP:       the base WP's step clause shape (`wp_lift_step`'s
  premise, Lifting.lean:77), recursing ▷-guarded.

Consequences, each proved below:
- `wps_run` (donor `wps_goto`, lifting.v:1112): jump = consult the
  label precondition. Near-definitional.
- `wps_seq` — THE JUMP-AWARE SEQUENCING LEMMA (readiness R1's
  hand-proved obligation). Its jump case is a clause TRANSFER:
  `jumpRedex? (seq px e1 e2) = jumpRedex? e1` (Toy.lean), the
  syntactic image of the engine's context-discard. The semantic
  content — every step at a jump redex is THE context-independent
  jump — is paid once, in `wps_sound`'s jump case
  (`step_jump_inv`).
- `wps_sound` — the Löb-tied elimination into the base Iris WP,
  under `blockSpecs` (the ∗/∀-collection of per-label block specs =
  the donor's `[∗ map] wps_block`). THE DONOR's `wps_block_rec`
  (lifting.v:1306, one iLöb tying all back-edges) CORRESPONDS TO
  THIS LEMMA: in the label-context shape the per-label proofs
  (`blockSpecs_intro`) need no Löb and no mutual assumption — the
  back-edge circularity is broken by the jump clause — and the one
  Löb induction lands here instead. Partial correctness, donor
  parity.

The base WP (and with it iris-lean's adequacy chain) remains the
sole semantic interface: `wps` claims nothing an eventual
`wps_sound`-composed statement does not re-state in base-WP terms.
-/
import CerberusHeapLang.StmtProbe.Toy

set_option autoImplicit false

namespace CerberusHeapLang
namespace StmtProbe

open Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation

/-! ## Ghost state (house `SpikeGS` shape, Heap.lean:389/Lang.lean:128) -/

/-- Ghost-state prerequisites: invariants + one GenHeap of toy cells. -/
class ProbeGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  heap_pre : genHeapPreS Int Int GF THeapF

attribute [reducible, instance] ProbeGpreS.heap_pre

/-- The bundled ghost names. -/
class ProbeGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  [invGS : InvGS_gen hlc GF]
  heap : genHeapGS Int Int GF THeapF

attribute [reducible, instance] ProbeGS.heap

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The state interpretation: the toy heap IS the ghost map (the
    coupling invariant is trivial — the toy has no engine to couple
    to; the house `Coh` seam is orthogonal to the jump kernel). -/
instance ProbeState [ProbeGS hlc GF] : StateInterp THeap Empty GF where
  stateInterp σ _ _ _ := genHeapInterp σ

theorem probeStateInterp_eq [ProbeGS hlc GF] (σ : THeap) (ns : Nat)
    (κs : List Empty) (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt = genHeapInterp σ := rfl

instance instProbeIrisGS [ProbeGS hlc GF] : IrisGS_gen hlc TRt GF where
  invGS := ProbeGS.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    letI := @ProbeGS.invGS hlc GF _
    iintro $

/-- Non-vacuity witness for the ghost-state prerequisites (mirror of
    `SpikeGF`, Lang.lean:152 — the functor list exists; the bundled
    `ProbeGS` is constructed from it by allocation exactly as the
    house `SpikeGS` is in Adequacy.lean, which the probe does not
    repeat: Prop-level adequacy is out of S0 scope). -/
def ProbeGF : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨_root_.Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Int (Agree (DiscreteO Int)) THeapF),
          by infer_instance⟩
  | 5 => ⟨constOF (HeapView Int (Agree (DiscreteO GName)) THeapF),
          by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instProbeGpreS_ProbeGF : ProbeGpreS ProbeGF where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6

/-! ## The statement WP -/

/-- One unfolding of the statement WP. Three clauses: value / jump
    redex / step (see the module header). The step clause is
    verbatim `wp_lift_step`'s premise shape (Lifting.lean:77) at
    this instance's `numLatersPerStep = 0`, minus forks. -/
def wps.pre [ProbeGS hlc GF] (Q : TFn) (Ls : Nat → Int → IProp GF)
    (F : (Int → TEnv → IProp GF) → TExpr → TEnv → IProp GF)
    (Ψ : Int → TEnv → IProp GF) (e : TExpr) (ρ : TEnv) : IProp GF :=
  match toValE e with
  | some z => iprop(|={⊤}=> Ψ z ρ)
  | none =>
    match jumpRedex? e with
    | some la =>
      iprop(|={⊤}=> ∃ px k z, ⌜Q la.1 = some (px, k)⌝ ∗
        ⌜evalOp ρ la.2 = some z⌝ ∗ Ls la.1 z)
    | none =>
      iprop(∀ (σ₁ : THeap) (ns : Nat) (obs obs' : List Empty) (nt : Nat),
        stateInterp σ₁ ns (obs ++ obs') nt ={⊤,∅}=∗
        ⌜PrimStep.Reducible ((⟨Q, e, ρ⟩ : TRt), σ₁)⌝ ∗
        ▷ ∀ (r : TRt) (σ₂ : THeap) (eₜ : List TRt),
          ⌜((⟨Q, e, ρ⟩ : TRt), σ₁) -<obs>-> (r, σ₂, eₜ)⌝ -∗ £ 1 ={∅,⊤}=∗
          stateInterp σ₂ (ns + 1) obs' nt ∗ F Ψ r.e r.ρ)

instance wps.pre.contractive [ProbeGS hlc GF] (Q : TFn)
    (Ls : Nat → Int → IProp GF) :
    OFE.Contractive (wps.pre (GF := GF) Q Ls) where
  distLater_dist := by
    intro n F F' HF Ψ e ρ
    unfold wps.pre
    cases toValE e
    case some => exact .rfl
    case none =>
      cases jumpRedex? e
      case some => exact .rfl
      case none =>
        refine BI.forall_ne fun σ₁ => ?_
        refine BI.forall_ne fun ns => ?_
        refine BI.forall_ne fun obs => ?_
        refine BI.forall_ne fun obs' => ?_
        refine BI.forall_ne fun nt => ?_
        refine BI.wand_ne.ne .rfl ?_
        refine BIFUpdate.ne.ne ?_
        refine BI.sep_ne.ne .rfl ?_
        refine OFE.Contractive.distLater_dist fun m m_n => ?_
        refine BI.forall_ne fun r => ?_
        refine BI.forall_ne fun σ₂ => ?_
        refine BI.forall_ne fun eₜ => ?_
        refine BI.wand_ne.ne .rfl ?_
        refine BI.wand_ne.ne .rfl ?_
        refine BIFUpdate.ne.ne ?_
        refine BI.sep_ne.ne .rfl ?_
        exact HF m m_n _ _ _

/-- The statement WP: guarded fixpoint of `wps.pre` (the same
    construction as iris-lean's own `wp`, WeakestPre.lean:118). -/
def wps [ProbeGS hlc GF] (Q : TFn) (Ls : Nat → Int → IProp GF) :
    (Int → TEnv → IProp GF) → TExpr → TEnv → IProp GF :=
  fixpoint (wps.pre Q Ls)

theorem wps_unfold [ProbeGS hlc GF] {Q : TFn} {Ls : Nat → Int → IProp GF}
    {Ψ : Int → TEnv → IProp GF} {e : TExpr} {ρ : TEnv} :
    wps (GF := GF) Q Ls Ψ e ρ ⊣⊢ wps.pre Q Ls (wps Q Ls) Ψ e ρ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wps.pre Q Ls).toContractiveHom)).dist Ψ e ρ

variable [ProbeGS hlc GF]
variable {Q : TFn} {Ls : Nat → Int → IProp GF}

/-! ## Structural rules -/

/-- Value rule (the donor's Return channel / `wps_return`,
    lifting.v:1107). -/
theorem wps_val {Ψ : Int → TEnv → IProp GF} (z : Int) (ρ : TEnv) :
    Ψ z ρ ⊢ wps Q Ls Ψ (.val z) ρ := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toValE_val]
  iintro H
  imodintro
  iexact H

/-- JUMP RULE (`wps_goto`, lifting.v:1112, adapted to the
    label-context shape): a registered jump is verified by
    consulting the label's precondition at the argument's value —
    nothing else. Near-definitional: the judgment's jump clause IS
    this rule. -/
theorem wps_run {Ψ : Int → TEnv → IProp GF} {l : Nat} {a : TOp}
    {px : Option Nat} {k : TExpr} {z : Int} {ρ : TEnv}
    (hl : Q l = some (px, k)) (ha : evalOp ρ a = some z) :
    Ls l z ⊢ wps Q Ls Ψ (.run l a) ρ := by
  rw [wps_unfold.to_eq]
  simp only [wps.pre, toValE_run, jumpRedex?_run]
  iintro H
  imodintro
  iexists px, k, z
  isplit
  · ipureintro; exact hl
  isplit
  · ipureintro; exact ha
  iexact H

/-- Monotonicity/consequence in the value channel. The wand is
    consumed at the value exit only; jump exits are Ψ-independent
    (the label preconditions carry everything across a jump — the
    label-context logic's standard discipline). -/
theorem wps_wand {Ψ₁ Ψ₂ : Int → TEnv → IProp GF} (e : TExpr) (ρ : TEnv) :
    wps Q Ls Ψ₁ e ρ ⊢
      iprop((∀ z ρ', Ψ₁ z ρ' -∗ Ψ₂ z ρ') -∗ wps Q Ls Ψ₂ e ρ) := by
  iloeb as IH generalizing %e %ρ
  cases htv : toValE e with
  | some z =>
    obtain rfl := toValE_eq_some htv
    rw [wps_unfold.to_eq, wps_unfold.to_eq]
    simp only [wps.pre, toValE_val]
    iintro H HΨ
    imod H with H
    imodintro
    iapply HΨ $$ H
  | none =>
    cases hjr : jumpRedex? e with
    | some la =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H HΨ
      iexact H
    | none =>
      rw [wps_unfold.to_eq, wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro H HΨ %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨$, H⟩
      imodintro
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      imod H $$ %r %σ₂ %eₜ %Hstep Hcred with ⟨$, H⟩
      imodintro
      iapply IH $$ %(r.e) %(r.ρ) H HΨ

/-- FRAME over the statement WP (derived from `wps_wand`; the frame
    rides to the value exit; at a jump it is released — the label
    invariant is the only thing that crosses a back edge). -/
theorem wps_frame {Ψ : Int → TEnv → IProp GF} {R : IProp GF}
    (e : TExpr) (ρ : TEnv) :
    iprop(wps Q Ls Ψ e ρ ∗ R) ⊢
      wps Q Ls (fun z ρ' => iprop(Ψ z ρ' ∗ R)) e ρ := by
  iintro ⟨H, HR⟩
  iapply (wps_wand e ρ) $$ H
  iintro %z %ρ' HΨ
  isplitl [HΨ]
  · iexact HΨ
  · iexact HR

/-! ## THE JUMP-AWARE SEQUENCING LEMMA (readiness R1's obligation)

`Language.Context`-based `wp_bind` is FALSE for the toy's `seq`
frame once the global jump exists (a jump of `e1` and of
`seq px e1 e2` step to the SAME configuration — `primStep_fill`
cannot hold). This lemma replaces it, by Löb induction with three
cases:
- e1 finished: the beta step; the continuation comes from the value
  channel of the premise (which carries `wps` of e2 at the bound
  env — the binding form of the house `wp_sseq`).
- e1 at a jump redex: BOTH sides' jump clauses are the SAME formula
  (`jumpRedex?_seq`) — the jump case of sequencing is a transfer,
  because the jump's successor never looked at the frame.
- e1 steps: the factor theorem (`step_seq_factor`, jump disjunct
  excluded) + the lift (`Step.lift_seq`), then Löb. -/
theorem wps_seq {Ψ : Int → TEnv → IProp GF} (px : Option Nat)
    (e1 e2 : TExpr) (ρ : TEnv) :
    wps Q Ls (fun z ρ' => wps Q Ls Ψ e2 (bindPat px z ρ')) e1 ρ ⊢
      wps Q Ls Ψ (.seq px e1 e2) ρ := by
  iloeb as IH generalizing %e1 %ρ
  cases htv : toValE e1 with
  | some z =>
    -- e1 is finished: one beta step into e2 at the bound env.
    obtain rfl := toValE_eq_some htv
    rw [wps_unfold.to_eq, (wps_unfold (e := .seq px (.val z) e2)).to_eq]
    simp only [wps.pre, toValE_val, toValE_seq, jumpRedex?_seq, jumpRedex?_val]
    iintro H %σ₁ %ns %obs %obs' %nt Hσ
    imod H with H
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    isplitr
    · ipureintro
      exact ⟨[], ⟨Q, e2, bindPat px z ρ⟩, σ₁, [],
        ⟨Step.head (K := []) HeadStep.beta rfl rfl, rfl, rfl⟩⟩
    inext
    iintro %r %σ₂ %eₜ %Hstep Hcred
    obtain ⟨hs, hfn, rfl⟩ := Hstep
    rcases step_seq_factor hs with ⟨z', hz', hout⟩ | ⟨e1', ρ', σ', hs', -, hout⟩ |
        ⟨l, a, px', k, z', hjr, -, -, hout⟩
    · obtain ⟨hre, hrρ, hσ⟩ : r.e = e2 ∧ r.ρ = bindPat px z ρ ∧ σ₂ = σ₁ := by
        obtain rfl : z' = z := by
          have := hz'
          simp only [TExpr.val.injEq] at this
          exact this.symm
        simpa [Prod.mk.injEq] using hout
      subst hσ
      rw [hre, hrρ]
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · iexact Hσ
      · iexact H
    · exact absurd hs' step_val_elim
    · simp at hjr
  | none =>
    cases hjr : jumpRedex? e1 with
    | some la =>
      -- THE JUMP CASE: both jump clauses are literally the same
      -- formula — the frame was never consulted.
      rw [wps_unfold.to_eq, (wps_unfold (e := .seq px e1 e2)).to_eq]
      simp only [wps.pre, htv, hjr, toValE_seq, jumpRedex?_seq]
      iintro H
      iexact H
    | none =>
      -- e1 steps: factor + lift + Löb.
      rw [wps_unfold.to_eq, (wps_unfold (e := .seq px e1 e2)).to_eq]
      simp only [wps.pre, htv, hjr, toValE_seq, jumpRedex?_seq]
      iintro H %σ₁ %ns %obs %obs' %nt Hσ
      imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, H⟩
      imodintro
      isplitr
      · ipureintro
        obtain ⟨obs0, r', σ', eₜ', hps⟩ := hred
        obtain ⟨hs', hfn', hnil'⟩ := hps
        exact ⟨obs0, ⟨Q, .seq px r'.e e2, r'.ρ⟩, σ', eₜ',
          ⟨Step.lift_seq px e2 hjr hs', rfl, hnil'⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hfn, rfl⟩ := Hstep
      rcases step_seq_factor hs with ⟨z', hz', -⟩ | ⟨e1', ρ', σ', hs', -, hout⟩ |
          ⟨l, a, px', k, z', hjr', -, -, -⟩
      · rw [hz'] at htv; cases htv
      · obtain ⟨hre, hrρ, hσ⟩ : r.e = .seq px e1' e2 ∧ r.ρ = ρ' ∧ σ₂ = σ' := by
          simpa [Prod.mk.injEq] using hout
        subst hσ
        rw [hre, hrρ]
        imod H $$ %(⟨Q, e1', ρ'⟩ : TRt) %σ₂ %([] : List TRt)
          %(⟨hs', rfl, rfl⟩ :
            ((⟨Q, e1, ρ⟩ : TRt), σ₁) -<obs>-> (⟨Q, e1', ρ'⟩, σ₂, []))
          Hcred with ⟨$, H⟩
        imodintro
        iapply IH $$ %e1' %ρ' H
      · rw [hjr'] at hjr; cases hjr

/-! ## The rules for the remaining constructs -/

/-- Branch rule, guard = 0 (`Eif` shape: big-step guard as a pure
    hypothesis; donor `wps_if`, lifting.v:1256). -/
theorem wps_ifz_zero {Ψ : Int → TEnv → IProp GF} {g : TOp}
    {e1 e2 : TExpr} {ρ : TEnv} (hg : evalOp ρ g = some 0) :
    wps Q Ls Ψ e1 ρ ⊢ wps Q Ls Ψ (.ifz g e1 e2) ρ := by
  rw [(wps_unfold (e := .ifz g e1 e2)).to_eq]
  simp only [wps.pre, toValE_ifz, jumpRedex?_ifz]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨Q, e1, ρ⟩, σ₁, [],
      ⟨Step.head (K := []) (HeadStep.ifz_zero hg) rfl rfl, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hfn, rfl⟩ := Hstep
  obtain ⟨z', hg', hcase⟩ := step_ifz_inv hs
  obtain rfl : z' = 0 := by rw [hg] at hg'; exact (Option.some.inj hg').symm
  rcases hcase with ⟨-, hout⟩ | ⟨hne, -⟩
  · obtain ⟨hre, hrρ, hσ⟩ : r.e = e1 ∧ r.ρ = ρ ∧ σ₂ = σ₁ := by
      simpa [Prod.mk.injEq] using hout
    subst hσ
    rw [hre, hrρ]
    imod Hclose with -
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iexact H
  · exact absurd rfl hne

/-- Branch rule, guard ≠ 0. -/
theorem wps_ifz_nonzero {Ψ : Int → TEnv → IProp GF} {g : TOp}
    {e1 e2 : TExpr} {z : Int} {ρ : TEnv}
    (hg : evalOp ρ g = some z) (hz : z ≠ 0) :
    wps Q Ls Ψ e2 ρ ⊢ wps Q Ls Ψ (.ifz g e1 e2) ρ := by
  rw [(wps_unfold (e := .ifz g e1 e2)).to_eq]
  simp only [wps.pre, toValE_ifz, jumpRedex?_ifz]
  iintro H %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨Q, e2, ρ⟩, σ₁, [],
      ⟨Step.head (K := []) (HeadStep.ifz_nonzero hg hz) rfl rfl, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hfn, rfl⟩ := Hstep
  obtain ⟨z', hg', hcase⟩ := step_ifz_inv hs
  obtain rfl : z' = z := by rw [hg] at hg'; exact (Option.some.inj hg').symm
  rcases hcase with ⟨rfl, -⟩ | ⟨-, hout⟩
  · exact absurd rfl hz
  · obtain ⟨hre, hrρ, hσ⟩ : r.e = e2 ∧ r.ρ = ρ ∧ σ₂ = σ₁ := by
      simpa [Prod.mk.injEq] using hout
    subst hσ
    rw [hre, hrρ]
    imod Hclose with -
    imodintro
    isplitl [Hσ]
    · iexact Hσ
    · iexact H

/-- Load small axiom at the statement layer (any fraction; the
    points-to is the UB-exclusion: it makes the cell's presence — the
    reducibility side condition — a theorem). -/
theorem wps_load {Ψ : Int → TEnv → IProp GF} {ℓop : TOp} {ρ : TEnv}
    {av v : Int} {dq : DFrac} (hℓ : evalOp ρ ℓop = some av) :
    iprop(pointsTo (GF := GF) av dq v ∗ (pointsTo av dq v -∗ Ψ v ρ)) ⊢
      wps Q Ls Ψ (.load ℓop) ρ := by
  rw [(wps_unfold (e := .load ℓop)).to_eq]
  simp only [wps.pre, toValE_load, jumpRedex?_load]
  iintro ⟨Hpt, HΨ⟩ %σ₁ %ns %obs %obs' %nt Hσ
  rw [probeStateInterp_eq]
  ihave %Hget : ⌜Iris.Std.PartialMap.get? σ₁ av = some v⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨Q, .val v, ρ⟩, σ₁, [],
      ⟨Step.head (K := []) (HeadStep.load hℓ Hget) rfl rfl, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hfn, rfl⟩ := Hstep
  obtain ⟨a', v', hℓ', hget', hout⟩ := step_load_inv hs
  obtain rfl : av = a' := by rw [hℓ] at hℓ'; exact Option.some.inj hℓ'
  obtain rfl : v = v' := by rw [Hget] at hget'; exact Option.some.inj hget'
  obtain ⟨hre, hrρ, hσ⟩ : r.e = .val v ∧ r.ρ = ρ ∧ σ₂ = σ₁ := by
    simpa [Prod.mk.injEq] using hout
  subst hσ
  rw [hre, hrρ]
  imod Hclose with -
  imodintro
  isplitl [Hσ]
  · rw [probeStateInterp_eq]
    iexact Hσ
  · iapply wps_val
    iapply HΨ $$ Hpt

/-- Store small axiom at the statement layer (full ownership; the
    cell must be live — `HeadStep.store` requires presence, and the
    points-to supplies it). -/
theorem wps_store {Ψ : Int → TEnv → IProp GF} {ℓop vop : TOp} {ρ : TEnv}
    {av v v0 : Int} (hℓ : evalOp ρ ℓop = some av) (hv : evalOp ρ vop = some v) :
    iprop(pointsTo (GF := GF) av (DFrac.own 1) v0 ∗
      (pointsTo av (DFrac.own 1) v -∗ Ψ v ρ)) ⊢
      wps Q Ls Ψ (.store ℓop vop) ρ := by
  rw [(wps_unfold (e := .store ℓop vop)).to_eq]
  simp only [wps.pre, toValE_store, jumpRedex?_store]
  iintro ⟨Hpt, HΨ⟩ %σ₁ %ns %obs %obs' %nt Hσ
  rw [probeStateInterp_eq]
  ihave %Hget : ⌜Iris.Std.PartialMap.get? σ₁ av = some v0⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], ⟨Q, .val v, ρ⟩, Iris.Std.PartialMap.insert σ₁ av v, [],
      ⟨Step.head (K := []) (HeadStep.store hℓ hv Hget) rfl rfl, rfl, rfl⟩⟩
  inext
  iintro %r %σ₂ %eₜ %Hstep Hcred
  obtain ⟨hs, hfn, rfl⟩ := Hstep
  obtain ⟨a', v', v0', hℓ', hv', hget', hout⟩ := step_store_inv hs
  obtain rfl : av = a' := by rw [hℓ] at hℓ'; exact Option.some.inj hℓ'
  obtain rfl : v = v' := by rw [hv] at hv'; exact Option.some.inj hv'
  obtain ⟨hre, hrρ, hσ⟩ : r.e = .val v ∧ r.ρ = ρ ∧
      σ₂ = Iris.Std.PartialMap.insert σ₁ av v := by
    simpa [Prod.mk.injEq] using hout
  subst hσ
  rw [hre, hrρ]
  imod Hclose with -
  imod (genHeap_update (v₂ := v)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplitl [Hσ]
  · rw [probeStateInterp_eq]
    iexact Hσ
  · iapply wps_val
    iapply HΨ $$ Hpt

/-! ## Block specifications and the Löb-tied elimination -/

/-- Per-label block specification (donor `wps_block`,
    lifting.v:1302, adapted: the block precondition is indexed by
    the jump-argument value, and quantifies the jump-time env —
    label bodies must be verified for every env a jump may arrive
    in; the registered-continuation discipline makes bodies closed,
    so this quantifier is free in practice). -/
def wpsBlock (Q : TFn) (Ls : Nat → Int → IProp GF)
    (Ψ : Int → TEnv → IProp GF) (l : Nat) : IProp GF :=
  iprop(□ ∀ (px : Option Nat) (k : TExpr) (z : Int) (ρ : TEnv),
    ⌜Q l = some (px, k)⌝ -∗ Ls l z -∗ wps Q Ls Ψ k (bindPat px z ρ))

/-- All block specifications (donor `[∗ map] wps_block`,
    lifting.v:1306's premise collection; flat form — unregistered
    labels are vacuous because the lookup premise is
    unsatisfiable). -/
abbrev blockSpecs (Q : TFn) (Ls : Nat → Int → IProp GF)
    (Ψ : Int → TEnv → IProp GF) : IProp GF :=
  iprop(□ ∀ (l : Nat) (px : Option Nat) (k : TExpr) (z : Int) (ρ : TEnv),
    ⌜Q l = some (px, k)⌝ -∗ Ls l z -∗ wps Q Ls Ψ k (bindPat px z ρ))

theorem blockSpecs_wpsBlock {Ψ : Int → TEnv → IProp GF} (l : Nat) :
    blockSpecs Q Ls Ψ ⊢ wpsBlock (GF := GF) Q Ls Ψ l := by
  unfold blockSpecs wpsBlock
  iintro #H
  imodintro
  iintro %px %k %z %ρ %hQ HLs
  iapply H $$ %l %px %k %z %ρ %hQ HLs

/-- Assembling the block specifications needs NO Löb and no mutual
    assumption — the back-edge circularity is broken by the jump
    clause (each body's own jumps discharge against `Ls` directly).
    This is where the label-context shape pays: the donor
    `wps_block_rec`'s mutual-□ premise is not needed; its Löb lives
    in `wps_sound` below. -/
theorem blockSpecs_intro {Ψ : Int → TEnv → IProp GF}
    (h : ∀ l px k z ρ, Q l = some (px, k) →
      Ls l z ⊢ wps (GF := GF) Q Ls Ψ k (bindPat px z ρ)) :
    ⊢ blockSpecs Q Ls Ψ := by
  unfold blockSpecs
  imodintro
  iintro %l %px %k %z %ρ %hQ HLs
  iapply h l px k z ρ hQ $$ HLs

/-- THE LÖB-TIED ELIMINATION (the donor `wps_block_rec` analog +
    the stmt-WP-to-WP collapse in one): under the block
    specifications, the statement WP entails the base Iris WP with
    the value-channel postcondition. ONE Löb induction ties every
    back edge: at a jump redex the (□) block spec turns the label
    precondition into the body's statement WP, and the induction
    hypothesis — a step later, aligned with the jump step's ▷ —
    turns that into the base WP. Partial correctness (donor parity).

    This is also where the jump clause is CERTIFIED against the
    step relation: `step_jump_inv` (every step at a jump redex is
    THE context-independent jump) and `step_of_jumpRedex`
    (reducibility) are exactly the two directions the readiness
    review's "same successor" proof obligation asked for. -/
theorem wps_sound {Ψ : Int → TEnv → IProp GF} (e : TExpr) (ρ : TEnv) :
    blockSpecs Q Ls Ψ ⊢
      iprop(wps Q Ls Ψ e ρ -∗
        WP (⟨Q, e, ρ⟩ : TRt) @ Stuckness.NotStuck; ⊤ {{ w, Ψ w.z w.ρ }}) := by
  iloeb as IH generalizing %e %ρ
  cases htv : toValE e with
  | some z =>
    obtain rfl := toValE_eq_some htv
    rw [wps_unfold.to_eq, wp_unfold.to_eq]
    simp only [wps.pre, toValE_val, wp.pre, probe_toVal_eq, toValRt_mk,
      Option.map_some]
    iintro #HB Hwps
    imod Hwps with Hwps
    imodintro
    iexact Hwps
  | none =>
    have htoval : ToVal.toVal (Val := TRVal) (⟨Q, e, ρ⟩ : TRt) = none := by
      rw [probe_toVal_eq, toValRt_mk, htv]
      rfl
    cases hjr : jumpRedex? e with
    | some la =>
      obtain ⟨l, a⟩ := la
      rw [wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro #HB Hwps
      iapply wp_lift_step htoval
      iintro %σ₁ %ns %obs %obs' %nt Hσ
      imod Hwps with ⟨%px, %k, %z, %hl, %ha, HLs⟩
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      isplitr
      · ipureintro
        exact ⟨[], ⟨Q, k, bindPat px z ρ⟩, σ₁, [],
          ⟨step_of_jumpRedex hjr hl ha, rfl, rfl⟩⟩
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hfn, rfl⟩ := Hstep
      obtain ⟨px', k', z', hl', ha', hout⟩ := step_jump_inv hjr hs
      dsimp only at hl' ha' hout hfn
      obtain ⟨rfl, rfl⟩ : px = px' ∧ k = k' := by
        rw [hl] at hl'
        exact ⟨congrArg Prod.fst (Option.some.inj hl'),
          congrArg Prod.snd (Option.some.inj hl')⟩
      obtain rfl : z = z' := by rw [ha] at ha'; exact Option.some.inj ha'
      obtain ⟨hre, hrρ, hσ⟩ : r.e = k ∧ r.ρ = bindPat px z ρ ∧ σ₂ = σ₁ := by
        simpa [Prod.mk.injEq] using hout
      have hr : r = (⟨Q, k, bindPat px z ρ⟩ : TRt) := by
        obtain ⟨rfn, re, rρ⟩ := r
        simp only at hre hrρ hfn
        rw [hre, hrρ, hfn]
      subst hσ
      rw [hr]
      imod Hclose with -
      imodintro
      isplitl [Hσ]
      · simp only [List.length_nil, Nat.add_zero]
        iexact Hσ
      isplitr []
      · ihave Hwps' := HB $$ %l %px %k %z %ρ %hl HLs
        iapply IH $$ %k %(bindPat px z ρ) HB Hwps'
      · simp only [Algebra.BigOpL.bigOpL_nil]
        itrivial
    | none =>
      rw [wps_unfold.to_eq]
      simp only [wps.pre, htv, hjr]
      iintro #HB Hwps
      iapply wp_lift_step htoval
      iintro %σ₁ %ns %obs %obs' %nt Hσ
      imod Hwps $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%hred, Hwps⟩
      imodintro
      isplitr
      · ipureintro
        exact hred
      inext
      iintro %r %σ₂ %eₜ %Hstep Hcred
      obtain ⟨hs, hfn, hnil⟩ := Hstep
      have hr : r = (⟨Q, r.e, r.ρ⟩ : TRt) := by
        obtain ⟨rfn, re, rρ⟩ := r
        simp only at hfn
        rw [hfn]
      imod Hwps $$ %r %σ₂ %eₜ %(⟨hs, hfn, hnil⟩ :
          ((⟨Q, e, ρ⟩ : TRt), σ₁) -<obs>-> (r, σ₂, eₜ)) Hcred with ⟨HSI, Hwps⟩
      imodintro
      isplitl [HSI]
      · subst hnil
        simp only [List.length_nil, Nat.add_zero]
        iexact HSI
      isplitr []
      · rw [hr]
        iapply IH $$ %(r.e) %(r.ρ) HB Hwps
      · subst hnil
        simp only [Algebra.BigOpL.bigOpL_nil]
        itrivial

end StmtProbe
end CerberusHeapLang
