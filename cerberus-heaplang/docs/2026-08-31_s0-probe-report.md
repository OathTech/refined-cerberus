# S0 jump-kernel probe report (2026-08-31)

[AGENT] S0 worker report, per the two-phase arc plan
(`2026-08-31_two-phase-arc-plan.md` §Phase 1) and the readiness
review's §5.0 probe prescription
(`2026-08-31_while-lang-readiness.md`). The probe artifacts are
`CerberusHeapLang/StmtProbe/{Toy,Wps,Demo}.lean` (+ the
`StmtProbe.lean` root), wired into the lib root ahead of Audit.lean;
all probe theorem cones are exactly the classical trio (curated pins
added for `wps_seq`, `wps_sound`, `demo_loop`); both audits green.

## Verdict up front: GO

The statement-stratified WP architecture works over a toy with the
engine-measured jump shape (context-discarding `run` against a
static label map, live env in the expression tuple): the jump-aware
sequencing lemma is proved with no `Language.Context` instance and
no unsoundness-shaped weakening; the loop demonstration (back-edge
jump + per-label invariant + env-carried counter) lands in the BASE
Iris WP as partial correctness; the current corpus's exhibit shapes
re-prove on the stratified layer by re-phrasing. No kill criterion
fired — with one judged distinction on the "new WP definition"
criterion, flagged for operator review in §5.

## 1. The central finding: the donor's literal `stmt_wp` shape does
## not transplant; the label-context shape does

The donor's `stmt_wp` (lifting.v:1002) is a single-Φ CPS wrapper
over the base WP:

    stmt_wp E Q Ψ s := ∀ Φ rf, ⌜Q = rf.f_code⌝ -∗
        (∀ v, Ψ v -∗ WP (Return v) {{Φ}}) -∗ WP (to_rtstmt rf s) {{Φ}}

`wps_goto` and `wps_block_rec` port to that shape without trouble.
What does NOT is SEQUENCING — and the donor never needs it, because
Caesium's statement grammar is syntactically continuation-passing
(`Assign o1 o2 e s` carries its continuation `s`; `Goto` only ever
sits in statement tail position, so no rule ever composes a
jump-capable subterm with a pending continuation). Core's `Esseq`
binds an arbitrary jump-capable subexpression — the measured
elaborated loop has `run while_…` under the sseq spine (readiness
§2.1) — so the arc MUST compose through jumps.

Why the CPS wrapper cannot do it (the analysis that drove the
design; meta-level argument, recorded here as evidence — it is an
unprovability-of-shape claim, not a machine-checked theorem): to
derive `wps Ψ (seq px e1 e2)` from a wps premise about `e1`, the
proof must instantiate the premise's `∀ Φ'` once, and the two exit
modes need DIFFERENT `Φ'`:

- the value channel (e1 finishes with z, e2 must still run) needs
  `Φ' = the bind-post` (`fun w => WP e2[bind] {{Φ}}`) — but then the
  jump channel would owe `WP cont {{bind-post}}`, which is false:
  after a real jump `e2` is dead, yet the bind-post re-runs it at
  the label continuation's end;
- the jump channel (e1 jumps; the sseq-extended registered
  continuation covers the program's remainder) needs `Φ' = Φ` — but
  then the value channel would owe `Ψ₁ z -∗ Φ z`, i.e. that e1's
  intermediate value is a final program value.

The root cause: the base WP of `e1`-standalone runs THROUGH a jump
to the program's real end, so its postcondition conflates e1's own
values with program-final values; no single-Φ wrapper over it can
split the exits. (Adding a jump channel to the wrapper — `□(Ls l z
-∗ WP cont {{Φ}})` as an extra premise — fails the same way: the two
channels still share the one Φ.)

The shape that works is the classical LABEL-CONTEXT statement logic
(de Bruin 1981-style label-assumption judgments, the standard form
in program logics for unstructured control flow), realized as a
guarded fixpoint with a JUMP CLAUSE: at a jump redex the judgment's
obligation is the per-label precondition, and tracking stops there —
each exit mode has its own clause, so the Φ-clash never forms.

## 2. The Lean shape that worked (the definitions)

Toy (Toy.lean; mirror notes in its header — static label map riding
in the expression tuple exactly like Caesium's `to_rtstmt rf`,
`Step.jump` computing its successor without the frame stack, env in
the expression per readiness R2):

```lean
abbrev TFn := Nat → Option (Option Nat × TExpr)          -- static label map
structure TRt where fn : TFn; e : TExpr; ρ : TEnv        -- Language Expr
structure TRVal where fn : TFn; z : Int; ρ : TEnv        -- Language Val
inductive Step (fn : TFn) : TExpr × TEnv × THeap → TExpr × TEnv × THeap → Prop
  | head : HeadStep e ρ σ e' ρ' σ' → …fill K e… → …fill K e'…   -- rebuilt redex
  | jump : fn l = some (px, k) → evalOp ρ a = some z →
      …fill K (.run l a)… → Step fn (eK, ρ, σ) (k, bindPat px z ρ, σ)
instance : Language TRt THeap Empty TRVal
```

The statement WP (Wps.lean), a guarded fixpoint via iris-lean's
PUBLIC Banach machinery (`fixpoint` + a hand-proved
`OFE.Contractive` instance copied from the `wp.pre.contractive`
template; iris-lean itself untouched):

```lean
def wps.pre (Q : TFn) (Ls : Nat → Int → IProp GF) (F) (Ψ) (e) (ρ) : IProp GF :=
  match toValE e with
  | some z => |={⊤}=> Ψ z ρ                                    -- value channel
  | none => match jumpRedex? e with
    | some la => |={⊤}=> ∃ px k z, ⌜Q la.1 = some (px,k)⌝ ∗
        ⌜evalOp ρ la.2 = some z⌝ ∗ Ls la.1 z                   -- JUMP clause
    | none => ∀ σ₁ ns obs obs' nt, stateInterp … ={⊤,∅}=∗
        ⌜Reducible (⟨Q,e,ρ⟩, σ₁)⌝ ∗ ▷ ∀ r σ₂ eₜ, ⌜step⌝ -∗ £1 ={∅,⊤}=∗
        stateInterp … ∗ F Ψ r.e r.ρ                            -- step clause
def wps (Q) (Ls) : (Int → TEnv → IProp GF) → TExpr → TEnv → IProp GF :=
  fixpoint (wps.pre Q Ls)
```

`jumpRedex? : TExpr → Option (Nat × TOp)` is the structural
redex search through the `seq` spine; `jumpRedex? (seq px e1 e2) =
jumpRedex? e1` is the SYNTACTIC image of the engine's
context-discard, and `step_jump_inv`/`step_of_jumpRedex` (Toy.lean)
certify the clause against the step relation: at a jump redex,
every step is THE jump and its successor is frame-independent.

The rule set proved over it (Wps.lean, key signatures):

```lean
theorem wps_run  (hl : Q l = some (px,k)) (ha : evalOp ρ a = some z) :
    Ls l z ⊢ wps Q Ls Ψ (.run l a) ρ                     -- wps_goto analog
theorem wps_seq  :                                        -- THE R1 obligation
    wps Q Ls (fun z ρ' => wps Q Ls Ψ e2 (bindPat px z ρ')) e1 ρ ⊢
      wps Q Ls Ψ (.seq px e1 e2) ρ
theorem wps_wand : wps Q Ls Ψ₁ e ρ ⊢ (∀ z ρ', Ψ₁ z ρ' -∗ Ψ₂ z ρ') -∗ wps Q Ls Ψ₂ e ρ
theorem wps_frame : wps Q Ls Ψ e ρ ∗ R ⊢ wps Q Ls (fun z ρ' => Ψ z ρ' ∗ R) e ρ
theorem wps_val / wps_ifz_zero / wps_ifz_nonzero / wps_load / wps_store
abbrev  blockSpecs Q Ls Ψ := □ ∀ l px k z ρ, ⌜Q l = some (px,k)⌝ -∗
      Ls l z -∗ wps Q Ls Ψ k (bindPat px z ρ)             -- [∗map] wps_block
theorem blockSpecs_intro : (∀ l px k z ρ, Q l = some (px,k) →
      Ls l z ⊢ wps Q Ls Ψ k (bindPat px z ρ)) → ⊢ blockSpecs Q Ls Ψ  -- NO Löb
theorem wps_sound (e ρ) : blockSpecs Q Ls Ψ ⊢               -- ONE Löb, ties all
      wps Q Ls Ψ e ρ -∗ WP ⟨Q,e,ρ⟩ @ NotStuck; ⊤ {{ w, Ψ w.z w.ρ }}
```

Donor correspondence (the mission's `wps_goto`/`wps_block`/
`wps_block_rec` items):

| donor (lifting.v) | probe | delta |
|---|---|---|
| `stmt_wp` :1002 | `wps` | CPS wrapper → label-context fixpoint (§1 forcing fact: Core's Esseq grammar) |
| `wps_return` :1107 | `wps_val` | value channel in place of Return |
| `wps_goto` :1112 | `wps_run` | jump = consult the label precondition; near-definitional (the clause IS the rule); the donor's `▷` is paid at the actual step inside `wps_sound` |
| `wps_block` :1302 | `wpsBlock` / `blockSpecs` | precondition indexed by the jump-argument value; jump-time env quantified (bodies are closed under the sseq-extended registration discipline, so the quantifier is free) |
| `wps_block_rec` :1306 | `blockSpecs_intro` + `wps_sound` | the mutual-□ + iLöb of the donor SPLITS: per-label proofs need NO Löb (the jump clause breaks the back-edge circularity); the one Löb induction lands in `wps_sound`, which is simultaneously the stmt-WP-to-WP collapse |
| (no donor analog) | `wps_seq` | the jump-aware sequencing lemma — the thing the CPS grammar exempted the donor from |

## 3. What the jump-aware sequencing proof actually needed

`wps_seq` is a Löb induction with three cases:

1. **e1 finished** (`toValE e1 = some z`): the conclusion's step
   clause; the unique step is the beta (`step_seq_factor`, first
   disjunct + `step_val_elim`/`jumpRedex?` exclusions of the
   others); the continuation `wps Ψ e2 (bindPat px z ρ)` comes
   straight from the premise's value channel. No Löb IH used.
2. **e1 at a jump redex** (`jumpRedex? e1 = some (l,a)`): the two
   sides' jump clauses are the SAME FORMULA — `jumpRedex? (seq px
   e1 e2) = jumpRedex? e1` and the clause never mentions Ψ or the
   frame. The proof is `iintro H; iexact H`. This is where the
   engine's context-discard pays: the jump obligations are computed
   from the redex and env alone, so `seq`-framing is invisible.
3. **e1 steps**: `step_seq_factor` (the readiness's "factor theorem
   gains one disjunct" — beta / framed step / global jump, the
   jump disjunct excluded by case 2's hypothesis), `Step.lift_seq`
   for reducibility transfer, then the Löb IH one step later.

The SEMANTIC content of case 2 — that the syntactic clause transfer
is justified against the real step relation — is paid exactly once,
in `wps_sound`'s jump case: `step_of_jumpRedex` (reducibility at a
registered label) and `step_jump_inv` (every step at a jump redex is
the jump, successor `(k, bindPat px z ρ, σ)` independent of the
decomposition). Those two lemmas are the probe form of the readiness
review's "same successor" proof obligation, and their Core
analogues are the new engine-certification obligations of S3 (§6).

What was NOT needed: no `Language.Context` instance for the `seq`
frame (none exists in the probe — deliberately), no weakening of any
rule statement, no whole-run machinery in the judgment (indices are
`Q, Ls, Ψ, e, ρ`; `Q` is the static map, `Ls` is logic-side data),
no touch inside iris-lean.

## 4. The demonstrations

**The toy loop** (Demo.lean): counter in the ENV via the jump
argument (Erun parameter rebinding), a heap cell bumped every
iteration, guard on the env-bound counter — all three live-env
mechanisms of readiness R2 exercised. The registered body is
sseq-extended (its exit branch returns the program's final value).

```lean
theorem demo_loop [ProbeGS hlc GF] (v0 n : Int) (hn : 0 ≤ n) (ρ : TEnv) :
    pointsTo cAddr (DFrac.own 1) v0 ⊢
      WP (⟨demoFn, .run loopLbl (.lit n), ρ⟩ : TRt) @ NotStuck; ⊤
        {{ w, ⌜w.z = v0 + n⌝ ∗ pointsTo cAddr (DFrac.own 1) (v0 + n) }}
```

with the per-label invariant `demoLs v0 n loopLbl x = ⌜0 ≤ x ≤ n⌝ ∗
cAddr ↦ v0 + (n − x)`. The block proof (`demo_block`) is
Löb-free — the back edge is one `wps_run` against the invariant at
`x−1`; `wps_sound` (the one Löb) lands it in the base WP. Partial
correctness, donor parity; the conclusion is a plain Iris `WP`, so
the eventual adequacy story is untouched.

**Coverage preservation** (`probe_store_frame`,
`probe_seq_stores`): the current corpus's two exhibit shapes (store
under FRAME = Rules.lean `exhibit`; two sequenced disjoint stores =
`exhibitC_triple`) re-proved on the stratified layer with the SAME
compositional discipline (small axiom + frame + sequencing;
distinctness carried by ∗ alone) — and for an ARBITRARY label
context `(Q, Ls)`, since jump-free code never consults it. S2's
migration of the corpus is therefore a re-phrasing, not a re-proof.

## 5. Kill-criteria review (pre-registered list)

- **"Jump-aware sequencing unprovable without a false Context
  instance or unsoundness-shaped weakening"** — did not fire:
  `wps_seq` proved, no Context instance anywhere in the probe, rule
  statements unweakened.
- **"Whole-run machinery forced into judgment indices"** — did not
  fire: see §3.
- **"Perf wall (~1hr per attempt)"** — did not fire by two orders
  of magnitude: per-file elaboration of the probe modules is
  seconds (lake module builds: Toy ≈0.8s, Wps ≈1.1s, Demo <1s —
  derived from build logs); the full two-package gate run is
  minutes and dominated by the pre-existing corpus.
- **"(b) needs a new WP definition inside iris-lean itself"**
  (readiness §5.0 wording) — JUDGED NOT FIRED, with the distinction
  flagged for operator review: iris-lean is untouched; `wps` is a
  package-local DERIVED judgment built from iris-lean's public
  `fixpoint`/`Contractive` API (the same machinery `wp` itself uses)
  and is eliminated into the unmodified base WP by `wps_sound`, so
  the base WP remains the sole semantic/adequacy interface. What the
  probe DOES establish is that the donor's wrapper-style `stmt_wp`
  (a definition-over-WP, no new fixpoint) is not attainable for
  Core's grammar (§1) — a derived fixpoint judgment at the package
  level is the honest price of expression-grammar jumps. If the
  operator reads the criterion as banning any new fixpoint judgment
  anywhere, this is a KILL-shaped fact and the report is the record;
  the worker's reading is that the criterion guards iris-lean's
  boundary, which is intact.

## 6. Migration prescription for S1/S2 (and the S3 landing)

- **S1 (env rework, unchanged from the readiness prescription —
  the probe validates the shape):** env into the language
  expression (`E := CoreExpr × EnvStack`, `Val := SpikeVal ×
  EnvStack`, componentwise `toVal`/`ofVal` — the probe's
  `TRt`/`TRVal` pattern, minus the label-map component which S1
  does not yet need). Betas stay `wp_lift_pure_det_step_no_fork`
  lifts; `Mem`/Heap.lean untouched. The probe's
  record-plus-projections Language instance worked with zero
  friction beyond `dsimp`-normalizing literal-record projections in
  proofs.
- **S2 (corpus migration):** migrate rules to `wps_*` form
  mechanically — the probe's `wps_store`/`wps_load` show the exact
  pattern (same UB-exclusion preconditions; the reducibility side
  condition discharged by the points-to through the coupling
  invariant; the house `storeM_success`/`loadM_success` engine
  seams are reused verbatim inside the clause-level step handler).
  Current `wp_sseq`'s statement survives as the no-jump corollary
  of the sequencing lemma; the corpus re-proves per
  §4's coverage-preservation evidence. Statement diffs for the
  frozen-corpus regression gate: post shapes gain the (ignorable)
  final-env argument, triples restate over `wps` with a
  quantified/arbitrary label context — flag both in the gate diff
  as strengthenings.
- **S3 (the jump layer on the Core mirror):** add the label map to
  the runtime tuple (or equivalently the frozen-context
  restatement: `blockSpecs`'s `Q` is tied to
  `core_run_state.labeled` by a pure equation — the donor's
  `⌜Q = rf.f_code⌝` analog; legitimate because nothing writes
  `labeled` on the positive sequential path). Define the Core
  `jumpRedex?` mirroring `get_ctx`'s decomposition restricted to
  the fragment's frames (Esseq spine now; new frames extend it
  together with the factor theorem), and prove the two
  certification lemmas the probe identified as THE load-bearing
  pair: the factor theorem's jump disjunct and the jump-redex
  inversion (engine cites: step_ctx's Erun arm,
  Core_reduction.lean:484; label lookup and `current_proc_opt`
  panic channels excluded by WF premises per the readiness table).
  Port `wps.pre`/`Contractive`/`wps_unfold` by template (the
  contractivity proof is shape-copying, ~25 lines). The loop rule
  is `blockSpecs_intro` + `wps_sound` — expect the Core `wps_sound`
  to be the one genuinely laborious proof (it was the longest in
  the probe), structured exactly as here: value / jump / step, with
  the step case a transfer and the jump case the block-spec
  consultation one ▷ later.
- **Mechanical frictions to expect** (all encountered and solved in
  the probe, none architectural): match-reduction discipline
  (per-constructor simp lemmas for `toValE`/`jumpRedex?`, never
  unfolding the defs over variable scrutinees); `bindPat`/env
  normalization to cons form before proofmode unification;
  `Persistent` visibility for the block-spec context (abbrev or an
  explicit instance); subst-direction discipline in inversion
  aftermath (state equalities with the surviving variable on the
  LEFT); the house `ihave`-pure-assert borrow pattern for
  `genHeap_valid`; `omega` in place of the absent `ring`.

## 7. Inventory and gate status

- `CerberusHeapLang/StmtProbe/Toy.lean` — toy language, step
  relation, inversion/factor lemmas, `Language` instance.
- `CerberusHeapLang/StmtProbe/Wps.lean` — ghost state (ProbeGS +
  `ProbeGF` non-vacuity witness for the prerequisites; the bundled
  GS is constructible by the house Adequacy.lean allocation pattern
  — Prop-level adequacy is out of S0 scope by charter), `wps`
  fixpoint + contractivity + unfolding, the rule set, block specs,
  `wps_sound`.
- `CerberusHeapLang/StmtProbe/Demo.lean` — corpus shapes + the loop.
- Wiring: `CerberusHeapLang/StmtProbe.lean` imported by the lib
  root ahead of `Audit.lean`; Audit imports the probe, so both
  sweeps (trio-exactness over every theorem; banned-axiom check
  over every constant) cover it; curated pins added for `wps_seq`,
  `wps_sound`, `demo_loop` (each exactly
  `[propext, Classical.choice, Quot.sound]`).
- Gates: `./scripts/test_unit.sh` ALL GREEN at commit time (grep
  ban + both package builds, audits elaborated in-build).
