# Spike: a minimal separation logic over the real Core semantics

[USER 2026-08-30]: set the charter branch aside (parked:
`charter-aims-amendment`, unmerged record); work a design spike — "a
synthetic ultra-simple separation logic *over* the real core
semantics for a tight subset of the core AST." Ultra-simple
synthetic Core programs, no C, no RefinedC richness. The spike IS
the design work: every artifact settles a real design question at
minimum scale.

Constraints that carry over (rulings, not charter): cerberus-lean is
the only trusted semantics; iris-lean is the middle layer; kernel-
only proofs, trio cones, capped/gated builds; ~1hr grind bar;
stop-and-report on kills.

## The fragment (tight AST subset)

Synthetic Core programs authored in Lean as values of the ENGINE'S
generated AST types (no mirror grammar — non-negotiable):
- pure expressions: values only (substitution-closed; no
  environment);
- actions: `load`, `store` (allocation handled by SEEDING the
  initial memory state through the engine's own `allocateObject`;
  create/kill join the fragment only if seeding proves awkward);
- sequencing: strong sequencing (Esseq) first; weak (Ewseq) if free.
Nothing else. No unseq, no calls, no save/run, no Eif (Eif is the
first post-spike extension candidate, not in scope).

## Artifacts (each = a design decision settled by construction)

0. **Recon** (`docs/` note, half-day cap): pin the exact generated
   types — the expression AST constructors for the fragment, the
   memory-state type behind `memM`, the engine's stepping entry for
   expression-level reduction, and how `loadM`/`storeM`
   (CerbMem.lean:1586/1632) thread state. Output: the fragment's
   type signatures, written down with file:line cites.
1. **`RefinedCerberus/Spike/Step.lean`** — an inductive small-step
   `Step : Expr → Mem → Outcome → Prop` (exact shape from recon)
   for the fragment: one rule per construct, each with a mirror-cite
   to the engine behavior it reflects. Hand-written, grammar-keyed,
   zero authority: the soundness theorem (artifact 4) is what makes
   it mean anything.
2. **`Spike/Heap.lean`** — points-to over the engine's memory
   state via iris-lean ghost state (GenHeap if it fits). The
   granularity decision (byte-list vs value-level) is made HERE and
   recorded with its reasoning.
3. **`Spike/Rules.lean`** — the logic: `wp_load`, `wp_store`,
   `wp_seq` (bind); frame comes from Iris. WP via iris-lean's
   Language instance if it fits the fragment cleanly, else a direct
   WP definition over `Step` (decision recorded — donor shape
   preferred, not worshipped at spike scale).
4. **`Spike/Soundness.lean`** — THE POINT: soundness of the rules
   against the real engine for the fragment. Coupling target chosen
   by provability: candidate seams, tried in order — (a) the memM
   sub-machine (`loadM`/`storeM` against the memory state), (b) the
   expression-level reduction entry, (c) a whole-driver wrapper run
   of a one-procedure synthetic file. The chosen seam and the
   rejected ones are the spike's principal design finding.
5. **`Spike/Exhibit.lean`** — two end-to-end theorems on concrete
   synthetic programs (store-then-load returns the stored value;
   frame across an unrelated location), trio-clean cones, joined to
   the in-build audit sweep.

## Kill criteria (pre-registered; a kill ends the spike with a report)

- K1 no coupling seam admits a soundness statement without
  whole-run machinery entering the judgments — reported as EVIDENCE
  on the [USER]-raised goal-level hypothesis (the Core↔Caesium
  abstraction gap may make the target mis-set), not worked around.
- K2 the perf tripwire (the measured pathological-unfolding regime,
  or the ~1hr bar).
- K3 iris-lean fit failure (instantiation forces the rules out of
  recognizable separation-logic shape).

## Non-goals

No C elaboration, no RefinedC typing layer, no automation, no
classifier, no charter revisions. The spike report (a dated doc:
what was settled, what was found, what broke) is the input to
whatever plan comes next.

## Process

Work on this branch (`spike-minilog`) in its worktree; iterate with
per-file probes; substantive commits on green steps; gates before
any claim. Semantics pin: 8fb380c9c (bumped here from a8f86112d —
records-only upstream delta, re-verified stamp-identical at setup).

## Acceptance: the classic package ([USER 2026-08-30], the go order)

The spike passes when the following are theorems, and the exhibit
proofs are COMPOSITIONAL (small axiom + structural rule, never
monolithic):
- SMALL AXIOMS:  {x ↦ -} store(x,v) {x ↦ v}   and
  {x ↦ v} load(x) {r. ⌜r = v⌝ ∗ x ↦ v}
- FRAME:  {P} e {Q}  ⊢  {P ∗ R} e {Q ∗ R}
- SEQ/BIND:  {P} e1 {Q} and {Q} e2 {R}  give  {P} e1;e2 {R}
  (value-binding form as the fragment needs)
- CONSEQUENCE (from BI entailment), and wp_wand.
- THE EXHIBIT (the operator's form, derived by FRAME on the store
  small axiom):  {x ↦ - ∗ y ↦ a} store(x,7) {x ↦ 7 ∗ y ↦ a}
- one anti-frame sanity check: the derivation FAILS (stuck goal)
  without the y-cell in the precondition when the postcondition
  claims it — locality is real, not decorative.
Triples are defined over the Iris WP in the standard way; all of
the above discharge through artifact 4's soundness into
engine-behavior statements.

## Full-build derisk register ([USER 2026-08-30]: "derisk aspects of
the full RefinedC build")

Spike decisions are made FULL-BUILD-FORWARD: where costs are close,
choose the option the RefinedC port will actually stand on (the port
map's consumed-interface strata are the reference). Target risks —
the report closes each as RETIRED / OPEN / CHANGED-SHAPE:
- R1 the coupling seam (which engine entry adequacy targets) — the
  full build inherits this choice directly.
- R2 points-to basis: must be growable to the donor's ty_deref/
  ty_ref shape (l ◁ₗ ty ⟷ l ↦ v ∗ v ◁ᵥ ty) — weigh byte/MemValue
  granularity against what loadM/storeM manipulate AND what the
  typing stratum needs; a convenience ↦ that can't carry the type
  system retires nothing.
- R3 WP form: prefer iris-lean's WP with the mask/fupd structure
  (the donor's typed_read_end E→∅ discipline needs it later) over a
  bespoke minimal WP.
- R4 UB channel: the WP must be UB-EXCLUDING (safety = loadM/storeM
  failure impossible under the precondition), not success-partial —
  UB-freedom is RefinedC's product.
- R5 provenance honesty: x in x ↦ v is a real PointerValue with
  provenance; the small axioms must not idealize it away.
- R6 the bind/sequencing story: wp_seq through Iris bind over real
  Esseq — tests the "bind layer dissolves" finding on live proofs.

## Stretch S1: the donor stratum in miniature ([USER]: "prototype
aspects of that design 'in miniature'")

Gated on the core package landing green (never at its expense): one
miniature of the RefinedC type stratum over the spike substrate —
- a baby type former `intT : Z → SpikeTy` with the donor's
  factorization in miniature: `l ◁ₗ intT z  ⟷  l ↦ v ∗ v ◁ᵥ intT z`
  (ty_deref/ty_ref shape, type.v:277-282 as the reference), where
  `v ◁ᵥ intT z` says the real MemValue encodes z;
- ONE typed rule in the donor's judgment shape (a miniature
  typed_write or typed_read) proved from the small axioms +
  factorization — demonstrating the typing stratum grows on this
  substrate by construction;
- the exhibit re-proved at the typed level.
This prototypes, in miniature: the type-former interface, the
value/location ownership split, and the typing-layer-on-WP
architecture — the three load-bearing joints of the full build.

## Extension D: the real engine entry ([USER 2026-08-30]: "extend
this to cover the real engine, not our hand-rolled driver")

Retire the drive-vs-production delta: re-export the semantic triples
against the SHIPPED pipeline — `runND` over the production driver
from `initial_driver_state`, through the `finalize`/`Driver.hack`
readout. Obligations: D1 scheduler collapse (single-thread round =
our loop body, by unfolding Driver.lean's round); D2 runND
branch-free collapse (branch-freeness already proved per-construct);
D3 hack-on-value readout lemmas; D4 `create` joins the fragment
(self-contained programs) + the cold-start theorem from
`initial_driver_state file fs`. Known unknown, resolved either way
honestly: whether the production path's cone touches `runEffectful`
— trio-clean if avoidable, else the one declared boundary appears in
the final cones with its mover, pinned exactly.
