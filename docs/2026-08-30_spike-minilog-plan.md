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
