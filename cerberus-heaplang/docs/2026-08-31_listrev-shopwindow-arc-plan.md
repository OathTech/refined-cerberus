# Arc: list-reverse + the shop window

[USER 2026-08-31]: land list-reverse ("this would make the case this
is truly the reynolds/ohearn logic — without it, it's harder to
argue"), then a shop-window phase making the demo pedagogically
useful, closed by a fresh-eyes auditor roleplaying a PL reader who
knows nothing about the project. Pause before merge, per standard
practice.

## Phase A — list-reverse (the canonical exhibit)

Prerequisites (registered stretch items, sharpened by the [USER]
one-allocation array ruling):
1. NULL: an honest null-pointer encoding in the byte/MemValue model
   + the null-test as a pointer memop (same certification pattern
   as load: one memM lemma, one Step rule, one wps rule; WF/panic
   premises stated never absorbed).
2. NODES: one allocation per node, TWO fields inside it (value,
   next) — intra-node field access by pointer arithmetic (legal
   within the allocation), inter-node traversal by LOADED pointers
   (each carrying its own provenance). The exhibit demonstrates
   both halves of the pointer discipline in one program.
3. THE PREDICATE: `isList p xs` by plain structural recursion on
   the mathematical list (no step-indexing — readiness-checked);
   node cells composed by ∗.
Then THE PROOF, textbook shape mandatory (the point of the
exhibit): in-place reversal loop, invariant
`isList p reversed ∗ isList q rest` with
`xs = reversed.reverse ++ rest`, via blockSpecs_intro + small
axioms + frame — no monolithic unfolding; certified through the
engine lane like fib; variant → total export if it falls out along
the fib pattern (best effort, not gating). Standing discipline:
signature diff vs the S4 snapshot; findings itemized; claims never
outrun theorems.

## Phase B — the shop window (pedagogy)

For a READER, not a reviewer: a worked walkthrough doc (what a Core
program looks like, what a triple over the real engine means, how
to check a claim yourself in minutes — commands run, output
pasted); module ordering/naming pass so the package reads in
teaching order; README recast to make the Reynolds/O'Hearn claim
explicitly and back it immediately with the exhibit table
(store/load → frame → loops → fib total → array → LIST-REVERSE);
divergence register kept crisp. No proof-content changes in this
phase (docs/naming only; renames mechanical with the audit
following).

## Phase C — the close

The fresh-eyes NAIVE-PL-READER review ([USER]-mandated instrument):
an auditor roleplaying a PL-literate reader who knows separation
logic and roughly what Iris is, and has NEVER heard of Cerberus,
lem, or this project. Acceptance questions: within minutes, can
they tell WHAT is proved, over WHAT semantics, WHY the trust story
holds, and HOW to check it; anything reading as jargon, overclaim,
or unexplained magic is a finding. Findings folded; then the
standard skeptical close audit if content changed materially; then
PAUSE for the [USER] merge word.
