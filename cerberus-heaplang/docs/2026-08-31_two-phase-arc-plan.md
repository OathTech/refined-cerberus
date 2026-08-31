# The two-phase arc: restratify, then loops

[USER 2026-08-31] end state, verbatim framing: "a tiny separation
logic (really just reynolds/ohearn) over a synthetic fragment of
core. So not at all RefinedC, but it'll derisk a lot of the
fundamental machinery." Base logic is PARTIAL CORRECTNESS (donor
parity — RefinedC is partial); termination measures are an optional
variant layer whose product (step bounds) upgrades conclusions to
the unconditional production `.done` equation. Input evidence:
`2026-08-31_while-lang-readiness.md` (the rework findings) and the
merge audit.

## Phase 1 — restratify, coverage-preserving

Same coverage (branch-free sequential fragment); rules re-phrased so
loops/branching become additive later.
- S0 FIRST (kill-criterion probe, the risky kernel): the
  statement-WP stratification in the donor's shape (stmt_wp/
  wps_goto/wps_block_rec analogs over the engine's static label
  map) + the jump-aware sequencing proof, over a toy Step WITH env.
  Kills: sequencing unprovable without a false Context instance;
  whole-run machinery forced into judgments; the perf wall. A kill
  ends the phase with the evidence.
- S1: env into the language tuple (live state; betas stay
  pure-deterministic; Mem/heap layer untouched); rule phrasing
  generalizes to operand-evaluated forms (ACTION_EVAL shape; pexpr
  lemma library stays lazy).
- S2: migrate the corpus onto the stratified layer.
- ACCEPTANCE = the frozen-corpus regression gate: every current
  exported theorem re-proves with statements unchanged or
  strengthened (diffed against the pre-phase exports); a changed
  statement is a finding with justification, never a silent
  re-baseline. Gates green both packages; no new qualifiers;
  drive-monotonicity only if free (else phase 2).

## Phase 2 — extend (gated on phase 1)

Eif/Ecase (mixed guard granularity as measured); Esave/Erun; the
loop rule in two forms — invariant-only (partial, default) and
invariant+variant (well-founded measure → step bound); the
termination-accounting restatement (reachability invariant +
drive-monotonicity; bounds discharge hterm/fuel); allocator-cursor
resource for wp_create; pexpr arithmetic and pointer memops as the
exhibits need; panic channels excluded by stated WF premises.
ACCEPTANCE: fib and list-reverse verified end-to-end on authored
Core through the loop rule and the production entry; the README
scope section updated to match, still claiming nothing beyond the
theorems.

## Amendment ([USER 2026-08-31], pre-phase-2): acceptance exhibits

Phase 2 ACCEPTANCE = fib + an ARRAY-WALK exhibit (array-sum first;
in-place increment if cheap): loops, invariants, variants for the
bounds, pointer arithmetic, big-sep pre-states (∗_{i<n} base+i ↦
vs[i] — no recursion; the bigSepA_ptx plumbing already exists).
LIST-REVERSE demotes to a REGISTERED STRETCH with three named
prerequisites, each priced small, none gating the phase: a null
encoding in the byte model + the null-test memop; a struct-free
node encoding (two adjacent cells); the recursive representation
predicate (plain structural recursion on the mathematical list —
no step-indexing, per the readiness check). Rationale: pre-states
for unbounded linked data are the subtle part; the array walk
isolates loop machinery from the linked-data layer, so a phase-2
failure is attributable.
