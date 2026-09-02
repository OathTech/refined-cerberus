# Foundations Phase 3 — total correctness into the logic (design record + oracle + exit criteria)

Worker slice record, foundations arc Phase 3 (arc plan
`docs/2026-08-31_foundations-arc-plan.md` §Phase 3; audit F-02 and
the Phase-3 remediation list + exit criteria,
`docs/2026-08-31_cerberus-heaplang-foundational-audit.md`).
Commits: `d0ae541` (1/3, the total layer), `e92f7f1` (2/3, the
clients + the negative test), this commit (3/3, oracle + records).
Gates: `scripts/test_unit.sh` ALL GREEN at every commit.

## 1. The TWP fit (audit remediation item 1 — the gating question)

The pinned Iris `TotalWeakestPre`/`TotalAdequacy` instantiate over
the existing `Language CoreRt Mem Empty CoreRVal` instance AS-IS:
the probe (notation `WP … [{ … }]`, `twp.unfold`, `twp.to_wp`,
`twp_total`) elaborated with zero changes to any instance or to
iris-lean. No stop-and-report condition arose; no fixpoint was
hand-rolled for the TWP itself. `wpt_sound` (below) is the pinned
TWP's first consumer; `twp_total` is consumed as-is by
`wpt_strongly_normalizing`.

## 2. The total statement judgment (`wpt`, Wpt.lean)

[AGENT] design decisions, with reasoning:

- **Structural recursion on a step budget, no fixpoint machinery.**
  `wpt M Ls k Ψ e ρ` is defined by recursion on `k`: the step
  clause recurses at `k−1`; the jump clause does not recurse (the
  body's obligation lives in `blockSpecsT`); at `k = 0` a non-value,
  non-jump term is `⌜False⌝`. This is the least-fixpoint discipline
  of total WPs realized through the budget's well-foundedness — no
  Löb, no ▷, no `BIMonoPred`/OFE plumbing. The collapse and both
  adequacy proofs are inductions on the budget.

- **THE MANDATORY DECREASE (the audit's exact criterion).** Label
  preconditions are VARIANT-INDEXED (`LabelSpecT GF = sym → Nat →
  List value → EnvStack → IProp GF` — the classical Floyd variant as
  a specification parameter); the jump clause demands
  `∃ m, ⌜1 + m ≤ k⌝ ∗ Ls l m vs ρ`, and `blockSpecsT` requires every
  label body verified at budget `m` for EVERY claimed variant. The
  decrease is a structural component of the judgment, not an
  optional hypothesis — `blockSpecs_intro_variant` (the audit's
  zero-consumer lemma) is DELETED, replaced by
  `blockSpecsT`/`blockSpecsT_intro`.

- **Variant-in-the-invariant, forced by list-reverse.** A first cut
  indexed the judgment by a measure function
  `μ : sym → List value → Nat`; list-reverse's variant (the
  remaining chain length) is heap-resident and not computable from a
  pointer argument, so the measure moved into the label
  precondition's index, where the invariant pins it
  (`m = lrCost rest'.length`). This is the classical shape and
  subsumes the function form (fib pins `m = 2·(n−i)+3` the same
  way).

- **The variant IS the step budget (fused, deliberately).** A
  rule's budget = its own engine steps + the delivery cost of its
  final value (1 bare / 2 annot — the REMOVE-ANNOT tau); sequencing
  composes budgets additively, the bound value's delivery cost
  prepaying the beta (pure) or beta + wrapper merge (annot). One
  mechanism yields both halves the audit ordered separated:
  termination (the budget is the well-founded measure) and the
  executable bound (the budget is drive fuel). Budgets are upper
  bounds (`wpt_mono_k`), so clients may over-approximate.

- **Rule set**: mirrors of the wps rules consumed by the exhibits —
  the value/jump rules, one generic deterministic-tau lifting
  (`wpt_det_step`) instantiating if/save/pure/load-eval/store-eval/
  memop-eval/memop-ptreq, the three sequencing rules + the
  annotation layer (strong induction on the budget replacing Löb),
  and the generic typed-subrange memory rules
  (`wpt_load_at`/`wpt_store_at` + whole-cell forms), each priced at
  3 (access step + annot-value delivery). NOT mirrored (RED in the
  manifest, registered): create / Ecase / Ewseq — mechanical analogs
  of their wps rules with no total consumer yet.

## 3. The two adequacy halves (TotalAdequacy.lean; audit item 2's
separation)

- **Logical half** `wpt_strongly_normalizing`: seeded footprint +
  `blockSpecsT ∗ wpt` ⟹ `Relation.StronglyNormalizing ErasedStep`
  at the launched configuration — `twp_total` consumed as-is over
  the unified relation (ghost construction mirrors
  `spike_step_adequacy`).

- **Cost half** `wpt_drive_aux` / `wpt_engine_boundU/J` — THE
  GENERIC MEASURE→DRIVE-FUEL SIMULATION: the judgment at budget k
  plus the seeded footprint yields the unconditional
  `driveU/driveJ … k … = .done v σ'` equation with the readout ψ;
  one `engine_step_matchU` application per budget unit, proved once,
  here. Exhibit totality proofs contain no engine steps ever again.

- **Fuel honesty without run-length coupling** (what keeps the
  exported equations unconditional in the loop count): the
  step-monotone size potential `pot` (value leaves 1, other leaves
  2, case at 2·esize; `Frag.pot_step_bound`: never increases along
  non-jump cone steps, resets to the registered body at jumps).
  Per-step `esize e ≤ pot e ≤ pot(entry/body) ≤ lemDefaultFuel` —
  STATIC hypotheses (`pot fibProg = 4`, `pot lrProg = 7`, by `rfl`),
  where the generic `esize ≤ +1 per step` bound would have forced
  `2·n`-coupled fuel hypotheses and destroyed fib's unconditional
  statement.

- **The state-inert cone** (`stateInert` — no Eaction/Ememop/Ecase;
  `Frag.stateInert_step`): action-free programs preserve the memory
  state step by step, so the generic bound theorem pins their final
  state — fib's exported `.done (fib n) σ₀` keeps its verbatim
  shape. Deliberately conservative (memops and loads are
  individually state-preserving but excluded; a client needing them
  extends the predicate + one lemma arm).

## 4. Clients (audit item 4)

- **fib**: `fib_certified_total` — STATEMENT VERBATIM (the
  unconditional `driveJ … (2·n+4) … = .done (fib n) σ₀`) — is now a
  corollary: `fib_body_wpt` (the partial invariant + the variant pin
  `2·(n−i)+3`; the back edge is arithmetic) → `fib_blockSpecsT` →
  `fib_wpt` → `wpt_engine_boundJ`. `fib_loop_drive` (the
  operational induction with explicit `Step.*`/`driveJ_step`
  rewrites) is RETIRED — grep confirms zero Step constructors /
  driveJ_step chains in either exhibit's proofs. NEW
  `fib_terminates` (strong normalization).

- **list-reverse (the registered residual CLOSES)**:
  `list_reverse_certified_total` — unconditional
  `driveJ … (13·|xs| + 7) … = .done (ptrVal p') σ'` with
  `ChainAt σ' p' xs.reverse`; plus `list_reverse_terminates`. THE
  BOUND IS DERIVED, not assumed: per label entry
  `lrCost r = 13·r + 6` (null test 3, guard 1, load 4, store 4,
  jump 1 + target). The old notes' ~11·|xs|+6 ESTIMATE undercounted:
  the true engine cost is 12 per iteration (the nested annot
  wrappers of the load/store footprint annotations merge in one
  extra step before the jump), and the budget algebra reserves one
  further unit (each wrapper prepays a merge; the engine spends one
  merge for two wrappers) — documented at `lrCost`. Total node-field
  rules are one-line clients of the generic subrange rules (F-04
  discipline preserved at the total stratum).

- **THE NEGATIVE TEST** (DivergeExhibit.lean): the self-jump loop
  steps to itself (`dg_self_step`), is not strongly normalizing
  (`dg_not_normalizing`), and `diverge_total_unprovable` derives
  False from ANY purported total derivation (any label context,
  postcondition, budget) via the total adequacy — unprovability in
  the strongest (semantic) form. The stuck obligation of a direct
  attempt: the jump clause's `∃ m', 1 + m' ≤ m` against a body that
  `blockSpecsT` requires at every claimed variant, including 0.
  Deleting the decrease conjunct from `wpt.pre` makes the loop
  derivable at any budget AND breaks the budget inductions of
  `wpt_sound`/`wpt_drive_aux` — the structural tripwire.

## 5. The oracle (frozen-corpus regression)

Snapshots: `docs/2026-09-01_phase2-signatures-post.txt (byte-identical to the former 2026-09-01_phase3-signatures-pre.txt, deduplicated 2026-09-02)` (= the
phase-2 post, 16051 lines) /
`docs/2026-09-01_phase3-signatures-post.txt` (16998 lines). Derived
tally (labeled as derived; the snapshots are the record): 2
declarations DELETED, 0 exported statements changed, ~102 added.

DELETED (2) — both sanctioned by the audit/mission:
- `blockSpecs_intro_variant` (F-02: zero consumers, no termination
  consequence; replaced by `blockSpecsT`, whose termination
  consequences are `wpt_sound` → `twp_total` and the drive-fuel
  simulation);
- `fib_loop_drive` (the operational side proof the audit's
  acceptance criterion retires).

UNCHANGED: every previously exported statement — including
`fib_certified_total` (verified: absent from the statement diff;
its curated axiom pin unchanged, cone exactly the trio) and the
whole partial lane. `blockSpecs_intro` re-checked identical
(diff-context artifact only).

ADDED (~102): the total judgment + rule set (Wpt.lean), the two
adequacy halves + potential + state-inert machinery
(TotalAdequacy.lean), the fib/list-reverse total lanes, the
negative exhibit, and equation-lemma internals.

## 6. Audit Phase-3 exit criteria, checked against the tree

1. **"Removing the decrease proof makes a looping example
   unprovable."** — The decrease is the jump clause's
   `⌜1 + m ≤ k⌝`, never optional; `diverge_total_unprovable` shows
   the looping example's derivation is FALSE (semantic
   unprovability), and the module header records the exact stuck
   obligation and the structural consequences of deleting the
   premise (the collapse's and the simulation's inductions are ON
   the budget).
2. **"`blockSpecs_intro_variant` is either replaced or has a
   theorem-level termination consequence."** — REPLACED:
   `blockSpecsT`/`blockSpecsT_intro` (Wpt.lean), whose
   theorem-level termination consequences are
   `wpt_strongly_normalizing` and `wpt_engine_boundU/J`.
3. **"Total example proofs contain no explicit engine Step
   constructors."** — fib and list-reverse total proofs are
   corollaries of the generic theorems; grep over both exhibits:
   zero `Step.*` constructor applications and zero `driveJ_step`
   uses remain (only retirement notes in comments).

Arc-plan Phase-3 items: 1 (TWP used, no hand-rolled fixpoint) DONE;
2 (jump-aware total judgment, mandatory decrease) DONE; 3 (collapse
to TWP + adequacy over the Phase-1 relation + the separated generic
cost theorem) DONE; 4 (fib as corollary; total list-reverse) DONE.

## 7. Registered follow-ons (honest, named)

- Total rules for create / Ecase / Ewseq: mechanical analogs of
  their wps rules; no consumer yet (manifest total-lane RED cells
  name them).
- The listrev bound's one-unit-per-iteration reservation slack
  (13 vs the engine's true 12): tightening would need the annot
  layer's budget to distinguish merge-consuming from jump-through
  wrappers; priced as not worth the rule-surface complexity now.
- `stateInert` is conservative (excludes memops/loads); extending
  it is one predicate arm + one lemma arm per construct.
- The counter loop (LoopExhibit) keeps its partial export only; a
  total counter export is a mechanical fib-pattern replay if ever
  wanted (fib supersedes it as the state-free total exhibit).

## 8. Operational findings

- The `omega` anomaly recorded in the phase-2 notes reproduced in
  budget-arithmetic side goals mentioning `deliveryCost w` (atoms
  from unreduced projections); explicit `Nat.le_trans`/
  `Nat.le_of_succ_le_succ` terms or a prior `simpa [deliveryCost]`
  reduction discharge the same goals instantly and are used at
  those sites.
- `rw` inside the Iris proof mode rewriting the whole entailment
  (phase-2 finding) was USED deliberately this phase: proofmode-
  hypothesis budget/env rewrites (`rw [hbind]`) act on the spatial
  context as intended.
- `induction … using Nat.strongRecOn generalizing …` re-introduces
  the generalized variables automatically in the `ind` case; an
  explicit `intro` afterwards silently destructures the ENTAILMENT
  (UPred applications) instead — surfaced as bizarre
  `ValidAt`-typed hypotheses; removed everywhere.
