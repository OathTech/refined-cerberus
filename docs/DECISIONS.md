# Decisions register

Append-only log of design rulings and their provenance. One entry
per ruling: date, [USER]/[AGENT] tag, the ruling, pointer to the
fuller record. CLAUDE.md is working practices ONLY and never logs
rulings ([USER 2026-08-29]: "CLAUDE.md isn't the right place for
logging design rulings" — the predecessor repo's CLAUDE.md became
an unreadable chronicle; this file is the fix). Full rationale for
the founding slate: `2026-08-29_rules-of-engagement.md`.

- **2026-08-29 [USER] Attachment layer**: instantiate the Iris
  program logic directly over Core; no Caesium-shaped intermediate.
  Preserves the ability to extend our reasoning.
- **2026-08-29 [USER] RefinedC is a target, not an end state**:
  steer hard at their design (coherent north star, reuse their
  design beats, no what-are-we-doing wars); extension beyond them
  only after parity.
- **2026-08-29 [USER] v1/reasoning-era designs are highly
  untrusted**: that route failed; nothing enters as design.
  Model-fidelity facts are leads only, re-verified against code.
- **2026-08-29 [USER] Proof quarry**: the cerberus-lean park
  branches carry substantial Lean proof text over Core — for
  concrete Core-wrangling obligations, search there before
  re-deriving; quarried material re-enters only where the
  RefinedC-targeted structure calls for it, re-verified in place.
- **2026-08-29 [USER] Frontend out of scope**: RefinedC's
  frontend/annotation layer is irrelevant to the core goal. Port
  target = program-logic lifting + type system + Lithium-style
  automation; specs/proofs authored in Lean natively.
- **2026-08-29 [USER] Semantics pin**: wait for
  `core/semantics-first` to land on the cerberus-lean mainline;
  pin the post-merge commit.
- **2026-08-29 [USER] Validation**: acceptance ladder = RefinedC's
  own examples/tutorial suite ("their proofs transfer"); the frozen
  15-program corpus is a secondary check once expressible, never a
  driver.
- **2026-08-29 [USER] Process**: arc/charter/orchestrator practices
  carry over; the convergence-era layered doctrine does NOT (each
  item re-earns its place). See rules-of-engagement §4–§6.
- **2026-08-29 [USER] Worktrees**: main is fine during arc-0 setup;
  thereafter arc branches in build-primed worktrees for parallel
  work.
- **2026-08-29 [USER] CLAUDE.md is working practices only**: design
  rulings live here, not there.
- **2026-08-29 [USER] THE NORTH STAR** (ratified verbatim from the
  metric/goal-collapse conversation): the product is a **Lean-native
  C verification framework** — RefinedC's architecture (ownership/
  refinement type system + Lithium-class goal-directed automation)
  rebuilt natively in Lean on iris-lean, attached directly to the
  cerberus-lean Core semantics, able to verify NEW C programs (specs
  and proofs authored in Lean, kernel-certified against the
  executable semantics, cost comparable to RefinedC's), extensible
  past their fragment toward the parent project's Linux-stack aim.
  Replay harnesses, transfer walls, and donor fidelity are
  MECHANISMS in service of this — each retired or demoted to a
  validation lane at parity, never reported as the product. (The
  house parallel: the OCaml differential oracle drove the semantics
  build and stayed a validation lane forever; replay is this port's
  OCaml oracle.) Binding instruments: (1) TWO LEDGERS — wall/replay
  metrics = the build ledger; the product ledger = a NATIVE
  VERIFICATION EXHIBIT at every arc close (a never-seen C program,
  in no donor corpus, verified end-to-end: Lean spec, our
  automation, trio cone); arc reports carry both, never conflated.
  (2) DISPOSITION-AT-INTRODUCTION — every scaffolding mechanism is
  born with a recorded disposition (dies-at-parity or
  demotes-to-validation-lane), decided at introduction; replay's
  disposition: demotes to a differential lane. (3) ENGINE-NOT-
  REPLAYER — the Lithium port is a free-running goal-solving
  engine; replay is a test harness AROUND it (feed their goal,
  compare outcomes), never a code path or mode INSIDE it. Carried
  into the Lane L charter as a design constraint.
- **2026-08-29 [AGENT] Arc-0 audit re-baseline**: the BI smoke
  lemma's axiom cone is empty (stronger than the trio bound); pinned
  as such at first build. Plant-test transcript in the arc-0 commit
  message (`a7ff8b0`).

## The attachment-targeting conversation (2026-08-29)

- **2026-08-29 [USER] TRUST ARCHITECTURE** (verbatim): "the
  cerberus-lean operational semantics is the ***only*** semantics
  that we trust. The relational semantics is a derived layer on top
  of it"; "we are going to build on top of the actual cerberus-lean
  operational semantics… This will be legitimately built on
  cerberus-lean, or it is off target"; "the intended end state of
  all of this is an adequacy result that can be stated *exclusively*
  over the cerberus-lean semantics… 'mirroring' without proof is
  valueless." Named failure mode: a pile of RefinedC machinery not
  coupled to cerberus-lean has no value regardless of donor
  fidelity. Consequences: any layer/engine disagreement is by
  definition a defect in the derived layer; no ported layer counts
  as capability until its downward theorem exists (adequacy spine
  load-bearing from rung one, never retrofitted); transfer-ladder
  rows count only when the proof discharges through the spine into
  an engine-only statement. Baked into CLAUDE.md header.
- **2026-08-29 [USER] Calls = substitution at the attachment
  layer**: substitution is reconstructed at the attachment layer and
  the environment disappears — keeps typed_function/wp_call literal.
  (Independently the failed prototype's final design conversation
  reached the same conclusion — corroboration, not justification.)
- **2026-08-29 [USER] Prototype relational-semantics work upgraded
  to DESIGN DONOR** for the derived-layer question specifically ("we
  may already have a design donor here") — evaluated on merits
  against the criterion sane / legitimate / scales-to-RefinedC;
  the untrusted-as-design default still governs everything else.
- **2026-08-29 [AGENT] Targeting calls** (each derived from ratified
  rulings; full statements in the port map §4 and the conversation
  record): (1) fragment referent = sequentialised Core, Eunseq out
  of fragment 1 [from "their sequentialized fragment first"];
  (2) atomics stubbed with temporal ledger row [sequential-first;
  ladder is gauge not goal]; (3) annotation payloads re-home to
  Lean-side spec/proof-script channels, annotation-fired rules
  become explicitly-invoked steps — a divergence CLASS whose forcing
  fact is the ratified frontend-out-of-scope ruling; (4) provenance
  referent = whatever the semantics pin runs; (5) allocation-failure
  stance follows the pinned engine's actual create behavior;
  (6) alignment recorded against the matching Caesium config;
  (7) wp/wp_det relational split ports unchanged; (8) adequacy shape
  mirrors theirs + an executable-layer corollary; (9) layouts/
  op_types, mem_cast dissolve-or-port, liveness ghosts, RA bundle,
  W-analog extent = fact-finding against the semantics, each ending
  in a ledger row. Pre-registered fallback on calls: if the
  substitution correspondence resists, an env-aware call rule as a
  ledgered divergence — no heroic grinding past its value.
- **2026-08-29 [AGENT] Statement-layer derisk plan** ([USER]
  prompted: "danger of doing violence to our goals… derisk the
  design"): empirical shape-correspondence study first (both
  pipelines executable, C as join key), then two candidate designs
  argued against the measured table under hostile review, then a
  vertical spike with pre-registered kill criteria. Evidence:
  `docs/2026-08-30_caesium-core-shape-study.md` (finding: sharp
  statement-position grammar; control flow near-bijective via
  save/run; shared Ail ancestry; bind layer dissolves by grammar;
  divergences: pattern-shaped correspondence with inline UB
  templates, per-iteration locals lifetime).
- **2026-08-30 [AGENT] Relational-layer candidates memo delivered**
  (`docs/2026-08-30_relational-semantics-candidates.md`, written
  under the trust-architecture rulings): recommends the HYBRID —
  the prototype's proved per-step spine (two-sided runner
  characterization + engine-only adequacy path) as the trunk,
  syntactic per-construct characterization lemmas grown on it as
  the WP layer; pre-registered falsification probe (two exemplar
  lemmas at ∀-configuration). NOT yet ratified — hostile review
  pending. New facts of record: the Lean pipeline never calls
  Core_sequentialise (verified: zero callers; test_exec.sh notes
  it) → realizing the sequentialised fragment needs Lean-side
  wiring + a validation lane, [USER] decision pending (cross-repo);
  the trimmed relsemcore spine (runND_sound) survives
  core/semantics-first; finalize runs a second evaluator
  (Driver.hack) → result postconditions need a characterization
  lemma family.
