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
- **2026-08-29 [AGENT] Arc-0 audit re-baseline**: the BI smoke
  lemma's axiom cone is empty (stronger than the trio bound); pinned
  as such at first build. Plant-test transcript in the arc-0 commit
  message (`a7ff8b0`).
