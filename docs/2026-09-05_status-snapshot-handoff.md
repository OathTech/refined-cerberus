# Status snapshot for handoff — 2026-09-05

Written by the orchestrator [AGENT] at the operator's request ("a 'status
snapshot' doc … What are we doing, and what's next?"). Point-in-time; the
authoritative state is the tree plus `docs/DECISIONS.md` (append-only,
later governs) and `docs/KNOWN-OPEN-ITEMS.md` (what is known, disclosed
and owned). Read `CLAUDE.md` first for the working practices; they are
not repeated here.

## 1. What this repo is doing

The product is **cerberus-heaplang** (`cerberus-heaplang/`): a classical
Reynolds/O'Hearn separation logic over Cerberus Core, in Lean 4 on
iris-lean, whose every export is a theorem about the GENUINE cerberus-lean
semantics at a pinned commit (`scripts/semantics-pin.env`, currently
`f95ef8d9c`). Its normative statement is `cerberus-heaplang/ARCHITECTURE.md`
(passed a fresh full review at A− on 2026-09-04; a further fresh review is
ratified for after E5–E7). Two rulings frame the demo's purpose:
- [USER 2026-09-04] "The demo should be the best possible version of
  Reynolds/O'Hearn … it shakes out many of the theory difficulties. Fancy
  logic features aren't needed" — the LOGIC axis is closed (masks, function-
  pointer logic → the RefinedC arc).
- [USER 2026-09-04] "our aim here is to build a logic over Core emitted as
  an output from C code. Authored-core is just a confection" — the DIALECT
  axis is open: **arc E**, restating the demo's covered features in the
  Core the elaborator actually emits, one construct per slice.

The longer-term direction is a RefinedC-family verifier for agent-driven
verification at scale over the same semantics (Lane C design note
`docs/2026-09-04_refinedc-layer-design-2.md`, nine open questions for the
operator; its copy seeds from the demo's version-one tag).

## 2. Where things are (main `8eeaf92`)

- **Merged and audited**: the calls arc C1–C4 (procedure specifications,
  the call rule, recursion via one Löb), the fuel-lane restatement F1 (no
  provisional lane; the partial lane over the genuine driver), the
  external-audit response AR5 (variant-level rule-use manifest, fail-closed
  instruments, the public readout boundary), the hygiene/coverage slices
  H1, and **arc E slices E1–E4**: annotations with the live location,
  `bound`, constructor constants, loaded values and patterns, the C `int`
  arithmetic with the demo's first integer rules, std.core unfolding on a
  transcribed three-function standard-library file, and `unseq`.
- **The t1 milestone** (E4): `t1_certified_production` — the first corpus
  program (`docs/corpus-e0/t1.c`: `int x = 3; int y = x + 1; return y;`),
  transcribed VERBATIM from the elaborator's Core and checked against it by
  the gate's corpus speedbump, certified end to end through the genuine
  pipeline; the oracle's own run agrees (`Specified(4)`, exit 4). Ten closed
  shipped-driver statements in total; 652 pinned exports, every one with
  axiom set exactly the trio.
- **Every merge in this period** was preceded by a fresh Fable-class range
  audit (all A−, no trust or correctness finding) and an orchestrator FULL
  gate recorded verbatim in DECISIONS; every fix and every erratum against
  our own claims is logged.

## 3. What is parked, and how to resume it

**Branch `dialect-e5` at `f433820` (worktree `worktrees/dialect-e1`) — E5,
the negative-action protocol.** A committed PARK record: the slice has
ENDED; working past it needs the operator's approval.
- Slice 1 LANDED and gated (b36ebf2): the assignment protocol mirrored and
  classified, the run-state supplies live as writers on the control state,
  a soundness catch on the `bound` rules fixed before landing.
- Slice 2 HALF-DONE and gated (09a89c7): the supply floor in both
  judgments, the rule faces incl. the assignment protocol as one derived
  rule. NOT done: pins for the new theorems, five manifest rows, coverage
  witnesses, the corpus transcriptions t5/t6/t4 and their certifications,
  `seq_rmw`/`PtrValidForDeref`/`Elet`. Estimate to acceptance: 4–8 h.
- Resume plan: `cerberus-heaplang/docs/2026-09-05_e5-notes.md` §S2.9;
  debts: KNOWN-OPEN-ITEMS C19. One design point awaits the operator's veto
  (§S2.5: the seeded profiles normalise the supplies). FIRST action after
  completing slice 2: the range audit 8eeaf92..HEAD; then the merge ask.

**Branch `repin-scout2` at `07ceb44` (worktree primed at cerberus-lean
`de2fbf1`)** — the measurement for the LemLib-representation re-pin;
record `docs/2026-09-03_repin-scout-2.md` (on main).

## 4. What's next, in order

1. Finish E5 (above) → range audit → merge ask.
2. E6: the C call protocol (`Eccall` is a SCHEDULER-round path, so adequacy
   lifts to a scheduler induction and the outer fuel starts doing work);
   own stop-and-report if the induction resists. Then seven corpus programs
   certify.
3. E7: the outcome-list closed form (factorial forks under `unseq`).
4. The demo's VERSION-ONE tag; the fresh full ARCHITECTURE review (new
   reviewer; the cite checker `cerberus-heaplang/scripts/cite_check.sh`
   first).
5. The shared Iris↔Cerberus coupling library extraction (Lane C item 6,
   recommended YES; the demo becomes its regression suite), then the
   RefinedC layer's first slices.

Blocked on the semantics side (operator relays; nothing to do here until
they land): the LemLib re-pin (next cerberus-lean pin), the fuel-parametric
semantics (F2 restatement, `docs/2026-09-04_fuel-restatement-design.md`),
the concurrency S1 selector (one-token slice), the two lem-lean requests.

## 5. Decisions waiting on the operator

- The Lane C note's nine questions (`docs/2026-09-04_refinedc-layer-design-2.md` §7).
- E5 §S2.5 (supplies normalisation in the seeded profiles): ratify or veto.
- Whether the cite checker joins the gate as a drift speedbump.

## 6. Practices a successor must keep (pointers, not restatements)

`CLAUDE.md` (all of it); every merge needs its own explicit yes at the
point of merge; every merge range gets a fresh-reviewer audit; audit
findings are claims — verify by measurement before remedy; gate tails
recorded verbatim (selection rule in DECISIONS' AR5-range-audit entry);
no Lean build uncapped (`scripts/capped`); one heavy build at a time,
40G each when two run; a committed park record ends a slice.
