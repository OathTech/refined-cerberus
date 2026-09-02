# Resume note — the allocation arc at the P3 quiescent point

[USER 2026-09-02]: paused here for the restart into persistent
sessions (zellij) + the operator-side items below. State when paused:
branch `heaplang-alloc-arc`, P0–P3 CLOSED (last commit `a8f61fa`,
the P3 phase-exit closure, FULL-gate claim point), tree clean.
Orchestrator's independent full-gate verification result: see the
"Verification" line appended at the bottom of this note.

## Orchestrator's independent gate verification of the P3 close (a8f61fa)
Run 2026-09-02, `./scripts/test_unit.sh` (FULL tier), log
/tmp/claude-1000/p3-verify.log, verbatim tail:
```
ok: statement census regenerated, no drift
ALL GATES GREEN
GATE-EXIT=0
```
Gates 1-5 all `ok:` (1 grep ban; 2 root build; 3 demo build; 4h/4s
manifest; 5 census). The worker's claimed green is thereby
independently confirmed; the P3 close stands. This is the quiescent
point for the zellij restart.

## What P0–P3 delivered (one line each; details in the phase notes)
- P0: claims corrected before logic; create downgraded; CORE-DRIVE-ROW;
  R-01..R-11 closure table with the audit's acceptance tests.
- P1: allocation model (AllocReq/PlanFits/opaque allocCap), launch
  coherence + the one `launchResources` helper, cursor-free public
  `wps_create`/`wpt_create` (derived bound 2), launcher smoke.
- P2: whole-program logic proofs; 85 operational declarations deleted;
  R-01 + R-02 CLOSED by plant transcripts; the bind-your-pointer design
  record (∀-quantified rule rejects hard-coded allocator outputs).
- P3: dependency-certified manifest (staged cone checks, execution
  witness, layer cut over 608 exhibit declarations; vacuous
  constructor-cone test measured and rejected), four plants detected;
  `CerberusRound` exhaustive classification (two-sided step arm;
  refusal arm two-sided for store/load/create/case, one-sided with
  reasons for 14 rows); R-04 CLOSED, R-03 CLOSED at classification
  level; `--fast` tier + HARD/SPEEDBUMP classification in test_unit.sh.

## P3.5 — CUT THE CRUFT (first restart slice; [USER 2026-09-02], DECISIONS)
Brief: `docs/AUDIT-BRIEF.md`. "Delete the junk here and elsewhere in
the project"; gates "sized proportionate to the demo-level work
we're doing and consistent with moving fast"; "the actual logic
itself must be pristine". Supersedes the audit's P3 gate-hardening
prescription (R-04 restated honestly in the closure table).

Measured inventory (line counts at pause) and disposition:
- `cerberus-heaplang/scripts/capability_manifest.lean` 1,507 → ≲ 250:
  a claim-point SPEEDBUMP REPORT. Keep: rows derived from `Frag`'s
  constructors (an unmapped constructor shows up) + the one check that
  caught real overclaims (the named rule is in some exhibit's proof
  cone). The hand-maintained multi-cell row table (~340 lines) becomes
  ONE LINE per construct: constructor → rule theorem name ([USER
  2026-09-02]: "No giant enumerative tables unless we are actually
  legitimately worried about trust"). CUT: layer cut over 608 exhibit
  declarations + path reporting, production-requirement staging,
  execution witness, accumulating-failure monad, multi-line machine
  output, README MANIFEST-SCOPE token tie. Human table only.
- `scripts/statement_census.lean` 114 + `docs/STATEMENT_CENSUS.txt` +
  gate 5: DELETE (redundant with committed signature snapshots).
- `scripts/signature_snapshot.lean` 46: keep as an on-demand
  instrument; STOP producing per-phase pre/post pairs (22 committed
  snapshot files stay as history; no new ones unless a phase changes
  a public statement surface).
- `scripts/test_unit.sh` 285 → ~80: gates 1-3 + the speedbump report;
  `--fast` = gates 1-3; header says plainly that nothing here is
  designed to survive adversarial attack. Drop the HARD/SPEEDBUMP
  table and per-gate timing prose.
- `CerberusHeapLang/Audit.lean` 738: keep the axiom-cone sweep over
  the public exports + the banned-axiom sweep; cut the runEffectful
  boundary/origin discipline (goes with the re-pin); collapse the
  curated exact-pin prose to the export list. Target ≲ 250.
- Plants retained as permanent gates: remove; transcripts stay in
  the phase notes as history.
- `CerberusHeapLang/StmtProbe/` (Demo/Toy/Wps): measured at pause —
  imported only by the lib root and Audit.lean, i.e. the S0 probe left
  in the tree with no consumer. DELETE (the s0-adjudication note holds
  its findings); drop its pins from Audit.lean.
- CLAUDE.md: replace "Gates minimal … plant-tested in both directions"
  with the speedbump rule; add the AUDIT-BRIEF pointer; retire the
  uncapped interim ruling once cgroup-direct `capped` is adopted.
- Arc records (plans/notes) are NOT junk: they are the record. Leave.
Verification for P3.5: gates 1-3 green; the report runs in ≲ 30 s
quiet; `wc -l` before/after table in the P3.5 note.

## Slice 1 of the restart — THE RETIREMENT RE-PIN (P7 moved ahead of P4)
[USER 2026-09-02]: runEffectful is retired on the cerberus-lean
mainline; rebase now so P5/P6 (layering, the docs rewrite) happen once
on a trio-clean tree.
1. Pin bump: scripts/semantics-pin.env → `ddcfc919972a31bc43a0454e6b2e76a19e6c4594`
   (mainline head at pause; 38+ commits past 58ec50779; code-bearing:
   14 files on primed paths — native fresh_int.c/tags.c deleted,
   generated Core_run_aux/Driver entry constructors changed). Remove
   .cerberus-ws, re-run setup — the content guard WILL trip (real
   semantics change) → deliberate re-pin, record it.
2. Entry shape landed as supply-PARAMETERIZED (the consumer review's
   shape (b)): `initial_driver_state (supply : Nat) file fs :
   driver_state × Nat` + `initial_driver_state_given` /
   `initial_core_run_state_given`. Production statements gain a
   ∀-supply quantifier (free: the fragment never reads the seam) —
   the sanctioned statement class for this slice; itemize per
   theorem under the frozen-corpus oracle.
3. Re-certify the entry/driver path: Soundness/DriverCollapse/
   ProdEntry/ProdLoop* unfold the changed constructors; the 14-file
   `git diff 58ec50779 ddcfc919972a31bc43a0454e6b2e76a19e6c4594 -- lean_frontend/generated` IS the
   change manifest (the A3 ask, answered by git). Also check
   `_root_.drive`'s signature for supply threading.
4. Delete the boundary: Audit.lean's module-scoped allowance + the
   origin-discipline machinery become vestigial → remove; every pin
   re-baselines to the classical trio; the take-on-faith README
   subsection loses item 1 (record the retirement, keep item 2);
   R-11/P7 CLOSED.
5. Adopt the mainline's `scripts/capped` (cgroup-direct mode, no
   systemd-run dependency — 22 cgroup references in the
   upstream script): copy verbatim, verify in-sandbox that it caps
   (not falls back), then RETIRE the "uncapped in-sandbox" interim
   ruling in CLAUDE.md (DECISIONS entry with the evidence).
6. CLAUDE.md working-practices additions (drop-in text below).

## CLAUDE.md drop-in text (Trust rules / Process sections)
- **Two-tier gating** (ACL2Lean model, adopted [USER 2026-09-01]):
  the FULL gate (`scripts/test_unit.sh`) is REQUIRED at claim points —
  phase/arc exits, merge candidates, re-pins, any commit claiming
  green — recorded in the commit. Intermediate commits may use
  `scripts/test_unit.sh --fast` and MUST say `fast-gate` in the
  message (never the full-gate marker), so tiers cannot masquerade.
  Batch within a round; one full gate at the round's end is the
  honest claim point. The orchestrator re-verifies with the FULL
  gate at boundaries regardless.
- **Speedbumps, not adversarial gates** ([USER 2026-09-02]): the
  trust base is the build + the in-build axiom sweep + the banned-
  methods grep — nothing else is a fail-closed gate. Every other
  check is a SPEEDBUMP: a claim-point report that catches honest
  drift, never designed to survive adversarial attack, never a
  fast-tier blocker. Over-elaborate gating is cut, not classified.
  New checks are allowed when high bang-for-buck (cheap, catches a
  real class of mistake); no giant enumerative tables unless a trust
  property is legitimately at risk ([USER 2026-09-02]).
- **Gate cruft**: measure a gate's cost when adding checks; prefer
  single-pass/memoized computation; a gate whose runtime grows past
  its trust value is a defect.

## Then: P4 → P5 → P6 → the dependency-tracing re-audit (briefed with docs/AUDIT-BRIEF.md) → check-in
- P4 (raw-API closure — R-05 wps/wpt label framing; R-06 real view/
  fraction clients or drop the claims; R-08 IsXFrame → SymFrame;
  R-09 SemTriple over MachineCtx or honest renaming; P4.1 metadata
  split incl. absorbing the bounds conjunct into persistent allocMeta).
- P5 (layering + API.lean + import gate + the public-API-only
  readiness smoke test; StmtProbe out of the main import graph;
  example constants out of Rules/Wps; the sem_triple_prod hpre
  retirement candidate).
- P6 (the authoritative docs rewrite, ONCE, on the trio-clean tree).
- Close: the audit's final acceptance checklist + a fresh
  DEPENDENCY-TRACING re-audit (must trace proof cones, not names).

## Housekeeping
- Gate-4 cost: ≈130 s quiet / 340–416 s contended; the fixed ≈88 s is
  Lean INTERPRETING the generator script (import ≈2 s) — compiling the
  generator as a module is the registered cheap win (→ ≈40 s).
- The 39-hour orphan `lean CerberusHeapLang/Soundness.lean` (pid
  3818822, reparented to systemd, cwd deleted, from the S1b credit
  crash) was killed by the operator 2026-09-02; no other long-runners.
- Box contention from other agents inflated all gate times during P3.
