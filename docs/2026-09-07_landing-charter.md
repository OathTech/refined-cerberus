# Landing charter — the agent-built branches, pulled apart and landed incrementally

Status: DRAFT for the operator's ratification ([USER 2026-09-07]: "put
together a plan to land all this … chartered work … somewhat incremental —
you'll build a set of new branches which pull out the good bits and land.
I'm happy to sequence these however seems convenient"). Author: the
orchestrator [AGENT]. Inputs: `docs/2026-09-07_branch-landability-assessment.md`
and the two auditors' reports it cites. Every slice below is one change,
on a NEW branch off the then-current main, with a fresh-reviewer range
audit and its own merge ask; every merge needs the operator's explicit
yes at the point of merge. Nothing here authorises a merge.

## 0. Ground rules for the landings

- Source branches (`dialect-e5` at cb46e4c, `demo-repin` = `parked/demo-
  expansion-2026-09-07` at a41292d) are READ-ONLY records; we cherry-pick
  or re-cut from them, never merge them.
- Each landing commits the SOURCE branch's Lean content it takes with the
  original commit messages preserved where cherry-picked, plus our own fix
  commits; docs from the source are taken only where they are shop-window
  truth (README/ARCHITECTURE/CLAIMS/manifest); the source's DECISIONS
  entries are NOT taken — each landing writes ONE orchestrator entry that
  points at the source branch as the record; the source's build-log docs,
  progress records, axiom dumps (`docs/evidence/*`) and the failing WIP
  patch stay on the parked branch.
- Each landing: FULL gate (orchestrator, verbatim tail), signature census
  (pre = the previous landing's post), manifest/CLAIMS/boundary/skeleton
  instruments green, `cite_check.sh` last on any docs touch, the range
  audit, the merge ask. Sizes are worker-time at the measured velocity of
  E1–E4 (≈ ½ day per M slice incl. audit).

## 1. Rulings the operator owes before the corresponding slice (my recommendation in brackets)

- **R1 — the pin.** Ratify cerberus-lean `89f7e688530c6910884518811d645e4e892e4507`
  as the demo's pin (KOI A6 said "waits for the next pin"; 89f7e68 IS a
  next pin: mainline head with the fuel-parameter arc C4 merged, 37 seams
  byte-identical, our gate green). [Ratify; state that further pins follow
  the same per-slice pattern.]
- **R2 — fragment vs fuel.** The re-pin branch moved the potential
  premises INTO a fuel-relative `Frag [LemFuel]` (+ a `2 ≤ LemFuel.fuel`
  floor); our F2 design kept `Frag` syntactic and put `pot e ≤ LemFuel.fuel`
  as a hypothesis on adequacy theorems. [Restore the syntactic fragment
  with the hypothesis form in L2 — the manifest/classification and the
  RefinedC layer want a fuel-free fragment; cost M inside L2. Alternative:
  accept the fuel-relative fragment with a ruling and a disclosure.]
- **R3 — E5 §S2.5.** The seeded profiles normalise the run state's
  supplies to `⟨0,0⟩` instead of a premise on ~20 exports. [Accept;
  disclosed; the alternative is noise.]
- **R4 — the t1 referent.** The landed statement is over the pipeline's
  WHOLE emitted file, machine-quoted from the pinned frontend and checked by
  an executable round-trip (option (b) mechanised); option (a), the
  elaborator inside the statement, remains the named target. [Ratify the
  wording; KOI A7 restored accordingly.]
- **R5 — E6/E7.** Park the scheduler work as a record; E6 proper is
  re-cut later as its own slice per the design (calls are in the stop-state:
  "works on real emitted core"). [Park now; E6 proper after L4; the v1 tag
  waits for E6 — or, if the operator prefers an earlier tag, v1a after L4
  as "emitted Core, call-free programs".]
- **R6 — the park override.** The other agent worked past the E5 park
  record on the operator's authority. [Record the operator's words
  verbatim in L1's DECISIONS entry; no other action.]
- **R7 — housekeeping (optional).** Delete the eighteen fully-merged
  branches; keep `lane-b-seed`, the parked branch, `repin-scout2` until L2
  lands (then delete both scouts); `charter-aims-amendment` to an archive
  tag or delete.

## 2. The slices, in landing order

### L0 — the assessment (docs-only; the pending ask on 30010f4)
This assessment, the two audit reports, this charter, the DECISIONS pointer.

### L1 — E5 complete (from `dialect-e5` f433820..cb46e4c) — size S–M
New branch `land/e5-complete` off main; rebase cb46e4c's 14 commits onto
main (linear; docs-only conflicts expected). Fix commits: (a) PROVENANCE —
the charter's "already authorized" for the actual-file closure and the
re-pin → "[AGENT]-proposed, adopted through the operator's goal command";
the `[USER, paraphrase]` permission → verbatim or an [AGENT] reading; the
park override recorded verbatim (R6); (b) the census snapshot at the
candidate head (auditor's own: slice-1 post → head 372/2/18; `load_atomic`
the only range-owned text change); (c) record truth — KOI state line, the
600 supply floor "sufficient not necessary" (measured at `sup = 0` too),
B6 slack rows (t5 21, t6 13, t4 324), ARCHITECTURE §2.5 cites; (d) R3
recorded. Range audit 8eeaf92..head (the full E5 audit the park owed:
slice 1 + slice 2 + the completion). Acceptance: t5/t6/t4 certified
(already), oracle cross-checks re-run at the candidate, gate green.
Landed state: E5 complete at the OLD pin.

### L2 — the re-pin to 89f7e68 (from `demo-repin` G1: ce4d7de) — size M
New branch `land/repin-89f7e68` off L1's main. Cherry-pick the CODE commit
ce4d7de (+ any G1 code prerequisite; the 13 red-frontier docs commits are
NOT taken — their content is summarised in ONE re-pin record we write),
then: (a) R2 — restore the syntactic `Frag` with `pot e ≤ LemFuel.fuel` as
hypotheses (per `docs/2026-09-04_fuel-restatement-design.md` §3) unless the
operator rules otherwise; (b) shipped-constant corollaries at
`⟨100000000⟩` for the ten closed statements (the design's §3; the branch
has none); (c) THE EXHAUSTION PARAGRAPH — measure the eight reachable
ambient opaque-exhaustion rows at this pin (their C3/C4 manifests), state
which of (A)/(B)/(C)/(D) each is, and carry the honest hypothesis on the
partial closed forms if any (D) remains (our fuel review §2; KOI A2/A5);
(d) the UNPLANNED third class — the allocator/memory-contract changes at
the pin (negative-size alloc, retained bytes, requested address) — its own
census section and manifest rows; (e) the census over the whole surface
(pre = L1's post on the OLD pin: ~860/35/1599 — classify binder-only vs
real); (f) `scripts/semantics-pin.env`, `lake-manifest.json` (LemLib
f6542f8), `setup-cerberus-dep.sh --check` in the record; (g) KOI A1/A2/A4/
A6 updated (A2 closes; A1 partially — the constants are gone; A4 closes —
upstream `LemLibPmapLaws`). Range audit. Acceptance: every export
`[LemFuel]`, zero fuel numerals outside the shipped corollaries (gate grep
extended — plant it), the ten closed statements + t1/t4/t5/t6 certified at
the new pin, oracle cross-checks with the NEW pin's binary (build it: the
primary's binary is the mainline build).

### L3 — the actual emitted file in the t1 statement (from `demo-repin` G2: 3aac95d..5bfe992) — size M
New branch `land/actual-file` off L2's main. Cherry-pick the G2 commits
(code + `scripts/inspect-emitted-file.sh` + the machine-quoted data the
statement uses; NOT the `a7-*` progress docs — one record); then: (a) the
round-trip check as a gate SPEEDBUMP (9.6 s measured; plant it); (b) an
independent `BEq` equality beside `toExpr`; (c) name and document the
`mkAuxLemma` kernel-certificate device in ARCHITECTURE §3 (what it is, why
it is kernel-checked, what it is not); (d) R4 wording on README/ARCHITECTURE/
KOI A7; (e) decide the retained wrapper `CorpusT1Exhibit` (keep as the
transcribed form beside the actual-file form, both pinned, or retire).
Range audit. Acceptance: `t1` certified over the pipeline's whole file at
the new pin; the check red on a perturbed data term.

### L4 — `seq_rmw` re-cut (from `demo-repin` G4: 567c578..19292c0, without G3) — size M
New branch `land/seq-rmw` off L3's main. RE-CUT (not cherry-pick: G4 sits
on G3's `Step` changes): the engine arms (`step_ctx` SeqRMW arm,
`Driver.lean:312` `SeqRMWRequest2`), the mirror rule, the public rules at
cost 8, the `negFree → boundFree` premise change WITH its census; drop the
PROVISIONAL label only if the rules are the final form. Range audit.
Acceptance: an emitted `i++` certified (a corpus program using it, if the
call-free set has one; else a synthetic transcribed from the elaborator).

### L5 — E6 proper (after R5) — size L, own stop-and-report
Per the design (`docs/2026-09-04_emitted-core-dialect-design.md` §B6/§C E6)
and the Lane C note §3: the C call protocol, `Eccall` as a scheduler round,
the `driver2` induction, outcome-list closed forms. The parked G3 work is
the REFERENCE (its statements over the shipped engine are sound; its 32
device-carrying pins, the unclosed candidate fragment and the E7-first
ordering are not taken). Acceptance: t2/t3/t10 certified with oracle
cross-checks. Then E7 if still needed (factorial's fork).

### L6 — v1 tag + the fresh ARCHITECTURE review + the coupling-library extraction
Per the standing rulings; the review before the tag; `cite_check.sh`
first.

## 3. Housekeeping with each landing
- The parked branch keeps everything not taken (build-log DECISIONS,
  evidence dumps, progress records, the WIP patch); its name says so.
- The source branches' DECISIONS are never merged; ours point at them.
- Worktrees: one per active landing; audit copies removed after their
  report is committed.

## 4. Estimate (measured velocity, incl. audits)
L0 now; L1 ≈ ½ day; L2 ≈ 1 day; L3 ≈ ½–1 day; L4 ≈ ½–1 day; L5 ≈ 2–3 days;
L6 ≈ 1 day. About a week to v1 with E6 in; about three days to L4.

## 5. Provenance
[USER 2026-09-07]: the request. [AGENT]: the plan, the recommendations in
brackets, the sizes. Nothing built, merged or deleted.
