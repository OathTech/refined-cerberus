# Naive-reader review: cerberus-heaplang (2026-08-31)

Reviewer persona: a PL researcher fluent in Reynolds/O'Hearn
separation logic, aware of Iris at the survey level (never used it
seriously), able to read Lean. Zero prior knowledge of Cerberus,
Core, lem, cerberus-lean, or this project. Instructions followed:
start at `cerberus-heaplang/README.md`, read only what the
documents point to, in link order; run the documented commands.
Session budget ~90 minutes of honest reading; all wall-clock
observations below are real.

Files read, in order: `cerberus-heaplang/README.md` →
`cerberus-heaplang/docs/WALKTHROUGH.md` →
`CerberusHeapLang/ListRevExhibit.lean` (statement region) →
`CerberusHeapLang/FibExhibit.lean` (statement region) →
`CerberusHeapLang/Adequacy.lean` (`driveJ`) →
`CerberusHeapLang/Soundness.lean` (`dischargeStep`) →
`CerberusHeapLang/Audit.lean` (header) — plus, on explicit
front-doc pointers only: `../scripts/semantics-pin.env` (README
sends me), the engine's generated `Driver.lean:273` (the README
divergence table cites it), and `LemLib.lean:54` (the Audit header
cites it). Every external send is logged in the stumble log.

---

## 1. The timed cold read

**~3 min — end of the README's first screen (title + first two
paragraphs).** I know: Cerberus is an executable C semantics; it
compiles C to a typed functional IL called Core; the engine here is
a Lean 4 port of that, validated differentially against the OCaml
original; this package builds a small Iris logic over a fragment of
Core and "certifies every rule against the engine." I can answer
(a) in outline and half of (b). The first sentence uses
"cerberus-lean" and "HeapLang-analog" before defining either, but
both are defined within the same paragraph / the next one — mild
turbulence only. "Provenance" gets an inline gloss on first use:
good.

**~8 min — after the exhibit table.** The table is the best and the
hardest part of the first screen. It names ten theorems with claims
I can parse as a separation logician (small axioms, THE FRAME, loop
invariant, list reversal). But three column vocabularies — "Lane"
(drive / driveJ / production), "Axiom cone", "trio" — are used
*before* they are defined (lanes: the paragraph after the table;
trio: the trust-story section). I read the table, read on, and came
back. On the second pass the table is excellent.

**~12 min — after the lanes paragraph + trust story.** Now I can
answer (a) fully, (b) fully, and (c) in outline. Checkpoint answers
at this point: the theorems are statements about the engine's own
step-function loop (drive lane) or the shipped pipeline (production
lane); the trust base is the Lean kernel + the classical trio + one
declared axiom in two modules + the semantics port itself, with the
package's own step relation "interior" (a wrong mirror can only
lose theorems, not create false ones — I flagged this as the key
claim to test against the walkthrough).

**~20 min — after "Scope of the claims" + the divergence register +
"How to verify me".** I can answer (d): build, read the audit tail,
run `#print axioms` on the ten pinned theorems, run the census
script. The scope section is dense but honest to a fault — every
qualifier I would have hunted for (fuel hypotheses, seeded-state
hypotheses, drive-vs-production asymmetry, fragment enumeration,
no `wp_create`) is stated on the claim's face. The divergence
register is written partly in internal shorthand (D26, R2, D14 —
labels into dated notes I was told not to read), but each row's
*content* is understandable without them.

**~50 min — after the walkthrough (read fully).** This is the
document that makes the package reviewable. §2 gives me a Core
program I can actually read; §3.1 shows me a small axiom I
recognize (it IS the small store axiom, with the UB-exclusion
reading spelled out); §3.2 gives the exported `SemTriple` with the
∀-frame quantifier structure — as a separation logician I accept
this as the frame property stated semantically; §4's three-tier
trust story is the clearest statement of "what you must trust" I
have seen in a mechanized-logic README; §5's per-identifier reading
tables with a mechanical census are, frankly, above the standard of
the field. After §5 I could answer (c) precisely, including where
the residual trust sits (tier 3, the spec idiom).

**~50–75 min — the claim check (§3 below): source reading + running
every documented command.** All commands completed in ≈1 second
each on this checkout (warm build cache); the build replayed from
cache in 0.4 s with the documented tail verbatim. A stranger on a
cold cache would see something much longer and the docs nowhere say
how long to expect — noted as a finding. The walkthrough's "five
minutes" claim held for me, with the caveat that I inherited a
primed workspace.

### The acceptance answers, in my own words (my comprehension test)

**(a) WHAT is proved?** A small Iris-based separation logic —
points-to over allocation-sized byte cells, store/load small
axioms, frame, sequencing, consequence, and label-context loop
rules — is built over a small fragment of Core (store/load/create,
one pointer-equality memop, sequencing, if, save/run jumps, a few
pure forms; single-threaded; no allocation rule in the logic), and
every exhibit proved in it is exported down to a theorem whose
statement mentions only the engine's execution: for the loop
exhibits, "iterating the engine's own step function plus the
driver's request discharge, from any memory carrying the seeded
footprint, never reaches undefined behavior, never wedges, and any
delivered value satisfies the postcondition" — for list reversal,
the delivered value is a pointer whose chain in the final engine
memory spells the reversed list; for fib there is additionally a
total, hypothesis-free equation `driveJ … (2n+4) … = .done (fib n)`;
for one straight-line program the theorem is an equation about the
shipped production pipeline itself.

**(b) Over WHAT semantics, and why trust it?** Core is the typed
functional intermediate language of Cerberus, an executable C
semantics from Cambridge (Memarian, Sewell, et al.) with a
byte-level, provenance-aware memory object model. The engine in the
theorems is a Lean 4 port of that semantics — the actual generated
interpreter code, not a re-formalization — pinned by commit, and
claimed to be differentially validated against the original OCaml
implementation (same test programs, behaviors compared). Important
honesty note I verified in the docs: the exhibit programs are
written directly in Core, not compiled from C source — "real C
semantics" means the real interpreter and memory model of a C
semantics, not that any exhibit starts from C syntax. And the
differential-validation claim itself is *imported*: it belongs to
the semantics project and is not inspectable from this package
(see finding MAJOR-2).

**(c) WHY believe the theorems mean what they claim (the trust
base)?** Restating the three tiers as I understood them: (1) every
theorem is Lean-kernel-checked, and an in-build audit asserts every
theorem's transitive axiom cone is exactly `propext`,
`Classical.choice`, `Quot.sound`, except two production-entry
modules that add one declared axiom `runEffectful` (which I dug up:
`axiom runEffectful {α : Type} : (Unit → BaseIO α) → α`, a
world-erasure seam used by the shipped initial state's symbol
counter; the docs argue it enters through the statement's
definition cone only and the fragment never reads the affected
field). (2) The remaining hypotheses are on the statements' faces —
fuel budgets, seeded footprints, typing side conditions — never
absorbed. (3) What is left to *read* rather than check is the
"spec idiom": `drive`/`driveJ` (a 10-line projection of the
engine's driver loop), `dischargeStep` (the driver's request
discharge re-stated function-by-function with file:line citations
into the generated engine code), and the footprint/readout
predicates (`SeedChain`, `ChainAt`, `Sat`/`Coh`). If those said
something other than claimed, theorems could be true but
uninteresting; the guards are that they are tiny and printed, that
concrete demos (`list_reverse_demo`, `fib_certified_total`,
`exhibitA_prod`) pin them to executable reality and rule out
vacuity, and that the hand-written mirror step relation and all of
Iris sit strictly inside proofs — so a bug there can only make
theorems unprovable, never make a false engine statement provable.
I tested this restatement against the docs and believe I have it
right. What the tiers do NOT cover, and the docs admit: whether the
Lean engine faithfully ports Cerberus (deferred to upstream
differential validation), and whether `driveJ` is faithful to the
real driver for loops beyond this fragment (registered:
`aid_supply` ticking is ignored; the production `runND` equation
for a loop run is explicitly NOT claimed).

**(d) HOW do I check it myself?** Run the setup script and the
capped `lake build` from the package dir; a green build elaborates
every proof and runs `Audit.lean`, which sweeps all 755 theorems'
axiom cones against the declared boundary and all 1499 constants
for `sorryAx`/`ofReduce*` (documented tail, which I reproduced
verbatim). Then `#print axioms` on the ten pinned theorems via the
documented heredoc (I reproduced the documented output
character-for-character), and the statement-surface census script,
which re-derives the engine/spec-idiom/Iris/core partition of each
pinned statement (reproduced; matches the walkthrough's paste
exactly). Tier 3 is checked by reading the printed definitions,
which the walkthrough lays out per identifier.

---

## 2. The stumble log

Severity: READER-MAJOR = blocked or misled understanding;
READER-MINOR = friction; NOTE = observation (including positives).

1. **READER-MAJOR — the one axiom is never exhibited.** The trust
   story's most sensitive element, `runEffectful`, is discussed at
   length (temporal, statement-cone-only, retirement planned) in
   README, walkthrough §4, and the Audit.lean header — but its
   actual *statement* is printed in none of them. The register chain
   README → `Audit.lean` header → "LemLib.lean:54" terminates at a
   file:line inside a vendored `.lake` dependency; I had to grep to
   learn it is `axiom runEffectful {α : Type} : (Unit → BaseIO α) → α`.
   A reader asked to accept an axiom should be shown the axiom. (It
   is, for what it's worth, a choice-flavored world-erasure axiom I
   find consistency-plausible — but I had to do that analysis with
   no help from the docs.)

2. **READER-MAJOR — the semantics' trustworthiness is asserted, not
   exhibitable.** Acceptance question (b) bottoms out in "differentially
   validated against the OCaml oracle," and the only pointer offered
   is `../scripts/semantics-pin.env` — a pin file written in project
   jargon ("[USER] mission order", "the pin dance", "S-basket") that
   tells me *which commit*, not *what the validation covers* (how
   many programs? which fragment? where is the record?). The
   walkthrough honestly says "validation is that project's, not this
   package's," but gives no landing point for a reader who wants to
   assess it. From inside the package the strongest claim in the
   headline — "a real C semantics" — is take-it-on-faith.

3. **READER-MINOR — exhibit-table forward references.** "Lane",
   "trio", "drive/driveJ/production", and "in-budget fuel" appear as
   column vocabulary before any of them is defined (lanes: next
   paragraph; trio: two sections later). I read the table twice.

4. **READER-MINOR — `aids` (the "action-id supply") is never
   explained in front-doc prose.** It appears in every drive-lane
   statement (`aids : Nat → Nat`), the fib docstring waves at "any
   action-id supply," and §5.1's reading table does not give it a
   row. I only learned what it mirrors (the driver's fresh
   action-id draw) from a comment inside `Soundness.lean`.

5. **READER-MINOR — redundant hypothesis unexplained.**
   `list_reverse_certified` carries both `hfuel : 6 + nsteps ≤
   lemDefaultFuel` and `hfuel2 : 5 + nsteps ≤ lemDefaultFuel`; the
   second is a trivial consequence of the first. The reading table
   bins them jointly as "in-budget fuel" and never remarks on the
   redundancy — a reader wonders whether they missed a subtlety.
   (The docstring's "interim in-budget form" hints this is known
   scaffolding, but nothing says so plainly.)

6. **READER-MINOR — the build's actual experience is
   under-documented.** (i) `../scripts/capped` printed two loud
   warnings — "systemd user bus unavailable (sandbox); running
   UNCAPPED" and "interim per [USER 2026-08-29]" — that reference
   governance context a stranger cannot decode; neither README nor
   walkthrough says these may appear or what they mean for the
   verification claim (answer: nothing — the cap is a
   resource-limit wrapper — but I had to infer that). (ii) The
   docs give the expected *tail* but not an expected cold-build
   duration; mine replayed from cache in 0.4 s, which is obviously
   not what a fresh clone would see. (iii) The tail is preceded by
   dozens of `unusedVariables` linter warnings from `generated/*`
   files, unmentioned — a stranger's first reaction is to wonder if
   warnings matter.

7. **READER-MINOR — internal shorthand in the divergence
   register.** Entries lean on labels like "D26", "R2", "the D14
   partition rows", "recon §2.6" — indices into dated internal notes
   the front docs otherwise don't require. Row contents survive
   without them, but every such label is a small "this document was
   written for insiders" signal.

8. **READER-MINOR — house-flavored phrases used as if standard.**
   "The registered growth step", "the allocator-cursor resource",
   "fail-closed absences of a mirror step", "statement-stratified
   WP". Each is decodable from context, but each cost a re-read.
   (Contrast: "provenance", "small axioms", "guarded fixpoint" are
   all properly glossed.)

9. **READER-MINOR — the wp_store table row.** "derived logic
   (interior; meaning lands via the exports below)" in the Lane
   column was opaque on first read; it becomes clear only after the
   trust story defines "interior". Two reads.

10. **READER-MINOR — front docs send outside the package.** Logged
    sends: README → `../scripts/semantics-pin.env` (twice);
    README/walkthrough builds → repo-root `scripts/capped` and
    `scripts/setup-cerberus-dep.sh`; Audit.lean header →
    `LemLib.lean:54` (vendored dep) *and* the semantics repo's
    `lean_frontend/TODO.md` / `DESIGN.md` for the axiom story;
    `dischargeStep`/divergence register → the engine's generated
    `Driver.lean` / `Core_reduction.lean` (fair — that's the object
    of study). The package is *almost* self-contained; the two
    sends that carry real trust weight (pin file, axiom
    declaration) are the two that land on insider-written or
    vendored files — see findings 1 and 2.

11. **NOTE (positive) — every verbatim claim I checked was
    verbatim.** Statement quotes for `list_reverse_certified`
    (ListRevExhibit.lean:1690) and `fib_certified_total`
    (FibExhibit.lean:570) match source exactly; `driveJ`,
    `SeedChain`, `ChainAt`, `Coh` as printed in the walkthrough
    match source; line citations (lrBody:930, wp_store Rules.lean:143,
    Driver.lean:273) all accurate; the divergence-register claim
    that the driver drops the memory order (`mo1` unused in
    `action_request_sequential2`) is visibly true in the generated
    engine source.

12. **NOTE (positive) — documented outputs reproduced exactly.**
    Build tail (755 theorems / 40 boundary / 1499 constants / 434
    jobs), all ten `#print axioms` lines, and the census sections
    for the three walked theorems match the docs
    character-for-character on this checkout.

13. **NOTE (positive) — the ghost-functor binder treatment.** §5.2's
    handling of the one machinery-shaped hypothesis
    (`{GF : BundledGFunctors} [SpikeGpreS GF]`) — a universally
    quantified hypothesis can weaken but never strengthen; here is
    the concrete instance; here is the demo running at it — is
    exactly the argument a skeptical reader needs, made before I
    could ask.

14. **NOTE — authorship disclosure.** The README ends "Built by AI
    agents (Claude, Anthropic) under the direction and review of
    Mike Dodds." Relevant context for a reviewer, plainly stated.

15. **NOTE — setup script on this checkout was a no-op** (already
    primed, 0.008 s, self-describing output). The docs don't say
    what it does on a truly cold machine or that it needs no
    network; "offline" is claimed for the build but the setup step's
    behavior is undescribed.

16. **NOTE — a nice fact the reading table doesn't call out.**
    `fib_certified_total`'s conclusion is `.done (ivVal (fibSpec
    n.toNat)) σ₀` — the *initial* memory returned unchanged, i.e.
    the fib program provably touches no memory. Implied by the
    statement, unmentioned in prose; a one-liner would land it.

Tally: 2 READER-MAJOR, 8 READER-MINOR, 6 NOTE.

---

## 3. The claim check (reader-grade)

### 3.1 `list_reverse_certified` (mandatory pick)

**Found in source:** `CerberusHeapLang/ListRevExhibit.lean:1690`,
exactly where both docs say, with statement identical to the
walkthrough §5.2 verbatim quote (I diffed by eye, binder by
binder). The docstring above it restates the claim consistently
with the README table row.

**Statement vs. the §5.2 reading table:** every identifier in the
statement is covered by a table row or by the section-variable
preamble (`loc/ann/ra/mo/*bty` — quantified metadata). Checked off:
`SeedChain`, `ChainAt`, `Coh`, `SpikeHeapF`/`SpikeCell`, `driveJ`,
`procThread`, `lrProg`/`lrRS`/`lrProcSym`, `ptrVal`, the engine
bin (`PointerValue`, `isLibraryLocation`, `lemDefaultFuel`,
`kill_reason`, `mem_error`, `fmapEmpty`, …), the GF binder, and the
hypothesis rows. The printed `SeedChain`/`ChainAt`/`Coh`
definitions match source. **Not covered by the bins:** (i) the
`hfuel`/`hfuel2` redundancy (finding 5); (ii) `nsteps`/`aids` have
no rows — plain quantified data, but `aids`' meaning is genuinely
undocumented at the front (finding 4); (iii) the `[fmapEmpty]`
env-stack literal in `procThread … [fmapEmpty]` — decodable because
`procThread` is printed in §5.1, so acceptable. Verdict: **the
table suffices to parse and understand the statement**; the two
loose ends are friction, not gaps in meaning.

**Documented verification, run:** `#print axioms
CerberusHeapLang.list_reverse_certified` → `[propext,
Classical.choice, Quot.sound]` (matches docs; ~1 s). Census section
for the theorem regenerated via
`../scripts/capped ~/.elan/bin/lake env lean scripts/statement_census.lean`
→ ENGINE(14)/SPEC-IDIOM(18)/IRIS(1: `Iris.BundledGFunctors`)/
LEAN-CORE(19), identical to the walkthrough's paste. Also ran
`#print axioms` on `list_reverse_demo` (trio — so the hypotheses
are concretely satisfiable, the anti-vacuity point).

### 3.2 `fib_certified_total` (my pick: the boldest claim)

**Found in source:** `CerberusHeapLang/FibExhibit.lean:570`,
statement identical to §5.1's verbatim quote. The proof directly
above/around it is a per-step `driveJ_step` induction with a
concrete variant accounting — consistent with the "termination
accounting" story; I did not audit the proof (the docs' point is
that I don't need to — only the statement and the kernel).

**Statement vs. the §5.1 reading table:** every identifier covered
(`driveJ`, `DriveResult.done`, `procThread`, `fibProg`/`fibRS`/
`fibProcSym`, `fibSpec`, `ivVal`, `Mem`; engine bin; `hn`;
section-variable preamble for `ra/ibty/abty/bbty`). The table's
"nothing else" hypothesis row is accurate: `σ₀` and `aids` are
universally quantified, and there is genuinely no fuel hypothesis —
the concrete bound `2·n+4` sits inside the statement instead. The
printed `driveJ`/`DriveResult`/`procThread`/`ivVal`/`fibSpec`
definitions all match source (`Adequacy.lean:529` etc.). **Not
covered by the bins:** only the unremarked σ₀-returned-unchanged
fact (finding 16). Verdict: **table fully suffices**; this is the
cleanest statement in the package and the docs are right to lead
§5 with it.

**Documented verification, run:** `#print axioms` → exactly the
trio (matches). Census section matches the paste
(ENGINE 6 / SPEC IDIOM 10 / IRIS 0 / LEAN CORE 17).

### 3.3 Extra spot-checks performed along the way

- Full documented build: tail verbatim as documented (0.4 s, cache
  replay; `capped` warned UNCAPPED — finding 6).
- Full ten-theorem verify-me heredoc: output matches the README's
  "observed output" block exactly, including the line-wrapping of
  the last entry.
- `dischargeStep` (Soundness.lean:149) read against the generated
  engine `Driver.lean:273`: the StoreRequest2/LoadRequest2/
  CreateRequest2 arms visibly project the driver's
  `storeM`/`loadM`/`allocateObject` calls; `mo1` is indeed dropped
  by the engine, as the divergence register claims.

---

## 4. The skeptic's questions (seminar Q&A)

| # | Question I would ask | Answered? | Where / residue |
|---|---|---|---|
| Q1 | Is this really *the* frame rule, or a lookalike? | **Yes** | `SemTriple` (walkthrough §3.2): ∀ disjoint R, same R returned verbatim — the semantic frame property; plus `semantic_frame`, `triple_frame`, and the concrete exhibitB. Residue, registered: framing granularity is whole-allocation byte-list cells, no per-byte splitting (README divergence table) — so ∗ separates allocations, not bytes. Real frame rule at coarse granularity. |
| Q2 | What is this driveJ vs "production" business, and does the asymmetry undermine the headline? | **Yes — candidly** | README "Scope"; walkthrough §4 "one honest asymmetry". Straight-line programs reach the shipped pipeline (`runND` equation); the flagship loop exhibits stop at `driveJ`, a *package-defined* 10-line projection of the driver's loop, plus a proved registration tie for the label maps. My judgment: softens, does not undermine — but it does mean the headline exhibit's statement lives partly in tier-3 (read-the-idiom) trust, and the docs say so themselves. |
| Q3 | What exactly is the one axiom, and why should I accept the "temporal" story? | **Partly** | Role, scope (2 modules, statement-cone-only), entry path, and retirement plan: documented thoroughly (Audit.lean header). The axiom's *statement*: shown nowhere; I grepped vendored source to find `axiom runEffectful {α : Type} : (Unit → BaseIO α) → α` (finding 1). The "holds for every value of the seam" claim is prose, not a theorem I can point at. |
| Q4 | How big is the certified fragment, really? | **Yes** | README "Scope" enumerates it exactly: store/load/create, `PtrEq` only, `Esseq` at three pattern shapes, `Esave`/`Eif`/`Erun`, value-scrutinee `Ecase`, a few pure forms; no `Ewseq`, no allocation rule, no other memops, single-threaded, no concurrency. It is small and the docs never pretend otherwise. |
| Q5 | Are the exhibits C programs, or hand-authored Core? | **Yes** | Walkthrough §2: "written directly in Core." No exhibit passes through the C→Core elaborator. "Real C semantics" = real interpreter + memory object model; the C frontend is exercised nowhere in this package. I'd want the README to say this one sentence more bluntly. |
| Q6 | Why believe the Lean engine *is* Cerberus? | **Deferred, not answerable here** | "Differentially validated against the OCaml oracle" + a commit pin. No summary of validation scope/coverage is reachable from the package (finding 2). Honest about the deferral ("validation is that project's"), but a stranger cannot close this loop. |
| Q7 | Could the spec idiom be gamed — could `drive` compute something other than what the driver does? | **Structurally addressed** | Tier 3 (§4): smallness + printed definitions; demos as executable vacuity checks; and decisively `exhibitA_prod`, which states the *shipped* `runND ∘ initial_driver_state` composite with no package-defined execution function at all — pinning the idiom from outside for straight-line runs. My Driver.lean:273 spot-check corroborated `dischargeStep`. Residue: for loops the pin is indirect (registration tie only), and `driveJ` ignores `aid_supply` ticking — registered. |
| Q8 | Does the postcondition claim anything about heap cells outside the footprint? | **Yes — explicitly bounded** | README Scope: the general `SemTriple` constrains only the P ⊎ R split it quantifies; untracked cells are not claimed preserved (the production equation does pin the full final layout state). Stated before I could ask. |
| Q9 | Could the seeded-chain hypotheses be unsatisfiable (vacuous theorem)? | **Yes** | `list_reverse_demo` instantiates a 3-node chain with every decode fact by `rfl`; the walkthrough names vacuity as exactly the risk the demos discharge (§4 guard 2). Verified: demo's cone is the trio. |
| Q10 | Is "in-budget fuel" hiding proof slack? | **Yes, answered** | The budget is the engine's own `lemDefaultFuel = 10^6`, an interpreter artifact; and `fib_certified_total` shows the variant route that eliminates fuel hypotheses entirely. List-reverse-total is a registered residual with a named plan (11·n + 6). |

Unanswered or only-partly-answered from within the package: **Q3
(the axiom's statement) and Q6 (what the differential validation
actually covers)** — the same two items as the MAJOR findings.

---

## 5. Verdict

**Would I believe the Reynolds/O'Hearn-over-real-C claim after this
session? Yes, with one precisely locatable reservation — and the
docs themselves taught me where to put it.**

The Reynolds/O'Hearn half I now believe outright: the small axioms
are small axioms (one-cell footprint, UB-exclusion by ownership),
the frame property is the real ∀-frame quantifier structure and not
a lookalike, `isList` is plain structural recursion, the loop
invariant is the textbook one, and the flagship proof is
compositional. The "over a real C semantics" half I believe *as
scoped by the docs*: theorems in engine-only vocabulary about the
execution of a genuinely independent, executable, byte-level,
provenance-aware Core interpreter — with the loop exhibits stated
against a small, cited, demo-pinned projection of that engine's
driver rather than the shipped pipeline, on a small hand-authored
fragment, and with the engine's fidelity to Cerberus-the-C-semantics
resting on an upstream validation claim I could not inspect. Nothing
I checked — ten axiom cones, three census partitions, five line
citations, one engine-source divergence claim, two full statement
reads — came back other than exactly as documented, and that track
record is itself evidence. This is the rare artifact whose
documentation *under*-promises relative to what spot-checking
finds.

**The single change that would most improve a stranger's path:** add
a short, self-contained "what you are asked to take on faith"
subsection to the README's trust story that (a) prints the one
axiom verbatim — `axiom runEffectful {α : Type} : (Unit → BaseIO α)
→ α` — with its one-paragraph consistency story, and (b) summarizes
in two or three sentences what the upstream differential validation
actually covers (what is compared, at roughly what scale, and the
path to its record), instead of pointing at a jargon-laden pin
file. Those are the only two places my acceptance questions (b) and
(c) currently dangle on out-of-package pointers; closing them makes
the package's trust story fully auditable from the README alone.

---

*Reader-experience facts for the record: all documented commands
were run; every one completed in ≈1 s on this (warm-cache, primed)
checkout — setup 0.008 s, build replay 0.4 s, verify-me ≈1 s,
census ≈1 s. `scripts/test_unit.sh` (both packages + grep gate) was
not run, to stay within the session budget. No files outside this
review were modified; nothing was committed.*
