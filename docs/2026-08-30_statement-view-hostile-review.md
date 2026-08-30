# Hostile review: the statement-view design (Candidate A recommendation)

Date: 2026-08-30. Provenance: [AGENT: hostile reviewer, not the design
author], commissioned under the [USER 2026-08-29] statement-layer
derisk plan (DECISIONS.md: "two candidate designs argued against the
measured table under hostile review"). Document under review:
`docs/2026-08-30_statement-view-design.md` (this worktree, 799 lines,
DRAFT). Brief: break the recommendation if it can be broken.

Method: (1) all cited evidence docs re-read (STUDY, CENSUS, MAP,
RELMEMO, DECISIONS); (2) every load-bearing donor cite re-verified
against `deps/refinedc/theories/` at the port-map checkout —
programs.v:66-98, function.v:5-65, lifting.v:1001-1319, 540-570,
automation.v:145-254, notation.v:69-82; (3) ten fresh probe C files
elaborated through the pinned OCaml driver (census-lane
configuration, `--pp=core --rewrite`, NO `--sequentialise`, matching
the E7 fragment-1 flip), sources and outputs at
`/tmp/claude-1000/hostile-probes/` (ephemeral; all load-bearing
quotes inline below, labeled verbatim). Probe command (identical to
the study §1.2 except the flag set):

```
CERB=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_build/default/backend/driver/main.exe
RT=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_build/install/default
$CERB --runtime=$RT --pp=core --rewrite <file.c>
```

All 10 probes exit 0, empty stderr (transcript: `h01_switch`,
`h02_dowhile`, `h03_ternary`, `h04_shortcircuit`, `h05_comma`,
`h06_nestedloop`, `h07_fnptr`, `h08_globals`, `h09_sizeof`,
`h10_static`).

---

## VERDICT: UPHOLD-WITH-AMENDMENTS

The core architecture survives hostile examination: the classifier's
untrusted-dispatch-metadata status is genuine (§1 below — no
promotion into a trust path was found; rules-as-theorems plus
elaboration recheck means misclassification can only produce stuck
goals, never wrong theorems), and the deciding argument against
Candidate B (template cost is candidate-invariant; only A converts it
into donor shape) survives AT THE STATEMENT STRATUM, which is where
the candidates genuinely differ.

What does not survive: (i) the claimed closure of the species/template
sets — broken by the first four cheap probes beyond the corpus,
including constructs the assumption register does not even list as
unmeasured; (ii) row A-3 as stated — the wholesale deletion of the
`ls`/post-condition clause breaks the calling convention's
argument-slot ownership round-trip; (iii) the "9 rows, all bin (b)"
arithmetic, which is understated on A's side (substrate-forced WP
carrier) and overstated against B; (iv) the spike, which as scoped
cannot fire the design's own flip criteria. Findings and required
amendments below. None of these flips A→B; several of them, left
unamended, would make a "spike survived, ratify" claim unsound.

---

## Findings

### MAJOR-1: Row A-3 breaks the argument-slot ownership round-trip; the spike cannot detect it

The design (§3.2 delta (i), §3.5, row A-3) drops `typed_stmt`'s `ls`
and `typed_stmt_post_cond`'s points-to clause wholesale, justified by
E6/A7: "Core kills locals in-band before the return join; there is
nothing left to return."

That justification covers LOCALS only. It does not cover ARGUMENT
SLOTS, and the donor's clause covers both:

- Donor `typed_stmt_post_cond` (programs.v:66-67, verbatim):
  `(∃ ty, v ◁ᵥ ty ∗ ([∗ list] l;v ∈ ls;(fn.(f_args) ++ fn.(f_local_vars)), l ↦|v.2|) ∗ R v ty)` —
  note `f_args ++ f_local_vars`.
- Donor `wp_call` (lifting.v:1053-1056, verbatim): the return
  continuation is
  `(∀ v, Ψ' v -∗ ([∗ list] l; v ∈ lsa; fn.(f_args), l↦|v.2|) ∗ ([∗ list] l; v ∈ lsv; fn.(f_local_vars), l↦|v.2|) ∗ Φ v)`
  — the callee hands the ARG-slot points-to back so the caller-side
  proof can free the blocks (lifting.v:1088).
- Core's calling convention (STUDY row 7, re-confirmed verbatim this
  session, h07 `apply`): the CALLER creates and stores each argument
  slot, passes the slot pointer to `ccall`, and kills the slot AFTER
  the call returns:
  `let strong a_548: loaded integer = ccall('signed int (*) (signed int)', a_537, a_543) in kill('signed int', a_543) ;`
  The kill is the T4 template ([CENSUS] §2.3), a caller-side
  obligation.
- The callee proc receives the slot pointer (`proc add1 (x: pointer)`)
  and loads through it — so slot ownership must transfer INTO the
  callee at `Eccall` (this is exactly `typed_function`'s
  `lsa ◁ₗ atys` premise, function.v:62, which §3.5 keeps).

Consequence: ownership of each arg slot goes into the callee and,
under the design as written, never comes back — `fn_ret_prop`
(function.v:53-54) has no slot clause in the donor (slots return via
the post-cond, which the design deleted), so the caller's T4 kill
rule has no `l ↦ …`/freeable to consume. Either the post-cond keeps
an ARGS clause (donor-shaped minus locals — the honest amendment), or
`fn_ret_prop`/`typed_function` changes beyond the declared rows
(a KA3 event), or an undeclared lending/fraction divergence is
invented. A-7 (kills-before-return) is about the callee's own locals
and is irrelevant to this.

This is a shape-correctness hole in the design's central deliverable
(the declared signature delta), and it sits precisely in the zone the
spike excludes (A9: no call template in the spike files). Registered
gap A9 is therefore not merely "the reviewer may demand a third
file" — without a call file the spike is structurally blind to a
known-broken row. Amendment required before spike dispatch: restate
A-3 as "post-cond keeps the f_args clause, drops the f_local_vars
clause"; add the call file (see spike widening).

### MAJOR-2: The species/template closure fails on first contact beyond the corpus, including constructs the assumption register does not list

The design rests its bounded-classifier argument on E1's closed
six-species set and E7/CENSUS's 4-template closure, with A1/A2
registering `switch`, do-while, statics, globals, varargs as
unmeasured. Ten cheap probes (method above) show the closure is
narrower than registered, and A1's unmeasured list itself omits the
most common offenders:

**(a) `switch` (h01) — a seventh statement species plus nested-save
structure.** Verbatim (h01_switch.core:5-13, trimmed):

```
case a_519 of
  | Specified(a_520: integer) =>
      let strong a_521: integer = pure(conv_int('signed int', a_520)) in
      if a_521 = 0 then run case_524(r) else pure(Unit) ;
      if a_521 = 1 then run case_523(r) else pure(Unit) ;
      ...
      save case_524: unit (r: pointer:= r) in
      ...
  | Unspecified(_: ctype) =>
      pure(undef(<<UB036_exceptional_condition>>))
end ;
```

Three departures from the species set: (i) a statement-position
`Ecase` whose arms are SPINE SEGMENTS — not the truthiness-coercion
species 3 (pure/nd bodies) and not covered by any constructor in
§3.1's list; (ii) the case-label saves are NESTED INSIDE the case
arm, not on the proc spine — the save-map extraction and the
"save set IS the block map" story (§3.3, E3) must reach saves under
case arms (C fall-through between cases arrives as save adjacency
there, so A-6 must fire inside an arm); (iii)
`let strong a_521 = pure(conv_int(...))` is a value-binding spine
node WITHOUT `Ebound` — species 2 is defined as
`let strong x = Ebound(…)` and does not match. A2's "presumably
Ecase + save cluster ... by analogy with Eif" was directionally right
and materially insufficient.

**(b) do-while (h02) — same new species, DIFFERENT truthiness
handling.** Verbatim (h02_dowhile.core:54-59):

```
case a_516 of
  | Specified(a_515: integer) =>
      if not(a_515 = 0) then run do_514(s) else pure(Unit)
  | Unspecified(_: ctype) =>
      pure(undef(<<DUMMY(unspecified AilSdo)>>))
end ;
```

The do-while back-edge condition does NOT use the measured
`nd(True,False)` truthiness coercion (row A-4's template): it is a
statement-position `Ecase` with the Unspecified arm an
`undef(<<DUMMY(unspecified AilSdo)>>)` — a different template for the
same C construct family (loop conditions), directly against the E11
uniformity extrapolation, and carrying an elaborator DUMMY tag (see
NOTE-12).

**(c) `?:`, `&&`, `||` (h03, h04) — expression-position conditional
effects, absent from BOTH evidence docs' taxonomies, and A1 does not
name them.** Verbatim (h03_ternary.core:35-55, trimmed):

```
case a_522 of
  | Specified(a_523: integer) =>
      if a_523 = 0 then
        let strong a_525: loaded integer = load('signed int', a) in
        pure(conv_loaded_int('signed int', a_525))
      else
        let strong a_532: loaded integer =
          let weak (a_526, a_527) = unseq(load('signed int', b), pure(Specified(1))) in
          ...
  | Unspecified(_: ctype) =>
      pure(undef(<<UB_CERB004_unspecified__conditional>>))
end
```

— an `Ecase`/`Eif` with EFFECTFUL branches (loads, nested unseq)
inside the full-expression `Ebound`; in h04 the same shape sits
INSIDE Eunseq arms (12 unseq nodes for two short-circuit conditions;
the `&&` right operand's load chain is conditionally evaluated inside
an arm). The census's arm taxonomy (T1 arm classes: loads, load
chains, pure, ccall, kill, rmw — §2.1/§2.3) has no
conditional-effect class. Worse for the evidence base: the census
CORPUS contained one instance — u10's `max` is `a > b ? a : b` — and
the mechanical classifier (content markers, CENSUS §1.3) absorbed its
conditional structure into "load-chain"; the shape was measured and
not seen. So A1 ("corpus representativeness") is itself incomplete:
`&&`/`||`/`?:` — the most common C operators after arithmetic — are
neither measured, nor listed as unmeasured, nor mapped in §3.6's
dispatch table, while the DONOR has three dedicated rules for exactly
this row (`type_ife` programs.v:1293, `type_logical_and` :1308,
`type_logical_or` :1324, over the `IfE`-desugared `LogicalAnd/Or`
notation, notation.v:69-82). A donor rule family with no declared
Core-side counterpart is a hole in the "ports shape-literally with
donor file:line cites" residue claim (§3.8 closing paragraph), not
just a corpus gap.

**(d) Smaller closure breaks** (each needs a species/template or an
explicit out-of-fragment ruling): `create_readonly` action species
for string literals (h08_globals.core:22, verbatim:
`create_readonly(Ivalignof('char[3]'), 'char[3]', Specified(Array(...)))`);
top-level `glob` initializer expressions (globals + statics — h10
shows `static int c` becomes a `glob`), currently on no agenda row;
array-typed stores (`store('signed int[3]', a_555, a_559)`);
`Esseq` INSIDE `Ebound` for the comma operator (h05); indirect-call
template variance (h07: designator arm is
`let strong a_536 = load(...) in pure((a_536, cfunction(a_536)))`
with an extra variadic-flag disjunct
`if a_540 \/ not(are_compatible ...)` — the call chain is a template
FAMILY, not one template); shift operators wholly unprobed (donor
`int_arithop_sidecond` ShlOp/ShrOp are implementation-defined-flavored,
lifting.v:562-567 — the Core catch-pattern for `<<`/`>>` may not
match the measured add/sub/mul pattern).

Consequences. The fail-closed architecture ABSORBS all of this
correctly (everything above lands in `SUnclassified` loudly — the
design behaves as designed), so this does not refute A. What it
refutes is: (i) the "bounded artifact" framing of §3.1/§3.9 — the
species set demonstrably grows on first contact with everyday C, so
the classifier-fragility price quoted against B is higher than
represented; (ii) §6 flip 2's threshold ("at material frequency") is
already met — every C program with `switch`, do-while, `&&`, `||` or
`?:` fails the lint as specified, which is approximately every C
program; (iii) A1/A2 must be rewritten from this probe set before the
spike, and the species/template set revised, else KA1 is
untestable-by-construction (see MAJOR-5).

### MAJOR-3: The "loud at ingestion" advantage is overstated — the lint as specified cannot see the newly found gaps

§5's head-to-head credits A with "coverage failure mode: loud at
ingestion (lint)" vs B's "loud mid-proof". `viewCheck` (§3.7) runs
`classify`, which is defined over STATEMENT-position forms (§3.1).
The MAJOR-2(c) shapes live at expression grain — inside `Ebound`,
inside unseq arms — where dispatch is the `liRExpr`-analog at proof
time, not the classifier. Unless the lint is specified to recurse
through expression content and check template coverage there (it is
not, as written), a never-seen program with `&&` in a condition
passes the lint and fails mid-proof — exactly B's failure mode. The
product-gauge claim (§3.9: "either classifies fully ... or fails
loudly at ingestion") is false as specified. Amendment: define
`viewCheck`'s recursion to cover the expression-template layer, or
strike the ingestion-vs-mid-proof row from the head-to-head.

### MAJOR-4: The substrate coupling is deeper than declared — the "9 rows" count is conditional on D-promotion

§6's process note claims the recommendation "does NOT depend on the
unratified [RELMEMO] hybrid being chosen — any substrate that
delivers syntax-facing per-construct WP lemmas supports either
candidate." A4 registers only that the stage-α stratum "will exist in
∀-configuration form."

But §3.2's signatures are written against a SYNTAX-INDEXED WP carrier:
`typed_val_expr (e : CoreExpr) ... WP e {{Φ}}` "ports verbatim";
`WPs` is "a definition over WP." Under the actually-recommended
RELMEMO 3.E hybrid, that carrier does not exist until D-promotion:
3.E's own scalability paragraph (RELMEMO §3.E) says judgments are
"configuration-flavored (`ctl`-token premises) rather than
donor-literal `WP e`," and instructs that "the port ledger must carry
this as a divergence ... bin (b) ... unless/until promotion to D
erases it." That is a tenth divergence row, touching the SIGNATURE of
every judgment in §3.2 (every `WP e`/`WPs s` becomes a
configuration-flavored analog), and the statement-view doc neither
counts it nor conditions its "shape-literal modulo 9 rows" headline
on D-promotion. The two documents' claims are inconsistent as
written: either the substrate is promoted to a syntax-indexed
Language instance (D) and §3.2 is as literal as claimed, or it is not
and the ledger is ≥10 rows with the extra row smeared across every
signature. The coupling must be declared: state the §3.2 signatures'
dependence on the syntax-indexed carrier, and register the
configuration-flavor row as conditional. (What genuinely IS
substrate-independent: the classifier, the species set, the template
content, the fail-closed story, rows A-1..A-9's forcing facts. What
is coupled: every "verbatim/shape-literal" signature claim.)

### MAJOR-5: The spike cannot fire the design's own flip criteria

§3.10's spike is `wrapping_add` + `p02_if`: straight-line arithmetic,
one `Eif`, early return, assignment, create/kill. Against the
registered risks:

- **No loop.** §6 flip 3 (the locals divergence escaping its rows —
  loop-locals' create/kill leaking into `typed_block`'s shape,
  breaking the `split_blocks`-analog) requires a loop with a
  body-local. Neither spike file has a loop at all, so the
  `typed_block`/`wps_block_rec` port — the Löb rule, the invariant
  channel, A-3's per-iteration story, and the A-6 fall-through rule
  at a loop exit — goes entirely unexercised. KA3 cannot fire on
  `typed_block` if `typed_block` is never used.
- **No call** (A9, registered) — but per MAJOR-1 this is now a
  known-broken row, not a nice-to-have.
- **No switch/do-while/&&** — per MAJOR-2 the species set fails
  there; KA1 as scoped ("any spine node in the two spike files lands
  in SUnclassified") is run against the two files the species set was
  MEASURED FROM. Its firing probability is approximately zero by
  construction; surviving it certifies nothing about closure.
- **Measurability of KA3/KA4**: "requires changing any donor judgment
  SIGNATURE beyond rows A-1..A-9" and "side-condition surface differs
  beyond the declared rows" have no specified measurement artifact or
  independent grader — as scoped, the spike worker self-grades
  literalness. Fix: KA3 requires a side-by-side signature table
  (donor `Definition` vs port, per judgment, diff annotated with its
  row); KA4 requires the donor wrapping_add trace's side-condition
  set (the SHELVED_SIDECOND set + in-walk discharges, extraction
  method already specified at MAP §3.8) as the committed baseline,
  both verified by the orchestrator per the worker-claimed-green
  rule.

Surviving the spike AS SCOPED would therefore not warrant
ratification. See the widening proposal at the end.

### MINOR-6: A6 (identity rebinding) is misclassified as ergonomics-only; it is load-bearing for `typed_block`'s shape

§3.3 claims the goto rule "does not DEPEND on identity defaults (it
substitutes whatever args appear), so A6 only affects invariant
ergonomics, not soundness." True for `wps_goto`'s analog; false for
`typed_block`. Donor `wps_block P b Q Ψ := □(P -∗ WPs Goto b {{Q,Ψ}})`
(lifting.v:1306-1307) is definable because `Goto b` is
argument-free. The analog `□(P -∗ WPs (run b ?args))` needs args in
the definition; only under identity rebinding is there a canonical
choice making one definition serve every run site and the A-6
fall-through insertion. If any elaboration path passes non-identity
args to a non-ret save, `typed_block`/`wps_block_rec` as shaped
(fixed `gmap label iProp`) cannot express the needed invariant — a
KA3-class shape failure, not an ergonomic one. (The measured
corpus already contains one non-identity save — `ret_N` takes the
return VALUE as a real block argument — handled only because
`SReturn` is special-cased.) Amendment: re-classify A6's blast
radius; add "non-identity args at a non-ret run site" to the flip
list; the loop spike file (widening w1) exercises it.

### MINOR-7: The ledger arithmetic is partially rhetorical on both sides

(a) **Against B.** §4.4 charges B ≈13 shape rows binned
(a)-unless-A-dead. But §4.2's own load-bearing observation is that B
needs the same template-scale lemmas; a B-variant retaining the
donor's expression-judgment SIGNATURES (typed_bin_op etc.) attached
to the same pexpr patterns A uses is plainly constructible — A itself
demonstrates the mechanism. The honest discriminator is the
STATEMENT stratum only (~5 judgments, ~8 statement rules,
`introduce_typed_stmt`/`typed_function` entry, `liRStmt` dispatch),
not 21-vs-9. The recommendation survives on that narrower ground
(that stratum is exactly what "the next layer ports literally" needs)
— but the head-to-head table should be corrected so the operator
adjudicates the real delta, not an inflated one.

(b) **On A's side.** Two understatements. First, MAJOR-4's
substrate-conditional tenth row. Second, A-1's bin: "dispatch via
classifier over patterns" is Cerberus-forced (E2/E4, genuine bin (b))
— but the classifier's PARTIALITY (vs a total grammar) is forced by
EVIDENCE limits ("the evidence cannot support [universal closure]",
§3.1, citing E11), which is a fact about our corpus, not about
Cerberus. Bin (b) requires a Cerberus forcing fact; partiality's
honest tag is an epistemic scope restriction. Split the row or
annotate it — otherwise the first ledger audit does it for you.

(c) **Blast radius disclosure.** The A-3 signature delta restates
every donor declaration mentioning the `fn ls R Q` spine — derived
count from `grep -c 'fn ls R Q' theories/typing/*.v`: programs.v 39,
int.v 7, automation.v 4, boolean.v 3, own.v 3, bytes.v 1,
function.v 1 = 58 textual occurrences across ~25-30 declarations
(type_goto/assign/if/switch/assert/exprs/skips/annot,
typed_block_rec, type_return at bytes.v:207, the elim-modal
instances, and the T-file TypedSwitch/TypedAssert instances). The
delta is uniform and mechanical (delete one argument, the length
premise, and per MAJOR-1 only the LOCALS half of the post-cond), so
one ledger row legitimately amortizes it — but the row should state
the count so "9 rows" is not mistaken for "9 touched declarations."

### MINOR-8: The avoided round-trip theorem survives in vestigial form; name it

§3.1 claims "no `to/of` round-trip theorem to prove and no trusted
boundary." Correct in the large — but three definitional-interface
functions sit inside JUDGMENT DEFINITIONS (not mere dispatch): the
save-map extraction ("Q = the proc's save map ... extracted once per
proc by the view", §3.3), the ret-label identification (`SReturn`
"recognized by the ret-label role"), and the fall-through identity-
Goto insertion (A-6). Because the `WPs`-analog ties Q to the proc
inside the definition (donor precedent: `⌜Q = rf.(rf_fn).(f_code)⌝`,
lifting.v:1003), a wrong extraction yields UNPROVABLE rules, not
unsound ones — the untrusted status holds — but the `wps_goto`-analog's
PROOF owes a one-time coherence theorem: extraction agrees with the
engine's own `Erun`-target resolution for every label (including
saves nested under case arms, per MAJOR-2(a), and label shadowing if
any). That is the vestige of the round-trip. Two amendments: (i) name
the lemma (one row or a stated obligation under A-6); (ii) prefer
defining the tie via the ENGINE's own save-collection functions
(`labeled`/`collect_saves`, cited at RELMEMO §3.D) rather than a
view-side extractor — then the coherence theorem is about engine
functions and mostly dissolves. Same discipline for the two
classification-inserts-syntax cases: the `SGoto`-by-fall-through and
`SSkip`-unreachable rules must be STATED over the actual Core shapes
(spine-flows-into-`Esave`; `Esseq` headed by `Erun`), with the view
supplying only the pointer to which rule to try — §3.3/§3.5 gesture
at this correctly; make it normative so no implementation ships a
donor-style trivial skip rule keyed on classification alone.

### MINOR-9: KA-criteria operationalization (consolidated)

From MAJOR-5: KA1 must be re-run against the REVISED species set on
files outside its derivation corpus (the widening's lint sweep); KA3
needs the signature table artifact; KA4 needs the committed donor
trace baseline; graders are the orchestrator, not the spike worker.
KA2/KA5 are measurable as stated. Add KA6 (below).

### NOTE-10: Pre-decide the `conv_loaded_int` surface

Every measured store wraps its value in `conv_loaded_int` (STUDY
row 1). The donor surfaces the corresponding conversion as a separate
expression-rule firing (the frontend emits an explicit
`UnOp (CastOp ...)` — visible in the study's own row-1 Caesium quote
— typed via the cast rules, lifting.v:349+). The design does not say
whether the Core conv is a separate pattern rule (donor-shaped) or
folded into the assignment/return templates (a KA4 surface
difference). It appears in both spike files; decide before the spike
so KA4 has a defined expectation. Adjacent positive check: the
arithmetic correspondence claimed in §3.4 is real for add/sub/mul —
`int_arithop_sidecond` AddOp/SubOp/MulOp = `n ∈ it`
(lifting.v:555-560) matches "the mathematical sum is in range" from
the `catch_exceptional_condition_*` pattern. Div/mod/shift unprobed
(MAJOR-2(d)).

### NOTE-11: `undef(<<DUMMY(unspecified AilSdo)>>)` in the semantics of record

The do-while probe (MAJOR-2(b)) shows the pinned elaborator emitting
a DUMMY UB tag on a reachable-in-principle path (Unspecified do-while
condition). Whatever rule covers that arm will be quantifying over an
elaborator placeholder. Flag to the cerberus-lean side (fragment/UB
taxonomy) — not this design's defect, but its rules will touch it.

### NOTE-12: Globals/statics initialization has no home

h08/h10: globals (and statics, which lower to globals) are `glob`
initializer EXPRESSIONS (create/store chains, `create_readonly` for
string literals). The donor's counterpart machinery
(`alloc_new_blocks`, `globals.v`'s `initialized`, adequacy.v's
initial-heap construction — MAP §1.3 stratum v, §5.1) needs a
Core-side story that no current agenda row owns. Cheap to add as a
fact-finding row now; expensive to discover during the first
`t05_main`-class exhibit.

### NOTE-13: Attack on the untrusted-status claim — result negative (design holds)

For the record, the promotion hunt came up empty: the ingestion lint
is advisory (fail-noisy, no proof value); the derived-form WP lemma
statements as described quantify over Core term schemas, never over
`classify`; the trace-alignment/replay lane is a build-ledger harness
outside the trust path (ENGINE-NOT-REPLAYER ruling); dispatch is
meta-level with elaboration re-checking every match. The two soft
spots found (definitional-tie functions, classification-inserted
syntax) are shape/provability risks, not soundness risks, and are
covered by MINOR-8. The claim "a misclassification cannot produce a
wrong proof, only a failed or stuck one" withstood adversarial
reading.

---

## Minimal spike widening (proposal)

Three additions; anything less leaves the declared flip criteria
untestable:

- **w1 — one loop file with a body-local** (t_binary_search twin, or
  the h06 nested-loop probe): require an actual
  `typed_block`/Löb-rule discharge for the loop head with the
  `split_blocks`-analog invariant map, with the body-local's
  create/kill inside the save. Tests: §6 flip 3, row A-3's
  per-iteration story, A-6 fall-through at the loop exit, MINOR-6's
  identity-args dependence, and the `wps_block_rec` port — none of
  which the current spike touches.
- **w2 — one call file** (p06_call twin): caller-side T3/T4 +
  `Eccall` atomic-call rule + callee `typed_function`, end-to-end,
  with the argument-slot ownership round-trip explicit. New kill
  criterion **KA6**: the caller's post-call kill discharges without
  changing `fn_ret_prop`/`typed_function` beyond the AMENDED A-3
  (args clause retained). Tests MAJOR-1.
- **w3 — a lint-only closure sweep** (hours, no proofs): revise the
  species/template set against h01-h10, then run `viewCheck` (with
  expression-template recursion per MAJOR-3) over the frozen
  15-program corpus + the 23 census files + h01-h10, and REPORT the
  `SUnclassified` census as a dated evidence doc. This converts
  A1/A2 from assumptions into measurements and makes KA1 meaningful
  (it then runs against files outside the species set's derivation
  corpus).

Ratification condition: spike survival = KA1-KA6 all silent on
w1+w2+the original two files, with the KA3/KA4 artifacts
(signature table, trace-baseline comparison) produced and
orchestrator-verified, and the MAJOR-2/3/4 amendments folded into a
revised design doc (fresh-eyes re-review of the delta only is NOT
sufficient per house rules if the revision is major; operator to
scope).

— end of hostile review —
