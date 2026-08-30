# Hostile review: the relational-semantics candidates memo (3.E hybrid)

Date: 2026-08-30. Provenance: [AGENT: hostile reviewer, fresh eyes —
did not write the memo]. Object under review:
`docs/2026-08-30_relational-semantics-candidates.md` (the "memo"),
recommendation 3.E (hybrid: rehabilitated park per-step ndM trunk +
stage-grown syntactic characterization stratum, D-promotion open,
probe first). Criteria: the NORTH STAR and TRUST ARCHITECTURE blocks
(CLAUDE.md), the DECISIONS register through the 2026-08-30 eunseq
entry. Method: source verification against the park branch
(`arc/segment-ladder`), the trimmed mainline (`core/semantics-first`),
the pinned iris-lean, and the generated engine; no runtime probes were
run (every finding below is a source citation, checkable in minutes;
a build-probe would have added nothing a cite does not).

Cite conventions: `park:` = `git -C ../cerberus-lean show
arc/segment-ladder:`, `core:` = `… core/semantics-first:`; `memo §` =
the document under review; `v3a` =
park:lean_frontend/docs/2026-08-29_v3a-loops-mechC.md.

---

## VERDICT: UPHOLD-WITH-AMENDMENTS

The trunk's load-bearing evidence is real — I verified it at source:

- `ksteps_of_runND` is a genuine ∀-expression, ∀-state theorem at the
  production fuel budget
  (park:lean_frontend/relsem/RelSem/PerStep.lean:431,533), cone
  `[propext, Quot.sound]` pinned in-build
  (park:lean_frontend/relsem/RelSem/Audit.lean:929-931).
- `cerbSt_adequacy` / `kAdequateSt_of_wp` are general (any
  `KDriveExpr`, any initial state with `MemInv`/`EnvWf`), trio cones
  pinned (park:…/CerbStateAdequacy.lean:136,239; Audit.lean:1014-1023).
- `m1_proved` exists, trio cone pinned (Audit.lean:359-360).
- The iris pins are byte-identical
  (park:lean_frontend/lakefile.toml rev `34390a01…` = this repo's
  lakefile.toml = deps/iris-lean HEAD — re-verified this session), so
  the zero-interface-migration claim holds.
- The peel anchors are rfl-grade as claimed
  (park:…/PerStepPeel.lean:66 `dnms_succ_unfold := rfl`;
  `runND_callND_eq_callK2` at :595).
- `runND_sound` survives on the trimmed mainline as claimed
  (core:lean_frontend/relsemcore/RelSem/RunND.lean:190).
- The postmortem's own salvage map endorses mechanism C and the V1
  decomposition as forward donors (POSTMORTEM-AND-FORWARD-BRIEF.md §4
  rows "Mechanism C", "The V1 state decomposition") — rehabilitation
  per se does not contradict the failure analysis, which was
  paradigm-level (harness primacy, the concrete-X disease), not a
  verdict on these components.

So the recommendation is not refuted. But the memo overstates what
the proved exhibits actually say (finding 1), was written against a
fragment definition superseded the same day (finding 2), misses a
structural donor-fit break that makes D-promotion mandatory rather
than optional (finding 3), and pre-registers a probe whose exemplars
dodge both the ratified fragment and the measured hard class
(findings 2, 4). Ratification should be conditional on the
amendments in §"Amended recommendation".

---

## MAJOR findings

### MAJOR-1. The proved "engine-only adequacy" is not the statement
the memo says it is — three undeclared qualifiers, one axiom bridge,
and the statement faces did not survive the trim.

The memo presents the exhibit as: "`CallHarnessAdequate prior tagDefs
file fname args fs spec` = ∀ triples ∈ `CerbND.runND (callND …)
(initial state)`, outcome is Active ∧ spec (relsemcore Call.lean; …
byte-identical statement defs; exhibit M1)" and concludes "Fully
discharges governing ruling 3" (memo §3.B); §2.4(v) calls M1
"PROVED with trio cone, end-to-end". What is actually proved:

```
M1Statement : Prop :=
  CorpusEnvHyp →
  ∀ (x : Int), intRange x →
    CallHarnessAdequateCns m1Prior m1File.tagDefs m1File "sgn"
      [intValue x] corpusFs (sgnSpec x)
```
(park:lean_frontend/relsem/RelSem/M1Statement.lean:44-49), where:

1. **`CallHarnessAdequateCns` is the CONSISTENCY-FILTERED face**
   (park:lean_frontend/relsemcore/RelSem/Threaded.lean:227): it
   quantifies runner outcomes *conditioned on
   `ConsistentRun prior seed st'`* (:214) — executions whose
   fresh-symbol draw window is non-capturing. Not every enumerated
   outcome; every *consistent* one.
2. **`m1Prior` is instrument-checked fixture data, not a theorem**:
   Threaded.lean's own header (:~200, "TEMPORAL registration")
   states the agreement "prior ⊇ the file's symbol numbers" is
   checked by the PriorCensus instrument, with a *registered mover*
   (a total symbol-census function) that was never built.
3. **The initial state is `initial_driver_state_threaded`**
   (Threaded.lean:75-97) — a hand-written field-for-field mirror of
   the generated `initial_driver_state` whose single change replaces
   the ambient draw `runEffectful (fun () =>
   CerberusFresh.freshIntIO ())` with an explicit seed. The
   *production* entry the differential lanes validate — ambient
   `initial_driver_state`, the one quoted by the mainline
   `HarnessAdequate` (core:…/RelSem/Cerberus.lean:268) — is
   reachable from the threaded form only through bridge lemmas that
   "DELIBERATELY carry `runEffectful`" (Threaded.lean header), and
   the ambient bridge family was in fact **deleted** at the
   2026-08-27 kill-list ("all were `runEffectful` carriers over the
   ambient `initial_driver_state`" —
   park:lean_frontend/relsemcore/RelSem/Call.lean:323-330 comment).
4. **`CorpusEnvHyp` = `CerberusFresh.digest () = ""`**
   (park:lean_frontend/relsem/RelSem/CorpusStatements.lean:36) — a
   statement-level hypothesis about an `@[extern]` opaque
   (CerberusFresh.lean:62). The trio cone is achieved by *assuming*
   a world fact, which is honest, but it is fine print the memo's
   "quantified exclusively over cerberus-lean objects" gloss hides.
5. **Threaded.lean did not survive the semantics-first trim.** The
   mainline relsemcore is exactly
   {Call, Cerberus, ExecModel, Machine, RunND} (tree listing,
   core:lean_frontend/relsemcore/RelSem/); the trimmed Call.lean
   ends at `callND` (:202/218 lines) — `CallHarnessAdequate`
   (park Call.lean:282), the Thr/Cns family, and the anti-vacuity
   metatheorem `consistentRun_of_supply_le` all have to be re-landed.
   Memo fact-of-record 2 ("the trimmed relsemcore spine … survives")
   is true of `runND_sound` and `HarnessAdequate`, but the *proved
   WP-facing statement faces* are park-only.

Consequence for the trust architecture: the end-state ruling demands
adequacy "stated EXCLUSIVELY over the cerberus-lean semantics" with
no relational vocabulary. The proved exhibits are stated over a
relsemcore-defined mirror state, a relsemcore-defined consistency
predicate with an instrument-trusted fixture, and an opaque-world
hypothesis; the step to the production entry costs the `runEffectful`
boundary axiom in the cone. Each element is defensible as a *declared
temporal boundary with a named mover* — but the memo declares none of
them, and §3.B's "fully discharges governing ruling 3 … from day
one" is false as stated. The honest form is: "discharges into a
∀-seed threaded/consistency-filtered statement; the production-entry
corollary carries the `runEffectful` boundary axiom (or waits on a
cerberus-lean-side seed-threading mover); `prior` correctness is
temporal with the census-function mover." Refined-cerberus's Audit
architecture (exact-cone assertions, boundary entries with
provenance) can absorb exactly this — but only if it is put on the
register *before* re-landing, as an operator-visible decision.

### MAJOR-2. The memo and its probe are premised on the sequentialised
fragment, which the same-day eunseq ruling superseded — the probe as
registered exercises almost none of the ratified fragment, and the
new obligations it creates are unpriced.

The memo throughout assumes "the port's referent fragment is
sequentialised/evaluated Core, Eunseq excluded" (memo §1.2), builds
§2.5's α/β realization decision on it, and rests candidate D's
tractability on it verbatim: "the sequentialised-fragment restriction
of §2.5 shrinking the context grammar to `Cwseq/Csseq/Cannot/Cbound`
— no `Cunseq` — which is what makes this tractable: single-redex
determinism per round, no interleaving fanout" (memo §3.D). The
DECISIONS 2026-08-30 eunseq entry supersedes this: **fragment 1 =
non-sequentialised Core, Eunseq live**, with the attachment layer
owing the shared-reads/disjoint-writes meta-theorem and an
atomic-call rule.

Consequences the memo does not price:

1. **The probe's premise excludes the fragment's bread and butter.**
   Both P1 and P2 are stated "with `C` unseq-free" (memo §4). Per the
   census, 98/98 Eunseq nodes sit inside every C full expression's
   `Ebound`, and 84 of 201 arms are single loads
   (2026-08-30_eunseq-census.md §2.1) — i.e. in fragment-1
   executions, *load rounds overwhelmingly occur inside `Cunseq`
   contexts*. P2 (the load exemplar) restricted to unseq-free `C`
   proves a lemma about configurations the ratified fragment rarely
   visits. A pass would not license the stratum.
2. **Under live unseq, per-construct round characterization needs a
   scheduling premise.** The engine's round advances the *first*
   `can_advance` step in `step_ctx`'s offered list
   (`find_can_advance`, generated/Driver.lean — first-match; greedy
   loop in `drive_nonmemory_steps_aux2`; plain action requests ARE
   greedy: `can_advance (Step_action_request2 … is_unseq_with_ccall)
   = ¬is_unseq_with_ccall`). With `Cunseq` in the grammar the offered
   list is a fanout (`get_ctx_unseq_aux`), so "arena = C[redex] ⟹
   the round does X" is only true when the redex is the *leftmost
   advanceable* one — a premise about the whole context's traversal
   order, not a local syntactic fact. This is statable (it is a
   standardization/leftmost-strategy premise — classical lineage:
   Curry–Feys standardization; deterministic abstract-machine
   scheduling), but it is a materially heavier statement than the
   probe's, and it is exactly falsifier F1's shape. The probe must
   test it, not avoid it.
3. **The unseq meta-theorem is a region rule, not a construct
   lemma.** On the trunk, one Eunseq's execution spans many rounds
   under the greedy schedule, with UB determined at the join
   (`do_race`, join-only). "Shared reads/disjoint writes ⇒ the join
   is race-free and value-determined" is a multi-round invariant
   argument over the round relation with footprint accounting — the
   proof genus of the park's *segment* machinery, not of `cstep_*`
   introduction lemmas. One mitigating engine fact the DECISIONS
   entry already exploits: race detection is schedule-independent at
   the join, and adequacy only quantifies the runner's actual
   schedule set (greedy-first + `pick` for call arms,
   generated/Driver.lean `new_drive_core_threads`), so the rule need
   not quantify arbitrary interleavings. Still: nothing in memo
   §3.E's effort shape or §4 prices this obligation; it is the
   single largest un-designed item on the ratified fragment's
   critical path (every C binary expression sits under a T1 unseq).
4. §2.5's α/β operator decision, carried into §4's decision list, is
   moot; the memo needs a revision pass, not a footnote.

### MAJOR-3. `Atomic` is uninstantiable on the trunk's language —
the donor's atomic/mask machinery cannot be grown on B/E, so
D-promotion is parity-required, not an open option.

iris-lean `Atomic a e` requires every primStep successor of `e` to be
irreducible (weak) or a value (strong)
(deps/iris-lean/Iris/Iris/ProgramLogic/Language.lean:248-253, read
this session). On `KDriveExpr`, every mid-program configuration is
`.seq m k` and steps to `k v` / `.seq m' k` — the *rest of the entire
program*, reducible and non-value by construction. Hence no
mid-program KExpr is `Atomic`; the class is satisfiable only at
termination. RefinedC's typing layer consumes `Atomic` instances via
TC resolution at `typed_read_end`/`typed_write_end`'s `E → ∅` mask
dance (`iApply wp_atomic`, RefinedC programs.v:1389; port map
§1.3.3/agenda 10), and the acceptance ladder's spinlock/mpool rungs
need the atomic rules. On the trunk the *capability* is partially
recoverable by bespoke per-round lifting lemmas that open invariants
across one `KStep` inside `wp_lift_step`'s mask window — but that is
a structural divergence CLASS in the very stratum E claims to deliver
in donor shape ("does this let RefinedC's next layer port
literally?" — no), and the `wp_atomic`/`Atomic`-typeclass route never
ports. The memo files this as an open question about D's Expr/State
split (memo §6 bullet 3) and omits it from §3.B/§3.E's risk lists,
where it belongs with a determinate answer: on B/E it is *no by
inspection of the type*. Consequence: E's "whether to LATER promote
… becomes a refactor decision taken with evidence" (memo §3.E) is
wrong on one axis we already have the evidence for — reaching ladder
parity requires the promotion. The recommendation survives, but its
"promotion optional" framing does not; promotion criteria belong in
the charter now.

### MAJOR-4. The probe's exemplars dodge the measured hard class —
a pass would not de-risk the ~55-lemma stratum.

The park's own measurements locate the expensive class precisely:
"an eval ENTRY whose redex cases on symbolic data (guard/conv/case
chains) runs the interpreter's fuel loop away (measured 16–48G OOM
…); kernel evaluation is IMPOSSIBLE here by measurement … —
hypothesis-fed laws are the only route" (v3a §3 finding 1, §6 row 1).
Per the shape study, this class is not a corner: every C condition
elaborates to a truthiness `Ecase` with `nd(True,False)` on
Unspecified, and every binop carries `case (Specified …,Specified …)`
UB chains — "a statement view over Core faces per-construct
*patterns*, not per-construct *constructors*" (shape study §3(v)3).
So the WP-lemma stratum's real unit is the per-TEMPLATE lemma over
symbolic operands, and its hard core is exactly the symbolic
case-chain payload. The probe's P1 is "pure `Eif` on a boolean
value" — the eval payload is trivial; P2 is a load request — no
symbolic eval at all. Both were, in essence, already demonstrated by
the park (cstep_tau/cstep_eval fired cross-program at 0.35-0.6 s,
v3a §1) *at ground discovery*; what P1/P2 add is only the ∀-context
premise (which finding 2 shows is mis-scoped anyway). F3 ("proofs go
through at sane cost — the recommendation stands") is therefore too
generous: the probe can return GO while the stratum's dominant cost
class remains unmeasured at ∀-quantification. The probe needs a
symbolic-payload exemplar (see the probe section below).

---

## MINOR findings

### MINOR-5. "Two-sided characterization" is overstated by one
direction.

What exists: (i) `ksteps_of_runND` — runner ⊆ KSteps endpoints
(proved, ∀-KExpr, production fuel); (ii) soundness "by construction"
— each `KStep` arm is premised on one `app` equation
(park:…/PerStep.lean:104-135). No theorem of the converse inclusion
(KSteps endpoint ⇒ runner membership) exists on the park branch
(searched; only `ksteps_of_*`). For the adequacy direction the memo
needs, (i) is exactly right and sufficient — but the memo's
legitimacy axis explicitly scores "characterization vs one-direction
soundness" (memo governing ruling 2 gloss, §3.B "a genuine two-sided
characterization"), crediting B with a theorem it holds only as a
definitional discipline. State it as: one proved inclusion + premises
grounded in engine observations.

### MINOR-6. Mis-cite conflating the adequacy faces.

Memo §3.B quotes "`CallHarnessAdequate prior tagDefs file fname args
fs spec` … (relsemcore Call.lean …)". The def carrying `prior` is
`CallHarnessAdequateCns` (park:…/RelSem/Threaded.lean:227);
Call.lean's `CallHarnessAdequate` (park :282) takes no `prior` and no
consistency filter. The stray `prior` is the only trace in the memo
of the consistency machinery that MAJOR-1 shows is load-bearing —
i.e. the mis-cite conceals the exhibit's actual strength. Correct the
cite and surface the Cns semantics.

### MINOR-7. The secondary probe is uninformative for the question it
is sold as settling.

`Language.Context` for KExpr continuation-append (memo §4 secondary)
looks provable (graft `done(value v) ↦ k v`, `done(killed) ↦
done(killed)`; the KStep arms are continuation-parametric, and kill
passes through bind). But passing it yields bind at *driver-round
granularity*: Core subterms are not KExprs, so no `K` over KDriveExpr
can ever focus a Core subexpression — the donor's
`wp_bind`/`find_expr_fill` idiom gets no carrier from this either
way. (The Core-side bind story instead rides the monadic-normal-form
grammar fact — shape study §3(iv) — inside the ∀-context stage-α
premise.) Replace with a probe that tests actual consumption (below).

### MINOR-8. The re-landing bill is larger than "re-landing proved
text", and cross-repo.

Beyond PerStep*/PerStepIris/Obs/Peel/Call and CerbStateRA/WP/Step/
Adequacy (~6k lines), the trunk needs: Threaded.lean's faces +
anti-vacuity metatheorem (MAJOR-1.5), the Kit/* `se_*` eval-law
family and round kit that `cstep_eval` payloads consume, the
statement/fixture discipline (CorpusFiles/Statements, PriorCensus
instrument) if M1-class exhibits are to be re-established, and the
audit-slate registrations. All of it re-homes into refined-cerberus
against a semantics pin that does not yet exist (arc-0 open item) and
must expose the generated modules + RelSemCore through Lake. The
memo's "weeks-scale grinding against a known surface" may still be
right, but the surface should be enumerated in the charter, not
gestured at. (Also: PerStep completeness hardcodes `lemDefaultFuel =
999999 + 1` by rfl at :467 — brittle against any engine fuel-budget
change; note for re-landing.)

### MINOR-9. "No thrown-away work on either exit" oversells the
promotion path.

Stage-α lemmas transfer to D (their conclusions translate from
`app (dnmsRoundM …)` equations to CoreStep membership through a thin
dictionary). But every Iris-facing artifact founded on B's `Language`
instance — the wpk_* rule set, the state-interp coupling, and every
`typed_*` judgment defined via that WP — re-proves against D's
instance on promotion; WPs over different languages do not transfer.
E's plan is to grow precisely this stratum large before deciding.
Combined with MAJOR-3 (promotion is parity-required), the discardable
mass at promotion time is a real cost E's effort-shape should carry,
and an argument for promoting *early* (after the probe, before the
stratum is wide) rather than "with evidence" at leisure.

---

## NOTES

### NOTE-10. Verified-as-claimed inventory.

For the record, the memo's checkable load-bearing claims that
*passed* hostile verification: park cones (M1 trio; adequacy stack
trio; `runEffectful` carriers registered separately —
park:…/Audit.lean:359,1014-1023,1357); iris pin identity (34390a01,
three-way); peel anchor rfl-discipline; mainline survival of
`runND_sound`/`HarnessAdequate`/`callND`; the §2.4(vi) admission (no
syntactic-premise stratum anywhere on the park — confirmed: `cstep_*`
premises are ground `find_can_advance (dnmsDiscover …) = some _`
discovery equations, park:…/CStep.lean:130-181); the sequentialise
pass being dead in the Lean pipeline; `maxHeartbeats 2000000` caps
confined to probe instruments (park:…/CStepProbe.lean). The memo's
§5 fact 3 (`Driver.hack` finalize wrinkle) is accurate and its
consequence (a characterization lemma family for result
postconditions) is correctly flagged.

### NOTE-11. Opaque-world hypotheses are part of the "engine-only"
fine print and belong in the charter.

`drive`'s cone consults `CerbGlobal.current_execution_mode` (an
`opaque` with unsafe `implemented_by`, CerbGlobal.lean:79/116-117)
inside `driver2`, and the park's peel handles it by casing *both*
branches of the mode read (park:…/PerStepPeel.lean:426-460,
`driver2Rest_done`). `CerberusFresh.digest` is `@[extern]`. Any
statement about the production entry either cases these or hypothesizes
them (CorpusEnvHyp-style). This is manageable — but the
language-instance charter should own the policy (case-both-branches
in peel anchors; enumerate every statement-level world hypothesis),
because these hypotheses are exactly where "engine-only" statements
silently become "engine-under-assumptions" statements.

### NOTE-12. The postmortem's caution applies to E's headline virtue.

E's strongest selling point is "smallest distance to a first verified
exhibit" (memo §3.E). The exhibit in question is an M1-class harness
adequacy — a *build-ledger* item under the north star's two-ledger
instrument, not a product-ledger native-verification exhibit (which
needs the typing/automation strata that sit on the unbuilt stage-α
stratum in every candidate). The postmortem's paradigm-3 failure was
precisely harness observations promoted to deliverable. The memo does
not confuse the ledgers, but a ratifying operator should read its
schedule argument with that discount: E's time-to-*product* advantage
over a D-first design slice is roughly the trunk re-landing vs the
cfg-split design slice — much smaller than the time-to-*exhibit*
advantage the memo foregrounds.

---

## What the falsification probe SHOULD be

The registered probe (P1 pure-Eif-at-bool, P2 load, both unseq-free
∀-context; kills F1 not-statable / F2 perf / F3 pass) tests
∀-context statability on the easy payload classes of a superseded
fragment. Re-register as follows (one worktree slice, same scale
discipline, kills pre-registered):

- **P1′ (keep, as-is).** Pure `Eif` at a boolean value, ∀-context
  over the sequencing grammar. Cheap sanity anchor; F1/F2 kills
  unchanged.
- **P2′ (fix the context).** The T1 operand-unseq load: an arena
  whose redex region is `let weak (a,b) = unseq(load(τ,x), e₂) in …`
  inside an otherwise arbitrary unseq-free spine. Prove the round
  advances the LEFT arm's load under a standardization premise ("no
  advanceable redex offered to the left of the hole" — stated
  against `get_ctx`'s traversal order), and that the successor arena
  is the same context with that arm advanced. Kill: the
  standardization premise cannot be stated as a syntactic condition
  on `C` (forces offered-list enumeration per shape) — then the
  syntax-facing stratum does not exist *on the ratified fragment*,
  which is the question that matters now.
- **P3 (new — the measured hard class).** One per-template lemma with
  a symbolic eval payload: the truthiness template (`case a of
  Specified k => pure (if not(k = 1) …) | Unspecified _ =>
  nd(True,False)`) at a symbolic operand, ∀-state, hypothesis-fed
  per the P02 route — i.e. the class v3a measured as
  kernel-impossible. Success = a ∀-quantified template lemma at sane
  cost whose instances need no per-program hand-chains. Kill = the
  lemma is only achievable per-instance (the stratum's cost model is
  then per-program, the concrete-artifact disease in new clothes) or
  trips F2's perf tripwire. This, not P1/P2, is the stratum's
  scaling question.
- **F2 (keep).** >10 min or >16G on one lemma kills, chartering
  representation work first. Given that stage-α proofs must induct
  over fueled generated functions (`get_ctx`/`step_ctx` lemFuel
  plumbing) — something the park never did (its ∀-state lemmas kept
  discovery as a hypothesis) — F2 is genuinely live; keep the
  tripwire tight.
- **Replace the secondary probe** (Language.Context
  continuation-append — uninformative, MINOR-7) with a **vertical
  consumption exemplar**: state ONE donor-shaped rule end-to-end on
  the trunk — e.g. the load-template `wp` rule in `typed_val_expr`
  premise shape (ctl-token judgment), proved from P2′/P3-class
  lemmas through a `wpk_seq_*` rule, discharging into the (honestly
  restated, per MAJOR-1) adequacy face at one M1-class fixture. That
  tests the path the ~55-lemma stratum will actually travel:
  syntactic premise → round lemma → Iris rule → engine statement.
- **Add one decidable design check, not a probe**: record in the
  charter that `Atomic` is uninstantiable on the trunk (MAJOR-3),
  with the chosen mitigation (bespoke single-KStep invariant lifting
  in fragment 1; D-promotion before the atomics rung) — so the probe
  outcome cannot be read as licensing the mask-dance stratum on B/E.

---

## Amended recommendation (what UPHOLD is conditional on)

1. **Revise the memo against the eunseq ruling** (fragment 1 = live
   unseq): rewrite §1.2/§2.5/§3.D/§4; delete the α/β decision from
   the operator list; add the unseq region meta-theorem and the
   atomic-call rule to the priced obligations, with their proof
   genus named (multi-round region rule over the round relation;
   fractional-permission separation lineage per DECISIONS).
2. **Restate the adequacy end-state honestly** (MAJOR-1): the trunk's
   proved form is ∀-seed threaded + consistency-filtered +
   world-hypotheses; the production-entry corollary carries
   `runEffectful` (boundary entry, provenance: temporal; candidate
   movers: the ambient bridge with the axiom declared, or upstreaming
   seed-threading into the pinned engine's initial state; `prior`'s
   mover: the registered symbol-census function). Put all of it in
   DECISIONS + the Audit boundary plan *before* re-landing begins.
3. **Declare D-promotion parity-required** (MAJOR-3) with a
   pre-registered promotion trigger (no later than the atomics rung;
   arguably immediately after a GO probe, per MINOR-9's
   discard-mass argument), and take the Expr/State-split design
   conversation to the operator on that schedule, not "with
   evidence" indefinitely.
4. **Re-register the probe** per the section above (P1′/P2′/P3 +
   vertical consumption exemplar + kills).
5. **Correct the record** (MINOR-5/-6): the characterization claim
   and the Cns cite, so the register's summary of the memo does not
   inherit the overstatements.

If the re-registered probe fails P2′ or P3, the recommendation falls
back to the operator conversation the memo itself names: a restricted
context grammar or a D-first design slice — with the trunk's
adequacy spine (the genuinely proved part) surviving either way.

---

*Review discipline note: no runtime probes were run; every finding is
a source cite against pinned/parked trees, independently checkable.
Nothing in the memo file was modified; nothing is committed.*
