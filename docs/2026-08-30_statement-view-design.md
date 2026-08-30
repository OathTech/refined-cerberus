# The statement-view question: two candidate designs

**DRAFT — hostile review pending. Not ratified; nothing here is a
decision.**

Date: 2026-08-30. Provenance: [AGENT: arc-2 design author], under the
[USER 2026-08-29] "Statement-layer derisk plan" ruling (DECISIONS.md):
two candidate designs argued strictly from the measured evidence, then
hostile review (not this author), then a vertical spike with
pre-registered kill criteria. This document is step two.

The question (port map §4 agenda items 2 + 16, informed by the Eunseq
census): RefinedC's typing layer is split
`typed_val_expr`/`typed_stmt`/`typed_place` over Caesium's two-sorted
grammar (`expr`/`stmt`, lang.v:28-86); Core is expression-only. How
does the ported typing layer meet Core?

Evidence base (all claims below cite one of these or donor source;
anything not derivable is marked ASSUMPTION and listed in §8):

- **[STUDY]** `docs/2026-08-30_caesium-core-shape-study.md` — the
  shape-correspondence table + findings.
- **[CENSUS]** `docs/2026-08-30_eunseq-census.md` — the Eunseq
  templates, skeleton invariance, atomic-call fact.
- **[MAP]** `docs/2026-08-29_port-map-draft.md` — judgment inventory
  (§2), interface strata (§1.3), Lithium algorithm (§3), agenda (§4).
- **[RELMEMO]** `docs/2026-08-30_relational-semantics-candidates.md` —
  the WP substrate this layer sits on (hybrid 3.E, itself unratified).
- Donor source: `deps/refinedc/theories/{typing,caesium}` at the
  port-map checkout; key cites re-verified against source this
  session: programs.v:66-99 (`typed_stmt_post_cond`/`typed_stmt`/
  `typed_block`/`typed_val_expr`), lifting.v:1001-1017 (`stmt_wp`),
  lifting.v:1108-1120 (`wps_return`/`wps_goto`),
  lifting.v:1306-1309 (`wps_block`/`wps_block_rec`),
  automation.v:145-247 (`liRStmt`/`liRIntroduceTypedStmt`/`liRExpr`
  dispatch).

Governing constraints (CLAUDE.md, binding): NORTH STAR — RefinedC's
architecture rebuilt natively; TRUST ARCHITECTURE — the cerberus-lean
operational semantics is the only trusted semantics, every obligation
ultimately discharges into the engine, no violence to Core's
semantics; referent discipline — every divergence binned
(a) unnecessary invention / (b) real Cerberus constraint /
(c) inherited pseudo-constraint, forcing facts stated about Cerberus.
Acceptance question for every choice: **"does this let RefinedC's
next layer port literally?"**

---

## 1. The measured ground (numbered for citation below)

Facts only; each is load-bearing somewhere in §3-§7.

- **E1 — statement positions exist, sharply.** Every examined proc
  body decomposes into an `Esseq` spine whose nodes are drawn from a
  closed six-species set: create/store/kill actions;
  `let strong x/_ = Ebound(…)` (exactly one per C full expression);
  truthiness-coercion `Ecase`; `Eif` with pure condition and spine
  branches; `Esave`/`Erun`; `pure(Unit)` fillers. No counterexample in
  12 artifacts. [STUDY §3(i)]
- **E2 — the correspondence is pattern-shaped, not constructor-
  shaped.** One Caesium `Assign`/`Call` ↔ 10-40 Core nodes, dominated
  by inline UB checks (`Specified/Unspecified` cases,
  `catch_exceptional_condition_*`, `PtrValidForDeref`,
  `params_length`/`are_compatible`) that Caesium keeps inside its
  opsem/WP lemmas. And the mapping is segment-to-statement (a C `if`
  costs 2 condition spine nodes + the `Eif`). [STUDY §3(v).3, §3(i)]
- **E3 — control flow is save/run only, near-bijective with the
  donor's block map.** One save per C join point (loop head/exit,
  continue point, C label, return) — the same points RefinedC's
  frontend cuts Caesium blocks at (shared Ail ancestry:
  ail_to_coq.ml consumes `AilS*`; both sides inherit cabs→Ail).
  Two deltas: Core saves are nested with fall-through entry; saves
  carry parameter lists (block-argument style, identity defaults,
  args passed back at `run`). [STUDY §3(ii), §3(v).1]
- **E4 — the bind layer dissolves by grammar.** Every operand of
  `Eaction`/`Ememop`/`Eccall`/`Erun`/`Eif`-cond/`Ecase`-scrutinee is
  a syntactically pure `pexpr` (core.lem:319-343); the redex is
  always at the head of the let-chain; nothing like Caesium's
  `find_expr_fill` is needed. [STUDY §3(iv)]
- **E5 — no place syntax exists.** L-value evaluation is ordinary
  value computation (loads + `PtrValidForDeref` guards +
  `member_shift`/`array_shift` pure ops); Caesium's
  `find_place_ctx`/`IntoPlaceCtx` walk (programs.v:257-285) has no
  syntactic tree to walk. [STUDY §3(iv) corollary, rows 9-10]
- **E6 — locals lifetimes genuinely diverge.** Caesium hoists all
  locals to function scope, allocated by the opsem at call
  (lifting.v:1046 `wp_call`; lang.v:90 `f_local_vars`); Core is
  block-scoped `create`/`kill`, re-created per loop iteration
  (t_binary_search's `k`). Reachable kills occur in-band on the spine
  before `run ret_N`; post-`run` kills are unreachable residue.
  [STUDY row 8, row 6, §3(v).4-5]
- **E7 — fragment 1 is NON-sequentialised Core** ([AGENT 2026-08-30]
  flip, DECISIONS.md, [USER] veto point open): 98/98 Eunseq nodes sit
  inside one C full expression's `Ebound`; none spans a statement;
  the save/run/statement skeleton is token-identical with and without
  the pass. Everything reduces to 4 templates (T1 operand, T2
  assignment, T3 call-argument, T4 kill) + 1 rmw variant; 92% of arms
  read-only+pure; a bare store NEVER occurs as an arm. The proof rule
  is shared-reads/disjoint-writes, whose premise IS the engine's
  join-time race check (`overlapping`, CerbMem.lean:1186 =
  impl_mem.ml:527-532); call-bearing arms are a second ATOMIC rule
  shape (arena replacement, core_reduction.lem:1347-1368).
  [CENSUS §2.1, §2.3, §4, §5, §6]
- **E8 — the donor's statement layer is thin and derived.** `WPs` is
  a definition over `WP` (stmt_wp, lifting.v:1001-1008: quantify over
  the runtime function, tie `Q` to `f_code`, provide the return
  continuation); `typed_stmt s fn ls R Q := ⌜len⌝ -∗ WPs s {{Q,
  post}}` with `typed_stmt_post_cond` returning the locals'
  points-to (programs.v:66-70); `typed_block P b fn ls R Q :=
  wps_block P b Q post` (programs.v:72-74) where `wps_block P b Q Ψ
  := □(P -∗ WPs Goto b {{Q,Ψ}})` and `wps_block_rec` is the Löb rule
  over a `gmap label` of invariants (lifting.v:1306-1315). Statement
  judgments are 5 of the 23 (`typed_stmt`, `typed_block`,
  `typed_switch`, `typed_assert`, + `typed_annot_stmt`); the
  several-hundred-rule type-former instance library hangs off the
  expression/place judgments. [MAP §2.2; donor source re-verified]
- **E9 — the donor's dispatch is a syntactic matcher.** `liRStmt`
  reflects the statement via `W.of_stmt` and lazymatches ~12 W
  constructors to `type_assign`/`type_return`/`type_if`/…, with a
  3-way `Goto` case (precond-hyp / block-hint Löb / plain lookup) and
  a loud terminal `fail "do_stmt: unknown stmt"`; `liRExpr` likewise
  over ~17 W expression heads with `fail "do_expr: unknown expr"`.
  (automation.v:145-247, read this session.) Stop-with-goal, not
  fail-open. [MAP §3.2; donor source]
- **E10 — the WP substrate is configuration-flavored until promoted.**
  [RELMEMO 3.E, recommended, unratified]: the adequacy trunk is the
  proved ndM spine (`runND_sound` against the production runner,
  engine-only `HarnessAdequate` forms); the per-construct WP lemmas
  are stage-α syntactic characterization lemmas over `step_ctx`,
  probed by pre-registered falsifiers F1-F3. Both candidates below
  consume that stratum; neither fixes its risks.
- **E11 — uniformity is high but the corpus is small.** Same C
  construct → same Core template in every occurrence, across 23 small
  files; variance sources systematic. But: no `switch` probe exists,
  no do-while, no statics/varargs; representativeness beyond the
  probe corpus is an ASSUMPTION (§8 A1-A2). [STUDY §3(iii); CENSUS
  §1.2]
- **E12 — annotation carriers don't exist over Core.** Elaborated
  plain-C Core has no AnnotExpr/AnnotStmt analog; block/loop
  invariants survive anyway via the `split_blocks` proof-script
  channel (a `gmap label (iProp Σ)`, observed in the generated
  wrapping_add proof). The annotation divergence CLASS is already
  ratified ([USER] frontend-out-of-scope; DECISIONS targeting call
  3). [MAP §4 item 15; STUDY row 11]

---

## 2. Shared obligations (candidate-independent)

These fall out identically under A and B; they are listed once so the
comparison in §6 is about what actually differs.

1. **The WP substrate.** Both candidates state their per-form WP
   obligations over the [RELMEMO] trunk's syntax-facing lemma
   stratum; both inherit its F1/F2 kill criteria (E10). If stage-α
   lemmas cannot be stated at ∀-context, BOTH candidates die as
   specified — that is a substrate failure, not a discriminator.
2. **The unseq templates + atomic-call rule** (E7). T1-T4 + rmw are
   expression-local (inside `Ebound`), so they integrate below the
   statement question in both candidates: T1 (operand unseq) gets the
   shared-reads/disjoint-writes rule whose side condition mirrors the
   engine's `overlapping` check; T3/T4 call arms get the atomic-call
   rule (callee footprint, atomic w.r.t. siblings per the
   arena-replacement fact); T2's store is always sequenced after the
   join, so assignment's write obligation sits on the spine, not in
   the unseq. The `neg(…)` polarity exclusion at the join
   (core_reduction.lem:214-240 via [CENSUS §6.1]) is part of the T2
   rule's premise accounting. The one-time unseq-rule meta-theorem
   owed by the attachment layer (DECISIONS 2026-08-30) is unchanged
   by this document.
3. **Place machinery** (E5). Neither candidate can port
   `find_place_ctx`/`typed_place` as a syntax walk over l-value
   trees — the trees don't exist. Both need the same replacement:
   the *pure* offset chains (`member_shift`/`array_shift` pexprs)
   ARE syntactic, so a place-context finder over pexpr chains can
   reconstruct the donor's `place_ectx_item` list for the
   member/index cases, while the deref links (load + guard patterns)
   arrive as prior computation steps and enter through
   `FindLoc`-style context search on the location VALUE. Design
   detail is deliberately out of this document's scope (it is the
   other half of item 16); what matters here: it is identical work
   under A and B and does not discriminate.
4. **op_type ↔ ctype mapping** (MAP §4 item 5). Donor rules dispatch
   on `op_type`; Core actions carry ctypes. Both candidates need the
   same classification; fact-finding row already on the agenda.
5. **Annotation channel** (E12): both candidates drop
   `typed_annot_expr`/`typed_annot_stmt` from fragment 1 under the
   ratified divergence class; invariants ride the `split_blocks`
   analog over the save-label map (which exists in both candidates —
   the save/run skeleton is candidate-independent, E3/E7).
6. **Fail-closed automation posture.** Both candidates reproduce the
   donor's stop-with-goal semantics (E9): an unhandled shape leaves
   a legible residual goal naming the Core subterm; no default rule
   absorbs it. (House fail-closed rule; also the donor's own
   behavior.)

---

## 3. CANDIDATE A — the statement-shaped view

### 3.1 Definition strategy

A **fail-closed partial classifier, not a total grammar and not a
semantic object.** Concretely:

- A Lean inductive `SView` of statement-position forms, one
  constructor per measured species (E1) plus the derived forms below.
  Approximate constructor set (names illustrative):
  `SAction` (create/store/kill/rmw at spine level), `SLetE e k`
  (value-binding full-expression node: `let strong x = Ebound(e) in`,
  including the `_`-discard case), `STruthiness v k` (the coercion
  `Ecase` + `End(True,False)` pattern), `SIf v s1 s2`, `SGoto L args`
  (`Erun`), `SReturn` (`Erun ret_N` — recognized by the ret-label
  role), `SSkip` (`pure(Unit)` fillers + unreachable residue tails),
  `SUnclassified (t : CoreExpr)`.
- A total function `classify : CoreExpr → SView` where every shape
  outside the measured patterns lands in `SUnclassified` — total as a
  function, partial as a grammar, loud by construction. This is the
  fail-closed resolution of the brief's either/or: a "total
  classifier over sequentialisable spine shapes" would require
  proving the six-species closure holds for all elaborator output,
  which the evidence cannot support (E11); a fail-closing partial
  match requires only that it holds on the programs we verify, and
  turns the closure claim into a per-program check.
- **The view is dispatch metadata only.** Typing rules are theorems
  about Core terms; `classify` picks which rule the automation
  applies (the donor precedent is exactly this: `W.of_stmt` reflection
  feeding a lazymatch, E9). There is no `to/of` round-trip theorem to
  prove and no trusted boundary: a misclassification cannot produce a
  wrong proof, only a failed or stuck one, because the applied rule's
  statement is over the actual Core term and elaboration re-checks
  the match. This is deliberately weaker than Caesium's `W` (a full
  reflected copy with `to_expr/of_expr` correctness, tactics.v:9,378)
  because Core's grammar purity (E4) already dissolves the
  context-finding job `W` mainly exists for; the residual job is
  dispatch, and dispatch needs no soundness theorem.
- **Grain: node-grain with derived forms only where measured as
  templates.** The multi-node patterns admitted are exactly the
  measured recurring segments: the truthiness coercion (E1 species 3
  + `End` arm, [STUDY] row 2), the assignment tail
  (`neg(store)`-after-unseq-join, [CENSUS] T2), the call chain
  (metadata lookup + arg create/stores + `Eccall` + kill-unseq,
  [STUDY] row 7 / [CENSUS] T3-T4), and the four unseq templates
  (expression layer, E7). Everything else is single-node. Rationale:
  every widening of a pattern beyond one constructor is classifier
  fragility priced against elaborator variance; the evidence
  supports exactly these segments as templates (E11 uniformity) and
  no more. In particular a C `if` is NOT reassembled into one
  synthetic `SIfC` — the 3-node segment (bound; truthiness; `Eif`)
  is typed by three rule firings whose composition equals the
  donor's `type_if` content (see §3.3).

### 3.2 The judgments: how typed_stmt / typed_block / typed_val_expr port

- `typed_val_expr (e : CoreExpr) (T : val → type → iProp) :=
  ∀ Φ, (∀ v ty, v ◁ᵥ ty -∗ T v ty -∗ Φ v) -∗ WP e {{Φ}}` — ports
  **verbatim** (programs.v:96-98); it is the judgment for `Ebound`
  bodies and pexpr evaluation. The value-typed judgments hanging off
  it (`typed_bin_op`, `typed_call`, `typed_if`, `typed_value`, …,
  MAP §2.2) keep their signatures; what changes is which syntactic
  pattern their dispatch fires on (§3.6).
- `typed_stmt (s : CoreExpr) (fn : SaveMap) (R : val → type → iProp)
  (Q : SaveMap) := WPs s {{Q, typed_stmt_post_cond fn R}}` — same
  shape as programs.v:68-69 with two DECLARED deltas: (i) the `ls`
  locals-location list and the post-condition's locals points-to
  clause are dropped (ledger row A-3, §3.5 — forced by E6: Core
  kills locals in-band before the return join; there is nothing left
  to return); (ii) `s` ranges over Core spine segments and the rule
  set includes a binder-passing rule for value-binding spine nodes
  (row A-2, forced by E4/E1 wrinkle: condition results and return
  values are spine-bound). `WPs` itself is re-derived exactly as the
  donor derives it — a definition over `WP` quantifying the ambient
  proc and tying `Q` to the proc's save map, with the
  `run ret_N`-continuation in place of the `Return`-continuation
  (stmt_wp, lifting.v:1001-1008 as the template).
- `typed_block P b fn R Q := wps_block P b Q post` with
  `wps_block P b Q Ψ := □(P -∗ WPs (goto b) {{Q,Ψ}})` and the Löb
  rule `wps_block_rec` over `gmap label iProp` — ports verbatim in
  shape (lifting.v:1306-1315, programs.v:72-74), because of E3: the
  save set IS the block map.

### 3.3 The save/run ↔ block map realization

- **Q = the proc's save map**: a finite map from save labels to
  (parameter list, body). Extracted once per proc by the view;
  extraction is mechanical because saves are syntax nodes.
- **`Erun L(args)` ↔ `Goto L`**: the `wps_goto` analog
  (lifting.v:1112-1119 as template: `Q !! b = Some s → ▷ WPs s' -∗
  WPs (run b args)`) where `s'` is the save body with parameters
  substituted by the `run` arguments. The measured identity-rebinding
  discipline (E3: `w: pointer := w`; args passed back) + the ratified
  calls-are-substitution ruling (DECISIONS 2026-08-29) make this a
  substitution step with no environment residue — the same move,
  smaller scale. The `▷` is honest: `Erun` is a real engine step
  (stage-α characterization lemma per E10). ASSUMPTION A6 records
  that identity-rebinding is measured, not proven of the elaborator;
  the rule as stated does not DEPEND on identity defaults (it
  substitutes whatever args appear), so A6 only affects invariant
  ergonomics, not soundness.
- **Fall-through entry** (E3 delta 1): where a spine segment ends by
  flowing into a following `Esave`, the view presents it as
  `SGoto L (identity args)` — the analog of the donor frontend's
  explicit trailing `Goto` in every block ([STUDY] row 3: Caesium
  blocks have no fall-through either; their frontend inserts the
  Goto; our view inserts it at classification time). The
  corresponding rule obligation is that entering a save body by
  fall-through and by `run` with identity args are the same engine
  configuration — one characterization lemma (row A-6).
- **Return**: `run ret_N(v)` classified as `SReturn`; `wps_return`
  analog (lifting.v:1108-1110 template) hands `v` to the return
  continuation. The save's default-parameter UB (`undef(UB088)` on
  fall-off-end, [STUDY] row 6) is a genuine extra proof obligation at
  the `ret` save — surfaced as the rule for reaching `Esave ret_N`
  by fall-through, which demands proving the function cannot fall
  off the end of a value-returning path (donor has no counterpart;
  their frontend guarantees block chains end in Return; row A-3b).
- **The Goto 3-way** (E9): `type_goto_precond` (hyp search) /
  block-hint Löb via `typed_block` / plain map lookup — ports
  case-for-case; the `compute_map_lookup` over the code marker
  becomes a kernel-legal map-lookup step per the already-flagged
  vm_compute ledger row (MAP §4 item 14a; not new here).

### 3.4 Inline-UB-check content: inside the derived forms' WP obligations

Decision (argued, not assumed): the UB-inflation content (E2) goes
**inside the derived-form WP lemmas**, not surfaced as per-node side
conditions — with the semantic side conditions the donor also has
surfacing in the SAME positions the donor's rules put them.

- Argument from the acceptance question: the donor's rule library
  (e.g. int.v's 31 instances; `type_add_int_int` etc.) presents
  side conditions like overflow bounds computed from the opsem
  (`int_arithop_sidecond`, lifting.v:555 per MAP §1.3). Core spells
  the same checks syntactically (`catch_exceptional_condition_add`
  under a `Specified` case, [STUDY] row 1). If the port's arithmetic
  WP lemma over the Core pattern emits "the mathematical sum is in
  range" as its side condition, the donor's int-rule instances port
  literally on top; if instead each Core node became its own goal,
  every donor instance would need restating against a 10-40× goal
  surface — the next layer would NOT port literally.
- The `Specified/Unspecified` case splits and the truthiness
  `End(True,False)` arms are discharged INSIDE the lemma by the type
  information (`v ◁ᵥ int it` yields a defined value, killing the
  `Unspecified` branch); the WP lemma's statement covers both
  branches (the `End` rule is a conjunction over arms — no branch is
  dropped, no violence to the semantics), and the typed rule prunes
  using ownership. Same pattern for `PtrValidForDeref` (discharged
  from `l ◁ₗ …`/`loc_in_bounds`-analog) and the call-site
  `params_length`/`are_compatible` checks (discharged from the
  function-pointer type's metadata, `function_ptr` analog).
- Checks with NO donor counterpart (the ret-save fall-off default,
  A-3b; `store(τ,x,Unspecified τ)` for uninitialized locals, [STUDY]
  surprise 8) surface as honest new premises on the corresponding
  rules and get ledger rows — they are Cerberus-real UB the donor
  under-models, the same "strictly more honest" posture as the unseq
  rule (DECISIONS 2026-08-30).

### 3.5 The per-iteration locals divergence, honestly

No hoisting, no view-level lifetime surgery — that would be violence
to Core's semantics (create/kill are engine actions with UB
consequences; a hoisted view would validate programs the engine
kills). Instead:

- `create`/`kill` are first-class statement-view forms with
  alloc/free-shaped rules: `create` produces `l ◁ₗ uninit τ` + a
  freeable-analog; `kill` consumes them (donor precedent: `Alloc`
  expr / `Free` stmt, lang.v:36,79; `wps_free` lifting.v:1123).
- Consequence for loop invariants: a loop-local's ownership is
  created and killed INSIDE the loop body's save, so the block
  invariant at `while_N` does not mention it — strictly simpler
  invariants than the donor's (where all locals are owned for the
  whole function and every block invariant carries them via
  `typed_stmt`'s `ls`). The cost is the signature delta already
  declared (typed_stmt drops `ls`; post-cond drops the locals
  clause; `typed_function`'s "locals arrive as uninit" premise
  becomes per-create rules in the body instead of a preamble —
  function.v:59's `fp_atys` argument discipline survives because
  argument SLOTS are created by the caller, [STUDY] row 7).
- The dead residue after `run ret_N` ([STUDY] surprise 4, E6) is
  classified `SSkip`-unreachable; its rule is trivial (the segment
  is dead by the run-step characterization — no obligation
  discharged against it, no obligation skipped: reachability is the
  engine's, not the view's).

### 3.6 The Lithium-analog dispatch

`liRStmt`-analog matches on `classify s` when the goal head is
`typed_stmt s fn R Q` — one dispatch row per `SView` constructor,
structurally isomorphic to automation.v:145-192 (Assign→assignment
derived form; Goto→3-way; Return; If; ExprS→`SLetE`; SkipS→`SSkip`;
the AnnotStmt rows dropped per E12). `liRExpr`-analog matches inside
`typed_val_expr e T` on: Core pexpr heads, the action species
(load/store/rmw/memop), `Eccall` (→ `typed_call`), the four unseq
templates T1-T4 (→ the unseq/atomic rules, E7), `Ebound`
(→ its bind rule, row A-5), `Eif`/`Ecase` on values (→ `typed_if`
/`typed_switch`-analog). Terminal cases fail loudly with the Core
subterm displayed (E9's `fail "do_stmt: unknown stmt"` ported as
policy; §2.6). The matcher runs meta-level (tactic-side, donor-style
reflection); nothing about it enters the kernel or the trust story.

### 3.7 Out-of-view shapes: the fail-closed story

Three layers, all loud:

1. **Ingestion lint**: `viewCheck : proc → List CoreExpr` runs
   `classify` over the whole proc at spec-ingestion and reports every
   `SUnclassified` BEFORE any proof is attempted (fail-noisy,
   up-front; the per-program closure check replacing the unprovable
   universal closure claim, §3.1).
2. **Dispatch**: an `SUnclassified` reached mid-proof leaves the
   stop-with-goal residual naming the subterm (E9 semantics).
3. **No semantic gap**: because rules are theorems over Core terms
   and WP is over the engine, an unclassified shape only lacks
   AUTOMATION — manual WP/characterization-lemma reasoning remains
   available for it, and a recurring unclassified shape is a
   measured trigger for extending the view (a new dated evidence doc
   + ledger row, never a silent widening).

### 3.8 Ledger cost (binned per the referent discipline)

Derived count: **9 rows, all bin (b)** — every forcing fact is about
Cerberus, stated from the evidence docs:

| row | divergence | forcing fact (Cerberus) |
|---|---|---|
| A-1 | dispatch via classifier over patterns, not a reflected grammar copy (`W` shrinks to a matcher) | statement positions are patterns, not constructors (E2); bind layer dissolved by grammar purity (E4) |
| A-2 | `typed_stmt` gains the binder-passing rule for value-binding spine nodes | grammar purity forces spine pre-evaluation of conditions/results (E4, E1) |
| A-3 | `typed_stmt` drops `ls`; post-cond drops locals clause; create/kill are first-class rules; (A-3b) ret-save fall-off premise | block-scoped in-band create/kill, per-iteration re-creation, in-band kills before the return join, UB088 default (E6, [STUDY] row 6) |
| A-4 | truthiness-coercion derived form incl. `End(True,False)` | elaborator inserts the case+nd on every condition ([STUDY] row 2, surprise 6) |
| A-5 | `Ebound` rule (no Caesium analog) | full-expression bounding is Core syntax ([STUDY] §3(iv) caveat b) |
| A-6 | fall-through save entry = inserted identity-Goto | saves are nested with fall-through (E3) |
| A-7 | `seq_rmw` rule (no donor counterpart) | elaborator emits a dedicated rmw action for `i++` ([STUDY] surprise 7) |
| A-8 | uninit locals: explicit `store(Unspecified)` handled by the uninit type rule | elaborator stores indeterminate values; Caesium leaves poison bytes with no statement ([STUDY] surprise 8) |
| A-9 | unseq T1-T4 + atomic-call rules | already registered (DECISIONS 2026-08-30; E7) — listed for completeness, not new cost |

Everything else in the statement stratum — `typed_stmt`'s WPs shape,
`typed_block`/`wps_block(_rec)`, `wps_goto`/`wps_return`, the Goto
3-way, `typed_switch`/`typed_assert` (switch modulo A1/A2),
`introduce_typed_stmt`/`typed_function`, the dispatch table — ports
shape-literally with donor file:line cites.

### 3.9 Automation cost and gauges

- **Automation**: the classifier (≈6 node species + ≈7 template
  patterns) is new meta-code with no donor counterpart — the one
  genuinely novel automation artifact; the dispatch table, rule
  registration, and committed-choice walk port per MAP §3. Template
  matching is wider than constructor matching: fragility risk if the
  elaborator varies (mitigated by the lint + E11 uniformity;
  monitored by the spike).
- **Transfer ladder ("their proofs transfer")**: preserved at
  statement grain. Donor proof-term traces (MAP §3.8) contain
  `liRStmt`-species steps that map 1:1 to view-dispatch steps; the
  replay lane can align traces modulo the 9 declared rows. Rule
  citations stay rule-grade (this lemma = programs.v:NNNN).
- **Product gauge (native exhibit)**: a never-seen program either
  classifies fully (lint) and runs the donor-shaped pipeline, or
  fails loudly at ingestion with a named shape — a measurable,
  honest gauge. Coverage risk exists (E11) but is surfaced, not
  absorbed.

### 3.10 Spike design (Candidate A) — pre-registered kill criteria

**Vertical slice: `wrapping_add`, end-to-end.** Chosen because both
sides exist and are measured: the Core twin (`t_wrapping_add`,
[STUDY]/[CENSUS]) and the donor's compiled proof term
(MAP §3.8 probe). Secondary file: `p02_if` (adds truthiness, `Eif`,
early return, save/run). Scope: (S1) implement `classify` for the
six species + templates; lint both files. (S2) state + prove the
derived-form WP lemmas needed by these two files over the [RELMEMO]
stage-α substrate (load, store, the T1 unseq template, arithmetic
pattern, truthiness, `Eif`, run/save, create/kill, `Ebound`).
(S3) discharge `typed_function` for wrapping_add by donor-shaped
rule applications (manual liRStep-analog is acceptable; the engine
need not be the full interpreter). (S4) compare the resulting side
conditions and rule sequence against the donor's wrapping_add trace.

Kill criteria (registered NOW; any firing = stop-and-report to the
operator, not workaround):

- **KA1 (view wrong)**: any spine node in the two spike files lands
  in `SUnclassified` after the declared species+templates are
  implemented — the measured closure fails on its own corpus.
- **KA2 (substrate mismatch)**: a derived-form WP lemma cannot be
  STATED over ∀-configurations / needs per-program premises
  (inherits [RELMEMO] F1).
- **KA3 (literalness false)**: discharging S3 requires changing any
  donor judgment SIGNATURE beyond rows A-1..A-9 — the candidate's
  central claim fails.
- **KA4 (template content misplaced)**: the S4 side-condition surface
  differs from the donor's beyond the declared rows (e.g. raw
  `Specified`-case goals leak through that `v ◁ᵥ int it` should have
  killed).
- **KA5 (grind tripwire)**: any single lemma > ~10 min or > 16G
  (house rule; [RELMEMO] F2 analog).

---

## 4. CANDIDATE B — the expression-grain port

### 4.1 Definition strategy

Follow Core's grammar as-is. No view, no classifier: the typing layer
is defined over Core constructors directly.

- `typed_expr (e : CoreExpr) (T : val → type → iProp)` — one
  judgment, the literal port of `typed_val_expr` (programs.v:96),
  now covering ALL of Core including former statement positions;
  "statement" = `typed_expr` at unit/discarded value.
- `typed_stmt` dissolves into `typed_expr` + one new judgment for
  control: `typed_body (e : CoreExpr) (Q : SaveMap) (R : …)` — the
  save/run judgment carrying the label map and return continuation
  (the `WPs` content, lifting.v:1001-1008, restated over Core spine
  positions). Note Q survives: the save/run skeleton is a fact about
  Core (E3, E7), not about Candidate A — B also has a block map,
  `wps_goto`/`wps_block_rec` analogs, and the `split_blocks`
  invariant channel.
- The donor's statement rules are transported **content-wise, not
  shape-wise**: e.g. `type_assign`'s content (evaluate the RHS,
  `typed_write`) becomes the rule for the
  `Esseq(let weak _ = neg(store(τ,lv,rv)), rest)` position;
  `type_if`'s content splits across the rules for the bound node,
  the truthiness `Ecase`, and `Eif`; `type_return`'s content becomes
  the `Erun ret_N` rule. Citations degrade to "content from
  programs.v:1171 (type_assign), restructured" — content-grade, not
  rule-grade.

### 4.2 The same details, at expression grain

- **Inline-UB-check content**: B faces the identical placement
  question and the evidence forces the SAME answer one level down.
  At raw grain, every Core node (each `load`, each `Specified` case,
  each `catch_exceptional_condition_*`, each `PtrValidForDeref`)
  is a rule firing — a 10-40× goal surface per C statement (E2)
  that no donor instance matches. So honest B still needs
  template-scale lemmas for the pure UB patterns (a symbolic
  evaluator for pexprs emitting donor-grade side conditions) —
  i.e. **B does not escape pattern-shaped correspondence; it
  relocates it into the pure-expression layer and loses the donor
  shape it was buying**. This is the load-bearing observation
  against B, and it is measured (E2 is about expression content,
  not statements).
- **save/run ↔ blocks**: identical mechanics to §3.3 (the facts are
  candidate-independent); only the judgment they attach to differs
  (`typed_body` instead of `typed_stmt`), and `typed_block`'s Löb
  shape must be restated against it.
- **Per-iteration locals**: identical honest treatment (§3.5) —
  create/kill rules; E6's forcing facts don't care about the
  candidate. The `ls`-dropping delta becomes moot only because the
  whole `typed_stmt` signature is already gone.
- **Unseq templates + atomic call**: identical (§2.2); at raw grain
  the T1-T4 patterns are again multi-node — so B carries pattern
  matching for exactly the census templates anyway, under another
  name.
- **Dispatch (liR-analog)**: matches raw Core constructor heads —
  `Esseq | Ewseq | Elet | Epure | Ebound | Eaction(create/store/
  load/kill/rmw) | Ememop | Eccall | Eunseq | Erun | Esave | Eif |
  Ecase | End` — the simplest possible matcher (a genuine advantage:
  zero classifier fragility, robust to elaborator variance by
  construction), plus the pexpr symbolic-evaluation trigger, plus —
  per the previous point — the template patterns it could not
  actually avoid.

### 4.3 Donor citation granularity and the acceptance ladder

- The PORT LEDGER's row discipline (rule cites donor file:line)
  degrades for the whole statement stratum and the arithmetic rule
  library: rows cite content mappings, and "does this rule match the
  donor's" stops being checkable by signature comparison — audit
  cost lands on every future ledger adjudication.
- "Their proofs transfer" weakens to content transfer: the donor
  trace's `liRStmt` steps and typed_bin_op-instance steps
  (`type_add_int_int_inst` etc., MAP §3.8) have no 1:1 counterpart;
  the replay lane must align trace SEGMENTS to step sequences —
  the build ledger's oracle role gets coarser exactly where the
  port is most novel.
- The instance library: the several-hundred `[instance]` rules hang
  off expression judgments (E8), and their typed_bin_op/typed_un_op
  attachment points assume operator-shaped syntax Core does not have
  (arith is pure-pexpr patterns, E2/E4) — so under B they are
  re-derived as pexpr-evaluation lemmas rather than instances of a
  ported judgment. Content preserved; shape, citations, and the
  registration discipline (MAP §3.4) all re-designed.

### 4.4 Ledger cost

Rows A-2..A-9 all persist (they are semantic facts, not view
artifacts). Add shape rows: `typed_stmt`→`typed_expr`+`typed_body`
collapse; `typed_block`/`typed_switch`/`typed_assert` restated;
`introduce_typed_stmt`/`typed_function` entry reshaped; the ~8
statement rules (`type_assign/return/if/switch/assert/goto/exprs/
skips`) transported content-wise; `liRStmt` dispatch replaced;
`typed_bin_op`/`typed_un_op` + their instance files re-attached to
pexpr patterns. Derived count: **8 semantic rows + ~13 shape rows ≈
21 rows.** Binning is the crux: each shape row claims forcing fact
"Core is expression-only" — a real Cerberus fact, but bin (b)
requires the fact to FORCE the divergence, and Candidate A is a
constructive proof that it does not (the statement view exists and is
measured near-bijective, E1/E3). Unless the spike kills A, the shape
rows bin as **(a) unnecessary invention**, which the referent
discipline instructs us to resolve by adopting theirs.

### 4.5 Automation cost and gauges

- Automation: simplest matcher; but the statement-stratum automation
  design (goto/invariant placement, block splitting, return
  handling, rule registration for pexpr evaluation) is re-designed
  without a donor template — new design surface, which the north
  star explicitly steers away from ("reuse their design beats") and
  which draws adversarial-review load with no donor answer key.
- Product gauge: no ingestion lint is needed (no classifier), but
  the coverage question is identical one level down — a never-seen
  program can still present a Core shape with no rule; B surfaces it
  later (mid-proof stuck goal) rather than earlier (lint). Slower
  parity is the main gauge risk: more novel design between here and
  the first exhibits.

### 4.6 Spike design (Candidate B) — pre-registered kill criteria

Same vertical slice (`wrapping_add` + `p02_if`), same substrate:
(S1') state `typed_expr`/`typed_body` and the raw-grain rule set for
the two files' constructors + the pexpr evaluation lemmas;
(S2') discharge wrapping_add's `typed_function` analog;
(S3') produce the content-map table: donor trace step → our step
sequence, for the full donor wrapping_add trace.

Kill criteria:

- **KB1 (control collapse fails)**: `typed_body` cannot state the
  goto/block-invariant (Löb) rule against the save map, or the
  `split_blocks` invariant channel cannot attach — the collapsed
  judgment is structurally wrong.
- **KB2 (damage escapes the stratum)**: more than 3 expression-layer
  donor judgments (beyond the declared typed_bin_op/typed_un_op
  re-attachment) require signature changes — B's premise that
  divergence is confined to the statement stratum fails.
- **KB3 (transfer map fails)**: no total content map from the donor
  wrapping_add trace to our step sequence exists (some donor step
  has no counterpart content) — the acceptance ladder's meaning is
  lost, not just coarsened.
- **KB4 (goal-surface blowup)**: the S2' proof requires manually
  visiting > ~5× the donor trace's step count for equivalent content
  — the E2 inflation has landed on the user, and automation-side
  compression (= reinventing A's templates) would be needed anyway.
- **KB5 (grind tripwire)**: as KA5.

---

## 5. Head-to-head summary (derived from §3-§4)

| dimension | A (statement view) | B (expression grain) |
|---|---|---|
| typed_stmt/typed_block/typed_val_expr | shape-literal modulo 9 declared rows | typed_val_expr literal; statement stratum reshaped |
| ledger rows | ≈9, all bin (b) | ≈21; ~13 bin (a)-unless-A-dead |
| donor citation grade | rule-grade | content-grade in statement + arith strata |
| dispatch matches on | view constructors (classifier over measured patterns) | raw Core constructors + pexpr evaluator + (unavoidably) the same templates |
| novel artifact | the classifier (dispatch-only, untrusted) | statement-stratum + arith-registration design without donor template |
| coverage failure mode | loud at ingestion (lint) | loud mid-proof (stuck goal) |
| transfer ladder | trace-alignable at statement grain | segment-level content alignment only |
| trust architecture | identical: rules over Core terms, WP over engine, adequacy via trunk | identical |
| semantics violence | none (view is metadata; create/kill/nd/UB all first-class) | none |
| E2 (UB inflation) handling | template WP lemmas, donor-shaped sidecond surface | same lemmas needed, non-donor-shaped attachment |

---

## 6. RECOMMENDATION

**Candidate A — the statement-shaped view, node-grain variant with
the declared template set, fail-closed classifier.** [AGENT], for
the operator and the hostile reviewer to attack.

Anchored in the acceptance question: the "next layer" above this
choice is precisely programs.v's judgment set, function.v, the
several-hundred-rule type-former instance library, and the
automation dispatch (E8, MAP §2). Under A, that layer ports
shape-literally except for nine declared, evidence-forced rows;
under B, the statement stratum and the arithmetic attachment points
are re-designed and every affected row's donor cite degrades to a
content mapping. The measured facts say the price of A is bounded
and known (E1's closed species set, E3's near-bijection, E7's
template closure with skeleton invariance), while B's apparent
simplicity is partially illusory: the pattern-shaped correspondence
it avoids at statement level reappears inside expressions (E2, E4 —
the UB-inflation templates and unseq templates must be matched by
ANY design that wants donor-scale side conditions), so B pays the
template cost anyway and forfeits the literalness it was meant to
buy. **That is the deciding argument: the pattern-matching cost is
candidate-invariant; only A converts it into donor shape.**

Anchored in the north star and trust architecture: A does no
violence to Core — the view is untrusted dispatch metadata; every
rule is a theorem about the actual Core term; `End` branches,
`neg` polarity, create/kill lifetimes, and Cerberus-only UB (UB088,
Unspecified stores, unseq races) are first-class obligations, some
strictly more honest than the donor's own model; and every
obligation discharges through the [RELMEMO] trunk into engine-only
statements identically under both candidates — the trust story does
not discriminate, so the referent discipline does, and it says
adopt theirs (bin (a) resolution of B's shape rows).

Process note: this recommendation deliberately does NOT depend on
the unratified [RELMEMO] hybrid being chosen — any substrate that
delivers syntax-facing per-construct WP lemmas (RELMEMO §1.2 item 2)
supports either candidate; substrate failure (F1/F2) kills both
equally (§2.1).

### What evidence would flip it

1. **KA1 or KA2 firing in the spike** — the classifier is not total
   on its own measured corpus, or the derived-form lemmas cannot be
   stated at ∀-configuration: the view as specified does not exist;
   B (or a restricted-fragment conversation) takes over.
2. **Corpus-widening breaks closure** (A1/A2): probing `switch`,
   nested/irregular control, statics, or the frozen 15-program
   corpus produces statement-position shapes outside the species set
   at material frequency — the classifier stops being a bounded
   artifact and B's constructor robustness starts paying for itself.
3. **The locals divergence escapes its rows**: if spike invariants
   for loops with loop-locals cannot be expressed without
   create/kill state leaking into `typed_block`'s shape (breaking
   the `split_blocks`-analog port), row A-3 was underpriced and the
   statement stratum is not as literal as claimed.
4. **KB-side surprise**: if B's spike (run second, only if A's
   fails or the reviewer demands both) shows the content-map is
   total AND the goal surface stays within ~2× donor trace length
   without template lemmas, the deciding argument (E2
   candidate-invariance) is empirically wrong and must be retracted.
5. **Elaborator instability**: any pinned-engine update changing the
   measured templates (E11 uniformity) — the view's maintenance cost
   model would need re-pricing against B's.

---

## 7. What this document does NOT decide

Per the containment rule (attachment-layer scope is decided in
operator conversation): the [RELMEMO] substrate choice; the place
machinery design (§2.3 — the other half of item 16, needs its own
evidence-driven pass); the `typed_switch` port (blocked on A2's
probe); the [USER] veto point on the E7 sequentialisation flip; and
the spike's dispatch itself (this document only registers its design
and kill criteria).

---

## 8. Assumption register

Everything below is used above but NOT derivable from the evidence
docs or donor source; each is marked where used.

- **A1 — corpus representativeness.** All shape/census claims rest
  on 23 small files (12 study + 11 census probes). Unmeasured:
  `switch`, do-while, nested loops beyond binary_search, statics,
  globals initialization order, string/compound literals, varargs,
  VLAs. Used in: §3.1 (partial-classifier argument), §6 flip 2.
- **A2 — switch elaboration.** `typed_switch`'s Core target
  (presumably `Ecase` + save cluster) was never probed; its literal
  portability is assumed by analogy with `Eif`. Used in: §3.8, §7.
- **A3 — classifier implementability.** That a meta-level pattern
  matcher over Core terms (incl. the ≈7 multi-node templates) is
  buildable in Lean tactic code at acceptable cost is assumed from
  general Lean metaprogramming capability, not measured. Used in:
  §3.6, §3.9.
- **A4 — substrate delivery.** The stage-α characterization lemma
  stratum ([RELMEMO], unratified, probe pending) will exist in
  ∀-configuration form. Both candidates assume it; kill criteria
  inherited (KA2). Used in: §2.1, §3.10.
- **A5 — instance-library independence.** The claim that the
  type-former instance library depends on the statement stratum only
  through the ≤5 statement judgments is derived from MAP §2.1-2.2's
  file inventory, not verified instance-by-instance. A mechanical
  sweep (which judgments each `[instance]` targets) is cheap and
  should precede ratification. Used in: E8, §4.3, §6.
- **A6 — identity-rebinding universality.** Save parameters were
  identity-rebinding in every probe; not proven of the elaborator.
  The goto rule does not depend on it (it substitutes actual args);
  invariant ergonomics do. Used in: §3.3.
- **A7 — kills-before-return universality.** Reachable kills
  preceded `run ret_N` on every measured path; not proven for all
  elaboration paths (e.g. `return` from deeply nested scopes with
  multiple live locals was not specifically probed). Row A-3's
  post-cond deletion depends on it; if violated, the post-cond
  needs a residual-ownership clause instead. Used in: §3.2, §3.5.
- **A8 — proc entry triviality.** That Caesium's
  `f_init`/`introduce_typed_stmt` entry (function.v:5-8) maps to
  "enter the proc body expression" with no analog of the
  code-map-substitution step beyond §3.3's save-map extraction.
  Used in: §3.8.
- **A9 — spike sufficiency.** That `wrapping_add` + `p02_if`
  exercise enough of the species set to make KA1-KA4 meaningful
  (they cover 5 of 6 species and 2 of 4 templates; T3/T4 call
  templates appear only via p06/u07-class probes — the hostile
  reviewer may demand a third spike file with a call; registered
  here as a known gap in the spike, not silently absorbed).
  Used in: §3.10, §4.6.

— end of DRAFT —
