# Fresh-eyes review: the port map draft (2026-08-29)

Reviewer: fresh-eyes Fable-class, PL-professor brief — did not author the
document; findings, not grades. Document under review:
`docs/2026-08-29_port-map-draft.md` (653 lines). Reviewed FULLY (not a
delta pass) against `deps/refinedc` at `25f706d417df...` (confirmed via
`git rev-parse HEAD`), with executable probes against the repo-local
built donor (`.refinedc-ws`, per the toolchain setup record). All
file:line cites below re-derived from source during this review, not
copied from the draft. Probe transcripts labeled as such; derived
tallies labeled as derived.

## Verdict

**SOUND CORE — REVISE BEFORE USING AS THE LEDGER FOUNDATION.**

The load-bearing structural claims are right: the dependency inversion
is real and correctly evidenced; the 23-judgment inventory is genuinely
exhaustive over `typing/programs.v` (independently re-enumerated); the
judgment signature transcriptions are accurate; the Lithium
architectural picture (goal grammar, 19-sub-tactic `liStep`,
committed-choice discipline, shelving, evar telescope, hooks) matches
the source closely; the stmt_wp/label-map, mem_cast,
alloc-failure-as-divergence, UIP, and adequacy claims all verify. The
examples survey names real files.

Two claims the ledger would inherit as errors must be fixed: (1) the
§1.3 "exhaustive, mechanical" interface list has *systematic* blind-spot
classes (record projections, silently-resolved typeclass instances,
Ltac-level and hint-database consumption) that would surface later as
mysterious port failures; (2) the §3.2–3.3 determinism story draws the
walk/solver boundary in the wrong place — the walk is **not**
solver-free, which is exactly the fact a replay-style validation harness
needs. The agenda is missing at least two first-order questions.

Replay-lane feasibility (dimension 4): **POSITIVE**, but on different
evidence than the note offers — see §D4 below and the probe transcript.

Counts: **4 MAJOR**, **8 MINOR**, **4 NOTE**.

---

## MAJOR findings

### MAJOR-1. The §1.3 interface list is not "exhaustive" — four systematic blind-spot classes

The list's method (top-level declaration names ∩ typing/ word tokens)
misses whole *kinds* of interface surface, not just stragglers. Each
class verified by grep against `theories/typing/*.v`:

(a) **Record projections.** The scan catches record *names*
(`layout:5`, `int_type:7`, `function:90`, `state:99`) but not their
fields, which typing/ uses pervasively:
`ly_size` in **10** typing files, `sl_members` in 4, `f_args`/
`f_local_vars` in 3, `it_signed` in 2, plus `f_code`, `f_init`,
`st_heap`, `st_fntbl`, `ul_members` (grep -lw counts, derived). None
appear in §1.3 or §1.4. An attachment layer built to the 247-name list
would lack the projections the typing layer's statements are written in.

(b) **Data constructors beyond §1.4's expr/stmt list.** `MByte`,
`ProvAlloc`, `ProvFnPtr` are each used in typing files (grep -lw = 1
each); §1.4 covers only expr/stmt/op_type/order constructors.
Additionally, `typing/programs.v` itself (not just automation) pattern-
matches **W-module constructors**: `find_place_ctx` (programs.v:257) is
a `Fixpoint` over `W.expr` matching `W.Deref`/`W.GetMember`/
`W.GetMemberUnion`/`W.AnnotExpr`/`W.BinOp`/`W.UnOp` (programs.v:257-276)
— §1.3's tactics.v row lists only `expr/to_expr/ectx_item/stmt/to_stmt/
subst_stmt/to_stmt_subst`.

(c) **Silently-resolved typeclass instances.** Typing proofs depend on
caesium instances that never appear as word tokens:
- `Atomic` instances (lifting.v:39-50): consumed at programs.v:1389
  (`iApply wp_atomic`) via TC resolution — the word "Atomic" occurs
  **zero** times in typing/*.v.
- `Persistent`/`Timeless`/`Fractional` instances on the assertion layer
  (ghost_state.v:65-128; `Fractional` machinery used in typing/type.v,
  4 hits) — required for `iDestruct`/persistence moves to typecheck.
These are attachment-layer proof obligations as real as the ~55 wp
lemmas, and they are invisible to the method.

(d) **Ltac- and hint-database-level consumption.**
- `W.of_expr`/`W.of_stmt` (Ltac reflection, used at
  typing/automation.v:159,226) — Ltac, so no declaration-name hit.
- The `bitfield_rewrite` rewrite HintDb (caesium/bitfield.v:260-282),
  fed to Lithium's `normalize_hook` = `autorewrite` path.
- `LiEntails` Hint Extern for `normalize_bitfield` registered **in
  caesium** (bitfield.v:300) but fired during typing's automation.
- `CanSolve`-guarded instances (bitfield.v:341-357) and the
  `CaesiumConfigEnforceAlignment` Hint Extern (config/config.v:25).

Impact: the §1.3 headline "This is the exact surface our Core+Iris
attachment layer must supply" is false as stated. Fix: keep the list,
demote its claim to "the named-identifier stratum," and add the four
classes above as enumerated sections (a projection/constructor sweep is
mechanical; the instance/Ltac strata need a targeted pass).

### MAJOR-2. The determinism boundary is misdrawn: the walk is not solver-free

§3.3 claims side conditions "are not solved during the walk beyond a
cheap `done` fast path"; §3.2 presents step determinism as structural.
Both understate the in-walk solver surface:

- **`liCase` pruning runs the full solver mid-walk.** The pruning
  quoted in §3.2(3) ends in `try by [exfalso; can_solve]`
  (interpreter.v:1120), and RefinedC sets `can_solve_hook ::=
  solve_goal` (typing/automation.v:45) — i.e. the complete
  `normalize_and_simpl_goal`/`refined_solver lia` pipeline
  (solvers.v:235-242) executes **during** the walk, and whether a
  branch exists in the residual proof depends on its strength.
- **`liSideCond` does more than `done` in-walk**: under the `∃ₗ`
  telescope it runs `normalize_hook` for progress, `liExInst`
  (unification), and `tac_simpl_and_unsafe_envs` via `SimplAndUnsafe`
  TC search (interpreter.v:458-478) — including *provability-losing*
  simplification, in-walk.
- **`li_tactic`/`LiEntails` goals run arbitrary registered Ltac
  mid-walk** (e.g. `li_vm_compute` — definitions.v:311-325;
  `normalize_bitfield` — bitfield.v:300; `compute_map_lookup` in the
  `Goto` path, typing/automation.v:170-176 +
  automation/proof_state.v:29), with results flowing into subsequent
  goals.

Consequence for the ledger and the replay lane: "same residual side
conditions" is not well-defined relative to the note's model — the
residual set is a function of the in-walk solver/hook surface, not of
the grammar walk alone. The note must name these as the actual
nondeterminism/heuristic boundaries. (The §3.2 claims that *are* right:
head-connective disjointness, one-lemma-per-step, committed TC choice,
`once`-committed FindInContext — all verified at
interpreter.v:1177-1201, 195-211, 577-592.)

### MAJOR-3. Missing agenda question: what plays the annotation carrier over Core?

RefinedC's `typed_annot_expr`/`typed_annot_stmt` rules (programs.v:41,
46) fire on `AnnotExpr`/`AnnotStmt` **syntax nodes** that the frontend
plants in the program (notation.v:106-109), carrying the payloads in
`annotations.v` (share, stop, learn, lock, reduce, …). With the
frontend out of scope and Core produced by Cerberus elaboration of
plain C, nothing plants these nodes. Note the split: block/loop
*invariants* arrive via the `split_blocks` proof-script argument (a
`gmap label (iProp Σ)` — observed directly in the generated
wrapping_add proof), so they survive; but the in-program hint channel
(sharing, copy-to-uninit, lock annotations, `annot_reduce_int` at
int.v:386 — which is also a `li_vm_compute` carrier, cf. MINOR-6) has
**no Core story**, and several type formers' rules key on it. The
14-item agenda never asks what plays this channel (Core/Ail
annotations? a side table keyed by location? magic calls?). This is a
first-order attachment-layer question; its absence means the operator
conversation the agenda exists to serve would not decide it.

### MAJOR-4. "typing is ported as-is" glosses typing's hard dependency on Caesium's reflected syntax; no agenda row covers syntax-directed dispatch

§1.1's port mapping ("caesium is the layer we replace; lithium and
typing are ported as-is") is contradicted in the small by typing's own
text: the place machinery (`find_place_ctx`, programs.v:257;
`IntoPlaceCtx`, programs.v:278) is defined **over `W.expr`**, and the
automation's statement/expression dispatch (`liRStmt`/`liRExpr`,
automation.v:145-247) matches on W constructors after `W.of_stmt/
of_expr` reflection. Porting typing "as-is" therefore requires a
Core-side analog of module W (reflected syntax + context finders +
`to_expr/of_expr` correctness) — which is attachment-layer design work
over *Core's* constructor set, not a literal port. §1.3's stratum (iv)
gestures at this, but: (i) the layer-map sentence should carry the
caveat, and (ii) the agenda has **no question** about syntax-directed
bind/dispatch over Core (what plays `W`, `find_expr_fill`,
`find_place_ctx` when the syntax is Core's — including whether Core's
already-sequenced form makes the bind layer dissolve). Item 2 covers
labels/statements only.

---

## MINOR findings

### MINOR-1. The actual step is `liEnsureInvariant; …; liSimpl` — both omitted

`liRStep` (automation.v:257-268) is
`liEnsureInvariant; try liRIntroduceLetInGoal; first [...]; liSimpl` —
the note documents the `first [...]` core and `liRIntroduceLetInGoal`
but never mentions `liEnsureInvariant` (mandatory before stepping — the
donor's own Lithium tutorial calls it explicitly,
tutorial/proofs/lithium/lithium_tutorial.v:30) or the trailing
`liSimpl`. A Lean reimplementation scoped from §3.7 would omit the
invariant-maintenance and per-step simplification phases; a replay
harness would mis-align steps.

### MINOR-2. §3.6's "proof terms are linear chains of `tac_apply_i2p` rule nodes" is an oversimplification (probe)

Probe (transcript): recompiled the generated wrapping_add typing proof
against `.refinedc-ws/_build` with a trailing `Print` (probe file in
/tmp; compile time 1.4 s). The printed term contains **13**
`tac_apply_i2p` nodes but ~30 distinct `tac_*` species (top of the
sorted count: `14 tac_ex_evar, 13 tac_sep_pure, 13 tac_apply_i2p,
12 tac_do_intro, 10 tac_li_apply, 9 tac_find_hyp,
8 tac_find_in_context, …`), with the committed rule choices visible as
instance constants (`find_in_context_type_loc_id_inst ×12,
type_read_copy_inst, type_place_id_inst, copy_as_id_inst,
type_add_int_int_inst, macro_wrapping_add_inst, uninit_mono_inst,
simple_subsume_val_to_subsume_inst`). So: not a chain of
`tac_apply_i2p` — a chain of `tac_*` nodes of which `tac_apply_i2p`
marks the rule applications. This correction is *good news* (see §D4)
but the ledger should carry the accurate statement.

### MINOR-3. Interface scope vs the acceptance ladder: examples consume caesium beyond typing/

The ratified gauge is "their proofs transfer"
(rules-of-engagement §7), but §1.3 is scoped to typing/'s consumption.
The generated example proofs import caesium surface typing/ never
touches — e.g. `From caesium Require Import builtins_specs` in
`generated_proof_wrapping_add.v`, with spec text using
`Z_least_significant_one` (generated_spec.v); typing/*.v references
builtins_specs **zero** times. The attachment-layer obligation set for
the ladder is therefore a superset of §1.3 even after MAJOR-1 is fixed.
The doc should state which sections' surface is typing-scoped vs
ladder-scoped.

### MINOR-4. §1.1 undersells what caesium takes from lithium

"only … `base` utilities and the SimplifyHyp/SimplifyGoal classes" —
caesium/bitfield.v (`From lithium Require Import simpl_classes
definitions`) also consumes `li_tactic`, registers a `LiEntails` Hint
Extern (bitfield.v:300), a `NormalizeBitfield` extern (:316), and
`CanSolve`-guarded instances (:341-357). Matters because it is the
one existing example of a *semantics-layer* package feeding the
Lithium hook surface — the exact pattern the attachment layer will use.

### MINOR-5. Derived tallies and file sizes: several wrong

Spot-audit of the labeled-derived numbers (all re-counted):
`automation/` is **525** lines, not 877; `annotations.v` **27**, not
39; `exist.v` **111**, not "~60"; `axioms.v` **11**, not 8; int.v
`[instance]` count **31**, not 32 (own.v 39 ✓, array.v 32 ✓);
hooks.v has **17** `Ltac *hook` declarations in **68** lines (doc:
"~14", ":1-62"). Also internal inconsistency: the judgment→class hook
is cited as ":628-651" in §2.1 but ":622-645" in §2.2/§3.4 — actual is
622-645 (`Ltac generate_i2p_instance_to_tc_hook` at programs.v:622).
Trivial off-by-ones (fine, noting only): `typed_function` is
function.v:59 (doc: 60); `refinedc_adequacy` adequacy.v:40 (doc: 41);
adequacy.v is 127 lines (doc "~150").

### MINOR-6. `vm_compute` is in the *rule grammar*, not only "the solver path"

§3.6/§4-item-14(a) locate the vm_compute trust delta in the solver
layer. In fact `li_tactic (li_vm_compute …)` occurs inside registered
**typing rules**: `annot_reduce_int` (int.v:386) has it in the rule's
continuation; the `Goto` step runs `compute_map_lookup` over the
CODE_MARKER-wrapped label map (automation.v:170-176,
automation/proof_state.v:25-29). The house ban therefore requires a
kernel-legal computation story at the rule/interpreter level, not a
solver swap — the ledger row should be priced accordingly.

### MINOR-7. Missing agenda question: which Core fragment, and Core's evaluation-order nondeterminism

Item 13 covers relational `eval_bin_op` only. Core has *unsequenced*
composition (`Eunseq`, wseq/sseq) — evaluation-order ND with UB at
races, a fundamentally different ND species than Caesium's per-op
relational results (Caesium fixes evaluation order via its ectx
discipline). The rules of engagement say "their evaluated/
sequentialized fragment first," but the agenda never asks the concrete
question: is the port's referent sequentialised Core (which pass,
pinned where), and what happens to the WP when `Eunseq` is present?
This decision shapes the language-instance design (item 1) and should
be on the table explicitly.

### MINOR-8. FindInContext continuation subtlety worth stating

`liFindInContext` commits to the first FIC instance **whose entire
continuation** (`simpl; repeat liExist false; liFindHypOrTrue key`,
interpreter.v:589-591) succeeds; `liFindHypOrTrue` tries
`tac_sep_true` *before* the hypothesis scan (:571-575) — i.e. "prove it
from True/emp" beats "find it in context". The note's summary ("first
instance whose continuation succeeds is committed") is right but the
`tac_sep_true`-first ordering and the `liExist` inside the continuation
are behavioral details a reimplementation will get wrong from the note
as written (the probe's term shows both `tac_find_hyp` and
`tac_find_in_context` nodes, so the choice is at least trace-visible).

---

## NOTE findings

**NOTE-1 (anti-innovation lens).** §3.7(iii) leans toward "attribute-fed
DiscrTrees" citing "the prior review's observation" — reasoning-era
material is untrusted-design by ruling; the Lean rule-indexing choice
should be argued from the donor's actual requirements (Hint Mode
semantics, priority order, `Typeclasses Opaque` discipline — all
correctly documented in §3.4) at the attachment conversation, not
pre-tilted by v1. Symmetric check found no place where the doc invents
a Cerberus-side answer RefinedC already gives; §4's questions properly
ask rather than decide (item 6's dissolve-or-port on mem_cast, item 7's
env-vs-substitution, item 8's alloc-failure stance are all posed with
forcing-fact demands — good).

**NOTE-2.** `liExtensible` handles `subsume` natively before consulting
the hook (interpreter.v:195-200 `liExtensible_to_i2p` has a built-in
`subsume` case); the note presents rule dispatch as hook-only. Cosmetic
for the port map, non-cosmetic for a reimplementation's dispatch table.

**NOTE-3.** The §2 inventory is confirmed exhaustive: independent
re-enumeration of programs.v found exactly the 23 judgment forms +
`typed_stmt_post_cond` (aux); grep for `iProp_to_Prop` classes outside
programs.v/function.v across typing/ returns **nothing** — no judgments
in disguise. The only additions a ledger row-list should carry beyond
the doc's count: the `li_tactic` *operations* registered by
typing/caesium (`li_vm_compute`, `normalize_bitfield`,
`compute_map_lookup`, the loc-eq solver ops in automation/loc_eq.v) —
each is a rule-shaped extension point needing a ported counterpart.

**NOTE-4.** §5 adequacy claims verified in full, including the nice
observation that the typed→WP direction literally applies
`type_call`/`type_val`/`type_call_fnptr` inside the adequacy proof
(adequacy.v:80-84) — confirmed at source. §5.2's example files all
exist as named (VerifyThis2021/challenge{1,2}.c, mpool, btree,
scheduler, linux/{pkvm,casestudies} GPL-separated). UIP (axioms.v:5-8,
an `EqdepElimination` module instantiation) and the alloc-failure
Löb-divergence story (lang.v:471-497 `CallFailS`/`AllocFailS` — note
*calls* also alloc-fail, not just `Alloc`; lifting.v:52-59
`wp_alloc_failed` by `iLöb`) verified as claimed.

---

## §D4. Replay-lane feasibility assessment (dimension 4, requested)

Question: does the Lithium note establish what an ACL2Lean-style
*replay* of the Lithium IR needs — determinism boundaries, the meaning
of "same residual side conditions," where nondeterminism/heuristics
live?

**As written: no** (MAJOR-2, MINOR-1, MINOR-8 are exactly the gaps).
The note's determinism story would lead a replay harness to treat the
walk as a pure grammar-directed rewrite with side conditions batched at
the end; in reality branch pruning, the `done` fast path, unsafe
simplification, and registered Ltac all fire mid-walk, so the residual
goal set co-varies with the solver/hook surface.

**Feasibility itself: POSITIVE**, on probe evidence the note only
half-states. The compiled proof term of a real automation-closed donor
proof (wrapping_add probe, MINOR-2 transcript) is a complete,
machine-readable step trace: every interpreter step leaves a
distinguishable `tac_*` node, committed rule choices appear as named
`*_inst` constants, FindInContext/hypothesis choices appear as
`tac_find_hyp`/`tac_find_in_context` nodes with their instantiations,
and in-walk solver discharges appear as embedded pure subproofs. A
replay harness should therefore replay **from the proof-term trace**
(or equivalently from `liTrace_hook` instrumentation — hooks.v provides
the channel), where all four nondeterminism sources are already
resolved and recorded — rather than attempt to reproduce Coq-side TC
resolution, unification, and `lia` behavior blind. Under that design,
"same residual side conditions" becomes well-defined: the shelved
`SHELVED_SIDECOND` set plus the recorded in-walk discharges, both
extractable from the term. The note should be amended to say this;
with MAJOR-2/MINOR-1 fixed it would be sufficient to scope the lane.

---

## What was probed vs read (method disclosure)

Executed: dune/dep-structure inspection; ~60 file:line spot-checks
across caesium/lithium/typing (all quoted claims above re-derived);
grep sweeps for the four blind-spot classes; two compiled probes
against the built donor (`imp_probe.v` import smoke, 0.6 s;
`li_probe.v` full wrapping_add typing proof + term print, 1.4 s,
exit 0). Not probed for time: liStep single-stepping on a synthetic
goal (the donor's own lithium_tutorial.v documents the single-step,
`Fail liStep`-on-stuck, and `unshelve_sidecond` behaviors and was read
instead); reproduction of the 614-declaration count (the 247-name
headline was consistency-checked against the list itself: 250 rows,
247 unique names, dups = expr/stmt/subst_stmt across lang.v/W).

---

## Re-mark (rev2, 2026-08-29)

Re-mark by the original fresh-eyes reviewer (author→professor→re-mark
pattern) of port-map **rev2** (worktree branch `arc1-port-map-rev2`,
commit `bf676d3`, 312 insertions / 58 deletions). Method: full read of
the rev2 diff; every NEW cite the revision introduced was spot-checked
against `deps/refinedc` @ `25f706d41` (transcripted greps/seds; ~20
checks), including the three contested items below. No new probes were
needed — the revision's re-run of the wrapping_add probe reproduces my
tallies verbatim in §3.8.

### Per-finding disposition

| Finding | Disposition | Basis |
|---|---|---|
| MAJOR-1 (interface blind spots) | **ADDRESSED** | §1.3 retitled "named-identifier stratum"; new §1.3.1–§1.3.4 enumerate projections/constructors/instances/Ltac+hint-DBs. New cites verified: `sl_nodup`→typing/struct.v, `hs_heap`/`hs_allocs`→adequacy.v, W-constructor list at programs.v:257-276 exact (incl. `W.Loc`/`W.LocInfoE`/`W.LValue` my review missed), Atomic instance names `cas/skipe/deref/use_atomic` at lifting.v:39-50 exact. The revision *extended* the finding correctly (EqDecision/Countable/Inhabited stratum — see adjudication 3). |
| MAJOR-2 (determinism boundary) | **ADDRESSED** | §3.2 now separates step *selection* (structural) from step *outcomes* (solver-coupled); §3.3 rewritten around the three in-walk surfaces with correct cites (can_solve_hook ::= solve_goal, automation.v:45; solvers.v:235-242; interpreter.v:458-478). |
| MAJOR-3 (annotation carrier) | **ADDRESSED** | New agenda item 15. Question-form verified: states the frontend-plants-nodes fact, the invariants-survive-via-`split_blocks` split (correct — probe-observed), then asks carrier + first-fragment membership. No smuggled decision. |
| MAJOR-4 (W-syntax dependence) | **ADDRESSED** | §1.1 port-mapping sentence now carries the structural caveat with cites; new agenda item 16 asks the dispatch/bind question, including the dissolution possibility, as alternatives — not a decision. |
| MINOR-1 (liEnsureInvariant/liSimpl) | **ADDRESSED** | §3.2 gives liRStep's full shape; tutorial cite (lithium_tutorial.v:30) verified — `liEnsureInvariant.` is literally line 30. |
| MINOR-2 (proof-term claim) | **ADDRESSED** | §3.6 corrected ("chains of `tac_*` nodes of which `tac_apply_i2p` marks the rule applications"); §3.8 carries the probe tallies, which match my transcript exactly. |
| MINOR-3 (ladder-scope) | **ADDRESSED** | Typing-scoped vs ladder-superset scope note added to §1.3 intro with the builtins_specs evidence. |
| MINOR-4 (caesium←lithium undersell) | **ADDRESSED** | §1.1 widened correctly; span corrected per adjudication 2 (upheld). |
| MINOR-5 (tallies) | **ADDRESSED** | All re-checked in rev2: automation/ 525, annotations.v 27, exist.v 111, axioms.v 11, int.v 31, function.v:59, adequacy.v 127/:40, hook cite :622-645 (both places), hooks.v:1-68. Hook count now 16 — my 17 conceded (adjudication 1). |
| MINOR-6 (vm_compute in rule grammar) | **ADDRESSED** | §3.6, agenda 14(a), and §6.5 all restated at the rule/interpreter level with correct cites. |
| MINOR-7 (Eunseq/fragment) | **ADDRESSED** | New agenda item 17; question-form clean ("which pass, pinned where; what happens to the WP when `Eunseq` is present?"). |
| MINOR-8 (FindInContext continuation) | **ADDRESSED** | §3.2(2) expanded; new spans verified: `liFindHyp` at interpreter.v:537 (so :537-570 correct), continuation `simpl; repeat liExist false; liFindHypOrTrue key` exactly at :589-591. |
| NOTE-1 (DiscrTree lean) | **ADDRESSED** | §3.7(iii) rewritten as an open choice argued from donor requirements; the prior-era lean removed. |
| NOTE-2 (native subsume case) | **ADDRESSED** | §3.2(1) now states the built-in `subsume` case before the hook. |
| NOTE-3 (li_tactic operations) | **ADDRESSED** | §2.2 row-list paragraph now carries the operations; all four new cites verified (compute_map_lookup = lithium/solvers.v:140; unfold_code_marker_and_compute_map_lookup = automation/proof_state.v:28-29; normalize_bitfield LiEntails extern region :294-300; loc_eq.v:46-70 incl. the FICLocSemantic `FindHypEqual` extern at :69). |
| NOTE-4 (verified-as-claimed record) | **ADDRESSED** (n/a) | Nothing to fold beyond the §6.5 vm_compute rewording, which is present and correct. |

Tally: 16/16 ADDRESSED, 0 PARTIALLY, 0 NOT ADDRESSED.

### The three adjudications

1. **hooks.v count — CONCEDED, worker is right: 16.** Anchored
   enumeration (`grep -n "^Ltac"` over hooks.v) yields exactly 16
   `Ltac *_hook` declarations (can_solve, normalize, check_injection,
   enrich_context, solve_goal_prepare, solve_goal_normalized_prepare,
   reduce_closed_Z, li_pm_reduce, unfold_instantiated_evar,
   solve_protected_eq, generate_i2p_instance_to_tc,
   liUnfoldLetGoal, liExtensible_to_i2p, liExtensible, liTrace,
   liToSyntax). My 17 was a regex artifact, though not the conjectured
   one: my unanchored `Ltac.*hook` matched the *comment* at hooks.v:3
   ("This file collects all Ltac hooks that Lithium provides."), not a
   digit-miscount. Rev2's "16 named Ltac hooks (hooks.v:1-68)" is
   correct.
2. **bitfield.v CanSolve span :328-357 — UPHELD (worker's widening
   correct).** `bf_range_empty_cons_inst` at bitfield.v:328 carries
   three `CanSolve` premises (:329-331) on a `SimplAnd` instance; the
   guarded family genuinely starts there. My :341-357 was the
   truncated head of a `| head` pipe, not a considered boundary. Note
   the widened span is also *tight*: `bf_range_empty_nil_inst` (:321)
   is unguarded, so starting at :328 is exactly right, and the
   SimplAnd/SimplBoth mixed description in §1.3.4 matches the source.
3. **Fractional relocation + EqDecision/Countable/Inhabited stratum —
   UPHELD, and a genuine improvement.** ghost_state.v:440-463 is
   precisely the `Timeless`/`Fractional`/`AsFractional` family on
   `heap_mapsto_mbyte` and `↦` (instances at :440, :443-444,
   :452-453, :457, :459, :462-463); my original ":65-128" was correct
   for the Persistent/Timeless assertion-layer instances but wrong to
   imply Fractional lived there (and rev2's :65-131 is the tighter
   truth — `fntbl_entry_tl` at :131 closes the run, past my :128).
   The added decidability/inhabitation stratum verifies exactly:
   loc.v:24-27 (`prov` Inhabited/EqDecision/Countable), val.v:12
   (`mbyte_dec_eq`), lang.v:724-732 (the Inhabited family through
   `state_inhabited`). This is a real further find within MAJOR-1's
   class (c) that my review did not surface.

### New agenda items and §3.8

- **Items 15/16/17** state MAJOR-3/MAJOR-4/MINOR-7 correctly and stay
  in question form; enumerated alternatives (side table vs Core/Ail
  annotations; dissolution to place-contexts-only or nothing) are
  posed as options, not answers. No smuggled decisions found.
- **§3.8** reproduces my §D4 result accurately (same tallies, same
  well-definedness formulation for "same residual side conditions",
  same never-blind-reproduction directive). "Lane L" is an
  established name in the DECISIONS register (the replay-disposition
  entry), so no jargon violation; the "should scope against" sentence
  is the one place §3 shades from fact into recommendation — tolerable
  because the recommendation is this review's own and Lane L's
  disposition is already [USER]-registered, but the Lane L charter
  should restate it as its own decision rather than inherit it from a
  recon document.

### Residual nits (non-blocking; for the next natural revision, not a re-fold)

- §3.3 still says RefinedC's overrides are "`::=` at :18,45,47,49";
  the full site list in typing/automation.v is :18, :25, :42, :45,
  :47, :49, :88 (solve_protected_eq_hook, liUnfoldLetGoal_hook,
  liToSyntax_hook are the unlisted three; two of them ARE discussed
  elsewhere in the doc). Incomplete enumeration, not an error.
- §1.3's method note still opens "produced mechanically — …
  intersected …" before the stratum caveat lands two sentences later;
  a reader quoting the first sentence alone still over-trusts the
  method. Cosmetic ordering.

### Verdict

**Rev2 is FIT to serve as the port-ledger foundation and as the basis
for the attachment-layer scope conversation.** All 16 findings are
addressed with source-verified cites; the two claims I called
ledger-poisoning (the "exhaustive" interface claim and the misdrawn
determinism boundary) are correctly repaired, and the revision's
counter-corrections to my own review (hooks count, CanSolve span,
Fractional location) are all themselves correct — the document now
reads as more careful than its reviewer on those three points, which
is the right failure mode. The residual nits above are recorded here
per the no-silent-fixes rule and do not warrant another revision pass
before the operator conversation.

[AGENT: fresh-eyes reviewer, re-mark 2026-08-29]
