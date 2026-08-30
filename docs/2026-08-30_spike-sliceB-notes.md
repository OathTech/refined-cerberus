# Spike slice B — build notes (artifact 4 + adequacy + engine exhibits)

[AGENT 2026-08-30] Slice-B worker record. Deliverables:
`RefinedCerberus/Spike/{Soundness,Adequacy,Exhibit}.lean` wired into
the lib root before `Audit.lean` (sweep: 196 theorems, all cones the
classical trio; 7 curated pins). Design decisions continue slice A's
numbering. Mid-slice the operator issued four upgrades, all folded in
(D14, D16, D17, D18); the orchestrator's original "seeded minimal
MemState" phrasing was corrected by the operator to the splitting
form (D17) — the seeded state survives only as the exhibits' test
instance.

## Design decisions ([AGENT] unless cited)

### D13. The boundary architecture: decomposition judgment + per-rule engine equations + one master theorem
Soundness.lean certifies Step by:
- `Decomp e ctx r` — the engine's context decomposition as a
  judgment (root redex classification `Redex` + Csseq/Cannot spine),
  proved equal to `get_ctx`'s output (`Decomp.get_ctx_at`) and
  related to Step both ways (`Decomp.rebuild` = the congruence rules'
  certification; `Decomp.step_factor` = their inversion);
- per-rule engine equations `step_ctx_*` (D14 shape), computing the
  engine's step list symbolically for each Step rule / value form;
- `engine_complete`: at every fragment configuration the engine has
  EXACTLY ONE behavior and it is `EngineMatch`ed by Step
  (Step-transition / value protocol / refusal-at-Step-stuckness).
The mapper-reduction tactic pattern (unfold step_ctx → dsimp → rw the
get_ctx equation → `cases ctx <;>` staged rewrites) reduces the
~1-page step_ctx body per lemma in well under a second — the K2
symbolic-unfolding tripwire NEVER fired (measured: full Soundness.lean
elaborates in ~5s).

### D14. Context undisturbed ([USER 2026-08-30], the theorem shape)
Per-rule statements quantify the machine's non-expression,
non-memory configuration and return it VERBATIM (⟨heap, ctx⟩ →
⟨heap', ctx⟩) — the machine-level locality of abstract separation
logic, proved of the engine's own step function. The measured
three-way partition (the certification's per-component finding):

| component | class | where read (engine cite) |
|---|---|---|
| file, extern | untouched-unread | only proc/impl/Erun arms (outside fragment) |
| errno, current_proc_opt, exec_loc | untouched-unread | — |
| current_loc | untouched-unread on the fragment | read only when `isLibraryLocation loc` (step_ctx loc' let) — excluded by the fragment's `hlib`; WRITTEN only when node annots carry `Aloc` (get_loc) — excluded by the fragment's `[]` annots |
| tagDefs | read-only-under-WF (store rule only) | memValueFromValue at operand encoding, step_action Store0 arm (Core_reduction.lean:424); premise = the encoding fact AT the quantified tagDefs |
| env | read-only-under-WF (the two betas only) | update_env (Core_aux.lean:868) fails loudly on `[]` — premise = nonemptiness; wildcard update is the identity (Core_aux.lean:861 first arm) |
| stack0, parent tid | read at PROGRAM-DONE only | Stack_empty/none select Step_done2 over RETURN/THREAD-DONE (step_ctx value arm) |
| core_run_state | read-only, verbatim (∀ rs in the discharge) | the fragment's request monads are `stExceptUndef_return`; the REAL driver ticks aid_supply per action (fresh_action_id', Driver.lean:284) — mirrored by the quantified `aid` parameter |
| tid | not state | copied verbatim into the request payload |
| arena, MemState | TOUCHED | the transition itself; memory only through the request discharge |

step_ctx itself ticks no counter (checked; dr_step_counter is
driver_state, outside the seam). The frozen-context `engineSteps_*`
forms are one-line corollaries; adequacy launches from them (D17's
triple still quantifies every configuration's MEMORY arbitrarily).

### D15. The discharge mirror and its three cited projections
`dischargeStep` mirrors `action_request_sequential2` (Driver.lean:273)
projected to (thread_state, MemState): (i) `prefixOfPointer` dropped —
it is `memReturn none` (CerbMem.lean:2064), state-invariant,
never-killing, trace-only; (ii) driver_state (trace/fs/concurrency/
step counter) projected away; (iii) the aid draw is a quantified
parameter (fragment continuations ignore it — slice A D2 confirmed at
certification level: the per-rule lemmas hold ∀ aid).
`EngineOutcome.offFragment` marks step forms the fragment never
produces; `engine_complete` needs only that refusals coincide with
Step-stuckness, so no storeM-shape lemma ("only NDactive/NDkilled")
was required — recorded as deliberately unproved-as-unneeded.

### D16. The exported face: semantic triples ([USER 2026-08-30], final form)
`SemTriple e P post` — engine vocabulary only (drive, MemState,
CellMap footprints, Sat = Coh); `ProvenTriple` (the Iris WP judgment)
is the interior hypothesis and the only place WP appears in the
exported layer. `semantic_triple_sound` is the headline;
`semantic_frame` moves a named frame F across a proved triple by
Iris framing (wp_frame_r + bigSepM_union) — no engine-level reproof.
Supporting interior lemmas: `genHeap_valid_big` (big-footprint
lookup, mirrors ghost_map_lookup_big), `bigSepM_own_disjoint` (two
fully-owned footprints are key-disjoint — via pointsTo_ne at a
classical witness), `Sat.mono` (submap closure), `cells_readout`
(footprint cells + stateInterp ⇒ the pure conclusion).

### D17. The splitting configuration ([USER 2026-08-30], correcting the minimal-heap phrasing)
The triple quantifies R (the rest) EXPLICITLY: pre `Sat σ (P ∪ R)`,
post `Sat σ' (Q ∪ R)` with THE SAME R — verbatim rest at cell
granularity. Since `Sat` constrains only its footprint's cells, the
non-footprint part of the MemState (other allocations, other bytes,
the side tables after D18) is additionally arbitrary. The engine-side
memory locality that makes R survive is slice A's `Coh.store`
(writeBytesTo is range-local: `readBytesFrom_writeBytesTo_disjoint`,
Heap.lean; allocation table untouched by storeM's active path) — no
new locality lemma was needed. No rule's engine step touches memory
outside the addressed footprint (no finding to report under the
operator's point (2)). The recon's seeded state appears ONLY in the
exhibits' engine instances, never in exported quantifiers.

### D18. The side-table de-pin ([USER 2026-08-30])
`Coh`'s global pins (lastUsedUnionMembers = [], funptrmap = []) are
GONE. The tables are symbolic (read-only context); each cell carries
`CellCoh.dec_indep` — decode is table-independent, exactly what
loadM's `reconstructValue` (CerbMem.lean:652) reads them for (the
unionmap enters only union arms, the funptrmap only pointer-byte
arms; for scalar cells the premise is `fun _ _ => rfl`). `StorableAt`
gained the serialization-side analogues (`bytes_fpm`, `stored_dec`;
storeM serializes at the state's CURRENT funptrmap, and its
funptrmap-update is the identity by the ∀-form neutrality already in
slice A's `fpm` field). Blast radius: Heap.lean (Coh/CellCoh/
StorableAt + the three memM theorems), two argument drops in
Rules.lean, `rfl`-component additions in the exhibits — under an
hour, option (a/b) of the operator's sequencing. Full-build shape
(per the instruction, recorded): ghost ownership of the tables
(funptrmap ↔ the donor's fntbl_entry analog); dec_indep is its
degenerate case.

### D19. Fuel honesty (the R-vi/K2 residue, now a stated side condition)
get_ctx is fuel-bounded with an OPAQUE exhaustion leaf (LemLib
fuelExhausted — deliberately not provably equal to anything), so
nothing about a configuration is provable at insufficient fuel:
fail-closed by construction. Every symbolic statement carries
`esize e ≤ lemDefaultFuel`; `esize` (the sequencing/annotation spine
depth) grows ≤ 1 per step (`Step.esize_succ`), so drive statements
carry `esize e₀ + steps ≤ lemDefaultFuel` (10^6 — irrelevant at any
practical scale, but the honest form).

### D20. Values in the drive: the D1 readout composed
`engine_complete`'s value protocol: bare value → `Step_done2 v`
(stack empty, no parent — the two premises PROGRAM-DONE actually
reads); annot value → the REMOVE-ANNOT tau to the bare value (no
Step analogue — exactly slice A's D1 divergence), then done. In the
adequacy induction the annot-value case exits through a two-step
sub-lemma (`drive_value_pure`) carrying the postcondition across the
tau; the delivered engine value is `SpikeVal.val w` — the annotation
erasure happens exactly here, once.

### D21. Termination of exhibit (a) by simulation, not evaluation
`drive` on the concrete seeded state does NOT reduce definitionally
(Std.TreeMap insert/get? are not kernel-reducible — see D22), so the
probe-as-theorem (`exhibitA_terminates`: six steps to
`.done Specified(7)`) is proved by SIMULATION: six applications of
the per-rule certification lemmas with the concrete memM facts
supplied by slice A's `storeM_success`/`loadM_success`/`Coh.store`
instantiated at the seeded state. Safety and the value's uniqueness
come from adequacy (`exhibitA_engine`); the simulation adds only
"it actually gets there".

### D22. Operational finding: TreeMap-backed state is defeq-opaque; stage every rfl
`Std.TreeMap`/`ExtTreeMap` operations do not reduce definitionally
(well-founded internals). Consequences: (i) seeded-state facts are
proved via record-projection rfl (shallow) + `Std.TreeMap.get?`
lemmas (`getElem_insert` etc.), NEVER by evaluating the map; (ii) a
plain `rfl` whose sides differ anywhere near a map forces the
elaborator into the map internals — maxRecDepth, which house rules
forbid bumping — the resolution is STAGING (`show`-ascription /
`rw [show _ = _ from rfl]` at the exact stuck scrutinee, the same
discipline as slice A's D12 matcher finding, now for defeq
unfolding); (iii) `dischargeStep`'s memM matches connect to
`applyMemM` facts by case analysis, not defeq.

### D23. Store's ILLTYPED arm is certified, not excluded
`memValueFromValue` failure at a store operand gives the engine's
`ACTION_ILLTYPED → Step_error2` (certified with its verbatim message,
`engineSteps_store_illtyped`) and Step is provably stuck there
(store_inv needs the encoding fact) — so the refusal is
EngineMatch'd without adding a well-formedness side condition to the
fragment. The WP excludes it because `wp_store` demands the encoding
fact (slice A); adequacy turns that into "the engine never reaches
the ILLTYPED report".

### D24. loc0 = `.unknown` in the exhibits
`isLibraryLocation (.other s)` routes through `getFilename = some
"<internal>"` and a String.splitOn refutation — a string computation
the kernel has no business grinding through. `.unknown` gives the
non-library fact by rfl. Recorded divergence from the recon probe's
`.other "spike"` (semantically irrelevant: loc reaches only error
payloads).

## Slice-A claims checked against this build

- D2 (no aid in terms) CONFIRMED at certification level: per-rule
  lemmas hold ∀ aid.
- D5 (loc): resolved by carrying `isLibraryLocation loc = false` in
  the fragment (the first of D5's two options); loc-irrelevance of
  the active path was not needed.
- D9 (UB exclusion = NotStuck): the refusal certification makes it
  engine-real — killed/error outcomes exist exactly where Step is
  stuck, and NotStuck refutes them on the WP-covered cone.
- D11 (SpikeGS honest gap): CLOSED — `spike_step_adequacy` constructs
  the bundled ghost state by `genHeap_init` over the initial cell
  map, exactly the HeapLang pattern.
- Slice A's `Coh` global pins: REMOVED (D18) — the slice-A reasoning
  ("fragment-invariant") was sound but needlessly global; the
  per-cell inertness premise is strictly more general.
- Recon unknowns closed: step_ctx symbolic-unfolding perf (K2) is a
  non-issue at fragment scale (D13); R-ii/R-iii context supplies are
  now THEOREMS (D14's partition), not judgments-hygiene notes.

## Gate status

`./scripts/test_unit.sh`: ALL GATES GREEN (grep ban + build;
capped falls back uncapped-loud in-sandbox per the recorded ruling).
In-build audit: axiom sweep over 196 RefinedCerberus theorems, all
cones within the classical trio; curated pins on `Spike.exhibit`,
`engine_complete`, `spike_engine_adequacy`, `exhibitA_engine`,
`exhibitB_engine`, `exhibitA_terminates`, `semantic_triple_sound`,
`semantic_frame` (exact trio each). No sorry, no non-kernel methods,
no new axioms, no maxRecDepth/heartbeat bumps.

## Extension D notes (D25+; production-driver coupling worker)

### D25. The collapse architecture: runOne layer + per-round equations + one simulation
The production coupling is proved at the ONE-LAYER level, not the
runner level: `runOne` (DriverCollapse.lean) applies an ndM tree to a
state and exposes the raw `nd_action × state`; composition lemmas
(`runOne_bind_active`, `runOne_liftMem_active`,
`runOne_liftCore_run_*`) collapse the driver's bind/lift plumbing one
layer at a time — each `nd_bind` spends one layer of its own FRESH
`nd_bind_lemFuel` budget (Nondeterminism.lean:188), so bind fuel
never accumulates across a run; the only per-step fuel is
`drive_nonmemory_steps_aux2`'s own loop budget (hence the `n + 2 ≤
lemDefaultFuel` side condition: n drive steps + the done-recording
and drain iterations). `runND` enters exactly once, at the very end
(`runND_active`, empty axiom cone). The unfolding recipe that works
against the generated fuelled definitions:
`rw [lemDefaultFuel_succ]; unfold f_lemFuel; dsimp only; rw [h]` —
the same staging discipline as D12/D22, now for fuel matchers.

### D26. wp_create is unprovable without an allocator-cursor resource (design finding)
`allocateObject` kills ("out of memory", CerbMem.lean:1479) when the
allocation cursor is exhausted — a condition the cell footprint says
nothing about, so the WP's NotStuck obligation for `create` cannot be
discharged from ownership. Consequence: `create` joins the fragment
at the Step/certification level only (rule + createRedex +
step_ctx_create + dischargeStep Create arm + engine_complete case);
cold-start programs discharge their create prefixes CONCRETELY on
the production-pinned initial memory, where success is a theorem.
The full-build shape is an allocator-cursor ghost resource in the
state interpretation (then `genHeap_alloc` is the ghost step of a
sound wp_create). Note the mirror details: create's continuation is
a BARE value (`mk_value_e (Vobject (OVpointer ptr))`, no Eannot
residue — step_action's Create arm, Core_reduction.lean:424), and
allocateObject DISCARDS both tid and the requested address
(CerbMem.lean:1470-1474) — the Step rule pins them to 0/none and the
certification bridges by `allocateObject_arg_irrel` (D28).

### D27. The scheduler's opaque mode read is handled by cases, and both branches converge
`driver2`'s random-vs-exhaustive branch reads
`CerbGlobal.current_execution_mode ()` — an `opaque` constant (not
an axiom; kernel-consistent, value unknowable). The round equation
(`driver2_done`) is proved by `cases` on the mode test: on a
SINGLETON non-blocked step list both branches reduce to the same
pick-the-one-step path (`pick` on a singleton is `NDactive`,
Nondeterminism.lean:276 — no ND node, so branch-freeness survives
the scheduler). Unit-valued debug plumbing (`print_debug_pure` & co)
disappears definitionally by Unit eta.

### D28. Concrete-state defeq is the cost center; symbolic bridges keep it off the path
Two measured hazards, both avoided structurally rather than by limit
bumps: (i) letting the elaborator discover that discarded arguments
don't matter (`get_with_address []` vs `none` in the create payload)
forces whnf of `allocateObject` AT THE CONCRETE STATE — a heartbeat
blowout; the fix is the symbolic-argument equation
`allocateObject_arg_irrel` proved once at symbolic arguments
(Soundness.lean). (ii) `simp` on byte-level facts at a LITERAL
address evaluates the TreeMap bytemap (kernel deep recursion); the
fix is stating the length fact at a universal address
(`errno_bytes_len (a : Int)`), exactly the exhibit's `bytes_len`
shape. Corollary of D22, recorded because both failures were
observed live in this slice.

### D29. The production simulation consumes the drive hypothesis, not adequacy
`prod_loop_done` takes `∀ aids, drive … = .done v σfin` and mirrors
it step-for-step through the production loop; the killed/refused
engine arms are REFUTED by the hypothesis (a killed drive cannot be
`.done`), so no NotStuck input is needed and the whole collapse
layer stays engine-vocabulary (and trio-exact). The ∀-quantification
over action-id supplies is what lets the induction realign with the
production supply (which starts at the opaque
`initial_core_run_state` seed): the drive successor is
aid-independent on the fragment (slice-A D2 at work), so each step
instantiates the hypothesis at a cons of the production draw.
Adequacy (the SemTriple hypothesis) enters only once, at the very
end of `sem_triple_prod`, to convert the delivered value/state into
the postcondition — the same division of labor as
`spike_engine_adequacy` vs `exhibitA_terminates`.

### D30. The boundary event (D5) landed as declared, module-scoped
`runEffectful` (LemLib.lean:54, the semantics repo's one residual
axiom) enters the cones of exactly the theorems whose STATEMENTS
mention `initial_driver_state` (its `initial_core_run_state` draws
sym_supply through the effectful seam). Audit.lean now carries a
module-scoped boundary: `Spike.ProdEntry`/`Spike.ProdExhibit` are
allowed trio + runEffectful; every other module (including all of
DriverCollapse) is held to the trio by the sweep. Boundary entry is
TEMPORAL with the mover named (the semantics repo's register owns
runEffectful's deletion). The modified sweep was plant-tested in
both directions: a runEffectful-carrying statement outside the
boundary modules fails the build; a `sorry` inside them fails the
build.

## Extension D gate status

`./scripts/test_unit.sh`: ALL GATES GREEN (grep ban + build; capped
falls back uncapped-loud in-sandbox per the recorded ruling).
In-build audit: sweep re-baselined 209 → 287 in this commit
(Extension D: the create certification, the DriverCollapse layer,
the ProdEntry cold start + theorems, the ProdExhibit demonstration);
34 theorems in the two production-entry boundary modules carry
exactly trio + runEffectful (statement-level, see D30), all others
trio-exact. New curated pins: prod_loop_done, driver2_done,
finalize_done (exact trio), prod_run_eq, sem_triple_prod,
exhibitA_prod (exact trio + runEffectful). No sorry, no non-kernel
methods, no maxRecDepth/heartbeat bumps.
