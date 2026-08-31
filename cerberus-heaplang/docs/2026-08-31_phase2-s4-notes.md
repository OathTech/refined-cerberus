# Phase-2 S4 slice notes: the acceptance (fib + array-sum)

[AGENT] S4 worker record, per the two-phase arc plan
(`2026-08-31_two-phase-arc-plan.md`) WITH the [USER] acceptance
amendment (fib + array-walk; list-reverse a registered stretch), the
S3 notes' §7 risk read (`2026-08-31_phase2-s3-notes.md` — the work
order), and standing discipline (frozen-corpus signature diff,
findings itemized, WF premises stated never absorbed).

Commits: S4.1 `61eaeea` (the acceptance kit + the env-map seam),
S4.2 `fe835ab` (FIB end-to-end), S4.3 `4654e67` (ARRAY-SUM
end-to-end), S4.4 (this commit: termination accounting, the
production registration tie, this record, the claims surfaces).
Gates green at each commit (`scripts/test_unit.sh`: grep ban + both
packages with in-build audits).

## 1. What landed (per mission item)

1. **FIB** (`FibExhibit.lean`): the iterative two-accumulator loop
   `save loop:(i:=0,a:=0,b:=1) in if (i<n) then run loop(i+1,b,a+b)
   else pure(a)`, verified by `blockSpecs_intro` with the
   data-dependent invariant `a = fibSpec i ∧ b = fibSpec (i+1)` over
   ANY reachable frame, collapsed by `wps_sound`, exported by
   `engine_adequacyJ`: `fib_certified` — driveJ never kills/derails
   and any delivered value = `ivVal (fibSpec n.toNat)`, at ANY
   initial memory (empty seeded footprint; `Coh σ ∅` vacuous). Pinned
   trio-exact. NO Ecase and NO binding-sseq were needed for fib's
   shape — the S3 risk read's items (a)-(c) turned out to be
   ARRAY-side (and the Ecase EVAL arm not needed at all): fib's whole
   data flow rides jump arguments and the S4 PURE exit.
2. **ARRAY-SUM** (`ArrayExhibit.lean`):
   `save loop:(i:=0,acc:=0,p:=base) in if (i<n) then lets
   Specified(x) = load(int,p) in run loop(i+1,acc+x,
   array_shift(p,int,1)) else pure(acc)`, with the index-partitioned
   invariant `acc = (vs.take i).sum ∧ p = base + 4i` carrying the
   array cell; `array_sum_certified` — value = `ivVal vs.sum` AND
   the array preserved (final `CellCoh` at the seeded bytes). Pinned
   trio-exact.
3. **TERMINATION ACCOUNTING** (driveJ lane): `driveJ_step` /
   `driveJ_done` (Adequacy.lean — one certified drive step per
   mirror step via `engine_step_matchJ`; the drive-monotonicity
   lemma was NOT needed: the exhibit is driven at the exact bound).
   `fib_certified_total`: at the loop variant's step bound
   `2·n + 4`, driveJ DELIVERS `fib n` — UNCONDITIONAL (no fuel
   hypotheses at all; the per-step `esize`/`peDepth` budgets are
   constants discharged outright). The induction measure IS the
   variant `n − i` (2 steps per iteration: guard + jump; entry 1,
   exit 3). Honest residual: the GENERAL variant-rule-to-step-bound
   theorem (from `blockSpecs_intro_variant`'s measure to a bound for
   an arbitrary program) is not established — the exhibit-level
   product is; a general theorem needs a step-counting refinement of
   the wps layer (registered forward item).
4. **PRODUCTION TIE** (ProdEntry.lean, boundary): `collect_saves`
   and `collect_labeled_continuations_NEW` COMPUTE the fib and
   counter-loop label maps (no array registration tie exists —
   plural corrected per arc-close audit MINOR 4) on the synthetic
   one-proc file (`collect_saves_fib`
   / `collect_saves_loop`, both `rfl`), so `LabeledAt` at the
   SHIPPED `initial_core_run_state` is DERIVED
   (`fib_labeledAt_production`, `loop_labeledAt_production`) — the
   S3 exhibit's recorded gap ("a collect-computed-Q bonus equation
   was NOT proved") closes. `counter_loop_certified_production`
   re-exports the counter loop with the run state built by the
   shipped registration only. Honest residual: the full
   production-face `.done` equation for a LOOP run (driver2-level)
   is NOT established — DriverCollapse's scheduler equations are
   pinned at the phase-1 profile (spike run state / no proc); the
   step-bound product (`fib_certified_total`) is its in-budget
   discharge waiting on run-state-general driver2 equations.

## 2. Design decisions ([AGENT], each with the forcing fact)

- **The array is ONE allocation** (recorded divergence from the
  amendment's `∗_{i<n} base+i·|int| ↦ vs[i]` pre-state phrasing;
  module header carries the full statement). Forcing fact about
  Cerberus: `loadM` resolves the pointer's PROVENANCE allocation and
  bounds-checks against it (generated/CerbMem.lean:1586-1631), and
  `arrayShiftPtrval` PRESERVES provenance (CerbMem.lean:1127-1142);
  in this ghost model a cell IS an allocation (`CellCoh` keys on the
  allocation id) — so a pointer walked by real arithmetic can never
  legally reach a sibling allocation: the ∗-of-cells array is not
  walkable IN THE ENGINE, by construction (exactly C's object
  model). The array is one allocation/one ghost cell; per-element
  structure lives in the index-partitioned invariant + per-element
  decode premises (`hdec` — the interior analog of
  `CellCoh.dec_indep`, instantiable by `rfl` at concrete bytes);
  the heap footprint still flows through the big-sep machinery.
- **`Specified`-binder lets instead of Ecase for load unwrapping.**
  `update_env_aux`'s `CaseCtor Cspecified` arm (Core_aux.lean:861)
  binds the payload OBJECT value — Core's own mechanism turns a
  loaded `Vloaded (LVspecified ov)` into an arithmetic-usable
  binding with NO new evaluation machinery; the Ecase EVAL arm
  (small-step scrutinees) stays unmirrored (registered).
- **PURE exits at `PEsym` shape.** The Epure engine equation needs
  the pexpr's head constructor exposed (step_ctx's CTX-value arms
  match `Epure (PEval _)` under the redex), so the general-`PePure`
  equation is a per-constructor × per-context case product
  (~25×7 heavy engine unfoldings — a measured blowup, stopped
  before the grind tripwire); the exhibits need only variable
  reads, so `stepDischarge_pure_sym`/`FragJ.pure_sym` are scoped to
  `PEsym`. Mirror `Step.pure_eval` and the inversion stay general.
  Extension is bounded and named.
- **The phase-1 step_ctx equations GENERALIZE `Decomp` → `DecompJ`**
  (their proofs read `hd` only through `get_ctx_default`), because
  a phase-1 redex can now sit under an S4 `Specified`-binder frame
  which `Decomp` cannot represent. Consequence: S3's
  `DecompJ.toDecomp` is FALSIFIED by the new frame and RETIRED
  (in-file note at its former site; its one consumer served by the
  generalized equations; phase-1 callers embed via `Decomp.toJ`).
- **The env-map seam CLOSED as S3 prescribed** (`EnvLaws.lean`):
  `Std.TransCmp symOrd` proved by characterizing the engine's
  symbol order (`mapKeyCompare` = `setElemCompare` = `ordCompare`
  over the Symbol Eq0/Ord0 instances) as
  `compareLex (compareOn digest) (compareOn number)` — using
  `digest_compare`'s REAL definition (CerberusFresh.lean:43, not
  extern-opaque) and core's `TransOrd String`. `SymFrame` (empty or
  captured-at-`symOrd`) + `envAdd_lookup` (Std.TreeMap's
  `getElem?_insert` under the instance) make lookup-after-add a
  one-comparison split; the S3 `IsXFrame`-style shape pins are not
  needed by any S4 invariant (S3's exhibit keeps its own — statement
  frozen). NOTE: the order is NOT `LawfulEqCmp` (comparator-EQ
  symbols may differ in `symbol_description`) — exactly the bucket
  subtlety LemLib's Fmap representation documents.

## 3. Statement-change findings (the frozen-corpus diff)

Instrument re-run: `scripts/signature_snapshot.lean` → committed
`2026-08-31_phase2-s4-signatures-post.txt`, name-keyed diff against
`2026-08-31_phase2-s3-signatures-post.txt` (derived tally; the
parser counts every dumped entry kind incl. ctor/rec):

- **UNCHANGED: 1107** — including, verbatim: every S3 headline
  (`counter_loop_certified`, `wps_sound`, `engine_step_matchJ`,
  `engine_adequacyJ`, `DecompJ.step_factor`, `stepDischarge_run`),
  the whole wps rule set (`wps_seq`, `wps_store`, `wps_load`,
  `wps_run`, `blockSpecs*`), the semantic face (`SemTriple`,
  `semantic_triple_sound`, `semantic_frame`), `engine_complete`,
  the prod layer, and the phase-1 corpus.
- **REMOVED: 1 = `DecompJ.toDecomp`** (falsified by the S4
  `sseq_spec` frame — §2; retirement note in Soundness.lean at the
  former site).
- **CHANGED: 42**, all in four classes (itemized):
  - **(S4-a) inductive-extension machinery** (the S3 J2 precedent):
    `Step`/`RedexJ`/`DecompJ`/`FragJ`/`PePure` gain constructors →
    their `rec`/`casesOn`/`recOn`/`below.*` entries (23 entries).
  - **(S4-b) `Step.sseq_inv`** gains the two `Specified`-binder beta
    disjuncts (the S3 precedent: node inversions gain disjuncts for
    new rules; every user extended, wildcard contexts refute by
    constructor clash `specPat_ne_base`).
  - **(S4-c) the seven phase-1 engine equations**
    (`step_ctx_store/_store_illtyped/_load/_create/_beta_pure/
    _beta_annot/_merge` + their `engineSteps_*` wrappers): the `hd`
    premise generalized `Decomp` → `DecompJ` (a strengthening —
    every old use passes `.toJ`; §2).
  - **(S4-d) def-body/equation artifacts**: `evalPexpr.eq_def`/
    `.induct`, `peDepth.eq_def` (the `PEarray_shift` arm — values on
    the old grammar unchanged), `evalPexpr_none_of_shape` (gains the
    `hne4` off-grammar hypothesis for the new arm).
- **ADDED: 170** (new content): the S4 Step rules + inversions, the
  EnvLaws module, the wps rules (`wps_pure`, `wps_load_eval`,
  `wps_seq_spec`, `wps_load_interior`), the Soundness certification
  layer (bridge arms, new redex/frame cases, the four new engine
  equations), the interior-load memM facts, the drive-step
  equations, and the three exhibit families with their pins.

Boundary: module set unchanged (`ProdEntry`/`ProdExhibit`);
boundary theorem count 34 → 40 (+6: the S4 registration-tie
theorems. CORRECTED TALLY [orchestrator, arc-close audit MINOR 3]:
3 of the 6 carry trio + `runEffectful` through the
`initial_core_run_state` STATEMENTS; the other 3
(`collect_saves_fib`/`collect_saves_loop`/`collect_new_fib`) are
trio-only — the original "each carrying" claim erred conservatively
but was a wrong derived tally). Sweep: 542 → 643
boundary-swept theorems; banned-axiom sweep 1319 constants clean;
all pre-existing pins byte-identical; +6 S4 pins (`fib_certified`,
`array_sum_certified`, `fib_certified_total`,
`fib_labeledAt_production`, `counter_loop_certified_production` —
the production two carrying the declared boundary — and the S3 set
untouched).

## 4. The acceptance theorems (verbatim signatures)

```lean
theorem fib_certified {GF : BundledGFunctors} [SpikeGpreS GF]
    (sbty : core_base_type) (n : Int) (hn : 0 ≤ n) (σ₀ : Mem)
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 3 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 2 + nsteps ≤ lemDefaultFuel) :
    let prog := fibProg ra n sbty ibty abty bbty
    let rs := fibRS ra n ibty abty bbty
    (∀ r, driveJ rs aids nsteps
      (procThread fibProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread fibProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread fibProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      v = ivVal (fibSpec n.toNat))

theorem fib_certified_total (sbty : core_base_type) (n : Int)
    (hn : 0 ≤ n) (σ₀ : Mem) (aids : Nat → Nat) :
    driveJ (fibRS ra n ibty abty bbty) aids (2 * n.toNat + 4)
      (procThread fibProcSym (fibProg ra n sbty ibty abty bbty)
        [fmapEmpty]) σ₀ =
      .done (ivVal (fibSpec n.toNat)) σ₀

theorem array_sum_certified {GF : BundledGFunctors} [SpikeGpreS GF]
    (sbty : core_base_type) (vs : List Int) (id a : Int)
    (aty : ctype) (bs : List CerbMem.AbsByte)
    (hsz : vs.length * 4 ≤ CerbMem.sizeofCtype aty)
    (ety : integerType)
    (hdec : ∀ (i : Nat) (hi : i < vs.length),
      ∀ (lum : List (Int × identifier)) (fpm : CerbMem.Funptrmap),
      CerbMem.reconstructValue lum fpm (a + ((4 * i : Nat) : Int)) intTy
          ((bs.drop (4 * i)).take (CerbMem.sizeofCtype intTy)) =
        CerbMem.MemValue.MVinteger ety (CerbMem.integerIval vs[i]))
    (hlib : CerbLocation.isLibraryLocation loc = false)
    (σ₀ : Mem)
    (hcoh : Coh σ₀ ((Iris.Std.PartialMap.singleton id
      (SpikeCell.mk a aty bs)) : SpikeHeapF SpikeCell))
    (nsteps : Nat) (aids : Nat → Nat)
    (hfuel : 4 + nsteps ≤ lemDefaultFuel)
    (hfuel2 : 3 + nsteps ≤ lemDefaultFuel) :
    let prog := arrProg loc ann ra mo sbty ibty accbty pbty xbty
      (cellPtr id a) vs.length
    let rs := arrRS loc ann ra mo ibty accbty pbty xbty vs.length
    (∀ r, driveJ rs aids nsteps
      (procThread arrProcSym prog [fmapEmpty]) σ₀ ≠ .killed r) ∧
    (driveJ rs aids nsteps
      (procThread arrProcSym prog [fmapEmpty]) σ₀ ≠ .stuck) ∧
    (∀ (v : value) (σ' : Mem),
      driveJ rs aids nsteps
        (procThread arrProcSym prog [fmapEmpty]) σ₀ = .done v σ' →
      v = ivVal vs.sum ∧ CellCoh σ' id ⟨a, aty, bs⟩)
```

(Section variables: fib's `ra ibty abty bbty`; array's
`loc ann ra mo ibty accbty pbty xbty`.) All conclusions are engine
vocabulary only; cones exactly the classical trio (pinned).
`hdec`'s decode premises are `rfl`-dischargeable at concrete byte
images (the general int-codec roundtrip theorem is not taken on —
recorded as a bounded forward item if quantified-byte-free
statements are wanted).

## 5. Frictions (for the next slice)

- **Stale-olean per-file iteration**: `lake env lean <file>` checks
  against the last BUILT oleans of dependencies; after editing an
  upstream module, dependents must go through `lake build` or the
  errors are phantom (bit twice early in S4.1).
- **Instance identity ≠ instance value**: the generated code's `==`
  chains (`instBEqOfEq0` towers) are semantically the core tests but
  synthesis-distinct — standalone `have`-restatements pick AMBIENT
  instances and rewrites then miss. The working patterns: manipulate
  the goal's OWN terms (`split at`), coerce hypothesis-side by
  `by exact` (defeq bridges `decide`-based tests), and characterize
  irreducibly-stuck chains once (`lemNatBeq_iff`).
- **Record-update syntax is line-break brittle** inside anonymous
  constructors (field values must not start on a fresh line).
- **`decide +kernel` vs free variables**: side conditions like
  `peDepth pe ≤ lemDefaultFuel` with metadata-quantified `pe` need
  the `rw [show … = k from rfl]; omega` form (helpers
  `peDepth_sym_le`/`peDepth_val_le`).
- **The subst-orientation drill** (S3's note) again: `obtain rfl :
  kept = killed` with the SURVIVOR on the left; the interior-load
  proof hit it at `mv = mval'`.
