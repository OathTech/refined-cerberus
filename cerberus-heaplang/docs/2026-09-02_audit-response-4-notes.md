# Audit-response-4 notes — closing the re-review's four Low findings

Re-review: `../../docs/2026-09-02_cerberus-heaplang-audit-response-re-review.md`
(third auditor, at `b34998d`), §"New findings in the response" N-1..N-4 and
§"Recommended next actions" (action 1). Branch `audit-response-4` from
`e1935a1`. Remit: DOCS ONLY — no statement, proof or import edit; the one
`.lean` change is the wording of `Audit.lean`'s two emitted sweep sentences
and its header comment (N-3, recorded in §4). Two commits:

| Commit | Content | Gate |
|---|---|---|
| A `56f5e39` | N-1, N-2, N-4 and the open-acceptance items, on ARCHITECTURE.md / README.md / docs/WALKTHROUGH.md | docs only, no gate run |
| B (this) | N-3 (README expected tail; `Audit.lean` sentences + header), this record, the README records list | FULL gate green (§6, run at this tree with the `Audit.lean` change; the remaining edits are docs) |

Every decision below is [AGENT] unless tagged. Quoted text is verbatim;
derived tallies are labelled.

## 1. Finding → fix → location

| Finding | Fix | Location |
|---|---|---|
| N-1 (ARCHITECTURE overstates direct engine reference by exports) | The overbroad sentence replaced by the reviewer's sentence verbatim (§2); `prod_run_eqJ` described as generic collapse machinery with the package-defined delivery premise `DriverDoneAt` (ProdLoop.lean) and the label tie `LabeledAt`; "closed shipped-driver statement" reserved for the four discharged production theorems, named; the four's `prodFile` wrapper and the input-dependent in-budget bounds (`hfuel`) stated | ARCHITECTURE.md §1 and §6 (root-of-trust lane); README first paragraph and "Where the headline claim rests"; WALKTHROUGH §1.2 (the exhibit), §1.3 ("The two lanes, labelled"), §5 ("The production entry") |
| N-2 (`prodMem₀_launchCoh` is not a global well-formedness theorem) | "globally well formed" replaced by the concrete claim (§3); `prodMem₀_launchCoh` cited only for `LaunchCoh` at the empty footprint and any fitting plan; "globally well formed" reserved for the future `MemWF` invariant and its initialization proof | ARCHITECTURE.md §7 (freshness bullet); README register row (freshness); WALKTHROUGH §4 ("Freshness is footprint-relative") |
| N-3 (the checked-in audit-count transcript is not reproducible) | Diagnosed by measurement (§4): the totals depend on the semantics workspace's build state, and the two workspaces differ at the same pin; fixed totals removed from the README's expected tail (the only expected tail — WALKTHROUGH §6 and ARCHITECTURE.md point at it and quote no totals); the stable verdicts shown; `Audit.lean`'s sentences reworded so the verdict leads and the count is labelled informational | README "How to build and verify"; `CerberusHeapLang/Audit.lean` (two `logInfo` strings, header paragraph) |
| N-4 (the known generated concurrency `sorry` belongs in the normative trust story) | The qualification added (§5) to every trust section; "declares no axiom" made exact: no `axiom` declaration, one generated `sorry` | ARCHITECTURE.md §6 ("THE ONE KNOWN ADMISSION IN THE PINNED SEMANTICS TREE"); README "What you are asked to take on faith" (the semantics bullet made exact + a new bullet); WALKTHROUGH §6 |
| Next action 1 (keep mirror completeness and the shipped-driver generic adequacy theorem as explicit open acceptance items) | Both listed by name, each with the condition that closes it; the PROVISIONAL label stays until then | ARCHITECTURE.md §7 (first two bullets) |

Not touched: `Heap.lean`'s header (STATE INTERPRETATION paragraph) still
reads "the production cold-start state is globally well formed,
`prodMem₀_launchCoh`" — a module comment, outside the docs-only remit and
not among the surfaces the re-review names; recorded in §7 for the
orchestrator. `docs/DECISIONS.md`, the review records and the AR-3 record
are untouched (the historical totals they quote stay as quoted).

## 2. N-1 — the sentences placed

The reviewer's sentence, verbatim, on ARCHITECTURE.md §1, README's first
paragraph and WALKTHROUGH §1.3:

> Every exported execution theorem is either explicitly provisional over
> driveU or reaches the shipped engine; every public logical rule has a
> kernel-checked adequacy path through the package mirror to the engine.

ARCHITECTURE.md §1 adds the gloss: "(The reusable rules and assertion laws
are statements in Iris over the mirror `Step` and the ghost resources, §3,
§6; what makes them statements about the engine is that adequacy path, not
their own text.)" Removed: "every exported theorem is a statement about the
engine's execution and memory states" (ARCHITECTURE.md §1) and "whose
exported theorems are statements about the execution and memory states of
the cerberus-lean engine" (README first paragraph). Grep for "statement
about the engine" / "statements about the execution" over
`cerberus-heaplang/{ARCHITECTURE,README}.md` and `docs/WALKTHROUGH.md`
after the edit: zero hits (the dated records keep theirs).

`prod_run_eqJ`, on ARCHITECTURE.md §6: "generic collapse machinery, not a
closed statement: its premise `hdd` is the package-defined delivery fact
`DriverDoneAt` (ProdLoop.lean) that the total judgment supplies, its
premise `hQe` is the package-defined label tie `LabeledAt`, and it carries
the in-budget bound `k + 2 ≤ lemDefaultFuel` on the certified step count."
The premises quoted from the current tree (ProdEntry.lean):

```lean
theorem prod_run_eqJ (sup : Nat) (e : CoreExpr) {Q : LabelMap}
    (hQe : LabeledAt ((initial_core_run_state sup
      (collect_labeled_continuations_NEW (prodFile e))).1) mainSym Q)
    (ψ : value → Mem → Prop) (k : Nat)
    (hdd : DriverDoneAt mainSym Q (prodThread e) e [fmapEmpty] prodMem₀ ψ k)
    (hfl : k + 2 ≤ lemDefaultFuel)
    (fs : CerbFS.FsState) (args : List String) :
```

"Closed shipped-driver statement" means exactly `exhibitA_prod`
(ProdExhibit.lean), `fib_certified_production`,
`counter_loop_certified_production`, `list_reverse_certified_production`
(ProdLoopExhibit.lean). Their statements mention the package's `prodFile`
wrapper (the reviewer's observation) — now said on every surface — and two
carry an explicit in-budget bound where the certified step count depends on
an input (`fib_certified_production`: `hfuel : 2 * n.toNat + 6 ≤
lemDefaultFuel`; `counter_loop_certified_production`: `hfuel : 6 * n.toNat
+ 8 ≤ lemDefaultFuel`); none carries a termination hypothesis. The AR-3
record's list of "root-of-trust exports" included `prod_run_eqJ`; the
current surfaces no longer call it one.

## 3. N-2 — the replacement

On all three surfaces, in substance identical (the ARCHITECTURE.md §7
text): "The production cold-start state `prodMem₀` contains only the
allocator-created errno allocation and no dead allocations
(`prodMem₀_allocations`, `prodMem₀_deadAllocations`, ProdEntry.lean);
`prodMem₀_launchCoh` proves `LaunchCoh` for the empty footprint and any
fitting plan, and no more. "Globally well formed" is reserved for the
future `MemWF` invariant (allocation-id discipline, live/dead consistency,
range disjointness of all live allocations, cursor bounds) and its
initialization proof, registered for the malloc/free extension."

The three theorems, verbatim from ProdEntry.lean:

```lean
theorem prodMem₀_allocations :
    prodMem₀.allocations =
      (({} : Mem).allocations.insert 0 errnoAllocRec) := rfl

theorem prodMem₀_deadAllocations : prodMem₀.deadAllocations = [] := rfl

theorem prodMem₀_launchCoh (reqs : List AllocReq)
    (hfit : PlanFits fmapEmpty ⟨prodMem₀.lastAddress, prodMem₀.nextAllocId⟩ reqs) :
    LaunchCoh fmapEmpty prodMem₀ (∅ : SpikeHeapF SpikeCell) reqs := by
```

## 4. N-3 — the diagnosis, measured

**The two totals.** The AR-3 record and the README quoted `2249 theorems /
3536 constants`; the re-reviewer's fresh build at the same revision printed
`2210 / 3474`. Both runs: 116 pins, every verdict green.

**Where each number lives.** Lake stores the recorded log of a module in
its `.trace`; reading `cerberus-heaplang/.lake/build/lib/lean/CerberusHeapLang/Audit.trace`
(read-only) in each checkout: the primary `refined-cerberus` checkout (at
`b34998d`, the reviewer's environment) records `2210 theorems` /
`3474 constants`; the `audit-response-3` and `audit-response-4` worktrees
record `2249` / `3536`. The `heaplang-alloc-arc` worktree (pre-L-1 sweeps)
records `1158` / `1950`.

**Fresh vs replay is NOT the cause.** In this worktree: the primed replay
(`lake build`, no-op, 0.58 s wall) printed `2249 / 3536`; then
`cerberus-heaplang/.lake/build` was deleted and the package rebuilt from
scratch (`../scripts/capped ~/.elan/bin/lake build`, 34 modules built, 29.3
s wall, exit 0), verbatim:

```
info: CerberusHeapLang/Audit.lean:206:0: CerberusHeapLang export pins: 116 trio-exact
info: CerberusHeapLang/Audit.lean:206:0: CerberusHeapLang axiom sweep: 2249 theorems (internal details included) bounded by the trio
info: CerberusHeapLang/Audit.lean:206:0: CerberusHeapLang banned-axiom sweep: 3536 constants of every kind (internal details included) checked; sorryAx/ofReduceBool/ofReduceNat absent from all cones
Build completed successfully (446 jobs).
```

Same totals fresh and replayed. (The brief's ≤ 2 builds: this fresh build
and the FULL gate of §6 — whose gate 3 rebuilt all 34 package modules
again, see §7, and printed the same `2249` / `3536`: three fresh
measurements in this worktree, one replay, all equal.)

**The delta, named.** A scratch script (not retained) listing every
constant the sweeps count — module of origin under `CerberusHeapLang`,
with kind — was run against three environments: this worktree primed,
this worktree fresh, and the primary checkout's built tree (read-only,
via `LEAN_PATH` pointing at its `.lake`/`.cerberus-ws` outputs; nothing
written there). Primed = fresh, byte-identical (3536 lines: 2249 `thm`,
1058 `def`, 163 `ctor`, 33 `induct`, 33 `rec`). Primary = 3474 lines
(2210 `thm`, 1035 `def`). `diff primary fresh`: 62 lines added, 0 removed
— 39 theorems + 23 definitions, ALL of module `CerberusHeapLang.ListRevExhibit`
and all auxiliaries of `CerbMem` functions (derived classification):
34 `…match_N.eq_N` equation lemmas, 4 `…_sparseCasesOn_N.else_eq`, 1
`CerbMem.reconstructValue_lemFuel.eq_def`, 18 `…match_N.splitter`
definitions, 5 `…splitter._sparseCasesOn_N`; the functions:
`reconstructValue_lemFuel` (40), `sizeofCtype_lemFuel` (5),
`splitBytesProv` (3), `memberAlign_lemFuel` (3), `offsetsofMembers_lemFuel`
(2), `offsetsof_lemFuel` (2), `memValueToBytes_lemFuel` (2). Example
names: `_private.CerberusHeapLang.ListRevExhibit.0.CerbMem.reconstructValue_lemFuel.match_18.splitter`,
`_private.CerberusHeapLang.ListRevExhibit.0.CerbMem.memValueToBytes_lemFuel.match_1.eq_1`.
These are declarations Lean realizes on demand (`split`/`simp` on a
`match`) for DEPENDENCY definitions while elaborating a package module,
stored in that module's `.olean` with the package module as origin —
hence counted — unless the imported environment already carries them.

**The environmental input, identified.** The two semantics workspaces
are at the same pinned commit (`git rev-parse HEAD` in both
`.cerberus-ws`: `ddcfc919972a31bc43a0454e6b2e76a19e6c4594`) but their
primed, gitignored `lean_frontend/generated/` trees differ in exactly one
file, `CerbMem.lean` (`diff -rq`): this worktree's is 2,221 lines and is
byte-identical to the pin's tracked hand-written source
(`git show ddcfc91…:lean_frontend/CerbMem.lean | diff -` → 0 lines);
the primary checkout's is 2,559 lines and is byte-identical to
cerberus-lean `4cb8c4ee9`'s (`git show 4cb8c4ee9:lean_frontend/CerbMem.lean
| diff -` → 0 lines) — the mem-scale arc's C3 change ("DOCUMENTED
DIVERGENCE (mem-scale C3, 2026-09-02)": the struct arm of
`memValueToBytes_lemFuel` made linear, plus the reference form
`memValueToBytes_append_lemFuel` and the equality theorem
`memValueToBytes_lemFuel_eq_append`; `git diff --stat ddcfc91 4cb8c4ee9 --
'lean_frontend/*.lean'`: `lean_frontend/CerbMem.lean | 368 +++…--`, 353
insertions, 15 deletions). The `.primed-from` stamps say when and from
what: worktree `ddcfc919972a31bc43a0454e6b2e76a19e6c4594 2026-09-02T01:54:34Z`;
primary `4cb8c4ee9f138ae474a08ad5d6b2c38db823ded4 2026-09-02T15:15:54Z`.
33 of the workspace's semantics `.olean.hash` files differ accordingly
(and 3 LemLib ones; LemLib is at the same `045dcb0` in both). The mechanism,
measured: a second scratch script (not retained) counted, in each
environment's `CerbMem.olean` (read-only, `import CerbMem` only), the
`CerbMem`-origin match auxiliaries of `reconstructValue_lemFuel`,
`memValueToBytes_lemFuel`, `sizeofCtype_lemFuel` and `splitBytesProv`:
29 against the pin's `CerbMem.lean`, 106 against the C3 one (e.g.
`_private.CerbMem.0.CerbMem.reconstructValue_lemFuel.match_1.eq_1`,
`_private.CerbMem.0.CerbMem.memValueToBytes_lemFuel.match_16.splitter`) —
the C3 file's own kernel-checked equality proof realizes them inside
`CerbMem`. ListRevExhibit then finds them in the imported environment and
does not realize package-origin copies, so the totals drop by 39 / 62
while every verdict and all 116 pins are unchanged.

So the totals are a census of auxiliary declarations that depends on
the dependency's build state, not a property of the package's source —
the brief's hypothesis (auxiliaries "generated on demand vary") holds,
but the varying input is the semantics workspace, not fresh-vs-replay.

**The fix.** README's expected tail now shows the pin count and the two
verdict phrases with the totals as `N`/`M`, labelled informational and
environment-dependent, and points here. `Audit.lean`'s two sentences
now lead with the verdict and label the count (the change is text only;
the checks are untouched):

```lean
  logInfo s!"CerberusHeapLang axiom sweep: every theorem bounded by the trio ({swept} swept, \
    internal details included — count informational, environment-dependent)"
```

```lean
  logInfo s!"CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all \
    cones ({checked} constants of every kind swept, internal details included — count \
    informational, environment-dependent)"
```

The header paragraph "THE SCOPE IS EXACT" gains the sentence that the
totals are informational, with the two measured values and this record's
path. The `#eval` moved from line 206 to line 216 (header growth), so the
message prefix is now `Audit.lean:216:0`.

**A finding beyond N-3, for the orchestrator (§7).** The primary
checkout's `.cerberus-ws` is primed from cerberus-lean `4cb8c4ee9`, not
from the pin, although its clone is checked out at the pin. The prime
script's content guard (`scripts/setup-cerberus-dep.sh`, `CONTENT_PATHS`:
`frontend lean_frontend/generated lean_frontend/native
lean_frontend/lakefile.toml lean_frontend/Makefile Makefile`) passed
(`git diff --quiet ddcfc91 4cb8c4ee9 -- <paths>` exits 0, measured) because
the hand-written seams `lean_frontend/*.lean` that `make lean-prelude-src`
copies INTO `generated/` (`lean_frontend/handwritten_copy.manifest`) are
not in the list, and `generated/` itself is gitignored. The re-reviewer's
"fresh full build at exactly b34998d" therefore elaborated
cerberus-heaplang against the C3 `CerbMem.lean` — green, 116 pins, so the
package's theorems hold against both texts of the memory model — but the
primary checkout's build is not a build against the pin's semantics.
This record changes nothing there (read-only; outside the remit).

## 5. N-4 — the paragraph placed

ARCHITECTURE.md §6, verbatim (README's "What you are asked to take on
faith" bullet and WALKTHROUGH §6 carry the same content in their own
sentences; README's "Neither the semantics workspace nor its lem runtime
(`LemLib`) declares an axiom" became "… contains an `axiom` declaration;
the semantics tree does contain one generated `sorry` (next bullet)"):

> THE ONE KNOWN ADMISSION IN THE PINNED SEMANTICS TREE. The pinned
> cerberus-lean tree declares no `axiom`, but it contains one generated
> admission: two `(sorry : String)` terms in the debug-log branch of
> `auxAddToRfLoad` in the generated concurrency model (`Cmm_op.lean`;
> Lean reports `declaration uses sorry` for it during the build). It is
> outside every current export cone: the package sweep (Audit.lean)
> establishes that `sorryAx` reaches no `CerberusHeapLang` constant.
> Concurrency is out of scope for this package (`drive fmapEmpty false
> …` in every production statement). The admission must be closed
> upstream or separately bounded before any concurrency or whole-engine
> claim is made on this semantics; it is reported to the cerberus-lean
> team in `../docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md`.

The build line it refers to, verbatim from this slice's fresh build and
from the FULL gate: `warning: generated/Cmm_op.lean:283:5: declaration
uses `sorry``. The pinned file (this worktree's `.cerberus-ws`,
`generated/Cmm_op.lean`, the `auxAddToRfLoad` definition) contains the
two terms `((sorry : String))` inside `String.append "CONCUR CHOSE ==> " …`;
the sweep line `sorryAx/ofReduceBool/ofReduceNat absent from all cones`
is the measured exclusion.

## 6. The FULL gate (run at this tree, after the `Audit.lean` change; the
remaining edits of this commit are docs)

`scripts/test_unit.sh` through `scripts/capped` (gates 2-3 and the
manifest run are `capped` invocations), exit code 0. Verbatim: the gate
headers and verdicts, then the tail.

```
== gate 1: banned proof-method grep (native_decide / bv_decide / ofReduce*) ==
ok: no banned proof-method references
== gate 2: capped build, root package (elaborates its axiom audit) ==
ok: root build green
== gate 3: capped build, cerberus-heaplang (elaborates its axiom audit) ==
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
scripts/test_unit.sh  374.46s user 26.17s system 158% cpu 4:12.05 total
exit 0
```

```
ℹ [444/446] Built CerberusHeapLang.Audit (1.2s)
info: CerberusHeapLang/Audit.lean:216:0: CerberusHeapLang export pins: 116 trio-exact
info: CerberusHeapLang/Audit.lean:216:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (2249 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:216:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (3536 constants of every kind swept, internal details included — count informational, environment-dependent)
✔ [445/446] Built CerberusHeapLang (710ms)
Build completed successfully (446 jobs).
ok: cerberus-heaplang build green
== speedbump: capability manifest (regenerate; red on a red row or drift) ==
cerberus-lean-proj env: switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam, git redirects active
ok: capability manifest regenerated, no drift
== speedbump: import direction (semantics → heap → rules → adequacy → clients) ==
ok: import direction — no core module imports an exhibit/example/production module
ALL GATES GREEN
scripts/test_unit.sh  374.46s user 26.17s system 158% cpu 4:12.05 total
exit 0
```

## 7. Borderline, for the orchestrator

- **`Heap.lean` header still says "globally well formed".** The STATE
  INTERPRETATION paragraph of `CerberusHeapLang/Heap.lean` reads "(the
  production cold-start state is globally well formed,
  `prodMem₀_launchCoh`)". A module comment; not on the re-review's list
  of surfaces; outside this slice's docs-only remit (editing it rebuilds
  the package from `Heap` down). Recommended: the N-2 wording, next
  code-touching slice.
- **The primary checkout's semantics workspace is primed from
  `4cb8c4ee9`, not the pin** (§4): its clone is at `ddcfc91…` but its
  `generated/CerbMem.lean` is cerberus-lean `4cb8c4ee9`'s (mem-scale C3),
  stamped `.primed-from 4cb8c4ee9… 2026-09-02T15:15:54Z`. The prime
  script's content guard passed because `lean_frontend/*.lean` (the
  hand-written seams copied into `generated/` per
  `handwritten_copy.manifest`) is not among `CONTENT_PATHS` and
  `generated/` is gitignored — a fail-open gap in
  `scripts/setup-cerberus-dep.sh`'s guard. Consequences: the re-review's
  "fresh full build at exactly b34998d" ran against the C3 memory model
  (green, 116 pins — the package holds against both texts), and N-3's
  discrepancy is this and nothing else. Nothing was changed outside this
  worktree; the fix (add the manifest's files to the guard, and re-prime
  or re-pin the primary deliberately) is a decision for the operator.
- **The FULL gate rebuilds the shared semantics dependency twice.** Gate
  2 (root package) "Built" 28 `.cerberus-ws` modules (`Loc` … `CerbMem`)
  that gate 3 (cerberus-heaplang) then "Built" again along with 33 more
  (`Loc` … `Driver`, `CerbND`) and all 34 package modules — the two Lake
  workspaces compute different traces for the same path dependency
  (same pins and `moreLeanArgs`; the trace inputs include per-workspace
  `CerberusLean:extraDep` / `importAllArts` hashes). Cost: the 4:12 gate
  is mostly this (a no-op package replay is 0.6 s, a fresh package build
  29 s). Not a trust matter (the counts and pins are identical either
  way, measured); a perf/hygiene item for whoever owns the gate.
- **`Audit.lean` message prefix moved** from `:206:0:` to `:216:0:`
  (header growth). Dated records quoting `206` are historical and
  untouched.
- **The worktree's `.cerberus-ws` has an untracked `lean_frontend/native/native/`**
  (the nesting the prime script's comment calls inert); the primary's
  has `native/*.o` files the worktree's lacks. Neither feeds the library
  build.
- The scratch dir `.ar4-scratch/` (three name dumps, the fresh-build
  and gate logs) and the two scratch scripts were deleted at slice end;
  everything load-bearing from them is quoted above.
