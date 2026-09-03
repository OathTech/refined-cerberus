# Request to the lem-lean team: `Pmap` laws, a reducing `join`, and the fuel scheme

Requester: refined-cerberus / cerberus-heaplang (the separation-logic demo
over Cerberus Core; every export is a theorem about the shipped
cerberus-lean pipeline, whose generated code and runtime LemLib are yours).
Pins at the time of the request: cerberus-lean `f95ef8d9c` (LemLib
`045dcb0`); the re-pin under preparation targets cerberus-lean `de2fbf1bd`
(LemLib `3c88f0d`, the parity-fix mainline). Measurements below are from
the re-pin scout `docs/2026-09-03_repin-scout-2.md` (same repository) and
from the fuel discussion recorded in `docs/DECISIONS.md` (2026-09-03).
Provenance: the fuel item is a [USER 2026-09-03] ruling ("this a defect in
the cerberus-lean semantics. The correct way to do this is for the
semantics to take fuel as a parameter, and for the executable interpreter
to pick 10^8 if it wants to (it doesn't matter)"), already raised with the
cerberus-lean team by the operator; items 1–2 are [AGENT] recommendations
the operator asked to have written up. Nothing here asks for a change of
behaviour: every item is about what a consumer can PROVE about the code
you already generate.

## 1. A lookup-after-insert law for `Pmap` / `Fmap` (needed; blocks the re-pin)

At `3c88f0d`, `Fmap α β` is `inductive Fmap | empty | mk (cmp) (m : Pmap α β)`
over the verbatim pmap.ml AVL port (`LemLib.lean:755`, `:1052`), with
`fmapAddBy cmp k v` = `Pmap.add` and `fmapLookupBy _ k` = `Pmap.find? c k m`
under the CAPTURED comparator (`:1071`, `:1076`). The generated Core
environments (`Fmap sym value`) are exactly these maps, and our
environment laws (the referents of pinned exports `symAdd_lookup`,
`symAdd_lookup_two`, `envAdd_lookup`; `EnvLaws.lean`) were proved against
the previous `Std.TreeMap`-backed representation. They now need, for a
comparator `cmp` that is a strict total order (as every generated
comparator is):

    find?_add_same : Pmap.find? cmp k (Pmap.add cmp k v m) = some v
    find?_add_other : cmp k k' ≠ EQ → Pmap.find? cmp k (Pmap.add cmp k' v m) = Pmap.find? cmp k m

(equivalently at the `Fmap` level for `fmapLookupBy`/`fmapAddBy`), plus
whatever well-formedness predicate they need (`Pmap.add` preserves it;
`Empty` has it) — or, if you prefer to state them without an invariant,
through `bindings`: `Pmap.bindings` is sorted under `cmp` and `find?`
agrees with membership in `bindings`. `LemLibTheorems` at `3c88f0d` ships
no `Pmap`/`Pset` law (measured). The AVL rebalancing (`bal`, `create`,
`add`) makes these case-heavy but classical; they belong next to the
port, once, rather than in each consumer. We will carry a local proof
in the interim if the re-pin must not wait; we would replace it by yours.

## 2. A structurally recursive `Pmap.join` (needed for definitional computation)

`Pmap.join` (`LemLib.lean:915`, pmap.ml:185) is defined by well-founded
recursion (`termination_by sizeOf l + sizeOf r`). WF-recursive
definitions do not reduce by `rfl`/`decide`/`dsimp` in the kernel, so
every generated function that reaches `join` — `fmapUnionBy`,
`fmapDeleteBy`/`remove`, `Pset.union`/`remove` — stops computing on
closed terms. Measured consequence on our side at `de2fbf1bd`: 17
declarations in 7 files (the C4 procedure-registration lemmas and every
`collect_saves`/`collect_labeled_continuations` computation on closed
programs, previously `:= rfl`) fail with `Type mismatch rfl`; the
workaround is equation-lemma rewriting per site, and any future proof
that computes an engine map through these functions hits the same wall.
Request: define `join` by structural recursion — e.g. on the AVL height
already stored in `Node` (`join` recurses only into a subtree of the
taller side, so a height fuel `h := lh + rh` or `max lh rh + 1` suffices
and is exact, not a 10^k constant), or via a `fuel` argument instantiated
from the heights at the call sites — so that the OCaml-mirroring
behaviour is unchanged and closed terms reduce. Zero behavioural change;
this is about kernel computability only.

## 3. The fuel scheme (raised by the operator; consumer requirements)

The backend seals each fuelled `let rec` behind a fixed wrapper
(`f := f_lemFuel 100000000` in the generated Driver.lean for `driver2`,
`drive_nonmemory_steps_aux2`, `hack`, `print_eval_conv_aux`, and
`nd_bind`; `lemDefaultFuel = 1000000` (`LemLib.lean:57`) for the rest).
Two constants, ≥ 6 sealed recursions (derived counts, scout + DECISIONS).
The ruling: fuel is an artifact of totality, not of the C semantics; the
semantics should take fuel as a parameter and the executable pick a value
once. What a consumer needs from the resulting scheme, stated as
properties rather than a mechanism:

- **One fuel position, quantifiable.** A single parameter (module-level
  or a typeclass-style instance argument — not per-signature threading,
  which would change every generated signature) read by EVERY fuelled
  recursion; the executable entry is its instance at the chosen constant
  by `rfl`. With that, a partial-correctness theorem is `∀ fuel, …` and a
  total one `∀ fuel ≥ bound, …`, and the constants disappear from
  statements (ours currently carry `≤ CerbFuel.driverFuel` and
  `≤ lemDefaultFuel` hypotheses at ~60 sites — the same defect, inherited).
- **A single, kernel-transparent exhaustion outcome** — the `_zero`
  lemma pattern cerberus-lean already gives for the driver
  (`fuelExhaustedKill`, `rfl`), for every fuelled function, so
  "exhausted" is recognisable in the kernel wherever it arises.
- **Fuel monotonicity as a generated or generic theorem**: if a run
  completes at fuel `f` it completes identically at every `f' ≥ f`. This
  is what turns "done at the bound" into "done for all fuel above it";
  the scheme is uniform, so the backend is the right place to guarantee
  it (per-function lemma, or one generic lemma over the fuel scheme).
- **Interface, not mirror.** On the zero-discrepancy axis fuel is
  invisible (OCaml diverges where Lean exhausts), so this is a defect of
  the port's reasoning interface, not an execution discrepancy; we flag
  it so it is filed in the right register on your side.

## What we will do on our side

Items 1–2: re-pin slice, one change at a time (record: the scout §6
plan); local `Pmap` law only if yours is not available in time. Item 3:
when the fuel-parametric semantics lands, one restatement slice — every
closed export becomes fuel-parametric, shipped-constant versions become
corollaries; thread-level lemmas unchanged. Until then our closed forms
are documented as instances at the shipped budgets.
