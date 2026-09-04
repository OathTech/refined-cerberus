# Reynolds--O'Hearn Separation Logic Audit

Date: 2026-09-04

## Executive verdict

The core logic appears sound and substantially faithful to a
Reynolds--O'Hearn-style separation logic. This audit found no obvious
kernel-level soundness hole, circular headline theorem, vacuous adequacy result,
or example that proves its program specification by bypassing the logical rules
and reasoning directly about `Step`.

In particular, the implementation has several strong features:

- fractional authoritative heap ownership;
- local load, store, allocation, kill, and free rules;
- a frame rule that frames label specifications as well as heap resources;
- guarded recursive procedure specifications;
- distinct partial- and total-correctness judgments;
- adequacy to the generated Cerberus execution engine; and
- an actual negative total-correctness result for divergence, rather than merely
  a fuel-exhaustion example.

Nevertheless, the project does not yet meet all of its stated design goals. The
principal problems found here are not false logical rules, but overclaimed
capability coverage, leakage of implementation-specific Iris resources into
examples, and an unnecessarily closed top-mask-only statement logic.

The overall assessment is:

> A credible and unusually careful research implementation whose supported
> fragment looks logically sound, but whose public coverage and abstraction
> claims are currently stronger than its machinery justifies.

The capability-reporting defect should be fixed before treating "0 red" as
evidence that the logic covers the complete supported language. The example/API
abstraction issue should follow. Mask generalization is less urgent for classic
sequential separation logic, but important if using Iris to its full extent is
an actual design requirement.

## Scope and verification status

This review covered the architecture, heap model, partial and total
weakest-precondition judgments, local rules, procedure and label specifications,
driver collapse and adequacy, semantic triple projection, capability scripts,
API boundary documentation, and representative positive and negative examples.

The pinned Cerberus dependency check passed, including the byte-for-byte seam
synchronization checks.

The repository's mandated capped build was attempted. The static policy checks
and import-direction gate passed, but the Lean build could not start because the
`nono` OS sandbox denied access to the delegated cgroup and the systemd user bus.
The repository's prohibition on an uncapped Lean build was not bypassed.
Consequently:

- this is a source-level and dependency-level audit;
- it does not independently certify fresh elaboration of the current checkout;
  and
- the absence of `sorry`, `admit`, `axiom`, and `unsafe` in package sources was
  confirmed statically, but the in-build axiom gate was not freshly executed.

## What is working well

### 1. The resource model is recognizably separation logic

The heap interpretation is not merely a predicate over semantic memory. It uses
authoritative Iris ownership, view fragments, and fractional cell ownership,
with actual splitting and recombination laws. See
[`Heap.lean`](../cerberus-heaplang/CerberusHeapLang/Heap.lean).

That supports the key intended property: examples reason locally about owned
resources rather than obtaining arbitrary facts from the concrete Cerberus
memory state.

### 2. Atomic rules are derived from a common logical interface

`AtomicStep` and `wp_of_atomic` provide a uniform bridge from an executable
Cerberus action to an Iris rule, including reducibility, mask transitions, state
interpretation, and the later modality. See
[`Rules.lean`](../cerberus-heaplang/CerberusHeapLang/Rules.lean).

The load, store, allocation, kill, and free rules are then lifted into both
statement judgments. This is considerably better than proving each rule by
unrelated semantic case analysis.

### 3. Partial and total correctness are meaningfully distinct

The partial judgment is a guarded fixed point with separate value, jump, call,
and ordinary-step cases; see
[`Wps.lean`](../cerberus-heaplang/CerberusHeapLang/Wps.lean).

The total judgment is indexed by a well-founded budget and charges delivery,
jumps, calls, and ordinary steps; see
[`Wpt.lean`](../cerberus-heaplang/CerberusHeapLang/Wpt.lean). This is not just
partial correctness with an informal termination claim attached.

### 4. Frame reasoning covers control abstractions

The frame infrastructure handles label specifications rather than framing only
heap assertions. This matters for non-structured Cerberus control flow and is a
good adaptation of classic local reasoning to the actual semantic language.

### 5. Adequacy proves the right kind of property

The semantic triple quantifies over arbitrary disjoint frames and preserves the
same frame in the result. The final projection to memory triples is therefore
based on a genuine frame-preserving safety result, rather than a closed-state
execution theorem disguised as a Hoare triple. See
[`Adequacy.lean`](../cerberus-heaplang/CerberusHeapLang/Adequacy.lean).

`DriverSafeCtl` also rules out ordinary semantic failures: permitted executions
must either stop only through the designated fuel-exhaustion condition or finish
with the postcondition.

### 6. The divergence exhibit addresses the desired theorem

The divergence example does not stop at showing that a particular bounded run
exhausts fuel. It shows that assuming a total logical derivation leads to a
contradiction with the concrete driver behavior. This is the correct shape of
negative validation for a total-correctness logic. See
[`DivergeExhibit.lean`](../cerberus-heaplang/CerberusHeapLang/Examples/DivergeExhibit.lean).

## Findings

| Severity | Finding | Effect |
| --- | --- | --- |
| High | Capability manifest treats constructor-level association as complete logical coverage | "0 red" is not reliable evidence that all supported semantic cases have rules |
| Medium | Example layer names and manipulates internal Iris resources, while its enforcement inventory is incomplete | The advertised public abstraction boundary is not maintained |
| Medium | `wps` and `wpt` hard-code the top invariant mask | Prevents mask-polymorphic and namespace-sensitive Iris composition |
| Note | Adequacy maintains two independently proved semantic bridges | Documented duplication and maintenance risk, not a present soundness defect |

### Finding 1 -- High: the capability manifest overstates rule coverage

The language fragment has broad constructors such as `store`, `kill`, `alloc`,
and `free`. The capability generator associates each entire constructor with one
or more theorem names. See
[`capability_manifest.lean`](../cerberus-heaplang/scripts/capability_manifest.lean).

That association does not establish that a rule covers every successful semantic
form represented by the constructor. In fact, the project already acknowledges
several counterexamples:

- locking stores are representable, but the public store rule is for the
  non-locking form;
- killing a live static region can succeed semantically, but the kill rule is
  restricted to dynamic regions;
- zero-cost allocation can succeed, while the allocation rule assumes a positive
  region cost; and
- `free(NULL)` is a semantic no-op, but the free rule requires a concrete
  dynamic-region ownership resource.

The generated report nevertheless describes these constructor rows as having a
"covering rule" and reports zero red entries. See
[`CAPABILITY_MANIFEST.md`](../cerberus-heaplang/docs/CAPABILITY_MANIFEST.md).

The check itself establishes approximately that:

1. a theorem name is associated with the constructor; and
2. some selected exhibit depends on that theorem.

It does not establish:

- exhaustiveness over constructor parameters;
- coverage of all semantically successful variants;
- coverage of both partial and total judgments;
- that the dependency is part of the exhibit's headline proof rather than
  incidental; or
- that uncovered variants have explicit, reviewable no-rule classifications.

The manifest's `declaredNoRule` set is empty even though the documentation
describes known no-rule cases.

This does not make an existing rule unsound. It does mean the project's primary
advertised coverage measurement is unsound as a coverage metric.

#### Remediation

Replace constructor-level rows with variant-sensitive rule cases. For example,
classify:

- `Store0 false` versus locking store;
- dynamic-region kill versus static-region kill;
- positive-cost versus zero-cost allocation; and
- null, dynamic-region, created-region, and other free cases.

Each semantic case should have exactly one of:

- a partial rule and a total rule;
- a deliberate partial-only classification;
- an explicit no-rule entry with its reason; or
- an explicit out-of-scope classification justified by the defined language
  boundary.

The generated check should fail if:

- a semantically admitted case has no classification;
- a supported case lacks either required judgment;
- a named theorem is missing; or
- a claimed exhibit does not depend on the intended exported rule.

Until that exists, rename the output to a "rule-use manifest" and remove claims
that zero red means complete constructor coverage.

### Finding 2 -- Medium: the client abstraction boundary is not enforced

The API documentation states that examples should not refer directly to `CohG`,
state-interpretation internals, `Step`, or fixed-point unfoldings, and should
obtain semantic conclusions through public consequences. See
[`API.lean`](../cerberus-heaplang/CerberusHeapLang/API.lean).

Most logical proofs respect the important part of that rule: they use `wps` and
`wpt` proof rules instead of semantic transition reasoning.

However, some projection/readout portions cross the advertised boundary:

- [`DisposeExhibit.lean`](../cerberus-heaplang/CerberusHeapLang/Examples/DisposeExhibit.lean)
  defines helpers explicitly in terms of `CohG` and `metaInterp`.
- [`MallocListExhibit.lean`](../cerberus-heaplang/CerberusHeapLang/Examples/MallocListExhibit.lean)
  does the same for lists of dead regions.

These helpers do not appear to exploit a semantic transition fact to prove a
logical triple, so this is not a soundness bypass. Nevertheless, they make
example proofs depend on the concrete ghost-state organization. That weakens the
claim that examples reason exclusively through a clean public logic.

The associated enforcement script also provides less assurance than the
documentation suggests. Its client list contains only a subset of the modules
that the capability report regards as clients, omitting examples such as
disposal and allocation/list developments. See
[`parametric_inventory.lean`](../cerberus-heaplang/scripts/parametric_inventory.lean).

It also contains stale export seeds for declarations that no longer exist.
Missing seeds are rendered as `(MISSING)` rather than making the check fail. This
means the inventory can silently lose its connection to the current public
theorem graph.

#### Remediation

Move multi-object readout results into the public adequacy/projection layer. The
public API should provide generic lemmas along the following lines:

- persistent dead-object facts can be folded over a finite collection;
- a big-separating conjunction of dead-region tokens implies the corresponding
  concrete readout; and
- a postcondition expressed through public ownership assertions projects without
  clients mentioning `CohG` or `metaInterp`.

Then change the positive examples to use only those lemmas.

There should also be one authoritative classification of modules:

- positive logical clients;
- semantic regression tests;
- generated-engine mirror tests;
- production wrappers; and
- negative/unprovability tests.

Both the capability manifest and parametricity inventory should consume that
classification. Every configured export seed should be resolved as a checked
declaration, with a missing name being a hard failure.

### Finding 3 -- Medium: the statement logic is unnecessarily fixed to `top`

The lower-level atomic interface is mask-polymorphic: `AtomicStep` and
`wp_of_atomic` can be used at an arbitrary Iris mask.

The public statement judgments discard that generality. Their definitions
hard-code `top`, and their atomic lifting rules instantiate transitions from
`top` to the empty mask. See
[`Wps.lean`](../cerberus-heaplang/CerberusHeapLang/Wps.lean) and
[`Wpt.lean`](../cerberus-heaplang/CerberusHeapLang/Wpt.lean).

This is adequate for a conventional closed, sequential separation logic. It is
not the most general Iris interface. In particular, it obstructs:

- mask-polymorphic library specifications;
- reasoning while some invariant namespaces are already disabled; and
- nesting the language logic inside a larger Iris development with its own
  invariant discipline.

This should not be described as an inability to use invariants at all: top-mask
atomic reasoning can still open ordinary invariants. The missing capability is
mask-sensitive composition.

#### Remediation

Introduce mask-indexed judgments, for example `wpsE E` and `wptE E`, and define
the current `wps` and `wpt` as convenient top-mask abbreviations.

Thread the mask through:

- the guarded statement functional;
- ordinary-step and atomic rules;
- label and procedure specifications;
- framing and monotonicity rules; and
- CPS collapse and adequacy entry points.

Add at least one regression test that allocates an invariant in a namespace and
proves an atomic memory operation under a mask excluding that namespace. This
would show that the generalization is operational rather than merely syntactic.

## Documented limitations noted in passing

[`KNOWN-OPEN-ITEMS.md`](KNOWN-OPEN-ITEMS.md) already identifies several material
limitations, including:

- fixed upstream execution fuels and a weak outer-fuel formulation for closed
  partial correctness;
- annotation-free authored Core rather than an end-to-end C front-end theorem;
- empty tag-definition and external-environment assumptions in the present
  projection;
- acknowledged no-rule operation cases;
- missing seeded total/tree demonstrations and other coverage gaps;
- no concurrency, function pointers, or modeled external calls;
- residual proof and automation gaps; and
- `Pmap`, dependency pinning, and regeneration concerns.

Those remain important qualifications on any broad statement that this is
already a separation logic "for C", but they are not counted as new findings in
this audit.

The architecture also documents that adequacy and the step-matching layer consume
separately proved versions of the same semantic bridge. See
[`ARCHITECTURE.md`](../cerberus-heaplang/docs/ARCHITECTURE.md). This is not
presently a soundness hole, but it creates duplication and future drift risk.
Eventually, one certified engine-round theorem should feed both the rule layer
and driver collapse.

## Recommended remediation order

1. **Make capability reporting truthful.** Introduce variant-level
   classifications, distinguish partial from total coverage, and turn missing
   declarations or classifications into hard failures.

2. **Seal the public client boundary.** Move collection/readout reasoning into
   exported projection lemmas and unify the module inventories.

3. **Add negative architectural checks.** Positive examples should fail CI if
   they directly mention `Step`, `CohG`, `metaInterp`, statement unfoldings, or
   generated engine transition definitions, except in explicitly classified
   semantic-test modules.

4. **Generalize the judgments over masks.** Preserve top-mask aliases so
   existing examples continue to present a classic Reynolds--O'Hearn interface.

5. **Consolidate semantic bridges.** Remove or factor the duplicate proof path
   between step matching and driver collapse.

6. **Add a small trusted claim matrix.** For every headline claim, record:
   - its exported theorem;
   - whether it is partial, total, semantic, or projected;
   - the examples demonstrating it;
   - its supported operation variants;
   - known exclusions; and
   - the CI check that prevents the claim from becoming stale.

## Final assessment

For the operation variants it actually supports, the central separation logic
appears well designed and appropriately connected to Iris and Cerberus. The
examples' main program proofs generally do reason through logical rules, and the
adequacy results prove substantially the right semantic property.

The project's largest present correctness-of-presentation problem is that its
capability machinery certifies theorem association, not semantic rule coverage,
while being presented as the latter. The most important cleanliness problem is
that some examples still depend on concrete ghost-state internals during
projection. Fixing those two issues would materially improve confidence that the
repository is not only sound, but also says precisely what it has proved.

## Reproducing the blocked build check

To obtain a fresh build audit under `nono`, either restart once with access to
the delegated cgroup, for example:

```text
nono run --allow /sys/fs/cgroup -- codex
```

The allowance should be narrowed to the actual delegated cgroup parent where
possible. Alternatively, create a persistent profile draft under
`~/.config/nono/profile-drafts` and explicitly promote it with
`nono profile promote` after review.
