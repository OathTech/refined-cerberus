# Dependency and fuel update: preflight — 2026-09-06

[AGENT, active demo-completion goal] Read-only preparation for M2 while
the E5 review scope/dispatch decision is pending. This is a source and
contract inventory, **not a compatibility build or a completed scout**.
The reviewed candidate remains `f60cdcf`; its review brief is committed
at `7191dec`. No dependency pin, sibling source or build artifact changes
in this preflight.

## Measured starting points

- The current demo pin is `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`.
- The clean cerberus-lean primary is at
  `89f7e688530c6910884518811d645e4e892e4507`, 109 commits after that pin
  (`git rev-list --count`, derived count). Relative to its handoff's
  recommended target `0a62dd7f7`, only the handoff document changed.
- The clean lem-lean primary is at
  `f6542f8e6860d12d4655e6648bc4c45dabd1d798`. That is also the current
  cerberus-lean Lake requirement. The semantics package still selects
  Lean 4.32.2; lem-lean's standalone package selects 4.28.0, so consumer
  builds must continue selecting the semantics/demo package toolchain.
- The old scout `07ceb44` measured an older consumer and older semantics
  `de2fbf1`, with LemLib `3c88f0d`. Its 41-site breakage count and 2.5–4-day
  forecast are historical, not measurements or estimates for this update.

These heads were read from the actual repositories, not inferred solely
from their handoffs. Recheck them before creating the new dependency
workspace; choose a concrete target and record any movement.

## Current interfaces and their consequences

**Fuel.** LemLib now declares `class LemFuel where fuel : Nat`; no global
library instance supplies a default. Generated drive and the ND runners
accept the ambient instance. The old `lemDefaultFuel`,
`CerbFuel.driverFuel` and hand-written `CerbND.drive_lemFuel` interface
are retired upstream. Quantify the current interface and prove sufficient
bounds; do not restore a hidden numerical default to make old proofs
compile. Low-fuel setup/runner cases belong to the partial theorem's
exhaustion classification, not only the old outer driver loop.

**Measured traversals.** The current generated `get_ctx` is
`get_ctx_lemFuel (generic_expr.lemSize g + 1) g`; `one_step_unseq_aux`
and `get_ctx_unseq_aux` likewise select their proved structural bounds.
The old static-potential assumptions may become removable or change their
role. Use the upstream sufficiency theorems rather than substituting an
ambient fuel number into every old proof site. Measure the actual needs
of `step_eval_pexpr` and the remaining ambient callees separately.

**Finite maps.** `LemLibPmapLaws` now provides `Pmap.CmpLaws`, `Pmap.WF`,
`WF_add`, `find?_add_same` and `find?_add_other` against the actual Pmap
implementation. The old request to invent the missing lookup-after-insert
proof is discharged upstream. The consumer still needs to establish its
symbol comparator laws and carry the map-order invariant, and to check
collector/registration computations on the changed map representation.
No current build result for those repairs is claimed here.

**Layout and tag hypotheses.** Layout and byte reconstruction are now
measured wrappers. Their sufficiency theorems require
`CerbTagsWf.Acyclic` or `AcyclicPair`, with rank decreasing along resolved
by-value tag references. Discharge those conditions where a used theorem
requires them, including concrete empty or finite tag tables; do not add
an axiom or presume a proved frontend invariant. The upstream C4 manifest
also records an accepted ill-formed alignment example for which acyclicity
fails. Direct statements about the wrapper and use of its conditional
sufficiency theorem are distinct claims. Integer byte-image proofs should
be rechecked against the measured wrappers.

**Configuration.** `CerbGlobal`'s configuration readers now unfold to the
default configuration, with public equality lemmas. Update the demo's
opaque-configuration explanation and any switch-general wording when the
pin moves. Recheck the changed kill/refusal arms and memory-well-formedness
proofs; old no-change observations about driver/fuel code no longer apply.

**Full-file connection.** A7 remains a required charter item. During the
scout, inspect the current whole-file construction and available Core
parsing/serialization path, including stdlib, impl, tags and procedure
maps. Choose a direct emitted-file certificate, a faithful complete
transcription with an executable equality check, or a proved preservation
bridge. The current four main-body skeleton matches are not evidence that
this seam is closed.

## Next concrete action

Create an isolated scout worktree from the completed E5 candidate, leaving
the review candidate and its pinned workspace intact. Target the current
clean semantics head and its exact LemLib requirement. Use the repository
setup script to prime the dependency with its stamp/seam checks; update
only the scout's dependency manifest deliberately and inspect its diff.
Run a capped package build to measure the first failure frontier, then
separate representation, fuel and semantic-statement obligations. Do not
land stubs or claim compatibility from a partial build. A re-pin commit
must include the repairs and their validation.

Keep the review request pending; no reviewer is dispatched by this
preflight. The M2 build/repair work can proceed independently of that
approval, provided the E5 review referent remains stable. No time or
breakage estimate is made before that measurement.

Sources read: the sibling cerberus-lean handoff and consumer change
manifests `2026-09-04_fuel-parameter-C1-change-manifest.md`,
`2026-09-04_fuel-parameter-C2-change-manifest.md`,
`2026-09-05_fuel-parameter-C3-change-manifest.md`,
`2026-09-05_fuel-parameter-C4-change-manifest.md`,
`2026-09-05_cerbglobal-defs-change-manifest.md`, checked against the live
LemLib/Pmap laws, CerbFuel, generated Core_reduction/Driver and CerbMem
source where described above. These are upstream records, not fresh local
validation results. The active charter remains unfinished.
