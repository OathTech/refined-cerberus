# Re-pin: t4, malloc-list and full regression gate — 2026-09-06

[AGENT, active demo charter] The package now passes the full gate at
semantics `89f7e688530c6910884518811d645e4e892e4507`, LemLib
`f6542f8e6860d12d4655e6648bc4c45dabd1d798`, and Lean 4.32.2. This is the
first coherent source/pin checkpoint of the M2 repair, on `demo-repin`
in `worktrees/demo-repin`, following the documentation checkpoint
`1270ed9`. The source checkpoint's commit is the one containing this
record. It is a validated intermediate revision, not M2 acceptance,
charter completion, a review result or a park.

This supersedes the red frontier in the [t5/t6 record](2026-09-06_repin-t5-t6.md).
The derived repair count is 52 previously failing targets and two new
memory modules. All package clients now build. These counts describe
repair progress; they do not measure semantic coverage. Earlier dated
records retain their actual red-gate measurements as history.

## Retained t4

`t4_certified_production` uses the same caller's LemFuel instance in
`CerbND.runND (drive ...)`, requiring ambient fuel at least 917 and
initial symbol supply at least 600. The public total derivation keeps
cost 915 and requires positive ambient fuel for its allocations. The
production result is still exactly one active specified ten, unblocked
with empty stdout and stderr. The file remains
`prodFileLib stdlibE3 [] CorpusE0.t4Main`: A7 is still open.

All four continuations, short-circuit structure, both assignments,
cleanup and return remain. The invariant still owns i = n and
s = sum(0..n−1), n ≤ 5, with budget 159*(5−n)+98. Semantic declarations
now carry LemFuel; the two label-context membership proofs use the
existing sufficient operand bound of forty. Allocation clients supply
positive alignment, no requested address and the actual signed-int
serialization bounds. The assignment helper drops only its obsolete
fixed-default structural ceiling; its RHS proof and effect/freshness
protocol remain. Unused `t4Main_pot` and `t4Q_pot` are removed.

The shipped map tree differs from the old registration equation.
`t4Q_eq` now reduces by reflexivity with insertion order, innermost
first: break, return, while, continue. Its four concrete lookup results
are unchanged; the generic lookup and all-body membership proof use
that exact tree. The program is unchanged.

## Malloc-list

The partial and total logic clients retain the build/free invariant,
region ownership, identity distinctness and dead-region readout. They
now explicitly require positive ambient fuel, positive alignment and
`n.toNat ≤ 9223372036854775807`. The signed-long serializer and byte-image
lemmas carry the real signed-64-bit range. The body derives the current
counter's range from the invariant's count equation. Pointer serialization
uses the actual address bounds already supplied by NodePtrWF.

The production export adds positive alignment but needs no additional
input-size bound: `ml_counter_bound` derives the signed-long bound from
the original allocation-headroom premise
`n.toNat * (15 + max al.toNat 1) ≤ 281474976710647`. Its sufficient ambient
fuel is still `25 * n.toNat + 9`: public cost `25 * n.toNat + 7` plus two
driver iterations. The output remains unit and a list of n distinct dead
allocation identities with absent allocation records, no blocking and
empty stdout/stderr, over actual `runND (drive ...)` at that same fuel.

Body membership needs ambient fuel at least two; save initializers have
pure depth exactly one. Registration is factored by the actual program's
structural size 36 and a collector equation at any worker budget k+7.
These structural facts are kernel proofs independent of ambient fuel.
The program, list predicates, public costs and footprint claims are
retained. No heartbeat or recursion limit was raised.

## Audit and report reconciliation

The inventory of the remaining 893 exact-trio entries found four changes:
`procCtxF_runState_labeled`, `procCtxF_sym_supply`,
`procCtx_runState_labeled`, and `procCtx_sym_supply` now have empty cones.
Their reflexivity proofs are unchanged. Together with the previously
measured `prodThread_eq_ctlThread` and `prodCtx_extern`, they now have an
explicit empty-cone list in Audit.lean. All six retain theorem-existence
and exact-dependency checks. No artificial axiom dependency was added.
The full-theorem trio bound and all-constant banned-axiom sweep are
unchanged. Deleted fixed-default helpers lose their obsolete list slots.

The first full gate found five claim-name diagnostics: two appearances
each of the deleted t4/t6 potential helpers and the retired drive mirror.
The claim matrix now describes actual drive with caller-supplied fuel,
low-budget setup exhaustion, current classification bounds, the A5
kernel/runtime distinction and the retained corpus fuel premises. The
bound-rule manifest row drops its obsolete structural ceiling. Two
unused prose vocabulary entries are removed. The regenerated manifest
adds the two accurately classified memory modules and retains the same
77 variant classifications, including seven undemonstrated partial faces.
There are no new client-boundary allowances.

## Verification

All Lean/Lake commands ran serially through the repository cap at 40G
from the package cwd. Final target build lines (verbatim):

```text
✔ [457/457] Built CerberusHeapLang.CorpusT4Exhibit (9.6s)
✔ [453/453] Built CerberusHeapLang.MallocListExhibit (1.0s)
```

The [focused inspection](evidence/2026-09-06_repin-t4-malloclist-axioms.lean)
checks all 126 declared theorems (55 t4, 71 malloc-list) and prints 27
selected signatures. It exited zero without warnings. Derived cone
counts: 114 exactly the classical trio; five `{propext, Quot.sound}`;
four only `propext`; three axiom-free. The last group is `t4Sum_succ`,
`t4Kill_eq`, `mlProg_size`. Focused inspection complements the exhaustive
package audit, not its replacement.

Both `CERB_MEM_MAX=40G scripts/test_unit.sh --fast` and then the full
`CERB_MEM_MAX=40G scripts/test_unit.sh` exited zero. Verbatim audit output
from the final full run:

```text
info: CerberusHeapLang/Audit.lean:1080:0: CerberusHeapLang export pins: 889 trio-exact, 6 axiom-free-exact
info: CerberusHeapLang/Audit.lean:1080:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (6351 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1080:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (9457 constants of every kind swept, internal details included — count informational, environment-dependent)
```

The sweep totals are informational and environment-dependent. The
verdicts, not the totals, are the trust check. The fast log has 33
package-module warning headers (31 Potential, two Heap); no new warning
was emitted by t4 or malloc-list. Warning cleanup remains recorded work.

Verbatim regenerated report totals:

```text
MANIFEST: 35 constructors, 77 variant rows (40 RULE, 0 RULE-TOTAL-UNDEMONSTRATED, 7 RULE-PARTIAL-UNDEMONSTRATED, 0 PARTIAL-ONLY, 24 NO-RULE, 6 OUT-OF-SCOPE), 0 red, 25 consumer modules
CLAIMS: 17 claim rows, 183 declaration names checked in the theorem cell, 339 declaration-shaped spans checked across every cell (43 vocabulary words, 2 retired names); plants (deleted name in a prose cell; retired name without its marker) red as expected
```

The full run reports no manifest drift, every corpus skeleton match and
mutation mismatch, 18 core modules respecting import direction, and:

```text
BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0
ok: client boundary — no unallowlisted internals mention
ALL GATES GREEN
```

The skeleton remains a constructor/annotation comparison; it does not
establish whole-file identity. No new oracle execution is claimed.
`scripts/setup-cerberus-dep.sh --check` exited zero: exact pin, verified
Lean generation stamp, 37 hand-written seams byte-identical to the pin.
`git diff --check` passes. Main and the E5 review worktree remain parked.
Ephemeral logs live in `.tmp/repin-scout/`, chiefly
`full-repin-regressions-final.log`, `t4-malloclist-axioms-final.log` and
`audit-pin-inventory.log`; the commands and durable evidence above own
the checkpoint claim.

## Next work

Reconcile the README, architecture, walkthrough, known-item ledger and
remaining source commentary with the quantified fuel contracts. The
architecture citation speedbump reports 277 cites: 52 EXACT, 153 DECL,
26 USE, 22 HAND, 24 PIN, zero missing files; 20 range cites are included
in those classes. This reports drift, not a completed citation review.
The older prose and quoted signatures remain an explicit M2 task.

Decide and document the generic fragment-start ambient-one disposition;
closed production already covers zero and one by exact setup equations.
Continue the faithful emitted-file investigation required by A7, then
E6's raw-call/scheduler adequacy and the remaining deterministic corpus,
E7's all-outcomes t9 result, exemplar cleanup and full acceptance review.
B1's seeded any-memory total forms and A5's runtime-panic boundary remain
explicit. The E5 range review and partial-face coverage disposition are
still open; review dispatch approval remains pending. No review, merge
or push is claimed. The full goal remains active.
