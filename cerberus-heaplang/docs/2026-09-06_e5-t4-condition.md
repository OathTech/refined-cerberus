# E5 t4 controlling expression — 2026-09-06

[L1 landing note, 2026-09-07, AGENT] Record of the code, taken onto main with the code from the other agent's `dialect-e5` (landing charter §2 L1). "The charter" / "the active demo-completion goal" below is that agent's `docs/2026-09-05_demo-completion-charter.md`, a process document that stays on the parked branch `parked/demo-expansion-2026-09-07` and is not on main; its scope statements are [AGENT] readings, not rulings.

[AGENT, active demo-completion goal] Continued on `dialect-e5` from
`ef0255e`, with a clean worktree. The previous goal turn was progress:
the t4 transcription, whole-term membership, shared load derivation and
engine-checked continuations were committed and validated. The semantics
pin remains `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`, Lean 4.32.2.
Main and sibling repositories are unchanged.

## Proved now

`CorpusT4Exhibit.lean` proves the emitted controlling expression for
variable in-range integer contents, through public rules. The concrete
program is unchanged. Both short-circuit branches and every nested truth
conversion remain in the transcription and membership theorem.

- `wpt_t4Lt`: read an owned integer cell and compare with an in-range
  constant, budget 16. The explicit case-selection premise is discharged
  by kernel equality at each emitted pair of pattern binders.
- `wpt_t4Truth`: one emitted truth conversion, adding 8 to its head's
  budget. Its post passes the resulting frame and dynamic annotations
  through. The engine's selected-branch depth check is discharged.
- `wpt_t4Left` and `wpt_t4Right`: the left comparison with two truth
  conversions, budget 32, and the right comparison with one, budget 24.
- `wpt_t4And`: the raw conjunction, budget 63. If i is less than 5,
  the proof reads s and evaluates the right comparison. Otherwise it
  follows the emitted zero branch and retains ownership of s as a frame.
  The budget is a common upper bound; the zero branch uses monotonicity.
- `wpt_t4Cond`: the final equality-to-zero conversion and enclosing
  full-expression bound, budget 72. It returns the specified bit of the
  negated conjunction as a bare value. Both owned cells are preserved;
  the bound removes the dynamic annotations exactly where the emission
  puts it.
- `wpt_t4Bool`: the emitted loaded-integer-to-Boolean decoding, budget 4,
  returning the original conjunction's Boolean value.

The cell-read hypotheses explicitly state reconstruction and absence of
a trap; integer range hypotheses govern the standard-library conversions.
These proofs assume `StdE3 M.file` and identity external-symbol resolution.
`t4SourceFrame` records the two source-pointer bindings and ordinary frame
well-formedness; its extension lemma hides accumulated temporary bindings
from the next statement's interface. This is a proof interface, not a
change to the program or its environment operations.

The loop body, decreasing budget, block specifications and t4 production
result are not yet proved. Result 10 remains the intended source-level
calculation, not a t4 shipped-driver theorem. The full-file/library
criterion A7 and the existing transcription boundary remain open.

## Public rule addition

The raw conjunction binds an annotated comparison result with a strong
symbol binder. Its engine transition and fragment coverage existed, but
the public symbol-binding rule accepted only bare results. Added
`wps_seq_sym_annot` and `wpt_seq_sym_annot`: bind the underlying value,
then prove the continuation wrapped in the same dynamic annotations.

Both rules are derived through the existing judgments and engine-matched
step. Their proofs cover delivery, ordinary head steps, label jumps and
procedure calls; the total proof uses induction on its head budget, and
the partial proof uses the existing guarded recursion pattern. No mirror
constructor, engine classification, memory invariant or adequacy theorem
changed. Neither rule discards the annotation or substitutes a different
sequence form. t4 uses the total rule twice on its nonzero path.

The new partial face is proved but has no partial corpus client. The
manifest therefore records RULE-PARTIAL-UNDEMONSTRATED, joining the
charter's existing E5 partial-face disposition item. This is an explicit
open review item, not a declaration that the partial acceptance criterion
is complete.

## Validation and record maintenance

All fifteen new theorem cones were individually measured as exactly
`[propext, Classical.choice, Quot.sound]`, and all fifteen were pinned.
Targeted capped builds and the fast gate passed with 864 pins. The
manifest was deliberately regenerated: 35 constructors, 76 variant rows,
40 RULE, 6 RULE-PARTIAL-UNDEMONSTRATED, 24 NO-RULE, 6 OUT-OF-SCOPE,
zero red, 25 consumers. Claim C17 records the controlling-expression
result and its limits; 17 claim rows and 165 theorem-cell names are
checked. The FULL gate exited 0; selected output, verbatim:

```
info: CerberusHeapLang/Audit.lean:1024:0: CerberusHeapLang export pins: 864 trio-exact
info: CerberusHeapLang/Audit.lean:1024:0: CerberusHeapLang axiom sweep: every theorem bounded by the trio (5923 swept, internal details included — count informational, environment-dependent)
info: CerberusHeapLang/Audit.lean:1024:0: CerberusHeapLang banned-axiom sweep: sorryAx/ofReduceBool/ofReduceNat absent from all cones (8994 constants of every kind swept, internal details included — count informational, environment-dependent)
Build completed successfully (472 jobs).
ok: capability manifest regenerated, no drift
ok: corpus skeleton — every transcription matches its emitted text, every plant mismatches
ok: import direction — 18 core modules, none imports an exhibit/example/production module
BOUNDARY: 29 modules checked, 0 internals mention(s) in total, exit=0
ALL GATES GREEN
```

This revalidates the existing t1/t5/t6 production proofs after the rule
addition. The new partial and total core rules each built in 6 seconds,
and the final t4 module build took 2.2 seconds. `git diff --check` passes.

API, README and ARCHITECTURE now describe annotated strong symbol
binding as ruled. Corrected the old claim that every emitted symbol-bound
head is a bound expression, and the claim matrix's stale four-annotated-
binder and three-transcribed-program counts. Removed blank lines that
broke the later claim rows out of their Markdown table. The citation
report remains at 283 citations: 175 EXACT, 53 DECL, 25 USE, 21 HAND,
9 PIN, zero NOFILE and 25 RANGE, with zero automatic fixes. Its existing
manual-review queue remains open.

## Next action

Prove the two effectful assignment right-hand sides (`s + i` and `i + 1`)
and factor their shared negative-store protocol. Then compose the body,
registered continuations and loop invariant with a decreasing total
budget. Keep the accumulated source-pointer frame interface and the
fresh-symbol floor explicit. Finish the t4 production equation and full
verification before calling t4 certified; E5 range review and every later
charter milestone remain open. This checkpoint continues the active
goal and is not a park, merge or push.
