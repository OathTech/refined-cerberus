# Next whole-file slice: emitted integer assignment and t5

Follow-up: after the operator asked about a larger coherent landing, the
[whole-file corpus proposal](2026-09-08_whole-file-corpus-proposal.md)
recommends grouping t5/t6/t4 as one V1-1b slice, with additional fresh
t4/t6 evidence. This original scout remains the record of the shared
technical prerequisite and a possible first internal checkpoint.

Status: read-only scout and recommendation, [AGENT 2026-09-08], against
`demo-whole-file-t1` at `d49cd3b`. This is neither an activated charter nor
a claim that the proofs below have been implemented. The parent owns the
current review fixes and build lane; this scout ran no Lean/Lake builds.
Working practices: `AGENTS.md`; audit scope: `docs/AUDIT-BRIEF.md`;
known limits: `docs/KNOWN-OPEN-ITEMS.md` (especially A7, B7, B19–20, C19–20).

Recommend the first part of V1-1b: **reusable emitted integer assignment
support, consumed by a complete-file t5 conditional certificate**. Keep t4
and t6 for subsequent slices. This is a coherent continuation of V1-1a:
the capture and driver layers get a second genuine frontend consumer, and
the client layer becomes reusable across emitted programs with actual
symbol identities, type annotations, and linked-library calls.

## Evidence and actual remaining obligations

The existing evidence in the parent worktree is
`.lake/whole-file-evidence/reuse/{t5.json,T5Data.lean,t5.cabs.json,roundtrip.log}`.
It is a prior parent-run executable observation, not a theorem or a new
run by this scout. `t5.json` records:

- Frontend supply 47; the second component returned by driver initialization
  is 48. Use the actual initialization function in the theorem; do not
  silently replace the recorded supply with a convenient floor.
- A normal-callconv file with empty globals/tags, 110 stdlib entries,
  6 impl entries, and 11 funs/extern/funinfo entries. Main is symbol 19
  under digest `b4ef7a8b3c9b74305159f25518c8a7fe`.
- Exact quotation/supply and independent structural-data comparison pass;
  captured comparator checks pass. At ambient fuel 1000 the actual driver
  produces one Active result, `Specified(1)`, unblocked, empty trace and
  output streams. This does not establish the eventual theorem's fuel floor.
- Cabs SHA-256 `b6fa355f81261be0fb9b91aa471b758dd90756fbccc38ba9a3010be0c73f5f6a`;
  generated data SHA-256 `24b866bd6131ce31d547be17b9ec8b4ab466fffcf143adc8314fe46002be3cba`.

I independently compared the generated Lean text between the `stdlib :=`
and `impl :=` field boundaries with `Examples/EmittedT1Data.lean`: the
whole blocks are byte-identical. This is useful additional measurement,
not a Lean equality proof. `EmittedStdCore.hasIntLibrary_of_stdlib_data_eq`
(line 108) already transfers the integer contract to another file given
library-data equality and its comparator check. The integer support is
therefore reusable with this same captured library today; arbitrary
library-body correspondence is not established.

The old t5 theorem cannot be applied to the new file directly:

| Mismatch | Evidence | Work required |
|---|---|---|
| Truncated library | `StdCore.StdE3` is exactly `file.stdlib = stdlibE3` (StdCore:180); t5_wpt requires it (CorpusT5Exhibit:423). The actual map has 110 entries. | Use actual `EmittedStdCore.HasIntLibrary` lookup facts, or generic evaluated-operand premises instantiated from that contract. Do not prove a false `StdE3` equality. |
| Symbols and supply | Legacy x/r are 505/506, temporaries about 508–529, and t5_wpt requires `600 ≤ sym_supply` (CorpusT5Exhibit:426, 518–522). Fresh data has x/r 21/22, return label24, source temporary numbers through46. | Rebuild exact-body shape lemmas; prove the required non-collisions from captured supply47 and actual symbol numbers. Do not carry600 into the new production statement. |
| Type and operand annotations | Actual assignment uses annotated signed-int ctype, annotated pointer read and conversion call (T5Data:41957–42090). Legacy `Examples/EmittedInt` load/store helpers fix `intTy`, `psym`, `convLoadedInt`, and `StdE3` (lines105,195). | Add shared support parameterized by annotations, type, symbols and conversion operands/proofs. Existing actual-library evaluator lemmas already accept annotation lists and annotated signed-int types (EmittedStdCore:330,343). |
| Extern premise too strong | `Wpt.wpt_neg_bound` requires `∀ x, resolveExtern M.extern x = x` (4860–4890). Whole-file startup has a singleton main self-binding; `EnvLaws.resolveExtern_self_compare` (462) proves only key-comparison equality for every symbol, since descriptive metadata is ignored by lookup. | A narrowly generalized assignment lemma using comparison equality is necessary. The only use of the strong premise in the existing proof is the final fresh-binder read (4957–4960); `evalPexpr_sym_of_compare` (EnvLaws:447) provides the replacement. Preserve the old signature as a specialization. |

The last row is an important fence correction: promising all of Wpt
byte-frozen while directly reusing `wpt_neg_bound` would be unjustified.
Either allow a narrowly named comparison-based helper in Wpt, factoring the
existing theorem through it, or derive the helper in a separate support
module from the same public rules. The latter must not become an
unexplained copy of a hundred-line proof. Apply the same discipline to the
partial twin if it is generalized; do not broaden the judgment definitions.

The source's assignment tail lacks a dynamic `Eannot` node, as does the
legacy source. This is not an additional obstacle: `wpt_bound_wseq_tuple`
(Wpt:4657) introduces the dynamic annotation around the tail after operand
binding; the legacy consumer matches it to `negAssignBody` at
CorpusT5Exhibit:203–221. The actual body must still be checked exactly.

I counted constructors in the generated `funs` field (T5Data:40018–43051):
2 expression `Ecase`, 1 expression `Eif`, 4 `Eunseq`, and 2 negative stores.
These have existing rules and legacy consumers: `wpt_t5Gt` (98),
`wpt_t5Cond` (143), `wpt_t5AssignBlock` (183), `wpt_t5If` (371);
`Examples/CorpusE5.t5Main_frag` (97) covers both branches, including the
unspecified-value nondeterministic branch. The new exact body needs its
own syntactic `Frag` proof and separate `evalDepth` bound, retaining R2.
No new mirror constructor is indicated by this inspection. This is a
structural feasibility finding, not an already checked new proof.

The report's `uncovered_body_kinds = ["case", "case", "if"]` comes from
`CorpusE0.uncoveredKinds` (1211), whose old diagnostic explicitly labels
all expression if/case nodes uncovered. It is not a failed `Frag` decision
and must not be used as t5's acceptance criterion or silently reinterpreted
as a new coverage gap. Scope any diagnostic cleanup narrowly and retain the
kernel membership proof as the authoritative coverage fact.

## Proposed landing content

1. A comparison-based derived assignment rule, preserving current public
   signatures; annotation/type/operand-parametric emitted integer load and
   assignment support. Put shared facts outside positive-client modules.
   The generic rules should consume ordinary evaluation/memory premises;
   the captured-library adapter supplies those premises for this pin.
   This makes the rules library-parametric without falsely claiming a
   theorem about arbitrary library implementations. Reuse an existing t1
   fact through the common support where a small extraction is sufficient.
2. A retained complete `EmittedT5Data`, exact-body shape and membership
   proofs, return-label proof, and total proof over that body. Consume
   `wpt_driver_done_alloc_extern` (ProdLoop:551) and `prod_run_eqJ_file`
   (ProdEntry:950), then export a direct actual-driver theorem and a
   capture/supply-equality transfer theorem matching t1's boundary.
   Result: one Active `Specified(1)`, unblocked with empty outputs, all
   ambient fuels above a proved sufficient bound, arbitrary fs/arguments.
   Keep the old wrapper theorem and shipped form as labelled regressions.
3. Generalize the small whole-file speedbump invocation to retain/check t1
   and t5; verify fresh Cabs, complete data by both comparison methods, actual
   comparator paths and exact supply. Reuse the existing cheap main/supply
   negative check. Update advertised corpus/API/A7 surfaces to say t1+t5,
   leaving t4/t6 and frontend correctness open.

The generic value is substantive: actual-extern-safe assignment applies to
any matching symbol map, type and evaluated store operands; shared integer
client rules retain actual annotations and avoid hardcoded legacy stdlib
symbols. The concrete t5 proof tests comparison, conditional selection,
negative assignment, a fresh temporary and return through the same
complete-file entry layer. This is more than a second data dump.

Freeze semantics/Lem/Iris pins, Step/Round/Soundness/Fragment, judgment
constructors, heap coupling and driver protocol. Limit any Wps/Wpt edits
to the named assignment-premise generalization with old statements
preserved. Do not fold in arbitrary-library matching, symbolic-int
storability V1-4b, the whole FreshAbove/derived-cost campaign V1-4a, calls,
scheduler, seq_rmw, globals, tags or broad client-import cleanup.

Acceptance: kernel-checked comparison-based helper first; exact actual
body membership and total proof; all old export signatures preserved;
new exact axiom pins; full capped gate plus both whole-file observations
and negative comparisons; independent full-range review. Audit must check
that the new theorem runs the captured supply and complete file, and that
no constructor-identity extern assumption has slipped back into its
premises. The measured fuel1000 is a scout setting, not a proposed proof
floor; derive a named sufficient budget from the composed rules.

## Why this before the other plan items

V1-1b as all t4/t5/t6 would conflate this shared client generalization with
two additional control-flow migrations. T6 carries five registered labels
and a dispatch proof (CorpusT6Exhibit:191–224,470); t4 carries loop,
continue/break and decreasing-budget reasoning (CorpusT4Exhibit:451–491,
1425). T5 has the single return-label map (CorpusT5Exhibit:251), so it is
the smaller first consumer. The shared assignment and comparison support
then reduces repetition when t6 and t4 follow.

V1-2 seq_rmw introduces new mirror/logic faces and its own premise census;
it is larger semantic scope while this known complete-file gap remains.
V1-4a is deliberately later in the plan so its signature census sees the
finished emitted interfaces. The new t5 proof should use an exact local
freshness obligation, without claiming to close that broader floor task.
Calls await the separately owned scheduler/re-pin work. None is a better
bounded successor to the newly reusable whole-file infrastructure.

## Parent verification after the t1 landing

[AGENT 2026-09-08, parent] Independently inspected the cited Wpt proof,
`evalPexpr_sym_of_compare`, `resolveExtern_self_compare`, the actual t1
runtime-extern reconstruction, the existing integer load/store helpers,
and `hasIntLibrary_of_stdlib_data_eq`. The extern premise is used only at
the fresh-binder lookup in `wpt_neg_bound`; the proposed generalization
has a concrete proof site and preserves the existing theorem's contract.
The exact t5 runtime map and new proof still need kernel verification in
the proposed slice.

Re-read the retained t5 report, independently recomputed both hashes above,
and compared its entire stdlib quotation block with the now-landed t1
data: identical. The recorded round-trip/comparator results, supply47 and
sole Active return1 agree with this report. The t5 report has no negative
check results yet; those are proposed acceptance work, not completed work.
The measured run at fuel1000 is still only an executable observation.

The t1 landing is complete on main `4bc0a98`; its full primary gate passed.
This recommendation remains on the separate `scout-next-whole-file-slice`
branch for review, with no implementation or merge of the proposed slice.
