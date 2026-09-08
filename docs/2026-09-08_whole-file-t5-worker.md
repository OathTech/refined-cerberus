# Complete-file t5 worker record

[AGENT 2026-09-08]. Parent charter:
`docs/2026-09-08_whole-file-corpus-charter.md`. Worktree
`worktrees/worker-whole-corpus-t5`, created from `demo-whole-file-corpus`
at `f6045fd` through the primary `scripts/new-worktree.sh`. Shared support
commit `abbfbd6` is adopted as `ccefa15`; parent owns its integration.

## Captured file and body checkpoint

`Examples/EmittedT5Data.lean` is the complete existing tool quotation from
the verified t1 slice's reusable t5 experiment, with only its namespace
changed from `CerberusHeapLang.CaptureReuseT5` to
`CerberusHeapLang.CorpusA7.T5`. The parent will independently run the fresh
Cabs/quotation/comparator speedbump at integration. No generator or
semantics source was modified here.

`Examples/EmittedT5.lean` projects main from that data, proves exact body
equality including annotations, procedure metadata and save initializer,
and proves syntactic membership for both if branches, unspecified cases,
and dead cleanup. Its independent evaluator-depth bound is 40. The
complete reference collector's main lookup is kernel checked; original
comparators remain guarded by their finite checks. Captured library data
equals the t1 captured library, enabling the existing actual-library
contract without a truncated-file assumption.

Captured frontend supply is 47. The returned supply after driver
initialization is 48; the initial run state's `sym_supply` itself is 47,
as `initial_core_run_state` draws the current supply into that field.
Source cell numbers are 21 and 22, return label 24, and temporaries 25–46.

All Lean commands use package cwd and `scripts/capped`, `CERB_MEM_MAX=40G`.
Verbatim successful lines from the targeted build log (root-relative,
ignored and ephemeral `.lake/t5-worker-evidence/proof-build.log`):

```text
✔ [454/455] Built CerberusHeapLang.Examples.EmittedT5 (4.5s)
```

The first body equality check caught a missing pointer annotation on the
negative store; `assignmentPtr` now retains
`Astd "§6.5.16#3, sentence 1"`. The complete-body equality then passed.
The public proof module remains in progress at this checkpoint and is
not included in this checkpoint commit. The full parent gate and final
adversarial review remain required before claiming the charter complete.

Cache refresh attempted to overwrite existing read-only package Git
objects, reporting permission denials. Those unnecessary writes were
not retried. The existing dependency checkout and copied build artifacts
were used; the build trace identifies Lean 4.32.2. No provider source or
dependency pin changed.
