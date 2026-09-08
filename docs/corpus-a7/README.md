# Retained complete-file t1 input

`t1.cabs.json` is the OCaml no-libc Cabs export of `docs/corpus-e0/t1.c`,
with that exact relative source path. The full claim-point speedbump
regenerates it with the existing read-only OCaml driver and compares bytes:

```sh
CERB_MEM_MAX=40G scripts/check-emitted-t1.sh
```

Cabs SHA-256: `e89a6a7bbff9cc30a9203010ff8c01beb5b496a0c9fad2ac8c1a6cd416b69134`.
The certified Core producer is the pinned **Lean** frontend loading this
Cabs in a fresh process: parse the pinned standard/implementation libraries,
set the TU digest, `frontendTU true 0`, single-file `link`, `convert_file`.
This does not assert equality to the OCaml driver's printed Core.

The complete data term lives in
`cerberus-heaplang/CerberusHeapLang/Examples/EmittedT1Data.lean` (frontend
supply 36). The certificate is `CorpusA7.T1.certified_production` at ambient
execution fuel at least 50, under the original comparator checks; the
transfer theorem `_of_capture_eq` makes the original file/data and supply
premises explicit. No IO frontend-correctness theorem is claimed.

To inspect/check that retained term, from the repository root:

```sh
mkdir -p .lake/inspection
scripts/inspect-emitted-file.sh docs/corpus-a7/t1.cabs.json \
  .lake/inspection/t1.json 50 \
  cerberus-heaplang/CerberusHeapLang/Examples/EmittedT1Data.lean \
  CerberusHeapLang.CorpusA7.T1 --check-data --selftest
```

Omitting `--check-data` generates the requested data file, elaborates it,
and compares it against another frontend load. Use a fresh destination to
retain a new program. Omitting both data arguments produces a diagnostic
report only. The loader, quoter and independent structural comparator are
reusable; this inspection workflow currently requires a main, the same
captured standard library, and a successful run at the chosen fuel.

Comparison preserves all eleven fields, optional map trees (including
heights), annotations and observed floating-point bits. Comparator functions
remain separate: their three finite checks are also evaluated on the very
frontend instance compared to the retained data. Negative checks require
`main := none` to fail both data comparisons, and supply + 1 to fail only
supply comparison. These are executable speedbumps, not kernel theorems.

The old `CorpusE0.t1Main` text/skeleton and
`t1_certified_production` wrapper remain regression artifacts. A7 remains
open for the other corpus files and the target with the elaborator in the
statement. See [implementation record](../2026-09-08_whole-file-t1-implementation.md).
