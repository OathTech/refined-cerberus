# Retained complete-file t1 input

`t1.cabs.json` is the OCaml no-libc Cabs export of `docs/corpus-e0/t1.c`,
with that exact relative source path. The full claim-point speedbump
regenerates it with the existing read-only OCaml driver and compares bytes:

```sh
CERB_MEM_MAX=40G scripts/check-emitted-t1.sh
```

Cabs SHA-256: `e89a6a7bbff9cc30a9203010ff8c01beb5b496a0c9fad2ac8c1a6cd416b69134`.

OCaml producer identity, measured again at the 2026-09-08 landing:

- Binary: the sibling `cerberus-lean/_build/default/backend/driver/main.exe`.
- Binary SHA-256: `7d1778bba8defb85233c4be211ab9cbe4b32dae13cf4afc9de79fae3c9302cd4`.
- Its own `--version`: `git-cn-pin-720-g9a7f7ad31`, identifying build revision
  `9a7f7ad31960af91134821b00e3c2f4aa14444a1`. This is the binary's embedded
  build identification; the build was not independently reproduced here.
- Runtime directory: the sibling `cerberus-lean/_build/install/default`.

The sibling checkout was at `94f339eb4c171a82d49faa46fe859c0210638375` when
measured; that current checkout is not the binary's build revision or the
pinned Lean semantics revision. The full gate requires this external OCaml
build and runtime; if absent, the whole-file step fails. `--fast` does not
run this step. Each run prints the binary hash, its version and both paths
in the speedbump's log. A different binary hash is disclosed, not rejected:
the exact fresh-Cabs comparison remains the drift check. The hash above
identifies the artifact that reproduced the retained fixture at landing.

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
