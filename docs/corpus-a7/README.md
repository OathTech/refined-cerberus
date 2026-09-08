# Retained complete-file corpus inputs

These fixtures are the OCaml no-libc Cabs exports of the four supported
programs, with the exact relative source paths below. The full claim-point
speedbump regenerates each with the existing read-only OCaml driver and
compares bytes:

```sh
CERB_MEM_MAX=40G scripts/check-emitted-corpus.sh
```

| Fixture | Source under `docs/corpus-e0/` | Frontend supply | Cabs SHA-256 |
|---|---|---:|---|
| `t1.cabs.json` | `t1.c` | 36 | `e89a6a7bbff9cc30a9203010ff8c01beb5b496a0c9fad2ac8c1a6cd416b69134` |
| `t5.cabs.json` | `t5_ifelse.c` | 47 | `b6fa355f81261be0fb9b91aa471b758dd90756fbccc38ba9a3010be0c73f5f6a` |
| `t6.cabs.json` | `t6_switch.c` | 51 | `022e59276e520a87d7febf0508383e3e19e4d44fc44aaab9b13562c5965bb83d` |
| `t4.cabs.json` | `t4_while.c` | 92 | `7b896e9240d5535915aa73e35af0ac98c6dc1310c162ae1845666455ad5ee02a` |

A single program can be selected with `scripts/check-emitted-corpus.sh t4`
(and similarly for the others). `scripts/check-emitted-t1.sh` retains the
original command as a compatibility wrapper selecting t1.

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
identifies the artifact that produced these fixtures and reproduced t1 at landing.

The captured Core producer is the pinned **Lean** frontend loading this
Cabs in a fresh process: parse the pinned standard/implementation libraries,
set the TU digest, `frontendTU true 0`, single-file `link`, `convert_file`.
This does not assert equality to the OCaml driver's printed Core.

The complete data terms live in
`cerberus-heaplang/CerberusHeapLang/Examples/EmittedT{1,5,6,4}Data.lean`,
under namespaces `CerberusHeapLang.CorpusA7.T{1,5,6,4}`. The frontend
supplies above are retained data. The diagnostic JSON's
`after_driver_initialization_supply` is the initializer's returned next
supply (one higher); the initial run state's supply is the captured value.

The comparison runs use ambient fuel50 for t1 and1000 for t5/t6/t4.
These are executable capture/comparison settings, separate from the
all-sufficient-fuel execution theorems and their composition bounds. The
comparison must observe singleton Active returns4/1/20/10 respectively,
unblocked with empty trace/stdout/stderr. No IO frontend-correctness
theorem is claimed. Proof and review status are recorded in the
[corpus implementation record](../2026-09-08_whole-file-corpus-implementation.md).

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

The old `CorpusE0` text/skeletons and `t{1,4,5,6}_certified_production`
wrappers remain regression artifacts. The named A7 target with the
elaborator in the statement remains open. Six other corpus programs need
additional semantic/rule support and are outside this migration.
