# cerberus-heaplang — a classical separation logic over Cerberus Core, in Lean 4 on iris-lean

The product of this repository is the package
[`cerberus-heaplang/`](cerberus-heaplang/): a Reynolds/O'Hearn-style
separation logic for a fragment of Cerberus's Core intermediate language,
built on iris-lean, whose exported theorems are statements about the
execution and memory states of the
cerberus-lean semantics (the Lean 4 port of the Cerberus C semantics,
a sibling repository — see Prerequisites). Start with its normative architecture statement,
[`cerberus-heaplang/ARCHITECTURE.md`](cerberus-heaplang/ARCHITECTURE.md);
its [README](cerberus-heaplang/README.md) and
[walkthrough](cerberus-heaplang/docs/WALKTHROUGH.md) follow from there.
The package's dated records (slice notes, independent audits, external
reviews) are under `cerberus-heaplang/docs/`.

What is here besides the package: `docs/DECISIONS.md` (the append-only
register of rulings, with [USER]/[AGENT] provenance), `docs/AUDIT-BRIEF.md`
(the standing brief every auditor is graded against), the dated
repository-level records (audits, the fuel-exhaustion request to the
cerberus-lean team and its review, an upstream note), and `scripts/`
(`capped` for cgroup-capped builds, `setup-cerberus-dep.sh` for the pinned
semantics workspace, `test_unit.sh` the gate runner).

Longer-term direction: an agent-driven C verification layer in the
RefinedC design family, built above this logic. That work lives on the
branch `refinedc/dev` (its Lake package, donor-toolchain scripts and design
notes) while it is brought to a presentable state; nothing of it is on
`main`, and nothing here should be read as a port of RefinedC.

## Building

Prerequisites: a BUILT checkout of cerberus-lean as the sibling directory
`../cerberus-lean`, at (or content-equal on the semantics-bearing paths to)
the commit in `scripts/semantics-pin.env`, built with cerberus-lean's own
toolchain (its `lean_frontend/generated`, `native`, `.lake` are copied
into the workspace here — they are not in any git tree). The setup
script fails closed, naming the mismatch, if the sibling is absent or
differs from the pin. Lean 4.32.2 via elan. The Lake dependencies are
git-pinned to public repositories and resolve either from the network or from local mirrors
via a `GIT_CONFIG_GLOBAL` redirect file (this development environment
uses the latter; `scripts/capped` loads it when present).

```bash
scripts/setup-cerberus-dep.sh            # once: the pinned cerberus-lean workspace (see scripts/semantics-pin.env)
cd cerberus-heaplang && ../scripts/capped ~/.elan/bin/lake build   # capped; elaborates the in-build axiom audit
scripts/test_unit.sh                      # the gates (banned-methods grep; the capped build) + two speedbump reports
```

Toolchain: Lean 4.32.2 (elan). Dependencies (batteries, Qq, iris-lean) are
git-pinned in `cerberus-heaplang/lakefile.toml`; the semantics enters as a
path dependency on the pinned workspace `.cerberus-ws/lean_frontend`
(a clone of cerberus-lean at `scripts/semantics-pin.env`'s commit, primed
from a built checkout and checked seam-by-seam against the pin).

## License

Copyright 2026 Oath Technologies. Licensed under the Apache License,
Version 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). The
dependencies carry their own licenses (batteries, Qq and iris-lean:
Apache 2.0 — their pinned `LICENSE` files are byte-identical to ours,
measured with `cmp` on 2026-09-03; cerberus-lean and LemLib: see theirs).
