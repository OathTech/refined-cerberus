# Fresh-eyes review of the shareable `main` candidate (main-share @ eddb253)

[AGENT 2026-09-03] Reviewer role: a PL researcher who knows separation logic and
Iris, has heard of Cerberus, knows nothing about this project. Read-only; no
builds run; this file is the only write. Standard applied, verbatim from the
operator: "What's on main doesn't need to be perfect, just not misleading."

Files read, in order: `README.md`, `CLAUDE.md`, `docs/DECISIONS.md` (first 60
lines and the tail entry), `docs/AUDIT-BRIEF.md`, the `docs/` listing,
`cerberus-heaplang/ARCHITECTURE.md`, `cerberus-heaplang/README.md` (whole),
`cerberus-heaplang/docs/WALKTHROUGH.md` (§1, §1.3, §6, §7 and its tail),
`scripts/test_unit.sh`, `scripts/setup-cerberus-dep.sh`,
`scripts/semantics-pin.env`, `scripts/capped`, `scripts/new-worktree.sh`,
`cerberus-heaplang/lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
`docs/CAPABILITY_MANIFEST.md`, the headers of `CerberusHeapLang.lean` and
`Audit.lean`. Then the requested grep (single-line and multi-line) over
everything except `docs/DECISIONS.md`, `docs/2026-*`, and
`cerberus-heaplang/docs/2026-*`, plus a relative-link existence check.

---

## (1) What a newcomer would believe, and whether it is true

After the root README and the demo's ARCHITECTURE I would believe: this repo's
product is one Lean 4 package, `cerberus-heaplang`, a Reynolds/O'Hearn
separation logic over a declared fragment of Cerberus Core, built on iris-lean.
A hand-written small-step mirror `Step` is certified one-directionally against
one round of the shipped cerberus-lean driver (`engine_step_matchU`), with a
per-constructor completeness classification up to a two-arm residual. Two
judgments (`wps` partial, `wpt` total) sit over Iris WP. Seven closed-program
total-correctness theorems are stated over the genuine shipped driver composite
(`CerbND.runND (drive …) (initial_driver_state …).1`); the partial-correctness
exports are stated over the package's own loop `driveU` and labelled
PROVISIONAL. Axiom cones are pinned in-build to `propext`/`Classical.choice`/
`Quot.sound`. No call rule, no C frontend (authored Core), single-threaded,
empty tag definitions. Around it: a gate runner, a cgroup-capped build wrapper,
a pinned-and-primed semantics workspace, an append-only rulings register and
many dated records. A RefinedC-style layer is longer-term work on a branch.

That belief is correct against the tree. Verified by inspection (no build):
`cerberus-heaplang/CerberusHeapLang/` holds 34 modules plus `Examples/{Layout,
MirrorCoverage,ReadinessSmoke}.lean`; `Audit.lean` is the last import of the
library root; the seven named production theorems exist
(`ProdExhibit.lean:265`, `ProdLoopExhibit.lean:75/620/1435`,
`DisposeExhibit.lean:1591`, `RegionLoopExhibit.lean:692`,
`MallocListExhibit.lean:1748`); `def driveU` is at `Adequacy.lean:181`; the
committed manifest ends `MANIFEST: 23 constructors, 25 rule rows, 0 red, 16
exhibit modules`; `scripts/` holds exactly `capped`, `new-worktree.sh`,
`semantics-pin.env`, `setup-cerberus-dep.sh`, `test_unit.sh`; `docs/` holds 16
dated records plus `AUDIT-BRIEF.md` and `DECISIONS.md` (1,429 lines, 87
entries); there is no root Lake package, no `RefinedCerberus` source anywhere
on main, and `.cerberus-ws/` is untracked (gitignored). There is no `LICENSE`
file (not a misleading-ness issue; flagged for a repo about to be shared).

---

## (2) Sentences / files on `main` that would mislead a newcomer

Graded: **M** = would give a false belief or a command that cannot run as
described; **L** = stale or dangling detail, easy to misread; **N** = note.

**M-1. The demo README describes a trust base with two packages and two trees.**
`cerberus-heaplang/README.md:758-761`, verbatim (the line break is why the
commit's single-line grep for "root package" missed it):

> The trust base is this build with its in-build sweep, the root
> package's build with its own sweep, and a grep for banned proof methods
> (`native_decide`/`bv_decide`/`ofReduce*`) over both trees — the three
> checks `scripts/test_unit.sh --fast` runs.

There is no root package and no second tree on main; `scripts/test_unit.sh
--fast` runs gate 1 (grep over `cerberus-heaplang/CerberusHeapLang` only) and
gate 2 (one capped build). Fix: "The trust base is this build with its in-build
sweep and a grep for banned proof methods (…) over the package — the two checks
`scripts/test_unit.sh --fast` runs."

**M-2. The root README's "Building" does not state the prerequisite that makes
step one runnable.** `README.md:31-40` gives `scripts/setup-cerberus-dep.sh` as
the first command and says the workspace is "a clone of cerberus-lean at
`scripts/semantics-pin.env`'s commit, primed from a built checkout". The script
itself (`scripts/setup-cerberus-dep.sh:21-30`) computes `SRC="$CONTAINER/
cerberus-lean"` with `CONTAINER` the parent directory of this repository and
requires that checkout to be BUILT: `lean_frontend/generated`,
`lean_frontend/native`, `lean_frontend/.lake` and the lem-sync stamps must
exist ("B FAIL: $SRC/$p missing — primary checkout not built?"), at or
content-equal to commit `f95ef8d9c…`. A reader without that sibling gets a
`git clone` failure on a nonexistent local path — fail-closed and loud, which
is right, but nothing in the README tells them (a) which repository this is,
(b) that it must be a sibling directory named `cerberus-lean`, (c) that it must
first be built with that repository's own toolchain (lem, opam) per its docs.
Fix: a short "Prerequisites" paragraph before the code block stating exactly
those three things and the pinned commit. (Details in (5).)

**L-1. Three references to a record that is not on `main`.**
`../docs/2026-09-03_repin-scout.md` is cited by `cerberus-heaplang/
ARCHITECTURE.md` §7 Goal 1 ("scout: `../docs/2026-09-03_repin-scout.md`"), by
the Fuel row of the divergences table in `cerberus-heaplang/README.md` (the
"Home" column), and by `scripts/semantics-pin.env:49` ("scout record
docs/2026-09-03_repin-scout.md §3.3"). The file exists only on branch
`repin-scout` (commit 8847a2f, not an ancestor of HEAD). Fix: either add the
record under `docs/` or annotate each citation "(branch `repin-scout`)", as
`cerberus-heaplang/docs/2026-09-03_repin-fuel-notes.md:7` already does.

**L-2. Stale manifest count in ARCHITECTURE.** `cerberus-heaplang/
ARCHITECTURE.md:382` and `:432` both say "22 constructors, 25 rule rows, 0 red,
16 exhibit modules"; the committed `docs/CAPABILITY_MANIFEST.md` and the demo
README (`:76`) say 23 (`Frag.call` was added at C2). Fix: 23 in both places.

**L-3. Root README links outside the repository.** `README.md:8`:
"[cerberus-lean](../cerberus-lean) semantics". In an external clone `../
cerberus-lean` does not exist. Fix: name the repository and branch/commit
(the pin is `f95ef8d9c317fa6b50cf6691216a8c37b1d3eabf`; the local checkout's
`origin` is `github.com:OathTech/cerberus-lean`, branch `mdd/cerberus-lean`,
which contains the pin per its remote-tracking ref) or drop the link.

**L-4. Gate-runner header describes two builds.** `scripts/test_unit.sh:4-6`:
"The TRUST BASE is gates 1-2: the banned-methods grep and the two capped
builds, each of which elaborates its package's in-build axiom sweep". One
build now. Fix: "the capped build of cerberus-heaplang, which elaborates its
in-build axiom sweep".

**L-5. Wrong relative path in the walkthrough.** `cerberus-heaplang/docs/
WALKTHROUGH.md:1644`: "and `../docs/DECISIONS.md`" — from
`cerberus-heaplang/docs/` the register is `../../docs/DECISIONS.md` (the same
file gets this right at `:77`). Cosmetic sibling: `:1203` cites
`docs/2026-09-03_k2.5-notes.md`, which is package-relative, not
walkthrough-relative.

**L-6. `.gitignore:5` `/.refinedc-ws`** — the donor workspace that moved to the
branch. Harmless; drop the line or comment it.

**L-7. `scripts/semantics-pin.env:22`** cites "[USER 2026-09-02] resume note
Slice 1" — the pause/resume note is on `refinedc/dev`, not main. Comment-only;
annotate "(branch `refinedc/dev`)" or leave.

**N-1. `CLAUDE.md` assumes the operator's container.** Layout rows
`../deps/iris-lean` and `../cerberus-lean`; Building: "resolve offline through
the container's `deps/gitconfig` redirects (`capped` self-loads the container
env)"; the whole "Sandbox regime" paragraph. None of this is false, and
CLAUDE.md is agent working practice, but an external reader will find none of
it applies. Fix: one sentence at the top — "Paths beginning `../` refer to the
`cerberus-lean-proj` container this repository is developed inside; outside it,
see README 'Prerequisites'." Also `CLAUDE.md:41` "`--fast` = the build only"
vs the script's "gates 1-2 only" (grep + build) — cosmetic.

**N-2. `docs/AUDIT-BRIEF.md:8-9`**: "as the derisking demo for the
RefinedC-architecture port". It is a [USER 2026-09-02] quotation, so do not
alter it; add a parenthetical after it: "(longer-term work on branch
`refinedc/dev`; not on `main`)". This is the only standing (undated) document
on main that still calls the RefinedC layer "the port". See (3).

**N-3. `README.md` root, "Building" block, comment on line 2**: "capped;
elaborates the in-build axiom audit" — correct. The Lake side is consistent
with the lakefile: `defaultTargets = ["CerberusHeapLang"]`, toolchain
`leanprover/lean4:v4.32.2`, deps `batteries`/`Qq`/`iris` git-pinned and
`CerberusLean` as `path = "../.cerberus-ws/lean_frontend"`. `lake-manifest.json`
is committed and also carries the path dep, so a bare `lake build` without the
workspace fails loudly on the missing path. No build command on main is
internally inconsistent with the lakefiles; the only non-runnable step is
M-2's prerequisite.

The requested grep otherwise came back clean: no `RefinedCerberus`, `root
package` (other than M-1's line-wrapped instance), `setup-refinedc`, `port
ledger`, `port-map`, `gate 3`, `attachment charter` or `resume-note` outside
the register and the dated records. `RelSem` appears once, in
`semantics-pin.env:49-50`, correctly describing an upstream cerberus-lean
prune. Every other `RefinedC` mention outside the branch-pointer sentences is a
design-donor citation in Lean doc-comments or the walkthrough ("RefinedC's
`al_alive`", "RefinedC's `ghost_state.v`", …) — comparisons, not promises.
`Step.lean:903` cites `docs/2026-08-31_C1-change-manifest.md` and labels it
"cerberus-lean docs/…"; that file exists in cerberus-lean's `lean_frontend/
docs/`, so the citation is honest though not resolvable from this repo.

---

## (3) Is the RefinedC-family work presented as present or imminent?

No, on every shop-window surface. Verbatim:

- `README.md:24-28`: "Longer-term direction: an agent-driven C verification
  layer in the RefinedC design family, built above this logic. That work lives
  on the branch `refinedc/dev` … while it is brought to a presentable state;
  nothing of it is on `main`, and nothing here should be read as a port of
  RefinedC."
- `CLAUDE.md:21-26`: "Longer-term direction … lives on the branch
  `refinedc/dev` until it is presentable; nothing of it is on `main`."
- `cerberus-heaplang/README.md:28-30`: "This package is a demonstration of
  classical separation logic over Core and nothing more; it is not a port of
  RefinedC (the RefinedC-family layer is longer-term work on the branch
  `refinedc/dev`, not on `main`)."
- `cerberus-heaplang/lakefile.toml:5-8`: "the HeapLang-analog for the Cerberus
  Core engine, alongside the RefinedC-family layer, which lives on the branch
  `refinedc/dev`" — "alongside" is a shade too coexistent, but the branch is
  named in the same breath.

Two places pull the other way, both quotations of rulings rather than new
prose: `docs/AUDIT-BRIEF.md` ("the derisking demo for the RefinedC-architecture
port", N-2) and the head of `docs/DECISIONS.md` (see (4)). Neither says
"imminent"; both say "the port" as if it were the project's standing frame.
With N-2's parenthetical and the register note below, the tree is consistent.

---

## (4) Are the records and the register clearly marked as history?

**Dated records: yes.** The root README calls them "The package's dated
records (slice notes, independent audits, external reviews)" and "the dated
repository-level records (audits, …)". The demo README's Records section opens
"History, provenance and process live in dated files, not here." The
walkthrough's tail says "Records — design history, decision provenance, the
audits and reviews — are the dated files under `docs/`". Every such file is
date-prefixed. One record a newcomer will be pointed at by CLAUDE.md
("Founding rationale: `docs/2026-08-29_rules-of-engagement.md`") opens
"**Status: BLESSED [USER 2026-08-29] …** CLAUDE.md is the operating-manual form
of this document" and ratifies "RefinedC is a TARGET, not an end state" — true
as a record, but its status line reads as current. A one-line reading note is
optional; the date prefix and CLAUDE.md's word "founding" carry most of the
load.

**The register: not sufficiently.** `docs/DECISIONS.md` describes itself as an
"Append-only log of design rulings and their provenance" — chronology is
implied, supersession is not stated. Within the first 60 lines a newcomer
reads, verbatim:

> **2026-08-29 [USER] THE NORTH STAR** (ratified verbatim …): the product is a
> **Lean-native C verification framework** — RefinedC's architecture (ownership/
> refinement type system + Lithium-class goal-directed automation) rebuilt
> natively in Lean on iris-lean …

and "**Validation**: acceptance ladder = RefinedC's own examples/tutorial
suite". Set beside the root README's "nothing here should be read as a port of
RefinedC", a top-down reader has two contradictory statements of what the
product is and no signpost that the second (2026-09-03, "SHAREABLE MAIN …")
sits 1,400 lines later at the tail. The operator ruled the register stays on
main; the fix is framing, not content: (a) add to the register's header
paragraph (which is not an entry) two sentences — "Entries are chronological;
where they conflict, the later ruling governs. For what `main` contains today
read the 2026-09-03 SHAREABLE MAIN entry at the tail: the RefinedC-architecture
programme described in the 2026-08-29 entries continues on branch
`refinedc/dev`." — and (b) in `README.md:16-17` change "the append-only
register of rulings" to "the append-only, chronological register of rulings
(read the tail for the current state)". If the header must not be touched, the
same text as one final [AGENT] entry achieves it.

---

## (5) Buildability from the instructions as written

**Inside the operator's container: yes**, and the tail entry of DECISIONS
records the FULL gate at 24c2410 verbatim ("ALL GATES GREEN / GATE-EXIT=0",
312 export pins trio-exact). I did not re-run it.

**For an external reader: no, not from the README alone.** Trace of the three
"Building" lines:

1. `scripts/setup-cerberus-dep.sh` → `SRC="<parent of repo>/cerberus-lean"`;
   `git clone --no-checkout "$SRC" "$WS"` fails immediately if absent (fatal:
   repository does not exist). If present but unbuilt, section B stops: "B
   FAIL: $SRC/$p missing — primary checkout not built?". If present, built, but
   at a different commit whose primed paths differ from the pin, section B
   stops fail-closed with a diff stat. All of this is honest and loud; none of
   it is described in the README beyond "primed from a built checkout". The
   README does not say the checkout must be a sibling named `cerberus-lean`,
   nor that building it requires cerberus-lean's own toolchain (lem via
   opam, `make lean-prelude-src`, `make lean-native-obj`, a capped `lake
   build`) — a multi-hour prerequisite with its own dependency chain.
2. `../scripts/capped ~/.elan/bin/lake build` → `capped` prints "note — no
   scripts/env.sh found above …; proceeding with the current environment" and
   runs (cgroup-direct if delegated, else systemd-run, else a loud UNCAPPED
   warning — all disclosed in the script). Lake then resolves the git deps
   over the network: `batteries` and `Qq` at revs the lakefile says are the
   ones "iris-lean's 4.32.2 build vendored"; `iris` at `34390a0…`, which the
   local iris-lean checkout shows on `origin/master` of
   `leanprover-community/iris-lean` ("fix: `wp_rec` keeps the evaluation
   context flat (#657)"); `LemLib` (inherited through the semantics workspace)
   from `https://github.com/septract/lem-lean` at `045dcb0…`, which the local
   lem-lean checkout shows on `origin/mdd/lean-backend` of `OathTech/lem-lean`.
   Whether those two organisation repositories are public cannot be verified
   from this sandbox; if `cerberus-lean` or `lem-lean` is private, the README
   should say the semantics is available on request.
3. `scripts/test_unit.sh` → runs as described once 1-2 succeed.

**Does the README say so honestly?** Partially. It discloses that the
semantics enters as a primed path dependency and is "checked seam-by-seam
against the pin", which is true and is the important trust fact. It omits the
location, build-state and provenance requirements that make step 1 runnable,
and it links the semantics to a path outside the repository (L-3). The fix is
M-2: a "Prerequisites" paragraph naming the repository, the branch and the pin
commit, the sibling-directory requirement, and that the checkout must be built
per its own README before `setup-cerberus-dep.sh` is run. The
`--check` mode of the script is worth one line too.

---

## (6) Verdict

**Shareable after fixes M-1, M-2, L-1, L-2, L-3 and the register note in (4).**
Each is a one-to-five-sentence edit; none touches a statement or proof.

- M-1 is the only sentence on main that describes something absent as part of
  the trust base — it must go.
- M-2 and L-3 are the "Building" honesty items: without them an external
  reader's first command fails for reasons the README does not disclose.
- The register note (4) removes the one head-on contradiction between the root
  README and a document the README itself points to.
- L-1 and L-2 are dangling/stale facts a careful reader will trip on within
  the first hour.

L-4 through L-7 and N-1/N-2 are worth doing in the same pass but would not, on
their own, mislead anyone about what this repository is. Separately from
"misleading": there is no `LICENSE` file; that is an operator decision to make
before the repository is shared, not a documentation fix.

Nothing on main over-claims the logic. The PROVISIONAL / ROOT-OF-TRUST split,
the one-directional certification, the residual, the absence of a call rule
and of a C frontend, the `Expr []` restriction, and the seven-theorem headline
are stated the same way in the root README, the demo README, ARCHITECTURE and
the walkthrough, and the theorems named exist in the tree at the files given.
