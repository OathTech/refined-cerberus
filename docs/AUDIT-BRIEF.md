# Standing brief for auditors of refined-cerberus / cerberus-heaplang

[USER 2026-09-02] (DECISIONS.md, verbatim there). Every audit brief
links this file; findings are graded against it.

**What we are building.** A small, well-designed, minimal
Reynolds/O'Hearn-style separation logic over the real cerberus-lean
Core semantics (cerberus-heaplang), as the derisking demo for the (longer-term, branch `refinedc/dev`)
RefinedC-architecture port. The trust base is the cerberus-lean
operational semantics plus the proof artifacts themselves.

**What an audit is for.** Finding SUBSTANTIVE LOGICAL AND COVERAGE
GAPS within the declared scope: an unsound or vacuous rule, a
statement that does not say what the docs say it says, a construct
claimed as covered whose rule is not proved or not consumed, an
adequacy chain with a hole, a claim in a shop-window document that
the theorems do not support. "The actual logic itself must be
pristine, enough to make Reynolds and O'Hearn weep with joy."

**What an audit is NOT for.** Hardening against adversarial
contributors. "We do not want to make everything insanely hardened
against all possible attacks, that's out of scope and will slow us
down enormously." Gates are sized proportionate to demo-level work
and to moving fast: the build + the in-build axiom sweep + the
banned-methods grep are the trust base; everything else is a
speedbump (a report that catches honest drift).

**Recommending a new check is fine — bang for buck is the test.**
[USER 2026-09-02]: "We don't want to quite go so far as to say we
should never add a new check. But a gate should be high bang for
buck. No giant enumerative tables unless we are actually legitimately
worried about trust." So: a cheap check that catches a real class of
mistake is welcome; certification machinery, dependency-cone
checkers, layer cuts, planted-negative suites, frozen censuses, and
hand-maintained enumerative tables are not, unless the finding names
a trust property that is actually at risk in the tree and the check
is the cheapest way to make the mistake visible.

**Grading.** A gap in the logic or its coverage is High regardless
of how it was found. A missing check, a possible-in-principle way to
sneak an unproved claim past a name-level test, or a process gap is
at most a Note unless it hides a gap that actually exists in the
tree — say which, by dependency tracing of the live proof terms, not
by the existence of a check.

## Known open items — read before auditing

`docs/KNOWN-OPEN-ITEMS.md` is the register of everything already known,
disclosed and owned (upstream defects with requests filed, disclosed
statement-shape limitations, the hygiene queue, applied errata). Do NOT
re-cite an entry as a new finding; cite it only if the entry is wrong,
the item is worse than recorded, or a claimed mover has been missed.
