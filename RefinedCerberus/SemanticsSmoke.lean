/-
Arc-0 semantics-pin smoke: the cerberus-lean dependency resolves and
its generated modules are importable. References the engine's
join-time race criterion (the eunseq-rule anchor, DECISIONS
2026-08-30). Plumbing only, no content.
-/
import CerbMem

namespace RefinedCerberus

theorem semantics_smoke (f : CerbMem.Footprint) :
    CerbMem.overlapping f f = CerbMem.overlapping f f := rfl

end RefinedCerberus
