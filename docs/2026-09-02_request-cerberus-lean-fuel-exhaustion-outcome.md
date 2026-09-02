# Request to the cerberus-lean team: a distinguished, transparent fuel-exhaustion outcome in the driver monad

[USER 2026-09-02] ruling that motivates this request (verbatim, DECISIONS.md):
"There should not be any reason for the driver to not be the actual, genuine,
legitimate, original Cerberus one. We should not be writing our own trusted
driver code." / "If we have limitations on the Cerberus side, we can in fact
make requests to the Cerberus team to improve the quality of Cerberus Lean.
This is the more appropriate way to deal with limitations like this, not to
invent some fake driver which doesn't give us the complete root of trust that
we're looking for."

Requester: refined-cerberus / cerberus-heaplang (the separation-logic demo over
Core). Pin at the time of the request: cerberus-lean `ddcfc919972a31bc43a0454e6b2e76a19e6c4594`,
LemLib `045dcb0`.

## What we need to state

Partial-correctness theorems about the SHIPPED driver, for programs that may
not terminate, in the shape

    ∀ fuel, every outcome of `runND (driver2_lemFuel fuel tds conc) st₀`
      is either (a) a terminal outcome satisfying the postcondition,
      or (b) FUEL EXHAUSTION — a value the kernel can recognise as such.

Our total-correctness production theorems already are statements about the
shipped `runND ∘ drive ∘ initial_driver_state` (they know a sufficient fuel).
Our partial-correctness exports are currently stated over a package-defined
loop (`driveU`) around the engine's `step_ctx`; the ruling above says that is
not acceptable as a root of trust, and we will restate them over the shipped
driver as soon as (b) is expressible.

## Why it is not expressible today

The Lem→Lean port makes the driver total with fuel. At fuel zero the
generated arms return the runtime's sentinel, e.g. (generated `Driver.lean`,
`driver2_lemFuel`; likewise `drive_nonmemory_steps_aux2_lemFuel`,
`print_eval_conv_aux_lemFuel`, `hack_lemFuel`, and `nd_bind_lemFuel` in
generated `Nondeterminism.lean`):

    | 0 => (fuelExhausted (ND (fun st => (NDkilled (Undef0 CerbLocation.Loc.unknown []), st))))

and in LemLib (`lean-lib/LemLib.lean`):

    @[implemented_by fuelExhaustedWithImpl]
    opaque fuelExhaustedWith {α : Type} (msg : String) (witness : α) : α := witness
    def fuelExhausted {α : Type} (witness : α) : α := fuelExhaustedWith "lem: fuel exhausted" witness

`fuelExhaustedWith` is deliberately OPAQUE ("the fuel-exhausted branch is not
provably equal to anything, in particular NOT to the witness") and loud at
runtime (panic). Both properties are right for their purpose — a wrong value
is never produced, and the kernel cannot prove the exhausted run equal to the
kill it would otherwise look like. But the consequence for statements is that
an out-of-fuel run of the shipped driver is an opaque term: no theorem can
classify it, so no theorem can quantify over all fuels and say anything about
the outcomes. (Note also that the witness chosen for the driver's arm is
`NDkilled (Undef0 Loc.unknown [])` — were the sentinel ever made transparent
as is, fuel exhaustion would become indistinguishable from undefined
behaviour at an unknown location, which is worse.)

## What we request

1. **A distinguished outcome for fuel exhaustion in the nondeterminism
   monad**, transparent to the kernel and distinct from every kill reason —
   e.g. a `kill_reason` constructor `FuelExhausted` (or an `nd_action`
   constructor) so that the fuel arm of every `ndM`-typed fueled worker is
       | 0 => ND (fun st => (NDkilled FuelExhausted, st))
   with NO opaque wrapper: the kernel sees exactly which outcome an
   out-of-fuel run produces.
2. **Runtime loudness preserved at the harness level, not by opacity**: the
   harnesses already classify KILL/HANG outcomes (mem-scale S0/S2); a
   `FuelExhausted` kill is a classifiable, fail-noisy outcome there, and
   `bind` propagates it like any kill (`nd_bind_lemFuel`'s `NDkilled` arm).
3. **Scope**: the driver loop (`driver2_lemFuel`), the ND bind
   (`nd_bind_lemFuel`), and the other `ndM`-typed fueled workers in
   `Driver.lean`. Fueled workers with PURE return types (e.g. `hack_lemFuel :
   … → value`, the `Core_reduction.lean` arms) may keep the opaque sentinel:
   they are not the driver's outcome and their exhaustion surfaces as the
   driver's, or is excluded by static bounds.
4. **A fuel-monotonicity lemma is welcome but not required**: with (1), we
   can prove what we need by induction on fuel ourselves.

The lem side (`declare {lean} fuel val` and the backend's choice of the
exhaustion default per worker) is where the change lives; the cerberus-lean
side chooses the constructor. We are happy to review the design note.

## Acceptance criterion (what we will prove once it lands)

    theorem <program>_certified_shipped (fuel : Nat) … :
      ∀ o ∈ runND (driver2_lemFuel fuel fmapEmpty false) dst₀,
        o.status = NDkilled FuelExhausted ∨ (o is Active-done ∧ post o.state)

stated over the shipped driver only, with `driveU` deleted from every
export. Until then our partial-correctness exports carry the label
PROVISIONAL: sound facts about `driveU`, not yet the root-of-trust statement.
