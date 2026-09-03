# Upstream note (for the cerberus-lean team's tray): `dynamic_addrs` is never cleaned, so `free` of a non-malloc'd object can be accepted after a zero-size `malloc` at the same base

Found 2026-09-03 while proving the demo's memory well-formedness invariant
(refined-cerberus, kill/free K0 audit finding N-1). Measured in BOTH the
Lean port and the un-forked upstream OCaml; the port is a faithful mirror,
so this is a Cerberus (concrete memory model) semantic imprecision, not a
cerberus-lean bug.

## The behaviour

Concrete memory model, upstream `memory/concrete/impl_mem.ml`
(`deps/cerberus-upstream`, the fork's merge-base):

- `allocate_region` (:1419-1436): `allocator size_n align_n` computes the
  address; the record is `{…; base= addr; size= size_n; ty= None; …}`;
  `dynamic_addrs= addr :: st.dynamic_addrs`. No check that `addr` is not
  the base of an existing allocation; zero-size regions are admitted
  (`size_n = 0` moves the cursor by nothing; if the alignment divides the
  current cursor, `addr` = the base of the most recently created object).
- `is_dynamic addr = List.mem addr st.dynamic_addrs` (:663).
- `kill` (dynamic and static arms): removes the allocation from
  `allocations`; NEVER removes from `dynamic_addrs` (the list has exactly
  one writer, `allocate_region`). `dynamic_addrs` may hold duplicates and
  bases of dead allocations.

Lean port (`lean_frontend/CerbMem.lean` at pin `ddcfc9199`): identical —
`allocateRegion` :1538-1548 (`size := sizeN.toNat`, no type, prepend), `killM`
:1573-1578 (checks `dynamicAddrs.contains alloc.base`; writes only
`deadAllocations`/`allocations`).

## The consequence

    p = create(int)          -- object at base B; cursor = B
    q = alloc(align, 0)      -- zero-size region; if align | B then base = B; B pushed
    free(p)                  -- dynamic kill of the CREATED object

`kill(dynamic, p)` passes the `is_dynamic` check because `B ∈ dynamic_addrs`,
and succeeds: the created (automatic-storage) object is freed with no UB
reported. In C this is undefined behaviour (free of a pointer not returned
by an allocation function, C11 7.22.3.3p2); Cerberus's UB179a ("kill of a
non-matching object") is exactly the UB that should fire and does not.
Reasoned from the code in both implementations; not executed (a Core test
program is a two-line exercise for whoever picks this up).

## What refined-cerberus does about it

The demo's `free` rule (K3) requires the metadata cell's `dynamic` flag,
which the state interpretation couples as `dynamic = true → base ∈
dynamic_addrs` (the one direction the engine preserves). Our precondition
therefore IMPLIES the engine's check (sound), and the program above is
outside the logic (deliberately incomplete on a program that is UB in C).
Recorded: refined-cerberus `docs/DECISIONS.md` (K0 range audit, N-1; K1).

## Suggested upstream fix

Either remove the base from `dynamic_addrs` in `kill`'s dynamic arm (the
list then tracks live dynamic allocations exactly and `is_dynamic` is
precise), or replace the list by a per-allocation `is_dynamic` flag on the
record (what the demo's ghost cell does), which also removes the
duplicate-address case. Both keep every other behaviour identical.
