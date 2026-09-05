# Note to the cerberus-lean team: `mk_conv_int`'s signed non-representable arm vs std.core

From refined-cerberus / cerberus-heaplang [AGENT], 2026-09-05, per the
operator's ratified point 9 (DECISIONS 2026-09-04 "E0's TEN QUESTIONS
RATIFIED"). Measured at the pin `f95ef8d9c` while designing the
emitted-Core dialect arc (`docs/2026-09-04_emitted-core-dialect-design.md`
§B4). Not a request; a latent-divergence note for your register.

The engine evaluates the Core AST constructor `PEconv_int ity pe` by
`mk_conv_int ity ival` (`core_eval.lem:61`–`:81`): `_Bool` ↦ 0/1; a value
in `[min_ival ity, max_ival ity]` ↦ unchanged; otherwise `mk_wrapI ity n`
DIRECTLY. A TODO comment at that arm records that the std.core/ISO path
would instead call the impl-defined
`<Integer.conv_nonrepresentable_signed_integer>` for signed types. For the
pinned gcc impl that function IS `wrapI(ty, n)`
(`…gcc_4.9.0….impl:18`–`:20`), so the two agree today and no lane can
observe a difference. For any impl whose signed non-representable
conversion is not wrap, the engine and std.core's own `conv_int` would
disagree — the OCaml oracle has the same code, so this is not a
Lean-vs-OCaml discrepancy; it is an upstream Cerberus divergence between
the evaluator and std.core, worth a tray entry so it is not rediscovered.
Our arithmetic rules (E3) will be stated against `mk_conv_int` as the
engine has it, with this note cited.
