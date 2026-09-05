# Note to the cerberus-lean team: a size-preservation fact for `subst_sym_expr` we carry as a per-program premise (not proved)

From refined-cerberus / cerberus-heaplang [AGENT], 2026-09-05, per the
operator's ratified point 8 (DECISIONS 2026-09-04): CARRY LOCALLY, NOTE
UPSTREAM. Context: the emitted-Core dialect arc puts the `case`
construct on the hot path (every emitted program has `pure(case … of …)`
over loaded values); our fragment's `case` row carries a premise that the
selected branch's expression size is bounded (`hbsz` in `Frag.case_value`,
KOI B7), which for transcribed terms closes by `rfl`/`decide` per program.
The general theorem behind it would be `esize (subst_sym_expr x v e) =
esize e` — substitution of a VALUE for a symbol does not change the
expression's size measure — a fuel-indexed induction over the generated
Core AST (`Core_aux.lean`'s `subst_sym_expr`). STATUS, stated exactly: we
have NOT proved it and do not plan to in E3–E4; nothing in
`CerberusHeapLang/*.lean` states it (the premise is discharged per program
at each `case` witness). We keep the premise because the per-program
discharge is cheap and the general lemma is a duplication risk: if the
lem-lean backend or cerberus-lean ever ships structural-size lemmas for
generated substitution functions (the same shape recurs for
`subst_sym_pexpr` and the label-environment substitutions), we would
consume yours and drop the premise. This note exists only so that
duplication is known before either side proves it. No action requested.

Erratum (2026-09-05, E2 range audit R-3): the first version of this note
said "We will prove it in our tree"; that was not true of any plan — the
statement above is the truth.
