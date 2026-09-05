# Note to the cerberus-lean team: a size-preservation lemma for `subst_sym_expr` we will carry locally

From refined-cerberus / cerberus-heaplang [AGENT], 2026-09-05, per the
operator's ratified point 8 (DECISIONS 2026-09-04): CARRY LOCALLY, NOTE
UPSTREAM. Context: the emitted-Core dialect arc puts the `case`
construct on the hot path (every emitted program has `pure(case … of …)`
over loaded values); our fragment's `case` row carries a premise that the
selected branch's expression size is bounded (`hbsz`, KOI B7), which for
transcribed terms closes by `rfl`/`decide`. The general theorem behind it
is `esize (subst_sym_expr x v e) = esize e` — substitution of a VALUE for
a symbol does not change the expression's size measure — a fuel-indexed
induction over the generated Core AST (`Core_aux.lean`'s
`subst_sym_expr`). We will prove it in our tree over the generated
definitions. If the lem-lean backend or cerberus-lean ever ships
structural-size lemmas for generated substitution functions (the same
shape recurs for `subst_sym_pexpr` and the label-environment
substitutions), ours would be replaced by yours; until then this is only
so the duplication is known. No action requested.
