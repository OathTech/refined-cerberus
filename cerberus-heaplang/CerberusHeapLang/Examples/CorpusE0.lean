/-
CerberusHeapLang.Examples.CorpusE0 — THE CORPUS TRANSCRIPTIONS AND THE
SKELETON INSTRUMENT (dialect arc E1, extended at E2; [USER 2026-09-04]
ratified E0 question 3: the pipeline's Core enters a statement as a
HAND-TRANSCRIBED term checked by an EXECUTABLE EQUALITY speedbump against
the oracle's emitted Core).

Three things live here — data, an instrument, and membership witnesses:

1. THE TRANSCRIPTION TABLE `corpusTable`: for each corpus program
   (docs/corpus-e0/<name>.annot.core at the repository root) the
   procedure it names and the hand-transcribed `CoreExpr` of that
   procedure's body. E1 transcribes t1 (`t1Main`); E2 names its
   sub-terms (`t1LoadX`, `t1Spec3`, …). Later slices add rows.

2. THE SKELETON CHECK (`scripts/corpus_skeleton.lean` runs it): the
   SKELETON of a term — the preorder token stream of its expression
   nodes, each node contributing the annotations the pretty-printer
   shows (`Astd` strings, in the printer's order; one `loc` marker when
   `get_loc` finds an `Aloc`) followed by its node kind
   (`lets`/`letw`/`seq`/`bound`/`unseq`…`endunseq`/`pure`/`store`/…, the
   printer's keywords) and, SINCE E2, the constructor-level skeleton of
   the pure expressions under `pure`, under every action and under `run`
   (`pexprSkeleton`: the printed constructor/keyword names `Specified`,
   `Unspecified`, `Ivalignof`, `tuple`, `case`/`alt`/`endcase`, `undef`,
   `not`, `if`/`then`/`else`, `op` for an infix binop, `array_shift`,
   `__conv_int__`, `catch_exceptional_condition_<op>`, a `PEcall`'s
   printed name; every symbol, literal, ctype and typed pattern binder is
   the opaque token `leaf`) — must EQUAL the token stream read off the
   emitted text by `tokenizeProc`. The printer facts the two sides share:
   pp_core.ml:549–680 (`Astd` comments are PREPENDED by a fold, so they
   print in REVERSE list order, then the `get_loc` marker, then the node;
   the wildcard-unit `Esseq` prints as `e1 ; e2`; `Ewseq` always prints
   `let weak`; `bound(e)`; action keywords pp_core.ml:690–745); for pure
   expressions pp_core.ml:304–308 (`Specified(…)`/`Unspecified('ty')`
   loaded values), :338–372 (`pp_ctor`), :376–385 (patterns; a `Ctuple`
   pattern prints as a parenthesised list, a binder as `x: ty`, the
   wildcard as `_: ty`), :412–419 (`iop_string`), :436–503 (`pp_pexpr`:
   `undef(<<UB>>)`, `PEctor Ctuple` as a parenthesised list, other
   constructors `Name(args)`, `case … of | pat => e … end`,
   `array_shift(p, ty, n)`, `not(e)`, the infix `PEop`, `__conv_int__(ty,
   e)`, `catch_exceptional_condition_<op>(ty, e1, e2)`).

   WHAT THE SKELETON DOES NOT CHECK (E2 scope): symbols, literals, ctypes,
   binder types and memory orders are LEAVES (not compared); the pure
   expressions of `save` initialisers, `if`/`case` scrutinees at the
   EXPRESSION level, `let` (Elet), `memop`, `pcall`/`ccall` arguments are
   still OPAQUE (checked annotation-free only); the association of a `;`
   chain is not observable in the text (no parentheses are printed) and is
   not compared. FAIL-CLOSED where the instrument is blind: a pure
   expression node carrying a printed annotation (the printer's
   `maybe_print_location`), a text `{-# … #-}` marker inside a pure or
   opaque region, a list literal (`[`), a constructor or pure-expression
   form outside the vocabulary above, a value the printer spells in a
   shape the skeleton does not know (a pointer, a float, a struct) — each
   is an ERROR, not a pass. A precedence parenthesis the printer inserts
   around a nested infix operand would be read as a `tuple` and MISMATCH
   (loud, not silent). The printed name of a `PEcall` is compared as the
   text spells it (`conv_loaded_int`, the builtin printed without its
   symbol number) against the transcription's `SD_Id` string.

3. E2 MEMBERSHIP WITNESSES for t1's sub-terms: the sub-terms E2 admits
   are in `Frag` (`t1LoadX_frag`, `t1LoadY_frag`, `t1Spec3_frag`,
   `t1Spec1_frag`, `t1KillX_frag`) — constructive `Frag` derivations,
   kernel-checked; and the two E3 shapes are OUTSIDE the covered operand
   grammar by kernel decision (`t1_convLoadedInt_uncovered`: the `PEcall`;
   `t1_case_uncovered`: the `case` whose first branch is a
   `catch_exceptional_condition`). `t1Main` as a whole is NOT in the E2
   fragment (it needs `conv_loaded_int`, the `catch_exceptional_condition`
   branch — E3 — and `unseq` — E4).

Plants (the vacuity check the script runs on every row): dropping the
first `bound` of a transcription, every `Astd`, or (E2) the first
`Specified(…)` constructor under a `pure`, MUST make the check fail; a
plant that passes fails the script.
-/
import CerberusHeapLang.Soundness
import CerberusHeapLang.StdCore
import CerberusHeapLang.Examples.Layout

set_option autoImplicit false

namespace CerberusHeapLang.CorpusE0



/-! ## The skeleton of a term -/

/-- The printer's action keyword (pp_core.ml `pp_action`). -/
def actionKeyword : generic_action_ Unit sym → String
  | Create _ _ _ => "create"
  | CreateReadOnly _ _ _ _ => "create_readonly"
  | Alloc0 _ _ _ => "alloc"
  | Kill Dynamic0 _ => "free"
  | Kill (Static0 _) _ => "kill"
  | Store0 true _ _ _ _ => "store_lock"
  | Store0 false _ _ _ _ => "store"
  | Load0 _ _ _ => "load"
  | SeqRMW true _ _ _ _ => "seq_rmw_with_forward"
  | SeqRMW false _ _ _ _ => "seq_rmw"
  | RMW0 _ _ _ _ _ _ => "rmw"
  | Fence0 _ => "fence"
  | CompareExchangeStrong _ _ _ _ _ _ => "compare_exchange_strong"
  | CompareExchangeWeak _ _ _ _ _ _ => "compare_exchange_weak"
  | LinuxFence _ => "linux_fence"
  | LinuxLoad _ _ _ => "linux_load"
  | LinuxStore _ _ _ _ => "linux_store"
  | LinuxRMW _ _ _ _ => "linux_rmw"

/-- The pure-expression operands of an action (checked annotation-free). -/
def actionPexprs : generic_action_ Unit sym → List (generic_pexpr Unit sym)
  | Create p1 p2 _ => [p1, p2]
  | CreateReadOnly p1 p2 p3 _ => [p1, p2, p3]
  | Alloc0 p1 p2 _ => [p1, p2]
  | Kill _ p => [p]
  | Store0 _ p1 p2 p3 _ => [p1, p2, p3]
  | Load0 p1 p2 _ => [p1, p2]
  | SeqRMW _ p1 p2 _ p3 => [p1, p2, p3]
  | RMW0 p1 p2 p3 p4 _ _ => [p1, p2, p3, p4]
  | Fence0 _ => []
  | CompareExchangeStrong p1 p2 p3 p4 _ _ => [p1, p2, p3, p4]
  | CompareExchangeWeak p1 p2 p3 p4 _ _ => [p1, p2, p3, p4]
  | LinuxFence _ => []
  | LinuxLoad p1 p2 _ => [p1, p2]
  | LinuxStore p1 p2 p3 _ => [p1, p2, p3]
  | LinuxRMW p1 p2 p3 _ => [p1, p2, p3]

/-- The annotations the printer shows, as tokens. -/
def annotTokens (an : List annot) : List String :=
  (an.filterMap fun a => match a with | Astd s => some s!"std:{s}" | _ => none).reverse ++
  (match get_loc an with | some _ => ["loc"] | none => [])

/-- A printed annotation on an annotation list. -/
def hasShownAnnot (an : List annot) : Bool :=
  an.any fun a => match a with | Astd _ => true | Aloc _ => true | _ => false

/-- A pure expression is CLEAN when no node of it carries a printed
    annotation (the instrument is blind inside pure expressions; a
    shown annotation there is an error, not a pass). -/
partial def pexprClean : generic_pexpr Unit sym → Bool
  | Pexpr an _ pe =>
    !hasShownAnnot an &&
    match pe with
    | PEsym _ | PEimpl _ | PEval _ | PEundef _ _ => true
    | PEconstrained xs => xs.all fun x => pexprClean x.2
    | PEerror _ p => pexprClean p
    | PEctor _ ps => ps.all pexprClean
    | PEcase p alts => pexprClean p && alts.all fun x => pexprClean x.2
    | PEarray_shift p1 _ p2 => pexprClean p1 && pexprClean p2
    | PEmember_shift p _ _ => pexprClean p
    | PEmemop _ ps => ps.all pexprClean
    | PEnot p => pexprClean p
    | PEop _ p1 p2 => pexprClean p1 && pexprClean p2
    | PEconv_int _ p => pexprClean p
    | PEwrapI _ _ p1 p2 => pexprClean p1 && pexprClean p2
    | PEcatch_exceptional_condition _ _ p1 p2 => pexprClean p1 && pexprClean p2
    | PEstruct _ xs => xs.all fun x => pexprClean x.2
    | PEunion _ _ p => pexprClean p
    | PEcfunction p => pexprClean p
    | PEmemberof _ _ p => pexprClean p
    | PEcall _ ps => ps.all pexprClean
    | PElet _ p1 p2 => pexprClean p1 && pexprClean p2
    | PEif p1 p2 p3 => pexprClean p1 && pexprClean p2 && pexprClean p3
    | PEis_scalar p | PEis_integer p | PEis_signed p | PEis_unsigned p
    | PEbmc_assume p => pexprClean p
    | PEare_compatible p1 p2 => pexprClean p1 && pexprClean p2

def checkClean (pes : List (generic_pexpr Unit sym)) : Except String Unit :=
  if pes.all pexprClean then pure ()
  else throw "a pure expression carries a printed annotation (Astd/Aloc) — \
    the skeleton instrument is blind inside pure expressions; extend it (E2/E3)"

/-! ## E2: the constructor-level skeleton of a pure expression -/

/-- The printer's constructor name (pp_core.ml:338–372 `pp_ctor`; `Ctuple`
    prints as a parenthesised list, :481, so its token is `tuple`). The
    list constructors (`[]: ty`, `::`, pp_core.ml:458–480) and
    `CivNULLcap` (an extra printed argument) are outside the vocabulary —
    fail-closed. -/
def ctorName : ctor → Except String String
  | Ctuple => pure "tuple"
  | Cspecified => pure "Specified"
  | Cunspecified => pure "Unspecified"
  | Civalignof => pure "Ivalignof"
  | Civsizeof => pure "Ivsizeof"
  | Civmax => pure "Ivmax"
  | Civmin => pure "Ivmin"
  | Carray => pure "Array"
  | CivCOMPL => pure "IvCOMPL"
  | CivAND => pure "IvAND"
  | CivOR => pure "IvOR"
  | CivXOR => pure "IvXOR"
  | Cfvfromint => pure "Cfvfromint"
  | Civfromfloat => pure "Civfromfloat"
  | _ => throw "a list constructor or CivNULLcap in a pure expression: outside the \
    skeleton's vocabulary (fail-closed; extend `ctorName` deliberately)"

/-- pp_core.ml:412–419 `iop_string`. -/
def iopSuffix : iop → String
  | IOpAdd => "_add"
  | IOpSub => "_sub"
  | IOpMul => "_mul"
  | IOpShl => "_shl"
  | IOpShr => "_shr"
  | IOpDiv => "_div"
  | IOpRem_t => "_rem_t"

/-- A VALUE's skeleton: the printer spells loaded values and tuples with
    the same surface as the constructors (pp_core.ml:304–308), so a
    transcription may write `Specified(3)` as `PEctor Cspecified [PEval 3]`
    or as `PEval (Vloaded (LVspecified 3))` — both print `Specified(3)`
    and both skeletonise to `Specified leaf`. Integers, ctypes, `Unit`,
    `True`/`False` are leaves; a pointer/float/array/struct/union value or
    a list is outside the vocabulary (fail-closed). -/
partial def valueSkeleton : value → Except String (List String)
  | Vunit | Vtrue | Vfalse | Vctype _ => pure ["leaf"]
  | Vobject (OVinteger _) => pure ["leaf"]
  | Vloaded (LVspecified ov) => do pure ("Specified" :: (← valueSkeleton (Vobject ov)))
  | Vloaded (LVunspecified _) => pure ["Unspecified", "leaf"]
  | Vtuple vs => do pure ("tuple" :: (← vs.mapM valueSkeleton).flatten)
  | _ => throw "a value the printer spells in a shape outside the skeleton's vocabulary \
    (pointer/float/array/struct/union/list) — fail-closed"

/-- A PATTERN's skeleton (pp_core.ml:376–385): a binder `x: ty` or the
    wildcard `_: ty` is a `leaf`; a constructor pattern is its name then
    its sub-patterns; a tuple pattern is `tuple` then its components. -/
partial def patSkeleton : pattern → Except String (List String)
  | Pattern an p => do
    if hasShownAnnot an then throw "a pattern carries a printed annotation"
    match p with
    | CaseBase _ => pure ["leaf"]
    | CaseCtor c ps => do pure ((← ctorName c) :: (← ps.mapM patSkeleton).flatten)

/-- THE PURE-EXPRESSION SKELETON (pp_core.ml:436–503 `pp_pexpr`). -/
partial def pexprSkeleton : generic_pexpr Unit sym → Except String (List String)
  | Pexpr an _ pe => do
    if hasShownAnnot an then
      throw "a pure expression node carries a printed annotation (Astd/Aloc) — the \
        skeleton compares no location inside pure expressions (fail-closed)"
    match pe with
    | PEsym _ => pure ["leaf"]
    | PEval v => valueSkeleton v
    | PEundef _ _ => pure ["undef"]
    | PEctor c ps => do pure ((← ctorName c) :: (← ps.mapM pexprSkeleton).flatten)
    | PEcase p alts => do
      let sp ← pexprSkeleton p
      let sa ← alts.mapM fun x => do
        pure ("alt" :: (← patSkeleton x.1) ++ (← pexprSkeleton x.2))
      pure ("case" :: sp ++ sa.flatten ++ ["endcase"])
    | PEcall (Sym (Symbol _ _ (SD_Id name))) ps => do
      pure (name :: (← ps.mapM pexprSkeleton).flatten)
    | PEcall (Impl c) ps => do
      pure (s!"impl:{string_of_implementation_constant c}" ::
        (← ps.mapM pexprSkeleton).flatten)
    | PEcall _ _ => throw "a PEcall at a name the printer does not spell as an identifier"
    | PEconv_int _ p => do pure ("__conv_int__" :: "leaf" :: (← pexprSkeleton p))
    | PEcatch_exceptional_condition _ op p1 p2 => do
      pure (("catch_exceptional_condition" ++ iopSuffix op) :: "leaf" ::
        (← pexprSkeleton p1) ++ (← pexprSkeleton p2))
    | PEwrapI _ op p1 p2 => do
      pure (("wrapI" ++ iopSuffix op) :: "leaf" :: (← pexprSkeleton p1) ++ (← pexprSkeleton p2))
    | PEop _ p1 p2 => do pure ((← pexprSkeleton p1) ++ "op" :: (← pexprSkeleton p2))
    | PEnot p => do pure ("not" :: (← pexprSkeleton p))
    | PEif p1 p2 p3 => do
      pure ("if" :: (← pexprSkeleton p1) ++ "then" :: (← pexprSkeleton p2) ++
        "else" :: (← pexprSkeleton p3))
    | PEarray_shift p1 _ p2 => do
      pure ("array_shift" :: (← pexprSkeleton p1) ++ "leaf" :: (← pexprSkeleton p2))
    -- E3 (std.core bodies): `is_unsigned(pe)` prints as a call-shaped keyword
    -- (pp_core.ml `pp_pexpr` PEis_unsigned arm); an implementation constant
    -- prints as `<Name>` (pp_core.ml `pp_impl`, `Implementation.
    -- string_of_implementation_constant`), and a call at one is that token
    -- followed by its arguments.
    | PEis_unsigned p => do pure ("is_unsigned" :: (← pexprSkeleton p))
    | PEimpl c => pure [s!"impl:{string_of_implementation_constant c}"]
    | _ => throw "a pure-expression form outside the skeleton's vocabulary (fail-closed; \
      extend `pexprSkeleton` deliberately, with the pp_core.ml cite)"

def pexprsSkeleton (pes : List (generic_pexpr Unit sym)) : Except String (List String) := do
  pure (← pes.mapM pexprSkeleton).flatten

/-- An ACTION's operand skeleton: `kill('ty', p)` prints the static kind's
    ctype as a first argument (pp_core.ml `pp_action`), a leaf; every other
    operand is a pure expression. -/
def actionSkeleton (act : generic_action_ Unit sym) : Except String (List String) :=
  match act with
  | Kill (Static0 _) p => do pure ("leaf" :: (← pexprSkeleton p))
  | act => pexprsSkeleton (actionPexprs act)

/-- THE SKELETON: the preorder token stream of the expression nodes. -/
partial def skeleton : CoreExpr → Except String (List String)
  | Expr an e => do
    let hd := annotTokens an
    match e with
    | Epure pe => do pure (hd ++ ["pure"] ++ (← pexprSkeleton pe))
    | Ememop _ pes => do checkClean pes; pure (hd ++ ["memop"])
    | Eaction (Paction pol (Action _ _ act)) => do
      let neg := match pol with | polarity.Pos => [] | polarity.Neg0 => ["neg"]
      pure (hd ++ neg ++ [actionKeyword act] ++ (← actionSkeleton act))
    | Ecase pe alts => do
      checkClean [pe]
      let bodies ← alts.mapM fun x => skeleton x.2
      pure (hd ++ ["case"] ++ bodies.flatten ++ ["endcase"])
    | Elet _ pe e2 => do checkClean [pe]; pure (hd ++ ["let"] ++ (← skeleton e2))
    | Eif pe e2 e3 => do
      checkClean [pe]; pure (hd ++ ["if"] ++ (← skeleton e2) ++ (← skeleton e3))
    | Eccall _ pty pf pes => do checkClean (pty :: pf :: pes); pure (hd ++ ["ccall"])
    | Eproc _ _ pes => do checkClean pes; pure (hd ++ ["pcall"])
    | Eunseq es => do
      let ts ← es.mapM skeleton
      pure (hd ++ ["unseq"] ++ ts.flatten ++ ["endunseq"])
    | Ewseq _ e1 e2 => do pure (hd ++ ["letw"] ++ (← skeleton e1) ++ (← skeleton e2))
    | Esseq (Pattern _ (CaseBase (none, BTy_unit))) e1 e2 => do
      pure (hd ++ (← skeleton e1) ++ ["seq"] ++ (← skeleton e2))
    | Esseq _ e1 e2 => do pure (hd ++ ["lets"] ++ (← skeleton e1) ++ (← skeleton e2))
    | Ebound b => do pure (hd ++ ["bound"] ++ (← skeleton b))
    | End es => do
      let ts ← es.mapM skeleton
      pure (hd ++ ["nd"] ++ ts.flatten ++ ["endnd"])
    | Esave _ inits body => do
      checkClean (inits.map fun x => x.2.2)
      pure (hd ++ ["save"] ++ (← skeleton body))
    | Erun _ _ pes => do pure (hd ++ ["run"] ++ (← pexprsSkeleton pes))
    | Epar es => do
      let ts ← es.mapM skeleton
      pure (hd ++ ["par"] ++ ts.flatten ++ ["endpar"])
    | Ewait _ => pure (hd ++ ["wait"])
    | Eannot _ b => do pure (hd ++ ["annot"] ++ (← skeleton b))
    | Eexcluded _ (Action _ _ act) => do
      checkClean (actionPexprs act); pure (hd ++ ["excluded"])

/-! ## The tokenizer of the emitted text -/

inductive Frame where
  | bound | unseq | nd | par | annot | neg | caseF
  deriving Repr, BEq, Inhabited

def isIdentChar (c : Char) : Bool := Bool.or c.isAlphanum (c == '_')

/-- `"` or `'` (the two quote characters of printed Core). -/
def isQuote (c : Char) : Bool := Bool.or (c == Char.ofNat 34) (c == Char.ofNat 39)

def startsWith (cs : List Char) (s : String) : Bool := s.toList.isPrefixOf cs

/-- The keyword `kw` stands alone at the head of `cs`. -/
def atKeyword (cs : List Char) (kw : String) : Bool :=
  startsWith cs kw &&
  match cs.drop kw.length with
  | [] => true
  | c :: _ => !isIdentChar c

partial def takeIdent (cs : List Char) (acc : String := "") : String × List Char :=
  match cs with
  | c :: rest => if isIdentChar c then takeIdent rest (acc.push c) else (acc, cs)
  | [] => (acc, [])

/-- Skip a quoted literal (`"…"` or `'…'`, no escapes in printed Core). -/
partial def skipQuoted (q : Char) : List Char → Except String (List Char)
  | [] => throw "unterminated quoted literal"
  | c :: rest => if c == q then pure rest else skipQuoted q rest

/-- Skip an OPAQUE region up to the matching close of an already-opened
    `(` (depth 1 at entry): pure-expression contents. A `{-# … #-}`
    marker inside is an error (the instrument would be blind to it). -/
partial def skipBalanced (cs : List Char) (depth : Nat := 1) : Except String (List Char) :=
  match cs with
  | [] => throw "unbalanced parentheses in an opaque region"
  | c :: rest =>
    if startsWith cs "{-#" then throw "an annotation marker inside an opaque (pure-expression) region"
    else if isQuote c then do skipBalanced (← skipQuoted c rest) depth
    else if Bool.or (c == '(') (c == '[') then skipBalanced rest (depth + 1)
    else if Bool.or (c == ')') (c == ']') then
      if depth == 1 then pure rest else skipBalanced rest (depth - 1)
    else skipBalanced rest depth

/-- Skip at depth 0 until the standalone keyword `kw`; return the rest
    after it. Parentheses/brackets nest; quoted literals are skipped; a
    marker is an error. -/
partial def skipUntilKw (cs : List Char) (kw : String) (depth : Nat := 0) :
    Except String (List Char) :=
  match cs with
  | [] => throw s!"keyword `{kw}` not found"
  | c :: rest =>
    if startsWith cs "{-#" then throw s!"an annotation marker before `{kw}` inside a skipped region"
    else if depth == 0 && atKeyword cs kw &&
        (match cs with | _ => true) then pure (cs.drop kw.length)
    else if isQuote c then do skipUntilKw (← skipQuoted c rest) kw depth
    else if Bool.or (c == '(') (c == '[') then skipUntilKw rest kw (depth + 1)
    else if Bool.or (c == ')') (c == ']') then skipUntilKw rest kw (depth - 1)
    else skipUntilKw rest kw depth

/-- Skip at depth 0 until the character `ch`; return the rest after it. -/
partial def skipUntilChar (cs : List Char) (ch : Char) (depth : Nat := 0) :
    Except String (List Char) :=
  match cs with
  | [] => throw s!"`{ch}` not found"
  | c :: rest =>
    if startsWith cs "{-#" then throw s!"an annotation marker before `{ch}` inside a skipped region"
    else if depth == 0 && c == ch then pure rest
    else if isQuote c then do skipUntilChar (← skipQuoted c rest) ch depth
    else if Bool.or (c == '(') (c == '[') then skipUntilChar rest ch (depth + 1)
    else if Bool.or (c == ')') (c == ']') then skipUntilChar rest ch (depth - 1)
    else skipUntilChar rest ch depth

partial def skipWs : List Char → List Char
  | c :: rest => if c.isWhitespace then skipWs rest else c :: rest
  | [] => []

/-- Expect `(` (after whitespace) and return the rest after it. -/
def expectParen (cs : List Char) (what : String) : Except String (List Char) :=
  match skipWs cs with
  | '(' :: rest => pure rest
  | _ => throw s!"expected `(` after `{what}`"

/-- Take the marker content after `{-#`, up to `#-}`. -/
partial def takeMarker (cs : List Char) (acc : String := "") : Except String (String × List Char) :=
  match cs with
  | [] => throw "unterminated `{-#` marker"
  | c :: rest =>
    if startsWith cs "#-}" then pure (acc, cs.drop 3) else takeMarker rest (acc.push c)

/-- Skip a number literal (digits; the printer prints integers in decimal). -/
partial def skipNumber : List Char → List Char
  | c :: rest => if c.isDigit then skipNumber rest else c :: rest
  | [] => []

/-- Skip a printed type after a binder's `:` — at depth 0 up to (not
    consuming) `,`, `)` or `=>`; parentheses nest (`(loaded integer,loaded
    integer)`). -/
partial def skipType (cs : List Char) (depth : Nat := 0) : Except String (List Char) :=
  match cs with
  | [] => throw "unterminated type annotation in a pure expression"
  | c :: rest =>
    if Bool.and (depth == 0) (Bool.or (Bool.or (c == ',') (c == ')')) (startsWith cs "=>")) then pure cs
    else if c == '(' then skipType rest (depth + 1)
    else if c == ')' then skipType rest (depth - 1)
    else skipType rest depth

/-- The characters of the printer's infix binops (`pp_binop`: `+ - * / rem_t
    rem_f ^ = > < >= <= /\\ \\/`). -/
def isOpChar (c : Char) : Bool :=
  ['+', '-', '*', '/', '\\', '^', '=', '<', '>', '!', '%'].contains c

partial def skipOps : List Char → List Char
  | c :: rest => if isOpChar c then skipOps rest else c :: rest
  | [] => []

/-- E3: the name inside `<…>` (identifier characters and `.`). -/
partial def takeImpl (cs : List Char) (acc : String := "") : String × List Char :=
  match cs with
  | c :: rest => if Bool.or (isIdentChar c) (c == '.') then takeImpl rest (acc.push c) else (acc, cs)
  | [] => (acc, [])

/-- E3: strip std.core SOURCE comments (`-- …` to end of line; `{- … -}`
    blocks, non-nesting in std.core) before tokenizing a `fun` body. The
    printed corpus texts carry none (the printer emits `{-# … #-}` markers,
    which are NOT comments and are left alone here). -/
partial def stripComments (cs : List Char) (acc : List Char := []) : List Char :=
  match cs with
  | [] => acc.reverse
  | c :: rest =>
    if startsWith cs "{-#" then stripComments (cs.drop 3) ('#' :: '-' :: '{' :: acc)
    else if startsWith cs "{-" then
      let rec skipBlock : List Char → List Char
        | [] => []
        | d :: r => if startsWith (d :: r) "-}" then r.drop 1 else skipBlock r
      stripComments (skipBlock (cs.drop 2)) acc
    else if startsWith cs "--" then
      stripComments (cs.dropWhile (· != '\n')) acc
    else stripComments rest (c :: acc)

/-- E2: THE PURE-EXPRESSION TOKENIZER over the text inside an opened `(`
    (`pure(`, an action's or a `run`'s argument list; depth 1 at entry,
    `depth` counts the OPEN parentheses inside the region): returns the
    tokens and the rest after the region's closing `)`. An identifier
    followed by `(` is a constructor/keyword/call name (its own token, the
    arguments inline); a bare `(` is a `tuple`; an identifier followed by
    `:` is a typed binder (`leaf`, its type skipped); any other identifier,
    a number, a quoted ctype is a `leaf`; `case`/`|`/`=>`/`end` give
    `case`/`alt`/(nothing)/`endcase`; `if`/`then`/`else` are themselves;
    an operator run is `op`; `undef(…)`'s angle-bracketed payload is
    opaque; `,` and `of` are separators. A marker or a list literal is an
    ERROR. -/
partial def pexScan (cs : List Char) (depth : Nat) (toks : Array String) :
    Except String (Array String × List Char) :=
  match cs with
  | [] => throw "unterminated pure-expression region"
  | c :: rest =>
    if startsWith cs "{-#" then
      throw "an annotation marker inside a pure expression — the skeleton compares none there"
    else if Bool.or c.isWhitespace (c == ',') then pexScan rest depth toks
    else if c == ')' then
      if depth == 1 then pure (toks, rest) else pexScan rest (depth - 1) toks
    else if c == '(' then pexScan rest (depth + 1) (toks.push "tuple")
    else if c == '[' then throw "a list literal in a pure expression: outside the vocabulary"
    else if isQuote c then do pexScan (← skipQuoted c rest) depth (toks.push "leaf")
    else if c.isDigit then pexScan (skipNumber rest) depth (toks.push "leaf")
    else if Bool.and (c == '-') (match rest with | d :: _ => d.isDigit | [] => false) then
      pexScan (skipNumber rest) depth (toks.push "leaf")
    else if startsWith cs "=>" then pexScan (cs.drop 2) depth toks
    else if Bool.and (c == '<') (match rest with | d :: _ => d.isAlpha | [] => false) then do
      -- E3: an implementation constant `<Name>` (std.core source; the printer's `pp_impl`)
      let (name, rest') := takeImpl rest
      match rest' with
      | '>' :: r =>
        -- a call at the constant: `<Name>(args)` — the arguments inline, as at an identifier
        match skipWs r with
        | '(' :: r' => pexScan r' (depth + 1) (toks.push s!"impl:{name}")
        | _ => pexScan r depth (toks.push s!"impl:{name}")
      | _ => throw "unterminated `<…>` implementation constant"
    else if c == '|' then pexScan rest depth (toks.push "alt")
    else if isOpChar c then pexScan (skipOps rest) depth (toks.push "op")
    else if Bool.or c.isAlpha (c == '_') then
      let (ident, rest') := takeIdent cs
      match ident with
      | "case" => pexScan rest' depth (toks.push "case")
      | "of" => pexScan rest' depth toks
      | "end" => pexScan rest' depth (toks.push "endcase")
      | "if" | "then" | "else" => pexScan rest' depth (toks.push ident)
      | "undef" => do
        pexScan (← skipBalanced (← expectParen rest' ident)) depth (toks.push "undef")
      | _ =>
        match skipWs rest' with
        | '(' :: r => pexScan r (depth + 1) (toks.push ident)
        | ':' :: ':' :: _ => throw "a list cons `::` in a pure expression: outside the vocabulary"
        | ':' :: r => do pexScan (← skipType r) depth (toks.push "leaf")
        | _ => pexScan rest' depth (toks.push "leaf")
    else throw s!"unexpected character `{c}` in a pure expression"

/-- Tokenize the pure-expression region after `kw(` and append. -/
def pexRegion (cs : List Char) (toks : Array String) : Except String (Array String × List Char) :=
  pexScan cs 1 toks

/-- The keywords whose parenthesised operands the E2 skeleton READS:
    `pure` and the actions (`actionSkeleton`). -/
def pexKeywords : List String :=
  ["pure", "create", "create_readonly", "alloc", "kill", "free", "store", "store_lock", "load",
   "seq_rmw", "seq_rmw_with_forward", "rmw", "fence", "compare_exchange_strong",
   "compare_exchange_weak", "linux_fence", "linux_load", "linux_store", "linux_rmw"]

/-- Leaf keywords whose parenthesised contents stay OPAQUE (the Lean side
    checks them annotation-free only): `memop`, `pcall`, `ccall`, `wait`. -/
def leafKeywords : List String := ["memop", "pcall", "ccall", "wait"]

/-- THE TOKENIZER over the body of one procedure (the text after `:=`;
    stops at the next top-level `proc`/`fun`/`glob` or at the end). -/
partial def scan (cs : List Char) (toks : Array String) (frames : List Frame) :
    Except String (Array String) :=
  match cs with
  | [] => if frames.isEmpty then pure toks else throw "unclosed frames at end of text"
  | c :: rest =>
    if c.isWhitespace then scan rest toks frames
    else if startsWith cs "{-#" then do
      let (content, rest') ← takeMarker (cs.drop 3)
      let t := content.trimAscii.toString
      let tok := if t.startsWith "<" then "loc" else s!"std:{t}"
      scan rest' (toks.push tok) frames
    else if c == ';' then scan rest (toks.push "seq") frames
    else if c == ',' then scan rest toks frames
    else if c == ')' then
      match frames with
      | [] => throw "unexpected `)`"
      | f :: fs =>
        match f with
        | .bound | .annot | .neg => scan rest toks fs
        | .unseq => scan rest (toks.push "endunseq") fs
        | .nd => scan rest (toks.push "endnd") fs
        | .par => scan rest (toks.push "endpar") fs
        | .caseF => throw "`)` closes a `case` (expected `end`)"
    else if c == '|' then
      match frames with
      | .caseF :: _ => do scan (← skipUntilKw rest "=>") toks frames
      | _ => throw "`|` outside a case"
    else if Bool.or c.isAlpha (c == '_') then
      let (ident, rest') := takeIdent cs
      match ident with
      | "proc" | "fun" | "glob" =>
        if frames.isEmpty then pure toks else throw s!"`{ident}` inside an open frame"
      | "let" =>
        let r := skipWs rest'
        if atKeyword r "strong" then do
          scan (← skipUntilChar (r.drop 6) '=') (toks.push "lets") frames
        else if atKeyword r "weak" then do
          scan (← skipUntilChar (r.drop 4) '=') (toks.push "letw") frames
        else do
          let r1 ← skipUntilChar r '='
          scan (← skipUntilKw r1 "in") (toks.push "let") frames
      | "bound" => do scan (← expectParen rest' ident) (toks.push "bound") (.bound :: frames)
      | "unseq" => do scan (← expectParen rest' ident) (toks.push "unseq") (.unseq :: frames)
      | "nd" => do scan (← expectParen rest' ident) (toks.push "nd") (.nd :: frames)
      | "par" => do scan (← expectParen rest' ident) (toks.push "par") (.par :: frames)
      | "neg" => do scan (← expectParen rest' ident) (toks.push "neg") (.neg :: frames)
      | "annot" => do
        let r ← match skipWs rest' with
          | '[' :: r => skipBalanced r
          | _ => throw "expected `[` after `annot`"
        scan (← expectParen r ident) (toks.push "annot") (.annot :: frames)
      | "excluded" => do
        let r ← match skipWs rest' with
          | '[' :: r => skipBalanced r
          | _ => throw "expected `[` after `excluded`"
        scan (← skipBalanced (← expectParen r ident)) (toks.push "excluded") frames
      | "save" => do scan (← skipUntilKw rest' "in") (toks.push "save") frames
      | "run" => do
        let (_, r) := takeIdent (skipWs rest')
        let (toks', r') ← pexRegion (← expectParen r ident) (toks.push "run")
        scan r' toks' frames
      | "if" => do scan (← skipUntilKw rest' "then") (toks.push "if") frames
      | "case" => do scan (← skipUntilKw rest' "of") (toks.push "case") (.caseF :: frames)
      | "end" =>
        match frames with
        | .caseF :: fs => scan rest' (toks.push "endcase") fs
        | _ => throw "`end` outside a case"
      | "then" | "else" | "in" | "of" => scan rest' toks frames
      | _ =>
        if pexKeywords.contains ident then do
          let (toks', r') ← pexRegion (← expectParen rest' ident) (toks.push ident)
          scan r' toks' frames
        else if leafKeywords.contains ident then do
          scan (← skipBalanced (← expectParen rest' ident)) (toks.push ident) frames
        else throw s!"unexpected identifier `{ident}` at expression level"
    else throw s!"unexpected character `{c}`"

/-- Locate `proc <name>` and tokenize its body (after `:=`). -/
def tokenizeProc (text : String) (name : String) : Except String (List String) := do
  let cs := text.toList
  let rec find (cs : List Char) : Except String (List Char) :=
    match cs with
    | [] => throw s!"`proc {name}` not found"
    | _ :: rest =>
      if atKeyword cs "proc" && atKeyword (skipWs (cs.drop 4)) name then pure (cs.drop 4)
      else find rest
  let body ← find cs
  let body ← skipUntilKw body ":="
  let toks ← scan body #[] []
  pure toks.toList

/-- E3: locate `fun <name>` in std.core SOURCE text and tokenize its body
    (after `:=`, up to the next top-level `fun`/`proc`/`glob` or the end)
    as ONE pure-expression region: comments stripped, the body wrapped in
    a parenthesis pair and read by `pexScan` (a std.core function body is
    a pure expression; the E2 tokenizer's vocabulary plus E3's
    `<impl>` constants). -/
def tokenizeFun (text : String) (name : String) : Except String (List String) := do
  let cs := stripComments text.toList
  let rec find (cs : List Char) : Except String (List Char) :=
    match cs with
    | [] => throw s!"`fun {name}` not found"
    | _ :: rest =>
      if atKeyword cs "fun" && atKeyword (skipWs (cs.drop 3)) name then pure (cs.drop 3)
      else find rest
  let body ← find cs
  let body ← skipUntilKw body ":="
  -- the body ends at the next top-level definition keyword (or the end)
  let rec cut (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if Bool.or (Bool.or (atKeyword cs "fun") (atKeyword cs "proc")) (atKeyword cs "glob") then acc.reverse
      else cut rest (c :: acc)
  let bodyText := cut body []
  let (toks, _) ← pexScan (bodyText ++ [')']) 1 #[]
  pure toks.toList

/-! ## The plants (negative fixtures: each MUST break the check) -/

/-- Drop the first `bound` node (preorder). -/
partial def dropFirstBound : CoreExpr → CoreExpr × Bool
  | Expr an e =>
    match e with
    | Ebound b => (b, true)
    | Esseq pat e1 e2 =>
      let (e1', d) := dropFirstBound e1
      if d then (Expr an (Esseq pat e1' e2), true)
      else let (e2', d2) := dropFirstBound e2; (Expr an (Esseq pat e1 e2'), d2)
    | Ewseq pat e1 e2 =>
      let (e1', d) := dropFirstBound e1
      if d then (Expr an (Ewseq pat e1' e2), true)
      else let (e2', d2) := dropFirstBound e2; (Expr an (Ewseq pat e1 e2'), d2)
    | Eunseq es =>
      let rec go : List CoreExpr → List CoreExpr × Bool
        | [] => ([], false)
        | x :: xs =>
          let (x', d) := dropFirstBound x
          if d then (x' :: xs, true) else let (xs', d') := go xs; (x :: xs', d')
      let (es', d) := go es
      (Expr an (Eunseq es'), d)
    | Eannot ds b => let (b', d) := dropFirstBound b; (Expr an (Eannot ds b'), d)
    | Esave sb inits b => let (b', d) := dropFirstBound b; (Expr an (Esave sb inits b'), d)
    | Eif pe e2 e3 =>
      let (e2', d) := dropFirstBound e2
      if d then (Expr an (Eif pe e2' e3), true)
      else let (e3', d3) := dropFirstBound e3; (Expr an (Eif pe e2 e3'), d3)
    | Elet pat pe b => let (b', d) := dropFirstBound b; (Expr an (Elet pat pe b'), d)
    | _ => (Expr an e, false)

/-- E2 plant: unwrap the first `pure(Specified(e))` met in preorder into
    `pure(e)` (the token `Specified` disappears from the skeleton). -/
partial def unwrapFirstSpecified : CoreExpr → CoreExpr × Bool
  | Expr an e =>
    match e with
    | Epure (Pexpr _ _ (PEctor Cspecified [p])) => (Expr an (Epure p), true)
    | Esseq pat e1 e2 =>
      let (e1', d) := unwrapFirstSpecified e1
      if d then (Expr an (Esseq pat e1' e2), true)
      else let (e2', d2) := unwrapFirstSpecified e2; (Expr an (Esseq pat e1 e2'), d2)
    | Ewseq pat e1 e2 =>
      let (e1', d) := unwrapFirstSpecified e1
      if d then (Expr an (Ewseq pat e1' e2), true)
      else let (e2', d2) := unwrapFirstSpecified e2; (Expr an (Ewseq pat e1 e2'), d2)
    | Eunseq es =>
      let rec go : List CoreExpr → List CoreExpr × Bool
        | [] => ([], false)
        | x :: xs =>
          let (x', d) := unwrapFirstSpecified x
          if d then (x' :: xs, true) else let (xs', d') := go xs; (x :: xs', d')
      let (es', d) := go es
      (Expr an (Eunseq es'), d)
    | Ebound b => let (b', d) := unwrapFirstSpecified b; (Expr an (Ebound b'), d)
    | Eannot ds b => let (b', d) := unwrapFirstSpecified b; (Expr an (Eannot ds b'), d)
    | Esave sb inits b => let (b', d) := unwrapFirstSpecified b; (Expr an (Esave sb inits b'), d)
    | Eif pe e2 e3 =>
      let (e2', d) := unwrapFirstSpecified e2
      if d then (Expr an (Eif pe e2' e3), true)
      else let (e3', d3) := unwrapFirstSpecified e3; (Expr an (Eif pe e2 e3'), d3)
    | Elet pat pe b => let (b', d) := unwrapFirstSpecified b; (Expr an (Elet pat pe b'), d)
    | _ => (Expr an e, false)

/-- Strip every `Astd` annotation from every expression node. -/
partial def stripStd : CoreExpr → CoreExpr
  | Expr an e =>
    let an' := an.filter fun a => match a with | Astd _ => false | _ => true
    Expr an' <| match e with
    | Esseq pat e1 e2 => Esseq pat (stripStd e1) (stripStd e2)
    | Ewseq pat e1 e2 => Ewseq pat (stripStd e1) (stripStd e2)
    | Eunseq es => Eunseq (es.map stripStd)
    | Ebound b => Ebound (stripStd b)
    | Eannot ds b => Eannot ds (stripStd b)
    | Esave sb inits b => Esave sb inits (stripStd b)
    | Eif pe e2 e3 => Eif pe (stripStd e2) (stripStd e3)
    | Elet pat pe b => Elet pat pe (stripStd b)
    | Ecase pe alts => Ecase pe (alts.map fun x => (x.1, stripStd x.2))
    | End es => End (es.map stripStd)
    | Epar es => Epar (es.map stripStd)
    | e => e

/-! ## t1 — `int main(void) { int x = 3; int y = x + 1; return y; }`
(docs/corpus-e0/t1.annot.core, transcribed by hand; E1 checks its
annotation/bound skeleton — the pure-expression contents (`Specified`,
`conv_loaded_int`, the `case`) are transcribed on a best reading of the
printed text and are NOT yet checked by the instrument). -/

/-- The source path the oracle printed into t1's `Aloc`s — VERBATIM from
    the E0 worktree's emission (docs/corpus-e0/t1.annot.core); an
    environment artefact whose text is immaterial: it is a non-library
    path (so the location update fires) and the skeleton compares `loc`
    PRESENCE only (E1 range audit §12). -/
def t1File : String := "refined-cerberus/worktrees/dialect-e0/docs/corpus-e0/t1.c"
def t1Pos (l c : Nat) : CerbLocation.Pos := ⟨t1File, l, c⟩
def t1Reg (c1 c2 : Nat) : CerbLocation.Loc := .region (t1Pos 1 c1) (t1Pos 1 c2) .noCursor
def t1RegP (c1 c2 cp : Nat) : CerbLocation.Loc :=
  .region (t1Pos 1 c1) (t1Pos 1 c2) (.pointCursor (t1Pos 1 cp))
def t1RegR (c1 c2 ca cb : Nat) : CerbLocation.Loc :=
  .region (t1Pos 1 c1) (t1Pos 1 c2) (.regionCursor (t1Pos 1 ca) (t1Pos 1 cb))

def sId (n : Nat) (s : String) : sym := Symbol "" n (SD_Id s)
def xSym : sym := Symbol "" 505 (SD_ObjectAddress "x")
def ySym : sym := Symbol "" 506 (SD_ObjectAddress "y")
def retSym : sym := sId 507 "ret"
def a508 : sym := sId 508 "a"
def a509 : sym := sId 509 "a"
def a510 : sym := sId 510 "a"
def a511 : sym := sId 511 "a"
def a512 : sym := sId 512 "a"
def a513 : sym := sId 513 "a"
def a515 : sym := sId 515 "a"
def a516 : sym := sId 516 "a"
def a517 : sym := sId 517 "a"
def a518 : sym := sId 518 "a"

def lint : core_base_type := BTy_loaded OTy_integer
def ptrTy : core_base_type := BTy_object OTy_pointer
def intCty : generic_pexpr Unit sym := Pexpr [] () (PEval (Vctype intTy))
def psym (x : sym) : generic_pexpr Unit sym := Pexpr [] () (PEsym x)
def specInt (n : Int) : generic_pexpr Unit sym :=
  Pexpr [] () (PEctor Cspecified [Pexpr [] () (PEval (Vobject (OVinteger (CerbMem.integerIval n))))])
def convLoadedInt (a : sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEcall (Sym convLoadedIntSym) [intCty, psym a])
def convInt (a : sym) : generic_pexpr Unit sym :=
  Pexpr [] () (PEconv_int (.Signed .Int_) (psym a))

def act (loc : CerbLocation.Loc) (a : generic_action_ Unit sym) : CoreExpr :=
  Expr [] (Eaction (Paction polarity.Pos (Action loc empty_annotation a)))
def wc : generic_pattern sym := Pattern [] (CaseBase (none, BTy_unit))
def seqE (e1 e2 : CoreExpr) : CoreExpr := Expr [] (Esseq wc e1 e2)
def letS (an : List annot) (x : sym) (bty : core_base_type) (e1 e2 : CoreExpr) : CoreExpr :=
  Expr an (Esseq (Pattern [] (CaseBase (some x, bty))) e1 e2)
def letW (an : List annot) (x : sym) (bty : core_base_type) (e1 e2 : CoreExpr) : CoreExpr :=
  Expr an (Ewseq (Pattern [] (CaseBase (some x, bty))) e1 e2)
def bnd (e : CoreExpr) : CoreExpr := Expr [Astd "§6.5#2"] (Ebound e)
def createInt (loc : CerbLocation.Loc) (x : sym) : CoreExpr :=
  act loc (Create (Pexpr [] () (PEctor Civalignof [intCty])) intCty (PrefSource loc [x]))
def killInt (x : sym) : CoreExpr := act (t1Reg 0 54) (Kill (Static0 intTy) (psym x))

/-- t1's `let weak a_515: pointer = pure(x) in load('signed int', a_515)`
    (the loaded read of `x`, t1.annot.core:22–27) — E2-admitted:
    `Frag.wseq_sym` over `Frag.pure_op` and `Frag.load_op`. -/
def t1LoadX : CoreExpr :=
  letW [Aloc (t1Reg 36 37), Aexpr] a515 ptrTy
    (Expr [Aloc (t1Reg 36 37), Aexpr] (Epure (psym xSym)))
    (act (t1Reg 36 37) (Load0 intCty (psym a515) NA))

/-- t1's `let weak a_516: pointer = pure(y) in load('signed int', a_516)`
    (t1.annot.core:47–51). -/
def t1LoadY : CoreExpr :=
  letW [Aloc (t1Reg 50 51), Aexpr] a516 ptrTy
    (Expr [Aloc (t1Reg 50 51), Aexpr] (Epure (psym ySym)))
    (act (t1Reg 50 51) (Load0 intCty (psym a516) NA))

/-- t1's `{-# §6.5#2 #-} bound({loc} pure(Specified(3)))` (t1.annot.core:6–10). -/
def t1Spec3 : CoreExpr := bnd (Expr [Aloc (t1Reg 25 26), Aexpr] (Epure (specInt 3)))

/-- t1's `{loc} pure(Specified(1))` — the `unseq`'s second arm (t1.annot.core:28–30). -/
def t1Spec1 : CoreExpr := Expr [Aloc (t1Reg 40 41), Aexpr] (Epure (specInt 1))

/-- t1's `pure(case (a_510, a_511) of …)` (t1.annot.core:32–39) — NOT
    E2-admitted: the first branch is a `catch_exceptional_condition` (E3). -/
def t1CasePe : generic_pexpr Unit sym :=
  Pexpr [] () (PEcase
    (Pexpr [] () (PEctor Ctuple [psym a510, psym a511]))
    [(Pattern [] (CaseCtor Ctuple
        [Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some a512, BTy_object OTy_integer))]),
         Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some a513, BTy_object OTy_integer))])]),
      Pexpr [] () (PEctor Cspecified
        [Pexpr [] () (PEcatch_exceptional_condition (.Signed .Int_) IOpAdd
          (convInt a512) (convInt a513))])),
     (Pattern [] (CaseBase (none, BTy_tuple [lint, lint])),
      Pexpr [] () (PEundef (t1Reg 36 41) UB036_exceptional_condition))])

/-- `main`'s body. -/
def t1Main : CoreExpr :=
  letS [Aloc (t1Reg 15 54), Astmt] xSym ptrTy (createInt (t1Reg 15 54) xSym)
  (letS [Astmt] ySym ptrTy (createInt (t1Reg 15 54) ySym)
  (letS [Aloc (t1Reg 17 27), Astmt] a508 lint t1Spec3
  (seqE (act (t1Reg 17 27) (Store0 false intCty (psym xSym) (convLoadedInt a508) NA))
  (letS [Aloc (t1Reg 28 42), Astmt] a509 lint
    (bnd (Expr [Astd "§6.5.6", Aloc (t1RegP 36 41 38), Aexpr]
      (Ewseq (Pattern [] (CaseCtor Ctuple
          [Pattern [] (CaseBase (some a510, lint)), Pattern [] (CaseBase (some a511, lint))]))
        (Expr [] (Eunseq [t1LoadX, t1Spec1]))
        (Expr [] (Epure t1CasePe)))))
  (seqE (act (t1Reg 28 42) (Store0 false intCty (psym ySym) (convLoadedInt a509) NA))
  (letS [Aloc (t1Reg 43 52), Astmt] a517 lint (bnd t1LoadY)
  (seqE (killInt xSym)
  (seqE (killInt ySym)
  (seqE (Expr [] (Erun empty_annotation retSym [convLoadedInt a517]))
  (seqE (killInt xSym)
  (seqE (killInt ySym)
  (seqE (Expr [] (Epure (Pexpr [] () (PEval Vunit))))
  (Expr [Aloc (t1RegR 0 54 4 8), Astmt]
    (Esave (retSym, lint) [(a518, ((lint, none), specInt 0))]
      (Expr [] (Epure (psym a518)))))))))))))))))

/-- E3: `main`'s body with the `unseq` node — the read of `x` beside
    `Specified(1)` — as a PARAMETER `u`: the witness shape of acceptance (i)
    (`t1MainWith_frag`: every other node is in the cone). -/
def t1MainWith (u : CoreExpr) : CoreExpr :=
  letS [Aloc (t1Reg 15 54), Astmt] xSym ptrTy (createInt (t1Reg 15 54) xSym)
  (letS [Astmt] ySym ptrTy (createInt (t1Reg 15 54) ySym)
  (letS [Aloc (t1Reg 17 27), Astmt] a508 lint t1Spec3
  (seqE (act (t1Reg 17 27) (Store0 false intCty (psym xSym) (convLoadedInt a508) NA))
  (letS [Aloc (t1Reg 28 42), Astmt] a509 lint
    (bnd (Expr [Astd "§6.5.6", Aloc (t1RegP 36 41 38), Aexpr]
      (Ewseq (Pattern [] (CaseCtor Ctuple
          [Pattern [] (CaseBase (some a510, lint)), Pattern [] (CaseBase (some a511, lint))]))
        u
        (Expr [] (Epure t1CasePe)))))
  (seqE (act (t1Reg 28 42) (Store0 false intCty (psym ySym) (convLoadedInt a509) NA))
  (letS [Aloc (t1Reg 43 52), Astmt] a517 lint (bnd t1LoadY)
  (seqE (killInt xSym)
  (seqE (killInt ySym)
  (seqE (Expr [] (Erun empty_annotation retSym [convLoadedInt a517]))
  (seqE (killInt xSym)
  (seqE (killInt ySym)
  (seqE (Expr [] (Epure (Pexpr [] () (PEval Vunit))))
  (Expr [Aloc (t1RegR 0 54 4 8), Astmt]
    (Esave (retSym, lint) [(a518, ((lint, none), specInt 0))]
      (Expr [] (Epure (psym a518)))))))))))))))))

theorem t1Main_eq_with : t1Main = t1MainWith (Expr [] (Eunseq [t1LoadX, t1Spec1])) := rfl

/-! ## E2: membership witnesses for t1's sub-terms -/

/-- The evaluator-fuel bound at an authored operand (its depth is tiny). -/
theorem depLe {pe : generic_pexpr Unit sym} (h : peDepth pe ≤ 9) :
    peDepth pe ≤ lemDefaultFuel := by
  rw [show lemDefaultFuel = 999999 + 1 from rfl]; omega

theorem specInt_pePure (n : Int) : PePure (specInt n) :=
  PePure.ctor _ _ rfl fun pe h => by
    rcases List.mem_singleton.mp h with rfl; exact PePure.val _ _

theorem t1LoadX_frag : Frag t1LoadX :=
  Frag.wseq_sym (Frag.pure_op rfl (PePure.sym _ _) (depLe (by decide)))
    (Frag.load_op rfl (PePure.sym _ _) (depLe (by decide)))

theorem t1LoadY_frag : Frag t1LoadY :=
  Frag.wseq_sym (Frag.pure_op rfl (PePure.sym _ _) (depLe (by decide)))
    (Frag.load_op rfl (PePure.sym _ _) (depLe (by decide)))

theorem t1Spec3_frag : Frag t1Spec3 :=
  Frag.bound (Frag.pure_op rfl (specInt_pePure 3) (depLe (by decide)))

theorem t1Spec1_frag : Frag t1Spec1 :=
  Frag.pure_op rfl (specInt_pePure 1) (depLe (by decide))

theorem t1KillX_frag : Frag (killInt xSym) :=
  Frag.kill_op rfl (PePure.sym _ _) (depLe (by decide))

/-- E3: `conv_loaded_int('signed int', a_508)` — a `PEcall` at covered
    arguments — is IN the covered operand grammar (E2 decided it OUT; the
    standard-library call is admitted since E3), kernel-decided. -/
theorem t1_convLoadedInt_covered : isPePure (convLoadedInt a508) = true := by decide

/-- E3: t1's `case` is in the covered grammar — its first branch's
    `catch_exceptional_condition_add(__conv_int__(…), __conv_int__(…))` is
    admitted since E3. -/
theorem t1_case_covered : isPePure t1CasePe = true := by decide

/-! ## E3: t1 is in the cone EXCEPT the `unseq` node (acceptance (i)) -/

/-- The evaluator-fuel bound at E3's larger operands (`conv_loaded_int(…)`
    carries the callee's static inlining budget, `stdBudget`). -/
theorem depLe40 {pe : generic_pexpr Unit sym} (h : peDepth pe ≤ 40) :
    peDepth pe ≤ lemDefaultFuel := by
  rw [show lemDefaultFuel = 999999 + 1 from rfl]; omega

/-- EVERY node of t1's `main` other than the `unseq` is in the cone: with
    any fragment `u` in the `unseq`'s position, `main` is a `Frag`. The
    `conv_loaded_int` calls (store operands, `run` argument), the
    `catch_exceptional_condition_add(__conv_int__ …)` case and the return
    protocol are E3's admissions; the rest E1/E2's. -/
theorem t1MainWith_frag (u : CoreExpr) (hu : Frag u) : Frag (t1MainWith u) :=
  .sseq_sym
    (.create_op rfl (.ctorTy [] Civalignof rfl [] intTy) (.val [] (Vctype intTy))
      (depLe (by decide)) (peDepth_val_le _ _))
    (.sseq_sym
      (.create_op rfl (.ctorTy [] Civalignof rfl [] intTy) (.val [] (Vctype intTy))
        (depLe (by decide)) (peDepth_val_le _ _))
      (.sseq_sym t1Spec3_frag
        (.sseq
          (.store_op rfl (.sym [] xSym) (PePure.of_isPePure rfl) (depLe (by decide))
            (depLe40 (by decide)))
          (.sseq_sym
            (.bound (Frag.wseq_tuple (pa := []) (ls := [([], some a510, lint), ([], some a511, lint)])
              hu (.pure_op rfl (PePure.of_isPePure rfl) (depLe40 (by decide)))))
            (.sseq
              (.store_op rfl (.sym [] ySym) (PePure.of_isPePure rfl) (depLe (by decide))
                (depLe40 (by decide)))
              (.sseq_sym (.bound t1LoadY_frag)
                (.sseq t1KillX_frag
                  (.sseq (.kill_op rfl (.sym [] ySym) (depLe (by decide)))
                    (.sseq
                      (.run (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact PePure.of_isPePure rfl)
                        (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact depLe40 (by decide)))
                      (.sseq t1KillX_frag
                        (.sseq (.kill_op rfl (.sym [] ySym) (depLe (by decide)))
                          (.sseq (.val_pure Vunit)
                            (.save
                              (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact PePure.of_isPePure rfl)
                              (fun pe h => by rcases List.mem_singleton.mp h with rfl; exact depLe (by decide))
                              (.pure_op rfl (.sym [] a518) (depLe (by decide))))))))))))))))

/-- The `unseq` node itself is NOT in the cone (no `Frag` constructor
    covers `Eunseq`; E4 owes it). -/
theorem t1_unseq_not_frag : ¬ Frag (Expr [] (Eunseq [t1LoadX, t1Spec1])) := fun h => nomatch h

/-- THE SYNTACTIC COVERAGE WALK (an instrument, not a theorem about
    `Frag`): descends the spine constructs the cone admits — `let strong`/
    `let weak` at symbol, wildcard and flat-tuple binders, `bound`,
    `annot`, `save` — and lists the node kinds it cannot descend into or
    admit: `pure`/action/`run` operands outside `isPePure`, `unseq`, `nd`,
    `par`, `if`/`case`/`let` at expression level, calls, `wait`. -/
def uncoveredKinds : CoreExpr → List String
  | Expr _ e =>
    match e with
    | Esseq (Pattern _ (CaseBase _)) e1 e2 => uncoveredKinds e1 ++ uncoveredKinds e2
    | Ewseq (Pattern _ (CaseBase _)) e1 e2 => uncoveredKinds e1 ++ uncoveredKinds e2
    | Esseq (Pattern _ (CaseCtor Ctuple _)) e1 e2 => uncoveredKinds e1 ++ uncoveredKinds e2
    | Ewseq (Pattern _ (CaseCtor Ctuple _)) e1 e2 => uncoveredKinds e1 ++ uncoveredKinds e2
    | Esseq _ _ _ => ["sseq-pattern"]
    | Ewseq _ _ _ => ["wseq-pattern"]
    | Ebound b => uncoveredKinds b
    | Eannot _ b => uncoveredKinds b
    | Esave _ inits body =>
      (if (inits.map fun x => x.2.2).all isPePure then [] else ["save-init"]) ++ uncoveredKinds body
    | Epure pe => if isPePure pe then [] else ["pure-operand"]
    | Eaction (Paction _ (Action _ _ act)) =>
      if (actionPexprs act).all isPePure then [] else ["action-operand"]
    | Erun _ _ pes => if pes.all isPePure then [] else ["run-operand"]
    | Eunseq _ => ["unseq"]
    | End _ => ["nd"]
    | Epar _ => ["par"]
    | Eif _ _ _ => ["if"]
    | Ecase _ _ => ["case"]
    | Elet _ _ _ => ["let"]
    | Eccall _ _ _ _ => ["ccall"]
    | Eproc _ _ _ => ["pcall"]
    | Ememop _ _ => ["memop"]
    | Ewait _ => ["wait"]
    | Eexcluded _ _ => ["excluded"]

/-- KERNEL-DECIDED: t1's `main` has EXACTLY ONE uncovered position, the
    `unseq` (E3 acceptance (i); the walk's verdict, `decide`). -/
theorem t1_uncovered_exactly_unseq : uncoveredKinds t1Main = ["unseq"] := by decide

/-! ## The table -/

/-- One corpus row: the `.annot.core` file (under docs/corpus-e0/ at the
    repository root), the procedure, the transcription. -/
structure Row where
  file : String
  proc : String
  term : CoreExpr

def corpusTable : List Row := [⟨"t1.annot.core", "main", t1Main⟩]

/-- THE COVERAGE LEDGER of the corpus (E1 range audit N-2,
    docs/2026-09-05_audit-e1-range.md: the check was table-driven, so a
    corpus file without a row was silently unchecked). Every
    `docs/corpus-e0/*.annot.core` file must be either a `corpusTable` row
    or listed here with the slice that owes its transcription; the script
    sweeps the directory and FAILS on a file that is neither (fail-closed).
    The `.annot.core` form is the one the tokenizer can read (it carries
    the printed `{-# … #-}` markers); the `.core` twin is the same program
    without them, and the `.seq.core`/`.seqrw.core` forms are the
    informational sequentialised emissions (E0 §D Q1: not the referent). -/
def pendingCorpus : List (String × String) :=
  [("t2.annot.core", "E6 (`Eccall`; the helper call in a `for` loop)"),
   ("t3_ptrarg.annot.core", "E6 (`Eccall`, `PtrValidForDeref`)"),
   ("t4_while.annot.core", "E5 (negative actions; `while`)"),
   ("t5_ifelse.annot.core", "E5 (negative actions; `if`/`else`)"),
   ("t6_switch.annot.core", "E5 (negative actions; `switch`)"),
   ("t7_struct.annot.core", "outside E — KOI B4 (`tagDefs`)"),
   ("t8_array.annot.core", "E6 (arrays; `PtrValidForDeref`)"),
   ("t9_fact.annot.core", "E7 (the outcome-list closed form)"),
   ("t10_evenodd.annot.core", "E6 (`Eccall`; mutual recursion)")]

/-! ## E3: THE TRANSCRIBED STANDARD LIBRARY vs the pinned std.core SOURCE -/

/-- One std.core row: the function's name and its transcribed body
    (StdCore.lean). The check reads the pinned SOURCE `runtime/libcore/
    std.core` (what the shipped pipeline parses, Main.lean:748): the oracle
    cannot print std.core (`--pp=core` on it aborts in the Core parser,
    docs/2026-09-05_e3-notes.md §3, measured). -/
structure StdRow where
  name : String
  body : generic_pexpr Unit sym

def stdTable : List StdRow :=
  [⟨"is_representable_integer", isReprBody⟩,
   ⟨"conv_int", convIntBody⟩,
   ⟨"conv_loaded_int", convLoadedIntBody⟩]

/-- The plants of a std row (each MUST break the comparison where it
    applies; a row NO plant applies to is a FAIL — an unplanted row):
    `Ivmin`/`Ivmax` swapped everywhere; the first `if`'s branches swapped;
    the first `case`'s alternatives reversed. -/
partial def swapIvMinMax : generic_pexpr Unit sym → generic_pexpr Unit sym × Bool
  | Pexpr an u pe =>
    match pe with
    | PEctor Civmin ps => (Pexpr an u (PEctor Civmax ps), true)
    | PEctor Civmax ps => (Pexpr an u (PEctor Civmin ps), true)
    | PEctor c ps =>
      let rs := ps.map swapIvMinMax
      (Pexpr an u (PEctor c (rs.map (·.1))), rs.any (·.2))
    | PEop op p1 p2 =>
      let (q1, d1) := swapIvMinMax p1
      let (q2, d2) := swapIvMinMax p2
      (Pexpr an u (PEop op q1 q2), Bool.or d1 d2)
    | PEif p1 p2 p3 =>
      let (q1, d1) := swapIvMinMax p1
      let (q2, d2) := swapIvMinMax p2
      let (q3, d3) := swapIvMinMax p3
      (Pexpr an u (PEif q1 q2 q3), Bool.or (Bool.or d1 d2) d3)
    | PEcall f ps =>
      let rs := ps.map swapIvMinMax
      (Pexpr an u (PEcall f (rs.map (·.1))), rs.any (·.2))
    | PEcase p alts =>
      let (q, d) := swapIvMinMax p
      let rs := alts.map fun x => let (b, db) := swapIvMinMax x.2; ((x.1, b), db)
      (Pexpr an u (PEcase q (rs.map (·.1))), Bool.or d (rs.any (·.2)))
    | _ => (Pexpr an u pe, false)

partial def swapFirstIf : generic_pexpr Unit sym → generic_pexpr Unit sym × Bool
  | Pexpr an u pe =>
    match pe with
    | PEif p1 p2 p3 => (Pexpr an u (PEif p1 p3 p2), true)
    | PEctor c ps =>
      let rec go : List (generic_pexpr Unit sym) → List (generic_pexpr Unit sym) × Bool
        | [] => ([], false)
        | q :: qs => let (q', d) := swapFirstIf q; if d then (q' :: qs, true) else
            let (qs', d') := go qs; (q :: qs', d')
      let (ps', d) := go ps
      (Pexpr an u (PEctor c ps'), d)
    | PEcase p alts =>
      let (q, d) := swapFirstIf p
      if d then (Pexpr an u (PEcase q alts), true) else
      let rec goA : List (pattern × generic_pexpr Unit sym) →
          List (pattern × generic_pexpr Unit sym) × Bool
        | [] => ([], false)
        | (pt, b) :: rest => let (b', d) := swapFirstIf b; if d then ((pt, b') :: rest, true) else
            let (rest', d') := goA rest; ((pt, b) :: rest', d')
      let (alts', d') := goA alts
      (Pexpr an u (PEcase p alts'), d')
    | _ => (Pexpr an u pe, false)

partial def reverseFirstCase : generic_pexpr Unit sym → generic_pexpr Unit sym × Bool
  | Pexpr an u pe =>
    match pe with
    | PEcase p alts => (Pexpr an u (PEcase p alts.reverse), true)
    | PEif p1 p2 p3 =>
      let (q1, d1) := reverseFirstCase p1
      if d1 then (Pexpr an u (PEif q1 p2 p3), true) else
      let (q2, d2) := reverseFirstCase p2
      if d2 then (Pexpr an u (PEif p1 q2 p3), true) else
      let (q3, d3) := reverseFirstCase p3
      (Pexpr an u (PEif p1 p2 q3), d3)
    | PEctor c ps =>
      let rec go : List (generic_pexpr Unit sym) → List (generic_pexpr Unit sym) × Bool
        | [] => ([], false)
        | q :: qs => let (q', d) := reverseFirstCase q; if d then (q' :: qs, true) else
            let (qs', d') := go qs; (q :: qs', d')
      let (ps', d) := go ps
      (Pexpr an u (PEctor c ps'), d)
    | _ => (Pexpr an u pe, false)

def stdPlants : List (String × (generic_pexpr Unit sym → generic_pexpr Unit sym × Bool)) :=
  [("Ivmin/Ivmax swapped", swapIvMinMax),
   ("first if's branches swapped", swapFirstIf),
   ("first case's alternatives reversed", reverseFirstCase)]

end CerberusHeapLang.CorpusE0
