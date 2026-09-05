/-
CerberusHeapLang.Examples.CorpusE0 — THE CORPUS TRANSCRIPTIONS AND THE
SKELETON INSTRUMENT (dialect arc E1; [USER 2026-09-04] ratified E0
question 3: the pipeline's Core enters a statement as a HAND-TRANSCRIBED
term checked by an EXECUTABLE EQUALITY speedbump against the oracle's
emitted Core).

Two things live here, both data/instruments, no proofs:

1. THE TRANSCRIPTION TABLE `corpusTable`: for each corpus program
   (docs/corpus-e0/<name>.annot.core at the repository root) the
   procedure it names and the hand-transcribed `CoreExpr` of that
   procedure's body. E1 transcribes t1 (`t1Main`). Later slices add rows.

2. THE SKELETON CHECK (`scripts/corpus_skeleton.lean` runs it): the
   ANNOTATION/BOUND SKELETON of a term — the preorder token stream of
   its expression nodes, each node contributing the annotations the
   pretty-printer shows (`Astd` strings, in the printer's order; one
   `loc` marker when `get_loc` finds an `Aloc`) followed by its node kind
   (`lets`/`letw`/`seq`/`bound`/`unseq`…`endunseq`/`pure`/`store`/…, the
   printer's keywords) — must EQUAL the token stream read off the
   emitted text by `tokenize`. The printer facts the two sides share:
   pp_core.ml:549–680 (`Astd` comments are PREPENDED by a fold, so they
   print in REVERSE list order, then the `get_loc` marker, then the node;
   the wildcard-unit `Esseq` prints as `e1 ; e2`; `Ewseq` always prints
   `let weak`; `bound(e)`; action keywords pp_core.ml:690–745).

   WHAT THE SKELETON DOES NOT CHECK (E1 scope): pure expressions are
   LEAVES — a `pure(...)`/operand's contents, patterns, symbols, ctypes
   and memory orders are not compared; the association of a `;` chain is
   not observable in the text (no parentheses are printed) and is not
   compared. FAIL-CLOSED where the instrument is blind: a term whose pure
   expressions carry `Astd`/`Aloc` annotations, or a text with a
   `{-# … #-}` marker inside an opaque (pure-expression) region, is an
   ERROR, not a pass. E2/E3 extend the printer to pure expressions.

Plants (the vacuity check the script runs on every row): dropping the
first `bound` of a transcription, or every `Astd`, MUST make the check
fail; a plant that passes fails the script.
-/
import CerberusHeapLang.Step
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

/-- THE SKELETON: the preorder token stream of the expression nodes. -/
partial def skeleton : CoreExpr → Except String (List String)
  | Expr an e => do
    let hd := annotTokens an
    match e with
    | Epure pe => do checkClean [pe]; pure (hd ++ ["pure"])
    | Ememop _ pes => do checkClean pes; pure (hd ++ ["memop"])
    | Eaction (Paction pol (Action _ _ act)) => do
      checkClean (actionPexprs act)
      let neg := match pol with | polarity.Pos => [] | polarity.Neg0 => ["neg"]
      pure (hd ++ neg ++ [actionKeyword act])
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
    | Erun _ _ pes => do checkClean pes; pure (hd ++ ["run"])
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

/-- Action/leaf keywords: `kw(…)`, the parenthesised contents opaque. -/
def leafKeywords : List String :=
  ["pure", "memop", "pcall", "ccall", "wait", "create", "create_readonly", "alloc", "kill",
   "free", "store", "store_lock", "load", "seq_rmw", "seq_rmw_with_forward", "rmw", "fence",
   "compare_exchange_strong", "compare_exchange_weak", "linux_fence", "linux_load",
   "linux_store", "linux_rmw"]

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
        scan (← skipBalanced (← expectParen r ident)) (toks.push "run") frames
      | "if" => do scan (← skipUntilKw rest' "then") (toks.push "if") frames
      | "case" => do scan (← skipUntilKw rest' "of") (toks.push "case") (.caseF :: frames)
      | "end" =>
        match frames with
        | .caseF :: fs => scan rest' (toks.push "endcase") fs
        | _ => throw "`end` outside a case"
      | "then" | "else" | "in" | "of" => scan rest' toks frames
      | _ =>
        if leafKeywords.contains ident then do
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
def convLoadedIntSym : sym := sId 0 "conv_loaded_int"

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

/-- `main`'s body. -/
def t1Main : CoreExpr :=
  letS [Aloc (t1Reg 15 54), Astmt] xSym ptrTy (createInt (t1Reg 15 54) xSym)
  (letS [Astmt] ySym ptrTy (createInt (t1Reg 15 54) ySym)
  (letS [Aloc (t1Reg 17 27), Astmt] a508 lint
    (bnd (Expr [Aloc (t1Reg 25 26), Aexpr] (Epure (specInt 3))))
  (seqE (act (t1Reg 17 27) (Store0 false intCty (psym xSym) (convLoadedInt a508) NA))
  (letS [Aloc (t1Reg 28 42), Astmt] a509 lint
    (bnd (Expr [Astd "§6.5.6", Aloc (t1RegP 36 41 38), Aexpr]
      (Ewseq (Pattern [] (CaseCtor Ctuple
          [Pattern [] (CaseBase (some a510, lint)), Pattern [] (CaseBase (some a511, lint))]))
        (Expr [] (Eunseq
          [letW [Aloc (t1Reg 36 37), Aexpr] a515 ptrTy
            (Expr [Aloc (t1Reg 36 37), Aexpr] (Epure (psym xSym)))
            (act (t1Reg 36 37) (Load0 intCty (psym a515) NA)),
           Expr [Aloc (t1Reg 40 41), Aexpr] (Epure (specInt 1))]))
        (Expr [] (Epure (Pexpr [] () (PEcase
          (Pexpr [] () (PEctor Ctuple [psym a510, psym a511]))
          [(Pattern [] (CaseCtor Ctuple
              [Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some a512, BTy_object OTy_integer))]),
               Pattern [] (CaseCtor Cspecified [Pattern [] (CaseBase (some a513, BTy_object OTy_integer))])]),
            Pexpr [] () (PEctor Cspecified
              [Pexpr [] () (PEcatch_exceptional_condition (.Signed .Int_) IOpAdd
                (convInt a512) (convInt a513))])),
           (Pattern [] (CaseBase (none, BTy_tuple [lint, lint])),
            Pexpr [] () (PEundef (t1Reg 36 41) UB036_exceptional_condition))])))))))
  (seqE (act (t1Reg 28 42) (Store0 false intCty (psym ySym) (convLoadedInt a509) NA))
  (letS [Aloc (t1Reg 43 52), Astmt] a517 lint
    (bnd (letW [Aloc (t1Reg 50 51), Aexpr] a516 ptrTy
      (Expr [Aloc (t1Reg 50 51), Aexpr] (Epure (psym ySym)))
      (act (t1Reg 50 51) (Load0 intCty (psym a516) NA))))
  (seqE (killInt xSym)
  (seqE (killInt ySym)
  (seqE (Expr [] (Erun empty_annotation retSym [convLoadedInt a517]))
  (seqE (killInt xSym)
  (seqE (killInt ySym)
  (seqE (Expr [] (Epure (Pexpr [] () (PEval Vunit))))
  (Expr [Aloc (t1RegR 0 54 4 8), Astmt]
    (Esave (retSym, lint) [(a518, ((lint, none), specInt 0))]
      (Expr [] (Epure (psym a518)))))))))))))))))

/-! ## The table -/

/-- One corpus row: the `.annot.core` file (under docs/corpus-e0/ at the
    repository root), the procedure, the transcription. -/
structure Row where
  file : String
  proc : String
  term : CoreExpr

def corpusTable : List Row := [⟨"t1.annot.core", "main", t1Main⟩]

end CerberusHeapLang.CorpusE0
