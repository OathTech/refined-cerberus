/-
corpus_skeleton.lean — THE EXECUTABLE EQUALITY SPEEDBUMP of the emitted-Core
dialect arc (E1; [USER 2026-09-04] E0 question 3). For every row of
`CerberusHeapLang.CorpusE0.corpusTable` the full printed body of
the hand-transcribed term must equal the token stream tokenized off the
oracle's emitted text `docs/corpus-e0/<file>` (repository root); and the
four PLANTS of every row (first `bound` dropped; every `Astd` stripped;
E2: the first `pure(Specified(…))` unwrapped; E4: the first `save`
initialiser's `Specified(…)` unwrapped) must NOT match — a plant that
matches means the instrument is vacuous and fails the run. E5 also plants
singleton tuples around expression-level case/if scrutinees and a case pattern;
each position must be exercised by at least one row and every applied plant
must mismatch. The FullText namespace below supersedes the opaque-leaf comparison
described by the older library module header.

Run (from cerberus-heaplang/):
  ../scripts/capped ~/.elan/bin/lake env lean scripts/corpus_skeleton.lean
Exit 0 = every row matches and every plant mismatches; non-zero otherwise (the
failure is raised as an `IO.userError` so every diagnostic printed before it is
emitted — never `IO.Process.exit`, which inside `#eval` discards them).
-/
import CerberusHeapLang.Examples.CorpusE0

open CerberusHeapLang CerberusHeapLang.CorpusE0

/- D6: render the complete printed body. The printer contract is the pinned
   ocaml_frontend/pprinters/pp_core.ml (precedence, annotations, patterns,
   expressions and actions). Only layout whitespace is ignored. Symbols use
   the emitted corpus's numbered local identifiers; std.core uses source names.
   Unprinted metadata (digests, action locations, save passing modes) is outside
   a TEXT comparison. Unsupported printed forms fail, never become opaque leaves. -/
namespace FullText

def parens (s : String) : String := "(" ++ s ++ ")"
def args (ss : List String) : String := parens (", ".intercalate ss)

def symbol (sourceNames : Bool) : sym → Except String String
  | Symbol _ n (SD_Id s) => pure (if sourceNames then s else s!"{s}_{n}")
  | Symbol _ _ (SD_ObjectAddress s) => pure s
  | Symbol _ _ (SD_FunArgValue s) => pure s
  | Symbol _ n SD_None => pure s!"a_{n}"
  | _ => throw "unsupported symbol description"

def pos (p : CerbLocation.Pos) : String := s!"{p.file}:{p.line}:{p.col}"
def cursor : CerbLocation.Cursor → String
  | .noCursor => ""
  | .pointCursor p => " " ++ pos p
  | .regionCursor a b => " " ++ pos a ++ " - " ++ pos b

def location : CerbLocation.Loc → Except String String
  | .unknown => pure "<unknown location>"
  | .point p => pure (pos p)
  | .region a b c => pure (s!"<{pos a}, {pos b}>" ++ cursor c)
  | _ => throw "unsupported printed location"

def marker (s : String) : String := "{-# " ++ s ++ " #-} "
def annotations (an : List annot) : Except String String := do
  for a in an do
    match a with
    | Astd _ | Aloc _ | Aexpr | Astmt | Auid _ | Alabel _ | Acerb _
      | Ainlined_label _ | Aattrs _ | Avalue _ => pure ()
    | _ => throw "unsupported printed annotation"
  let std := (an.filterMap fun a => match a with | Astd s => some (marker s) | _ => none).reverse
  let loc ← match get_loc an with | none => pure "" | some l => marker <$> location l
  pure (String.join std ++ loc)

def integerBase : integerBaseType → Except String String
  | .Ichar => pure "char" | .Short => pure "short" | .Int_ => pure "int"
  | .Long => pure "long" | .LongLong => pure "long long"
  | _ => throw "unsupported integer base type"
def integerTy : integerType → Except String String
  | .Bool0 => pure "_Bool" | .Char0 => pure "char"
  | .Signed t => ("signed " ++ ·) <$> integerBase t
  | .Unsigned t => ("unsigned " ++ ·) <$> integerBase t
  | _ => throw "unsupported integer type"
def cty : ctype → Except String String
  | Ctype [] (.Basic (.Integer t)) => (fun s => "'" ++ s ++ "'") <$> integerTy t
  | _ => throw "unsupported ctype"
partial def objectTy : core_object_type → Except String String
  | OTy_integer => pure "integer" | OTy_floating => pure "floating"
  | OTy_pointer => pure "pointer"
  | OTy_array t => ("array" ++ ·) <$> (parens <$> objectTy t)
  | _ => throw "unsupported object type"
partial def baseTy : core_base_type → Except String String
  | BTy_storable => pure "storable" | BTy_boolean => pure "boolean"
  | BTy_ctype => pure "ctype" | BTy_unit => pure "unit"
  | BTy_object t => objectTy t
  | BTy_loaded t => ("loaded " ++ ·) <$> objectTy t
  | BTy_tuple ts => args <$> ts.mapM baseTy
  | BTy_list t => (fun s => "[" ++ s ++ "]") <$> baseTy t

partial def val : value → Except String String
  | Vunit => pure "Unit" | Vtrue => pure "True" | Vfalse => pure "False"
  | Vctype t => cty t
  | Vobject (OVinteger (.IV .Prov_none n)) => pure (toString n)
  | Vloaded (LVspecified ov) => ("Specified" ++ ·) <$> (parens <$> val (Vobject ov))
  | Vloaded (LVunspecified t) => ("Unspecified" ++ ·) <$> (parens <$> cty t)
  | Vtuple vs => args <$> vs.mapM val
  | _ => throw "unsupported printed value"

def construct (c : ctor) (ss : List String) : Except String String := do
  match c with
  | Ctuple => pure (args ss)
  | _ => pure ((← ctorName c) ++ args ss)
partial def pat (src : Bool) : pattern → Except String String
  | Pattern an p => do
    if hasShownAnnot an then throw "annotated pattern"
    match p with
    | CaseBase (s, t) =>
      pure ((← match s with | none => pure "_" | some s => symbol src s) ++ ": " ++ (← baseTy t))
    | CaseCtor c ps => construct c (← ps.mapM (pat src))

def binop : _root_.binop → String × Nat
  | OpExp => ("^", 1) | OpMul => ("*", 2) | OpDiv => ("/", 2)
  | OpRem_t => ("rem_t", 2) | OpRem_f => ("rem_f", 2)
  | OpAdd => ("+", 3) | OpSub => ("-", 3)
  | OpLt => ("<", 4) | OpLe => ("<=", 4) | OpGt => (">", 4) | OpGe => (">=", 4)
  | OpEq => ("=", 5) | OpAnd => ("/\\", 6) | OpOr => ("\\/", 7)

partial def pexpr (src : Bool) (outer : Option Nat := none) : generic_pexpr Unit sym → Except String String
  | Pexpr an _ pe => do
    let prec := match pe with | PEop op _ _ => some (binop op).2 | _ => none
    let pp := pexpr src prec
    let body ← match pe with
      | PEsym s => symbol src s
      | PEval v => val v
      | PEundef _ ub => pure ("undef(<<" ++ stringFromUndefined_behaviour ub ++ ">>)")
      | PEctor c ps => construct c (← ps.mapM pp)
      | PEcase p bs => do
        let bs ← bs.mapM fun (p, b) => do pure (" | " ++ (← pat src p) ++ " => " ++ (← pp b))
        pure ("case " ++ (← pp p) ++ " of" ++ String.join bs ++ " end")
      | PEcall nm ps => do
        let name ← match nm with
          | Sym s => symbol true s
          | Impl c => pure ("<" ++ string_of_implementation_constant c ++ ">")
        pure (name ++ args (← ps.mapM pp))
      | PEimpl c => pure ("<" ++ string_of_implementation_constant c ++ ">")
      | PEconv_int t p => pure ("__conv_int__" ++ args [← cty (Ctype [] (.Basic (.Integer t))), ← pp p])
      | PEcatch_exceptional_condition t op p q =>
        pure ("catch_exceptional_condition" ++ iopSuffix op ++ args [← cty (Ctype [] (.Basic (.Integer t))), ← pp p, ← pp q])
      | PEwrapI t op p q =>
        pure ("wrapI" ++ iopSuffix op ++ args [← cty (Ctype [] (.Basic (.Integer t))), ← pp p, ← pp q])
      | PEop op p q => pure ((← pp p) ++ " " ++ (binop op).1 ++ " " ++ (← pp q))
      | PEnot p => pure ("not" ++ args [← pp p])
      | PEif p q r => pure ("if " ++ (← pp p) ++ " then " ++ (← pp q) ++ " else " ++ (← pp r))
      | PEarray_shift p t q => pure ("array_shift" ++ args [← pp p, ← cty t, ← pp q])
      | PEis_unsigned p => pure ("is_unsigned" ++ args [← pp p])
      | _ => throw "unsupported pure expression"
    let body := match prec, outer with
      | some p, some q => if p > q then parens body else body
      | _, _ => body
    pure ((← annotations an) ++ body)

def memorder : memory_order → String
  | .NA => "NA" | .Seq_cst => "seq_cst" | .Relaxed => "relaxed"
  | .Release => "release" | .Acquire => "acquire" | .Consume => "consume" | .Acq_rel => "acq_rel"
def action (a : generic_action_ Unit sym) : Except String String := do
  let pp := pexpr false none
  let operands ← match a with
    | Create p q _ | Alloc0 p q _ => pure [← pp p, ← pp q]
    | CreateReadOnly p q r _ => pure [← pp p, ← pp q, ← pp r]
    | Kill Dynamic0 p => pure [← pp p]
    | Kill (Static0 t) p => pure [← cty t, ← pp p]
    | Store0 _ p q r mo => pure ([← pp p, ← pp q, ← pp r] ++ if mo == .NA then [] else [memorder mo])
    | Load0 p q mo => pure ([← pp p, ← pp q] ++ if mo == .NA then [] else [memorder mo])
    | _ => throw "unsupported printed action"
  pure (actionKeyword a ++ args operands)

partial def expr : CoreExpr → Except String String
  | Expr an e => do
    let pp := pexpr false none
    let body ← match e with
      | Epure p => pure ("pure" ++ args [← pp p])
      | Eaction (Paction pol (Action _ _ a)) => do
        let s ← action a
        pure (match pol with | .Pos => s | .Neg0 => "neg" ++ parens s)
      | Ecase p bs => do
        let bs ← bs.mapM fun (p, b) => do pure (" | " ++ (← pat false p) ++ " => " ++ (← expr b))
        pure ("case " ++ (← pp p) ++ " of" ++ String.join bs ++ " end")
      | Eif p q r => pure ("if " ++ (← pp p) ++ " then " ++ (← expr q) ++ " else " ++ (← expr r))
      | Elet p a b => pure ("let " ++ (← pat false p) ++ " = " ++ (← pp a) ++ " in " ++ (← expr b))
      | Esseq (Pattern _ (CaseBase (none, BTy_unit))) a b => pure ((← expr a) ++ " ; " ++ (← expr b))
      | Esseq p a b => pure ("let strong " ++ (← pat false p) ++ " = " ++ (← expr a) ++ " in " ++ (← expr b))
      | Ewseq p a b => pure ("let weak " ++ (← pat false p) ++ " = " ++ (← expr a) ++ " in " ++ (← expr b))
      | Eunseq es => pure ("unseq" ++ args (← es.mapM expr))
      | End es => pure ("nd" ++ args (← es.mapM expr))
      | Epar es => pure ("par" ++ args (← es.mapM expr))
      | Ebound b => pure ("bound" ++ args [← expr b])
      | Esave (s, t) ins b => do
        let ins ← ins.mapM fun (s, ((t, _), p)) => do
          pure ((← symbol false s) ++ ": " ++ (← baseTy t) ++ ":= " ++ (← pp p))
        pure ("save " ++ (← symbol false s) ++ ": " ++ (← baseTy t) ++ " " ++ args ins ++ " in " ++ (← expr b))
      | Erun _ s ps => pure ("run " ++ (← symbol false s) ++ args (← ps.mapM pp))
      | Eexcluded n (Action _ _ a) => pure (s!"excluded[{n}]" ++ args [← action a])
      | _ => throw "unsupported expression form"
    pure ((← annotations an) ++ body)

/-- A lexical stream retaining every non-layout character; strings and printed
    annotation payloads are whole tokens. No syntax position is skipped. -/
partial def tokens (cs : List Char) : Except String (List String) := do
  match cs with
  | [] => pure []
  | c :: rest =>
    if c.isWhitespace then tokens rest
    else if startsWith cs "{-#" then
      let (m, rest) ← takeMarker (cs.drop 3)
      pure (("{-# " ++ m.trimAscii.toString ++ " #-}") :: (← tokens rest))
    else if isQuote c then
      let (q, rest) := spanQuoted c rest [c]
      unless q.getLast? == some c do throw "unterminated quoted token"
      pure (String.ofList q :: (← tokens rest))
    else if isIdentChar c then
      let (s, rest) := takeIdent cs
      pure (s :: (← tokens rest))
    else pure (String.singleton c :: (← tokens rest))

def bodyTokens (kind name text : String) (source : Bool) : Except String (List String) := do
  let cs := if source then stripComments text.toList else text.toList
  let rec find : List Char → Except String (List Char)
    | [] => throw s!"`{kind} {name}` not found"
    | c :: rest =>
      if atKeyword (c :: rest) kind && atKeyword (skipWs ((c :: rest).drop kind.length)) name
      then pure ((c :: rest).drop kind.length) else find rest
  let body ← skipUntilKw (← find cs) ":="
  let ts ← tokens body
  pure (ts.takeWhile fun t => !(["fun", "proc", "glob"].contains t))

def termTokens (e : CoreExpr) : Except String (List String) := do tokens (← expr e).toList
def pureTokens (p : generic_pexpr Unit sym) : Except String (List String) := do tokens (← pexpr true none p).toList
end FullText

/-- D6's dead-literal plant, changing only Specified(0) in a save initializer. -/
def plantSaveLiteral : CoreExpr → CoreExpr × Bool := rewriteFirstExpr fun e =>
  match e with
  | Expr an (Esave sb ins body) =>
    let rec go : List SaveInit → Option (List SaveInit)
      | [] => none
      | (s, (t, Pexpr pa u (PEctor Cspecified [Pexpr va v (PEval (Vobject (OVinteger (.IV .Prov_none 0))))]))) :: rest =>
        some ((s, (t, Pexpr pa u (PEctor Cspecified [Pexpr va v (PEval (Vobject (OVinteger (CerbMem.integerIval 7))))]))) :: rest)
      | i :: rest => (i :: ·) <$> go rest
    (fun ins => Expr an (Esave sb ins body)) <$> go ins
  | _ => none

def corpusDir : System.FilePath := "../docs/corpus-e0"

/-- E3: the pinned std.core SOURCE (the semantics workspace the package
    builds against; Main.lean:748 parses this file). -/
def stdCorePath : System.FilePath := "../.cerberus-ws/runtime/libcore/std.core"

def showToks (ts : List String) : String := " ".intercalate ts

def firstDiff (a b : List String) : Option (Nat × Option String × Option String) :=
  let rec go (i : Nat) : List String → List String → Option (Nat × Option String × Option String)
    | [], [] => none
    | x :: xs, y :: ys => if x == y then go (i + 1) xs ys else some (i, some x, some y)
    | x :: _, [] => some (i, some x, none)
    | [], y :: _ => some (i, none, some y)
  go 0 a b

/-- The two token streams of a row, or `none` after printing the failure. -/
def rowStreams (row : Row) : IO (Option (List String × List String)) := do
  let path := corpusDir / row.file
  let text? ← try
      let t ← IO.FS.readFile path
      pure (some t)
    catch e =>
      IO.eprintln s!"FAIL: cannot read {path}: {e}"
      pure none
  match text? with
  | none => pure none
  | some text =>
    match FullText.bodyTokens "proc" row.proc text false, FullText.termTokens row.term with
    | .ok tt, .ok st => pure (some (tt, st))
    | .error e, _ =>
      IO.eprintln s!"FAIL: {row.file}: tokenizer: {e}"
      pure none
    | _, .error e =>
      IO.eprintln s!"FAIL: {row.file}: renderer: {e}"
      pure none

/-- A plant's verdict: `some msg` = the plant MATCHES (vacuous instrument). -/
def plantVerdict (textToks : List String) (planted : CoreExpr) : String × Bool :=
  match FullText.termTokens planted with
  | .ok ts => if ts == textToks then ("MATCHES", true) else ("mismatch (expected)", false)
  | .error e => (s!"error ({e})", false)

/-- THE COVERAGE SWEEP (E1 range audit N-2): every `*.annot.core` file of
    the corpus directory is a table row or a `pendingCorpus` entry; a file
    that is neither is a FAIL (a silently unchecked program), and so is a
    pending entry or a row whose file does not exist (a stale ledger). -/
def coverageSweep (quiet : Bool) (rows : List Row) (pending : List (String × String)) :
    IO (Bool × List String) := do
  let entries ← System.FilePath.readDir corpusDir
  let files := (entries.map fun e => e.fileName).filter fun f => f.endsWith ".annot.core"
  let files := files.qsort (· < ·)
  let mut fail := false
  let mut report : List String := []
  for f in files do
    if rows.any (·.file == f) then
      report := report ++ [s!"| {f} | transcribed |"]
    else match pending.find? (·.1 == f) with
      | some (_, why) => report := report ++ [s!"| {f} | pending — {why} |"]
      | none =>
        unless quiet do
          IO.eprintln s!"FAIL: corpus file {f} has no transcription row and no pending entry (fail-closed)"
        fail := true
  for r in rows do
    unless files.contains r.file do
      unless quiet do IO.eprintln s!"FAIL: table row {r.file} names no corpus file"
      fail := true
  for (f, _) in pending do
    unless files.contains f do
      unless quiet do IO.eprintln s!"FAIL: pending entry {f} names no corpus file"
      fail := true
  pure (fail, report)

def checkCorpus (rows : List Row) : IO Unit := do
  let mut fail := false
  IO.println "# Corpus full-text check (D6: leaves, symbols, types, operators, punctuation and locations)"
  IO.println ""
  -- the coverage sweep, and its plant: the ledger with t1's row removed
  -- (and not made pending) MUST fail
  let (sweepFail, report) ← coverageSweep false corpusTable pendingCorpus
  IO.println "| corpus file | status |"
  IO.println "|---|---|"
  for line in report do IO.println line
  IO.println ""
  if sweepFail then
    IO.eprintln "FAIL: corpus coverage sweep — an unchecked corpus file or a stale ledger entry"
    fail := true
  let (plantFail, _) ← coverageSweep true (corpusTable.filter (·.file != "t1.annot.core")) pendingCorpus
  if !plantFail then
    IO.eprintln "FAIL: coverage-sweep plant (t1's row dropped) STILL PASSES — vacuous sweep"
    fail := true
  else
    IO.println "coverage sweep: every corpus file rowed or pending; plant (t1 row dropped) fails (expected)"
  IO.println ""
  let operandPlants : List (String × (CoreExpr → CoreExpr × Bool)) :=
    [("case scrutinee", wrapFirstCaseScrutinee), ("if condition", wrapFirstIfScrutinee),
     ("case pattern", wrapFirstCasePattern)]
  let mut exercisedOperands : List String := []
  IO.println "| file | proc | tokens | term = text | plant: bound dropped | plant: Astd stripped | plant: Specified unwrapped | plant: save initialiser unwrapped | E5 operand plants |"
  IO.println "|---|---|---|---|---|---|---|---|---|"
  for row in rows do
    match ← rowStreams row with
    | none => fail := true
    | some (textToks, termToks) =>
      let eqMain := textToks == termToks
      if !eqMain then
        fail := true
        IO.eprintln s!"FAIL: {row.file}/{row.proc}: full text mismatch"
        match firstDiff termToks textToks with
        | some (i, a, b) =>
          IO.eprintln s!"  first difference at token {i}: term `{a.getD "<end>"}`, text `{b.getD "<end>"}`"
        | none => pure ()
      let (dead, foundDead) := plantSaveLiteral row.term
      if !foundDead then
        IO.eprintln s!"FAIL: {row.file}: no save initialiser Specified(0) for the dead-literal plant"
        fail := true
      else
        let (msg, bad) := plantVerdict textToks dead
        IO.println s!"dead-literal plant: {row.file}/{row.proc}: save Specified(0) -> Specified(7): {msg}"
        if bad then fail := true
      let (planted, dropped) := dropFirstBound row.term
      let mut plantBound := "no bound to drop"
      if !dropped then
        IO.eprintln s!"FAIL: {row.file}: plant `bound dropped` — the term has no bound to drop"
        fail := true
      else
        let (msg, bad) := plantVerdict textToks planted
        plantBound := msg
        if bad then
          IO.eprintln s!"FAIL: {row.file}: plant `bound dropped` STILL MATCHES — vacuous instrument"
          fail := true
      let (plantStd, badStd) := plantVerdict textToks (stripStd row.term)
      if badStd then
        IO.eprintln s!"FAIL: {row.file}: plant `Astd stripped` STILL MATCHES — vacuous instrument"
        fail := true
      let (plantedSp, foundSp) := unwrapFirstSpecified row.term
      let mut plantSp := "no Specified to unwrap"
      if !foundSp then
        IO.eprintln s!"FAIL: {row.file}: plant `Specified unwrapped` — the term has no pure(Specified(…))"
        fail := true
      else
        let (msg, bad) := plantVerdict textToks plantedSp
        plantSp := msg
        if bad then
          IO.eprintln s!"FAIL: {row.file}: plant `Specified unwrapped` STILL MATCHES — vacuous instrument"
          fail := true
      -- E4: the save initialiser's `Specified` (a position the E2 plant never reached)
      let (plantedSv, foundSv) := unwrapFirstSaveInit row.term
      let mut plantSv := "no save initialiser Specified to unwrap"
      if !foundSv then
        IO.eprintln s!"FAIL: {row.file}: plant `save initialiser unwrapped` — the term has no `save … (x:= Specified(…))`"
        fail := true
      else
        let (msg, bad) := plantVerdict textToks plantedSv
        plantSv := msg
        if bad then
          IO.eprintln s!"FAIL: {row.file}: plant `save initialiser unwrapped` STILL MATCHES — vacuous instrument"
          fail := true
      let mut operandVerdicts : List String := []
      for (name, plant) in operandPlants do
        let (planted, found) := plant row.term
        if found then
          exercisedOperands := name :: exercisedOperands
          let (msg, bad) := plantVerdict textToks planted
          operandVerdicts := operandVerdicts ++ [s!"{name}: {msg}"]
          if bad then
            IO.eprintln s!"FAIL: {row.file}: plant `{name}` STILL MATCHES — vacuous instrument"
            fail := true
        else operandVerdicts := operandVerdicts ++ [s!"{name}: n/a"]
      IO.println s!"| {row.file} | {row.proc} | {termToks.length} | {if eqMain then "equal" else "DIFFER"} | {plantBound} | {plantStd} | {plantSp} | {plantSv} | {"; ".intercalate operandVerdicts} |"
  for (name, _) in operandPlants do
    unless exercisedOperands.contains name do
      IO.eprintln s!"FAIL: no corpus row exercises the E5 `{name}` plant"
      fail := true
  IO.println ""
  -- E3: the transcribed standard library against the pinned std.core SOURCE
  -- (the semantics workspace's runtime/libcore/std.core — the file the shipped
  -- pipeline parses). Every `stdTable` row's full body equals the token
  -- stream of its `fun` body; every applicable plant mismatches; a row with no
  -- applicable plant is red (an unplanted instrument).
  IO.println "# E3: transcribed std.core fragment vs the pinned std.core source"
  IO.println ""
  let stdText? ← try
      let t ← IO.FS.readFile stdCorePath
      pure (some t)
    catch e =>
      IO.eprintln s!"FAIL: cannot read {stdCorePath}: {e}"
      pure none
  match stdText? with
  | none => fail := true
  | some stdText =>
    IO.println "| fun | tokens | term = source | plants (applicable: verdict) |"
    IO.println "|---|---|---|---|"
    for row in stdTable do
      match FullText.bodyTokens "fun" row.name stdText true, FullText.pureTokens row.body with
      | .ok textToks, .ok termToks =>
        let eq := textToks == termToks
        if !eq then
          fail := true
          IO.eprintln s!"FAIL: std.core/{row.name}: full text mismatch"
          IO.eprintln s!"  source: {showToks textToks}"
          IO.eprintln s!"  term:   {showToks termToks}"
          match firstDiff termToks textToks with
          | some (i, a, b) => IO.eprintln s!"  first difference at token {i}: term {a}, source {b}"
          | none => pure ()
        let mut applicable := 0
        let mut verdicts : List String := []
        for (pname, plant) in stdPlants do
          let (planted, applied) := plant row.body
          if applied then
            applicable := applicable + 1
            match FullText.pureTokens planted with
            | .ok ts =>
              if ts == textToks then
                fail := true
                IO.eprintln s!"FAIL: std.core/{row.name}: plant `{pname}` STILL MATCHES — vacuous instrument"
                verdicts := verdicts ++ [s!"{pname}: MATCHES"]
              else verdicts := verdicts ++ [s!"{pname}: mismatch (expected)"]
            | .error e => verdicts := verdicts ++ [s!"{pname}: error ({e})"]
        if applicable == 0 then
          fail := true
          IO.eprintln s!"FAIL: std.core/{row.name}: no plant applies — an unplanted row"
        IO.println s!"| {row.name} | {termToks.length} | {if eq then "equal" else "DIFFER"} | {"; ".intercalate verdicts} |"
      | .error e, _ =>
        fail := true
        IO.eprintln s!"FAIL: std.core/{row.name}: tokenizer: {e}"
      | _, .error e =>
        fail := true
        IO.eprintln s!"FAIL: std.core/{row.name}: renderer: {e}"
  IO.println ""
  if fail then
    -- `throw`, NOT `IO.Process.exit`: inside `#eval` Lean emits the action's
    -- captured stdout/stderr only after it returns, so an `exit` would discard
    -- every diagnostic printed above (E2 range audit H-1). The uncaught error
    -- makes `lean` exit non-zero, which is what the gate reads.
    throw (IO.userError "corpus-skeleton: FAIL")
  else
    IO.println s!"corpus-skeleton: ok — {corpusTable.length} corpus row(s) and {stdTable.length} std.core row(s) equal, every plant mismatches"

def main : IO Unit := checkCorpus corpusTable

#eval main
