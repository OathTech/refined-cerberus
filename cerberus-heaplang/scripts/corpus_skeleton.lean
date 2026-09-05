/-
corpus_skeleton.lean — THE EXECUTABLE EQUALITY SPEEDBUMP of the emitted-Core
dialect arc (E1; [USER 2026-09-04] E0 question 3). For every row of
`CerberusHeapLang.CorpusE0.corpusTable` the annotation/bound skeleton of
the hand-transcribed term must equal the token stream tokenized off the
oracle's emitted text `docs/corpus-e0/<file>` (repository root); and the
four PLANTS of every row (first `bound` dropped; every `Astd` stripped;
E2: the first `pure(Specified(…))` unwrapped; E4: the first `save`
initialiser's `Specified(…)` unwrapped) must NOT match — a plant that
matches means the instrument is vacuous and fails the run. Scope and blind spots: the module's header
(CerberusHeapLang/Examples/CorpusE0.lean).

Run (from cerberus-heaplang/):
  ../scripts/capped ~/.elan/bin/lake env lean scripts/corpus_skeleton.lean
Exit 0 = every row matches and every plant mismatches; non-zero otherwise (the
failure is raised as an `IO.userError` so every diagnostic printed before it is
emitted — never `IO.Process.exit`, which inside `#eval` discards them).
-/
import CerberusHeapLang.Examples.CorpusE0

open CerberusHeapLang CerberusHeapLang.CorpusE0

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
    match tokenizeProc text row.proc, skeleton row.term with
    | .ok tt, .ok st => pure (some (tt, st))
    | .error e, _ =>
      IO.eprintln s!"FAIL: {row.file}: tokenizer: {e}"
      pure none
    | _, .error e =>
      IO.eprintln s!"FAIL: {row.file}: skeleton: {e}"
      pure none

/-- A plant's verdict: `some msg` = the plant MATCHES (vacuous instrument). -/
def plantVerdict (textToks : List String) (planted : CoreExpr) : String × Bool :=
  match skeleton planted with
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

def main : IO Unit := do
  let mut fail := false
  IO.println "# Corpus skeleton check (E1 skeleton; E2 pure expressions; E3 std.core fragment; E4 save initialisers)"
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
  IO.println "| file | proc | tokens | term = text | plant: bound dropped | plant: Astd stripped | plant: Specified unwrapped | plant: save initialiser unwrapped |"
  IO.println "|---|---|---|---|---|---|---|---|"
  for row in corpusTable do
    match ← rowStreams row with
    | none => fail := true
    | some (textToks, termToks) =>
      let eqMain := textToks == termToks
      if !eqMain then
        fail := true
        IO.eprintln s!"FAIL: {row.file}/{row.proc}: skeleton ≠ text"
        IO.eprintln s!"  text: {showToks textToks}"
        IO.eprintln s!"  term: {showToks termToks}"
        match firstDiff termToks textToks with
        | some (i, a, b) =>
          IO.eprintln s!"  first difference at token {i}: term `{a.getD "<end>"}`, text `{b.getD "<end>"}`"
        | none => pure ()
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
      IO.println s!"| {row.file} | {row.proc} | {termToks.length} | {if eqMain then "equal" else "DIFFER"} | {plantBound} | {plantStd} | {plantSp} | {plantSv} |"
  IO.println ""
  -- E3: the transcribed standard library against the pinned std.core SOURCE
  -- (the semantics workspace's runtime/libcore/std.core — the file the shipped
  -- pipeline parses). Every `stdTable` row's body skeleton equals the token
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
      match tokenizeFun stdText row.name, pexprSkeleton row.body with
      | .ok textToks, .ok termToks =>
        let eq := textToks == termToks
        if !eq then
          fail := true
          IO.eprintln s!"FAIL: std.core/{row.name}: skeleton ≠ source"
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
            match pexprSkeleton planted with
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
        IO.eprintln s!"FAIL: std.core/{row.name}: skeleton: {e}"
  IO.println ""
  if fail then
    -- `throw`, NOT `IO.Process.exit`: inside `#eval` Lean emits the action's
    -- captured stdout/stderr only after it returns, so an `exit` would discard
    -- every diagnostic printed above (E2 range audit H-1). The uncaught error
    -- makes `lean` exit non-zero, which is what the gate reads.
    throw (IO.userError "corpus-skeleton: FAIL")
  else
    IO.println s!"corpus-skeleton: ok — {corpusTable.length} corpus row(s) and {stdTable.length} std.core row(s) equal, every plant mismatches"

#eval main
