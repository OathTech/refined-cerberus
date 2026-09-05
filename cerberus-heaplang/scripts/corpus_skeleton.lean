/-
corpus_skeleton.lean — THE EXECUTABLE EQUALITY SPEEDBUMP of the emitted-Core
dialect arc (E1; [USER 2026-09-04] E0 question 3). For every row of
`CerberusHeapLang.CorpusE0.corpusTable` the annotation/bound skeleton of
the hand-transcribed term must equal the token stream tokenized off the
oracle's emitted text `docs/corpus-e0/<file>` (repository root); and the
two PLANTS of every row (first `bound` dropped; every `Astd` stripped)
must NOT match — a plant that matches means the instrument is vacuous and
fails the run. Scope and blind spots: the module's header
(CerberusHeapLang/Examples/CorpusE0.lean).

Run (from cerberus-heaplang/):
  ../scripts/capped ~/.elan/bin/lake env lean scripts/corpus_skeleton.lean
Exit 0 = every row matches and every plant mismatches; 1 otherwise.
-/
import CerberusHeapLang.Examples.CorpusE0

open CerberusHeapLang CerberusHeapLang.CorpusE0

def corpusDir : System.FilePath := "../docs/corpus-e0"

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

def main : IO Unit := do
  let mut fail := false
  IO.println "# Corpus skeleton check (E1)"
  IO.println ""
  IO.println "| file | proc | tokens | term = text | plant: bound dropped | plant: Astd stripped |"
  IO.println "|---|---|---|---|---|---|"
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
        | some (i, a, b) => IO.eprintln s!"  first difference at token {i}: term {a}, text {b}"
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
      IO.println s!"| {row.file} | {row.proc} | {termToks.length} | {if eqMain then "equal" else "DIFFER"} | {plantBound} | {plantStd} |"
  IO.println ""
  if fail then
    IO.println "corpus-skeleton: FAIL"
    IO.Process.exit 1
  else
    IO.println s!"corpus-skeleton: ok — {corpusTable.length} row(s) equal, every plant mismatches"

#eval main
