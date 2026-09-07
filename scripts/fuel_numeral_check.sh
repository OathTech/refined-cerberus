#!/usr/bin/env bash
# fuel_numeral_check.sh — THE NO-FUEL-NUMERAL GATE (L2, 2026-09-07; the F2
# design's gate addition, docs/2026-09-04_fuel-restatement-design.md §4, and
# the landing charter's acceptance "zero fuel numerals outside the shipped
# corollaries"). Part of the trust base (gate 1 in test_unit.sh): FAIL-CLOSED.
#
# The rule ([USER 2026-09-03], DECISIONS "FUEL IS A DEFECT"; [USER 2026-09-03]
# no magic values): the ambient fuel is a quantified position `[LemFuel]`.
# The shipped binary's default `--fuel 100000000` is the ONLY numeral, and it
# may appear in exactly one place in this package — a `*_shipped` corollary,
# which instantiates a `[LemFuel]`-quantified export at `⟨100000000⟩` and
# says so in its name. Every other occurrence of a fuel numeral, or of a
# retired fuel constant, anywhere in the package's Lean sources is RED.
#
#   scripts/fuel_numeral_check.sh            # check the tree
#   scripts/fuel_numeral_check.sh --selftest # plant on scratch copies; every plant must be RED
#
# What is scanned: every .lean under cerberus-heaplang/CerberusHeapLang and the
# lib root, comments stripped (nested block comments and line comments), string
# and char literals kept (a numeral in a string is still a smell) and RESPECTED
# by the stripper: a `--` or `/-` inside a literal is not a comment, a `"`
# inside a comment does not open a string (the L2 range audit's H-2 / KOI C11
# class). An unterminated literal or block comment at end of file is RED (the
# stripper could not classify the file — fail-closed). The numerals are
# matched in the spellings a fuel bound is written in (`100000000`,
# `100_000_000`, `10^8`; likewise the retired `1000000` and `999999`; a hex
# or other exotic spelling is not covered — the gate is a speedbump against
# honest drift, not an adversarial filter). A hit is
# allowed only inside the DECLARATION whose header is `theorem <name>_shipped`:
# the allowance ends at the next declaration header AND at the next
# column-0 command that is not one (`#eval`, `open`, `set_option … in`, …).
# Retired constant names (`lemDefaultFuel`, `driverFuel`, `ndDefaultFuel`) are
# never allowed — they do not exist at the pin, so a mention is dead text.
set -euo pipefail
cd "$(dirname "$0")/.."

NUMERALS='100000000|100_000_000|10\s*\^\s*8|1000000|1_000_000|10\s*\^\s*6|999999|999_999'
RETIRED='lemDefaultFuel|CerbFuel\.driverFuel|ndDefaultFuel'

# scan <dir> <libroot>: prints violations, returns 1 if any
scan() {
  local dir="$1" root="$2" bad=0
  local files
  files=$(find "$dir" -name '*.lean' | sort)
  files="$files"$'\n'"$root"
  local f
  for f in $files; do
    [[ -f "$f" ]] || continue
    python3 - "$f" "$NUMERALS" "$RETIRED" <<'PY' || bad=1
import re, sys
path, numerals, retired = sys.argv[1], sys.argv[2], sys.argv[3]
src = open(path, encoding='utf-8').read()
# One pass over the source: blank comment text (nested /- -/ blocks, -- line
# comments) while tracking string and char literals, so a comment opener inside
# a literal is literal text and a quote inside a comment is comment text.
# Newlines are kept everywhere (line numbers survive); literal text is kept.
def ident_char(c): return c.isalnum() or c in "_'!?"
out = []; i = 0; n = len(src); depth = 0; state = 'code'   # code | str | line
while i < n:
    c = src[i]
    if state == 'line':
        if c == '\n': state = 'code'; out.append('\n')
        else: out.append(' ')
        i += 1; continue
    if depth > 0:
        if src.startswith('/-', i): depth += 1; out.append('  '); i += 2; continue
        if src.startswith('-/', i): depth -= 1; out.append('  '); i += 2; continue
        out.append(c if c == '\n' else ' '); i += 1; continue
    if state == 'str':
        if c == '\\' and i + 1 < n: out.append(src[i:i+2]); i += 2; continue
        if c == '"': state = 'code'
        out.append(c); i += 1; continue
    # code
    if src.startswith('/-', i): depth = 1; out.append('  '); i += 2; continue
    if src.startswith('--', i): state = 'line'; out.append('  '); i += 2; continue
    if c == '"': state = 'str'; out.append(c); i += 1; continue
    if c == "'" and (i == 0 or not ident_char(src[i-1])):
        j = i + 1                       # a char literal 'x' / '\n' / '"' / '\''
        j += 2 if (j < n and src[j] == '\\') else 1
        if j < n and src[j] == "'": out.append(src[i:j+1]); i = j + 1; continue
    out.append(c); i += 1
if state == 'str' or depth > 0:
    what = 'string literal' if state == 'str' else 'block comment'
    print(f"FAIL: {path}: unterminated {what} at end of file — the comment stripper cannot classify this file (fail-closed)")
    sys.exit(1)
lines = ''.join(out).split('\n')
num_re = re.compile(r'(?<![0-9A-Za-z_])(' + numerals + r')(?![0-9A-Za-z_])')
ret_re = re.compile(r'\b(' + retired + r')\b')
hdr_re = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|example|opaque|axiom)\s+([^\s:({\[]+)')
current = ('', '')
bad = False
for n, l in enumerate(lines, 1):
    m = hdr_re.match(l)
    if m: current = (m.group(1), m.group(2))
    elif l and not l[0].isspace():
        # a column-0 command that is not a declaration header (`#eval`, `open`,
        # `set_option … in`, `omit … in`, an attribute on its own line, `end`):
        # the `*_shipped` allowance does not extend past the declaration
        current = ('', '')
    for m2 in ret_re.finditer(l):
        print(f"FAIL: {path}:{n}: retired fuel constant `{m2.group(1)}` (in {current[0]} {current[1]})"); bad = True
    for m2 in num_re.finditer(l):
        allowed = current[0] == 'theorem' and current[1].endswith('_shipped')
        if not allowed:
            print(f"FAIL: {path}:{n}: fuel numeral `{m2.group(1)}` outside a `*_shipped` corollary (in {current[0]} {current[1]})"); bad = True
sys.exit(1 if bad else 0)
PY
  done
  return $bad
}

if [[ "${1:-}" == "--selftest" ]]; then
  tmp="$(mktemp -d "${TMPDIR:-/tmp}/fuelnum.XXXXXX")"
  trap 'rm -rf "$tmp"' EXIT
  mkdir -p "$tmp/pkg/CerberusHeapLang"
  ok=1
  red() {   # red <label> <expected-hit-count-or-'*'>: the plant in PlantA.lean must be RED
    echo "$1:"
    if scan "$tmp/pkg/CerberusHeapLang" "$tmp/pkg/none.lean" > "$tmp/out"; then echo "  PLANT FAIL: accepted"; ok=0
    else echo "  PLANT OK: $(grep -c FAIL "$tmp/out") hit(s)"; fi
  }
  green() { # green <label>: the plant must be GREEN (positive control)
    echo "$1:"
    if scan "$tmp/pkg/CerberusHeapLang" "$tmp/pkg/none.lean" > "$tmp/out"; then echo "  PLANT OK: green"
    else echo "  PLANT FAIL: red on an allowed shape"; cat "$tmp/out"; ok=0; fi
  }
  # plant A: a numeral inside an ordinary theorem — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_bad (n : Nat) (h : n ≤ 100000000) : n ≤ 100000000 := h
L
  red "PLANT A (numeral in an ordinary theorem)"
  # plant B: a retired constant name, in a def — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
def plant_dead : Nat := lemDefaultFuel
L
  red "PLANT B (retired constant)"
  # plant C: a numeral in a comment only — must be GREEN (comments are not code)
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
-- the shipped default is 100000000
/- lemDefaultFuel was 1000000 -/
theorem plant_fine : True := trivial
L
  green "PLANT C (numeral in comments only, positive control)"
  # plant D: the allowed shape — numeral inside a *_shipped theorem — must be GREEN
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_shipped (n : Nat) (h : n ≤ 100000000) :
    n ≤ 100000000 := h
theorem after (n : Nat) : n = n := rfl
L
  green "PLANT D (numeral inside a *_shipped corollary, positive control)"
  # plant E: the numeral in the theorem AFTER a *_shipped one — must be RED (the allowance does not leak)
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_shipped : True := trivial
theorem leak (n : Nat) (h : n ≤ 1000000) : n ≤ 1000000 := h
L
  red "PLANT E (numeral in the declaration after a *_shipped one)"
  # plant F: the numeral in a NON-declaration command after a *_shipped theorem — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_shipped : True := trivial
#eval (100000000 : Nat)
L
  red "PLANT F (numeral in a non-declaration command after a *_shipped one)"
  # plant G: the numeral spelled 10^8 in an ordinary statement — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_pow (n : Nat) (h : n ≤ 10^8) : n ≤ 10 ^ 8 := h
L
  red "PLANT G (the numeral spelled 10^8)"
  # plant H: the numeral spelled 100_000_000 — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_sep (n : Nat) (h : n ≤ 100_000_000) : n ≤ 100_000_000 := h
L
  red "PLANT H (the numeral spelled 100_000_000)"
  # plant I: the numeral on a line after a string literal containing `--` — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_str : "--".length = 2 ∧ (100000000 : Nat) = 100000000 := ⟨rfl, rfl⟩
L
  red "PLANT I (numeral after a \"--\" string literal on the same line)"
  # plant K: a `"` inside a line comment must not open a string that hides the next declaration — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
-- the "shipped default
theorem plant_after_quote_comment (n : Nat) (h : n ≤ 100000000) : n ≤ 100000000 := h
L
  red "PLANT K (numeral after a comment containing a lone \")"
  # plant L: a char literal '"' before a *_shipped theorem must not open a string — must be GREEN
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
def plant_char : Char := '"'
theorem plant_shipped (n : Nat) (h : n ≤ 100000000) : n ≤ 100000000 := h
L
  green "PLANT L (char literal '\"' before a *_shipped corollary, positive control)"
  if [[ $ok -eq 1 ]]; then echo "fuel_numeral_check: SELFTEST OK (11 plants: 8 red as required, 3 positive controls green)"; exit 0; fi
  echo "fuel_numeral_check: SELFTEST FAILED"; exit 1
fi

if scan cerberus-heaplang/CerberusHeapLang cerberus-heaplang/CerberusHeapLang.lean; then
  n=$(find cerberus-heaplang/CerberusHeapLang -name '*.lean' | wc -l)
  echo "ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant ($((n+1)) files scanned, comments stripped)"
else
  echo "FAIL: fuel numeral or retired fuel constant outside a *_shipped corollary (above)" >&2
  exit 1
fi
