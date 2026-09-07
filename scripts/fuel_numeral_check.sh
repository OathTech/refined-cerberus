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
# lib root, comments stripped (line comments and block comments), string
# literals kept (a numeral in a string is still a smell). A hit is allowed only
# when the nearest preceding declaration header is a `theorem <name>_shipped`.
# Retired constant names (`lemDefaultFuel`, `driverFuel`, `ndDefaultFuel`) are
# never allowed — they do not exist at the pin, so a mention is dead text.
set -euo pipefail
cd "$(dirname "$0")/.."

NUMERALS='100000000|1000000|999999'
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
    # strip block comments, then line comments; keep line numbers (blank the stripped text)
    python3 - "$f" "$NUMERALS" "$RETIRED" <<'PY' || bad=1
import re, sys
path, numerals, retired = sys.argv[1], sys.argv[2], sys.argv[3]
src = open(path, encoding='utf-8').read()
# blank block comments /- … -/ (nested), preserving newlines
out = []; i = 0; depth = 0
while i < len(src):
    if src.startswith('/-', i):
        depth += 1; i += 2; out.append('  '); continue
    if depth > 0 and src.startswith('-/', i):
        depth -= 1; i += 2; out.append('  '); continue
    c = src[i]
    out.append(c if (depth == 0 or c == '\n') else (' ' if c != '\n' else '\n'))
    i += 1
text = ''.join(out)
lines = text.split('\n')
# blank line comments
lines = [re.sub(r'--.*$', '', l) for l in lines]
num_re = re.compile(r'(?<![0-9A-Za-z_])(' + numerals + r')(?![0-9A-Za-z_])')
ret_re = re.compile(r'\b(' + retired + r')\b')
hdr_re = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|example|opaque|axiom)\s+([^\s:({\[]+)')
current = ('', '')
bad = False
for n, l in enumerate(lines, 1):
    m = hdr_re.match(l)
    if m: current = (m.group(1), m.group(2))
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
  # plant 1: a numeral inside an ordinary theorem — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_bad (n : Nat) (h : n ≤ 100000000) : n ≤ 100000000 := h
L
  echo "PLANT A (numeral in an ordinary theorem):"
  if scan "$tmp/pkg/CerberusHeapLang" "$tmp/pkg/none.lean" > "$tmp/a.out"; then echo "  PLANT FAIL: accepted"; ok=0; else echo "  PLANT OK: $(grep -c FAIL "$tmp/a.out") hit(s)"; fi
  # plant 2: a retired constant name, in a def — must be RED
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
def plant_dead : Nat := lemDefaultFuel
L
  echo "PLANT B (retired constant):"
  if scan "$tmp/pkg/CerberusHeapLang" "$tmp/pkg/none.lean" > "$tmp/b.out"; then echo "  PLANT FAIL: accepted"; ok=0; else echo "  PLANT OK: $(grep -c FAIL "$tmp/b.out") hit(s)"; fi
  # plant 3: a numeral in a comment only — must be GREEN (comments are not code)
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
-- the shipped default is 100000000
/- lemDefaultFuel was 1000000 -/
theorem plant_fine : True := trivial
L
  echo "PLANT C (numeral in comments only, positive control):"
  if scan "$tmp/pkg/CerberusHeapLang" "$tmp/pkg/none.lean" > "$tmp/c.out"; then echo "  PLANT OK: green"; else echo "  PLANT FAIL: red on a comment"; cat "$tmp/c.out"; ok=0; fi
  # plant 4: the allowed shape — numeral inside a *_shipped theorem — must be GREEN
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_shipped (n : Nat) (h : n ≤ 100000000) :
    n ≤ 100000000 := h
theorem after (n : Nat) : n = n := rfl
L
  echo "PLANT D (numeral inside a *_shipped corollary, positive control):"
  if scan "$tmp/pkg/CerberusHeapLang" "$tmp/pkg/none.lean" > "$tmp/d.out"; then echo "  PLANT OK: green"; else echo "  PLANT FAIL: red on the allowed shape"; cat "$tmp/d.out"; ok=0; fi
  # plant 5: the numeral in the theorem AFTER a *_shipped one — must be RED (the allowance does not leak)
  cat > "$tmp/pkg/CerberusHeapLang/PlantA.lean" <<'L'
theorem plant_shipped : True := trivial
theorem leak (n : Nat) (h : n ≤ 1000000) : n ≤ 1000000 := h
L
  echo "PLANT E (numeral in the declaration after a *_shipped one):"
  if scan "$tmp/pkg/CerberusHeapLang" "$tmp/pkg/none.lean" > "$tmp/e.out"; then echo "  PLANT FAIL: accepted"; ok=0; else echo "  PLANT OK: $(grep -c FAIL "$tmp/e.out") hit(s)"; fi
  if [[ $ok -eq 1 ]]; then echo "fuel_numeral_check: SELFTEST OK (5 plants: 3 red as required, 2 positive controls green)"; exit 0; fi
  echo "fuel_numeral_check: SELFTEST FAILED"; exit 1
fi

if scan cerberus-heaplang/CerberusHeapLang cerberus-heaplang/CerberusHeapLang.lean; then
  n=$(find cerberus-heaplang/CerberusHeapLang -name '*.lean' | wc -l)
  echo "ok: no fuel numeral (100000000/1000000/999999) outside a *_shipped corollary and no retired fuel constant ($((n+1)) files scanned, comments stripped)"
else
  echo "FAIL: fuel numeral or retired fuel constant outside a *_shipped corollary (above)" >&2
  exit 1
fi
