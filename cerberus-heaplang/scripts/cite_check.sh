#!/usr/bin/env bash
# cite_check.sh — the `file:line` cite audit for ARCHITECTURE.md (and any doc
# written in its cite convention). A SPEEDBUMP ([USER 2026-09-02]): it REPORTS
# drift and, on request, rewrites the cites it can attribute to a declaration;
# it is not a gate and is not in test_unit.sh. Born at the E4 range audit's D-2
# (docs/2026-09-05_audit-e4-range.md; KOI C18): 248 cites, 87 stale at 7af24b2.
#
#   usage (from cerberus-heaplang/):
#     scripts/cite_check.sh [--fix] [DOC]          DOC defaults to ARCHITECTURE.md
#   output: one TSV line per cite —
#     class  doc:line  file:N  ->  suggestion  ident  note
#   classes:
#     EXACT      line N (±1) of the file mentions the attributed identifier
#     DECL       stale: the identifier's declaration head is at another line
#                (rewritten by --fix when the cite is a single, tightly
#                attributed one; a RANGE start/end or a loose attribution is
#                reported with the suggestion and left for the hand check)
#     USE        stale: no declaration head found, the identifier occurs
#                elsewhere in the file (nearest occurrence suggested; HAND)
#     HAND       no identifier could be attributed (a prose/region cite, a
#                wildcard, a range end) — check by hand
#     PIN        a cite into the pinned semantics workspace or a vendored dep
#                that the identifier check cannot confirm — those files do not
#                move between pins; reported, never rewritten
#     NOFILE     the cited file could not be resolved
#   exit: 0 always (a speedbump reports; it never blocks) unless a usage error.
#
# THE CONVENTION IT READS. Cites are backticked spans `File.lean:N` or `:N`
# (the last-named file of the paragraph). The identifier is the backticked
# declaration-shaped span nearest BEFORE the cite on the same line, with two
# refinements: a parenthesised cite group `(`F:N`, `:M`, …)` after an
# identifier group `A`, `B`, … of the SAME length is mapped positionally
# (`wps_call`/`wps_call_root` (`Wps.lean:444`/`:494`)), and a span starting
# with `_` (`_alloc` `:667`) names the previous identifier's suffixed twin.
# A cite immediately joined by an en dash to another (`:6257`–`:6338`) is a
# RANGE and is never rewritten. In a table row the identifier is the row's
# first backticked span when no closer one exists.
# Files: a bare name resolves under CerberusHeapLang/ (then Examples/,
# scripts/, ../scripts/, docs/); a name preceded by the word "generated"
# resolves in the pinned workspace ../.cerberus-ws/lean_frontend/generated/;
# a path with a directory resolves as written (relative to cerberus-heaplang/).
#
# WHAT IT DOES NOT ESTABLISH: that a cite's line is the RIGHT declaration (the
# attribution is heuristic — a stale cite whose neighbouring identifier is a
# different declaration is rewritten to that declaration's line; read the
# TSV), nor anything about prose/region cites (HAND). It is a drift detector.
set -euo pipefail
cd "$(dirname "$0")/.."

fix=0
doc=ARCHITECTURE.md
for arg in "$@"; do
  case "$arg" in
    --fix) fix=1 ;;
    -*) echo "usage: $0 [--fix] [DOC]" >&2; exit 2 ;;
    *) doc="$arg" ;;
  esac
done
[[ -f "$doc" ]] || { echo "cite_check: no such doc: $doc" >&2; exit 2; }

tmp="$(mktemp -d "${TMPDIR:-.}/cite_check.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT

# ---- phase 1: extract every cite with its attributed identifier (gawk) ----
# TSV: docline \t col \t spantext \t file \t N \t ident \t flags
#   flags: R (part of a range), L (loose attribution), G (workspace 'generated')
gawk '
function isident(s) { return s ~ /^[A-Za-z_][A-Za-z0-9_.'\''?!₀-₉]*$/ }
function isfile(s)  { return s ~ /^[A-Za-z0-9_.\/-]+\.(lean|sh|md|tsv)$/ }
# flush(): process the spans of the finished paragraph (or table row) as ONE
# token stream — identifier groups and cite groups may straddle line breaks
function flush(    i, j, c, k, s, cg, gi, idx, f, N, flags, isrange, ident, altfile, sep, fp, mm) {
  if (n == 0) return
  gi = 0; delete idg; lastident = ""
  i = 1
  while (i <= n) {
    k = kind[i]
    if (k == "P") { if (span[i] !~ /\.md$/) { curfile = span[i]; curgen = (before[i] ~ /generated[^`]*$/) ? "G" : "" }; i++; continue }
    if (k == "I") {
      s = span[i]
      if (s ~ /^_/ && lastident != "") s = lastident s      # `_alloc` → previous ident + suffix
      idg[++gi] = s; lastident = s; i++; continue
    }
    if (k == "F" || k == "C") {
      # the cite group: consecutive cites joined by "/", ", ", "; ", " and ", "–" (whitespace incl. newlines)
      cg = 0; delete cgi; j = i
      while (j <= n && (kind[j] == "F" || kind[j] == "C")) {
        cgi[++cg] = j
        j++                                        # advance FIRST (j > i on exit: no stall)
        if (j <= n && (kind[j] == "F" || kind[j] == "C")) {
          sep = before[j]
          if (sep !~ /^[[:space:]]*(\/|,|;|–|and|—)?[[:space:]]*(\(|;)?[[:space:]]*$/) break
        }
      }
      # a module word directly before the group ("StructExhibit (`:199`, `:830`)",
      # the consumer table) names the file for the group; the paragraph file is the fallback
      altfile = ""
      if (match(before[cgi[1]], /([A-Za-z][A-Za-z0-9.]*) \($/, mm)) altfile = mm[1] ".lean"
      for (c = 1; c <= cg; c++) {
        idx = cgi[c]
        s = span[idx]
        if (kind[idx] == "F") { split(s, fp, ":"); f = fp[1]; N = fp[2]; curfile = f; curgen = (before[idx] ~ /generated[^`]*$/) ? "G" : "" }
        else { f = (altfile != "") ? altfile "|" curfile : curfile; N = substr(s, 2) }
        flags = ""
        isrange = 0
        if (before[idx] ~ /–[[:space:]]*$/) isrange = 1
        if (after[idx] ~ /^[[:space:]]*–/) isrange = 1
        if (isrange) flags = flags "R"
        if (curgen == "G") flags = flags "G"
        # positional mapping when the identifier group has the cite group'\''s length;
        # otherwise the nearest identifier, flagged L (loose) unless both groups are singletons
        if (cg == gi) ident = idg[c]
        else if (gi > 0 && lastident != "") { ident = lastident; if (cg > 1 || gi > 1) flags = flags "L" }
        else if (rowident != "") { ident = rowident; flags = flags "L" }
        else ident = "-"
        if (f == "") f = "-"
        print lineno[idx], col[idx], "`" span[idx] "`", f, N, ident, flags
      }
      i = j; gi = 0; delete idg
      continue
    }
    i++
  }
  n = 0; delete span; delete kind; delete before; delete after; delete col; delete lineno
}
BEGIN { curfile = ""; OFS = "\t"; n = 0; rowident = ""; tail = "" }
# a heading resets the file context; a blank line ends the paragraph; a table
# row is its own paragraph (the convention: `:N` cites the LAST-NAMED
# .lean/.sh file of the section)
/^#/ { flush(); curfile = ""; rowident = ""; tail = ""; next }
/^[[:space:]]*$/ { flush(); rowident = ""; tail = ""; next }
{
  line = $0
  if (line ~ /^\|/) { flush(); rowident = ""; tail = "" }
  # tokenise the backticked spans of the line, appending to the paragraph stream
  pos = 1; rest = line; first = n + 1
  while (match(rest, /`[^`]+`/)) {
    n++
    span[n] = substr(rest, RSTART + 1, RLENGTH - 2)
    col[n] = pos + RSTART - 1
    lineno[n] = NR
    before[n] = tail ((RSTART > 1) ? substr(rest, 1, RSTART - 1) : "")
    tail = ""
    pos += RSTART + RLENGTH - 1
    rest = substr(rest, RSTART + RLENGTH)
    after[n] = rest
  }
  # the text after the last span of this line joins the next span'\''s "before"
  if (n >= first) { tail = rest "\n" } else { tail = tail line "\n" }
  if (line ~ /^\|/ && n >= first) { for (q = first; q <= n; q++) if (isident(span[q])) { rowident = span[q]; break } }
  # classify the new spans
  for (q = first; q <= n; q++) {
    kind[q] = "O"
    s = span[q]
    if (s ~ /^[A-Za-z0-9_.\/-]+\.(lean|sh|md|tsv):[0-9]+$/) { kind[q] = "F" }
    else if (s ~ /^:[0-9]+$/) { kind[q] = "C" }
    else if (isfile(s)) { kind[q] = "P" }                  # before isident: `X.lean` is identifier-shaped too
    else if (isident(s)) { kind[q] = "I" }
    else if (s ~ /^[^ ]+ : [A-Za-z_][A-Za-z0-9_.'\''?!₀-₉]*$/) { kind[q] = "I"; span[q] = substr(s, index(s, " : ") + 3) }   # `Ls : LabelSpec` names LabelSpec
    else if (s ~ /^[A-Za-z_][A-Za-z0-9_.'\''?!₀-₉]* / && isident(substr(s, 1, index(s, " ") - 1))) { kind[q] = "I"; span[q] = substr(s, 1, index(s, " ") - 1) }
  }
  if (line ~ /^\|/) { flush(); rowident = ""; tail = "" }
}
END { flush() }' "$doc" > "$tmp/cites.tsv"

# ---- phase 2: resolve files, verify, suggest ----
resolve() {  # $1 = file(s) as cited ("a|b": try a, then b), $2 = flags
  local fs="$1" flags="$2" c f
  local ws="../.cerberus-ws/lean_frontend/generated"
  if [[ "$fs" == *"|"* ]]; then
    local r
    r="$(resolve "${fs%%|*}" "$flags")"; [[ -n "$r" ]] && { echo "$r"; return; }
    resolve "${fs#*|}" "$flags"; return
  fi
  f="$fs"
  if [[ "$f" == *.lean && "$f" == *.*.lean && "$f" != */* ]]; then   # Examples.CallSmoke.lean → Examples/CallSmoke.lean
    c="CerberusHeapLang/${f%.lean}"; c="${c//./\/}.lean"; [[ -f "$c" ]] && { echo "$c"; return; }
  fi
  if [[ "$f" == */* ]]; then
    for c in "$f" "CerberusHeapLang/$f" "../$f"; do [[ -f "$c" ]] && { echo "$c"; return; }; done
  else
    if [[ "$flags" == *G* ]]; then
      [[ -f "$ws/$f" ]] && { echo "$ws/$f"; return; }
    fi
    for c in "CerberusHeapLang/$f" "CerberusHeapLang/Examples/$f" "scripts/$f" "../scripts/$f" "docs/$f" "../docs/$f" "$ws/$f"; do
      [[ -f "$c" ]] && { echo "$c"; return; }
    done
  fi
  echo ""
}

# declaration heads of an identifier (last component), one line number per line
declines() {  # $1 = file, $2 = ident
  local f="$1" id="$2" last re
  last="${id##*.}"
  re="$(printf '%s' "$last" | sed 's/[][\.*^$?+(){}|\\]/\\\\&/g')"
  # theorem/def heads (with any namespace prefix), constructors `| name`, fields `name :`
  gawk -v re="$re" '
    $0 ~ ("^(private |protected |noncomputable |partial |unsafe |scoped |local |@\\[[^]]*\\] *)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|macro|syntax|notation|macro_rules|elab) ([A-Za-z0-9_'\''?!₀-₉]+\\.)*" re "([^A-Za-z0-9_'\''?!₀-₉]|$)") { print NR; next }
    $0 ~ ("^[[:space:]]*\\| " re "([^A-Za-z0-9_'\''?!₀-₉]|$)") { print NR; next }
    $0 ~ ("^[[:space:]]+\\(?" re "[[:space:]]*:") { print NR; next }
  ' "$f"
}

mentions() {  # $1 = file, $2 = ident, $3 = N : does line N or N±1 mention the ident's last component?
  local f="$1" id="$2" N="$3" last re
  last="${id##*.}"
  re="$(printf '%s' "$last" | sed 's/[][\.*^$?+(){}|\\]/\\\\&/g')"
  gawk -v re="$re" -v N="$N" 'NR >= N-1 && NR <= N+1 && $0 ~ ("(^|[^A-Za-z0-9_'\''?!₀-₉])" re "([^A-Za-z0-9_'\''?!₀-₉]|$)") { found = 1 } NR > N+1 { exit } END { exit !found }' "$f"
}

nearest() {  # stdin: line numbers; $1 = N → the nearest
  gawk -v N="$1" 'BEGIN { best = ""; bd = -1 } { d = $1 - N; if (d < 0) d = -d; if (bd < 0 || d < bd) { bd = d; best = $1 } } END { print best }'
}

n_all=0; n_exact=0; n_decl=0; n_use=0; n_hand=0; n_nofile=0; n_fixed=0; n_range=0; n_pin=0
: > "$tmp/report.tsv"
: > "$tmp/fixes.tsv"
while IFS=$'\t' read -r dl col span f N ident flags; do
  n_all=$((n_all + 1))
  path="$(resolve "$f" "$flags")"
  if [[ -z "$path" ]]; then
    n_nofile=$((n_nofile + 1))
    printf 'NOFILE\t%s:%s\t%s:%s\t->\t-\t%s\t%s\n' "$doc" "$dl" "$f" "$N" "$ident" "$flags" >> "$tmp/report.tsv"; continue
  fi
  total="$(wc -l < "$path")"
  isrange=""; [[ "$flags" == *R* ]] && isrange="R"
  pinned=""; case "$path" in ../.cerberus-ws/*|.lake/packages/*) pinned="P" ;; esac
  if [[ "$ident" == "-" || "$ident" == *'*'* || "$ident" == *'<'* ]]; then
    n_hand=$((n_hand + 1))
    printf 'HAND\t%s:%s\t%s:%s\t->\t-\t%s\t%s\n' "$doc" "$dl" "$path" "$N" "$ident" "no identifier attributed${isrange:+; range}" >> "$tmp/report.tsv"; continue
  fi
  if (( N <= total )) && mentions "$path" "$ident" "$N"; then
    n_exact=$((n_exact + 1))
    [[ -n "$isrange" ]] && n_range=$((n_range + 1))
    printf 'EXACT\t%s:%s\t%s:%s\t->\t%s\t%s\t%s\n' "$doc" "$dl" "$path" "$N" "$N" "$ident" "$flags" >> "$tmp/report.tsv"; continue
  fi
  if [[ -n "$pinned" ]]; then
    # the pinned workspace / vendored deps do not move between pins: a cite there
    # that the identifier check cannot confirm is reported, never rewritten
    n_pin=$((n_pin + 1))
    printf 'PIN\t%s:%s\t%s:%s\t->\t-\t%s\t%s\n' "$doc" "$dl" "$path" "$N" "$ident" "pinned/vendored file, unchanged since the pin — not judged (identifier not on the line)" >> "$tmp/report.tsv"; continue
  fi
  decl="$(declines "$path" "$ident" | nearest "$N")"
  if [[ -n "$decl" ]]; then
    n_decl=$((n_decl + 1))
    note="$flags"
    if [[ -n "$isrange" ]]; then note="RANGE (delta $((decl - N))) — hand check"; n_range=$((n_range + 1))
    elif [[ "$flags" == *L* ]]; then note="loose attribution — hand check"
    elif [[ $fix -eq 1 ]]; then
      printf '%s\t%s\t%s\t%s\n' "$dl" "$col" "$span" "$decl" >> "$tmp/fixes.tsv"; note="FIXED"; n_fixed=$((n_fixed + 1))
    else note="fixable"; fi
    printf 'DECL\t%s:%s\t%s:%s\t->\t%s\t%s\t%s\n' "$doc" "$dl" "$path" "$N" "$decl" "$ident" "$note" >> "$tmp/report.tsv"; continue
  fi
  last="${ident##*.}"
  use="$( (grep -n -F -- "$last" "$path" || true) | cut -d: -f1 | nearest "$N")"
  if [[ -n "$use" ]]; then
    n_use=$((n_use + 1))
    printf 'USE\t%s:%s\t%s:%s\t->\t%s\t%s\t%s\n' "$doc" "$dl" "$path" "$N" "$use" "$ident" "no declaration head; nearest mention — hand check${isrange:+; range}" >> "$tmp/report.tsv"
  else
    n_hand=$((n_hand + 1))
    printf 'HAND\t%s:%s\t%s:%s\t->\t-\t%s\t%s\n' "$doc" "$dl" "$path" "$N" "$ident" "identifier not in file${isrange:+; range}" >> "$tmp/report.tsv"
  fi
done < "$tmp/cites.tsv"

cat "$tmp/report.tsv"

# ---- phase 3: apply the fixes (positional, per line, right to left) ----
if [[ $fix -eq 1 && -s "$tmp/fixes.tsv" ]]; then
  sort -t$'\t' -k1,1n -k2,2nr "$tmp/fixes.tsv" > "$tmp/fixes.sorted"
  gawk -F'\t' -v fixes="$tmp/fixes.sorted" '
    BEGIN { while ((getline l < fixes) > 0) { split(l, a, "\t"); nf[a[1]]++; fc[a[1], nf[a[1]]] = a[2]; fs[a[1], nf[a[1]]] = a[3]; fn[a[1], nf[a[1]]] = a[4] } }
    {
      line = $0
      if (NR in nf) {
        for (q = 1; q <= nf[NR]; q++) {            # right to left: columns stay valid
          c = fc[NR, q]; s = fs[NR, q]; newN = fn[NR, q]
          # byte-position replacement guarded by the span text at that position
          if (substr(line, c, length(s)) == s) {
            t = s; sub(/:[0-9]+`$/, ":" newN "`", t)
            line = substr(line, 1, c - 1) t substr(line, c + length(s))
          } else { print "cite_check: span moved at " FILENAME ":" NR " col " c " (" s ") — not rewritten" > "/dev/stderr" }
        }
      }
      print line
    }' "$doc" > "$tmp/doc.new"
  mv "$tmp/doc.new" "$doc"
fi

echo "cite-check: $doc — $n_all cites; EXACT $n_exact; DECL $n_decl (fixed $n_fixed; ranges among them counted in RANGE); USE $n_use; HAND $n_hand; PIN $n_pin; NOFILE $n_nofile; RANGE $n_range (never rewritten)"
