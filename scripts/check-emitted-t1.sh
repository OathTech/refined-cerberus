#!/usr/bin/env bash
# Retained single-fixture entry point; the full gate checks all four files.
set -euo pipefail
[[ $# -eq 0 ]] || { echo "usage: $0" >&2; exit 2; }
check_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec "$check_root/scripts/check-emitted-corpus.sh" t1
