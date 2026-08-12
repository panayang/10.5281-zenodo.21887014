#!/usr/bin/env bash
# Rebuild all five paper PDFs from a clean run of their LaTeX toolchains, and
# report a summary of errors, undefined references, and page counts for each.
#
# Run from anywhere (paths are resolved relative to the repository root):
#
#     tools/build_papers.sh              # rebuild all five
#     tools/build_papers.sh manuscript   # rebuild only paper/manuscript/{main,supplement}
#     tools/build_papers.sh preprint     # rebuild only paper/preprint/{main,supplement}
#     tools/build_papers.sh scd          # rebuild only paper/SCD.tex
#
# manuscript/main.tex and preprint/main.tex run pdflatex -> bibtex -> pdflatex
# -> pdflatex (they carry a bibliography); the two supplement.tex files run
# pdflatex twice (no bibliography); SCD.tex runs xelatex twice.
#
# Exits nonzero if any requested target fails to produce a PDF, reports a
# LaTeX error, or has residual undefined references after the full sequence.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOGDIR="$(mktemp -d -t build_papers.XXXXXX)"
FAIL=0

# Each entry: name | dir (relative to ROOT) | texfile (no extension) | engine | uses_bibtex (1/0)
TARGETS=(
  "manuscript-main|paper/manuscript|main|pdflatex|1"
  "manuscript-supplement|paper/manuscript|supplement|pdflatex|0"
  "preprint-main|paper/preprint|main|pdflatex|1"
  "preprint-supplement|paper/preprint|supplement|pdflatex|0"
  "SCD|paper|SCD|xelatex|0"
)

build_one() {
  local name="$1" dir="$2" tex="$3" engine="$4" bib="$5"
  local wd="$ROOT/$dir"
  local log="$LOGDIR/$name.log"

  echo "== $name  ($engine, $dir/$tex.tex) =="

  if [[ ! -f "$wd/$tex.tex" ]]; then
    echo "  SKIP: $wd/$tex.tex not found"
    FAIL=1
    return
  fi
  if ! command -v "$engine" >/dev/null 2>&1; then
    echo "  SKIP: $engine not found on PATH"
    FAIL=1
    return
  fi

  : > "$log"
  (
    cd "$wd" || exit 1
    "$engine" -interaction=nonstopmode "$tex.tex" >> "$log" 2>&1
    if [[ "$bib" == "1" ]]; then
      bibtex "$tex" >> "$log" 2>&1
      "$engine" -interaction=nonstopmode "$tex.tex" >> "$log" 2>&1
    fi
    "$engine" -interaction=nonstopmode "$tex.tex" >> "$log" 2>&1
  )
  local status=$?

  local errors undefined pages
  errors=$(grep -Ec '^!' "$log" || true)
  undefined=$(grep -Eic "Reference .* undefined|Citation .* undefined" "$log" || true)
  pages=$(pdfinfo "$wd/$tex.pdf" 2>/dev/null | awk '/^Pages:/{print $2}')

  if [[ "$status" -ne 0 || "$errors" -gt 0 || -z "$pages" ]]; then
    echo "  FAIL  exit=$status  errors=$errors  undefined_refs=$undefined  pages=${pages:-none}"
    echo "  log: $log"
    FAIL=1
  elif [[ "$undefined" -gt 0 ]]; then
    echo "  WARN  errors=0  undefined_refs=$undefined  pages=$pages"
    echo "  log: $log  (undefined refs sometimes need one more pass; rerun if this persists)"
    FAIL=1
  else
    echo "  OK    errors=0  undefined_refs=0  pages=$pages"
  fi
  echo
}

target_manuscript() {
  build_one "manuscript-main" "paper/manuscript" "main" "pdflatex" "1"
  build_one "manuscript-supplement" "paper/manuscript" "supplement" "pdflatex" "0"
}

target_preprint() {
  build_one "preprint-main" "paper/preprint" "main" "pdflatex" "1"
  build_one "preprint-supplement" "paper/preprint" "supplement" "pdflatex" "0"
}

target_scd() {
  build_one "SCD" "paper" "SCD" "xelatex" "0"
}

case "${1:-all}" in
  all)
    target_manuscript
    target_preprint
    target_scd
    ;;
  manuscript) target_manuscript ;;
  preprint)   target_preprint ;;
  scd)        target_scd ;;
  *)
    echo "usage: $0 [all|manuscript|preprint|scd]" >&2
    exit 2
    ;;
esac

echo "Logs kept in: $LOGDIR"
if [[ "$FAIL" -ne 0 ]]; then
  echo "One or more targets FAILED or need a rerun. See logs above."
  exit 1
fi
echo "All requested targets compiled cleanly."
