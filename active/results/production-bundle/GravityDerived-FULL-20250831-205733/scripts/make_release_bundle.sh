#!/usr/bin/env bash
set -euo pipefail

# Move to this script's directory
cd "$(dirname "$0")"

ROOT_DIR="$(cd ../.. && pwd)"
RESULTS_DIR="$ROOT_DIR/active/results"
PAPER_DIR="$ROOT_DIR/active/paper"
SCRIPTS_DIR="$ROOT_DIR/active/scripts"
RELEASE_DIR="$RESULTS_DIR/release"

mkdir -p "$RELEASE_DIR"

# Timestamped bundle name
STAMP="$(date +%Y%m%d-%H%M%S)"
BUNDLE_NAME="GravityDerived-${STAMP}"
STAGE_DIR="$RELEASE_DIR/$BUNDLE_NAME"

echo "[bundle] Staging into $STAGE_DIR"
rm -rf "$STAGE_DIR"
mkdir -p "$STAGE_DIR/scripts" "$STAGE_DIR/paper" "$STAGE_DIR/results"

# 1) Paper sources and PDFs if present
cp -f "$PAPER_DIR/Gravity-derived.tex" "$STAGE_DIR/paper/" 2>/dev/null || true
cp -f "$PAPER_DIR/dark-matter-galaxy-rotation.tex" "$STAGE_DIR/paper/" 2>/dev/null || true
cp -f "$ROOT_DIR/Gravity-derived.pdf" "$STAGE_DIR/paper/" 2>/dev/null || true
cp -f "$ROOT_DIR/dark-matter-galaxy-rotation.pdf" "$STAGE_DIR/paper/" 2>/dev/null || true

# 2) Scripts
cp -f "$SCRIPTS_DIR/build_sparc_master_table.py" "$STAGE_DIR/scripts/" 2>/dev/null || true
cp -f "$SCRIPTS_DIR/plot_example_rc.py" "$STAGE_DIR/scripts/" 2>/dev/null || true
cp -f "$SCRIPTS_DIR/make_figs.sh" "$STAGE_DIR/scripts/" 2>/dev/null || true
cp -f "$SCRIPTS_DIR/ledger_final_combined.py" "$STAGE_DIR/scripts/" 2>/dev/null || true
cp -f "$SCRIPTS_DIR/reproduce_048_fit.py" "$STAGE_DIR/scripts/" 2>/dev/null || true
cp -f "$SCRIPTS_DIR/visualize_best_fits.py" "$STAGE_DIR/scripts/" 2>/dev/null || true

# 3) Minimal results/artifacts if present
cp -f "$RESULTS_DIR/sparc_master.pkl" "$STAGE_DIR/results/" 2>/dev/null || true
cp -f "$RESULTS_DIR/example_rc.pdf" "$STAGE_DIR/results/" 2>/dev/null || true

# 4) Top-level release README
cat > "$STAGE_DIR/README_RELEASE.md" << 'EOF'
# Gravity-Derived Release Bundle

Contents:
- paper/: LaTeX sources and any compiled PDFs present
- scripts/: Core scripts to rebuild master table and example figure
- results/: Minimal artifacts if available (sparc_master.pkl, example_rc.pdf)

Quickstart:
1. Create a Python environment (>=3.10) with numpy, pandas, matplotlib.
2. From scripts/, run:
   - `python build_sparc_master_table.py`
   - `python plot_example_rc.py` (emits ../results/example_rc.pdf)

Notes:
- SPARC rotmod data should be available at active/data/Rotmod_LTG (see repo README).
- For full figures/tables and baseline comparisons, see the repository and companion paper.
EOF

# 5) Compress
echo "[bundle] Creating archives..."
cd "$RELEASE_DIR"
zip -r "$BUNDLE_NAME.zip" "$BUNDLE_NAME" >/dev/null
tar -czf "$BUNDLE_NAME.tar.gz" "$BUNDLE_NAME"

echo "[bundle] Wrote:"
echo "  $RELEASE_DIR/$BUNDLE_NAME.zip"
echo "  $RELEASE_DIR/$BUNDLE_NAME.tar.gz"


