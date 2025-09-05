#!/usr/bin/env bash
set -euo pipefail

# Move to this script's directory
cd "$(dirname "$0")"

echo "[make_figs] Building SPARC master table..."
python build_sparc_master_table.py | cat

# Global-only ILG and MOND runs (optional quick summaries)
MASTER="../results/sparc_master.pkl"
if [[ -f "$MASTER" ]]; then
  echo "[make_figs] Running ILG benchmark (time kernel default)..."
  python ilg_rotation_benchmark.py --master "$MASTER" --out ../results/ilg_rotation_benchmark_time_q1.csv | cat || true
  echo "[make_figs] Running MOND baseline (simple nu)..."
  python mond_rotation_benchmark.py --master "$MASTER" --out ../results/mond_rotation_benchmark_q1.csv | cat || true
fi

# BTFR and RAR summaries
if [[ -f "$MASTER" ]]; then
  echo "[make_figs] Building BTFR summary..."
  python btfr_summary.py --master "$MASTER" --out ../results/btfr_summary.csv | cat || true
  echo "[make_figs] Building RAR summary..."
  python rar_summary.py --master "$MASTER" --out ../results/rar_summary.csv | cat || true
fi

# Example rotation curve
echo "[make_figs] Plotting example rotation curve..."
python plot_example_rc.py | cat || true

# Placeholder for residual diagnostics (emitted by ILG with --resid_diag_out when run)
if [[ -f ../results/resid_diag_summary.csv ]]; then
  echo "[make_figs] Residual diagnostics summary present: ../results/resid_diag_summary.csv"
fi

echo "[make_figs] Done. See ../results/ for generated artifacts."


