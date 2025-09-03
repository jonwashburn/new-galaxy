#!/usr/bin/env bash
set -euo pipefail

# Build features
python3 active/scripts/build_sparc_features.py --subset_csv results/bench_rs_per_galaxy.csv --out_root results/rs_features --nx 96 --ny 96 --box_factor_xy 8.0 --lambda_rec_kpc 0.5 --A 7.0 --p 1.6

# 64^3 full batch
python3 active/scripts/sparc_3d_proxy_runner.py --subset_csv results/bench_rs_per_galaxy.csv --limit 0 --anisotropic --nx 64 --ny 64 --nz 64 --features_root results/rs_features --out_dir results/ilg3d_sparc_aniso_64_all

# Figures
python3 active/scripts/plot_figures.py --out_dir results/ilg3d_sparc_aniso_64_all --limit 12 --fig_dir results/figures
