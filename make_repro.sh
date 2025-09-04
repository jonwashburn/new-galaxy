#!/usr/bin/env bash
set -euo pipefail

# One-click reproduction entry point (CPU by default).
# Expected runtime (CPU laptop): ~15–30 min for 1D, ~10–20 min for 2D subset, 3D demos vary by grid.

python3 -m pip install -r active/env/requirements.txt

# Build SPARC master (if not present)
if [ ! -f galaxy-rotation/results/sparc_master.pkl ]; then
  python3 active/scripts/build_sparc_master_table.py
fi

# 1D global-only main benchmark (blend)
python3 active/scripts/ilg_rotation_benchmark.py \
  --master galaxy-rotation/results/sparc_master.pkl \
  --subset_csv results/bench_rs_per_galaxy.csv --kernel blend \
  --out results/ilg_rotation_benchmark_blend_q1_zeta_truegas.csv

# 2D prototype (full Q=1) – can be long; uncomment if desired
# python3 active/scripts/sparc_2d_proxy_runner.py \
#   --subset_csv results/bench_rs_per_galaxy.csv --nx 128 --box_factor 8.0 \
#   --smooth_sigma_rel 0.2 --out_dir results/ilg2d_sparc_aniso

# 3D prototype demo (small subset)
python3 active/scripts/sparc_3d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv --limit 8 --anisotropic \
  --nx 64 --ny 64 --nz 64 --out_dir results/ilg3d_sparc_aniso_64_demo

# Imaging pilot demo (synthetic input already in repo generation step)
if [ -f results/imaging_pilot_input/pilot_input.csv ]; then
  python3 active/scripts/imaging_pilot.py \
    --input_csv results/imaging_pilot_input/pilot_input.csv \
    --out_dir results/imaging_pilot --deproject --quicklook
fi

echo "Repro run completed. Key outputs in results/."


