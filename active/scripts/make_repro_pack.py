#!/usr/bin/env python3
"""
Make a lightweight repro bundle:
- Writes repro/REPRO.md and repro/commands.sh with step-by-step commands
- Lists key artifact paths (without bundling large binaries)
"""

from __future__ import annotations

from pathlib import Path
import subprocess
import datetime as _dt


REPRO_MD = """
# Repro pack (global-only ILG/RS prototype)

This bundle lists exact commands and artifact paths to reproduce the reported results (Q=1 subset) without per‑galaxy tuning and without v_obs leakage.

## Environment

- Python 3.10+
- Requirements: `pip install -r active/env/requirements.txt`

## Data & features

1) Build per‑galaxy RS features (thresholds + fields.npz / features.json):

```
python3 active/scripts/build_sparc_features.py \
  --subset_csv results/bench_rs_per_galaxy.csv \
  --out_root results/rs_features \
  --nx 96 --ny 96 --box_factor_xy 8.0 \
  --lambda_rec_kpc 0.5 --A 7.0 --p 1.6
```

Artifacts:
- thresholds: `results/rs_features/thresholds.json`
- per‑galaxy: `results/rs_features/<name>/{fields.npz,features.json}`

## 3D kernel (anisotropic)

64^3 full Q=1 (uses features_root):

```
python3 active/scripts/sparc_3d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv --limit 0 --anisotropic \
  --nx 64 --ny 64 --nz 64 \
  --features_root results/rs_features \
  --out_dir results/ilg3d_sparc_aniso_64_all
```

96^3 spot (24 gal):

```
python3 active/scripts/sparc_3d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv --limit 24 --anisotropic \
  --nx 96 --ny 96 --nz 96 \
  --features_root results/rs_features \
  --out_dir results/ilg3d_sparc_aniso_96_24
```

## Lensing demo (mid‑plane proxies)

```
python3 active/scripts/sparc_3d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv --limit 4 --anisotropic \
  --nx 64 --ny 64 --nz 64 \
  --features_root results/rs_features \
  --out_dir results/ilg3d_lensing_demo
```

Artifacts: `results/ilg3d_lensing_demo/<name>_lensing_midplane.npz`

## Ablations (24 gal, 64^3)

```
# D->I
python3 active/scripts/sparc_3d_proxy_runner.py --subset_csv results/bench_rs_per_galaxy.csv \
  --limit 24 --anisotropic --nx 64 --ny 64 --nz 64 \
  --features_root results/rs_features --ablate_D_identity \
  --out_dir results/ilg3d_ablate_D_identity_64_24

# g_ext=0
python3 active/scripts/sparc_3d_proxy_runner.py --subset_csv results/bench_rs_per_galaxy.csv \
  --limit 24 --anisotropic --nx 64 --ny 64 --nz 64 \
  --features_root results/rs_features --ablate_gext0 \
  --out_dir results/ilg3d_ablate_gext0_64_24

# const-sigma
python3 active/scripts/sparc_3d_proxy_runner.py --subset_csv results/bench_rs_per_galaxy.csv \
  --limit 24 --anisotropic --nx 64 --ny 64 --nz 64 \
  --features_root results/rs_features --ablate_const_sigma \
  --out_dir results/ilg3d_ablate_const_sigma_64_24

# no inner mask
python3 active/scripts/sparc_3d_proxy_runner.py --subset_csv results/bench_rs_per_galaxy.csv \
  --limit 24 --anisotropic --nx 64 --ny 64 --nz 64 \
  --features_root results/rs_features --ablate_no_inner_mask \
  --out_dir results/ilg3d_ablate_no_inner_mask_64_24

# K=1 null
python3 active/scripts/sparc_3d_proxy_runner.py --subset_csv results/bench_rs_per_galaxy.csv \
  --limit 24 --anisotropic --nx 64 --ny 64 --nz 64 \
  --features_root results/rs_features --ablate_K1 \
  --out_dir results/ilg3d_ablate_K1_64_24
```

## Trend checks & figures

```
# Monotonic trends (xi_bin, r/Rd)
python3 active/scripts/compute_trends.py --out_dir results/ilg3d_sparc_aniso_64_all --features_root results/rs_features

# Figures (12 examples)
python3 active/scripts/plot_figures.py --out_dir results/ilg3d_sparc_aniso_64_all --limit 12 --fig_dir results/figures
```

## Key artifacts index

- Prototype summary: `active/results/PROTOTYPE_RESULTS.md`
- 64^3 full Q=1 summary: `results/ilg3d_sparc_aniso_64_all/summary.csv`
- 96^3 spot: `results/ilg3d_sparc_aniso_96_24/summary.csv`
- Ablations summaries: under `results/ilg3d_ablate_*/summary.csv`
- Lensing demo: `results/ilg3d_lensing_demo/`
- Features root: `results/rs_features/`

"""


def main():
    repro_dir = Path("repro")
    repro_dir.mkdir(parents=True, exist_ok=True)
    (repro_dir / "REPRO.md").write_text(REPRO_MD.strip() + "\n")
    # commands.sh mirrors the REPRO.md commands
    (repro_dir / "commands.sh").write_text("""#!/usr/bin/env bash
set -euo pipefail

# Build features
python3 active/scripts/build_sparc_features.py --subset_csv results/bench_rs_per_galaxy.csv --out_root results/rs_features --nx 96 --ny 96 --box_factor_xy 8.0 --lambda_rec_kpc 0.5 --A 7.0 --p 1.6

# 64^3 full batch
python3 active/scripts/sparc_3d_proxy_runner.py --subset_csv results/bench_rs_per_galaxy.csv --limit 0 --anisotropic --nx 64 --ny 64 --nz 64 --features_root results/rs_features --out_dir results/ilg3d_sparc_aniso_64_all

# Figures
python3 active/scripts/plot_figures.py --out_dir results/ilg3d_sparc_aniso_64_all --limit 12 --fig_dir results/figures
""".strip() + "\n")
    try:
        sha = subprocess.check_output(["git", "rev-parse", "HEAD"]).decode().strip()
    except Exception:
        sha = "(unknown)"
    (repro_dir / "COMMIT_SHA.txt").write_text(f"{sha}\nGenerated: {_dt.datetime.utcnow().isoformat()}Z\n")
    print(f"Wrote repro bundle files under {repro_dir}")


if __name__ == "__main__":
    main()


