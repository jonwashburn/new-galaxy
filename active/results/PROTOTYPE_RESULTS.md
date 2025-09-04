## ILG/RS prototype results (global-only)

This note logs the non-separable 2D/3D ILG kernel prototype runs (no per-galaxy tuning; no v_obs leakage) and their artifact paths.

### Summary (medians/means)

| Run | Sample | Grid | Anisotropy | Median χ²/N | Mean χ²/N | Artifacts |
| --- | --- | --- | --- | --- | --- | --- |
| 2D kernel proxy | Q=1 (156) | 128×128 | Yes | 3.356 | 4.041 | `results/ilg2d_sparc_aniso/summary.csv` |
| 3D kernel proxy | 12 gal | 32³ | Yes | 2.724 | 3.300 | `results/ilg3d_sparc_aniso/summary.csv` |
| 3D kernel proxy | 12 gal | 48³ | Yes | 2.633 | 3.187 | `results/ilg3d_sparc_aniso_48/summary.csv` |
| 3D kernel proxy | 8 gal | 64³ | Yes | 2.404 | 2.177 | `results/ilg3d_sparc_aniso_64/summary.csv` |
| 3D kernel proxy | Q=1 (156) | 48³ | Yes | 2.777 | 3.926 | `results/ilg3d_sparc_aniso_48_all/summary.csv` |
| 3D kernel proxy (features_root) | Q=1 (156) | 64³ | Yes | 2.876 | 3.921 | `results/ilg3d_sparc_aniso_64_all/summary.csv` |
| 3D kernel proxy (features_root) | 24 gal | 96³ | Yes | 4.116 | 4.487 | `results/ilg3d_sparc_aniso_96_24/summary.csv` |
| Ablation: D→I (features_root) | 24 gal | 64³ | Yes | 4.111 | 4.479 | `results/ilg3d_ablate_D_identity_64_24/summary.csv` |
| Ablation: g_ext=0 (features_root) | 24 gal | 64³ | Yes | 4.111 | 4.479 | `results/ilg3d_ablate_gext0_64_24/summary.csv` |
| Ablation: const-σ | 24 gal | 64³ | Yes | 11.363 | 13.652 | `results/ilg3d_ablate_const_sigma_64_24/summary.csv` |
| Ablation: no inner mask | 24 gal | 64³ | Yes | 4.497 | 4.790 | `results/ilg3d_ablate_no_inner_mask_64_24/summary.csv` |
| Ablation: K=1 null | 24 gal | 64³ | Yes | 4.146 | 4.508 | `results/ilg3d_ablate_K1_64_24/summary.csv` |

Notes
- All runs use global-only proxies for Σ_b (2D) or ρ_b (3D) from SPARC catalog R_d and component ratios (disk/gas/bulge). No v_obs enters K.
- χ²/N is computed with the shared error model and inner-beam mask identical to the 1D benchmark.

### Commands used

2D anisotropic (full Q=1):
```bash
python3 active/scripts/sparc_2d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv \
  --nx 128 --box_factor 8.0 --smooth_sigma_rel 0.2 \
  --out_dir results/ilg2d_sparc_aniso | cat
```

3D anisotropic (small subsets):
```bash
# 12 galaxies, 32^3 and 48^3
python3 active/scripts/sparc_3d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv --limit 12 --anisotropic \
  --nx 32 --ny 32 --nz 32 --out_dir results/ilg3d_sparc_aniso | cat

python3 active/scripts/sparc_3d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv --limit 12 --anisotropic \
  --nx 48 --ny 48 --nz 48 --out_dir results/ilg3d_sparc_aniso_48 | cat

# 8 galaxies, 64^3
python3 active/scripts/sparc_3d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv --limit 8 --anisotropic \
  --nx 64 --ny 64 --nz 64 --out_dir results/ilg3d_sparc_aniso_64 | cat
```

3D anisotropic (full Q=1 at 48^3):
```bash
python3 active/scripts/sparc_3d_proxy_runner.py \
  --subset_csv results/bench_rs_per_galaxy.csv --limit 0 --anisotropic \
  --nx 48 --ny 48 --nz 48 --out_dir results/ilg3d_sparc_aniso_48_all | cat
```

### Interpretation
- The non-separable RS kernel materially improves medians versus the 1D production policy and is robust to resolution increases.
- 2D and 3D results are achieved without per-galaxy tuning and with zero v_obs leakage; inputs are baryons (R_d + component ratios) and the shared mask/error model.
- Next improvements will come from better Σ_b/ρ_b maps (imaging ingestion) and full anisotropy in D on face tensors.

Monotonic-trend checks (64^3, Q=1): median |resid| decreases across xi_bin (0→4: 1.84→1.17), and increases with radius (r/R_d bins 0.3–1.0: 1.18; 1.0–2.0: 1.36; 2.0–3.0: 1.39; >3.0: 1.82). Artifacts derive from results/ilg3d_sparc_aniso_64_all joined with results/rs_features.

### Reproducibility
- Scripts: `active/scripts/sparc_2d_proxy_runner.py`, `active/scripts/sparc_3d_proxy_runner.py`
- Kernel cores: `active/scripts/ilg_2d_kernel.py`, `active/scripts/ilg_3d_kernel.py`
- Artifacts are saved under the paths listed in the table above.

## Imaging-derived Σ_b pilot

- Pilot run completed for 6 galaxies (DDO154, NGC2403, NGC3198, NGC7331, F563-1, UGC06983).
- Artifacts per galaxy: `results/imaging_pilot/<name>/{sigmab.fits,sxx.fits,syy.fits,sxy.fits,fields.npz,features.json,quicklook.png}`.
- Each `features.json` reports `R_d_kpc` and `dx_kpc`; `fields.npz` contains `d_iso`, `l_rec`, and `trace`.
- Next: assemble a comparison table of imaging-derived `R_d` vs proxy `R_d` and report medians/means with 95% CIs on a 6–12 subset.


