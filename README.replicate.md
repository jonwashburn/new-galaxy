# Replication Guide (ILG rotation benchmarks)

## Environment

- Python 3.11+
- `pip install -r active/env/requirements.txt`

## Data

We assume the master table at `galaxy-rotation/results/sparc_master.pkl` (SHA256: `0bd5372c6be9c2c10543d67056ecfc1fbbc142615815614edd73e716f86844d9`) and the Q=1 list at `results/bench_rs_per_galaxy.csv` (156 names).

## Commands

1) ILG kernel sweep (Q=1):

```
python active/scripts/ilg_rotation_benchmark.py --master galaxy-rotation/results/sparc_master.pkl --subset_csv results/bench_rs_per_galaxy.csv --kernel accel --out results/ilg_rotation_benchmark_accel_q1.csv
python active/scripts/ilg_rotation_benchmark.py --master galaxy-rotation/results/sparc_master.pkl --subset_csv results/bench_rs_per_galaxy.csv --kernel time  --out results/ilg_rotation_benchmark_time_q1.csv
python active/scripts/ilg_rotation_benchmark.py --master galaxy-rotation/results/sparc_master.pkl --subset_csv results/bench_rs_per_galaxy.csv --kernel blend --out results/ilg_rotation_benchmark_blend_q1_zeta_truegas.csv
```

2) MOND baseline (Q=1):

```
python active/scripts/mond_rotation_benchmark.py --master galaxy-rotation/results/sparc_master.pkl --subset_csv results/bench_rs_per_galaxy.csv --out results/mond_rotation_benchmark_q1.csv
```

3) RAR/BTFR summaries:

```
python active/scripts/rar_summary.py  --master galaxy-rotation/results/sparc_master.pkl --subset_csv results/bench_rs_per_galaxy.csv --points_out results/rar_points_q1.csv  --summary_out results/rar_summary.csv
python active/scripts/btfr_summary.py --master galaxy-rotation/results/sparc_master.pkl --subset_csv results/bench_rs_per_galaxy.csv --points_out results/btfr_points_q1.csv --summary_out results/btfr_summary.csv
```

4) Ablations and sensitivity (optional):

```
python active/scripts/ilg_rotation_benchmark.py --master galaxy-rotation/results/sparc_master.pkl --subset_csv results/bench_rs_per_galaxy.csv --kernel blend --zeta_off   --out results/ilg_rotation_benchmark_blend_q1_zetaoff.csv
python active/scripts/ilg_rotation_benchmark.py --master galaxy-rotation/results/sparc_master.pkl --subset_csv results/bench_rs_per_galaxy.csv --kernel blend --gext_ratio 0.05 --out results/ilg_rotation_benchmark_blend_q1_gext005.csv
```

5) Example plot:

```
python active/scripts/plot_example_rc.py --master galaxy-rotation/results/sparc_master.pkl --galaxy NGC7331 --out results/rc_NGC7331.png --kernel blend
```

## CI

A GitHub Actions workflow (`.github/workflows/ci-benchmark.yml`) runs the benchmarks and uploads artifacts on push.

## Lean build (optional)

Install elan (Lean toolchain manager), then:

```
elan default leanprover/lean4:v4.12.0
lake update
lake build
```

This builds the Lean library (`ILG`). A future CI job will verify Lean builds cleanly.
