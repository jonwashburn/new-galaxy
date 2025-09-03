#!/usr/bin/env python3
"""
Global-only ILG sweep: explore small grids of hyperparameters without per-galaxy tuning.

Parameters swept (small, safe ranges):
  - kernel in {accel, time, blend}
  - zeta_on in {True, False}
  - ml_disk in {0.8, 1.0, 1.2}
  - gext_ratio in {0.0, 0.02, 0.05}  # units of a0

Optional CSVs (global-only): env_csv/env_weights, xi2_csv, s0_csv as supported by ilg_rotation_benchmark.py

Outputs:
  - results/ilg_sweep_global.csv with rows per config and med/mean chi2/N.
  - prints best configuration by median chi2/N.
"""

from __future__ import annotations

import argparse
import itertools
import json
import subprocess
from pathlib import Path
import pandas as pd


def run_cfg(args, kernel: str, zeta_on: bool, ml: float, gext_ratio: float) -> dict:
    cmd = [
        "python3", "active/scripts/ilg_rotation_benchmark.py",
        "--subset_csv", args.subset_csv,
        "--kernel", kernel,
        "--ml_disk", str(ml),
        "--gext_ratio", str(gext_ratio),
        "--out", "results/.tmp_ilg_sweep.csv",
        "--assert_n", str(args.assert_n or 0),
    ]
    if zeta_on is False:
        cmd.append("--zeta_off")
    # Optional global-only inputs
    if args.env_csv:
        cmd += ["--env_csv", args.env_csv]
    if args.env_weights:
        cmd += ["--env_weights", args.env_weights]
    if args.xi2_csv:
        cmd += ["--xi2_csv", args.xi2_csv, "--xi2_bins", str(args.xi2_bins)]
    if args.s0_csv:
        cmd += ["--s0_csv", args.s0_csv, "--s0_bins", str(args.s0_bins)]

    try:
        out = subprocess.check_output(cmd, stderr=subprocess.STDOUT, text=True)
    except subprocess.CalledProcessError as e:
        return {"kernel": kernel, "zeta_on": zeta_on, "ml_disk": ml, "gext_ratio": gext_ratio,
                "median": float("nan"), "mean": float("nan"), "status": f"error: {e.output[:200]}"}

    med = float("nan"); mean = float("nan")
    for line in out.splitlines():
        if line.strip().startswith("Median chi^2/N"):
            try:
                med = float(line.strip().split("=")[-1])
            except Exception:
                pass
        if line.strip().startswith("Mean   chi^2/N"):
            try:
                mean = float(line.strip().split("=")[-1])
            except Exception:
                pass
    return {"kernel": kernel, "zeta_on": zeta_on, "ml_disk": ml, "gext_ratio": gext_ratio,
            "median": med, "mean": mean, "status": "ok"}


def main():
    ap = argparse.ArgumentParser(description="Global-only ILG sweep")
    ap.add_argument("--subset_csv", type=str, default="results/bench_rs_per_galaxy.csv")
    ap.add_argument("--assert_n", type=int, default=156)
    ap.add_argument("--env_csv", type=str, default="")
    ap.add_argument("--env_weights", type=str, default="")
    ap.add_argument("--xi2_csv", type=str, default="")
    ap.add_argument("--xi2_bins", type=int, default=5)
    ap.add_argument("--s0_csv", type=str, default="")
    ap.add_argument("--s0_bins", type=int, default=3)
    ap.add_argument("--out", type=str, default="results/ilg_sweep_global.csv")
    args = ap.parse_args()

    kernels = ["accel", "time", "blend"]
    zetas = [True, False]
    mls = [0.8, 1.0, 1.2]
    gexts = [0.0, 0.02, 0.05]

    rows = []
    for (k, z, ml, gx) in itertools.product(kernels, zetas, mls, gexts):
        row = run_cfg(args, k, z, ml, gx)
        print(f"{row}")
        rows.append(row)

    df = pd.DataFrame(rows)
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    df.to_csv(args.out, index=False)
    # pick best by median
    best = df.sort_values(["median", "mean"]).iloc[0]
    print("Best config (by median):")
    print(json.dumps({"kernel": best["kernel"], "zeta_on": bool(best["zeta_on"]),
                      "ml_disk": float(best["ml_disk"]), "gext_ratio": float(best["gext_ratio"]),
                      "median": float(best["median"]), "mean": float(best["mean"])}, indent=2))


if __name__ == "__main__":
    main()


