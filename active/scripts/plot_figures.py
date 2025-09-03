#!/usr/bin/env python3
"""
Plot residual maps (radial) and w(r) overlays from 3D proxy outputs.
- Reads per-galaxy CSVs <name>_3d_proxy.csv with columns: r_kpc, v_obs, v_err, v_baryon, K_ring, v_model
- Produces: results/figures/<name>_rc.png with v_obs (error bars), v_model, and K_ring overlay (secondary axis)
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import List

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt


def plot_one(csv_path: Path, out_dir: Path) -> None:
    name = csv_path.name.replace("_3d_proxy.csv", "")
    df = pd.read_csv(csv_path)
    if not {"r_kpc", "v_obs", "v_err", "v_baryon", "K_ring", "v_model"}.issubset(df.columns):
        return
    r = df["r_kpc"].to_numpy(float)
    v_obs = df["v_obs"].to_numpy(float)
    v_err = df["v_err"].to_numpy(float)
    v_bar = df["v_baryon"].to_numpy(float)
    K_ring = df["K_ring"].to_numpy(float)
    v_model = df["v_model"].to_numpy(float)

    fig, ax = plt.subplots(figsize=(6.4, 4.0), dpi=150)
    # Observed with errors
    ax.errorbar(r, v_obs, yerr=v_err, fmt="o", ms=3, lw=0.8, color="#555555", ecolor="#bbbbbb", label="v_obs")
    # Model
    ax.plot(r, v_model, "-", lw=1.4, color="#1f77b4", label="v_model")
    # Baryon
    ax.plot(r, v_bar, "--", lw=1.0, color="#2ca02c", alpha=0.8, label="v_baryon")
    ax.set_xlabel("r [kpc]")
    ax.set_ylabel("velocity [km/s]")
    ax.grid(True, alpha=0.25)
    ax.legend(loc="best", fontsize=8)
    # Secondary axis for K_ring (w(r))
    ax2 = ax.twinx()
    ax2.plot(r, K_ring, ":", lw=1.2, color="#d62728", alpha=0.9, label="w(r)=K_ring")
    ax2.set_ylabel("w(r)")
    # Compose legends
    lines, labels = ax.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax2.legend(lines + lines2, labels + labels2, loc="upper right", fontsize=8)
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"{name}_rc.png"
    fig.tight_layout()
    fig.savefig(out_path)
    plt.close(fig)


def main():
    ap = argparse.ArgumentParser(description="Plot residual and w(r) overlays")
    ap.add_argument("--out_dir", type=str, required=True, help="Directory with <name>_3d_proxy.csv files")
    ap.add_argument("--limit", type=int, default=12)
    ap.add_argument("--fig_dir", type=str, default="results/figures")
    args = ap.parse_args()
    out_dir = Path(args.out_dir)
    fig_dir = Path(args.fig_dir)
    count = 0
    for csv_path in sorted(out_dir.glob("*_3d_proxy.csv")):
        plot_one(csv_path, fig_dir)
        count += 1
        if args.limit and count >= args.limit:
            break
    print(f"Wrote {count} figures to {fig_dir}")


if __name__ == "__main__":
    main()


