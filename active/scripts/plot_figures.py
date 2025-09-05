#!/usr/bin/env python3
"""
Plot residual maps (radial) and w(r) overlays from 3D proxy outputs.
- Reads per-galaxy CSVs <name>_3d_proxy.csv with columns: r_kpc, v_obs, v_err, v_baryon, K_ring, v_model
- Produces: results/figures/<name>_rc.png with v_obs (error bars), v_model, and K_ring overlay (secondary axis)
Also provides compact BTFR and RAR figure generation from summary CSVs.
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


def plot_btfr(btfr_csv: Path, out_png: Path) -> None:
    try:
        df = pd.read_csv(btfr_csv)
    except Exception:
        return
    # Expect columns with log10M_bary and log10Vflat (or similar). Fallback to generic names.
    cols = [c.lower() for c in df.columns]
    def col_like(key: str, default: str) -> str:
        for c in df.columns:
            if key in c.lower():
                return c
        return default
    xcol = col_like("logm", df.columns[0])
    ycol = col_like("logv", df.columns[1])
    fig, ax = plt.subplots(figsize=(4.2, 3.6), dpi=150)
    ax.scatter(df[xcol], df[ycol], s=10, alpha=0.6, color="#1f77b4")
    # simple OLS fit
    try:
        m, b = np.polyfit(df[xcol].to_numpy(float), df[ycol].to_numpy(float), 1)
        xs = np.linspace(df[xcol].min(), df[xcol].max(), 100)
        ax.plot(xs, m * xs + b, "-", lw=1.2, color="#d62728", alpha=0.9, label=f"fit: y={m:.2f}x+{b:.2f}")
        ax.legend(loc="best", fontsize=7)
    except Exception:
        pass
    ax.set_xlabel(xcol)
    ax.set_ylabel(ycol)
    ax.grid(True, alpha=0.25)
    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_png)
    plt.close(fig)


def plot_rar(rar_csv: Path, out_png: Path) -> None:
    try:
        df = pd.read_csv(rar_csv)
    except Exception:
        return
    # Expect columns gbar and gobs medians; fallback to first 2 numeric columns
    num_cols = [c for c in df.columns if np.issubdtype(df[c].dtype, np.number)]
    if len(num_cols) < 2:
        return
    x = df[num_cols[0]].to_numpy(float)
    y = df[num_cols[1]].to_numpy(float)
    fig, ax = plt.subplots(figsize=(4.2, 3.6), dpi=150)
    ax.scatter(x, y, s=10, alpha=0.6, color="#2ca02c")
    # 1:1 line and guide lines
    lo = max(np.nanmin(x), np.nanmin(y))
    hi = min(np.nanmax(x), np.nanmax(y))
    if np.isfinite(lo) and np.isfinite(hi):
        xs = np.linspace(lo, hi, 100)
        ax.plot(xs, xs, "--", lw=1.0, color="#888888", alpha=0.8)
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlabel(num_cols[0])
    ax.set_ylabel(num_cols[1])
    ax.grid(True, which="both", ls=":", alpha=0.3)
    out_png.parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(out_png)
    plt.close(fig)


def main():
    ap = argparse.ArgumentParser(description="Plot residual and w(r) overlays, plus compact BTFR and RAR figures")
    ap.add_argument("--out_dir", type=str, required=False, default="", help="Directory with <name>_3d_proxy.csv files")
    ap.add_argument("--limit", type=int, default=12)
    ap.add_argument("--fig_dir", type=str, default="results/figures")
    ap.add_argument("--btfr_csv", type=str, default="results/btfr_summary.csv")
    ap.add_argument("--rar_csv", type=str, default="results/rar_summary.csv")
    args = ap.parse_args()
    fig_dir = Path(args.fig_dir)

    # Per-galaxy residual/overlay plots
    if args.out_dir:
        out_dir = Path(args.out_dir)
        count = 0
        for csv_path in sorted(out_dir.glob("*_3d_proxy.csv")):
            plot_one(csv_path, fig_dir)
            count += 1
            if args.limit and count >= args.limit:
                break
        print(f"Wrote {count} RC figures to {fig_dir}")

    # Compact BTFR and RAR figures
    plot_btfr(Path(args.btfr_csv), fig_dir / "btfr_compact.png")
    plot_rar(Path(args.rar_csv), fig_dir / "rar_compact.png")
    print(f"Wrote BTFR/RAR figures to {fig_dir}")


if __name__ == "__main__":
    main()


