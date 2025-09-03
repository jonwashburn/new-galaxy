#!/usr/bin/env python3
"""
Compute the Radial Acceleration Relation (RAR) under the global-only ILG configuration.

Outputs:
- results/rar_points_q1.csv   (per-point pairs: g_bar, g_obs)
- results/rar_summary.csv     (binned summary: bin_left, bin_right, gobs_median, gobs_p16, gobs_p84, count)

Uses the same inputs and masks as the ILG benchmark: inner-beam b_kpc = 0.3 R_d, and the Q=1 subset if provided.
Note: RAR compares observed acceleration g_obs against baryonic acceleration g_bar; it does not depend on ILG weights.
"""

from __future__ import annotations

import argparse
import hashlib
import pickle
from pathlib import Path
from typing import Dict, Any, Optional, Set

import numpy as np
import pandas as pd


def load_master_table(path: Path) -> Dict[str, Dict[str, Any]]:
    with open(path, "rb") as f:
        return pickle.load(f)


def load_subset_names(path: Optional[str]) -> Optional[Set[str]]:
    if not path:
        return None
    try:
        df = pd.read_csv(path)
        if "name" in df.columns:
            names = set(map(str, df["name"].astype(str).tolist()))
        elif "galaxy" in df.columns:
            names = set(map(str, df["galaxy"].astype(str).tolist()))
        else:
            return None
        return names
    except Exception:
        return None


def baryonic_speed(v_gas: np.ndarray, v_disk: np.ndarray, v_bul: np.ndarray, upsilon_star: float = 1.0) -> np.ndarray:
    return np.sqrt(np.maximum(0.0, v_gas ** 2 + (np.sqrt(upsilon_star) * v_disk) ** 2 + v_bul ** 2))


def g_bar_ms2(v_bar_kms: np.ndarray, r_kpc: np.ndarray) -> np.ndarray:
    v2_m2s2 = (v_bar_kms ** 2) * (1000.0 ** 2)
    r_m = np.asarray(r_kpc, dtype=float) * 3.086e19
    r_m = np.where(r_m > 0.0, r_m, np.nan)
    return v2_m2s2 / r_m


def g_obs_ms2(v_obs_kms: np.ndarray, r_kpc: np.ndarray) -> np.ndarray:
    v2_m2s2 = (v_obs_kms ** 2) * (1000.0 ** 2)
    r_m = np.asarray(r_kpc, dtype=float) * 3.086e19
    r_m = np.where(r_m > 0.0, r_m, np.nan)
    return v2_m2s2 / r_m


def main():
    ap = argparse.ArgumentParser(description="Compute RAR summaries from SPARC master table")
    ap.add_argument("--master", type=str, default=None, help="Path to master table pickle")
    ap.add_argument("--subset_csv", type=str, default="", help="Optional CSV with 'name' or 'galaxy' column to filter sample")
    ap.add_argument("--ml_disk", type=float, default=1.0, help="Global stellar M/L (default 1.0)")
    ap.add_argument("--points_out", type=str, default="results/rar_points_q1.csv", help="Per-point output CSV")
    ap.add_argument("--summary_out", type=str, default="results/rar_summary.csv", help="Binned summary output CSV")
    args = ap.parse_args()

    # Resolve master
    if args.master is None:
        candidates = [Path("active/results/sparc_master.pkl"), Path("sparc_master.pkl"), Path("galaxy-rotation/results/sparc_master.pkl")]
        path = None
        for p in candidates:
            if p.exists():
                path = p
                break
        if path is None:
            raise FileNotFoundError("No master table found in default locations.")
    else:
        path = Path(args.master)

    raw_bytes = Path(path).read_bytes()
    sha = hashlib.sha256(raw_bytes).hexdigest()
    master = load_master_table(path)
    print(f"INPUT {path} sha256={sha} entries={len(master)}")

    # Optional subset
    subset_names = load_subset_names(args.subset_csv)
    if subset_names:
        master = {k: v for k, v in master.items() if str(k) in subset_names}

    # Accumulate pairs
    gbar_all: list[float] = []
    gobs_all: list[float] = []
    for name, g in master.items():
        df = g.get("data")
        if df is None:
            r = np.asarray(g.get("r", []), dtype=float)
            v_obs = np.asarray(g.get("v_obs", []), dtype=float)
            v_gas = np.asarray(g.get("v_gas", []), dtype=float) if "v_gas" in g else np.zeros_like(r)
            v_disk = np.asarray(g.get("v_disk", []), dtype=float) if "v_disk" in g else np.zeros_like(r)
            v_bul = np.asarray(g.get("v_bul", []), dtype=float) if "v_bul" in g else np.zeros_like(r)
        else:
            r = df["rad"].to_numpy(float)
            v_obs = df["vobs"].to_numpy(float)
            v_gas = df["vgas"].to_numpy(float)
            v_disk = df["vdisk"].to_numpy(float)
            v_bul = df["vbul"].to_numpy(float)

        ok = (r > 0) & (v_obs > 0)
        r = r[ok]
        v_obs = v_obs[ok]
        v_gas = v_gas[ok]
        v_disk = v_disk[ok]
        v_bul = v_bul[ok]
        if r.size < 3:
            continue

        R_d = float(g.get("R_d", 2.0))
        b_kpc = 0.3 * max(R_d, 1e-6)

        v_bar = baryonic_speed(v_gas, v_disk, v_bul, upsilon_star=args.ml_disk)
        gobsi = g_obs_ms2(v_obs, r)
        gbari = g_bar_ms2(v_bar, r)

        mask = (r >= b_kpc) & np.isfinite(gobsi) & np.isfinite(gbari)
        gbar_all.extend(gbari[mask].tolist())
        gobs_all.extend(gobsi[mask].tolist())

    # Write per-point CSV
    points_df = pd.DataFrame({"g_bar": gbar_all, "g_obs": gobs_all})
    points_path = Path(args.points_out)
    points_path.parent.mkdir(parents=True, exist_ok=True)
    points_df.to_csv(points_path, index=False)

    # Binned summary in log10 g_bar
    x = np.log10(np.clip(points_df["g_bar"].to_numpy(float), 1e-30, None))
    y = np.log10(np.clip(points_df["g_obs"].to_numpy(float), 1e-30, None))
    bins = np.linspace(-13.5, -8.5, 26)  # 0.2 dex bins across typical SPARC range
    idx = np.digitize(x, bins, right=False)
    rows = []
    for b in range(1, len(bins)):
        sel = (idx == b)
        if not np.any(sel):
            continue
        yb = y[sel]
        rows.append({
            "bin_left": bins[b-1],
            "bin_right": bins[b],
            "gobs_median": float(np.nanmedian(yb)),
            "gobs_p16": float(np.nanpercentile(yb, 16)),
            "gobs_p84": float(np.nanpercentile(yb, 84)),
            "count": int(np.sum(sel))
        })
    summary_df = pd.DataFrame(rows)
    summary_path = Path(args.summary_out)
    summary_df.to_csv(summary_path, index=False)

    print(f"Wrote {points_path}")
    print(f"Wrote {summary_path}")


if __name__ == "__main__":
    main()


