#!/usr/bin/env python3
"""
Compute monotonic-trend checks for 3D ILG prototype outputs:
- Reads per-galaxy CSVs from an out_dir (e.g., results/ilg3d_sparc_aniso_64_all)
- Joins RS Feature Builder features.json (xi_bin, Rd_kpc)
- Recomputes sigma_eff and standardized residuals
- Reports median |resid| by xi_bin and by r/Rd bins
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import pandas as pd


SIGMA0 = 10.0
F_FRAC = 0.05
ALPHA_BEAM = 0.3
K_TURB = 0.07
P_TURB = 1.3
V_DWARF_MAX = 80.0


def sigma_eff_kms(r_kpc: np.ndarray, v_obs_kms: np.ndarray, v_err_kms: np.ndarray, R_d_kpc: float, dwarf: bool, b_kpc: float) -> np.ndarray:
    r = np.asarray(r_kpc, dtype=float)
    v = np.asarray(v_obs_kms, dtype=float)
    sigma_obs = np.asarray(v_err_kms, dtype=float)
    sigma_beam = ALPHA_BEAM * b_kpc * v / (r + b_kpc)
    sigma_asym = (0.10 if dwarf else 0.05) * v
    sigma_turb = K_TURB * v * np.power(1.0 - np.exp(-r / max(R_d_kpc, 1e-6)), P_TURB)
    sig2 = sigma_obs ** 2 + SIGMA0 ** 2 + (F_FRAC * v) ** 2 + sigma_beam ** 2 + sigma_asym ** 2 + sigma_turb ** 2
    return np.sqrt(np.maximum(sig2, 1e-12))


def main():
    ap = argparse.ArgumentParser(description="Compute monotonic trends (prototype)")
    ap.add_argument("--out_dir", type=str, required=True, help="Directory with per-galaxy CSVs <name>_3d_proxy.csv")
    ap.add_argument("--features_root", type=str, required=True, help="Root with per-galaxy features/<name>/features.json")
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    feats_root = Path(args.features_root)
    rows: List[Tuple[int, float]] = []  # (xi_bin, abs_resid)
    rows_r: List[Tuple[float, float]] = []  # (r_over_Rd, abs_resid)

    count = 0
    for csv_path in sorted(out_dir.glob("*_3d_proxy.csv")):
        name = csv_path.name.replace("_3d_proxy.csv", "")
        fjson = feats_root / name / "features.json"
        if not fjson.exists():
            continue
        meta = pd.read_json(fjson, typ="series").to_dict()
        R_d = float(meta.get("Rd_kpc", 2.0))
        xi_bin = int(meta.get("xi_bin", 2))
        df = pd.read_csv(csv_path)
        r = df["r_kpc"].to_numpy(float)
        v_obs = df["v_obs"].to_numpy(float)
        v_err = df["v_err"].to_numpy(float)
        v_model = df["v_model"].to_numpy(float)
        if r.size < 5:
            continue
        b_kpc = 0.3 * max(R_d, 1e-6)
        v_outer = np.nanmedian(v_obs[-3:]) if v_obs.size >= 3 else np.nanmax(v_obs)
        dwarf = bool(v_outer < V_DWARF_MAX)
        sigma_eff = sigma_eff_kms(r, v_obs, v_err, R_d, dwarf, b_kpc)
        mask = np.isfinite(v_model) & (r >= b_kpc)
        if not np.any(mask):
            continue
        resid = (v_obs[mask] - v_model[mask]) / np.maximum(sigma_eff[mask], 1e-9)
        abs_resid = np.abs(resid)
        r_over_Rd = r[mask] / max(R_d, 1e-9)
        for ar in abs_resid:
            rows.append((xi_bin, float(ar)))
        for rr, ar in zip(r_over_Rd, abs_resid):
            rows_r.append((float(rr), float(ar)))
        count += 1
        if args.limit and count >= args.limit:
            break

    if not rows:
        print("No data for trends.")
        return
    # Aggregate by xi_bin
    df_xi = pd.DataFrame(rows, columns=["xi_bin", "abs_resid"])  # xi_bin in [0..4]
    trend_xi = df_xi.groupby("xi_bin")["abs_resid"].median().sort_index()
    print("Median |resid| by xi_bin:")
    print(trend_xi.to_string())
    # Aggregate by r/Rd bins
    df_r = pd.DataFrame(rows_r, columns=["r_over_Rd", "abs_resid"])  # continuous
    bins = np.array([0.3, 1.0, 2.0, 3.0, np.inf])
    labels = ["0.3-1.0", "1.0-2.0", "2.0-3.0", ">3.0"]
    df_r["rbin"] = pd.cut(df_r["r_over_Rd"], bins=bins, labels=labels, right=False)
    trend_r = df_r.groupby("rbin")["abs_resid"].median().reindex(labels)
    print("Median |resid| by r/Rd bin:")
    print(trend_r.to_string())


if __name__ == "__main__":
    main()


