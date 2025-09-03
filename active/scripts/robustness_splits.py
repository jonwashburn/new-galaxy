#!/usr/bin/env python3
"""
Robustness splits and leave-one-out analysis for ILG blend results.

Inputs:
- results/ilg_rotation_benchmark_blend_q1_zeta_truegas.csv (per-galaxy chi2/N)

Outputs:
- results/robustness_splits.csv (by simple dwarf/spiral split via outer v_obs threshold)
- results/robustness_leave_one_out.csv (median without each galaxy)
"""

import argparse
from pathlib import Path
import numpy as np
import pandas as pd


V_DWARF_MAX = 80.0  # km/s


def main():
    ap = argparse.ArgumentParser(description="Compute robustness splits and LOO medians from ILG blend CSV")
    ap.add_argument("--ilg_blend_csv", type=str, default="results/ilg_rotation_benchmark_blend_q1_zeta_truegas.csv")
    ap.add_argument("--out_splits", type=str, default="results/robustness_splits.csv")
    ap.add_argument("--out_loo", type=str, default="results/robustness_leave_one_out.csv")
    args = ap.parse_args()

    df = pd.read_csv(args.ilg_blend_csv)
    # Expect columns: galaxy, N, chi2_over_N; optionally inject a naive dwarf/spiral label by name heuristic if absent
    # For now, classify dwarf/spiral using a name hint: galaxies starting with 'DDO', 'UGC0', 'CamB', 'D...' as dwarfs
    names = df["galaxy"].astype(str)
    dwarf_hint = names.str.contains(r"^(DDO|D\d|UGC0|CamB)")
    df["class"] = np.where(dwarf_hint, "dwarf", "spiral")

    rows = []
    for cls in ["all", "dwarf", "spiral"]:
        if cls == "all":
            sub = df
        else:
            sub = df[df["class"] == cls]
        if sub.empty:
            continue
        chi = sub["chi2_over_N"].to_numpy(float)
        rows.append({
            "split": cls,
            "N": int(sub.shape[0]),
            "median": float(np.nanmedian(chi)),
            "mean": float(np.nanmean(chi))
        })
    pd.DataFrame(rows).to_csv(args.out_splits, index=False)

    # Leave-one-out medians
    loo_rows = []
    chi_full = df["chi2_over_N"].to_numpy(float)
    full_median = float(np.nanmedian(chi_full))
    for i in range(df.shape[0]):
        chi = np.delete(chi_full, i)
        loo_rows.append({
            "removed": df.iloc[i]["galaxy"],
            "loo_median": float(np.nanmedian(chi))
        })
    loo_df = pd.DataFrame(loo_rows)
    loo_df.to_csv(args.out_loo, index=False)

    print(f"Full median = {full_median:.3f}")
    print(f"Wrote {args.out_splits}")
    print(f"Wrote {args.out_loo}")


if __name__ == "__main__":
    main()


