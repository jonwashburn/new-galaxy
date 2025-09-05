#!/usr/bin/env python3
"""
Build a compact outlier autopsy table by merging the ILG outliers CSV and per-galaxy autopsy JSONs.

Inputs:
  --outliers_csv   Path to ILG outliers CSV (e.g., results/outliers_top10.csv)
  --autopsy_dir    Directory with per-galaxy JSONs (from --autopsy_dir)
  --out_csv        Output CSV path (e.g., results/outliers_autopsy_table.csv)

Output columns:
  galaxy, N, chi2_over_N, xi_u, R_d_kpc, resid_slope_r_over_Rd, max_abs_resid, where_max, dwarf
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, Any

import numpy as np
import pandas as pd


def main() -> None:
    ap = argparse.ArgumentParser(description="Build outlier autopsy table")
    ap.add_argument("--outliers_csv", type=str, required=True)
    ap.add_argument("--autopsy_dir", type=str, required=True)
    ap.add_argument("--out_csv", type=str, required=True)
    args = ap.parse_args()

    outliers = pd.read_csv(args.outliers_csv)
    outliers["galaxy"] = outliers["galaxy"].astype(str)
    aut_dir = Path(args.autopsy_dir)
    rows = []
    for _, row in outliers.iterrows():
        name = str(row["galaxy"]).replace("/", "_")
        p = aut_dir / f"{name}.json"
        rec: Dict[str, Any] = {
            "galaxy": str(row.get("galaxy")),
            "N": int(row.get("N", 0)),
            "chi2_over_N": float(row.get("chi2_over_N", np.nan)),
            "xi_u": np.nan,
            "R_d_kpc": np.nan,
            "resid_slope_r_over_Rd": np.nan,
            "max_abs_resid": np.nan,
            "where_max": "na",
            "dwarf": False,
        }
        try:
            if p.exists():
                data = json.loads(p.read_text())
                for k in rec.keys():
                    if k in data:
                        rec[k] = data[k]
        except Exception:
            pass
        rows.append(rec)

    if not rows:
        print("No outlier autopsies found.")
        return
    df = pd.DataFrame(rows)
    outp = Path(args.out_csv)
    outp.parent.mkdir(parents=True, exist_ok=True)
    df.to_csv(outp, index=False)
    print(f"Wrote autopsy table to {outp}")


if __name__ == "__main__":
    main()


