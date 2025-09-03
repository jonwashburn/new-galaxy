#!/usr/bin/env python3
"""
Build a second global complexity proxy (xi2_proxy) from baryon-only inputs:
  xi2_proxy := disc-dominance ratio = <vdisk^2>_disc / <vbar^2>_disc

Weights use exp(-r/R_d) per galaxy. This file writes a CSV with two columns:
  galaxy, xi2_proxy

Usage:
  python3 active/scripts/make_xi2_from_master.py --out results/xi2_disc_dominance.csv
"""

from __future__ import annotations

import argparse
import pickle
from pathlib import Path
from typing import Dict, Any
import numpy as np
import pandas as pd


def get_master_path() -> Path:
    candidates = [
        Path("active/results/sparc_master.pkl"),
        Path("sparc_master.pkl"),
    ]
    for p in candidates:
        if p.exists():
            return p
    raise FileNotFoundError("No master table pickle found.")


def load_master(path: Path) -> Dict[str, Dict[str, Any]]:
    with open(path, "rb") as f:
        return pickle.load(f)


def main():
    ap = argparse.ArgumentParser(description="Make xi2 proxy from baryon-only inputs")
    ap.add_argument("--master", type=str, default="", help="Path to master table pickle")
    ap.add_argument("--out", type=str, default="results/xi2_disc_dominance.csv")
    args = ap.parse_args()

    path = Path(args.master) if args.master else get_master_path()
    master = load_master(path)

    rows = []
    for name, g in master.items():
        df = g.get("data")
        if df is None:
            r = np.asarray(g.get("r", []), dtype=float)
            v_gas = np.asarray(g.get("v_gas", []), dtype=float)
            v_disk = np.asarray(g.get("v_disk", []), dtype=float)
            v_bul = np.asarray(g.get("v_bul", []), dtype=float)
        else:
            r = df["rad"].to_numpy(float)
            v_gas = df["vgas"].to_numpy(float)
            v_disk = df["vdisk"].to_numpy(float)
            v_bul = df["vbul"].to_numpy(float)
        if r.size < 3:
            continue
        R_d = float(g.get("R_d", 2.0))
        w = np.exp(-np.asarray(r) / max(R_d, 1e-6))
        vbar2 = np.maximum(0.0, v_gas**2 + v_disk**2 + v_bul**2)
        num = float(np.sum(w * (v_disk**2)))
        den = float(np.sum(w * vbar2))
        xi2 = num / den if den > 0 else np.nan
        if np.isfinite(xi2):
            rows.append({"galaxy": name, "xi2_proxy": xi2})

    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    pd.DataFrame(rows).to_csv(outp, index=False)
    print(f"Wrote xi2 proxy for {len(rows)} galaxies to {outp}")


if __name__ == "__main__":
    main()


