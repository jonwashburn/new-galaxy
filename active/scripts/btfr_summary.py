#!/usr/bin/env python3
"""
Compute the Baryonic Tully-Fisher Relation (BTFR) under the global-only configuration.

Outputs:
- results/btfr_points_q1.csv  (per-galaxy: log10(M_b), log10(V_flat))
- results/btfr_summary.csv    (slope, intercept, scatter, N)

Mass inference tries (in order):
- explicit M_baryon-like keys: ['M_baryon','Mbaryon','M_b','M_baryon_Msun']
- constructed: M_star + 1.33*(M_HI + M_H2)
  using star keys in ['Mstar','M_star'] and gas keys ['MHI','M_HI','Mgas','M_gas','MH2','M_H2']

V_flat is taken as the median of the outermost 30% radii of v_obs after inner-beam masking r>=0.3 R_d.
"""

from __future__ import annotations

import argparse
import hashlib
import pickle
from pathlib import Path
from typing import Dict, Any, Optional, Set, Tuple

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


def try_get_mass(g: Dict[str, Any]) -> Optional[float]:
    # direct keys
    for k in ["M_baryon","Mbaryon","M_b","M_baryon_Msun"]:
        if k in g:
            try:
                val = float(g[k])
                if np.isfinite(val) and val > 0:
                    return val
            except Exception:
                pass
    # composed
    mstar = None
    for k in ["Mstar","M_star"]:
        if k in g:
            try:
                mstar = float(g[k])
                break
            except Exception:
                pass
    mhi = None
    for k in ["MHI","M_HI","Mgas","M_gas"]:
        if k in g:
            try:
                mhi = float(g[k])
                break
            except Exception:
                pass
    mh2 = None
    for k in ["MH2","M_H2"]:
        if k in g:
            try:
                mh2 = float(g[k])
                break
            except Exception:
                pass
    if mstar is not None or (mhi is not None or mh2 is not None):
        gas = (mhi or 0.0) + (mh2 or 0.0)
        mb = (mstar or 0.0) + 1.33 * gas
        if np.isfinite(mb) and mb > 0:
            return float(mb)
    return None


def compute_v_flat(r: np.ndarray, v_obs: np.ndarray, R_d: float) -> Optional[float]:
    r = np.asarray(r, dtype=float)
    v = np.asarray(v_obs, dtype=float)
    if r.size < 5:
        return None
    b_kpc = 0.3 * max(float(R_d), 1e-6)
    mask = r >= b_kpc
    r_m = r[mask]
    v_m = v[mask]
    if r_m.size < 5:
        return None
    # outer 30% by radius
    k = max(3, int(0.3 * r_m.size))
    idx = np.argsort(r_m)
    sel = idx[-k:]
    v_flat = float(np.nanmedian(v_m[sel]))
    return v_flat if np.isfinite(v_flat) and v_flat > 0 else None


def main():
    ap = argparse.ArgumentParser(description="Compute BTFR summaries from SPARC master table")
    ap.add_argument("--master", type=str, default=None, help="Path to master table pickle")
    ap.add_argument("--subset_csv", type=str, default="", help="Optional CSV with 'name' or 'galaxy' column to filter sample")
    ap.add_argument("--points_out", type=str, default="results/btfr_points_q1.csv", help="Per-galaxy output CSV")
    ap.add_argument("--summary_out", type=str, default="results/btfr_summary.csv", help="Summary output CSV")
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

    rows = []
    for name, g in master.items():
        mb = try_get_mass(g)
        if mb is None:
            continue
        df = g.get("data")
        if df is None:
            r = np.asarray(g.get("r", []), dtype=float)
            v_obs = np.asarray(g.get("v_obs", []), dtype=float)
        else:
            r = df["rad"].to_numpy(float)
            v_obs = df["vobs"].to_numpy(float)
        ok = (r > 0) & (v_obs > 0)
        r = r[ok]
        v_obs = v_obs[ok]
        if r.size < 5:
            continue
        R_d = float(g.get("R_d", 2.0))
        vflat = compute_v_flat(r, v_obs, R_d)
        if vflat is None:
            continue
        rows.append({
            "galaxy": name,
            "log10_Mb": float(np.log10(mb)),
            "log10_Vflat": float(np.log10(vflat))
        })

    if not rows:
        print("No BTFR points computed.")
        return

    points_df = pd.DataFrame(rows)
    points_path = Path(args.points_out)
    points_path.parent.mkdir(parents=True, exist_ok=True)
    points_df.to_csv(points_path, index=False)

    # Fit y = a x + b in log-space
    x = points_df["log10_Mb"].to_numpy(float)
    y = points_df["log10_Vflat"].to_numpy(float)
    a, b = np.polyfit(x, y, 1)
    yhat = a * x + b
    resid = y - yhat
    scatter = float(np.sqrt(np.nanmean(resid ** 2)))
    summary_df = pd.DataFrame([{"slope": float(a), "intercept": float(b), "scatter_rms": scatter, "N": int(points_df.shape[0])}])
    summary_path = Path(args.summary_out)
    summary_df.to_csv(summary_path, index=False)

    print(f"Wrote {points_path}")
    print(f"Wrote {summary_path}")


if __name__ == "__main__":
    main()


