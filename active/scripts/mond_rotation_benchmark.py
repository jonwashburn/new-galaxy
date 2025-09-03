#!/usr/bin/env python3
"""
MOND rotation-curve benchmark (global-only, no per-galaxy tuning)

Fair baseline to compare with ILG under identical masks and error model.

Model:
  v_model(r) = sqrt( w_mond(r) ) * v_bar(r)
  w_mond(r)  = nu(y),  y = g_bar(r)/a0,  g_bar = v_bar^2 / r

We use the simple QUMOND interpolation: nu(y) = 0.5 + sqrt(0.25 + 1/y).

Error model and inner-beam mask match the ILG benchmark exactly.
"""

from __future__ import annotations

import argparse
import hashlib
import pickle
from pathlib import Path
from typing import Dict, Any, Optional, Tuple, Set

import numpy as np
import pandas as pd


A0 = 1.2e-10  # m s^-2

# error model (identical to ILG script)
SIGMA0 = 10.0  # km/s
F_FRAC = 0.05
ALPHA_BEAM = 0.3
K_TURB = 0.07
P_TURB = 1.3

# dwarf/spiral classification threshold (km/s)
V_DWARF_MAX = 80.0


def load_master_table(path: Path) -> Dict[str, Dict[str, Any]]:
    with open(path, "rb") as f:
        return pickle.load(f)


def baryonic_speed(v_gas: np.ndarray, v_disk: np.ndarray, v_bul: np.ndarray, upsilon_star: float = 1.0) -> np.ndarray:
    return np.sqrt(np.maximum(0.0, v_gas ** 2 + (np.sqrt(upsilon_star) * v_disk) ** 2 + v_bul ** 2))


def g_bar_ms2(v_bar_kms: np.ndarray, r_kpc: np.ndarray) -> np.ndarray:
    v2_m2s2 = (v_bar_kms ** 2) * (1000.0 ** 2)
    r_m = np.asarray(r_kpc, dtype=float) * 3.086e19
    r_m = np.where(r_m > 0.0, r_m, np.nan)
    return v2_m2s2 / r_m


def nu_simple(y: np.ndarray) -> np.ndarray:
    y = np.asarray(y, dtype=float)
    y = np.maximum(y, 1e-300)
    return 0.5 + np.sqrt(0.25 + 1.0 / y)


def sigma_eff_kms(
    r_kpc: np.ndarray,
    v_obs_kms: np.ndarray,
    v_err_kms: Optional[np.ndarray],
    R_d_kpc: float,
    dwarf: bool,
    b_kpc: float | None = None,
) -> np.ndarray:
    r = np.asarray(r_kpc, dtype=float)
    v = np.asarray(v_obs_kms, dtype=float)
    sigma_obs = np.asarray(v_err_kms, dtype=float) if v_err_kms is not None else np.zeros_like(v)
    if b_kpc is None:
        b_kpc = 0.3 * max(R_d_kpc, 1e-6)
    sigma_beam = ALPHA_BEAM * b_kpc * v / (r + b_kpc)
    sigma_asym = (0.10 if dwarf else 0.05) * v
    sigma_turb = K_TURB * v * np.power(1.0 - np.exp(-r / max(R_d_kpc, 1e-6)), P_TURB)
    sig2 = (
        sigma_obs ** 2
        + SIGMA0 ** 2
        + (F_FRAC * v) ** 2
        + sigma_beam ** 2
        + sigma_asym ** 2
        + sigma_turb ** 2
    )
    return np.sqrt(np.maximum(sig2, 1e-12))


def reduced_chi2(
    v_obs: np.ndarray,
    v_model: np.ndarray,
    sigma_eff: np.ndarray,
    r_kpc: np.ndarray,
    b_kpc: float,
) -> Tuple[float, int]:
    mask = r_kpc >= b_kpc
    v_o = v_obs[mask]
    v_m = v_model[mask]
    s = sigma_eff[mask]
    N = int(np.sum(mask))
    if N <= 1:
        return np.nan, 0
    chi2 = np.sum(((v_o - v_m) / s) ** 2)
    return float(chi2 / N), N


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


def main():
    ap = argparse.ArgumentParser(description="MOND rotation benchmark (global-only)")
    ap.add_argument("--master", type=str, default=None, help="Path to master table pickle")
    ap.add_argument("--ml_disk", type=float, default=1.0, help="Global stellar M/L (default 1.0)")
    ap.add_argument("--out", type=str, default="results/mond_rotation_benchmark.csv", help="Output CSV path")
    ap.add_argument("--subset_csv", type=str, default="", help="Optional CSV with 'name' or 'galaxy' column to filter sample")
    ap.add_argument("--assert_n", type=int, default=0, help="If >0, assert evaluated galaxy count equals this value")
    args = ap.parse_args()

    # Resolve master path
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
    chi2_list = []
    keys = list(master.keys())
    for name in keys:
        g = master[name]
        df = g.get("data")
        if df is None:
            r = np.asarray(g.get("r", []), dtype=float)
            v_obs = np.asarray(g.get("v_obs", []), dtype=float)
            v_gas = np.asarray(g.get("v_gas", []), dtype=float) if "v_gas" in g else np.zeros_like(r)
            v_disk = np.asarray(g.get("v_disk", []), dtype=float) if "v_disk" in g else np.zeros_like(r)
            v_bul = np.asarray(g.get("v_bul", []), dtype=float) if "v_bul" in g else np.zeros_like(r)
            v_err = None
        else:
            r = df["rad"].to_numpy(float)
            v_obs = df["vobs"].to_numpy(float)
            v_err = df["verr"].to_numpy(float)
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
        gbar = g_bar_ms2(v_bar, r)
        y = gbar / A0
        w_mond = nu_simple(y)
        v_model = np.sqrt(np.maximum(1e-12, w_mond)) * v_bar

        v_outer = np.nanmedian(v_obs[-3:]) if v_obs.size >= 3 else np.nanmax(v_obs)
        dwarf = bool(v_outer < V_DWARF_MAX)
        sigma_eff = sigma_eff_kms(r, v_obs, v_err, R_d_kpc=R_d, dwarf=dwarf, b_kpc=b_kpc)
        red_chi2, N = reduced_chi2(v_obs, v_model, sigma_eff, r, b_kpc)
        if np.isfinite(red_chi2) and N > 0:
            chi2_list.append(red_chi2)
            rows.append({"galaxy": name, "N": N, "chi2_over_N": red_chi2})

    if not rows:
        print("No galaxies evaluated.")
        return

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    pd.DataFrame(rows).to_csv(out_path, index=False)

    chi2_arr = np.array(chi2_list, dtype=float)
    print(f"Evaluated {chi2_arr.size} galaxies (MOND simple-nu)")
    if args.assert_n and chi2_arr.size != args.assert_n:
        raise SystemExit(f"assert_n failed: got {chi2_arr.size}, expected {args.assert_n}")
    print(f"Median chi^2/N = {np.nanmedian(chi2_arr):.3f}")
    print(f"Mean   chi^2/N = {np.nanmean(chi2_arr):.3f}")
    print(f"Results written to {out_path}")


if __name__ == "__main__":
    main()


