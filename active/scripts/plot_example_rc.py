#!/usr/bin/env python3
"""
Plot SPARC rotation curves with ILG model overlay for specified galaxies.

Usage:
  python active/scripts/plot_example_rc.py --master PATH --galaxy NAME --out PATH --kernel blend

Inputs:
- sparc_master.pkl (processed master table)

Output:
- PNG or PDF figure at --out
"""

from __future__ import annotations

import os, sys, math, pickle
from pathlib import Path
from typing import Dict, Any, Optional
import argparse

import numpy as np
import matplotlib.pyplot as plt


SECONDS_PER_YEAR = 365.25 * 24.0 * 3600.0


def find_master_table(project_root: Path) -> Optional[Path]:
    """Locate sparc_master.pkl in common locations."""
    candidates = [
        project_root / "active" / "results" / "sparc_master.pkl",
        project_root / "sparc_master.pkl",
    ]
    for p in candidates:
        if p.exists():
            return p
    return None


def n_analytic(r_kpc: np.ndarray, A: float = 7.0, r0_kpc: float = 8.0, p: float = 1.6) -> np.ndarray:
    return 1.0 + A * (1.0 - np.exp(-np.power(np.maximum(r_kpc, 0.0) / r0_kpc, p)))


def xi_from_quintile(u_center: float, C_LAG: float) -> float:
    # ξ = 1 + φ^{-5} * u_b^{1/2}
    return 1.0 + C_LAG * math.sqrt(max(0.0, min(1.0, u_center)))


def phi() -> float:
    return (1.0 + math.sqrt(5.0)) / 2.0

PHI = phi()
ALPHA = 0.5 * (1.0 - 1.0 / PHI)
C_LAG = PHI ** (-5.0)
A0 = 1.2e-10  # m s^-2

def g_bar_ms2(v_bar_kms: np.ndarray, r_kpc: np.ndarray) -> np.ndarray:
    v2_m2s2 = (v_bar_kms ** 2) * (1000.0 ** 2)
    r_m = r_kpc * 3.086e19
    r_m = np.where(r_m > 0.0, r_m, np.nan)
    return v2_m2s2 / r_m

def zeta_of_r(r_kpc: np.ndarray, R_d_kpc: float, h_over_Rd: float = 0.25) -> np.ndarray:
    r = np.asarray(r_kpc, dtype=float)
    R_d = float(max(R_d_kpc, 1e-6))
    h_z = h_over_Rd * R_d
    denom = np.maximum(r, 0.1 * R_d)
    z = 1.0 / np.sqrt(1.0 + (h_z / denom) ** 2)
    return np.clip(z, 0.8, 1.2)

def w_core_accel(gbar_ms2: np.ndarray, g_ext: float = 0.0) -> np.ndarray:
    base = np.power(np.maximum(1e-300, (gbar_ms2 + g_ext) / A0), -ALPHA) - np.power(1.0 + g_ext / A0, -ALPHA)
    return 1.0 + C_LAG * base

def w_core_time(T_dyn_s: np.ndarray, T_ref_s: float) -> np.ndarray:
    base = np.power(np.maximum(1e-300, T_dyn_s / max(T_ref_s, 1e-30)), ALPHA) - 1.0
    return 1.0 + C_LAG * base

def w_core_blend(gbar_ms2: np.ndarray, T_dyn_s: np.ndarray, T_ref_s: float, g_ext: float = 0.0) -> np.ndarray:
    a = np.power(np.maximum(1e-300, T_dyn_s / max(T_ref_s, 1e-30)), ALPHA)
    b = np.power(np.maximum(1e-300, (gbar_ms2 + g_ext) / A0), -ALPHA)
    base = a * b - 1.0
    return 1.0 + C_LAG * base

def compute_T_dyn_seconds(r_kpc: np.ndarray, v_bar_kms: np.ndarray) -> np.ndarray:
    r_m = np.asarray(r_kpc, dtype=float) * 3.086e19
    v_mps = np.asarray(v_bar_kms, dtype=float) * 1000.0
    safe_v = np.where(v_mps > 0.0, v_mps, np.nan)
    return 2.0 * math.pi * r_m / safe_v


def pick_representative_galaxy(master: Dict[str, Any]) -> str:
    """Pick the galaxy with the most data points for a clean plot."""
    best_name = None
    best_len = -1
    for name, g in master.items():
        try:
            n = len(g.get('r', []))
        except Exception:
            n = 0
        if n > best_len:
            best_len = n
            best_name = name
    if best_name is None:
        # Fallback to arbitrary
        best_name = next(iter(master.keys()))
    return best_name


def main() -> int:
    ap = argparse.ArgumentParser(description="Plot SPARC RC with ILG overlay")
    ap.add_argument("--master", type=str, default="", help="Path to master table pickle")
    ap.add_argument("--galaxy", type=str, default="", help="Galaxy name to plot (exact match)")
    ap.add_argument("--out", type=str, default="active/results/example_rc.png", help="Output image path (.png or .pdf)")
    ap.add_argument("--kernel", type=str, default="blend", choices=["accel","time","blend"], help="Core kernel")
    args = ap.parse_args()
    script_path = Path(__file__).resolve()
    project_root = script_path.parents[2]
    out_dir = project_root / "active" / "results"
    out_dir.mkdir(parents=True, exist_ok=True)

    master_path = Path(args.master) if args.master else find_master_table(project_root)
    if master_path is None:
        print("Error: sparc_master.pkl not found. Run build_sparc_master_table.py first.", file=sys.stderr)
        return 1

    with open(master_path, "rb") as f:
        master = pickle.load(f)

    if not isinstance(master, dict) or len(master) == 0:
        print("Error: sparc_master.pkl is empty or invalid.", file=sys.stderr)
        return 1

    name = args.galaxy if args.galaxy and args.galaxy in master else pick_representative_galaxy(master)
    g = master[name]

    r = np.asarray(g.get('r', []), dtype=float)
    v_obs = np.asarray(g.get('v_obs', []), dtype=float)
    v_baryon = np.asarray(g.get('v_baryon', []), dtype=float)
    T_dyn = np.asarray(g.get('T_dyn', []), dtype=float)  # years
    f_gas_true = float(g.get('f_gas_true', 0.0))
    sigma0 = float(g.get('Sigma_0', 0.0))

    if any(len(x) == 0 for x in (r, v_obs, v_baryon, T_dyn)):
        print(f"Error: selected galaxy '{name}' missing required arrays.", file=sys.stderr)
        return 1

    # Compute ILG model (match benchmark kernel)
    R_d = float(g.get('R_d', 2.0))
    zeta_r = zeta_of_r(r, R_d)
    n_r = n_analytic(r)
    gbar = g_bar_ms2(v_baryon, r)
    T_dyn_s = np.asarray(T_dyn, dtype=float) * SECONDS_PER_YEAR
    # Use global T_ref as median over this galaxy as a proxy for plotting
    T_ref = float(np.nanmedian(T_dyn_s)) if np.isfinite(np.nanmedian(T_dyn_s)) else 1.0
    if args.kernel == 'accel':
        core = w_core_accel(gbar)
    elif args.kernel == 'time':
        core = w_core_time(T_dyn_s, T_ref)
    else:
        core = w_core_blend(gbar, T_dyn_s, T_ref)
    # Simple xi proxy from f_gas_true quintile center: use center=0.5 if unknown
    xi = xi_from_quintile(0.5 if not np.isfinite(f_gas_true) else max(0.0, min(1.0, f_gas_true)), C_LAG)
    w_tot = np.maximum(1e-12, xi * n_r * zeta_r * core)
    v_model = np.sqrt(w_tot) * v_baryon

    # Plot
    plt.figure(figsize=(5.0, 3.2), dpi=150)
    order = np.argsort(r)
    plt.plot(r[order], v_obs[order], color='k', lw=1.6, label='v_obs')
    plt.plot(r[order], v_baryon[order], color='k', lw=1.2, ls='--', label='v_baryon')
    plt.plot(r[order], v_model[order], color='#1f77b4', lw=1.6, label='v_model (ILG)')
    plt.xlabel('r [kpc]')
    plt.ylabel('v [km/s]')
    plt.title(name)
    plt.legend(frameon=False, fontsize=8)
    plt.tight_layout()
    out_path = Path(args.out)
    if not out_path.is_absolute():
        out_path = project_root / out_path
    out_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(out_path)
    plt.close()
    print(f"Wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


