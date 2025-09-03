#!/usr/bin/env python3
"""
SPARC 2D proxy runner (global-only, no v_obs leakage):
- Loads the SPARC master table
- For each galaxy, builds a proxy 2D Σ_b(x,y) from catalog R_d and component ratios (disk/bulge/gas)
- Runs the 2D ILG kernel to get K(x,y)
- Azimuthally averages K to obtain w(r), then produces v_model(r) = sqrt(w) * v_baryon(r)
- Optionally computes reduced χ^2/N with the shared error model for a quick summary

Outputs:
- Per-galaxy CSV with columns: r_kpc, v_obs, v_err, v_baryon, w_ring, v_model
- Summary CSV with median/mean χ^2/N for the evaluated set
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Dict, Any, Optional, Set

import numpy as np
import pandas as pd

# Allow importing from repository root
sys.path.append(str(Path(__file__).resolve().parents[2]))
from active.scripts.ilg_2d_kernel import compute_kernel_2d  # type: ignore


# Shared error model constants (mirrors ilg_rotation_benchmark.py)
SIGMA0 = 10.0
F_FRAC = 0.05
ALPHA_BEAM = 0.3
K_TURB = 0.07
P_TURB = 1.3
V_DWARF_MAX = 80.0


def load_master_table(path: Path) -> Dict[str, Dict[str, Any]]:
    import pickle
    with open(path, "rb") as f:
        return pickle.load(f)


def get_master_path() -> Path:
    candidates = [
        Path("active/results/sparc_master.pkl"),
        Path("sparc_master.pkl"),
        Path("galaxy-rotation/results/ledger_final_combined_results.pkl"),
    ]
    for p in candidates:
        if p.exists():
            return p
    raise FileNotFoundError("No master table pickle found.")


def load_subset_names(path: Optional[str]) -> Optional[Set[str]]:
    if not path:
        return None
    try:
        df = pd.read_csv(path)
        if "name" in df.columns:
            return set(map(str, df["name"].astype(str).tolist()))
        if "galaxy" in df.columns:
            return set(map(str, df["galaxy"].astype(str).tolist()))
        return None
    except Exception:
        return None


def baryonic_speed(v_gas: np.ndarray, v_disk: np.ndarray, v_bul: np.ndarray, upsilon_star: float = 1.0) -> np.ndarray:
    return np.sqrt(np.maximum(0.0, v_gas ** 2 + (np.sqrt(upsilon_star) * v_disk) ** 2 + v_bul ** 2))


def sigma_eff_kms(r_kpc: np.ndarray, v_obs_kms: np.ndarray, v_err_kms: Optional[np.ndarray], R_d_kpc: float, dwarf: bool, b_kpc: Optional[float] = None) -> np.ndarray:
    r = np.asarray(r_kpc, dtype=float)
    v = np.asarray(v_obs_kms, dtype=float)
    sigma_obs = np.asarray(v_err_kms, dtype=float) if v_err_kms is not None else np.zeros_like(v)
    sigma0 = SIGMA0
    f = F_FRAC
    alpha_beam = ALPHA_BEAM
    if b_kpc is None:
        b_kpc = 0.3 * max(R_d_kpc, 1e-6)
    sigma_beam = alpha_beam * b_kpc * v / (r + b_kpc)
    sigma_asym = (0.10 if dwarf else 0.05) * v
    sigma_turb = K_TURB * v * np.power(1.0 - np.exp(-r / max(R_d_kpc, 1e-6)), P_TURB)
    sig2 = sigma_obs ** 2 + sigma0 ** 2 + (f * v) ** 2 + sigma_beam ** 2 + sigma_asym ** 2 + sigma_turb ** 2
    return np.sqrt(np.maximum(sig2, 1e-12))


from typing import Tuple as _Tuple


def build_sigma_b_2d(nx: int, R_d: float, gas_frac: float, bulge_frac: float, box_factor: float = 8.0) -> _Tuple[np.ndarray, float]:
    """Simple proxy Σ_b: weighted sum of exponentials (disk/gas) and a central Gaussian (bulge).
    Returns (Sigma_b, dx_kpc).
    """
    L = box_factor * max(R_d, 1e-6)
    dx = (2.0 * L) / nx
    x = np.linspace(-L + 0.5 * dx, L - 0.5 * dx, nx)
    y = np.linspace(-L + 0.5 * dx, L - 0.5 * dx, nx)
    X, Y = np.meshgrid(x, y, indexing="xy")
    R = np.sqrt(X ** 2 + Y ** 2)
    disk = np.exp(-R / max(R_d, 1e-6))
    gas = np.exp(-R / max(1.7 * R_d, 1e-6))
    bulge = np.exp(-(R ** 2) / max((0.2 * R_d) ** 2, 1e-6))
    # Normalize weights
    gas_w = np.clip(gas_frac, 0.0, 0.8)
    bulge_w = np.clip(bulge_frac, 0.0, 0.8)
    disk_w = np.clip(1.0 - gas_w - bulge_w, 0.0, 1.0)
    sigma = disk_w * disk + gas_w * gas + bulge_w * bulge
    sigma = sigma / np.maximum(np.max(sigma), 1e-12)
    return sigma.astype(np.float64), dx


def azimuthal_average_ring(field: np.ndarray, radii_kpc: np.ndarray, dx_kpc: float) -> np.ndarray:
    ny, nx = field.shape
    y, x = np.indices((ny, nx))
    xc, yc = (nx - 1) / 2.0, (ny - 1) / 2.0
    Rpix = np.hypot(x - xc, y - yc)
    rpix = radii_kpc / max(dx_kpc, 1e-12)
    w_ring = np.empty_like(radii_kpc, dtype=float)
    for i, r in enumerate(rpix):
        mask = (Rpix >= r - 0.5) & (Rpix < r + 0.5)
        if not np.any(mask):
            w_ring[i] = np.nan
        else:
            w_ring[i] = float(np.nanmean(field[mask]))
    return w_ring


def main():
    ap = argparse.ArgumentParser(description="SPARC 2D proxy runner for ILG kernel (global-only)")
    ap.add_argument("--master", type=str, default="", help="Path to SPARC master pickle")
    ap.add_argument("--subset_csv", type=str, default="results/bench_rs_per_galaxy.csv", help="Optional CSV with galaxy list")
    ap.add_argument("--ml_disk", type=float, default=1.0, help="Global stellar M/L")
    ap.add_argument("--nx", type=int, default=128, help="2D grid size (nx=ny)")
    ap.add_argument("--box_factor", type=float, default=8.0, help="Half-box size in units of R_d")
    ap.add_argument("--smooth_sigma_rel", type=float, default=0.2, help="Smoothing scale as fraction of R_d")
    ap.add_argument("--out_dir", type=str, default="results/ilg2d_sparc", help="Output directory")
    args = ap.parse_args()

    if args.master:
        mpath = Path(args.master)
    else:
        mpath = get_master_path()
    master = load_master_table(mpath)
    subset = load_subset_names(args.subset_csv)
    if subset is not None and len(subset) > 0:
        master = {k: v for k, v in master.items() if str(k) in subset}

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = []

    for name, g in master.items():
        df = g.get("data")
        if df is None:
            continue
        r = df["rad"].to_numpy(float)
        v_obs = df["vobs"].to_numpy(float)
        v_err = df["verr"].to_numpy(float)
        v_gas = df["vgas"].to_numpy(float)
        v_disk = df["vdisk"].to_numpy(float)
        v_bul = df["vbul"].to_numpy(float)
        ok = (r > 0) & (v_obs > 0)
        r = r[ok]; v_obs = v_obs[ok]; v_err = v_err[ok]
        v_gas = v_gas[ok]; v_disk = v_disk[ok]; v_bul = v_bul[ok]
        if r.size < 5:
            continue
        R_d = float(g.get("R_d", 2.0))
        v_bar = baryonic_speed(v_gas, v_disk, v_bul, upsilon_star=args.ml_disk)
        # Component-based proxy fractions
        gas_frac = float(np.nanmedian(np.where(v_bar > 0, (v_gas ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        bulge_frac = float(np.nanmedian(np.where(v_bar > 0, (v_bul ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        gas_frac = np.clip(gas_frac, 0.0, 0.8)
        bulge_frac = np.clip(bulge_frac, 0.0, 0.8)
        # Build Σ_b and run 2D kernel
        Sigma_b, dx_kpc = build_sigma_b_2d(args.nx, R_d, gas_frac, bulge_frac, box_factor=args.box_factor)
        smooth_sigma_px = max(args.smooth_sigma_rel * R_d / max(dx_kpc, 1e-12), 0.5)
        K, phi_sol, ax_bar, ay_bar, _ = compute_kernel_2d(Sigma_b, gext_ratio=0.0, smooth_sigma_px=smooth_sigma_px, anisotropic=True)
        # Azimuthal average to w(r)
        w_ring = azimuthal_average_ring(K, r, dx_kpc)
        v_model = np.sqrt(np.maximum(w_ring, 1e-6)) * v_bar
        # Reduced chi^2/N (shared error model)
        b_kpc = 0.3 * max(R_d, 1e-6)
        v_outer = np.nanmedian(v_obs[-3:]) if v_obs.size >= 3 else np.nanmax(v_obs)
        dwarf = bool(v_outer < V_DWARF_MAX)
        sigma_eff = sigma_eff_kms(r, v_obs, v_err, R_d_kpc=R_d, dwarf=dwarf, b_kpc=b_kpc)
        mask = np.isfinite(v_model) & (r >= b_kpc)
        if np.any(mask):
            N = int(np.sum(mask))
            chi2 = float(np.sum(((v_obs[mask] - v_model[mask]) / sigma_eff[mask]) ** 2))
            red = chi2 / max(N, 1)
        else:
            red = np.nan; N = 0

        # Save per-galaxy CSV
        df_out = pd.DataFrame({
            "r_kpc": r,
            "v_obs": v_obs,
            "v_err": v_err,
            "v_baryon": v_bar,
            "w_ring": w_ring,
            "v_model": v_model,
        })
        df_out.to_csv(out_dir / f"{name}_2d_proxy.csv", index=False)
        rows.append({"galaxy": name, "N": N, "chi2_over_N": red})

    if rows:
        df_summary = pd.DataFrame(rows)
        df_summary.to_csv(out_dir / "summary.csv", index=False)
        arr = df_summary["chi2_over_N"].to_numpy(float)
        print(f"Evaluated {arr.size} galaxies; median chi^2/N = {np.nanmedian(arr):.3f}; mean = {np.nanmean(arr):.3f}")
    else:
        print("No galaxies evaluated.")


if __name__ == "__main__":
    main()


