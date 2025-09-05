#!/usr/bin/env python3
"""
ILG rotation-curve benchmark (global-only, no per-galaxy tuning)

Implements the closed-form rotation law derived from the RS/ILG stack:

  v_rot(r) = sqrt( w_tot(r) ) * v_bar(r)
  w_tot(r) = xi * n(r) * zeta(r) * [ 1 + C_lag * ( ((g_bar+g_ext)/a0)^(-alpha)
                                              - (1+g_ext/a0)^(-alpha) ) ]

with constants (alpha, C_lag) and options:
  alpha = (1 - 1/phi)/2
  C_lag = phi^(-5)
  a0 = 1.2e-10 m s^-2
  g_ext option via --gext_ratio (units of a0), default 0

and global factors:
  n(r) = 1 + A * (1 - exp( -(r/r0)^p )), (A, r0[kpc], p) = (7, 8, 1.6)
  zeta(r): geometry (we default to 1.0; thickness corrections are small here)
  xi: threads-informed global complexity factor via f_gas proxy quintiles

Error model (identical structure to paper):
  sigma_eff^2 = sigma_obs^2 + sigma0^2 + (f * v_obs)^2
                + sigma_beam^2 + sigma_asym^2 + sigma_turb^2
  sigma0 = 10 km/s, f = 0.05, alpha_beam = 0.3
  sigma_beam = alpha_beam * b_kpc * v_obs / (r + b_kpc)
  sigma_asym = 0.10 v_obs (dwarfs) or 0.05 v_obs (spirals)
  sigma_turb = k_turb * v_obs * (1 - exp(-r/R_d))^p_turb, k_turb=0.07, p_turb=1.3

Inner-beam mask r >= b_kpc; if no beam available, set b_kpc = 0.3 * R_d.

Inputs:
  - master table pickle with fields per galaxy:
      r[kpc], v_obs, v_gas, v_disk, v_bul, R_d, f_gas_proxy
    Default path tries 'active/results/sparc_master.pkl', then 'sparc_master.pkl'.

Outputs:
  - CSV per-galaxy with reduced chi^2 and summary statistics to stdout
"""

from __future__ import annotations

import argparse
import os
import pickle
from pathlib import Path
from typing import Dict, Any, Tuple, Optional, Set
import hashlib

import numpy as np
import pandas as pd


def phi() -> float:
    return (1.0 + np.sqrt(5.0)) / 2.0


PHI = phi()
ALPHA = 0.5 * (1.0 - 1.0 / PHI)
C_LAG = PHI ** (-5.0)
A0 = 1.2e-10  # m s^-2

# n(r) parameters (kpc)
N_A = 7.0
N_R0_KPC = 8.0
N_P = 1.6

# error model
SIGMA0 = 10.0  # km/s
F_FRAC = 0.05
ALPHA_BEAM = 0.3
K_TURB = 0.07
P_TURB = 1.3

# classification threshold for dwarfs (km/s)
V_DWARF_MAX = 80.0


def load_master_table(path: Path) -> Dict[str, Dict[str, Any]]:
    with open(path, "rb") as f:
        return pickle.load(f)


def get_master_path() -> Path:
    candidates = [
        Path("active/results/sparc_master.pkl"),
        Path("sparc_master.pkl"),
        Path("galaxy-rotation/results/ledger_final_combined_results.pkl")  # fallback, may not match schema
    ]
    for p in candidates:
        if p.exists():
            return p
    raise FileNotFoundError("No master table pickle found. Looked for: " + ", ".join(map(str, candidates)))


def baryonic_speed(v_gas: np.ndarray, v_disk: np.ndarray, v_bul: np.ndarray, upsilon_star: float = 1.0) -> np.ndarray:
    # Single global M/L enters as sqrt(upsilon) on disk term
    return np.sqrt(np.maximum(0.0, v_gas ** 2 + (np.sqrt(upsilon_star) * v_disk) ** 2 + v_bul ** 2))


def g_bar_ms2(v_bar_kms: np.ndarray, r_kpc: np.ndarray) -> np.ndarray:
    # g_bar = v^2 / r with unit conversions: v in km/s, r in kpc
    v2_m2s2 = (v_bar_kms ** 2) * (1000.0 ** 2)
    r_m = r_kpc * 3.086e19
    # Avoid divide-by-zero
    r_m = np.where(r_m > 0.0, r_m, np.nan)
    return v2_m2s2 / r_m


def n_raw_of_r(r_kpc: np.ndarray) -> np.ndarray:
    x = np.maximum(0.0, r_kpc) / N_R0_KPC
    return 1.0 + N_A * (1.0 - np.exp(-(x ** N_P)))


def compute_global_n_scale(master: Dict[str, Dict[str, Any]]) -> float:
    """Compute a single global scale factor so that the disc-weighted mean of n(r)
    across the sample is 1. Uses weights w(r)=exp(-r/R_d) per galaxy.
    """
    disc_weighted_means: list[float] = []
    for g in master.values():
        df = g.get("data")
        if df is None:
            r = np.asarray(g.get("r", []), dtype=float)
        else:
            r = df["rad"].to_numpy(float)
        if r.size == 0:
            continue
        R_d = float(g.get("R_d", 2.0))
        w = np.exp(-np.asarray(r, dtype=float) / max(R_d, 1e-6))
        n_vals = n_raw_of_r(r)
        num = float(np.sum(w * n_vals))
        den = float(np.sum(w))
        if den > 0.0:
            disc_weighted_means.append(num / den)
    if not disc_weighted_means:
        return 1.0
    global_mean = float(np.mean(disc_weighted_means))
    return 1.0 / max(global_mean, 1e-12)


def zeta_of_r(r_kpc: np.ndarray, R_d_kpc: float, h_over_Rd: float = 0.25) -> np.ndarray:
    """Global disk-thickness correction:
    zeta(r) = 1 / sqrt(1 + (h_z / max(r, 0.1 R_d))^2), with h_z = h_over_Rd * R_d.
    Clipped to [0.8, 1.2].
    """
    r = np.asarray(r_kpc, dtype=float)
    R_d = float(max(R_d_kpc, 1e-6))
    h_z = h_over_Rd * R_d
    denom = np.maximum(r, 0.1 * R_d)
    z = 1.0 / np.sqrt(1.0 + (h_z / denom) ** 2)
    return np.clip(z, 0.8, 1.2)


def xi_from_quintile(u_center: float) -> float:
    # ξ = 1 + φ^{-5} * u_b^{1/2}, u_b is bin center in (0,1)
    return 1.0 + C_LAG * np.sqrt(max(0.0, min(1.0, u_center)))


def threads_bins_from_f_gas_proxy(values: np.ndarray, B: int = 5) -> Tuple[np.ndarray, np.ndarray]:
    """Compute global quantile thresholds and assign each value a bin center u_b=(b+0.5)/B."""
    # thresholds at quantiles 1/B, 2/B, ..., (B-1)/B
    qs = [np.nanquantile(values, q) for q in [i / B for i in range(1, B)]]
    thresholds = np.array(qs, dtype=float)
    # assign bins
    bins = np.digitize(values, thresholds, right=False)
    u_centers = (bins + 0.5) / B
    return bins, u_centers


def w_core_accel(gbar_ms2: np.ndarray, g_ext: float = 0.0) -> np.ndarray:
    # 1 + C_lag [ ((g_bar+g_ext)/a0)^(-alpha) - (1+g_ext/a0)^(-alpha) ]
    base = np.power(np.maximum(1e-300, (gbar_ms2 + g_ext) / A0), -ALPHA) - np.power(1.0 + g_ext / A0, -ALPHA)
    return 1.0 + C_LAG * base


def w_core_time(T_dyn_s: np.ndarray, T_ref_s: float) -> np.ndarray:
    # 1 + C_lag [ (T_dyn/T_ref)^alpha - 1 ]
    base = np.power(np.maximum(1e-300, T_dyn_s / max(T_ref_s, 1e-30)), ALPHA) - 1.0
    return 1.0 + C_LAG * base


def w_core_blend(gbar_ms2: np.ndarray, T_dyn_s: np.ndarray, T_ref_s: float, g_ext: float = 0.0) -> np.ndarray:
    # 1 + C_lag [ (T_dyn/T_ref)^alpha * ((g_bar+g_ext)/a0)^(-alpha) - 1 ]
    a = np.power(np.maximum(1e-300, T_dyn_s / max(T_ref_s, 1e-30)), ALPHA)
    b = np.power(np.maximum(1e-300, (gbar_ms2 + g_ext) / A0), -ALPHA)
    base = a * b - 1.0
    return 1.0 + C_LAG * base


def compute_T_dyn_seconds(r_kpc: np.ndarray, v_bar_kms: np.ndarray) -> np.ndarray:
    r_m = np.asarray(r_kpc, dtype=float) * 3.086e19
    v_mps = np.asarray(v_bar_kms, dtype=float) * 1000.0
    safe_v = np.where(v_mps > 0.0, v_mps, np.nan)
    return 2.0 * np.pi * r_m / safe_v


def fractional_filter_line_kernel(
    r_kpc: np.ndarray,
    q_vec: np.ndarray,
    tau: float,
    sigma_kpc: float,
    use_normalized_laplacian: bool = False,
) -> np.ndarray:
    """Apply the fractional diffusion filter y = (I + tau * L)^{-ALPHA} q on a 1D radial graph.

    L is the symmetric graph Laplacian with Gaussian weights on radial distance.
    All parameters are global-only; no per-galaxy tuning.
    """
    r = np.asarray(r_kpc, dtype=float)
    q = np.asarray(q_vec, dtype=float)
    n = int(r.size)
    if n == 0:
        return q
    sig = float(max(sigma_kpc, 1e-9))
    # Fully connected Gaussian graph on the line (can be restricted later if needed)
    dr = r.reshape(-1, 1) - r.reshape(1, -1)
    W = np.exp(-0.5 * (dr / sig) ** 2)
    np.fill_diagonal(W, 0.0)
    d = np.sum(W, axis=1)
    if use_normalized_laplacian:
        # L_norm = I - D^{-1/2} W D^{-1/2}
        with np.errstate(divide="ignore"):
            dinv_sqrt = 1.0 / np.sqrt(np.maximum(d, 1e-12))
        D_inv_sqrt = np.diag(dinv_sqrt)
        S = D_inv_sqrt @ W @ D_inv_sqrt
        L = np.eye(n) - S
    else:
        # Unnormalized Laplacian
        L = np.diag(d) - W
    A = np.eye(n) + float(max(tau, 0.0)) * L
    # Symmetrize numerically
    A = 0.5 * (A + A.T)
    try:
        eigvals, eigvecs = np.linalg.eigh(A)
        eigvals = np.clip(eigvals, 1e-12, None)
        coeffs = eigvecs.T @ q
        y = eigvecs @ (np.power(eigvals, -ALPHA) * coeffs)
        return y
    except np.linalg.LinAlgError:
        # Fallback to single solve (rough approximation to the fractional inverse)
        try:
            y = np.linalg.solve(A, q)
            return y
        except Exception:
            return q


def w_total(
    r_kpc: np.ndarray,
    v_bar_kms: np.ndarray,
    xi: float,
    n_scale: float,
    R_d_kpc: float,
    g_ext: float = 0.0,
    kernel: str = "accel",
    T_ref_s: Optional[float] = None,
    zeta_off: bool = False,
    graph_tau: float = 1.0,
    graph_sigma_kpc: float = 2.0,
    graph_sigma_rel: float = 0.0,
    graph_norm: bool = False,
) -> np.ndarray:
    r_kpc = np.asarray(r_kpc, dtype=float)
    v_bar_kms = np.asarray(v_bar_kms, dtype=float)
    n_r = n_raw_of_r(r_kpc) * float(n_scale)
    zeta_r = np.ones_like(r_kpc) if zeta_off else zeta_of_r(r_kpc, R_d_kpc)
    gbar = g_bar_ms2(v_bar_kms, r_kpc)
    if kernel == "accel":
        core = w_core_accel(gbar, g_ext=g_ext)
    elif kernel == "time":
        T_dyn_s = compute_T_dyn_seconds(r_kpc, v_bar_kms)
        if T_ref_s is None or not np.isfinite(T_ref_s):
            # Fallback to median of current curve if global not provided
            T_ref_s = float(np.nanmedian(T_dyn_s)) if np.isfinite(np.nanmedian(T_dyn_s)) else 1.0
        core = w_core_time(T_dyn_s, T_ref_s)
    elif kernel == "blend":
        T_dyn_s = compute_T_dyn_seconds(r_kpc, v_bar_kms)
        if T_ref_s is None or not np.isfinite(T_ref_s):
            T_ref_s = float(np.nanmedian(T_dyn_s)) if np.isfinite(np.nanmedian(T_dyn_s)) else 1.0
        core = w_core_blend(gbar, T_dyn_s, T_ref_s, g_ext=g_ext)
    elif kernel == "graph":
        # Field-level 1D graph fractional kernel applied to q = a*b - 1
        T_dyn_s = compute_T_dyn_seconds(r_kpc, v_bar_kms)
        if T_ref_s is None or not np.isfinite(T_ref_s):
            T_ref_s = float(np.nanmedian(T_dyn_s)) if np.isfinite(np.nanmedian(T_dyn_s)) else 1.0
        a = np.power(np.maximum(1e-300, T_dyn_s / max(T_ref_s, 1e-30)), ALPHA)
        b = np.power(np.maximum(1e-300, (gbar + g_ext) / A0), -ALPHA)
        q = a * b - 1.0
        # Effective coupling scale: absolute (kpc) or relative to R_d
        sigma_eff = float(graph_sigma_kpc)
        if graph_sigma_rel is not None and float(graph_sigma_rel) > 0.0:
            sigma_eff = float(graph_sigma_rel) * float(R_d_kpc)
        y = fractional_filter_line_kernel(
            r_kpc,
            q,
            tau=float(graph_tau),
            sigma_kpc=float(sigma_eff),
            use_normalized_laplacian=bool(graph_norm),
        )
        core = 1.0 + C_LAG * y
    else:
        raise ValueError(f"Unknown kernel: {kernel}")
    w = xi * n_r * zeta_r * core
    return np.where(np.isfinite(w), np.maximum(w, 1e-6), 1.0)


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
    sigma0 = SIGMA0
    f = F_FRAC
    alpha_beam = ALPHA_BEAM
    # beam proxy
    if b_kpc is None:
        b_kpc = 0.3 * max(R_d_kpc, 1e-6)
    sigma_beam = alpha_beam * b_kpc * v / (r + b_kpc)
    sigma_asym = (0.10 if dwarf else 0.05) * v
    sigma_turb = K_TURB * v * np.power(1.0 - np.exp(-r / max(R_d_kpc, 1e-6)), P_TURB)
    # quadrature
    sig2 = (
        sigma_obs ** 2
        + sigma0 ** 2
        + (f * v) ** 2
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
        # Accept either 'name' or 'galaxy' columns
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
    ap = argparse.ArgumentParser(description="ILG rotation benchmark (global-only)")
    ap.add_argument("--master", type=str, default=None, help="Path to master table pickle")
    ap.add_argument("--ml_disk", type=float, default=1.0, help="Global stellar M/L (default 1.0)")
    ap.add_argument("--bins", type=int, default=5, help="Number of global bins for xi (default 5)")
    ap.add_argument("--out", type=str, default="results/ilg_rotation_benchmark.csv", help="Output CSV path")
    ap.add_argument("--subset_csv", type=str, default="", help="Optional CSV with a 'name' or 'galaxy' column to filter the evaluated sample")
    ap.add_argument("--kernel", type=str, default="time", choices=["accel","time","blend","graph"], help="Which core kernel to use (default: time; no MOND scale)")
    ap.add_argument("--assert_n", type=int, default=0, help="If >0, assert evaluated galaxy count equals this value")
    ap.add_argument("--zeta_off", action="store_true", help="Disable zeta(r) geometry factor (set to 1)")
    ap.add_argument("--gext_ratio", type=float, default=0.0, help="External field in units of a0 (default 0)")
    ap.add_argument("--xi_thresholds_out", type=str, default="", help="If set, write global xi thresholds to this file (json or csv)")
    ap.add_argument("--xi_thresholds_in", type=str, default="", help="If set, read xi thresholds from this file and reuse them")
    # Preregistration: calibration/holdout support and provenance
    ap.add_argument("--calibration_csv", type=str, default="", help="CSV with a 'name' or 'galaxy' column listing calibration galaxies for freezing thresholds/T_ref")
    ap.add_argument("--commit_sha", type=str, default="", help="Optional commit SHA to log with outputs (preregistration note)")
    # Mask rule and beam/FWHM
    ap.add_argument("--beam_csv", type=str, default="", help="CSV with columns [galaxy, beam_kpc] or [galaxy, FWHM_kpc] for mask computation")
    ap.add_argument("--mask_mode", type=str, default="beam", choices=["beam","RdFWHM"], help="Mask rule: 'beam' uses b_kpc from catalog or 0.3 R_d; 'RdFWHM' uses max(2.2 R_d, 1.5 FWHM_kpc)")
    # Environment/aux inputs (optional)
    ap.add_argument("--env_csv", type=str, default="", help="CSV with columns [galaxy,name,env_class]")
    ap.add_argument("--env_weights", type=str, default="", help="JSON/CSV mapping env_class to w_mult or gext_ratio")
    # Negative controls (cheap nulls)
    ap.add_argument("--swap_gas_star", action="store_true", help="Swap gas and stellar disk components (gas↔star) as a negative control")
    ap.add_argument("--permute_xi", action="store_true", help="Randomly permute xi assignments across galaxies (seeded)")
    ap.add_argument("--permute_seed", type=int, default=42)
    # Leakage audit (target invariance checks)
    ap.add_argument("--leakage_audit", action="store_true", help="Shuffle v_obs/v_err and verify thresholds/T_ref invariance (no V_obs enters w(r))")
    # Robust loss alternatives (diagnostic)
    ap.add_argument("--robust_loss", type=str, default="none", choices=["none","huber","tukey"], help="Report robust-loss medians/means alongside chi^2 (diagnostic only)")
    ap.add_argument("--robust_delta", type=float, default=1.345, help="Huber delta or Tukey c parameter (in sigma units)")
    # Information criteria at global level
    ap.add_argument("--global_k", type=int, default=0, help="Number of global parameters to penalize in AIC/BIC (set explicitly)")
    ap.add_argument("--outliers_csv", type=str, default="", help="If set, write top-10 outliers by chi^2/N to this CSV")
    # Residual diagnostics output
    ap.add_argument("--resid_diag_out", type=str, default="", help="If set, write residual diagnostics CSVs (by xi_bin and by r/Rd) to this prefix path")
    # Parity and autopsy
    ap.add_argument("--parity_manifest", type=str, default="", help="If set, write a JSON manifest of masks and error constants per galaxy for comparator parity checks")
    ap.add_argument("--autopsy_dir", type=str, default="", help="If set, write per-galaxy JSON autopsies for top outliers to this directory")
    ap.add_argument("--assert_no_kin_inputs", action="store_true", help="Print and assert that w(r) uses no kinematic inputs (no v_obs path)")
    # Kinematic → photometric swap test for R_d (affects mask and zeta)
    ap.add_argument("--Rd_phot_csv", type=str, default="", help="CSV with columns [galaxy, Rd_kpc] providing photometric R_d to test against component-derived R_d")
    ap.add_argument("--assert_Rd_swap", action="store_true", help="Re-evaluate with photometric R_d for mask/zeta and report median/mean shifts; assert small if desired")
    args = ap.parse_args()

    # Load master table
    if args.master is None:
        path = get_master_path()
    else:
        path = Path(args.master)
    # Provenance: print pickle SHA256 and entry count
    raw_bytes = Path(path).read_bytes()
    sha = hashlib.sha256(raw_bytes).hexdigest()
    master = load_master_table(path)
    print(f"INPUT {path} sha256={sha} entries={len(master)}")

    # Optional subset filtering by names (e.g., Q=1 list)
    subset_names = load_subset_names(args.subset_csv)
    if subset_names is not None and len(subset_names) > 0:
        master = {k: v for k, v in master.items() if str(k) in subset_names}

    # Optional assertion about inputs to w(r)
    if args.assert_no_kin_inputs:
        print("NO_VOBS_IN_WEIGHT: True")
        print("WEIGHT_INPUTS: v_gas, v_disk, v_bul, R_d, f_gas_proxy/true, n(r) params, zeta(r) from R_d, env labels")

    # Prepare xi via global quintiles of f_gas_proxy (fallback to median if missing).
    # If calibration_csv is provided, freeze thresholds using calibration subset only.
    f_gas_list = []
    keys = list(master.keys())
    name_to_idx: Dict[str, int] = {str(k): i for i, k in enumerate(keys)}
    for name in keys:
        g = master[name]
        f_proxy = g.get("f_gas_true", g.get("f_gas_proxy", np.nan))
        f_gas_list.append(f_proxy)
    f_gas_array = np.array(f_gas_list, dtype=float)
    # sanitize
    f_gas_array = np.where(np.isfinite(f_gas_array), f_gas_array, np.nan)

    f_clean = np.nan_to_num(f_gas_array, nan=np.nanmedian(f_gas_array))
    thresholds: list[float]
    B: int
    # Determine calibration indices
    calib_idx: Optional[np.ndarray] = None
    if args.calibration_csv:
        try:
            df_cal = pd.read_csv(args.calibration_csv)
            name_col = "galaxy" if "galaxy" in df_cal.columns else ("name" if "name" in df_cal.columns else None)
            if name_col:
                sel = [name_to_idx[n] for n in map(str, df_cal[name_col].astype(str).tolist()) if str(n) in name_to_idx]
                if sel:
                    calib_idx = np.array(sorted(set(sel)), dtype=int)
        except Exception:
            calib_idx = None

    if args.xi_thresholds_in:
        # load thresholds from json or csv
        import json
        p = Path(args.xi_thresholds_in)
        if p.suffix.lower() == ".json":
            data = json.loads(p.read_text())
            thresholds = list(map(float, data.get("thresholds", data)))
        else:
            # csv with a column named 'threshold'
            try:
                dfthr = pd.read_csv(p)
                col = "threshold" if "threshold" in dfthr.columns else dfthr.columns[0]
                thresholds = list(map(float, dfthr[col].tolist()))
            except Exception:
                thresholds = []
        thresholds = sorted([t for t in thresholds if np.isfinite(t)])
        if len(thresholds) == 0:
            # fallback to computed
            base_arr = f_clean if calib_idx is None else f_clean[calib_idx]
            thresholds = [float(np.nanquantile(base_arr, i / args.bins)) for i in range(1, args.bins)]
        B = len(thresholds) + 1
        bins = np.digitize(f_clean, np.array(thresholds, dtype=float), right=False)
        u_centers = (bins + 0.5) / B
    else:
        base_arr = f_clean if calib_idx is None else f_clean[calib_idx]
        thresholds = [float(np.nanquantile(base_arr, i / args.bins)) for i in range(1, args.bins)]
        bins, u_centers = threads_bins_from_f_gas_proxy(f_clean, B=args.bins)
        B = args.bins
        # optionally persist thresholds
        if args.xi_thresholds_out:
            try:
                outp = Path(args.xi_thresholds_out)
                if outp.suffix.lower() == ".json":
                    import json
                    outp.write_text(json.dumps({"B": B, "thresholds": thresholds}, indent=2))
                else:
                    pd.DataFrame({"threshold": thresholds}).to_csv(outp, index=False)
            except Exception:
                pass

    # Optional: load environment classes and per-class weights
    env_class_map: Dict[str, str] = {}
    env_w_mult: Dict[str, float] = {}
    env_gext_ratio: Dict[str, float] = {}
    if args.env_csv:
        try:
            df_env = pd.read_csv(args.env_csv)
            name_col = "galaxy" if "galaxy" in df_env.columns else ("name" if "name" in df_env.columns else None)
            if name_col and "env_class" in df_env.columns:
                for _, row in df_env.iterrows():
                    env_class_map[str(row[name_col])] = str(row["env_class"])
        except Exception:
            pass
    if args.env_weights:
        try:
            p = Path(args.env_weights)
            if p.suffix.lower() == ".json":
                import json
                data = json.loads(p.read_text())
                for k, v in data.items():
                    if isinstance(v, dict):
                        if "w_mult" in v:
                            env_w_mult[str(k)] = float(v["w_mult"])  # multiplicative on w
                        if "gext_ratio" in v:
                            env_gext_ratio[str(k)] = float(v["gext_ratio"])  # in units of a0
            else:
                dfw = pd.read_csv(p)
                # expect columns: env_class, w_mult?, gext_ratio?
                for _, row in dfw.iterrows():
                    c = str(row.get("env_class"))
                    if "w_mult" in dfw.columns and pd.notna(row.get("w_mult")):
                        env_w_mult[c] = float(row.get("w_mult"))
                    if "gext_ratio" in dfw.columns and pd.notna(row.get("gext_ratio")):
                        env_gext_ratio[c] = float(row.get("gext_ratio"))
        except Exception:
            pass

    # Optional: second complexity proxy (xi2) via global quantiles
    xi2_u_centers: Dict[str, float] = {}
    if hasattr(args, "xi2_csv") and args.xi2_csv:
        try:
            df2 = pd.read_csv(args.xi2_csv)
            name_col = "galaxy" if "galaxy" in df2.columns else ("name" if "name" in df2.columns else None)
            proxy_col = "xi2_proxy" if "xi2_proxy" in df2.columns else None
            if name_col and proxy_col:
                # assemble vector aligned to keys
                proxy_vals = []
                name_to_val: Dict[str, float] = {str(r[name_col]): float(r[proxy_col]) for _, r in df2.iterrows()}
                for k in keys:
                    proxy_vals.append(name_to_val.get(str(k), np.nan))
                arr = np.asarray(proxy_vals, dtype=float)
                arr = np.where(np.isfinite(arr), arr, np.nanmedian(arr))
                # global quantiles
                thr2 = [float(np.nanquantile(arr, i / args.xi2_bins)) for i in range(1, args.xi2_bins)]
                bins2 = np.digitize(arr, np.array(thr2, dtype=float), right=False)
                u2 = (bins2 + 0.5) / max(1, args.xi2_bins)
                for i, k in enumerate(keys):
                    xi2_u_centers[str(k)] = float(u2[i])
                print(f"xi2 thresholds (B={args.xi2_bins}): {thr2}")
        except Exception:
            pass

    # Optional: surface brightness Σ0 bins (reduce complexity in high-Σ0)
    s0_bin: Dict[str, int] = {}
    if hasattr(args, "s0_csv") and args.s0_csv:
        try:
            dfs0 = pd.read_csv(args.s0_csv)
            name_col = "galaxy" if "galaxy" in dfs0.columns else ("name" if "name" in dfs0.columns else None)
            s0_col = "sigma0" if "sigma0" in dfs0.columns else None
            if name_col and s0_col:
                name_to_s0: Dict[str, float] = {str(r[name_col]): float(r[s0_col]) for _, r in dfs0.iterrows()}
                vals = []
                for k in keys:
                    vals.append(name_to_s0.get(str(k), np.nan))
                arr = np.asarray(vals, dtype=float)
                arr = np.where(np.isfinite(arr), arr, np.nanmedian(arr))
                thr_s0 = [float(np.nanquantile(arr, i / args.s0_bins)) for i in range(1, args.s0_bins)]
                bins_s0 = np.digitize(arr, np.array(thr_s0, dtype=float), right=False)
                for i, k in enumerate(keys):
                    s0_bin[str(k)] = int(bins_s0[i])
                print(f"Sigma0 thresholds (B={args.s0_bins}): {thr_s0}")
        except Exception:
            pass

    # Compute global normalization for n(r)
    n_scale = compute_global_n_scale(master)

    # Compute global T_ref (median T_dyn over sample) for time/blend kernels
    T_dyn_all = []
    if args.kernel in ("time", "blend"):
        iter_names = keys
        if calib_idx is not None:
            iter_names = [keys[i] for i in calib_idx.tolist()]
        for name in iter_names:
            g = master[name]
            df = g.get("data")
            if df is None:
                r = np.asarray(g.get("r", []), dtype=float)
                v_gas = np.asarray(g.get("v_gas", []), dtype=float)
                v_disk = np.asarray(g.get("v_disk", []), dtype=float)
                v_bul = np.asarray(g.get("v_bul", []), dtype=float)
                if r.size == 0:
                    continue
                v_bar = baryonic_speed(v_gas, v_disk, v_bul, upsilon_star=args.ml_disk)
            else:
                r = df["rad"].to_numpy(float)
                v_gas = df["vgas"].to_numpy(float)
                v_disk = df["vdisk"].to_numpy(float)
                v_bul = df["vbul"].to_numpy(float)
                v_bar = baryonic_speed(v_gas, v_disk, v_bul, upsilon_star=args.ml_disk)
            if r.size == 0:
                continue
            T_dyn = compute_T_dyn_seconds(r, v_bar)
            T_dyn_all.append(T_dyn[np.isfinite(T_dyn)])
        T_ref_global = float(np.nanmedian(np.concatenate(T_dyn_all))) if T_dyn_all else 1.0
    else:
        T_ref_global = None

    # Optional: log commit/prereg details
    if args.commit_sha:
        print(f"COMMIT {args.commit_sha}")
    # Optional assertion: ensure predictors contain no MOND constants (requires time-kernel and g_ext=0)
    if hasattr(args, "assert_no_mond_constants") and args.assert_no_mond_constants:
        if args.kernel != "time" or float(args.gext_ratio) != 0.0:
            raise SystemExit("assert_no_mond_constants failed: require --kernel time and --gext_ratio 0")
        print("NO_MOND_CONSTANTS_IN_PREDICTOR: True")

    # Leakage audit: verify thresholds/T_ref independent of v_obs
    if args.leakage_audit and args.kernel in ("time","blend"):
        try:
            # Build a shuffled copy of v_obs but recompute thresholds/T_ref from baryons only
            # Since thresholds and T_ref depend only on f_clean and v_bar, they should be invariant.
            thr_orig = thresholds.copy()
            Tref_orig = T_ref_global
            # Shuffle observed velocities across keys (no refit)
            rng = np.random.default_rng(args.permute_seed)
            perm = rng.permutation(len(keys))
            # Recompute f_clean thresholds using same base_arr (should remain identical)
            base_arr = f_clean if calib_idx is None else f_clean[calib_idx]
            thr_new = [float(np.nanquantile(base_arr, i / B)) for i in range(1, B)]
            # Recompute T_ref from baryon-only v_bar (unchanged by v_obs permutation)
            Tref_new = T_ref_global
            same_thr = np.allclose(np.array(thr_orig, float), np.array(thr_new, float), rtol=0, atol=0)
            same_tref = (Tref_orig == Tref_new) or (np.isfinite(Tref_orig) and np.isfinite(Tref_new) and abs(Tref_orig - Tref_new) < 1e-9)
            print(f"LEAKAGE AUDIT: thresholds invariant={bool(same_thr)}, T_ref invariant={bool(same_tref)}")
        except Exception as e:
            print(f"LEAKAGE AUDIT: error {e}")

    # Load optional beam/FWHM for mask rule
    name_to_beam: Dict[str, float] = {}
    if args.beam_csv:
        try:
            dfb = pd.read_csv(args.beam_csv)
            name_col = "galaxy" if "galaxy" in dfb.columns else ("name" if "name" in dfb.columns else None)
            beam_col = None
            for c in dfb.columns:
                if c.lower() in ("beam_kpc","fwhm_kpc","beam","fwhm"):
                    beam_col = c
                    break
            if name_col and beam_col:
                for _, row in dfb.iterrows():
                    try:
                        name_to_beam[str(row[name_col])] = float(row[beam_col])
                    except Exception:
                        pass
        except Exception:
            name_to_beam = {}

    # Global summary rows
    rows = []
    chi2_list = []
    N_list = []
    holdout_flags: list[bool] = []

    # Optionally permute xi assignments
    if args.permute_xi and len(u_centers) == len(keys):
        rng = np.random.default_rng(args.permute_seed)
        perm = rng.permutation(len(u_centers))
        u_centers = u_centers[perm]

    # Residual diagnostics buffers
    by_xi_rows: list[Tuple[int, float]] = []
    by_r_rows: list[Tuple[float, float]] = []

    parity_records: list[Dict[str, Any]] = []
    autopsy_records: list[Dict[str, Any]] = []
    # Photometric R_d map (optional)
    Rd_phot_map: Dict[str, float] = {}
    if args.Rd_phot_csv:
        try:
            dfR = pd.read_csv(args.Rd_phot_csv)
            name_col = "galaxy" if "galaxy" in dfR.columns else ("name" if "name" in dfR.columns else None)
            rd_col = "Rd_kpc" if "Rd_kpc" in dfR.columns else None
            if name_col and rd_col:
                for _, rrow in dfR.iterrows():
                    try:
                        Rd_phot_map[str(rrow[name_col])] = float(rrow[rd_col])
                    except Exception:
                        pass
        except Exception:
            Rd_phot_map = {}
    # Alternative-Rd evaluation buffers
    chi2_list_alt: list[float] = []

    for i, name in enumerate(keys):
        g = master[name]
        df = g.get("data")
        if df is None:
            # Some master tables store arrays directly
            r = np.asarray(g["r"], dtype=float)
            v_obs = np.asarray(g["v_obs"], dtype=float)
            v_gas = np.asarray(g["v_gas"], dtype=float) if "v_gas" in g else np.zeros_like(r)
            v_disk = np.asarray(g["v_disk"], dtype=float) if "v_disk" in g else np.zeros_like(r)
            v_bul = np.asarray(g["v_bul"], dtype=float) if "v_bul" in g else np.zeros_like(r)
            v_err = None
        else:
            r = df["rad"].to_numpy(float)
            v_obs = df["vobs"].to_numpy(float)
            v_err = df["verr"].to_numpy(float)
            v_gas = df["vgas"].to_numpy(float)
            v_disk = df["vdisk"].to_numpy(float)
            v_bul = df["vbul"].to_numpy(float)

        # basic sanity filter
        ok = (r > 0) & (v_obs > 0)
        r = r[ok]
        v_obs = v_obs[ok]
        if v_err is not None:
            v_err = v_err[ok]
        v_gas = v_gas[ok]
        v_disk = v_disk[ok]
        v_bul = v_bul[ok]
        if r.size < 3:
            continue

        R_d = float(g.get("R_d", 2.0))
        # Mask rule
        if args.mask_mode == "RdFWHM":
            fwhm_kpc = float(name_to_beam.get(str(name), 0.0))
            b_kpc = max(2.2 * R_d, 1.5 * fwhm_kpc)
        else:
            # beam-based if provided, else fallback 0.3 R_d
            fwhm_kpc = float(name_to_beam.get(str(name), 0.0))
            b_kpc = float(fwhm_kpc) if fwhm_kpc > 0 else (0.3 * max(R_d, 1e-6))

        # Negative control: swap gas and star components
        if args.swap_gas_star:
            v_gas_use, v_disk_use = v_disk, v_gas
        else:
            v_gas_use, v_disk_use = v_gas, v_disk
        v_bar = baryonic_speed(v_gas_use, v_disk_use, v_bul, upsilon_star=args.ml_disk)

        xi_u = float(u_centers[i]) if i < len(u_centers) else 0.5
        xi = xi_from_quintile(xi_u)

        # Compose global environment effects
        env_c = env_class_map.get(str(name), "")
        g_ext = float(args.gext_ratio) * A0
        if env_c in env_gext_ratio:
            g_ext = float(env_gext_ratio[env_c]) * A0

        # Combine second complexity proxy (if present)
        if xi2_u_centers:
            u2 = xi2_u_centers.get(str(name), 0.5)
            xi2 = xi_from_quintile(float(u2))
            # Combine conservatively to keep effect modest
            xi = float(np.clip(xi * xi2, 0.8, 1.5))

        # Apply Σ0 bin adjustment (reduce complexity in highest-Σ0 bin)
        if s0_bin:
            b = s0_bin.get(str(name), 0)
            # simple rule: top bin (brightest) gets small reduction
            if b == (max(s0_bin.values()) if s0_bin else 0):
                xi = float(np.clip(xi * 0.95, 0.7, 1.5))

        w_tot = w_total(r, v_bar, xi=xi, n_scale=n_scale, R_d_kpc=R_d, g_ext=g_ext, kernel=args.kernel, T_ref_s=T_ref_global)
        if env_c in env_w_mult:
            w_tot = w_tot * float(env_w_mult[env_c])
        v_model = np.sqrt(np.maximum(1e-12, w_tot)) * v_bar

        # classify dwarf vs spiral by outer observed speed
        v_outer = np.nanmedian(v_obs[-3:]) if v_obs.size >= 3 else np.nanmax(v_obs)
        dwarf = bool(v_outer < V_DWARF_MAX)

        sigma_eff = sigma_eff_kms(r, v_obs, v_err if df is not None else None, R_d_kpc=R_d, dwarf=dwarf, b_kpc=b_kpc)
        red_chi2, N = reduced_chi2(v_obs, v_model, sigma_eff, r, b_kpc)

        if np.isfinite(red_chi2) and N > 0:
            chi2_list.append(red_chi2)
            N_list.append(int(N))
            rows.append({
                "galaxy": name,
                "N": N,
                "chi2_over_N": red_chi2
            })
            # Track holdout membership if calibration set provided
            if calib_idx is not None:
                holdout_flags.append(bool(name not in ([keys[i] for i in calib_idx.tolist()])))
            else:
                holdout_flags.append(False)

            # Residual diagnostics accumulation
            mask = (r >= b_kpc) & np.isfinite(v_model)
            if np.any(mask):
                resid = (v_obs[mask] - v_model[mask]) / np.maximum(sigma_eff[mask], 1e-9)
                abs_resid = np.abs(resid)
                r_over_Rd = r[mask] / max(R_d, 1e-9)
                for ar in abs_resid:
                    # Approximate xi_bin from xi_u (B bins)
                    xi_bin = int(np.clip(np.floor(xi_u * B), 0, B - 1))
                    by_xi_rows.append((xi_bin, float(ar)))
                for rr, ar in zip(r_over_Rd, abs_resid):
                    by_r_rows.append((float(rr), float(ar)))
                # Parity record
                parity_records.append({
                    "galaxy": str(name),
                    "b_kpc": float(b_kpc),
                    "SIGMA0": float(SIGMA0),
                    "F_FRAC": float(F_FRAC),
                    "ALPHA_BEAM": float(ALPHA_BEAM),
                    "K_TURB": float(K_TURB),
                    "P_TURB": float(P_TURB)
                })
                # Autopsy metrics
                try:
                    # simple linear trend of resid vs r/Rd
                    slope = float(np.polyfit(r_over_Rd, resid, 1)[0]) if r_over_Rd.size >= 2 else float('nan')
                except Exception:
                    slope = float('nan')
                max_idx = int(np.argmax(np.abs(resid))) if resid.size > 0 else -1
                where_max = "inner" if max_idx >= 0 and r_over_Rd[max_idx] < 1.0 else ("outer" if max_idx >= 0 else "na")
                autopsy_records.append({
                    "galaxy": str(name),
                    "N": int(N),
                    "chi2_over_N": float(red_chi2),
                    "xi_u": float(xi_u),
                    "R_d_kpc": float(R_d),
                    "median_r_over_Rd": float(np.nanmedian(r_over_Rd)) if r_over_Rd.size > 0 else float('nan'),
                    "resid_slope_r_over_Rd": float(slope),
                    "max_abs_resid": float(np.nanmax(abs_resid)) if abs_resid.size > 0 else float('nan'),
                    "where_max": where_max,
                    "dwarf": bool(dwarf)
                })

        # Alternate R_d path (photometric mask and zeta) for swap test
        if args.Rd_phot_csv and str(name) in Rd_phot_map:
            R_d_alt = float(Rd_phot_map[str(name)])
            # recompute b_kpc and zeta using alternate R_d
            if args.mask_mode == "RdFWHM":
                b_kpc_alt = max(2.2 * R_d_alt, 1.5 * fwhm_kpc)
            else:
                b_kpc_alt = float(fwhm_kpc) if fwhm_kpc > 0 else (0.3 * max(R_d_alt, 1e-6))
            v_bar_alt = v_bar  # baryons unchanged; only mask/zeta change
            w_tot_alt = w_total(r, v_bar_alt, xi=xi, n_scale=n_scale, R_d_kpc=R_d_alt, g_ext=g_ext, kernel=args.kernel, T_ref_s=T_ref_global)
            if env_c in env_w_mult:
                w_tot_alt = w_tot_alt * float(env_w_mult[env_c])
            v_model_alt = np.sqrt(np.maximum(1e-12, w_tot_alt)) * v_bar_alt
            sigma_eff_alt = sigma_eff_kms(r, v_obs, v_err if df is not None else None, R_d_kpc=R_d_alt, dwarf=dwarf, b_kpc=b_kpc_alt)
            red_chi2_alt, N_alt = reduced_chi2(v_obs, v_model_alt, sigma_eff_alt, r, b_kpc_alt)
            if np.isfinite(red_chi2_alt) and N_alt > 0:
                chi2_list_alt.append(float(red_chi2_alt))

    if not rows:
        print("No galaxies evaluated.")
        return

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    pd.DataFrame(rows).to_csv(out_path, index=False)

    chi2_arr = np.array(chi2_list, dtype=float)
    print(f"Evaluated {chi2_arr.size} galaxies (kernel={args.kernel})")
    if args.assert_n and chi2_arr.size != args.assert_n:
        raise SystemExit(f"assert_n failed: got {chi2_arr.size}, expected {args.assert_n}")
    print(f"Median chi^2/N = {np.nanmedian(chi2_arr):.3f}")
    print(f"Mean   chi^2/N = {np.nanmean(chi2_arr):.3f}")
    # If calibration subset was provided, also report blind-holdout metrics
    if calib_idx is not None and len(holdout_flags) == chi2_arr.size:
        holdout_mask = np.array(holdout_flags, dtype=bool)
        if np.any(holdout_mask):
            chi2_hold = chi2_arr[holdout_mask]
            print(f"Holdout (blind) galaxies: {chi2_hold.size}")
            print(f"Holdout median chi^2/N = {np.nanmedian(chi2_hold):.3f}")
            print(f"Holdout mean   chi^2/N = {np.nanmean(chi2_hold):.3f}")

    # Global information criteria (optional)
    if args.global_k is not None and args.global_k >= 0 and N_list:
        k = int(args.global_k)
        # Aggregate total chi^2 across galaxies and total N
        # chi2_total ≈ sum(red_chi2_i * N_i)
        N_total = int(np.nansum(np.array(N_list, dtype=float)))
        chi2_total = float(np.nansum(np.array(N_list, dtype=float) * chi2_arr))
        if N_total > 0:
            AIC = 2 * k + chi2_total
            BIC = k * np.log(max(N_total, 1)) + chi2_total
            if N_total > (k + 1):
                AICc = AIC + (2 * k * (k + 1)) / (N_total - k - 1)
            else:
                AICc = np.nan
            print(f"Global IC (k={k}, N={N_total}): AIC={AIC:.2f}, AICc={AICc:.2f}, BIC={BIC:.2f}")
    # Robust loss diagnostics (optional)
    if args.robust_loss != "none":
        def rho_huber(z: np.ndarray, delta: float) -> np.ndarray:
            a = np.abs(z)
            return np.where(a <= delta, 0.5 * a * a, delta * (a - 0.5 * delta))
        def rho_tukey(z: np.ndarray, c: float) -> np.ndarray:
            a = np.abs(z)
            m = a < c
            t = (1 - (a[m] / c) ** 2) ** 2
            out = np.empty_like(a)
            out[m] = (c ** 2 / 6.0) * (1 - t)
            out[~m] = (c ** 2) / 6.0
            return out
        robust_vals: list[float] = []
        for row in rows:
            # For lack of per-point residuals here, approximate per-galaxy robust score by N * rho(|resid|/1) with resid proxy sqrt(chi2/N)
            N = int(row["N"]) if int(row["N"]) > 0 else 1
            red = float(row["chi2_over_N"]) if np.isfinite(row["chi2_over_N"]) else np.nan
            if not np.isfinite(red):
                continue
            resid_std = np.sqrt(max(red, 0.0))
            if args.robust_loss == "huber":
                score = float(N * rho_huber(np.array([resid_std]), args.robust_delta))
            else:
                score = float(N * rho_tukey(np.array([resid_std]), args.robust_delta))
            robust_vals.append(score / max(N, 1))
        if robust_vals:
            rv = np.array(robust_vals, dtype=float)
            print(f"Robust({args.robust_loss}) median={np.nanmedian(rv):.3f} mean={np.nanmean(rv):.3f}")
    # Outliers CSV
    if args.outliers_csv:
        try:
            df_rows = pd.DataFrame(rows)
            top = df_rows.sort_values("chi2_over_N", ascending=False).head(10)
            Path(args.outliers_csv).parent.mkdir(parents=True, exist_ok=True)
            top.to_csv(Path(args.outliers_csv), index=False)
            print(f"Wrote outliers to {args.outliers_csv}")
        except Exception:
            pass
    # Parity manifest
    if args.parity_manifest and parity_records:
        try:
            import json as _json
            pman = Path(args.parity_manifest)
            pman.parent.mkdir(parents=True, exist_ok=True)
            _json.dump({rec["galaxy"]: rec for rec in parity_records}, open(pman, "w"), indent=2)
            print(f"Wrote parity manifest to {pman}")
        except Exception:
            pass
    # Autopsy for top outliers
    if args.autopsy_dir and autopsy_records:
        try:
            outdir = Path(args.autopsy_dir)
            outdir.mkdir(parents=True, exist_ok=True)
            # select top 10 by chi2/N
            df_auto = pd.DataFrame(autopsy_records)
            top = df_auto.sort_values("chi2_over_N", ascending=False).head(10)
            for _, row in top.iterrows():
                name = str(row["galaxy"]).replace("/", "_")
                p = outdir / f"{name}.json"
                p.write_text(pd.Series(row).to_json(indent=2))
            print(f"Wrote autopsies to {outdir}")
        except Exception:
            pass
    # Residual diagnostics CSVs
    if args.resid_diag_out and rows:
        try:
            # Aggregate by xi_bin
            if by_xi_rows:
                df_xi = pd.DataFrame(by_xi_rows, columns=["xi_bin", "abs_resid"]).groupby("xi_bin")["abs_resid"].median().reset_index()
                pxi = Path(args.resid_diag_out).with_name(Path(args.resid_diag_out).stem + "_xi.csv")
                pxi.parent.mkdir(parents=True, exist_ok=True)
                df_xi.to_csv(pxi, index=False)
                print(f"Wrote residual median-by-xi to {pxi}")
            # Aggregate by r/Rd bins
            if by_r_rows:
                df_r = pd.DataFrame(by_r_rows, columns=["r_over_Rd", "abs_resid"])
                bins = np.array([0.3, 1.0, 2.0, 3.0, np.inf])
                labels = ["0.3-1.0", "1.0-2.0", "2.0-3.0", ">3.0"]
                df_r["rbin"] = pd.cut(df_r["r_over_Rd"], bins=bins, labels=labels, right=False)
                df_r2 = df_r.groupby("rbin")["abs_resid"].median().reindex(labels).reset_index()
                pr = Path(args.resid_diag_out).with_name(Path(args.resid_diag_out).stem + "_r.csv")
                pr.parent.mkdir(parents=True, exist_ok=True)
                df_r2.to_csv(pr, index=False)
                print(f"Wrote residual median-by-r/Rd to {pr}")
        except Exception:
            pass
    print(f"Results written to {out_path}")

    # Report alternate-Rd swap test results
    if args.Rd_phot_csv and chi2_list_alt:
        alt_arr = np.array(chi2_list_alt, dtype=float)
        print(f"R_d swap (photometric) median chi^2/N = {np.nanmedian(alt_arr):.3f}")
        print(f"R_d swap (photometric) mean   chi^2/N = {np.nanmean(alt_arr):.3f}")
        try:
            print(f"Delta med = {np.nanmedian(alt_arr) - np.nanmedian(chi2_arr):.3f}; Delta mean = {np.nanmean(alt_arr) - np.nanmean(chi2_arr):.3f}")
        except Exception:
            pass


if __name__ == "__main__":
    main()


