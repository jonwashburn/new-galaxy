#!/usr/bin/env python3
"""
Pure-global evaluation (non-fitted) for ILG and MOND baselines.

Inputs:
  - active/results/sparc_master.pkl (built previously)

Outputs (repo root 'results/' directory):
  - results/bench_rs_per_galaxy.csv
  - results/bench_mond_per_galaxy.csv
  - results/bench_global_summary.csv

Policy (global-only):
  - Single global stellar M/L = 1.0 applied to v_disk
  - Fixed analytic n(r) with (A, r0[kpc], p) = (7, 8, 1.6)
  - Fixed α = 0.191, C_lag = φ^{-5}, a0 = 1.2e-10 m/s^2, g_ext = 0
  - ξ = 1 + φ^{-5} * f_gas_true**0.5 (global-only proxy)
  - ζ(r) = 1 (geometric factor disabled for simplicity)
  - Error model: σ_eff^2 = σ_obs^2 + σ0^2 + (f v_obs)^2
"""

from __future__ import annotations

import os
import math
import pickle
import pathlib
from typing import Dict, Any, List, Tuple, Optional

import numpy as np
import pandas as pd


# Constants
KPC_TO_M = 3.086e19
KM_TO_M = 1.0e3
PHI = (1.0 + 5 ** 0.5) / 2.0
C_LAG = PHI ** (-5)  # ≈ 0.090
A0 = 1.2e-10  # m/s^2
ALPHA = 0.191

# Global-only settings
GLOBAL_ML = 1.0
N_A, N_R0, N_P = 7.0, 8.0, 1.6  # analytic n(r)

# Threads bins (global-only)
THREADS_BINS = 5

# Error-model settings (global-only, mirroring paper constants)
SIGMA0 = 10.0           # km/s
F_FLOOR = 0.05          # fractional
ALPHA_BEAM = 0.3        # dimensionless
ASYM_DWARF = 0.10       # fractional of v_obs
ASYM_SPIRAL = 0.05      # fractional of v_obs
K_TURB = 0.07           # dimensionless
P_TURB = 1.3            # dimensionless
# Caps (global-only) for outer-disk error proxies (fractions of v_obs)
ASYM_CAP_FRAC = 0.15
TURB_CAP_FRAC = 0.20


def n_analytic(r_kpc: np.ndarray) -> np.ndarray:
    return 1.0 + N_A * (1.0 - np.exp(-((r_kpc / N_R0) ** N_P)))


def xi_global(f_gas_true: float) -> float:
    return 1.0 + (PHI ** -5) * (max(f_gas_true, 0.0) ** 0.5)


# Threads-informed complexity (discrete, global thresholds)
def compute_fgas_edges(master_table: Dict[str, Any], num_bins: int = 5) -> np.ndarray:
    """Compute global quantile edges for f_gas_true across the sample.

    Returns an array of length (num_bins-1) with quantile cut points.
    Deterministic and global-only.
    """
    fvals: List[float] = []
    for g in master_table.values():
        try:
            # Prefer non-kinematic proxy if available to avoid circularity
            val = g.get('f_gas_proxy', None)
            if val is None:
                val = g.get('f_gas_true', 0.0)
            fvals.append(float(val))
        except Exception:
            fvals.append(0.0)
    if len(fvals) == 0:
        return np.array([])
    # Use evenly spaced quantiles excluding 0 and 1
    qs = np.linspace(0, 1, num_bins + 1)[1:-1]
    return np.quantile(np.array(fvals), qs)


def xi_threads(f_gas_true: float, edges: np.ndarray) -> float:
    """Discrete threads factor from global f_gas quantile bins.

    - Assign bin index b \in {0,..,B-1} by global edges
    - Map to a unit interval center u = (b + 0.5)/B
    - Return xi = 1 + C_LAG * sqrt(u)
    This preserves global-only policy and introduces a discrete, auditable
    complexity proxy aligned with the Ribbons/Threads perspective.
    """
    if edges.size == 0:
        return xi_global(f_gas_true)
    # Bin index
    b = int(np.searchsorted(edges, max(f_gas_true, 0.0), side='right'))
    B = edges.size + 1
    u = (b + 0.5) / B
    return 1.0 + C_LAG * (u ** 0.5)


def compute_global_n_norm(master_table: Dict[str, Any], trim_frac: float = 0.1) -> float:
    """Compute a global normalization c_n using a trimmed-mean of per-galaxy
    disc-weighted means of n(r). For each galaxy with valid R_d, compute
    E[n(r)] under w(r) ∝ r e^{-r/Rd} on [0.05 Rd, 6 Rd], then take a
    two-sided trimmed mean across galaxies.
    """
    means: List[float] = []
    for g in master_table.values():
        try:
            Rd = float(g.get('R_d', np.nan))
            if not (np.isfinite(Rd) and Rd > 0):
                continue
            r = np.linspace(0.05 * Rd, 6.0 * Rd, 600)
            w = r * np.exp(-r / Rd)
            m = float(np.trapz(n_analytic(r) * w, r) / np.trapz(w, r))
            if np.isfinite(m) and m > 0:
                means.append(m)
        except Exception:
            continue
    if not means:
        return 1.0
    arr = np.sort(np.array(means))
    k = int(trim_frac * arr.size)
    if k * 2 >= arr.size:
        mtrim = float(np.mean(arr))
    else:
        mtrim = float(np.mean(arr[k:-k]))
    return 1.0 / mtrim if mtrim > 0 else 1.0


def compute_global_Tref(master_table: Dict[str, Any]) -> float:
    """Compute a single global reference dynamical time T_ref as the median
    of per-galaxy median T_dyn values (SI seconds) using baryonic velocities.
    """
    tvals: List[float] = []
    for g in master_table.values():
        try:
            df = g['data']
            r = df['rad'].values.astype(float)
            v_gas = df['vgas'].values.astype(float)
            v_disk = df['vdisk'].values.astype(float)
            v_bul = df['vbul'].values.astype(float)
            v_baryon = np.sqrt(v_gas ** 2 + (math.sqrt(GLOBAL_ML) * v_disk) ** 2 + v_bul ** 2)
            r_m = r * KPC_TO_M
            v_mps = v_baryon * KM_TO_M
            with np.errstate(divide='ignore', invalid='ignore'):
                T_dyn = np.where(v_mps > 0, 2.0 * math.pi * r_m / v_mps, np.nan)
            T_dyn = T_dyn[np.isfinite(T_dyn) & (T_dyn > 0)]
            if T_dyn.size:
                tvals.append(float(np.median(T_dyn)))
        except Exception:
            continue
    if len(tvals) == 0:
        return 1.0
    return float(np.median(np.array(tvals)))


def w_g_kernel(g_bar_si: np.ndarray) -> np.ndarray:
    # g_ext = 0
    term = np.maximum(g_bar_si / A0, 1e-30)  # avoid div/underflow
    return 1.0 + C_LAG * (term ** (-ALPHA) - 1.0)


def w_t_kernel(T_dyn_si: np.ndarray, T_ref_si: float) -> np.ndarray:
    term = np.maximum(T_dyn_si / max(T_ref_si, 1e-30), 1e-30)
    return 1.0 + C_LAG * (term ** (ALPHA) - 1.0)


def compute_ilg_velocity(r_kpc: np.ndarray,
                         v_gas: np.ndarray,
                         v_disk: np.ndarray,
                         v_bul: np.ndarray,
                         v_obs: np.ndarray,
                         f_gas_true: float,
                         R_d_guess: float | None = None,
                         xi_value: float | None = None,
                         c_n: float = 1.0,
                         ml: float | None = None,
                         kernel: str = 'g',
                         T_ref: float | None = None) -> np.ndarray:
    # Apply global M/L to stellar disk
    ml_use = float(GLOBAL_ML if ml is None else ml)
    v_baryon = np.sqrt(v_gas ** 2 + (math.sqrt(ml_use) * v_disk) ** 2 + v_bul ** 2)

    # g_bar and T_dyn in SI
    r_m = r_kpc * KPC_TO_M
    v_baryon_mps = v_baryon * KM_TO_M
    g_bar = np.where(r_m > 0, (v_baryon_mps ** 2) / r_m, 0.0)
    T_dyn = np.where(v_baryon_mps > 0, 2.0 * math.pi * r_m / v_baryon_mps, 0.0)

    if kernel == 't':
        tref = float(T_ref) if (T_ref is not None and T_ref > 0) else 1.0
        w_core = w_t_kernel(T_dyn, tref)
    else:
        w_core = w_g_kernel(g_bar)
    n_r = c_n * n_analytic(r_kpc)
    xi = xi_global(f_gas_true) if xi_value is None else float(xi_value)
    # Geometric factor: simple thickness proxy using R_d if available
    if R_d_guess is None or R_d_guess <= 0:
        zeta = 1.0
    else:
        hz_over_Rd = 0.25
        hz = hz_over_Rd * R_d_guess
        # clip to [0.8, 1.2] as in paper
        zeta = np.clip(1.0 + 0.5 * (hz / (r_kpc + 0.1 * R_d_guess)), 0.8, 1.2)
    w = w_core * n_r * xi * zeta

    v_model = np.sqrt(np.maximum(w, 0.0)) * v_baryon
    return v_model


def mond_simple_nu_velocity(r_kpc: np.ndarray,
                            v_gas: np.ndarray,
                            v_disk: np.ndarray,
                            v_bul: np.ndarray) -> np.ndarray:
    # Global M/L = 1.0 for fair baseline
    v_baryon = np.sqrt(v_gas ** 2 + (math.sqrt(GLOBAL_ML) * v_disk) ** 2 + v_bul ** 2)
    r_m = r_kpc * KPC_TO_M
    v_baryon_mps = v_baryon * KM_TO_M
    g_N = np.where(r_m > 0, (v_baryon_mps ** 2) / r_m, 0.0)
    y = np.maximum(g_N / A0, 1e-30)
    # Simple nu: g = nu(y) * g_N with nu(y) = 0.5 + sqrt(0.25 + 1/y)
    nu = 0.5 + np.sqrt(0.25 + 1.0 / y)
    g = nu * g_N
    v_mps = np.sqrt(np.maximum(g, 0.0) * r_m)
    return v_mps / KM_TO_M


def sigma_total_kms(r_kpc: np.ndarray,
                    v_obs: np.ndarray,
                    v_err: np.ndarray,
                    R_d_guess: float | None = None,
                    is_dwarf: bool | None = None,
                    beam_kpc: float | None = None) -> np.ndarray:
    # Base floors
    sigma = v_err ** 2 + SIGMA0 ** 2 + (F_FLOOR * v_obs) ** 2
    # Beam smearing: prefer catalog beam_kpc if provided; else heuristic from R_d
    if beam_kpc is None:
        if R_d_guess is not None and R_d_guess > 0:
            beam_kpc = 0.3 * R_d_guess
        else:
            beam_kpc = 0.6  # conservative fallback
    sigma_beam = ALPHA_BEAM * beam_kpc * v_obs / (r_kpc + beam_kpc)
    sigma += sigma_beam ** 2
    # Asymmetry term
    if is_dwarf is None:
        is_dwarf = bool(np.nanmax(v_obs) < 80.0)
    asym_frac = ASYM_DWARF if is_dwarf else ASYM_SPIRAL
    sigma_asym = asym_frac * v_obs
    # cap asymmetry in outer regions (global cap)
    sigma_asym = np.minimum(sigma_asym, ASYM_CAP_FRAC * v_obs)
    sigma += sigma_asym ** 2
    # Turbulence/warp proxy
    if R_d_guess is None or R_d_guess <= 0:
        Rd = 2.0
    else:
        Rd = R_d_guess
    sigma_turb = K_TURB * v_obs * (1.0 - np.exp(-r_kpc / Rd)) ** P_TURB
    # cap turbulence in outer disk
    sigma_turb = np.minimum(sigma_turb, TURB_CAP_FRAC * v_obs)
    sigma += sigma_turb ** 2
    return np.sqrt(np.maximum(sigma, 0.0))


def huber_loss(residuals: np.ndarray, delta: float = 1.345) -> np.ndarray:
    """Huber loss for standard residuals r; returns loss per point."""
    r = np.asarray(residuals)
    absr = np.abs(r)
    quad = 0.5 * (absr ** 2)
    lin = delta * (absr - 0.5 * delta)
    return np.where(absr <= delta, quad, lin)


def compute_metrics(v_obs: np.ndarray, v_model: np.ndarray, sig: np.ndarray) -> Dict[str, float]:
    r = (v_obs - v_model) / np.maximum(sig, 1e-9)
    chi2 = float(np.sum(r ** 2))
    hub = float(np.mean(huber_loss(r)))
    med_abs = float(np.median(np.abs(r)))
    return {
        'chi2': chi2,
        'huber_mean': hub,
        'med_abs_resid': med_abs,
    }


def eval_pure_global_cohort(master_table: Dict[str, Any], use_q1_gate: bool, min_points: int,
                            force_kernel: Optional[str] = None,
                            T_ref_override: Optional[float] = None) -> Tuple[pd.DataFrame, str]:
    rows_g: List[Dict[str, Any]] = []
    rows_t: List[Dict[str, Any]] = []
    beam_mask_factor = 0.3  # heuristic when catalog beam is unavailable
    # Global threads thresholds (discrete complexity proxy)
    fgas_edges = compute_fgas_edges(master_table, num_bins=THREADS_BINS)
    c_n = compute_global_n_norm(master_table)
    T_ref = float(T_ref_override) if (T_ref_override is not None and T_ref_override > 0) else compute_global_Tref(master_table)

    # Global morphology thresholds (non-kinematic): use medians
    sigma0_vals: List[float] = []
    fgas_vals: List[float] = []
    for g in master_table.values():
        try:
            s0 = float(g.get('Sigma_0', np.nan))
            if np.isfinite(s0):
                sigma0_vals.append(s0)
        except Exception:
            pass
        try:
            fp = float(g.get('f_gas_proxy', np.nan))
            if np.isfinite(fp):
                fgas_vals.append(fp)
        except Exception:
            pass
    sigma0_thresh = float(np.median(np.array(sigma0_vals))) if sigma0_vals else np.nan
    fgas_thresh = float(np.median(np.array(fgas_vals))) if fgas_vals else 0.5

    for name, g in master_table.items():
        # Optional Q=1 gate when available
        if use_q1_gate:
            try:
                if int(g.get('Q', 1)) != 1:
                    continue
            except Exception:
                continue
        df = g['data']
        r = df['rad'].values.astype(float)
        v_obs = df['vobs'].values.astype(float)
        v_err = df['verr'].values.astype(float)
        v_gas = df['vgas'].values.astype(float)
        v_disk = df['vdisk'].values.astype(float)
        v_bul = df['vbul'].values.astype(float)

        f_gas_true = float(g.get('f_gas_true', 0.0))

        R_d_guess = float(g.get('R_d', 2.0))
        # Apply inner-beam mask: prefer catalog beam if present; else heuristic r >= 0.3 R_d
        beam_from_cat = g.get('beam_kpc', None)
        try:
            beam_from_cat = float(beam_from_cat) if beam_from_cat is not None else None
        except Exception:
            beam_from_cat = None
        b_kpc = (beam_from_cat if (beam_from_cat is not None and beam_from_cat > 0) else
                 beam_mask_factor * R_d_guess)
        mask = np.isfinite(r) & np.isfinite(v_obs) & np.isfinite(v_err) & (r >= b_kpc)
        r = r[mask]
        v_obs = v_obs[mask]
        v_err = v_err[mask]
        v_gas = v_gas[mask]
        v_disk = v_disk[mask]
        v_bul = v_bul[mask]
        if r.size < min_points:
            continue

        # Threads-informed xi (discrete, global thresholds)
        xi_val = xi_threads(f_gas_true, fgas_edges)
        v_ilg_g = compute_ilg_velocity(r, v_gas, v_disk, v_bul, v_obs, f_gas_true,
                                       R_d_guess, xi_value=xi_val, c_n=c_n,
                                       kernel='g', T_ref=None)
        v_ilg_t = compute_ilg_velocity(r, v_gas, v_disk, v_bul, v_obs, f_gas_true,
                                       R_d_guess, xi_value=xi_val, c_n=c_n,
                                       kernel='t', T_ref=T_ref)
        v_mond = mond_simple_nu_velocity(r, v_gas, v_disk, v_bul)

        # Non-kinematic dwarf/spiral proxy: low Sigma_0 or high f_gas_proxy
        try:
            s0 = float(g.get('Sigma_0', np.nan))
        except Exception:
            s0 = np.nan
        try:
            fp = float(g.get('f_gas_proxy', np.nan))
        except Exception:
            fp = np.nan
        is_dwarf = False
        if np.isfinite(s0):
            is_dwarf = (s0 < sigma0_thresh)
        if np.isfinite(fp):
            is_dwarf = is_dwarf or (fp > fgas_thresh)
        # 2-bit galaxy word using non-kinematic proxies
        gbit = 'G1' if (np.isfinite(fp) and fp >= fgas_thresh) else 'G0'
        sbit = 'S1' if (np.isfinite(s0) and s0 >= sigma0_thresh) else 'S0'
        class_code = f"{gbit}{sbit}"
        sig = sigma_total_kms(r, v_obs, v_err, R_d_guess=R_d_guess, is_dwarf=is_dwarf,
                              beam_kpc=beam_from_cat)
        m_ilg_g = compute_metrics(v_obs, v_ilg_g, sig)
        m_ilg_t = compute_metrics(v_obs, v_ilg_t, sig)
        m_mond = compute_metrics(v_obs, v_mond, sig)

        n_pts = int(r.size)
        rows_g.append({
            'name': name,
            'N': n_pts,
            'chi2_ilg': m_ilg_g['chi2'],
            'chi2N_ilg': m_ilg_g['chi2'] / max(n_pts, 1),
            'huber_ilg': m_ilg_g['huber_mean'],
            'medabs_ilg': m_ilg_g['med_abs_resid'],
            'chi2_mond': m_mond['chi2'],
            'chi2N_mond': m_mond['chi2'] / max(n_pts, 1),
            'huber_mond': m_mond['huber_mean'],
            'medabs_mond': m_mond['med_abs_resid'],
            'class': class_code,
        })

        rows_t.append({
            'name': name,
            'N': n_pts,
            'chi2_ilg': m_ilg_t['chi2'],
            'chi2N_ilg': m_ilg_t['chi2'] / max(n_pts, 1),
            'huber_ilg': m_ilg_t['huber_mean'],
            'medabs_ilg': m_ilg_t['med_abs_resid'],
            'chi2_mond': m_mond['chi2'],
            'chi2N_mond': m_mond['chi2'] / max(n_pts, 1),
            'huber_mond': m_mond['huber_mean'],
            'medabs_mond': m_mond['med_abs_resid'],
            'class': class_code,
        })

    df_g = pd.DataFrame(rows_g).sort_values('name')
    df_t = pd.DataFrame(rows_t).sort_values('name')
    med_g = float(np.median(df_g['chi2N_ilg'])) if len(df_g) else float('inf')
    med_t = float(np.median(df_t['chi2N_ilg'])) if len(df_t) else float('inf')
    if force_kernel in ('g', 't'):
        chosen = force_kernel
    else:
        chosen = 't' if med_t < med_g else 'g'
    df = df_t if chosen == 't' else df_g
    df.attrs['kernel'] = chosen
    return df, chosen


def class_spread_metric(df: pd.DataFrame) -> float:
    """Between-class robust spread: max minus min of class median chi2N_ilg."""
    if 'class' not in df.columns or df.empty:
        return float('inf')
    meds = df.groupby('class')['chi2N_ilg'].median().values
    if meds.size == 0:
        return float('inf')
    return float(np.max(meds) - np.min(meds))


def run_anchor_scan(master_table: Dict[str, Any], tref_multipliers: List[float]) -> pd.DataFrame:
    """Scan equal-weight anchor across kernels and a small T_ref grid.
    Returns a long DataFrame with per-cohort metrics for each candidate.
    """
    # Baseline T_ref from data
    T_ref0 = compute_global_Tref(master_table)
    grid = [None]  # placeholder for w_g
    trefs = [max(T_ref0 * m, 1e-6) for m in tref_multipliers]

    records: List[Dict[str, Any]] = []
    # Evaluate w_g for both cohorts
    for cohort, q1, minpts in [('Q1', True, 7), ('FULL', False, 5)]:
        df_g, _ = eval_pure_global_cohort(master_table, use_q1_gate=q1, min_points=minpts, force_kernel='g')
        rec = {
            'kernel': 'w_g',
            'T_ref': 'n/a',
            'cohort': cohort,
            'class_spread': class_spread_metric(df_g),
            'overall_median_chi2N': float(np.median(df_g['chi2N_ilg'])) if len(df_g) else float('inf'),
        }
        records.append(rec)

    # Evaluate w_t at each T_ref for both cohorts
    for Tref in trefs:
        for cohort, q1, minpts in [('Q1', True, 7), ('FULL', False, 5)]:
            df_t, _ = eval_pure_global_cohort(master_table, use_q1_gate=q1, min_points=minpts, force_kernel='t', T_ref_override=Tref)
            rec = {
                'kernel': 'w_t',
                'T_ref': float(Tref),
                'cohort': cohort,
                'class_spread': class_spread_metric(df_t),
                'overall_median_chi2N': float(np.median(df_t['chi2N_ilg'])) if len(df_t) else float('inf'),
            }
            records.append(rec)

    df_scan = pd.DataFrame(records)
    # Determine preferred anchors per cohort by minimal class_spread
    best_q1 = df_scan[df_scan['cohort'] == 'Q1'].sort_values(['class_spread', 'overall_median_chi2N']).head(1)
    best_full = df_scan[df_scan['cohort'] == 'FULL'].sort_values(['class_spread', 'overall_median_chi2N']).head(1)
    chosen_kernel = 'w_g'
    chosen_Tref = None
    if not best_q1.empty and not best_full.empty:
        k_q1 = best_q1.iloc[0]['kernel']
        k_full = best_full.iloc[0]['kernel']
        if (k_q1 == 'w_t') and (k_full == 'w_t'):
            Tq = best_q1.iloc[0]['T_ref']
            Tf = best_full.iloc[0]['T_ref']
            if isinstance(Tq, float) and isinstance(Tf, float) and (abs(Tq - Tf) / max(Tf, 1e-9) < 0.1):
                # both cohorts clearly prefer w_t with similar T_ref (within 10%)
                chosen_kernel = 'w_t'
                chosen_Tref = float(0.5 * (Tq + Tf))
    df_scan.attrs['chosen_kernel'] = chosen_kernel
    if chosen_Tref is not None:
        df_scan.attrs['chosen_Tref'] = chosen_Tref
    return df_scan


def main() -> None:
    base = pathlib.Path(__file__).resolve().parents[2]
    pkl_path = base / 'active' / 'results' / 'sparc_master.pkl'
    out_dir = base / 'results'
    out_dir.mkdir(parents=True, exist_ok=True)

    if not pkl_path.exists():
        raise FileNotFoundError(f"Missing master table: {pkl_path}")

    with open(pkl_path, 'rb') as f:
        master_table: Dict[str, Any] = pickle.load(f)

    # Optional derive-only mode through env vars (global-only, fixed anchor)
    derive_mode = os.environ.get('ILG_DERIVE_ONLY', '0') == '1'
    fixed_kernel = os.environ.get('ILG_ANCHOR_KERNEL', '').strip()  # 'w_g' or 'w_t'
    fixed_Tref = os.environ.get('ILG_TREF', '').strip()
    T_ref_override = float(fixed_Tref) if fixed_Tref not in ('', None) else None
    if derive_mode:
        # lock kernel per policy: default w_g; allow w_t only if explicitly provided
        if fixed_kernel not in ('w_g', 'w_t'):
            fixed_kernel = 'w_g'
        force_kernel = 'g' if fixed_kernel == 'w_g' else 't'
        df_full, kernel_full = eval_pure_global_cohort(master_table, use_q1_gate=False, min_points=5,
                                                       force_kernel=force_kernel, T_ref_override=T_ref_override)
        df_q1, kernel_q1 = eval_pure_global_cohort(master_table, use_q1_gate=True, min_points=7,
                                                   force_kernel=force_kernel, T_ref_override=T_ref_override)
    else:
        # Full-sample and Q=1 cohorts (auto-select kernel by median chi2N)
        df_full, kernel_full = eval_pure_global_cohort(master_table, use_q1_gate=False, min_points=5)
        df_q1, kernel_q1 = eval_pure_global_cohort(master_table, use_q1_gate=True, min_points=7)

    # Write per-galaxy CSVs (Q=1 as main; full-sample additional)
    df = df_q1
    df_rs = df[['name', 'N', 'chi2_ilg', 'chi2N_ilg', 'huber_ilg', 'medabs_ilg']].rename(columns={
        'chi2_ilg': 'chi2', 'chi2N_ilg': 'chi2N'
    })
    df_mond = df[['name', 'N', 'chi2_mond', 'chi2N_mond', 'huber_mond', 'medabs_mond']].rename(columns={
        'chi2_mond': 'chi2', 'chi2N_mond': 'chi2N'
    })

    df_rs.to_csv(out_dir / 'bench_rs_per_galaxy.csv', index=False)
    df_mond.to_csv(out_dir / 'bench_mond_per_galaxy.csv', index=False)

    # Summary (both cohorts)
    chosen_kernel = df_q1.attrs.get('kernel', 'g')
    kernel_tag = 'w_t' if chosen_kernel == 't' else 'w_g'
    policy = (
        f'pure-global (no per-galaxy tuning); kernel={kernel_tag}; '
        'analytic n(r) with global disc-weight normalization; global M/L=1.0; '
        f'ξ_threads: f_gas discretized by global {THREADS_BINS}-tiles; ζ with h_z/R_d=0.25; '
        'errors σ0, fractional floor, beam-proxy/cat-beam when available, asymmetry, turbulence; '
        'inner-beam mask uses catalog beam when available, else r>=0.3 R_d'
    )
    if derive_mode:
        policy += '; derive-only mode ON; fixed anchor via ILG_ANCHOR_KERNEL/ILG_TREF'
    def cohort_summary(df_cohort: pd.DataFrame, label: str, kernel_tag: str) -> Dict[str, Any]:
        return {
            'cohort': label,
            'kernel': kernel_tag,
            'N_ilg': int(len(df_cohort)),
            'median_chi2N_ilg': float(np.median(df_cohort['chi2N_ilg'])),
            'mean_chi2N_ilg': float(np.mean(df_cohort['chi2N_ilg'])),
            'median_huber_ilg': float(np.median(df_cohort['huber_ilg'])),
            'median_medabs_ilg': float(np.median(df_cohort['medabs_ilg'])),
            'policy': policy,
        }

    summaries: List[Dict[str, Any]] = []
    summaries.append(cohort_summary(df_q1, 'Q1', 'w_t' if kernel_q1 == 't' else 'w_g'))
    summaries.append(cohort_summary(df_full, 'FULL', 'w_t' if kernel_full == 't' else 'w_g'))
    # Write class summary (per cohort) and overall summary
    # Per-cohort class medians
    def write_class_summary(df: pd.DataFrame, label: str) -> None:
        if 'class' in df.columns and len(df):
            cls = df.groupby('class').agg(
                N=('name','count'),
                median_chi2N_ilg=('chi2N_ilg','median'),
                median_huber_ilg=('huber_ilg','median'),
                median_medabs_ilg=('medabs_ilg','median'),
            ).reset_index()
            cls['cohort'] = label
            path = out_dir / f'class_summary_{label}.csv'
            cls.to_csv(path, index=False)
    write_class_summary(df_q1, 'Q1')
    write_class_summary(df_full, 'FULL')

    pd.DataFrame(summaries).to_csv(out_dir / 'bench_global_summary.csv', index=False)

    print("Wrote:")
    for p in [
        out_dir / 'bench_rs_per_galaxy.csv',
        out_dir / 'bench_mond_per_galaxy.csv',
        out_dir / 'bench_global_summary.csv',
    ]:
        print(f"  - {p}")


if __name__ == '__main__':
    main()


