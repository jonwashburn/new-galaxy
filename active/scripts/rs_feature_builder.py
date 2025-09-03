#!/usr/bin/env python3
"""
RS Feature Builder (global-only; drop-in CLI)

Subcommands:
  thresholds   Build global ξ quintile thresholds from a list of Σ_b maps
  features2d   Derive fields/profiles/features from a single 2D Σ_b map
  features3d   Derive fields/profiles/features from a 3D ρ_b cube (projects to Σ)

Artifacts:
  - fields.npz   → traceS, ell_rec_kpc, anisotropy, D_iso
  - profiles.npz → r_kpc, n_of_r, zeta_of_r
  - features.json→ Rd_kpc, xi, xi_bin, g_ext_SI, constants, provenance
  - thresholds.json (thresholds subcommand output)

All quantities are derived from baryons (Σ or ρ) and optional environment
neighbors (M_Msun, D_kpc). No v_obs, no per‑galaxy tuning. Global-only policy:
ξ thresholds computed once and reused.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, Any, Tuple, List

import numpy as np
import pandas as pd


# Constants
PHI = (1.0 + np.sqrt(5.0)) / 2.0
C_LAG = PHI ** (-5.0)
A0_SI = 1.2e-10
G_SI = 6.67430e-11
MSUN_SI = 1.98847e30
KPC_SI = 3.085677581e19


def smooth_gaussian_fft(img: np.ndarray, sigma_px: float) -> np.ndarray:
    if sigma_px <= 0.0:
        return img.copy()
    ny, nx = img.shape
    y = np.arange(ny)
    x = np.arange(nx)
    Y, X = np.meshgrid(y, x, indexing="ij")
    yy = np.minimum(Y, ny - Y)
    xx = np.minimum(X, nx - X)
    R2 = (xx ** 2 + yy ** 2).astype(np.float64)
    g = np.exp(-0.5 * R2 / max(sigma_px ** 2, 1e-12))
    g /= np.sum(g)
    F = np.fft.fft2(img)
    G = np.fft.fft2(g)
    return np.fft.ifft2(F * G).real


def gradient_central(f: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    fx = 0.5 * (np.roll(f, -1, axis=1) - np.roll(f, 1, axis=1))
    fy = 0.5 * (np.roll(f, -1, axis=0) - np.roll(f, 1, axis=0))
    return fx, fy


def build_structure_sigma(sigma_b: np.ndarray, smooth_sigma_px: float = 2.0) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    eps = 1e-12
    s_log = np.log(np.maximum(sigma_b, eps))
    sx, sy = gradient_central(s_log)
    sxx = smooth_gaussian_fft(sx * sx, smooth_sigma_px)
    syy = smooth_gaussian_fft(sy * sy, smooth_sigma_px)
    sxy = smooth_gaussian_fft(sx * sy, smooth_sigma_px)
    trace = sxx + syy
    return sxx, syy, sxy, trace


def derive_Rd(sigma_b: np.ndarray, dx_kpc: float) -> float:
    ny, nx = sigma_b.shape
    y, x = np.indices((ny, nx))
    xc, yc = (nx - 1) / 2.0, (ny - 1) / 2.0
    Rpix = np.hypot(x - xc, y - yc)
    r_bins = np.arange(1, min(nx, ny) // 2)
    prof = []
    for r in r_bins:
        mask = (Rpix >= r - 0.5) & (Rpix < r + 0.5)
        if np.any(mask):
            prof.append(float(np.nanmedian(sigma_b[mask])))
        else:
            prof.append(np.nan)
    prof = np.array(prof)
    # Fit log Σ ≈ a - r/Rd by a simple slope proxy on central band
    rp_kpc = r_bins * dx_kpc
    mask = np.isfinite(prof) & (rp_kpc > 0.5 * np.nanmax(rp_kpc) / 6) & (rp_kpc < 3 * np.nanmax(rp_kpc) / 6)
    if np.sum(mask) < 5:
        return max(np.nanmax(rp_kpc) / 6.0, 0.5)
    yv = np.log(np.maximum(prof[mask], 1e-12))
    xv = rp_kpc[mask]
    A = np.vstack([xv, np.ones_like(xv)]).T
    # Least squares
    m, c = np.linalg.lstsq(A, yv, rcond=None)[0]
    Rd = max(-1.0 / m, 0.5) if m < 0 else max(np.nanmax(rp_kpc) / 6.0, 0.5)
    return Rd


def n_of_r(r_over_Rd: np.ndarray, A: float = 7.0, p: float = 1.6) -> np.ndarray:
    x = np.maximum(r_over_Rd, 0.0)
    return 1.0 + A * (1.0 - np.exp(-(x ** p)))


def eigvals2x2(sxx: np.ndarray, syy: np.ndarray, sxy: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    tr = sxx + syy
    det = sxx * syy - sxy * sxy
    disc = np.maximum(tr * tr - 4.0 * det, 0.0)
    root = np.sqrt(disc)
    lam_max = 0.5 * (tr + root)
    lam_min = 0.5 * (tr - root)
    return lam_min, lam_max


def zeta_from_anisotropy(aniso: np.ndarray) -> np.ndarray:
    # Geometry gate per spec: clip{ 1 + C_LAG * (anisotropy - 1) } in [0.8, 1.2]
    z = 1.0 + C_LAG * (np.clip(aniso, 1e-6, 1.0) - 1.0)
    return np.clip(z, 0.8, 1.2)


def complexity_scalar(trace: np.ndarray, R_d: float, dx_kpc: float) -> float:
    ny, nx = trace.shape
    y, x = np.indices((ny, nx))
    xc, yc = (nx - 1) / 2.0, (ny - 1) / 2.0
    Rpix = np.hypot(x - xc, y - yc)
    rp_kpc = Rpix * dx_kpc
    mask = (rp_kpc >= 0.5 * R_d) & (rp_kpc <= 2.5 * R_d)
    vals = trace[mask]
    return float(np.nanmedian(vals)) if vals.size > 0 else float(np.nanmean(trace))


def xi_from_quintile(u_center: float) -> float:
    return 1.0 + C_LAG * np.sqrt(max(0.0, min(1.0, u_center)))


def radial_profile(img: np.ndarray, dx_kpc: float) -> Tuple[np.ndarray, np.ndarray]:
    ny, nx = img.shape
    y, x = np.indices((ny, nx))
    xc, yc = (nx - 1) / 2.0, (ny - 1) / 2.0
    Rpix = np.hypot(x - xc, y - yc)
    rmax = int(min(nx, ny) // 2)
    r_vals = []
    v_vals = []
    for r in range(1, rmax):
        mask = (Rpix >= r - 0.5) & (Rpix < r + 0.5)
        if np.any(mask):
            v_vals.append(float(np.nanmedian(img[mask])))
            r_vals.append(r * dx_kpc)
    if len(r_vals) == 0:
        return np.zeros(0, dtype=float), np.zeros(0, dtype=float)
    return np.array(r_vals, dtype=float), np.array(v_vals, dtype=float)


def load_sigma_2d(path: Path) -> np.ndarray:
    if path.suffix.lower() == ".npz":
        data = np.load(path)
        if "Sigma" in data:
            return data["Sigma"]
        if "Sigma_b" in data:
            return data["Sigma_b"]
        # fallback: first array
        keys = list(data.keys())
        return data[keys[0]]
    else:
        arr = np.load(path)
        return arr


def load_rho_3d(path: Path) -> np.ndarray:
    if path.suffix.lower() == ".npz":
        data = np.load(path)
        if "rho" in data:
            return data["rho"]
        if "rho_b" in data:
            return data["rho_b"]
        keys = list(data.keys())
        return data[keys[0]]
    else:
        arr = np.load(path)
        return arr


def compute_gext_from_env(env_csv: str) -> float:
    if not env_csv:
        return 0.0
    try:
        df = pd.read_csv(env_csv)
    except Exception:
        return 0.0
    if df.empty:
        return 0.0
    M = np.array(df.get("M_Msun", np.zeros(len(df))), dtype=float)
    D = np.array(df.get("D_kpc", np.zeros(len(df))), dtype=float)
    with np.errstate(divide="ignore", invalid="ignore"):
        g = G_SI * (M * MSUN_SI) / np.maximum((D * KPC_SI) ** 2, 1e-30)
    g = np.nan_to_num(g, nan=0.0, posinf=0.0, neginf=0.0)
    return float(np.sum(g))


def build_fields_and_profiles_2d(Sigma: np.ndarray, dx_kpc: float, lambda_rec_kpc: float,
                                 A: float, p: float) -> Tuple[Dict[str, np.ndarray], Dict[str, np.ndarray], Dict[str, float]]:
    sigma_px = max(lambda_rec_kpc / max(dx_kpc, 1e-9), 0.0)
    sxx, syy, sxy, trace = build_structure_sigma(Sigma, smooth_sigma_px=sigma_px)
    lam_min, lam_max = eigvals2x2(sxx, syy, sxy)
    with np.errstate(divide="ignore", invalid="ignore"):
        anis = np.sqrt(np.clip(lam_min, 0.0, None) / np.maximum(lam_max, 1e-12))
    anis = np.nan_to_num(anis, nan=1.0, posinf=1.0, neginf=1.0)
    D_iso = 1.0 / np.maximum(1.0 + 0.5 * trace, 1e-6)
    ell_rec_kpc = lambda_rec_kpc / np.sqrt(np.maximum(1.0 + trace, 1e-9))
    zeta_local = zeta_from_anisotropy(anis)

    R_d_kpc = derive_Rd(Sigma, dx_kpc)
    r_kpc, zeta_r = radial_profile(zeta_local, dx_kpc)
    r_over_Rd = r_kpc / max(R_d_kpc, 1e-9)
    n_r = n_of_r(r_over_Rd, A=A, p=p)

    fields = {
        "traceS": trace.astype(np.float32),
        "ell_rec_kpc": ell_rec_kpc.astype(np.float32),
        "anisotropy": anis.astype(np.float32),
        "D_iso": D_iso.astype(np.float32),
    }
    profiles = {
        "r_kpc": r_kpc.astype(np.float32),
        "n_of_r": n_r.astype(np.float32),
        "zeta_of_r": zeta_r.astype(np.float32),
    }
    scalars = {
        "Rd_kpc": float(R_d_kpc),
    }
    return fields, profiles, scalars


def cmd_thresholds(args: argparse.Namespace) -> None:
    paths = [p.strip() for p in Path(args.inputs).read_text().splitlines() if p.strip() and not p.strip().startswith("#")]
    cvals: List[float] = []
    for p in paths:
        Sigma = load_sigma_2d(Path(p))
        fields, profiles, scalars = build_fields_and_profiles_2d(Sigma, dx_kpc=args.pixscale_kpc,
                                                                 lambda_rec_kpc=args.lambda_rec_kpc,
                                                                 A=args.A, p=args.p)
        trace = fields["traceS"]
        c = complexity_scalar(trace, scalars["Rd_kpc"], args.pixscale_kpc)
        cvals.append(float(c))
    if len(cvals) == 0:
        thresholds = []
    else:
        arr = np.array(cvals, dtype=float)
        thresholds = [float(np.nanquantile(arr, q)) for q in [0.2, 0.4, 0.6, 0.8]]
    out = {
        "thresholds": thresholds,
        "B": 5,
        "sample_size": len(cvals),
        "pixscale_kpc": args.pixscale_kpc,
        "lambda_rec_kpc": args.lambda_rec_kpc,
        "A": args.A,
        "p": args.p,
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    with open(args.out, "w") as f:
        json.dump(out, f, indent=2)
    print(f"Wrote thresholds to {args.out}")


def load_thresholds(thr_path: str) -> Tuple[List[float], int]:
    data = json.loads(Path(thr_path).read_text())
    thresholds = data.get("thresholds", [])
    B = int(data.get("B", 5))
    return thresholds, B


def assign_xi(c_val: float, thresholds: List[float], B: int) -> Tuple[float, int, float]:
    if not thresholds:
        return xi_from_quintile(0.5), 2, 0.5
    bins = int(np.digitize([c_val], np.array(thresholds), right=False)[0])
    u_center = (bins + 0.5) / float(B)
    return xi_from_quintile(u_center), bins, u_center


def cmd_features2d(args: argparse.Namespace) -> None:
    Sigma = load_sigma_2d(Path(args.input))
    fields, profiles, scalars = build_fields_and_profiles_2d(Sigma, dx_kpc=args.pixscale_kpc,
                                                             lambda_rec_kpc=args.lambda_rec_kpc,
                                                             A=args.A, p=args.p)
    thresholds, B = load_thresholds(args.thresholds)
    c_val = complexity_scalar(fields["traceS"], scalars["Rd_kpc"], args.pixscale_kpc)
    xi, xi_bin, u_center = assign_xi(c_val, thresholds, B)
    g_ext = compute_gext_from_env(args.env_csv or "")

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(out_dir / "fields.npz", **fields)
    np.savez_compressed(out_dir / "profiles.npz", **profiles)
    features = {
        "Rd_kpc": scalars["Rd_kpc"],
        "xi": xi,
        "xi_bin": int(xi_bin),
        "u_center": float(u_center),
        "g_ext_SI": float(g_ext),
        "phi": float(PHI),
        "C_lag": float(C_LAG),
        "a0_SI": float(A0_SI),
        "pixscale_kpc": float(args.pixscale_kpc),
        "lambda_rec_kpc": float(args.lambda_rec_kpc),
        "A": float(args.A),
        "p": float(args.p),
        "thresholds_file": str(Path(args.thresholds).resolve()),
        "provenance": {
            "input": str(Path(args.input).resolve()),
        },
    }
    with open(out_dir / "features.json", "w") as f:
        json.dump(features, f, indent=2)
    print(f"Wrote features to {out_dir}")


def cmd_features3d(args: argparse.Namespace) -> None:
    rho = load_rho_3d(Path(args.input))
    # Project to Σ for gates/profiles (sum along z)
    if rho.ndim != 3:
        raise ValueError("3D input must be a 3D array or NPZ with 'rho'/'rho_b'")
    Sigma = np.sum(rho, axis=0)
    fields, profiles, scalars = build_fields_and_profiles_2d(Sigma, dx_kpc=args.pixscale_kpc,
                                                             lambda_rec_kpc=args.lambda_rec_kpc,
                                                             A=args.A, p=args.p)
    thresholds, B = load_thresholds(args.thresholds)
    c_val = complexity_scalar(fields["traceS"], scalars["Rd_kpc"], args.pixscale_kpc)
    xi, xi_bin, u_center = assign_xi(c_val, thresholds, B)
    g_ext = compute_gext_from_env(args.env_csv or "")

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(out_dir / "fields.npz", **fields)
    np.savez_compressed(out_dir / "profiles.npz", **profiles)
    features = {
        "Rd_kpc": scalars["Rd_kpc"],
        "xi": xi,
        "xi_bin": int(xi_bin),
        "u_center": float(u_center),
        "g_ext_SI": float(g_ext),
        "phi": float(PHI),
        "C_lag": float(C_LAG),
        "a0_SI": float(A0_SI),
        "pixscale_kpc": float(args.pixscale_kpc),
        "lambda_rec_kpc": float(args.lambda_rec_kpc),
        "A": float(args.A),
        "p": float(args.p),
        "thresholds_file": str(Path(args.thresholds).resolve()),
        "provenance": {
            "input": str(Path(args.input).resolve()),
        },
    }
    with open(out_dir / "features.json", "w") as f:
        json.dump(features, f, indent=2)
    print(f"Wrote features to {out_dir}")


def main():
    ap = argparse.ArgumentParser(description="RS Feature Builder (global-only; CLI)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    ap_thr = sub.add_parser("thresholds", help="Build global ξ thresholds from Σ maps list")
    ap_thr.add_argument("--inputs", type=str, required=True, help="Text file listing Σ map paths (npz/npy), one per line")
    ap_thr.add_argument("--pixscale_kpc", type=float, required=True)
    ap_thr.add_argument("--lambda_rec_kpc", type=float, required=True)
    ap_thr.add_argument("--A", type=float, default=7.0)
    ap_thr.add_argument("--p", type=float, default=1.6)
    ap_thr.add_argument("--out", type=str, required=True)
    ap_thr.set_defaults(func=cmd_thresholds)

    ap_f2 = sub.add_parser("features2d", help="Derive features from a single 2D Σ map")
    ap_f2.add_argument("--input", type=str, required=True)
    ap_f2.add_argument("--pixscale_kpc", type=float, required=True)
    ap_f2.add_argument("--lambda_rec_kpc", type=float, required=True)
    ap_f2.add_argument("--thresholds", type=str, required=True)
    ap_f2.add_argument("--A", type=float, default=7.0)
    ap_f2.add_argument("--p", type=float, default=1.6)
    ap_f2.add_argument("--env_csv", type=str, default="")
    ap_f2.add_argument("--out_dir", type=str, required=True)
    ap_f2.set_defaults(func=cmd_features2d)

    ap_f3 = sub.add_parser("features3d", help="Derive features from a 3D ρ cube (projects to Σ)")
    ap_f3.add_argument("--input", type=str, required=True)
    ap_f3.add_argument("--pixscale_kpc", type=float, required=True)
    ap_f3.add_argument("--lambda_rec_kpc", type=float, required=True)
    ap_f3.add_argument("--thresholds", type=str, required=True)
    ap_f3.add_argument("--A", type=float, default=7.0)
    ap_f3.add_argument("--p", type=float, default=1.6)
    ap_f3.add_argument("--env_csv", type=str, default="")
    ap_f3.add_argument("--out_dir", type=str, required=True)
    ap_f3.set_defaults(func=cmd_features3d)

    args = ap.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()


