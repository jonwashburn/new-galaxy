#!/usr/bin/env python3
"""
SPARC 3D proxy runner (global-only):
- Builds a simple 3D baryon density ρ_b(x,y,z) per galaxy from catalog R_d and component ratios.
- Runs the 3D ILG kernel (matrix-free CG) to obtain K(x,y,z).
- Azimuthally averages the mid-plane K to w(r) at SPARC radii and forms v_model(r).
- Computes reduced χ^2/N with the shared error model.

Outputs: per-galaxy CSVs and a summary CSV.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Dict, Any, Optional, Set, Tuple

import numpy as np
import pandas as pd

sys.path.append(str(Path(__file__).resolve().parents[2]))
from active.scripts.ilg_3d_kernel import (
    fft_poisson_3d,
    grad3_central,
    build_RS_coeffs,
    apply_operator_3d_iso,
    apply_operator_3d_aniso,
    cg_solve_3d,
    azimuthal_vr_midplane,
)


# Error model constants
SIGMA0 = 10.0
F_FRAC = 0.05
ALPHA_BEAM = 0.3
K_TURB = 0.07
P_TURB = 1.3
V_DWARF_MAX = 80.0
PHI = (1.0 + np.sqrt(5.0)) / 2.0
ALPHA = 0.5 * (1.0 - 1.0 / PHI)
A0_SI = 1.2e-10


def resize_bilinear(img: np.ndarray, new_h: int, new_w: int) -> np.ndarray:
    h, w = img.shape
    if h == new_h and w == new_w:
        return img.copy()
    # Normalized src coordinates
    y = np.linspace(0, h - 1, new_h)
    x = np.linspace(0, w - 1, new_w)
    y0 = np.floor(y).astype(int); y1 = np.clip(y0 + 1, 0, h - 1)
    x0 = np.floor(x).astype(int); x1 = np.clip(x0 + 1, 0, w - 1)
    wy = (y - y0)[..., None]
    wx = (x - x0)[None, ...]
    Ia = img[y0[:, None], x0[None, :]]
    Ib = img[y0[:, None], x1[None, :]]
    Ic = img[y1[:, None], x0[None, :]]
    Id = img[y1[:, None], x1[None, :]]
    top = Ia * (1 - wx) + Ib * wx
    bot = Ic * (1 - wx) + Id * wx
    return top * (1 - wy) + bot * wy


def try_load_precomputed(features_root: Optional[str], galaxy_name: str) -> Optional[Tuple[np.ndarray, float, float, Optional[np.ndarray]]]:
    if not features_root:
        return None


def lensing_from_potential_2d(psi: np.ndarray, dx: float, dy: float) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    # First derivatives (deflection)
    dpsi_dx = 0.5 * (np.roll(psi, -1, axis=1) - np.roll(psi, 1, axis=1)) / max(dx, 1e-12)
    dpsi_dy = 0.5 * (np.roll(psi, -1, axis=0) - np.roll(psi, 1, axis=0)) / max(dy, 1e-12)
    # Second derivatives
    psi_xx = (np.roll(psi, -1, axis=1) - 2.0 * psi + np.roll(psi, 1, axis=1)) / max(dx * dx, 1e-24)
    psi_yy = (np.roll(psi, -1, axis=0) - 2.0 * psi + np.roll(psi, 1, axis=0)) / max(dy * dy, 1e-24)
    psi_xy = (np.roll(np.roll(psi, -1, axis=0), -1, axis=1)
              - np.roll(psi, -1, axis=0)
              - np.roll(psi, -1, axis=1)
              + psi) / max(dx * dy, 1e-24)
    # Weak-lensing-like fields (unnormalized, prototype units)
    kappa_star = 0.5 * (psi_xx + psi_yy)
    gamma1 = 0.5 * (psi_xx - psi_yy)
    gamma2 = psi_xy
    return dpsi_dx, dpsi_dy, kappa_star, gamma1, gamma2
    safe = galaxy_name.replace("/", "_").replace(" ", "_")
    base = Path(features_root) / safe
    fields_path = base / "fields.npz"
    feat_json = base / "features.json"
    if not fields_path.exists() or not feat_json.exists():
        # try unsanitized name
        base2 = Path(features_root) / galaxy_name
        fields_path = base2 / "fields.npz"
        feat_json = base2 / "features.json"
        if not fields_path.exists() or not feat_json.exists():
            return None
    try:
        fields = np.load(fields_path)
        D_iso_2d = fields["D_iso"].astype(np.float64)
        ell_kpc_2d = fields["ell_rec_kpc"].astype(np.float64)
        with open(feat_json, "r") as f:
            meta = pd.read_json(f, typ="series").to_dict()
        g_ext = float(meta.get("g_ext_SI", 0.0))
        pixscale_kpc = float(meta.get("pixscale_kpc", 0.5))
        # return (c_field_2d_kpc2, g_ext_SI, pixscale_kpc)
        c2d = (np.maximum(ell_kpc_2d, 0.0) ** 2) * np.maximum(D_iso_2d, 0.0)
        return c2d, g_ext, pixscale_kpc, ell_kpc_2d
    except Exception:
        return None


def load_master_table(path: Path) -> Dict[str, Dict[str, Any]]:
    import pickle
    with open(path, "rb") as f:
        return pickle.load(f)


def get_master_path() -> Path:
    for p in [
        Path("active/results/sparc_master.pkl"),
        Path("sparc_master.pkl"),
        Path("galaxy-rotation/results/ledger_final_combined_results.pkl"),
    ]:
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


def build_rho_3d(nx: int, ny: int, nz: int, lx: float, ly: float, lz: float,
                 R_d: float, gas_frac: float, bulge_frac: float) -> Tuple[np.ndarray, float, float, float]:
    dx = lx / nx; dy = ly / ny; dz = lz / nz
    x = np.linspace(-0.5 * lx + 0.5 * dx, 0.5 * lx - 0.5 * dx, nx)
    y = np.linspace(-0.5 * ly + 0.5 * dy, 0.5 * ly - 0.5 * dy, ny)
    z = np.linspace(-0.5 * lz + 0.5 * dz, 0.5 * lz - 0.5 * dz, nz)
    X, Y, Z = np.meshgrid(x, y, z, indexing="xy")
    R = np.sqrt(X ** 2 + Y ** 2)
    # Set vertical scale height and bulge scale
    hz = max(0.2 * R_d, 0.05)
    a_b = max(0.2 * R_d, 0.05)
    disk = np.exp(-R / max(R_d, 1e-6)) * (1.0 / np.cosh(Z / hz)) ** 2
    gas = np.exp(-R / max(1.7 * R_d, 1e-6)) * (1.0 / np.cosh(Z / (1.5 * hz))) ** 2
    r3 = np.sqrt(R ** 2 + Z ** 2)
    bulge = 1.0 / np.maximum(r3 * (r3 + a_b) ** 3, 1e-6)
    gas_w = np.clip(gas_frac, 0.0, 0.8)
    bulge_w = np.clip(bulge_frac, 0.0, 0.8)
    disk_w = np.clip(1.0 - gas_w - bulge_w, 0.0, 1.0)
    rho = disk_w * disk + gas_w * gas + bulge_w * bulge
    rho /= np.maximum(np.nanmax(rho), 1e-12)
    return rho.astype(np.float64), dx, dy, dz


def main():
    ap = argparse.ArgumentParser(description="SPARC 3D proxy runner for ILG kernel (global-only)")
    ap.add_argument("--master", type=str, default="", help="Path to SPARC master pickle")
    ap.add_argument("--subset_csv", type=str, default="results/bench_rs_per_galaxy.csv")
    ap.add_argument("--limit", type=int, default=20, help="Max galaxies to run (for speed)")
    ap.add_argument("--ml_disk", type=float, default=1.0)
    ap.add_argument("--nx", type=int, default=32)
    ap.add_argument("--ny", type=int, default=32)
    ap.add_argument("--nz", type=int, default=32)
    ap.add_argument("--box_factor_xy", type=float, default=8.0, help="Half-box in R_d units for x,y")
    ap.add_argument("--box_factor_z", type=float, default=2.0, help="Half-box in R_d units for z")
    ap.add_argument("--smooth_sigma_vox", type=float, default=1.0)
    ap.add_argument("--out_dir", type=str, default="results/ilg3d_sparc")
    ap.add_argument("--anisotropic", action="store_true")
    ap.add_argument("--features_root", type=str, default="", help="Root dir containing per-galaxy features/{fields.npz,features.json}")
    # Ablations
    ap.add_argument("--ablate_K1", action="store_true", help="Set K=1 (null kernel)")
    ap.add_argument("--ablate_D_identity", action="store_true", help="Set D=I (identity diffusion)")
    ap.add_argument("--ablate_gext0", action="store_true", help="Force g_ext=0 (f_ext=1)")
    ap.add_argument("--ablate_const_sigma", action="store_true", help="Use constant sigma_eff = SIGMA0")
    ap.add_argument("--ablate_no_inner_mask", action="store_true", help="Disable inner-beam mask (b_kpc=0)")
    # Permutation test (shuffle features assignment across galaxies)
    ap.add_argument("--permute_features", action="store_true", help="Randomly permute features assignment across galaxies")
    ap.add_argument("--permute_seed", type=int, default=42)
    ap.add_argument("--skip_existing", action="store_true", help="Skip galaxies that already have per-galaxy CSV in out_dir")
    ap.add_argument("--exclude_csv", type=str, default="", help="Comma-separated CSVs with a 'galaxy' column to exclude")
    # Convergence study (optional)
    ap.add_argument("--convergence_out", type=str, default="", help="If set, compute grid-convergence metrics and write CSV here")
    ap.add_argument("--convergence_grids", type=str, default="32,48,64,96", help="Comma-separated grid sizes to compare (nx=ny=nz)")
    ap.add_argument("--convergence_names_csv", type=str, default="", help="CSV with 'galaxy' column listing names to include in convergence study")
    args = ap.parse_args()

    mpath = Path(args.master) if args.master else get_master_path()
    master = load_master_table(mpath)
    subset = load_subset_names(args.subset_csv)
    if subset:
        master = {k: v for k, v in master.items() if str(k) in subset}

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = []
    count = 0

    # Build exclusion set from provided CSVs
    exclude: Set[str] = set()
    if args.exclude_csv:
        for p in [s.strip() for s in args.exclude_csv.split(",") if s.strip()]:
            try:
                df_ex = pd.read_csv(p)
                col = "galaxy" if "galaxy" in df_ex.columns else (df_ex.columns[0] if len(df_ex.columns) > 0 else None)
                if col:
                    exclude |= set(map(str, df_ex[col].astype(str).tolist()))
            except Exception:
                pass

    # Build permutation mapping if requested
    perm_map: Optional[Dict[str, str]] = None
    if args.permute_features and args.features_root:
        keys = sorted([str(k) for k in master.keys()])
        import numpy as _np
        rng = _np.random.default_rng(args.permute_seed)
        perm = keys.copy()
        rng.shuffle(perm)
        perm_map = {k: p for k, p in zip(keys, perm)}

    # Convergence names selection (optional)
    conv_names: Optional[Set[str]] = None
    if args.convergence_out and args.convergence_names_csv:
        try:
            dfc = pd.read_csv(args.convergence_names_csv)
            col = "galaxy" if "galaxy" in dfc.columns else (dfc.columns[0] if len(dfc.columns) > 0 else None)
            if col:
                conv_names = set(map(str, dfc[col].astype(str).tolist()))
        except Exception:
            conv_names = None

    def compute_vcirc_for_grid(name: str, df: pd.DataFrame, R_d: float, nx: int, anisotropic: bool) -> Tuple[np.ndarray, np.ndarray]:
        r = df["rad"].to_numpy(float)
        v_gas = df["vgas"].to_numpy(float)
        v_disk = df["vdisk"].to_numpy(float)
        v_bul = df["vbul"].to_numpy(float)
        v_bar = baryonic_speed(v_gas, v_disk, v_bul, upsilon_star=args.ml_disk)
        gas_frac = float(np.nanmedian(np.where(v_bar > 0, (v_gas ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        bulge_frac = float(np.nanmedian(np.where(v_bar > 0, (v_bul ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        gas_frac = np.clip(gas_frac, 0.0, 0.8)
        bulge_frac = np.clip(bulge_frac, 0.0, 0.8)
        # Build grid dims and box
        ny = nx; nz = nx
        lx = 2.0 * args.box_factor_xy * R_d
        ly = 2.0 * args.box_factor_xy * R_d
        lz = 2.0 * args.box_factor_z * max(0.2 * R_d, 0.05)
        rho, dx, dy, dz = build_rho_3d(nx, ny, nz, lx, ly, lz, R_d, gas_frac, bulge_frac)
        phi_b = fft_poisson_3d(rho, lx, ly, lz, kappa=1.0)
        phix, phiy, phiz = grad3_central(phi_b, dx, dy, dz)
        a_bar_x = -phix; a_bar_y = -phiy; a_bar_z = -phiz
        sxx, syy, szz, l_rec = build_RS_coeffs(rho, smooth_sigma_vox=args.smooth_sigma_vox)
        if anisotropic:
            cx = (l_rec ** 2) * (1.0 / np.maximum(1.0 + sxx, 1e-6))
            cy = (l_rec ** 2) * (1.0 / np.maximum(1.0 + syy, 1e-6))
            cz = (l_rec ** 2) * (1.0 / np.maximum(1.0 + szz, 1e-6))
            c_arg = (cx, cy, cz)
            Aop = apply_operator_3d_aniso
        else:
            d_iso = 1.0 / np.maximum(1.0 + (sxx + syy + szz), 1e-6)
            c_field = (l_rec ** 2) * d_iso
            c_arg = c_field
            Aop = apply_operator_3d_iso
        g_bar = np.sqrt(np.maximum(a_bar_x ** 2 + a_bar_y ** 2 + a_bar_z ** 2, 0.0))
        g_scale = max(np.nanmax(g_bar), 1e-9)
        f_alpha = np.power(np.maximum(1e-12, (g_bar / g_scale)), -ALPHA)
        phi_sol = cg_solve_3d(Aop, f_alpha, c_arg, dx, dy, dz, tol=1e-6, max_iter=400)
        y1 = cg_solve_3d(Aop, np.ones_like(f_alpha), c_arg, dx, dy, dz, tol=1e-6, max_iter=60)
        K = 1.0 + PHI ** (-5.0) * (phi_sol - y1)
        # Mid-plane circle speeds
        z0 = nz // 2
        r_kpc, v_circ = azimuthal_vr_midplane(a_bar_x[:, :, z0], a_bar_y[:, :, z0], K[:, :, z0], dx, dy)
        return r_kpc, v_circ

    # If convergence study is requested, run that path and exit
    if args.convergence_out:
        grids = [int(s) for s in str(args.convergence_grids).split(",") if str(s).strip().isdigit()]
        grids = sorted(set([g for g in grids if g >= 8]))
        if not grids:
            grids = [32, 48, 64, 96]
        names_iter = list(master.keys())
        if conv_names:
            names_iter = [n for n in names_iter if str(n) in conv_names]
        if args.limit:
            names_iter = names_iter[: args.limit]
        rows_conv = []
        for name in names_iter:
            g = master[name]
            df = g.get("data")
            if df is None:
                continue
            R_d = float(g.get("R_d", 2.0))
            # Reference at finest grid
            r_ref, v_ref = compute_vcirc_for_grid(name, df, R_d, max(grids), args.anisotropic)
            # Interpolate coarser vcirc onto reference radii for norm
            for nx in grids:
                r_co, v_co = compute_vcirc_for_grid(name, df, R_d, nx, args.anisotropic)
                # Interpolate
                try:
                    v_co_i = np.interp(r_ref, r_co, v_co, left=np.nan, right=np.nan)
                except Exception:
                    v_co_i = np.full_like(v_ref, np.nan)
                # L2 norm ratio
                mask = np.isfinite(v_ref) & np.isfinite(v_co_i)
                if np.any(mask):
                    num = float(np.linalg.norm(v_co_i[mask] - v_ref[mask]))
                    den = float(np.linalg.norm(v_ref[mask]) + 1e-12)
                    rel = num / den
                else:
                    rel = np.nan
                rows_conv.append({"galaxy": name, "nx": int(nx), "rel_L2_vs_max": rel})
        if rows_conv:
            dfc = pd.DataFrame(rows_conv)
            Path(args.convergence_out).parent.mkdir(parents=True, exist_ok=True)
            dfc.to_csv(Path(args.convergence_out), index=False)
            print(f"Wrote convergence metrics to {args.convergence_out}")
        return

    for name, g in master.items():
        if args.limit and count >= args.limit:
            break
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
        gas_frac = float(np.nanmedian(np.where(v_bar > 0, (v_gas ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        bulge_frac = float(np.nanmedian(np.where(v_bar > 0, (v_bul ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        gas_frac = np.clip(gas_frac, 0.0, 0.8)
        bulge_frac = np.clip(bulge_frac, 0.0, 0.8)

        # Grid and box
        lx = 2.0 * args.box_factor_xy * R_d
        ly = 2.0 * args.box_factor_xy * R_d
        lz = 2.0 * args.box_factor_z * max(0.2 * R_d, 0.05)
        rho, dx, dy, dz = build_rho_3d(args.nx, args.ny, args.nz, lx, ly, lz, R_d, gas_frac, bulge_frac)

        phi_b = fft_poisson_3d(rho, lx, ly, lz, kappa=1.0)
        phix, phiy, phiz = grad3_central(phi_b, dx, dy, dz)
        a_bar_x = -phix; a_bar_y = -phiy; a_bar_z = -phiz
        g_bar = np.sqrt(np.maximum(a_bar_x ** 2 + a_bar_y ** 2 + a_bar_z ** 2, 0.0))

        feat_name = perm_map[str(name)] if (perm_map is not None and str(name) in perm_map) else str(name)
        pre = try_load_precomputed(args.features_root, feat_name)
        if pre is not None:
            c2d_kpc2, g_ext_SI, pixscale_kpc, ell2d = pre
            # Resize c2d to grid mid-plane then tile along z
            ny, nx, nz = rho.shape
            # D identity ablation: use ell^2 only
            if args.ablate_D_identity and ell2d is not None:
                c2d_resized = resize_bilinear((np.maximum(ell2d, 0.0) ** 2), ny, nx)
            else:
                c2d_resized = resize_bilinear(c2d_kpc2, ny, nx)
            c_field = np.repeat(c2d_resized[..., None], nz, axis=2)
            c_arg = c_field
            Aop = apply_operator_3d_iso
            f_ext = 1.0 if args.ablate_gext0 else (1.0 + g_ext_SI / A0_SI) ** (-ALPHA)
        else:
            sxx, syy, szz, l_rec = build_RS_coeffs(rho, smooth_sigma_vox=args.smooth_sigma_vox)
            if args.anisotropic:
                if args.ablate_D_identity:
                    cx = (l_rec ** 2)
                    cy = (l_rec ** 2)
                    cz = (l_rec ** 2)
                else:
                    cx = (l_rec ** 2) * (1.0 / np.maximum(1.0 + sxx, 1e-6))
                    cy = (l_rec ** 2) * (1.0 / np.maximum(1.0 + syy, 1e-6))
                    cz = (l_rec ** 2) * (1.0 / np.maximum(1.0 + szz, 1e-6))
                c_arg = (cx, cy, cz)
                Aop = apply_operator_3d_aniso
            else:
                d_iso = 1.0 / np.maximum(1.0 + (sxx + syy + szz), 1e-6)
                c_field = (l_rec ** 2) * (1.0 if args.ablate_D_identity else d_iso)
                c_arg = c_field
                Aop = apply_operator_3d_iso
            f_ext = 1.0
        g_scale = max(np.nanmax(g_bar), 1e-9)
        f_alpha = np.power(np.maximum(1e-12, (g_bar / g_scale)), -ALPHA)
        phi_sol = cg_solve_3d(Aop, f_alpha, c_arg, dx, dy, dz, tol=1e-6, max_iter=400)
        y1 = cg_solve_3d(Aop, np.ones_like(f_alpha), c_arg, dx, dy, dz, tol=1e-6, max_iter=60)
        K = 1.0 + PHI ** (-5.0) * (phi_sol - y1 * f_ext)
        if args.ablate_K1:
            K = np.ones_like(K)

        # Mid-plane v(r)
        z0 = args.nz // 2
        r_kpc, v_circ = azimuthal_vr_midplane(a_bar_x[:, :, z0], a_bar_y[:, :, z0], K[:, :, z0], dx, dy)
        # Align to SPARC radii via interpolation of w(r)
        # Compute w_ring at SPARC radii using nearest ring index
        from numpy import interp
        # Build w(r) by averaging K and form v_model
        # Here approximate w_ring ≈ (v_circ / v_bar_ring)^2 when using our a_bar; instead, use K-ring directly
        # Build K-ring at the same ring edges used in azimuthal_vr_midplane
        # Simpler: sample K at nearest ring to r
        # Make pixel radii array for rings
        # We'll reuse azimuthal_vr_midplane’s ring spacing (1 px). Map r to pixel and take mean in ring.
        # For brevity, approximate w_interp using linear interpolation of the mid-plane azimuthal mean of K over r_kpc
        # Compute azimuthal mean of K over rings of r_kpc
        ny, nx = K[:, :, z0].shape
        Y, X = np.indices((ny, nx))
        xc, yc = (nx - 1) / 2.0, (ny - 1) / 2.0
        Rpix = np.hypot(X - xc, Y - yc)
        rpix = r_kpc / max(dx, 1e-12)
        K_ring = []
        for rpx in rpix:
            mask = (Rpix >= rpx - 0.5) & (Rpix < rpx + 0.5)
            K_ring.append(float(np.nanmean(K[:, :, z0][mask])) if np.any(mask) else np.nan)
        K_ring = np.array(K_ring)
        # Interpolate K_ring onto SPARC radii within the modeled box
        rmax_model = r_kpc[-1] if r_kpc.size > 0 else 0.0
        mask_in = (r > 0) & (r <= rmax_model)
        if not np.any(mask_in):
            continue
        K_at_r = np.interp(r[mask_in], r_kpc, K_ring, left=np.nan, right=np.nan)
        v_bar_sp = v_bar[mask_in]
        v_obs_sp = v_obs[mask_in]
        v_err_sp = v_err[mask_in]
        v_model = np.sqrt(np.maximum(K_at_r, 1e-6)) * v_bar_sp

        b_kpc = 0.0 if args.ablate_no_inner_mask else (0.3 * max(R_d, 1e-6))
        v_outer = np.nanmedian(v_obs_sp[-3:]) if v_obs_sp.size >= 3 else np.nanmax(v_obs_sp)
        dwarf = bool(v_outer < V_DWARF_MAX)
        sigma_eff = sigma_eff_kms(r[mask_in], v_obs_sp, v_err_sp, R_d_kpc=R_d, dwarf=dwarf, b_kpc=b_kpc)
        if args.ablate_const_sigma:
            sigma_eff = np.full_like(sigma_eff, SIGMA0)
        mask_eval = np.isfinite(v_model) & (r[mask_in] >= b_kpc)
        if np.any(mask_eval):
            N = int(np.sum(mask_eval))
            chi2 = float(np.sum(((v_obs_sp[mask_eval] - v_model[mask_eval]) / sigma_eff[mask_eval]) ** 2))
            red = chi2 / max(N, 1)
        else:
            red = np.nan; N = 0

        df_out = pd.DataFrame({
            "r_kpc": r[mask_in],
            "v_obs": v_obs_sp,
            "v_err": v_err_sp,
            "v_baryon": v_bar_sp,
            "K_ring": K_at_r,
            "v_model": v_model,
        })
        out_path = out_dir / f"{name}_3d_proxy.csv"
        if args.skip_existing and out_path.exists():
            # Already done; skip writing and counting
            pass
        else:
            df_out.to_csv(out_path, index=False)
        rows.append({"galaxy": name, "N": N, "chi2_over_N": red})

        # Prototype lensing maps (mid-plane; unnormalized kappa,gamma)
        try:
            psi_eff = (K[:, :, z0] * phi_b[:, :, z0]).astype(np.float64)
            ax, ay, kappa_star, gamma1, gamma2 = lensing_from_potential_2d(psi_eff, dx, dy)
            np.savez_compressed(out_dir / f"{name}_lensing_midplane.npz",
                                psi_eff=psi_eff.astype(np.float32),
                                alpha_x=ax.astype(np.float32),
                                alpha_y=ay.astype(np.float32),
                                kappa_star=kappa_star.astype(np.float32),
                                gamma1=gamma1.astype(np.float32),
                                gamma2=gamma2.astype(np.float32))
        except Exception:
            pass
        count += 1

    if rows:
        df_summary = pd.DataFrame(rows)
        df_summary.to_csv(out_dir / "summary.csv", index=False)
        arr = df_summary["chi2_over_N"].to_numpy(float)
        print(f"3D proxy evaluated {arr.size} galaxies; median chi^2/N = {np.nanmedian(arr):.3f}; mean = {np.nanmean(arr):.3f}")
    else:
        print("No galaxies evaluated.")


if __name__ == "__main__":
    main()


