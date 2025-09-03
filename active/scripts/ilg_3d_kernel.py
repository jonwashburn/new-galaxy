#!/usr/bin/env python3
"""
Minimal 3D ILG field-kernel prototype (global-only, no per-galaxy tuning)

Pipeline:
- Synthesize or load a 3D baryon density rho_b(x,y,z)
- Solve Poisson -∇^2 Φ_b = κ * rho_b via 3D FFT (periodic box)
- Compute a_bar = -∇Φ_b and g_b = |a_bar|
- Build structure tensor summary from ∇log rho_b → D_iso = 1/(1+tr S), ℓ_rec = λ_rec/sqrt(1+tr S)
- Solve (I - ∇·(ℓ^2 D ∇)) φ = f_alpha with CG (matrix-free)
- Solve y1 for constant RHS to normalize external-field subtraction
- Form K = 1 + C_LAG * (φ - y1 * f_ext) and a_eff = K * a_bar
- Export NPZ outputs; quick mid-plane v(r) CSV
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Tuple

import numpy as np


def phi() -> float:
    return (1.0 + np.sqrt(5.0)) / 2.0


PHI = phi()
ALPHA = 0.5 * (1.0 - 1.0 / PHI)
C_LAG = PHI ** (-5.0)
A0 = 1.2e-10


def make_rho_b(nx: int, ny: int, nz: int, lx: float, ly: float, lz: float,
               r_scale_kpc: float = 3.0, hz_kpc: float = 0.3,
               bulge_frac: float = 0.2, bulge_a_kpc: float = 0.5) -> np.ndarray:
    x = (np.arange(nx) - (nx - 1) / 2.0) * (lx / nx)
    y = (np.arange(ny) - (ny - 1) / 2.0) * (ly / ny)
    z = (np.arange(nz) - (nz - 1) / 2.0) * (lz / nz)
    X, Y, Z = np.meshgrid(x, y, z, indexing="xy")
    R = np.sqrt(X ** 2 + Y ** 2)
    # Disk: exponential in R with sech^2 vertical
    rho_disk = np.exp(-R / max(r_scale_kpc, 1e-6)) * (1.0 / np.cosh(Z / max(hz_kpc, 1e-6))) ** 2
    # Bulge: Hernquist ~ 1/(r (r+a)^3)
    r3 = np.sqrt(R ** 2 + Z ** 2)
    a = max(bulge_a_kpc, 1e-6)
    rho_bulge = 1.0 / np.maximum(r3 * (r3 + a) ** 3, 1e-6)
    rho = (1.0 - bulge_frac) * rho_disk + bulge_frac * rho_bulge
    rho /= np.nanmax(rho)
    return rho.astype(np.float64)


def fft_poisson_3d(rhs: np.ndarray, lx: float, ly: float, lz: float, kappa: float = 1.0) -> np.ndarray:
    ny, nx, nz = rhs.shape  # using (y,x,z) shape for consistency below
    # Actually our arrays are [ny,nx] in 2D; extend to 3D as [ny,nx,nz]
    nx = rhs.shape[1]; ny = rhs.shape[0]; nz = rhs.shape[2]
    dx = lx / nx; dy = ly / ny; dz = lz / nz
    kx = np.fft.fftfreq(nx, d=dx) * 2.0 * np.pi
    ky = np.fft.fftfreq(ny, d=dy) * 2.0 * np.pi
    kz = np.fft.fftfreq(nz, d=dz) * 2.0 * np.pi
    KX, KY, KZ = np.meshgrid(kx, ky, kz, indexing="xy")
    K2 = KX ** 2 + KY ** 2 + KZ ** 2
    rhs_hat = np.fft.fftn(rhs)
    denom = np.where(K2 > 0.0, K2, np.inf)
    phi_hat = (kappa * rhs_hat) / denom
    phi_hat[0, 0, 0] = 0.0 + 0.0j
    phi_field = np.fft.ifftn(-phi_hat).real
    return phi_field


def grad3_central(f: np.ndarray, dx: float, dy: float, dz: float) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    fx = (np.roll(f, -1, axis=1) - np.roll(f, 1, axis=1)) / (2.0 * dx)
    fy = (np.roll(f, -1, axis=0) - np.roll(f, 1, axis=0)) / (2.0 * dy)
    fz = (np.roll(f, -1, axis=2) - np.roll(f, 1, axis=2)) / (2.0 * dz)
    return fx, fy, fz


def build_RS_coeffs(rho: np.ndarray, smooth_sigma_vox: float = 1.0) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    eps = 1e-12
    s_log = np.log(np.maximum(rho, eps))
    ny, nx, nz = rho.shape
    # Assume unit voxels for smoothing scale; cheap Gaussian via FFT convolution
    def smooth3_fft(vol: np.ndarray, sigma: float) -> np.ndarray:
        if sigma <= 0.0:
            return vol.copy()
        # Build 1D Gaussian kernels and separable convolution via FFT: approximate by single 3D kernel
        y = np.arange(ny); x = np.arange(nx); z = np.arange(nz)
        Y, X, Z = np.meshgrid(y, x, z, indexing="ij")
        yy = np.minimum(Y, ny - Y)
        xx = np.minimum(X, nx - X)
        zz = np.minimum(Z, nz - Z)
        R2 = (xx ** 2 + yy ** 2 + zz ** 2).astype(np.float64)
        g = np.exp(-0.5 * R2 / max(sigma ** 2, 1e-12))
        g /= np.sum(g)
        F = np.fft.fftn(vol)
        G = np.fft.fftn(g)
        return np.fft.ifftn(F * G).real

    # Gradients of log rho
    # Use unit voxels for RS coefficients; geometry scaling handled elsewhere if needed
    sx, sy, sz = grad3_central(s_log, 1.0, 1.0, 1.0)
    sxx = smooth3_fft(sx * sx, smooth_sigma_vox)
    syy = smooth3_fft(sy * sy, smooth_sigma_vox)
    szz = smooth3_fft(sz * sz, smooth_sigma_vox)
    # Trace of structure tensor
    trace = sxx + syy + szz
    d_iso = 1.0 / np.maximum(1.0 + trace, 1e-6)
    l_rec = 1.0 / np.sqrt(np.maximum(1.0 + trace, 1e-6))
    return sxx, syy, szz, l_rec


def apply_operator_3d_iso(phi_field: np.ndarray, c_field: np.ndarray, dx: float, dy: float, dz: float) -> np.ndarray:
    c_xp = 0.5 * (c_field + np.roll(c_field, -1, axis=1))
    c_xm = 0.5 * (c_field + np.roll(c_field, 1, axis=1))
    c_yp = 0.5 * (c_field + np.roll(c_field, -1, axis=0))
    c_ym = 0.5 * (c_field + np.roll(c_field, 1, axis=0))
    c_zp = 0.5 * (c_field + np.roll(c_field, -1, axis=2))
    c_zm = 0.5 * (c_field + np.roll(c_field, 1, axis=2))
    dpx = (np.roll(phi_field, -1, axis=1) - phi_field) / dx
    dmx = (phi_field - np.roll(phi_field, 1, axis=1)) / dx
    dpy = (np.roll(phi_field, -1, axis=0) - phi_field) / dy
    dmy = (phi_field - np.roll(phi_field, 1, axis=0)) / dy
    dpz = (np.roll(phi_field, -1, axis=2) - phi_field) / dz
    dmz = (phi_field - np.roll(phi_field, 1, axis=2)) / dz
    flux = (c_xp * dpx - c_xm * dmx) / dx + (c_yp * dpy - c_ym * dmy) / dy + (c_zp * dpz - c_zm * dmz) / dz
    return phi_field - flux


def apply_operator_3d_aniso(phi_field: np.ndarray, c_xyz: Tuple[np.ndarray, np.ndarray, np.ndarray], dx: float, dy: float, dz: float) -> np.ndarray:
    cx, cy, cz = c_xyz
    cxp = 0.5 * (cx + np.roll(cx, -1, axis=1))
    cxm = 0.5 * (cx + np.roll(cx, 1, axis=1))
    cyp = 0.5 * (cy + np.roll(cy, -1, axis=0))
    cym = 0.5 * (cy + np.roll(cy, 1, axis=0))
    czp = 0.5 * (cz + np.roll(cz, -1, axis=2))
    czm = 0.5 * (cz + np.roll(cz, 1, axis=2))
    dpx = (np.roll(phi_field, -1, axis=1) - phi_field) / dx
    dmx = (phi_field - np.roll(phi_field, 1, axis=1)) / dx
    dpy = (np.roll(phi_field, -1, axis=0) - phi_field) / dy
    dmy = (phi_field - np.roll(phi_field, 1, axis=0)) / dy
    dpz = (np.roll(phi_field, -1, axis=2) - phi_field) / dz
    dmz = (phi_field - np.roll(phi_field, 1, axis=2)) / dz
    flux = (cxp * dpx - cxm * dmx) / dx + (cyp * dpy - cym * dmy) / dy + (czp * dpz - czm * dmz) / dz
    return phi_field - flux


def cg_solve_3d(apply_A, b: np.ndarray, c_field: np.ndarray, dx: float, dy: float, dz: float,
                tol: float = 1e-6, max_iter: int = 800) -> np.ndarray:
    x = np.zeros_like(b)
    r = b - apply_A(x, c_field, dx, dy, dz)
    p = r.copy()
    rs_old = np.vdot(r, r).real
    eps = 1e-30
    for _ in range(max_iter):
        Ap = apply_A(p, c_field, dx, dy, dz)
        alpha = rs_old / max(np.vdot(p, Ap).real, eps)
        x = x + alpha * p
        r = r - alpha * Ap
        rs_new = np.vdot(r, r).real
        if rs_new <= tol ** 2 * rs_old:
            break
        p = r + (rs_new / max(rs_old, eps)) * p
        rs_old = rs_new
    return x


def azimuthal_vr_midplane(ax: np.ndarray, ay: np.ndarray, K: np.ndarray, dx: float, dy: float) -> Tuple[np.ndarray, np.ndarray]:
    ny, nx = ax.shape
    y, x = np.indices((ny, nx))
    xc, yc = (nx - 1) / 2.0, (ny - 1) / 2.0
    Rpix = np.hypot(x - xc, y - yc)
    rx = (x - xc) / (Rpix + 1e-9)
    ry = (y - yc) / (Rpix + 1e-9)
    a_eff_r = (K * ax) * rx + (K * ay) * ry
    rmax = int(min(nx, ny) // 2)
    rbins = np.arange(1, rmax)
    v = []
    for r in rbins:
        mask = (Rpix >= r - 0.5) & (Rpix < r + 0.5)
        aavg = np.nanmean(a_eff_r[mask])
        # v^2 / r_phys = a_r  ⇒ v ≈ sqrt(a_r * r_phys)
        r_phys = r * dx  # assume dx=dy in kpc
        v.append(np.sqrt(max(aavg, 1e-12) * max(r_phys, 1e-9)))
    return rbins * dx, np.array(v)


def run_demo(args: argparse.Namespace) -> None:
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    nx, ny, nz = args.nx, args.ny, args.nz
    lx, ly, lz = args.lx_kpc, args.ly_kpc, args.lz_kpc
    dx, dy, dz = lx / nx, ly / ny, lz / nz

    if args.rho_path:
        rho = np.load(args.rho_path)
    else:
        rho = make_rho_b(nx, ny, nz, lx, ly, lz,
                         r_scale_kpc=args.r_scale_kpc, hz_kpc=args.hz_kpc,
                         bulge_frac=args.bulge_frac, bulge_a_kpc=args.bulge_a_kpc)

    phi_b = fft_poisson_3d(rho, lx, ly, lz, kappa=1.0)
    phix, phiy, phiz = grad3_central(phi_b, dx, dy, dz)
    a_bar_x = -phix; a_bar_y = -phiy; a_bar_z = -phiz
    g_bar = np.sqrt(np.maximum(a_bar_x ** 2 + a_bar_y ** 2 + a_bar_z ** 2, 0.0))

    sxx, syy, szz, l_rec = build_RS_coeffs(rho, smooth_sigma_vox=args.smooth_sigma_vox)
    if args.anisotropic:
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

    gext = float(args.gext_si)
    # Normalize by a characteristic scale to stay in a robust numeric band
    g_scale = max(np.nanmax(g_bar), 1e-9)
    g_b_eff = g_bar / g_scale
    f_alpha = np.power(np.maximum(1e-12, (g_b_eff + gext) / max(1.0, gext + 1e-12)), -ALPHA)
    f_ext = np.power(1.0 + gext / max(1.0, gext + 1e-12), -ALPHA)

    phi_sol = cg_solve_3d(Aop, f_alpha, c_arg, dx, dy, dz, tol=1e-6, max_iter=600)
    y1 = cg_solve_3d(Aop, np.ones_like(f_alpha), c_arg, dx, dy, dz, tol=1e-6, max_iter=100)

    K = 1.0 + C_LAG * (phi_sol - y1 * f_ext)
    a_eff_x = K * a_bar_x
    a_eff_y = K * a_bar_y
    a_eff_z = K * a_bar_z

    # Mid-plane rotation estimate
    z0 = nz // 2
    r_kpc, v_circ = azimuthal_vr_midplane(a_bar_x[:, :, z0], a_bar_y[:, :, z0], K[:, :, z0], dx, dy)

    np.savez(out_dir / "fields.npz",
             rho=rho, phi_b=phi_b,
             a_bar_x=a_bar_x, a_bar_y=a_bar_y, a_bar_z=a_bar_z,
             d_iso=d_iso, l_rec=l_rec, c_field=c_field,
             phi=phi_sol, y1=y1, K=K,
             r_kpc=r_kpc, v_circ=v_circ,
             meta=dict(nx=nx, ny=ny, nz=nz, lx=lx, ly=ly, lz=lz,
                       alpha=ALPHA, C_LAG=C_LAG, A0=A0, g_scale=g_scale))
    print(f"Saved {out_dir/'fields.npz'} with grid {nx}x{ny}x{nz} and box {lx}x{ly}x{lz} kpc")


def main():
    ap = argparse.ArgumentParser(description="Minimal 3D ILG kernel prototype (global-only)")
    ap.add_argument("--nx", type=int, default=32)
    ap.add_argument("--ny", type=int, default=32)
    ap.add_argument("--nz", type=int, default=32)
    ap.add_argument("--lx_kpc", type=float, default=40.0)
    ap.add_argument("--ly_kpc", type=float, default=40.0)
    ap.add_argument("--lz_kpc", type=float, default=8.0)
    ap.add_argument("--r_scale_kpc", type=float, default=3.0)
    ap.add_argument("--hz_kpc", type=float, default=0.3)
    ap.add_argument("--bulge_frac", type=float, default=0.2)
    ap.add_argument("--bulge_a_kpc", type=float, default=0.5)
    ap.add_argument("--gext_si", type=float, default=0.0, help="External field in SI units (toy)")
    ap.add_argument("--smooth_sigma_vox", type=float, default=1.0)
    ap.add_argument("--rho_path", type=str, default="")
    ap.add_argument("--anisotropic", action="store_true")
    ap.add_argument("--out_dir", type=str, default="results/ilg3d")
    args = ap.parse_args()
    run_demo(args)


if __name__ == "__main__":
    main()


