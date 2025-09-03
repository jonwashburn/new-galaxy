#!/usr/bin/env python3
"""
Minimal 2D ILG field-kernel prototype (global-only, no per-galaxy tuning)

What it does:
- Builds a proxy baryon surface density Σ_b(x,y) (toy exponential disk if none provided)
- Solves a Poisson proxy for Φ_b on a 2D grid (FFT-based periodic Poisson)
- Computes g_b = |∇Φ_b| and f_alpha = ((g_b + g_ext)/a0)^(-alpha)
- Builds structure tensor S from s = ∇log Σ_b via local smoothing → D_iso and ℓ_rec
- Solves one SPD elliptic system (I - ∇·(ℓ^2 D ∇)) φ = f_alpha via matrix-free CG
- Forms K = 1 + C_LAG * (φ - y1 * f_ext), where y1 solves (I - ∇·(ℓ^2 D ∇)) y1 = 1
- Outputs numpy arrays for φ, K, and acceleration fields (abar, aeff)

Notes:
- This is a didactic, deterministic prototype with periodic boundary in the FFT Poisson.
- Uses only numpy; no scipy dependency.
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
A0 = 1.2e-10  # SI, scale placeholder


def make_exponential_disk(nx: int, ny: int, r_scale_px: float, peak: float = 1.0) -> np.ndarray:
    x = np.arange(nx) - (nx - 1) / 2.0
    y = np.arange(ny) - (ny - 1) / 2.0
    X, Y = np.meshgrid(x, y, indexing="xy")
    R = np.sqrt(X ** 2 + Y ** 2)
    sigma = np.exp(-R / max(r_scale_px, 1e-6))
    sigma = peak * sigma / np.maximum(np.max(sigma), 1e-12)
    return sigma.astype(np.float64)


def fft_poisson_periodic(rhs: np.ndarray, dx: float = 1.0, dy: float = 1.0, kappa: float = 1.0) -> np.ndarray:
    """Solve -∇^2 Φ = kappa * rhs on a periodic box via FFT (zero-mean convention)."""
    ny, nx = rhs.shape
    kx = np.fft.fftfreq(nx, d=dx) * 2.0 * np.pi
    ky = np.fft.fftfreq(ny, d=dy) * 2.0 * np.pi
    KX, KY = np.meshgrid(kx, ky, indexing="xy")
    K2 = KX ** 2 + KY ** 2
    rhs_hat = np.fft.fft2(rhs)
    # Avoid division by zero at k=0 by setting mean(Φ)=0
    denom = np.where(K2 > 0.0, K2, np.inf)
    phi_hat = (kappa * rhs_hat) / denom
    phi_hat[0, 0] = 0.0 + 0.0j
    phi_field = np.fft.ifft2(-phi_hat).real
    return phi_field


def gradient_central(f: np.ndarray, dx: float = 1.0, dy: float = 1.0) -> Tuple[np.ndarray, np.ndarray]:
    """Central differences with periodic wrap for prototype consistency."""
    fx = (np.roll(f, -1, axis=1) - np.roll(f, 1, axis=1)) / (2.0 * dx)
    fy = (np.roll(f, -1, axis=0) - np.roll(f, 1, axis=0)) / (2.0 * dy)
    return fx, fy


def smooth_gaussian_fft(img: np.ndarray, sigma_px: float) -> np.ndarray:
    if sigma_px <= 0.0:
        return img.copy()
    ny, nx = img.shape
    y = np.arange(ny)
    x = np.arange(nx)
    Y, X = np.meshgrid(y, x, indexing="ij")
    # Build Gaussian kernel centered at (0,0) and roll to align
    # Using periodic assumption: construct kernel by distance on the torus
    yy = np.minimum(Y, ny - Y)
    xx = np.minimum(X, nx - X)
    R2 = (xx ** 2 + yy ** 2).astype(np.float64)
    g = np.exp(-0.5 * R2 / max(sigma_px ** 2, 1e-12))
    g /= np.sum(g)
    F = np.fft.fft2(img)
    G = np.fft.fft2(g)
    out = np.fft.ifft2(F * G).real
    return out


def build_structure_tensor(sigma_b: np.ndarray, smooth_sigma_px: float = 2.0) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    eps = 1e-12
    s_log = np.log(np.maximum(sigma_b, eps))
    sx, sy = gradient_central(s_log)
    # Local second-moment matrix components with smoothing
    sxx = smooth_gaussian_fft(sx * sx, smooth_sigma_px)
    syy = smooth_gaussian_fft(sy * sy, smooth_sigma_px)
    sxy = smooth_gaussian_fft(sx * sy, smooth_sigma_px)
    # Use isotropic summary: trace and simple anisotropy ratio
    trace = sxx + syy
    # Recognition diffusion: D_iso = 1 / (1 + trace)
    d_iso = 1.0 / np.maximum(1.0 + trace, 1e-6)
    # Recognition length: ℓ_rec = λ_rec / sqrt(1 + trace) with λ_rec normalized to 1 grid unit here
    l_rec = 1.0 / np.sqrt(np.maximum(1.0 + trace, 1e-6))
    return sxx, syy, sxy, trace, d_iso, l_rec


def apply_operator(phi_field: np.ndarray, c_field: np.ndarray, dx: float = 1.0, dy: float = 1.0) -> np.ndarray:
    """Compute (I - ∇·(c ∇)) phi on a grid with periodic boundary for simplicity.
    c_field = ℓ_rec^2 * D_iso (scalar field).
    """
    phi_ = phi_field
    # Fluxes at i+1/2, j and i, j+1/2 using arithmetic average of c
    c_right = 0.5 * (c_field + np.roll(c_field, -1, axis=1))
    c_left = 0.5 * (c_field + np.roll(c_field, 1, axis=1))
    c_up = 0.5 * (c_field + np.roll(c_field, -1, axis=0))
    c_down = 0.5 * (c_field + np.roll(c_field, 1, axis=0))
    # Gradients
    dphi_dx_right = (np.roll(phi_, -1, axis=1) - phi_) / dx
    dphi_dx_left = (phi_ - np.roll(phi_, 1, axis=1)) / dx
    dphi_dy_up = (np.roll(phi_, -1, axis=0) - phi_) / dy
    dphi_dy_down = (phi_ - np.roll(phi_, 1, axis=0)) / dy
    # Fluxes
    flux_x = c_right * dphi_dx_right - c_left * dphi_dx_left
    flux_y = c_up * dphi_dy_up - c_down * dphi_dy_down
    div_flux = (flux_x / dx + flux_y / dy)
    return phi_ - div_flux


def apply_operator_aniso(phi_field: np.ndarray, c_fields: Tuple[np.ndarray, np.ndarray], dx: float = 1.0, dy: float = 1.0) -> np.ndarray:
    """Anisotropic diagonal diffusion: c_fields = (c_x, c_y) for faces normal to x and y."""
    c_x, c_y = c_fields
    phi_ = phi_field
    cx_right = 0.5 * (c_x + np.roll(c_x, -1, axis=1))
    cx_left = 0.5 * (c_x + np.roll(c_x, 1, axis=1))
    cy_up = 0.5 * (c_y + np.roll(c_y, -1, axis=0))
    cy_down = 0.5 * (c_y + np.roll(c_y, 1, axis=0))
    dphi_dx_right = (np.roll(phi_, -1, axis=1) - phi_) / dx
    dphi_dx_left = (phi_ - np.roll(phi_, 1, axis=1)) / dx
    dphi_dy_up = (np.roll(phi_, -1, axis=0) - phi_) / dy
    dphi_dy_down = (phi_ - np.roll(phi_, 1, axis=0)) / dy
    flux_x = cx_right * dphi_dx_right - cx_left * dphi_dx_left
    flux_y = cy_up * dphi_dy_up - cy_down * dphi_dy_down
    div_flux = (flux_x / dx + flux_y / dy)
    return phi_ - div_flux


def cg_solve(apply_A, b: np.ndarray, c_arg, tol: float = 1e-6, max_iter: int = 500) -> np.ndarray:
    x = np.zeros_like(b)
    r = b - apply_A(x, c_arg)
    p = r.copy()
    rs_old = np.vdot(r, r).real
    eps = 1e-30
    for _ in range(max_iter):
        Ap = apply_A(p, c_arg)
        alpha = rs_old / max(np.vdot(p, Ap).real, eps)
        x = x + alpha * p
        r = r - alpha * Ap
        rs_new = np.vdot(r, r).real
        if rs_new <= tol ** 2 * rs_old:
            break
        p = r + (rs_new / max(rs_old, eps)) * p
        rs_old = rs_new
    return x


def compute_kernel_2d(sigma_b: np.ndarray, gext_ratio: float = 0.0, smooth_sigma_px: float = 2.0, anisotropic: bool = False) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    # 1) Poisson proxy for Φ_b and a_bar
    phi_b = fft_poisson_periodic(sigma_b, dx=1.0, dy=1.0, kappa=1.0)
    phix, phiy = gradient_central(phi_b)
    # a_bar = -∇Φ; magnitude
    a_bar_x = -phix
    a_bar_y = -phiy
    g_bar = np.sqrt(np.maximum(a_bar_x ** 2 + a_bar_y ** 2, 0.0))
    # 2) Build D_iso and ℓ_rec from structure tensor of Σ_b
    sxx, syy, sxy, trace, d_iso, l_rec = build_structure_tensor(sigma_b, smooth_sigma_px=smooth_sigma_px)
    if anisotropic:
        d_x = 1.0 / np.maximum(1.0 + sxx, 1e-6)
        d_y = 1.0 / np.maximum(1.0 + syy, 1e-6)
        c_x = (l_rec ** 2) * d_x
        c_y = (l_rec ** 2) * d_y
        c_arg = (c_x, c_y)
        Aop = lambda u, carr: apply_operator_aniso(u, carr, dx=1.0, dy=1.0)
    else:
        c_field = (l_rec ** 2) * d_iso
        c_arg = c_field
        Aop = lambda u, c: apply_operator(u, c, dx=1.0, dy=1.0)
    # 3) Right-hand side f_alpha
    gext = float(gext_ratio) * A0
    # Use dimensionless proxy since A0 SI is arbitrary in this toy; scale with max(g_bar)
    g_scale = max(np.nanmax(g_bar), 1e-9)
    g_b_eff = g_bar / g_scale
    f_alpha = np.power(np.maximum(1e-12, (g_b_eff + gext) / max(1.0, gext + 1e-12)), -ALPHA)
    f_ext = np.power(1.0 + gext / max(1.0, gext + 1e-12), -ALPHA)
    # 4) Solve (I - ∇·(c ∇)) φ = f_alpha and y1 = solve(..., 1)
    phi_sol = cg_solve(Aop, f_alpha, c_arg, tol=1e-6, max_iter=400)
    y1 = cg_solve(Aop, np.ones_like(f_alpha), c_arg, tol=1e-6, max_iter=400)
    # 5) Kernel K and effective acceleration
    K = 1.0 + C_LAG * (phi_sol - y1 * f_ext)
    a_eff_x = K * a_bar_x
    a_eff_y = K * a_bar_y
    return K, phi_sol, a_bar_x, a_bar_y, a_eff_x + 0.0 * a_eff_y  # return a scalar field too if needed


def run_demo(args: argparse.Namespace) -> None:
    np.random.seed(0)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    cases = []
    if args.sigma_path:
        sigma = np.load(args.sigma_path)
        cases.append(("custom", sigma))
    else:
        # Create a few toy disks
        sizes = [(args.ny, args.nx), (args.ny, args.nx), (args.ny, args.nx)]
        scales = [args.r_scale_px, 0.7 * args.r_scale_px, 1.3 * args.r_scale_px]
        peaks = [1.0, 1.0, 1.0]
        for i, ((ny, nx), rs, pk) in enumerate(zip(sizes, scales, peaks)):
            sigma = make_exponential_disk(nx, ny, r_scale_px=rs, peak=pk)
            cases.append((f"toy_{i+1}", sigma))

    for name, sigma in cases:
        K, phi_sol, ax_bar, ay_bar, aeff_scalar = compute_kernel_2d(
            sigma, gext_ratio=args.gext_ratio, smooth_sigma_px=args.smooth_sigma_px
        )
        # Save arrays
        np.save(out_dir / f"{name}_Sigma_b.npy", sigma)
        np.save(out_dir / f"{name}_phi.npy", phi_sol)
        np.save(out_dir / f"{name}_K.npy", K)
        np.save(out_dir / f"{name}_ax_bar.npy", ax_bar)
        np.save(out_dir / f"{name}_ay_bar.npy", ay_bar)
        # Lightweight diagnostic: report simple summaries
        print(f"{name}: K median={np.nanmedian(K):.3f} mean={np.nanmean(K):.3f}")


def main():
    ap = argparse.ArgumentParser(description="Minimal 2D ILG kernel prototype (global-only)")
    ap.add_argument("--nx", type=int, default=128, help="Grid width (default 128)")
    ap.add_argument("--ny", type=int, default=128, help="Grid height (default 128)")
    ap.add_argument("--r_scale_px", type=float, default=20.0, help="Toy exponential disk scale length in pixels")
    ap.add_argument("--gext_ratio", type=float, default=0.0, help="External field ratio in units of a0 (default 0)")
    ap.add_argument("--smooth_sigma_px", type=float, default=2.0, help="Smoothing sigma (pixels) for structure tensor")
    ap.add_argument("--sigma_path", type=str, default="", help="Optional .npy path for Σ_b array")
    ap.add_argument("--out_dir", type=str, default="results/ilg2d", help="Output directory for .npy files")
    args = ap.parse_args()
    run_demo(args)


if __name__ == "__main__":
    main()


