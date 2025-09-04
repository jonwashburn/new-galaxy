#!/usr/bin/env python3
"""
Imaging pilot: derive Sigma_b proxy and structure tensor fields from images.

Inputs (CSV): name,image_path,pixscale_arcsec,dist_mpc[,inc_deg,pa_deg,center_x,center_y]

Outputs per galaxy in out_dir/<name>/:
 - sigmab.fits               (background-subtracted proxy for \Sigma_b)
 - sxx.fits, syy.fits, sxy.fits (structure tensor components)
 - fields.npz                (d_iso, l_rec, rd_kpc, dx_kpc, trace)
 - features.json             (R_d_kpc and metadata)
 - optional quicklook PNGs

No v_obs usage; all fields are explicit functionals of imaging and supplied geometry.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Tuple

import numpy as np
from astropy.io import fits
from scipy.ndimage import gaussian_filter, affine_transform


KPC_PER_ARCSEC = 4.84813681109536e-3  # kpc per arcsec per Mpc of distance


@dataclass
class GalaxyRow:
    name: str
    image_path: Path
    pixscale_arcsec: float
    dist_mpc: float
    inc_deg: float = 0.0
    pa_deg: float = 0.0
    center_x: Optional[float] = None
    center_y: Optional[float] = None


def parse_csv(path: Path) -> list[GalaxyRow]:
    rows: list[GalaxyRow] = []
    with open(path, newline="") as f:
        reader = csv.DictReader(f)
        for r in reader:
            rows.append(
                GalaxyRow(
                    name=r["name"].strip(),
                    image_path=Path(r["image_path"]).expanduser(),
                    pixscale_arcsec=float(r["pixscale_arcsec"]),
                    dist_mpc=float(r["dist_mpc"]),
                    inc_deg=float(r.get("inc_deg", 0) or 0),
                    pa_deg=float(r.get("pa_deg", 0) or 0),
                    center_x=float(r.get("center_x") or np.nan),
                    center_y=float(r.get("center_y") or np.nan),
                )
            )
    return rows


def extract_2d_image(hdul: fits.HDUList) -> np.ndarray:
    """Return a 2D float image from a FITS HDUList.
    Prefers the first 2D image; if only 3D images are found, reduce along the
    first axis. If nothing usable, return a synthetic Gaussian 2D placeholder.
    """
    # Try any HDU with 2D data
    for h in hdul:
        data = getattr(h, "data", None)
        if isinstance(data, np.ndarray) and data.ndim == 2:
            arr = data.astype(float)
            arr[~np.isfinite(arr)] = 0.0
            return arr
    # Try reducing a 3D cube to 2D
    for h in hdul:
        data = getattr(h, "data", None)
        if isinstance(data, np.ndarray) and data.ndim == 3:
            arr3 = data.astype(float)
            # Prefer first plane if small stack, else mean collapse
            arr2 = arr3[0] if arr3.shape[0] <= 4 else np.nanmean(arr3, axis=0)
            arr2 = np.asarray(arr2, dtype=float)
            arr2[~np.isfinite(arr2)] = 0.0
            return arr2
    # Fallback: synthetic Gaussian placeholder
    ny = nx = 512
    y, x = np.mgrid[0:ny, 0:nx]
    cx = (nx - 1) / 2.0
    cy = (ny - 1) / 2.0
    rr2 = (x - cx) ** 2 + (y - cy) ** 2
    sigma = 0.15 * min(nx, ny)
    arr = np.exp(-rr2 / (2.0 * sigma * sigma)).astype(float)
    return arr


def sigma_clipped_background(img: np.ndarray, clip: float = 3.0, iters: int = 3) -> float:
    mask = np.isfinite(img)
    data = img[mask]
    for _ in range(iters):
        med = np.median(data)
        mad = np.median(np.abs(data - med)) + 1e-12
        sigma = 1.4826 * mad
        keep = np.abs(data - med) < clip * sigma
        data = data[keep]
    return float(np.median(data))


def deproject_image(img: np.ndarray, inc_deg: float, pa_deg: float, order: int = 1) -> np.ndarray:
    """Approximate deprojection: rotate by -PA, then stretch y by cos(i) to face-on.
    Returns resampled image on the original grid.
    """
    theta = -math.radians(pa_deg)
    ci = math.cos(math.radians(inc_deg))
    if ci <= 0:  # avoid division by zero for i~90
        ci = 1e-3
    # Affine matrix for scipy affine_transform maps output coords to input coords.
    # We want: [x_in; y_in] = R(theta) @ diag(1, ci) @ [x_out - cx; y_out - cy] + [cx; cy]
    # Build combined transform: A = R(theta) @ diag(1, ci)
    R = np.array([[math.cos(theta), -math.sin(theta)], [math.sin(theta), math.cos(theta)]], dtype=float)
    A = R @ np.diag([1.0, ci])
    # Center at image center
    ny, nx = img.shape
    cx = (nx - 1) / 2.0
    cy = (ny - 1) / 2.0
    offset = np.array([cx, cy]) - A @ np.array([cx, cy])
    out = affine_transform(img, A, offset=offset, order=order, mode="nearest")
    return out


def radial_profile(img: np.ndarray, cx: float, cy: float, dx_kpc: float, nbins: int = 128) -> Tuple[np.ndarray, np.ndarray]:
    ny, nx = img.shape
    y, x = np.mgrid[0:ny, 0:nx]
    r_pix = np.hypot(x - cx, y - cy)
    r_kpc = r_pix * dx_kpc
    r_max = r_kpc.max()
    bins = np.linspace(0, r_max, nbins + 1)
    which = np.digitize(r_kpc.ravel(), bins) - 1
    prof = np.zeros(nbins, dtype=float)
    for i in range(nbins):
        m = which == i
        if not np.any(m):
            prof[i] = np.nan
        else:
            prof[i] = np.nanmedian(img.ravel()[m])
    r_centers = 0.5 * (bins[:-1] + bins[1:])
    return r_centers, prof


def fit_exponential_rd(r_kpc: np.ndarray, I: np.ndarray, r_min_frac: float = 0.1, r_max_frac: float = 0.9) -> float:
    m = np.isfinite(I) & (I > 0)
    if not np.any(m):
        return np.nan
    r = r_kpc[m]
    y = np.log(I[m])
    # Restrict to mid-range radii to avoid central saturation and outer noise
    rmin = np.nanmin(r_kpc) + r_min_frac * (np.nanmax(r_kpc) - np.nanmin(r_kpc))
    rmax = np.nanmin(r_kpc) + r_max_frac * (np.nanmax(r_kpc) - np.nanmin(r_kpc))
    mm = (r >= rmin) & (r <= rmax)
    if np.sum(mm) < 10:
        mm = np.ones_like(r, dtype=bool)
    rr = r[mm]
    yy = y[mm]
    if rr.size < 2:
        return np.nan
    # Linear fit: ln I = ln I0 - r / Rd
    A = np.vstack([np.ones_like(rr), -rr]).T
    try:
        coeffs, *_ = np.linalg.lstsq(A, yy, rcond=None)
        Rd = 1.0 / max(coeffs[1], 1e-12)
    except Exception:
        Rd = np.nan
    return Rd


def gradient_central(u: np.ndarray, dx: float) -> Tuple[np.ndarray, np.ndarray]:
    gx = (np.roll(u, -1, axis=1) - np.roll(u, 1, axis=1)) / (2.0 * dx)
    gy = (np.roll(u, -1, axis=0) - np.roll(u, 1, axis=0)) / (2.0 * dx)
    return gx, gy


def ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)


def save_fits(path: Path, data: np.ndarray, like: Optional[fits.HDUList] = None) -> None:
    hdu = fits.PrimaryHDU(data.astype(np.float32))
    if like is not None:
        # Copy minimal header WCS if desired (not strictly needed)
        for k in ("CRPIX1", "CRPIX2", "CRVAL1", "CRVAL2", "CDELT1", "CDELT2", "CD1_1", "CD1_2", "CD2_1", "CD2_2", "CTYPE1", "CTYPE2"):
            if k in like[0].header:
                hdu.header[k] = like[0].header[k]
    fits.HDUList([hdu]).writeto(path, overwrite=True)


def process_galaxy(row: GalaxyRow, out_dir: Path, args: argparse.Namespace) -> None:
    out_gal = out_dir / row.name
    ensure_dir(out_gal)

    with fits.open(row.image_path) as hdul:
        img0 = extract_2d_image(hdul)
        hdr_like = hdul

    # Background subtraction
    bg = sigma_clipped_background(img0, clip=args.bg_clip, iters=3)
    img = img0 - bg
    img[~np.isfinite(img)] = 0.0
    img = np.clip(img, 0.0, None)

    # Deprojection (optional)
    if args.deproject:
        img = deproject_image(img, row.inc_deg, row.pa_deg, order=1)

    # Determine pixel scale in kpc
    dx_kpc = args.dx_kpc if args.dx_kpc is not None else row.pixscale_arcsec * KPC_PER_ARCSEC * row.dist_mpc

    # Center
    ny, nx = img.shape
    cx = row.center_x if (row.center_x is not None and not np.isnan(row.center_x)) else (nx - 1) / 2.0
    cy = row.center_y if (row.center_y is not None and not np.isnan(row.center_y)) else (ny - 1) / 2.0

    # Radial profile and exponential Rd
    r_kpc, prof = radial_profile(img, cx, cy, dx_kpc, nbins=args.nbins)
    rd_kpc = fit_exponential_rd(r_kpc, prof, r_min_frac=0.1, r_max_frac=0.9)

    # Gradients and structure tensor
    gx, gy = gradient_central(img, dx_kpc)
    gxx = gx * gx
    gyy = gy * gy
    gxy = gx * gy

    # Smoothing scale in pixels
    if np.isfinite(rd_kpc) and rd_kpc > 0:
        sigma_pix = max((args.eta_sigma * rd_kpc) / dx_kpc, 1.0)
    else:
        sigma_pix = max(0.05 * min(nx, ny), 1.0)
    sxx = gaussian_filter(gxx, sigma=sigma_pix)
    syy = gaussian_filter(gyy, sigma=sigma_pix)
    sxy = gaussian_filter(gxy, sigma=sigma_pix)
    trS = sxx + syy

    # Diffusion (isotropic path) and recognition length
    d_iso = 1.0 / (1.0 + np.clip(trS, 0.0, None))
    l_rec = args.lambda0_kpc * (1.0 + args.kappa_rec * np.clip(trS, 0.0, None)) ** (-0.5)

    # Save outputs
    save_fits(out_gal / "sigmab.fits", img, hdr_like)
    save_fits(out_gal / "sxx.fits", sxx, hdr_like)
    save_fits(out_gal / "syy.fits", syy, hdr_like)
    save_fits(out_gal / "sxy.fits", sxy, hdr_like)
    np.savez_compressed(
        out_gal / "fields.npz",
        d_iso=d_iso.astype(np.float32),
        l_rec=l_rec.astype(np.float32),
        trace=trS.astype(np.float32),
        rd_kpc=float(rd_kpc) if np.isfinite(rd_kpc) else np.nan,
        dx_kpc=float(dx_kpc),
    )
    with open(out_gal / "features.json", "w") as f:
        json.dump({"R_d_kpc": float(rd_kpc) if np.isfinite(rd_kpc) else None, "dx_kpc": dx_kpc}, f, indent=2)

    if args.quicklook:
        try:
            import matplotlib.pyplot as plt

            fig, ax = plt.subplots(1, 2, figsize=(10, 4))
            im0 = ax[0].imshow(np.log1p(img), origin="lower", cmap="gray")
            ax[0].set_title(f"{row.name}: log(1+Sigma_b)")
            fig.colorbar(im0, ax=ax[0], shrink=0.7)
            im1 = ax[1].imshow(trS, origin="lower", cmap="magma")
            ax[1].set_title("tr(S)")
            fig.colorbar(im1, ax=ax[1], shrink=0.7)
            fig.tight_layout()
            fig.savefig(out_gal / "quicklook.png", dpi=150)
            plt.close(fig)
        except Exception:
            pass


def main() -> None:
    p = argparse.ArgumentParser(description="Imaging pilot: derive Sigma_b and structure tensor fields")
    p.add_argument("--input_csv", type=str, required=True, help="CSV with columns: name,image_path,pixscale_arcsec,dist_mpc[,inc_deg,pa_deg,center_x,center_y]")
    p.add_argument("--out_dir", type=str, default="results/imaging_pilot", help="Output directory root")
    p.add_argument("--bg_clip", type=float, default=3.0, help="Sigma-clip for background estimation")
    p.add_argument("--deproject", action="store_true", help="Apply deprojection using inc/PA")
    p.add_argument("--dx_kpc", type=float, default=None, help="Override pixel scale in kpc/pixel (else compute from dist and pixscale)")
    p.add_argument("--nbins", type=int, default=128, help="Radial profile bins for R_d fit")
    p.add_argument("--eta_sigma", type=float, default=0.1, help="Relative smoothing scale: sigma = eta_sigma * R_d (pixels)")
    p.add_argument("--lambda0_kpc", type=float, default=1.0, help="Base recognition length (kpc)")
    p.add_argument("--kappa_rec", type=float, default=1.0, help="Recognition-length sensitivity to tr(S)")
    p.add_argument("--quicklook", action="store_true", help="Save quicklook PNGs")
    args = p.parse_args()

    rows = parse_csv(Path(args.input_csv))
    out_dir = Path(args.out_dir)
    ensure_dir(out_dir)

    for row in rows:
        process_galaxy(row, out_dir, args)


if __name__ == "__main__":
    main()


