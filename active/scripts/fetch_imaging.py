#!/usr/bin/env python3
"""
Fetch imaging cutouts from NASA SkyView by object name and save FITS files.

Inputs CSV (same format as imaging_pilot.py):
  name,image_path,pixscale_arcsec,dist_mpc[,inc_deg,pa_deg,center_x,center_y]

Only the fields name, image_path, pixscale_arcsec, dist_mpc are required.

For each row, we request a FITS cutout from the desired survey with
Scale=pixscale_arcsec (arcsec/pixel) and Pixels computed to cover a field-of-view
of fov_kpc across. If the primary survey fails, a fallback survey is attempted.
If both fail, a placeholder FITS is written so downstream scripts can proceed.
"""
from __future__ import annotations

import argparse
import csv
import math
import sys
from pathlib import Path
from typing import Optional

import numpy as np
from astropy.io import fits
from urllib.parse import urlencode
from urllib.request import urlopen


KPC_PER_ARCSEC_PER_MPC = 4.84813681109536e-3  # kpc per arcsec per Mpc


def ensure_dir(p: Path) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)


def compute_pixels(dist_mpc: float, pixscale_arcsec: float, fov_kpc: float, clamp_min: int = 512, clamp_max: int = 8192) -> int:
    # total field-of-view across in arcsec
    # kpc per arcsec at distance D is KPC_PER_ARCSEC_PER_MPC * D
    # so arcsec needed for fov_kpc is fov_kpc / (KPC_PER_ARCSEC_PER_MPC * D)
    denom = max(KPC_PER_ARCSEC_PER_MPC * max(dist_mpc, 1e-6), 1e-12)
    fov_arcsec = float(fov_kpc) / denom
    pixels = int(math.ceil(fov_arcsec / max(pixscale_arcsec, 1e-6)))
    return max(clamp_min, min(pixels, clamp_max))


def skyview_url(name: str, scale_arcsec: float, pixels: int, survey: str) -> str:
    params = {
        "Position": name,
        "Survey": survey,
        "Return": "FITS",
        "Scale": f"{scale_arcsec:.6f}",  # arcsec/pixel
        "Pixels": str(int(pixels)),
        "Sampler": "Lanczos3",
        "Projection": "Tan",
    }
    return "https://skyview.gsfc.nasa.gov/current/cgi/pskcall?" + urlencode(params)


def try_fetch(name: str, out_path: Path, pixscale_arcsec: float, dist_mpc: float, fov_kpc: float, survey: str, fallback_survey: Optional[str], timeout: int) -> bool:
    pixels = compute_pixels(dist_mpc, pixscale_arcsec, fov_kpc)
    url = skyview_url(name, pixscale_arcsec, pixels, survey)
    try:
        with urlopen(url, timeout=timeout) as resp:
            data = resp.read()
        if data and data[:6] in (b"SIMPLE", b"XTENSION") or (data and data[:30].lower().find(b"end") >= 0):
            ensure_dir(out_path)
            out_path.write_bytes(data)
            return True
    except Exception:
        pass

    if fallback_survey:
        url2 = skyview_url(name, pixscale_arcsec, pixels, fallback_survey)
        try:
            with urlopen(url2, timeout=timeout) as resp:
                data = resp.read()
            if data and data[:6] in (b"SIMPLE", b"XTENSION") or (data and data[:30].lower().find(b"end") >= 0):
                ensure_dir(out_path)
                out_path.write_bytes(data)
                return True
        except Exception:
            pass

    return False


def write_placeholder(out_path: Path, pixscale_arcsec: float, dist_mpc: float, fov_kpc: float) -> None:
    pixels = compute_pixels(dist_mpc, pixscale_arcsec, fov_kpc)
    # Simple centered Gaussian disk placeholder to keep downstream working
    ny = nx = int(pixels)
    y, x = np.mgrid[0:ny, 0:nx]
    cx = (nx - 1) / 2.0
    cy = (ny - 1) / 2.0
    rr2 = (x - cx) ** 2 + (y - cy) ** 2
    sigma_pix = 0.15 * min(nx, ny)
    img = np.exp(-rr2 / (2.0 * sigma_pix * sigma_pix)).astype(np.float32)
    hdu = fits.PrimaryHDU(img)
    # Degrees per pixel
    cd = pixscale_arcsec / 3600.0
    hdu.header["CDELT1"] = -cd
    hdu.header["CDELT2"] = cd
    hdu.header["BUNIT"] = "arb"
    hdu.header["COMMENT"] = "Placeholder image (fetch failed)"
    fits.HDUList([hdu]).writeto(out_path, overwrite=True)


def main() -> None:
    ap = argparse.ArgumentParser(description="Fetch FITS cutouts from SkyView for imaging pilot")
    ap.add_argument("--input_csv", required=True, help="CSV: name,image_path,pixscale_arcsec,dist_mpc,...")
    ap.add_argument("--survey", default="WISE 3.4 Micron", help="Primary SkyView survey name")
    ap.add_argument("--fallback_survey", default="DSS2 Red", help="Fallback survey if primary fails")
    ap.add_argument("--fov_kpc", type=float, default=40.0, help="Target field of view across, in kpc")
    ap.add_argument("--timeout", type=int, default=60, help="Per-request timeout (s)")
    args = ap.parse_args()

    rows = []
    with open(args.input_csv, newline="") as f:
        reader = csv.DictReader(f)
        for r in reader:
            rows.append(r)

    successes = 0
    for r in rows:
        name = r["name"].strip()
        image_path = Path(r["image_path"]).expanduser()
        pixscale_arcsec = float(r["pixscale_arcsec"]) if r.get("pixscale_arcsec") else 1.5
        dist_mpc = float(r["dist_mpc"]) if r.get("dist_mpc") else 10.0
        ok = try_fetch(name, image_path, pixscale_arcsec, dist_mpc, args.fov_kpc, args.survey, args.fallback_survey, args.timeout)
        if not ok:
            write_placeholder(image_path, pixscale_arcsec, dist_mpc, args.fov_kpc)
        successes += 1 if ok else 0
        print(f"[{name}] {'downloaded' if ok else 'placeholder written'} -> {image_path}")

    print(f"Completed {len(rows)} targets; {successes} downloaded, {len(rows) - successes} placeholders.")


if __name__ == "__main__":
    main()


