#!/usr/bin/env python3
"""
Build RS features (global-only) for SPARC Q=1 sample:
- Synthesizes a 2D proxy Σ_b(x,y) per galaxy from R_d and component ratios
- Computes RS fields (traceS, D_iso, ℓ_rec), profiles (n(r), ζ(r))
- Freezes global ξ thresholds.json from complexity scalars C_G
- Writes per-galaxy fields.npz, profiles.npz, features.json under out_root/<galaxy>

Inputs: SPARC master pickle (auto-discovered) and subset CSV (e.g., Q=1 list)
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Dict, Any, Optional, Set, Tuple, List

import numpy as np
import pandas as pd

sys.path.append(str(Path(__file__).resolve().parents[2]))
from active.scripts.rs_feature_builder import (
    build_fields_and_profiles_2d,
    complexity_scalar,
    assign_xi,
)


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


def synthesize_sigma_2d(nx: int, ny: int, R_d_kpc: float, gas_frac: float, bulge_frac: float, lx_kpc: float, ly_kpc: float) -> Tuple[np.ndarray, float, float]:
    dx_kpc = lx_kpc / nx
    dy_kpc = ly_kpc / ny
    x = np.linspace(-0.5 * lx_kpc + 0.5 * dx_kpc, 0.5 * lx_kpc - 0.5 * dx_kpc, nx)
    y = np.linspace(-0.5 * ly_kpc + 0.5 * dy_kpc, 0.5 * ly_kpc - 0.5 * dy_kpc, ny)
    X, Y = np.meshgrid(x, y, indexing="xy")
    R = np.sqrt(X ** 2 + Y ** 2)
    # Disk & gas exponentials; bulge: softened (Hernquist-like projected)
    disk = np.exp(-R / max(R_d_kpc, 1e-6))
    gas = np.exp(-R / max(1.7 * R_d_kpc, 1e-6))
    a_b = max(0.2 * R_d_kpc, 0.05)
    bulge = 1.0 / np.maximum((R ** 2 + a_b ** 2) ** 2, 1e-6)
    gas_w = np.clip(gas_frac, 0.0, 0.8)
    bulge_w = np.clip(bulge_frac, 0.0, 0.8)
    disk_w = np.clip(1.0 - gas_w - bulge_w, 0.0, 1.0)
    Sigma = disk_w * disk + gas_w * gas + bulge_w * bulge
    Sigma /= np.maximum(np.nanmax(Sigma), 1e-12)
    return Sigma.astype(np.float64), dx_kpc, dy_kpc


def main():
    ap = argparse.ArgumentParser(description="Build RS features for SPARC sample (global-only)")
    ap.add_argument("--subset_csv", type=str, default="results/bench_rs_per_galaxy.csv")
    ap.add_argument("--out_root", type=str, default="results/rs_features")
    ap.add_argument("--nx", type=int, default=96)
    ap.add_argument("--ny", type=int, default=96)
    ap.add_argument("--box_factor_xy", type=float, default=8.0)
    ap.add_argument("--lambda_rec_kpc", type=float, default=0.5)
    ap.add_argument("--A", type=float, default=7.0)
    ap.add_argument("--p", type=float, default=1.6)
    ap.add_argument("--limit", type=int, default=0, help="0 = all")
    args = ap.parse_args()

    mpath = get_master_path()
    master = load_master_table(mpath)
    subset = load_subset_names(args.subset_csv)
    if subset:
        master = {k: v for k, v in master.items() if str(k) in subset}

    out_root = Path(args.out_root)
    out_root.mkdir(parents=True, exist_ok=True)

    # Pass 1: compute complexities for thresholds
    names: List[str] = []
    complexities: List[float] = []
    count = 0
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
        r = r[ok]; v_obs = v_obs[ok]
        v_gas = v_gas[ok]; v_disk = v_disk[ok]; v_bul = v_bul[ok]
        if r.size < 5:
            continue
        R_d = float(g.get("R_d", 2.0))
        v_bar = np.sqrt(np.maximum(0.0, v_gas ** 2 + v_disk ** 2 + v_bul ** 2))
        gas_frac = float(np.nanmedian(np.where(v_bar > 0, (v_gas ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        bulge_frac = float(np.nanmedian(np.where(v_bar > 0, (v_bul ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        gas_frac = np.clip(gas_frac, 0.0, 0.8)
        bulge_frac = np.clip(bulge_frac, 0.0, 0.8)

        lx = 2.0 * args.box_factor_xy * R_d
        ly = 2.0 * args.box_factor_xy * R_d
        Sigma, dx_kpc, dy_kpc = synthesize_sigma_2d(args.nx, args.ny, R_d, gas_frac, bulge_frac, lx, ly)
        fields, profiles, scalars = build_fields_and_profiles_2d(Sigma, dx_kpc=dx_kpc, lambda_rec_kpc=args.lambda_rec_kpc, A=args.A, p=args.p)
        c_val = complexity_scalar(fields["traceS"], scalars["Rd_kpc"], dx_kpc)
        names.append(str(name))
        complexities.append(float(c_val))
        count += 1

    if len(complexities) == 0:
        print("No galaxies available for thresholds.")
        return

    arr = np.array(complexities, dtype=float)
    thresholds = [float(np.nanquantile(arr, q)) for q in [0.2, 0.4, 0.6, 0.8]]
    thr_json = {
        "thresholds": thresholds,
        "B": 5,
        "sample_size": len(complexities),
        "pixscale_kpc": float(2.0 * args.box_factor_xy * 2.0 / args.nx),  # nominal placeholder
        "lambda_rec_kpc": args.lambda_rec_kpc,
        "A": args.A,
        "p": args.p,
    }
    with open(out_root / "thresholds.json", "w") as f:
        json.dump(thr_json, f, indent=2)

    # Pass 2: write per-galaxy artifacts with ξ
    thr_list = thresholds; B = 5
    count = 0
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
        r = r[ok]; v_obs = v_obs[ok]
        v_gas = v_gas[ok]; v_disk = v_disk[ok]; v_bul = v_bul[ok]
        if r.size < 5:
            continue
        R_d = float(g.get("R_d", 2.0))
        v_bar = np.sqrt(np.maximum(0.0, v_gas ** 2 + v_disk ** 2 + v_bul ** 2))
        gas_frac = float(np.nanmedian(np.where(v_bar > 0, (v_gas ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        bulge_frac = float(np.nanmedian(np.where(v_bar > 0, (v_bul ** 2) / np.maximum(v_bar ** 2, 1e-12), np.nan)))
        gas_frac = np.clip(gas_frac, 0.0, 0.8)
        bulge_frac = np.clip(bulge_frac, 0.0, 0.8)

        lx = 2.0 * args.box_factor_xy * R_d
        ly = 2.0 * args.box_factor_xy * R_d
        Sigma, dx_kpc, dy_kpc = synthesize_sigma_2d(args.nx, args.ny, R_d, gas_frac, bulge_frac, lx, ly)
        fields, profiles, scalars = build_fields_and_profiles_2d(Sigma, dx_kpc=dx_kpc, lambda_rec_kpc=args.lambda_rec_kpc, A=args.A, p=args.p)
        c_val = complexity_scalar(fields["traceS"], scalars["Rd_kpc"], dx_kpc)
        xi, xi_bin, u_center = assign_xi(float(c_val), thr_list, B)

        out_dir = out_root / str(name)
        out_dir.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(out_dir / "fields.npz", **fields)
        np.savez_compressed(out_dir / "profiles.npz", **profiles)
        with open(out_dir / "features.json", "w") as f:
            json.dump({
                "Rd_kpc": float(scalars["Rd_kpc"]),
                "xi": float(xi),
                "xi_bin": int(xi_bin),
                "u_center": float(u_center),
                "g_ext_SI": 0.0,
                "pixscale_kpc": float(dx_kpc),
                "lambda_rec_kpc": float(args.lambda_rec_kpc),
                "A": float(args.A),
                "p": float(args.p),
                "thresholds_file": str((out_root / "thresholds.json").resolve()),
                "provenance": {"source": "build_sparc_features", "subset_csv": args.subset_csv},
            }, f, indent=2)
        count += 1

    print(f"Wrote thresholds and features for {count} galaxies under {out_root}")


if __name__ == "__main__":
    main()


