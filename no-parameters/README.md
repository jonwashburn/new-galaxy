# No-Parameters ILG

- Policy: pure-global, no per-galaxy tuning.
- Kernels: w_g (or globally chosen), α=0.191, C_lag=φ^-5, a0 fixed.
- ξ_threads: f_gas discretized by global quintiles (bins computed from a non-kinematic proxy to avoid circularity; prefers component-only proxy f_gas_proxy over any v_obs-derived quantity).
- n(r): analytic (7,8,1.6) with global disc-weight normalization.
- ζ(r): h_z/R_d=0.25 clipped.
- Errors: σ0, fractional floor, beam (catalog preferred), asymmetry, turbulence.
- Masks: inner-beam via catalog beam if present, else r≥0.3 R_d.

## Reproduce

Artifacts write to no-parameters/results/.

Notes on circularity avoidance:
- The complexity proxy ξ uses global quantile bins from f_gas_proxy computed from component curves (v_gas, v_disk, v_bul) only; it does not use v_obs.
- This keeps the ILG weight independent from the observed velocities used in the fit, maintaining a clean global-only policy.
