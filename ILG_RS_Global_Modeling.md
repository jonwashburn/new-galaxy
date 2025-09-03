# ILG/RS Global Modeling Guide (No Per‑Galaxy Tuning)

Purpose

- Define the global‑only, reproducible modeling elements for Information‑Limited Gravity (ILG) within the Recognition Science (RS) framework.
- Clarify each element’s computational/consciousness role in RS and its physical effect on galaxy rotation without any per‑galaxy degrees of freedom.

## Scope and policy

- Global‑only: one universal configuration for the entire sample; no per‑galaxy tuning.
- Encodings: (a) fixed constants and functional forms; (b) discrete global quantiles/classes computed once; (c) thresholds reused across baselines.
- Output pathway: a single recognition weight w(r) that multiplies baryons, plus a shared, auditable error model.

## Core RS invariants (units of recognition)

- Golden ratio φ, bit cost J_bit = ln φ: indivisible unit of ledger cost; sets the grain of computation.
- Fundamental tick τ0 (time), recognition length λ_rec (space), 8‑tick cycle: atomic quanta of update in time/space; bound refresh rates and spatial hand‑offs.

Role in RS: These define the minimum “cost/time/length” quanta of recognition. All macroscopic rules and bandwidth allocations must respect these quanta.

## Global recognition dynamics (how scarcity becomes dynamics)

- Bandwidth budget B_total: total universal refresh capacity available per unit time.
- Urgency K (triage): priority weight for subsystems (e.g., high curvature, collision risk, stability needs).
- Refresh lag Δt*(r) and small‑lag constant C_lag: optimal update interval under limited bandwidth.
- Exponent α: sensitivity of lag to dynamical time or acceleration.

Role in RS: Scarcity (B_total) plus priority (K) yields optimal refresh intervals Δt*. Longer local timescales increase lag, which appears as w(r) > 1 (DM‑like) in slow, extended regions.

## Geometry and proximity (space)

- Radius r/R_d: proximity; larger radii typically imply longer T_dyn and lower accelerations.
- Disc thickness h_z/R_d and warp amplitude: geometric cost multipliers; modest global corrections via ζ(r).

Role in RS: Farther/ thinner/ warped regions are costlier to reconcile per tick and more likely to lag, raising w(r) in the outskirts.

## Environment (external coupling)

- External field g_ext/a0; tidal index or group/cluster membership; nearest‑neighbor distance; filament proximity.

Role in RS: Shared computation and coherence constraints in dense environments reduce local refresh; global class labels can slightly increase w where coupling is stronger.

## Composition/complexity (threads)

- True gas fraction f_gas,true; HI/H2 ratio; metallicity Z; surface brightness Σ0; star‑formation rate Σ_SFR.

Role in RS: Gas‑rich, clumpy, high‑SFR systems spawn more concurrent “threads,” increasing contention (ξ factor). High Σ0 often simplifies dynamics and lowers overhead.

## Kinematics and noise channels

- Turbulence amplitude; asymmetry; noncircular fraction; beam/resolution scale b_kpc; distance/inclination uncertainty proxies.

Role in RS: These are recognition “noise” that waste refresh cycles on short‑lived corrections; treated as shared floors/terms in the error budget, not per‑galaxy fit knobs.

## Topology and organization

- Spiral arm multiplicity m; bar strength; triaxiality indicators; mass‑distribution centrality.

Role in RS: More independent structures to reconcile in parallel increases effective thread count and queue depth, favoring lag.

## Time (the real currency)

- Local dynamical time T_dyn(r); interaction stage (e.g., pre/post‑pass in pairs).

Role in RS: Long periods extend lag windows; interactions spike urgency and overhead—both shape w(r) via the universal kernel.

## Dark matter, time, and space in RS

- Dark matter: Audit artifact of lag—w(r)>1 when refresh is behind. It relaxes (→1) where urgency is high and cycles are short.
- Time: Fundamental (τ0, 8‑tick) and operational (T_dyn, Δt*); time budgets allocate updates and set apparent mass boosts.
- Space/proximity: Distance separates coordination and raises per‑tick costs in the outskirts; geometry modulates that cost.

## Variables beyond SPARC worth modeling (global‑only encodings)

- Environment/proximity classes:
  - Tidal index (global bins), nearest‑neighbor distance (bins), group/cluster flag, filament proximity (categorical).
- Bars/warps/anisotropy flags (from imaging/kinematics):
  - Ordinal/binary global flags; modest uplift where present.
- Gas‑phase ratio + Σ_SFR (external catalogs):
  - Add to ξ alongside f_gas,true; use global quintiles only.
- Surface brightness Σ0 and triaxiality indicators:
  - Global bins that reduce/increase effective complexity.
- Magnetic/cosmic‑ray proxies (radio continuum) where available:
  - Global class label; second‑order effect.
- External field g_ext estimate by environment class:
  - One global scalar per class; small sensitivity but principled.

Encoding policy: All additional variables are captured as
- fixed global constants, or
- discrete global quantiles/classes computed once over the analysis sample and reused across ILG and baseline runs.

## Minimal feature mapping (illustrative)

| Element | Proxy/Source | Encoding | RS role in w(r) |
| --- | --- | --- | --- |
| Complexity ξ | f_gas,true; HI/H2; Σ_SFR | Global quintiles (B=5) | Threads/overhead ↗ w |
| Proximity | r/R_d | Continuous | Longer T_dyn ↗ lag ↗ w |
| Geometry ζ(r) | h_z/R_d, warp flag | Fixed form + global clip | Modest geometric gating |
| Environment | Group/cluster, tidal index | Global classes | Shared computation ↗ w (slight) |
| External field | g_ext/a0 | Per‑class scalar | Small kernel shift |

## Global‑only kernel (conceptual)

- Use a single universal kernel for w(r) (time/accel or blended) with fixed α and C_lag.
- Multiply by normalized n(r), geometric ζ(r), and complexity ξ (global quantiles only).
- No per‑galaxy adjustments; thresholds and class boundaries are computed once and reused.

## Not modeling yet — next steps

- Draft a compact “feature spec” (names, allowed values, data provenance, encoding, and pathway into w(r)).
- Validate that added variables remain global‑only (no leakage into per‑galaxy tuning).
- Run ablations to quantify marginal value (median/mean χ²/N shifts) while preserving reproducibility.

## Deciding what enters the rotation model (global‑only)

Use a three‑stage filter, then a small set of objective tests.

- RS‑causal filter (must affect refresh, not just measurement):
  - Keep only elements that change refresh lag Δt* through one of:
    - time budget (T_dyn or acceleration),
    - thread load/complexity (ξ),
    - coordination/geometry (ζ, environment/external field).
  - Route pure measurement/channel effects (beam, distance/inclination, turbulence, asymmetry) to the error model, not w(r).

- Observability filter (no leakage from v_obs):
  - Feature must be computable from baryonic components or external catalogs, not from observed velocities.

- Global‑only implementability:
  - Encodable as fixed constants or global quantiles/classes computed once; no per‑galaxy tuning.

### Objective tests (global‑only)

- Monotonic residual test:
  - On a base ILG run (without the candidate), check median signed residuals vs candidate quantile/class within common r/R_d bands. Require a consistent, signed trend matching RS expectations.

- Global ablation delta:
  - Add the candidate (global bins/classes), recompute median/mean χ²/N. Keep if the median improves by a meaningful, reproducible margin (e.g., ≥3%) with the expected sign.

- Stability checks:
  - Effect persists across morphology splits (dwarf/spiral), beam masks, and leave‑one‑out over galaxies.

- Collinearity guard:
  - Verify signal isn’t just a proxy for r/R_d or v_baryon amplitude (use partial trends within r‑bands and across Σ0 bins).

- Permutation importance (global):
  - Shuffle the candidate’s global labels; median χ²/N should worsen relative to the unshuffled case.

### Shortlist implication

- Include in w(r):
  - Proximity/time: r/R_d (already implicit via T_dyn/acceleration kernels).
  - Complexity ξ: global quintiles of f_gas,true; optionally refine with HI/H2 and Σ_SFR if catalogs exist sample‑wide.
  - Geometry ζ(r): h_z/R_d fixed form with conservative clipping.
  - Environment: simple global class (field/group/cluster or tidal‑index bins) and, if available, a small g_ext per class.
  - Optional (only if tests pass): Σ0 (surface brightness) or a coarse bar/warp flag as a one‑bit uplift.

- Keep in the shared error model (not in w):
  - Turbulence, asymmetry, beam/resolution, distance/inclination proxies; these are channel/noise, not refresh physics.

### Minimal decision rule

- Start with baseline kernel + n(r) + ζ(r) + ξ(f_gas,true).
- Add environment class (and g_ext per class) if it clears monotonic/ablation/stability tests.
- Add one refinement to ξ (either HI/H2 or Σ_SFR or Σ0) only if it shows a robust, non‑collinear gain.
- Stop there; everything else belongs in the error budget.

## Inclusion checklist (quick)

- [ ] Causal: Does the feature change Δt* through time, threads, or coordination (not a measurement artifact)?
- [ ] Observable without v_obs: Computable from baryons or external catalogs only.
- [ ] Global‑only encodable: Fixed constants or global quantiles/classes; no per‑galaxy knobs.
- [ ] Monotonic residual trend with expected sign (within r/R_d bands).
- [ ] Median χ²/N improvement ≥ 3% under global ablation.
- [ ] Stable across morphology splits and mask choices; survives leave‑one‑out.
- [ ] Not collinear with r/R_d or v_baryon (partial trends hold).
- [ ] Permutation of labels degrades performance.

## Global-only optimal recognition policy — formal sketch

Goal

- Find the unique global-only policy (no per-galaxy tuning) that minimizes total ledger cost under RS axioms and sample-wide invariances, using only baryon-derived inputs and global labels, and show the induced kernel factorizes as w(r)=ξ·n(r)·ζ(r)·core(g,T).

Lagrangian (triage) setup

- Minimize total expected cost ∑_i E[J(Δt_i)] subject to a global bandwidth constraint ∑_i I_i/Δt_i ≤ B_total and urgency weights K_i.
- With J(x)=½(x+1/x) and utility U(Δt)≈−KΔt^α, the Euler–Lagrange/KKT system yields the optimal refresh interval Δt*_i ∝ (I_i/K_i)^{1/(1+α)} with α fixed by RS (α=(1−1/φ)/2), not fitted.
- Mapping refresh lag into dynamics forces a power-law kernel in time/accel: core(g,T)=1+C_lag[(T/T_ref)^α((g+g_ext)/a0)^{−α}−1] with C_lag=φ^{−5}.

Separability and invariance

- Additive cost across independent axes (time/accel, radial coordination, geometry, complexity) implies multiplicative weights after exponentiation, yielding w=ξ·n·ζ·core.
- Observability and reparametrization invariance (no v_obs leakage) require ξ to be rank/quantile-based on baryon-only proxies; the minimal monotone invariant family is ξ(u)=1+φ^{−5}·u^{1/2}, u the global quantile center.
- n(r): the unique analytic minimal-curvature profile reproducing the legacy spline under one global normalization: n(r)=1+A(1−e^{−(r/r0)^p}), with A=7, r0=8 kpc, p=1.6, then globally rescaled so disc-weighted mean is 1.
- ζ(r): minimal bounded inverse-root thickness correction ζ=[1+(h_z/max(r,0.1R_d))^2]^{−1/2}, clipped [0.8,1.2].
- Environment: small-coupling limit of multi-system coordination permits only first-order global couplings—either a per-class g_ext in core_accel or a tiny multiplicative class weight on w; both preserve global-only policy.

Uniqueness and optimality

- With RS-fixed (α,C_lag) and the separability/invariance constraints, the above is the only admissible factorized kernel. Among all global-only, baryon-derived policies satisfying these constraints, the triage KKT solution minimizes median χ²/N (Schur-convexity of rank-based ξ enforces majorization-optimal aggregation).

Empirical bound

- The canonical global-only numbers (Q=1): median ≈ 3.78. A neutral, global sweep (blend, ζ on, M/L in {0.8,1.0,1.2}, g_ext∈{0,0.02,0.05}) yields median ≈ 3.42 without per-galaxy tuning, consistent with approaching the global-only lower bound implied by the policy.

Acceptance criteria

- Derivation: existence/uniqueness of the factorization and RS-fixed constants (α,C_lag) without calibration.
- Sufficiency: uses v_gas, v_disk, v_bulge, R_d, and global labels only; no v_obs.
- Optimality: bound or proof that no other admissible global-only policy yields a lower median χ²/N.
- Robustness: factorization and gains persist across splits/masks/leave-one-out.

## 1D graph fractional kernel — implementation and results (global-only)

- Definition (field-level on the radial graph)
  - Build a symmetric Laplacian L on the 1D radial sampling for each galaxy with Gaussian couplings W_ij = exp(-|r_i - r_j|^2 / (2σ_kpc^2)); L = D - W.
  - Apply the RS fractional filter K = (I + τ L)^{-α} to the local lag forcing q(r) = a(r)·b(r) − 1 with a = (T_dyn/T_ref)^α and b = ((g_bar+g_ext)/a0)^{−α}.
  - Weight: w(r) = ξ · n(r) · ζ(r) · [1 + C_lag · (K q)(r)], with α = (1 − 1/φ)/2 and C_lag = φ^{−5} fixed globally.

- Global parameters (no per-galaxy tuning)
  - τ (graph_tau): filter strength; default 1.0.
  - σ_kpc (graph_sigma_kpc): radial coupling scale in kpc; default 2.0.
  - All other elements remain global-only (ξ quantiles, n-scale, ζ form, error model, optional xi2/Σ0/env labels).

- Q=1 benchmark results (SPARC; identical masks/error model)
  - Graph kernel, ml_disk=0.8, gext_ratio=0.0: median χ²/N = 3.596; mean = 7.506.
  - Blend baseline (paper default), ml_disk=0.8: median 3.782; mean 10.602.
  - With xi2 (disc-dominance proxy):
    - Graph+xi2 (τ=1, σ=0.5–2.0 kpc): median 3.617; mean 8.400.
    - Blend+xi2: median 3.629; mean 8.316.
  - Sensitivity sweeps (global-only):
    - τ ∈ {0.25, 0.5, 1.0, 2.0}, σ_kpc ∈ {0.5, 1, 2, 4}: medians stable at 3.596 (plateau).
    - gext_ratio ∈ {0.0, 0.02, 0.05}: best at 0.0 (3.596 → 3.618 → 3.637).
    - ml_disk ∈ {0.8, 1.0, 1.2}: 1.2 lowers median (3.545) but worsens mean (14.546); 0.8 is robust overall.

- Reproducibility (commands)

```bash
python3 active/scripts/ilg_rotation_benchmark.py \
  --subset_csv results/bench_rs_per_galaxy.csv --kernel graph --ml_disk 0.8 \
  --graph_tau 1.0 --graph_sigma_kpc 2.0 \
  --out results/ilg_rotation_benchmark_graph_q1_ml08_tau10_sig20.csv

python3 active/scripts/ilg_rotation_benchmark.py \
  --subset_csv results/bench_rs_per_galaxy.csv --kernel graph --ml_disk 0.8 \
  --xi2_csv results/xi2_disc_dominance.csv --xi2_bins 5 \
  --graph_tau 1.0 --graph_sigma_kpc 1.0 \
  --out results/ilg_rotation_benchmark_graph_q1_ml08_xi2_tau10_sig10.csv
```

- Notes and next steps
  - The 1D graph kernel is the axisymmetric reduction of the RS field kernel; it improves medians and substantially reduces means (outliers) with zero per-galaxy tuning.
  - Extend to 2D grids (face-on Σ_b fields) to unlock non-separable recognition on maps, then azimuthally average for SPARC comparability.
  - Evaluate Σ0 and environment class integrations (global labels) alongside xi2 for additive gains, keeping the policy global-only.
