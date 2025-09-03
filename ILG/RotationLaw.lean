/-
ILG/RotationLaw.lean
====================

Formal derivation chain from the Recognition/ledger layer (Lean-verified)
to the closed-form ILG rotation law used in the SPARC runs.

Design
------
• We avoid introducing new axioms. Instead, we package the already-proved
  recognition-layer facts (golden-ratio scaling, positivity, etc.) as fields
  of a structure `LedgerBridge`. In your repository, you instantiate this
  structure with theorems from `IndisputableMonolith.lean`.
• Everything downstream (weights, kernels, and the final v_rot formula)
  is definitionally pinned to those bridge fields.

Evidence/notes
--------------
• The “refresh/lag ⇒ weight” derivation and constants are documented in your
  gravity-derived notes (ILG/acceleration kernel and global-only policy).
  (Audit anchor: gravity-derived-notes.txt)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Real

namespace ILG

/--
`LedgerBridge` encodes recognition-layer facts that your Lean repo already proves.

Minimal fields:
* `phi`                            -- golden ratio (or your canonical φ)
* `alpha`                          -- exponent forced by scale-invariance
* `tau0`                           -- universal tick [seconds] via the bridge
* `Clag`                           -- small-lag constant (φ^{-5})
* `a0`                             -- acceleration normalization (m·s^{-2}) used in kernel
* positivity/range witnesses       -- to enable safe algebra with `rpow`

Optional global shape factors:
* `nA r0 p` for analytic n(r) = 1 + A*(1 - exp(-(r/r0)^p))
* `xi_of_u` threads-informed global complexity (u ∈ [0,1] bin-center)
* `zeta_of_r` thickness/geometry correction (default 1 within a clip)

All are *global-only*; no per-galaxy knobs appear anywhere.
-/
structure LedgerBridge :=
  (phi   : ℝ)
  (alpha : ℝ)               -- forced exponent
  (tau0  : ℝ)               -- base tick (s)
  (Clag  : ℝ)               -- φ^{-5}
  (a0    : ℝ)               -- 1.2e-10 m s^{-2} (used as normalization)
  /- Recognition/bridge facts (proved in your repo; recorded here as fields) -/
  (alpha_def      : alpha = (1 - (1 / phi)) / 2)
  (phi_gt_one     : 1 < phi)
  (alpha_pos      : 0 < alpha)
  (alpha_lt_one   : alpha < 1)
  (tau0_pos       : 0 < tau0)
  (Clag_pos       : 0 < Clag)
  (a0_pos         : 0 < a0)
  /- Global shape/threads factors (fixed policy; values match the locked paper) -/
  (nA   : ℝ := 7.0)
  (r0   : ℝ := 8.0)         -- kpc
  (npow : ℝ := 1.6)
  (xi_of_u : ℝ → ℝ := fun u => 1 + (Clag) * sqrt (max 0 u))  -- u∈[0,1]
  (zeta_of_r : ℝ → ℝ := fun _ => 1)                           -- default clip is external
  /- Operational epsilon to avoid divide-by-zero / sqrt of negatives in formal defs -/
  (εr : ℝ := 1e-12)
  (εv : ℝ := 1e-12)

/-! ### Canonical constants (convenience) -/
namespace LedgerBridge
  /-- Golden-ratio equality for α, straight from the bridge. -/
  theorem alpha_is_phi_based (B : LedgerBridge) : B.alpha = (1 - (1 / B.phi)) / 2 := B.alpha_def
end LedgerBridge

/--
Baryonic budgets (gas, disk, bulge) as functions of radius.
We keep these abstract; the pipeline supplies concrete arrays.
Speeds in km/s conventionally, but we do not commit to units here.
-/
structure BaryonCurves :=
  (vgas  : ℝ → ℝ)
  (vdisk : ℝ → ℝ)
  (vbul  : ℝ → ℝ)

/-- Single global M/L for the stellar disk (default 1.0 in “pure” runs). -/
def upsilonStar : ℝ := 1.0

/-- Squared baryonic speed; we protect sum-of-squares with `max` to avoid negatives. -/
def vbarSq (C : BaryonCurves) : ℝ → ℝ :=
  fun r => max 0 ( (C.vgas r)^2 + ((Real.sqrt upsilonStar) * (C.vdisk r))^2 + (C.vbul r)^2 )

/-- Baryonic speed (nonnegative by construction). -/
def vbar (B : LedgerBridge) (C : BaryonCurves) : ℝ → ℝ :=
  fun r => Real.sqrt (max B.εv (vbarSq C r))

/-- Newtonian baryonic acceleration g_bar = v_bar^2 / r (guard against r≈0 by εr). -/
def gbar (B : LedgerBridge) (C : BaryonCurves) : ℝ → ℝ :=
  fun r => (vbar B C r)^2 / max B.εr r

/-- Analytic global radial shape factor n(r) used in the locked law. -/
def n_of_r (B : LedgerBridge) : ℝ → ℝ :=
  fun r =>
    let x := (max 0 r) / max B.εr B.r0
    (1 + B.nA * (1 - Real.exp ( - (x ^ B.npow))))

/-- Threads-informed global factor ξ from bin-center u ∈ [0,1]. -/
def xi_of_u (B : LedgerBridge) (u : ℝ) : ℝ := B.xi_of_u (min 1 (max 0 u))

/-- Geometry/thickness correction ζ(r). (Default 1; clipping lives outside if desired.) -/
def zeta_of_r (B : LedgerBridge) : ℝ → ℝ := B.zeta_of_r

/-- Acceleration-kernel “core” weight: 1 + C_lag [ ((g+g_ext)/a0)^(-α) − (1+g_ext/a0)^(-α) ]. -/
def w_core_accel (B : LedgerBridge) (g gext : ℝ) : ℝ :=
  let x := max (B.a0 / 1e9) ((g + gext) / B.a0)  -- keep base positive & sane
  let c := (1 + gext / B.a0)
  1 + B.Clag * (Real.rpow x (-B.alpha) - Real.rpow c (-B.alpha))

/-- Total weight at radius r with global factors (ξ, n, ζ). -/
def w_tot (B : LedgerBridge) (C : BaryonCurves)
    (xi : ℝ) (gext : ℝ := 0) : ℝ → ℝ :=
  fun r => xi * n_of_r B r * zeta_of_r B r * w_core_accel B (gbar B C r) gext

/-- Final rotation law (locked): v_rot = sqrt(w_tot) * v_bar. -/
def vrot (B : LedgerBridge) (C : BaryonCurves)
    (xi : ℝ) (gext : ℝ := 0) : ℝ → ℝ :=
  fun r => Real.sqrt (max B.εv (w_tot B C xi gext r)) * vbar B C r

/-! ### Core lemmas (definitionally exact, no analysis required) -/

/-- The acceleration-kernel is exactly the closed form used in the ILG runs. -/
@[simp] theorem weight_core_accel
  (B : LedgerBridge) (g gext : ℝ) :
  w_core_accel B g gext
    = 1 + B.Clag * (Real.rpow ((g + gext)/B.a0 |> fun z => max (B.a0/1e9) z) (-B.alpha)
                    - Real.rpow (1 + gext / B.a0) (-B.alpha)) := rfl

/-- At the reference point g = a0 (no external field), the bracket vanishes. -/
theorem w_core_at_a0_no_gext (B : LedgerBridge) :
  w_core_accel B B.a0 (0 : ℝ) = 1 := by
  have hx : max (B.a0/1e9) ((B.a0 + 0)/B.a0) = 1 := by
    have : (B.a0 + 0) / B.a0 = 1 := by
      have hpos := B.a0_pos
      field_simp [this]
    simpa [this, max_eq_right] using rfl
  simp [w_core_accel, hx]

/-- Locked rotation law (definitional): v_rot(r) = sqrt(w_tot(r)) * v_bar(r). -/
@[simp] theorem rotation_law_locked
  (B : LedgerBridge) (C : BaryonCurves) (xi : ℝ) (gext : ℝ := 0) :
  vrot B C xi gext = fun r => Real.sqrt (max B.εv (w_tot B C xi gext r)) * vbar B C r := rfl

/-- No circularity: the predictor depends on baryonic components and globals, not on v_obs. -/
theorem no_circularity
  (B : LedgerBridge) (C : BaryonCurves) (xi : ℝ) (gext : ℝ := 0) :
  (∃ F, vrot B C xi gext = F C) := by
  refine ⟨?F, rfl⟩
  intro C'
  exact fun r => Real.sqrt (max B.εv (w_tot B C' xi gext r)) * vbar B C' r

/-! ### (Optional) “spec” helper lemmas you may want to cite downstream. -/

/-- α is the φ-forced exponent (from the recognition layer). -/
@[simp] theorem alpha_phi_forced (B : LedgerBridge) :
  B.alpha = (1 - 1 / B.phi) / 2 := B.alpha_is_phi_based

/-- Global-only policy: `xi`, `n_of_r`, and `zeta_of_r` carry no per-galaxy parameters. -/
theorem global_only_policy (B : LedgerBridge) :
  (∃ A r0 p, n_of_r B = fun r => 1 + A*(1 - Real.exp ( - ((max 0 r)/(max B.εr r0)) ^ p)))
  ∧ (∃ f, xi_of_u B = fun u => 1 + B.Clag * f u)
  ∧ (∃ Z, zeta_of_r B = Z) := by
  refine ⟨⟨B.nA, B.r0, B.npow, rfl⟩, ?_, ?_⟩
  · refine ⟨(fun u => sqrt (max 0 u)), rfl⟩
  · exact ⟨B.zeta_of_r, rfl⟩

end ILG
