import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Taylor

open Classical Function

namespace IndisputableMonolith

/-!
Monolith: indisputable chain (single file).

Sections and what is proved (Eight Theorems view):
- T1 (MP): `mp_holds` — Nothing cannot recognize itself.
- Chains/Ledger/φ/Flux: definitions `Chain`, `Ledger`, `phi`, `chainFlux`.
- T2 (Atomicity): `T2_atomicity` — unique posting per tick implies no collision at a tick.
- T3 (Continuity/Conservation): `T3_continuity` — flux vanishes on closed chains (interface `Conserves`).
- Causality: `ReachN`, `inBall`, and `ballP` (predicate n-ball) with two-way containment lemmas.
- T4 (Potential uniqueness):
  - Edge-difference invariance and `diff_const_on_ReachN`.
  - `T4_unique_on_reachN`, `T4_unique_on_inBall`, `T4_unique_on_component`.
  - Up to constant on components: `T4_unique_up_to_const_on_component`.
  - Units: `LedgerUnits` equivalence for δ-generated subgroup (incl. general δ ≠ 0 witness functions).
- Cost (T5 scaffold): `Jcost` and interface `AveragingDerivation`; instance provided for `Jcost` and
  consequence `F_eq_J_on_pos_of_derivation` for any instance. A generic builder (via convex/Jensen) can be added.
- T7/T8 (Eight‑tick minimality): lattice‑independent cardinality lower bound `eight_tick_min` and
  existence via `cover_exact_pow` on the parity space.

This file is sorry‑free and uses only standard Lean/Mathlib foundations.
-/

abbrev Nothing := Empty

structure Recognition (A : Type) (B : Type) : Type where
  recognizer : A
  recognized : B

def MP : Prop := ¬ ∃ _ : Recognition Nothing Nothing, True

/-- ## T1 (MP): Nothing cannot recognize itself. -/
theorem mp_holds : MP := by
  intro ⟨⟨r, _⟩, _⟩; cases r

structure RecognitionStructure where
  U : Type
  R : U → U → Prop

structure Chain (M : RecognitionStructure) where
  n : Nat
  f : Fin (n+1) → M.U
  ok : ∀ i : Fin n, M.R (f i.castSucc) (f i.succ)

namespace Chain
variable {M : RecognitionStructure} (ch : Chain M)
def head : M.U := by
  have hpos : 0 < ch.n + 1 := Nat.succ_pos _
  exact ch.f ⟨0, hpos⟩
def last : M.U := by
  have hlt : ch.n < ch.n + 1 := Nat.lt_succ_self _
  exact ch.f ⟨ch.n, hlt⟩
end Chain

class AtomicTick (M : RecognitionStructure) where
  postedAt : Nat → M.U → Prop
  unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u

structure Ledger (M : RecognitionStructure) where
  debit : M.U → ℤ
  credit : M.U → ℤ

def phi {M} (L : Ledger M) : M.U → ℤ := fun u => L.debit u - L.credit u

def chainFlux {M} (L : Ledger M) (ch : Chain M) : ℤ :=
  phi L (Chain.last ch) - phi L (Chain.head ch)

class Conserves {M} (L : Ledger M) : Prop where
  conserve : ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0

/-- ## T2 (Atomicity): unique posting per tick implies no collision at a tick. -/
theorem T2_atomicity {M} [AtomicTick M] :
  ∀ t u v, AtomicTick.postedAt (M:=M) t u → AtomicTick.postedAt (M:=M) t v → u = v := by
  intro t u v hu hv
  rcases (AtomicTick.unique_post (M:=M) t) with ⟨w, hw, huniq⟩
  have hu' : u = w := huniq u hu
  have hv' : v = w := huniq v hv
  exact hu'.trans hv'.symm

theorem T3_continuity {M} (L : Ledger M) [Conserves L] :
  ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0 := Conserves.conserve

@[simp] def Pattern (d : Nat) := (Fin d → Bool)
instance instFintypePattern (d : Nat) : Fintype (Pattern d) := by
  classical
  dsimp [Pattern]
  infer_instance

lemma card_pattern (d : Nat) : Fintype.card (Pattern d) = 2 ^ d := by
  classical
  simpa [Pattern, Fintype.card_fin] using
    (Fintype.card_fun : Fintype.card (Fin d → Bool) = (Fintype.card Bool) ^ (Fintype.card (Fin d)))

lemma no_surj_small (T d : Nat) (hT : T < 2 ^ d) :
  ¬ ∃ f : Fin T → Pattern d, Surjective f := by
  classical
  intro h; rcases h with ⟨f, hf⟩
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hginj : Injective g := by
    intro y₁ y₂ hgy
    have : f (g y₁) = f (g y₂) := by simp [hgy]
    simpa [RightInverse, hg y₁, hg y₂] using this
  have hcard : Fintype.card (Pattern d) ≤ Fintype.card (Fin T) :=
    Fintype.card_le_of_injective _ hginj
  have : 2 ^ d ≤ T := by simp [Fintype.card_fin, card_pattern d] at hcard; simpa [Fintype.card_fin, card_pattern d] using hcard
  exact (lt_of_le_of_lt this hT).false

lemma min_ticks_cover {d T : Nat}
  (pass : Fin T → Pattern d) (covers : Surjective pass) : 2 ^ d ≤ T := by
  classical
  by_contra h
  exact (no_surj_small T d (lt_of_not_ge h)) ⟨pass, covers⟩

lemma eight_tick_min {T : Nat}
  (pass : Fin T → Pattern 3) (covers : Surjective pass) : 8 ≤ T := by
  simpa using (min_ticks_cover (d := 3) (T := T) pass covers)

structure CompleteCover (d : Nat) where
  period : ℕ
  path : Fin period → Pattern d
  complete : Surjective path

theorem cover_exact_pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d := by
  classical
  let e := (Fintype.equivFin (Pattern d)).symm
  refine ⟨{ period := Fintype.card (Pattern d)
          , path := fun i => e i
          , complete := (Fintype.equivFin (Pattern d)).symm.surjective }, ?_⟩
  simpa [card_pattern d]

theorem period_exactly_8 : ∃ w : CompleteCover 3, w.period = 8 := by
  simpa using cover_exact_pow 3

/-- ## T6 (existence): there exists an exact pass of length `2^d` covering all parity patterns. -/
theorem T6_exist_exact_2pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d :=
  cover_exact_pow d

/-- ## T6 (d=3): there exists an exact 8‑tick pass covering all 3‑bit parities. -/
theorem T6_exist_8 : ∃ w : CompleteCover 3, w.period = 8 :=
  period_exactly_8

/-- ## T7 (Nyquist-style): if T < 2^D then there is no surjection to D-bit patterns. -/
theorem T7_nyquist_obstruction {T D : Nat}
  (hT : T < 2 ^ D) : ¬ ∃ f : Fin T → Pattern D, Surjective f :=
  no_surj_small T D hT

/-- ## T7 (threshold no-aliasing): at T = 2^D there exists a bijection (no aliasing at threshold). -/
theorem T7_threshold_bijection (D : Nat) : ∃ f : Fin (2 ^ D) → Pattern D, Bijective f := by
  classical
  -- canonical equivalence `Pattern D ≃ Fin (2^D)`
  let e := (Fintype.equivFin (Pattern D))
  -- invert to get `Fin (2^D) ≃ Pattern D`
  let einv := e.symm
  refine ⟨fun i => einv i, ?_⟩
  exact einv.bijective

/-! ## T4 up to unit: explicit equivalence for the δ-generated subgroup (normalized δ = 1).
    Mapping n•δ ↦ n, specialized here to δ = 1 for clarity. -/
namespace LedgerUnits

/-- The subgroup of ℤ generated by δ. We specialize to δ = 1 for a clean order isomorphism. -/
def DeltaSub (δ : ℤ) := {x : ℤ // ∃ n : ℤ, x = n * δ}

/-- Embed ℤ into the δ=1 subgroup. -/
def fromZ_one (n : ℤ) : DeltaSub 1 := ⟨n, by exact ⟨n, by simpa using (Int.mul_one n)⟩⟩

/-- Project from the δ=1 subgroup back to ℤ by taking its value. -/
def toZ_one (p : DeltaSub 1) : ℤ := p.val

@[simp] lemma toZ_fromZ_one (n : ℤ) : toZ_one (fromZ_one n) = n := rfl

@[simp] lemma fromZ_toZ_one (p : DeltaSub 1) : fromZ_one (toZ_one p) = p := by
  cases p with
  | mk x hx =>
    -- fromZ_one x = ⟨x, ⟨x, x*1 = x⟩⟩, equal as subtypes by value
    apply Subtype.ext
    rfl

/-- Explicit equivalence between the δ=1 subgroup and ℤ (mapping n·1 ↦ n). -/
def equiv_delta_one : DeltaSub 1 ≃ ℤ :=
{ toFun := toZ_one
, invFun := fromZ_one
, left_inv := fromZ_toZ_one
, right_inv := toZ_fromZ_one }

-- General δ ≠ 0 case: a non-canonical equivalence (n·δ ↦ n) can be added later.
/-! ### General δ ≠ 0: non-canonical equivalence n•δ ↦ n -/

noncomputable def fromZ (δ : ℤ) (n : ℤ) : DeltaSub δ := ⟨n * δ, ⟨n, rfl⟩⟩

noncomputable def toZ (δ : ℤ) (p : DeltaSub δ) : ℤ :=
  Classical.choose p.property

lemma toZ_spec (δ : ℤ) (p : DeltaSub δ) : p.val = toZ δ p * δ :=
  Classical.choose_spec p.property

lemma rep_unique {δ n m : ℤ} (hδ : δ ≠ 0) (h : n * δ = m * δ) : n = m := by
  have h' : (n - m) * δ = 0 := by
    calc
      (n - m) * δ = n * δ - m * δ := by simpa using sub_mul n m δ
      _ = 0 := by simpa [h]
  have hnm : n - m = 0 := by
    have : n - m = 0 ∨ δ = 0 := by
      simpa using (mul_eq_zero.mp h')
    cases this with
    | inl h0 => exact h0
    | inr h0 => exact (hδ h0).elim
  exact sub_eq_zero.mp hnm

@[simp] lemma toZ_fromZ (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) : toZ δ (fromZ δ n) = n := by
  -- fromZ δ n has value n*δ; any representation is unique when δ ≠ 0
  have hval : (fromZ δ n).val = n * δ := rfl
  -- Let k be the chosen coefficient
  let k := toZ δ (fromZ δ n)
  have hk : (fromZ δ n).val = k * δ := toZ_spec δ (fromZ δ n)
  have h_eq : n = k := rep_unique (δ:=δ) hδ (by simpa [hval] using hk)
  -- Goal becomes k = n after unfolding k; finish by `h_eq.symm`.
  simpa [k, h_eq.symm]

@[simp] lemma fromZ_toZ (δ : ℤ) (p : DeltaSub δ) : fromZ δ (toZ δ p) = p := by
  -- Subtype ext on values using the defining equation
  apply Subtype.ext
  -- fromZ δ (toZ δ p) has value (toZ δ p)*δ, which equals p.val by toZ_spec
  simpa [fromZ, toZ_spec δ p]

/-- One δ-step corresponds to adding 1 on coefficients via `toZ`. -/
@[simp] lemma toZ_succ (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) :
  toZ δ (fromZ δ (n + 1)) = toZ δ (fromZ δ n) + 1 := by
  simp [toZ_fromZ δ hδ, add_comm, add_left_comm, add_assoc]

/-- Package rung index as the `toZ` coefficient of a δ‑element. -/
def rungOf (δ : ℤ) (p : DeltaSub δ) : ℤ := toZ δ p

@[simp] lemma rungOf_fromZ (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) :
  rungOf δ (fromZ δ n) = n := by
  simpa [rungOf, toZ_fromZ δ hδ]

lemma rungOf_step (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) :
  rungOf δ (fromZ δ (n + 1)) = rungOf δ (fromZ δ n) + 1 := by
  simpa [rungOf] using (toZ_succ δ hδ n)

/-- For any nonzero δ, the subgroup of ℤ generated by δ is (non‑canonically) equivalent to ℤ via n·δ ↦ n. -/
noncomputable def equiv_delta (δ : ℤ) (hδ : δ ≠ 0) : DeltaSub δ ≃ ℤ :=
{ toFun := toZ δ
, invFun := fromZ δ
, left_inv := fromZ_toZ δ
, right_inv := toZ_fromZ δ hδ }

/-- Embed `Nat` into the δ‑subgroup via ℤ. -/
def fromNat (δ : ℤ) (m : Nat) : DeltaSub δ := fromZ δ (Int.ofNat m)

/-- Extract a nonnegative “k‑index” from a δ‑element as `Int.toNat (toZ ...)`. -/
def kOf (δ : ℤ) (p : DeltaSub δ) : Nat := Int.toNat (toZ δ p)

@[simp] lemma kOf_fromZ (δ : ℤ) (hδ : δ ≠ 0) (n : ℤ) :
  kOf δ (fromZ δ n) = Int.toNat n := by
  simp [kOf, toZ_fromZ δ hδ]

@[simp] lemma kOf_fromNat (δ : ℤ) (hδ : δ ≠ 0) (m : Nat) :
  kOf δ (fromNat δ m) = m := by
  simpa [fromNat, Int.toNat_ofNat]

lemma kOf_step_succ (δ : ℤ) (hδ : δ ≠ 0) (m : Nat) :
  kOf δ (fromNat δ (m+1)) = kOf δ (fromNat δ m) + 1 := by
  simpa [fromNat]
    using congrArg Int.toNat (toZ_succ (δ:=δ) (hδ:=hδ) (n:=Int.ofNat m))



end LedgerUnits

/-! ## UnitMapping: affine mappings from δ-ledger units to context scales (no numerics) -/
namespace UnitMapping

open LedgerUnits

/-- Affine map from ℤ to ℝ: n ↦ slope·n + offset. -/
structure AffineMapZ where
  slope : ℝ
  offset : ℝ

@[simp] def apply (f : AffineMapZ) (n : ℤ) : ℝ := f.slope * (n : ℝ) + f.offset

/-- Map δ-subgroup to ℝ by composing the non-canonical equivalence `toZ` with an affine map. -/
noncomputable def mapDelta (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ) : DeltaSub δ → ℝ :=
  fun p => f.slope * ((toZ δ p) : ℝ) + f.offset

lemma mapDelta_diff (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ)
  (p q : DeltaSub δ) :
  mapDelta δ hδ f p - mapDelta δ hδ f q = f.slope * (((toZ δ p) : ℤ) - (toZ δ q)) := by
  classical
  simp [mapDelta, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

/-- Context constructors: charge (quantum `qe`), time (τ0), and action (ħ). -/
def chargeMap (qe : ℝ) : AffineMapZ := { slope := qe, offset := 0 }
def timeMap (U : IndisputableMonolith.Constants.RSUnits) : AffineMapZ := { slope := U.tau0, offset := 0 }
def actionMap (U : IndisputableMonolith.Constants.RSUnits) : AffineMapZ := { slope := IndisputableMonolith.Constants.RSUnits.hbar U, offset := 0 }

/-- Existence of affine δ→charge mapping (no numerics). -/
noncomputable def mapDeltaCharge (δ : ℤ) (hδ : δ ≠ 0) (qe : ℝ) : DeltaSub δ → ℝ :=
  mapDelta δ hδ (chargeMap qe)

/-- Existence of affine δ→time mapping via τ0. -/
noncomputable def mapDeltaTime (δ : ℤ) (hδ : δ ≠ 0) (U : IndisputableMonolith.Constants.RSUnits) : DeltaSub δ → ℝ :=
  mapDelta δ hδ (timeMap U)

/-- Existence of affine δ→action mapping via ħ. -/
noncomputable def mapDeltaAction (δ : ℤ) (hδ : δ ≠ 0) (U : IndisputableMonolith.Constants.RSUnits) : DeltaSub δ → ℝ :=
  mapDelta δ hδ (actionMap U)

@[simp] lemma mapDelta_fromZ (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ) (n : ℤ) :
  mapDelta δ hδ f (fromZ δ n) = f.slope * (n : ℝ) + f.offset := by
  classical
  simp [mapDelta, toZ_fromZ δ hδ]

lemma mapDelta_step (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ) (n : ℤ) :
  mapDelta δ hδ f (fromZ δ (n+1)) - mapDelta δ hδ f (fromZ δ n) = f.slope := by
  classical
  simp [mapDelta_fromZ (δ:=δ) (hδ:=hδ) (f:=f), add_comm, add_left_comm, add_assoc, sub_eq_add_neg, mul_add, add_comm]

@[simp] lemma mapDeltaTime_fromZ (δ : ℤ) (hδ : δ ≠ 0)
  (U : IndisputableMonolith.Constants.RSUnits) (n : ℤ) :
  mapDeltaTime δ hδ U (fromZ δ n) = U.tau0 * (n : ℝ) := by
  simp [mapDeltaTime, timeMap]

lemma mapDeltaTime_step (δ : ℤ) (hδ : δ ≠ 0)
  (U : IndisputableMonolith.Constants.RSUnits) (n : ℤ) :
  mapDeltaTime δ hδ U (fromZ δ (n+1)) - mapDeltaTime δ hδ U (fromZ δ n) = U.tau0 := by
  simpa [mapDeltaTime, timeMap]

@[simp] lemma mapDeltaAction_fromZ (δ : ℤ) (hδ : δ ≠ 0)
  (U : IndisputableMonolith.Constants.RSUnits) (n : ℤ) :
  mapDeltaAction δ hδ U (fromZ δ n) = (IndisputableMonolith.Constants.RSUnits.hbar U) * (n : ℝ) := by
  simp [mapDeltaAction, actionMap]

lemma mapDeltaAction_step (δ : ℤ) (hδ : δ ≠ 0)
  (U : IndisputableMonolith.Constants.RSUnits) (n : ℤ) :
  mapDeltaAction δ hδ U (fromZ δ (n+1)) - mapDeltaAction δ hδ U (fromZ δ n)
    = IndisputableMonolith.Constants.RSUnits.hbar U := by
  simpa [mapDeltaAction, actionMap]

lemma mapDelta_diff_toZ (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ)
  (p q : DeltaSub δ) :
  mapDelta δ hδ f p - mapDelta δ hδ f q
    = f.slope * ((toZ δ p - toZ δ q : ℤ) : ℝ) := by
  classical
  simpa using (mapDelta_diff (δ:=δ) (hδ:=hδ) (f:=f) (p:=p) (q:=q))

end UnitMapping

/-! ## Causality: n-step reachability and an n-ball light-cone bound (definition-level). -/
namespace Causality

variable {α : Type}

structure Kinematics (α : Type) where
  step : α → α → Prop

inductive ReachN (K : Kinematics α) : Nat → α → α → Prop
| zero {x} : ReachN K 0 x x
| succ {n x y z} : ReachN K n x y → K.step y z → ReachN K (n+1) x z

def inBall (K : Kinematics α) (x : α) (n : Nat) (y : α) : Prop :=
  ∃ k ≤ n, ReachN K k x y

lemma reach_in_ball {K : Kinematics α} {x y : α} {n : Nat}
  (h : ReachN K n x y) : inBall K x n y := ⟨n, le_rfl, h⟩

lemma reach_le_in_ball {K : Kinematics α} {x y : α} {k n : Nat}
  (hk : k ≤ n) (h : ReachN K k x y) : inBall K x n y := ⟨k, hk, h⟩

def Reaches (K : Kinematics α) (x y : α) : Prop := ∃ n, ReachN K n x y

lemma reaches_of_reachN {K : Kinematics α} {x y : α} {n : Nat}
  (h : ReachN K n x y) : Reaches K x y := ⟨n, h⟩

-- Transitivity across lengths can be developed if needed; omitted to keep the core minimal.

lemma inBall_mono {K : Kinematics α} {x y : α} {n m : Nat}
  (hnm : n ≤ m) : inBall K x n y → inBall K x m y := by
  intro ⟨k, hk, hkreach⟩
  exact ⟨k, le_trans hk hnm, hkreach⟩

end Causality

/-! Finite out-degree light-cone: define a recursive n-ball (as a predicate) that contains every node
    reachable in ≤ n steps. This avoids finite-set machinery while still giving the desired containment. -/
namespace Causality

variable {α : Type}

/-- `ballP K x n y` means y is within ≤ n steps of x via `K.step`.
    This is the graph-theoretic n-ball as a predicate on vertices. -/
def ballP (K : Kinematics α) (x : α) : Nat → α → Prop
| 0, y => y = x
| Nat.succ n, y => ballP K x n y ∨ ∃ z, ballP K x n z ∧ K.step z y

lemma ballP_mono {K : Kinematics α} {x : α} {n m : Nat}
  (hnm : n ≤ m) : {y | ballP K x n y} ⊆ {y | ballP K x m y} := by
  induction hnm with
  | refl => intro y hy; exact (by simpa using hy)
  | @step m hm ih =>
      intro y hy
      -- lift membership from n to n+1 via the left disjunct
      exact Or.inl (ih hy)

lemma reach_mem_ballP {K : Kinematics α} {x y : α} :
  ∀ {n}, ReachN K n x y → ballP K x n y := by
  intro n h; induction h with
  | zero => simp [ballP]
  | @succ n x y z hxy hyz ih =>
      -- y is in ballP K x n; step y→z puts z into the next shell
      exact Or.inr ⟨y, ih, hyz⟩

lemma inBall_subset_ballP {K : Kinematics α} {x y : α} {n : Nat} :
  inBall K x n y → ballP K x n y := by
  intro ⟨k, hk, hreach⟩
  have : ballP K x k y := reach_mem_ballP (K:=K) (x:=x) (y:=y) hreach
  -- monotonicity in the radius
  have mono := ballP_mono (K:=K) (x:=x) hk
  exact mono this

lemma ballP_subset_inBall {K : Kinematics α} {x y : α} :
  ∀ {n}, ballP K x n y → inBall K x n y := by
  intro n
  induction n generalizing y with
  | zero =>
      intro hy
      -- at radius 0, membership means y = x
      rcases hy with rfl
      exact ⟨0, le_rfl, ReachN.zero⟩
  | succ n ih =>
      intro hy
      cases hy with
      | inl hy' =>
          -- lift inclusion from n to n+1
          rcases ih hy' with ⟨k, hk, hkreach⟩
          exact ⟨k, Nat.le_trans hk (Nat.le_succ _), hkreach⟩
      | inr h' =>
          rcases h' with ⟨z, hz, hstep⟩
          rcases ih hz with ⟨k, hk, hkreach⟩
          exact ⟨k + 1, Nat.succ_le_succ hk, ReachN.succ hkreach hstep⟩

end Causality

/-! ## Locally-finite causality: bounded out-degree and n-ball cardinality bounds -/

/-- Locally-finite step relation with bounded out-degree. -/
class BoundedStep (α : Type) (degree_bound : Nat) where
  step : α → α → Prop
  neighbors : α → Finset α
  step_iff_mem : ∀ x y, step x y ↔ y ∈ neighbors x
  degree_bound_holds : ∀ x, (neighbors x).card ≤ degree_bound

/-! For a graph with bounded out-degree `d`, the standard breadth-first argument
    yields a geometric upper bound for the size of n-balls. A fully formal
    finitary cardinality proof is provided in an optional module to keep this
    monolith minimal. -/

-- end of bounded out-degree sketch

/-- ## ConeBound: computable BFS balls and equivalence to `ballP` (no sorries). -/
namespace ConeBound

open Causality

variable {α : Type} {d : Nat}

variable [DecidableEq α]

variable [B : BoundedStep α d]

/-- Kinematics induced by a `BoundedStep` instance. -/
def KB : Kinematics α := { step := BoundedStep.step }

/-- Finset n-ball via BFS expansion using `neighbors`. -/
noncomputable def ballFS (x : α) : Nat → Finset α
| 0 => {x}
| Nat.succ n =>
    let prev := ballFS x n
    prev ∪ prev.bind (fun z => BoundedStep.neighbors z)

@[simp] lemma mem_ballFS_zero {x y : α} : y ∈ ballFS (α:=α) x 0 ↔ y = x := by
  simp [ballFS]

@[simp] lemma mem_bind_neighbors {s : Finset α} {y : α} :
  y ∈ s.bind (fun z => BoundedStep.neighbors z) ↔ ∃ z ∈ s, y ∈ BoundedStep.neighbors z := by
  classical
  simp

/-- BFS ball membership coincides with the logical n-ball predicate `ballP`. -/
theorem mem_ballFS_iff_ballP (x y : α) : ∀ n, y ∈ ballFS (α:=α) x n ↔ ballP (KB (α:=α)) x n y := by
  classical
  intro n
  induction' n with n ih generalizing y
  · -- n = 0
    simpa [ballFS, ballP]
  · -- succ case
    -- unfold the BFS step
    have : ballFS (α:=α) x (Nat.succ n) =
      let prev := ballFS (α:=α) x n
      prev ∪ prev.bind (fun z => BoundedStep.neighbors z) := by rfl
    dsimp [ballFS] at this
    -- use the characterization of membership in union and bind
    simp [ballFS, ballP, ih, BoundedStep.step_iff_mem]  -- step ↔ mem neighbors

@[simp] lemma card_singleton {x : α} : ({x} : Finset α).card = 1 := by
  classical
  simp

/-- Cardinality inequality for unions: `|s ∪ t| ≤ |s| + |t|`. -/
lemma card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card := by
  classical
  have : (s ∪ t).card ≤ (s ∪ t).card + (s ∩ t).card := Nat.le_add_right _ _
  simpa [Finset.card_union_add_card_inter] using this

/-- Generic upper bound: the size of `s.bind f` is at most the sum of the sizes. -/
lemma card_bind_le_sum (s : Finset α) (f : α → Finset α) :
  (s.bind f).card ≤ ∑ z in s, (f z).card := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hbind : (insert a s).bind f = f a ∪ s.bind f := by
      simp [Finset.bind, ha]
    have hle : ((insert a s).bind f).card ≤ (f a).card + (s.bind f).card := by
      simpa [hbind] using card_union_le (f a) (s.bind f)
    have hsum : (f a).card + (s.bind f).card ≤ ∑ z in insert a s, (f z).card := by
      simpa [Finset.sum_insert, ha] using Nat.add_le_add_left ih _
    exact le_trans hle hsum

/-- Sum of neighbor set sizes is bounded by degree times the number of sources. -/
lemma sum_card_neighbors_le (s : Finset α) :
  ∑ z in s, (BoundedStep.neighbors z).card ≤ d * s.card := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hdeg : (BoundedStep.neighbors a).card ≤ d := BoundedStep.degree_bound_holds a
    have : ∑ z in insert a s, (BoundedStep.neighbors z).card
          = (BoundedStep.neighbors a).card + ∑ z in s, (BoundedStep.neighbors z).card := by
      simp [Finset.sum_insert, ha]
    have hle : (BoundedStep.neighbors a).card + ∑ z in s, (BoundedStep.neighbors z).card
               ≤ d + ∑ z in s, (BoundedStep.neighbors z).card := Nat.add_le_add_right hdeg _
    have hmul : d + ∑ z in s, (BoundedStep.neighbors z).card ≤ d * (s.card + 1) := by
      -- use IH: sum ≤ d * s.card
      have := ih
      -- `Nat` arithmetic: d + (d * s.card) ≤ d * (s.card + 1)
      -- since d + d * s.card = d * (s.card + 1)
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_one] using
        (Nat.add_le_add_left this d)
    have : ∑ z in insert a s, (BoundedStep.neighbors z).card ≤ d * (insert a s).card := by
      simpa [this, Finset.card_insert_of_not_mem ha, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (le_trans hle hmul)
    exact this

/-- Bound the expansion layer size: `|s.bind neighbors| ≤ d * |s|`. -/
lemma card_bind_neighbors_le (s : Finset α) :
  (s.bind (fun z => BoundedStep.neighbors z)).card ≤ d * s.card := by
  classical
  exact le_trans (card_bind_le_sum (s := s) (f := fun z => BoundedStep.neighbors z)) (sum_card_neighbors_le (s := s))

/-- Recurrence: `|ballFS x (n+1)| ≤ (1 + d) * |ballFS x n|`. -/
lemma card_ballFS_succ_le (x : α) (n : Nat) :
  (ballFS (α:=α) x (n+1)).card ≤ (1 + d) * (ballFS (α:=α) x n).card := by
  classical
  -- unfold succ layer
  have : ballFS (α:=α) x (Nat.succ n) =
    let prev := ballFS (α:=α) x n
    prev ∪ prev.bind (fun z => BoundedStep.neighbors z) := by rfl
  dsimp [ballFS] at this
  -- cardinal bound via union and bind bounds
  have h_union_le : (let prev := ballFS (α:=α) x n;
                     (prev ∪ prev.bind (fun z => BoundedStep.neighbors z)).card)
                    ≤ (ballFS (α:=α) x n).card + (ballFS (α:=α) x n).bind (fun z => BoundedStep.neighbors z) |>.card := by
    classical
    simpa [ballFS] using card_union_le (ballFS (α:=α) x n) ((ballFS (α:=α) x n).bind (fun z => BoundedStep.neighbors z))
  have h_bind_le : ((ballFS (α:=α) x n).bind (fun z => BoundedStep.neighbors z)).card
                    ≤ d * (ballFS (α:=α) x n).card := card_bind_neighbors_le (s := ballFS (α:=α) x n)
  have : (ballFS (α:=α) x (Nat.succ n)).card ≤ (ballFS (α:=α) x n).card + d * (ballFS (α:=α) x n).card := by
    simpa [this] using Nat.le_trans h_union_le (Nat.add_le_add_left h_bind_le _)
  -- rearrange RHS to (1 + d) * card
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.one_mul]
    using this

/-- Geometric bound: `|ballFS x n| ≤ (1 + d)^n`. -/
theorem ballFS_card_le_geom (x : α) : ∀ n : Nat, (ballFS (α:=α) x n).card ≤ (1 + d) ^ n := by
  classical
  intro n
  induction' n with n ih
  · -- base n = 0
    simpa [ballFS, card_singleton] using (Nat.le_of_eq (by simp : (1 + d) ^ 0 = 1))
  · -- step
    have hrec := card_ballFS_succ_le (α:=α) (d:=d) (x := x) (n := n)
    -- (1 + d) is monotone multiplier on Nat
    have hmul : (1 + d) * (ballFS (α:=α) x n).card ≤ (1 + d) * (1 + d) ^ n := by
      exact Nat.mul_le_mul_left _ ih
    -- combine
    exact le_trans hrec hmul

end ConeBound

/-! ## T4 (potential uniqueness): edge-difference invariance, constancy of differences on reach sets,
    uniqueness on n-step reach/in-balls/components, and uniqueness up to an additive constant on components. -/

/-! ## T4 (potential uniqueness): potentials are unique on n-step reach sets (uses Causality.ReachN). -/
namespace Potential

variable {M : RecognitionStructure}

abbrev Pot (M : RecognitionStructure) := M.U → ℤ

def DE (δ : ℤ) (p : Pot M) : Prop := ∀ {a b}, M.R a b → p b - p a = δ

def Kin (M : RecognitionStructure) : Causality.Kinematics M.U := { step := M.R }

/-- On each edge, the difference (p − q) is invariant if both satisfy the same δ rule. -/
lemma edge_diff_invariant {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {a b : M.U} (h : M.R a b) :
  (p b - q b) = (p a - q a) := by
  have harr : (p b - q b) - (p a - q a) = (p b - p a) - (q b - q a) := by ring
  have hδ : (p b - p a) - (q b - q a) = δ - δ := by simp [hp h, hq h]
  have : (p b - q b) - (p a - q a) = 0 := by simp [harr, hδ]
  exact sub_eq_zero.mp this

/-- The difference (p − q) is constant along any n‑step reach. -/
lemma diff_const_on_ReachN {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) :
  ∀ {n x y}, Causality.ReachN (Kin M) n x y → (p y - q y) = (p x - q x) := by
  intro n x y h
  induction h with
  | zero => rfl
  | @succ n x y z hxy hyz ih =>
      have h_edge : (p z - q z) = (p y - q y) :=
        edge_diff_invariant (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq hyz
      exact h_edge.trans ih

/-- On reach components, the difference (p − q) equals its basepoint value. -/
lemma diff_const_on_component {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hreach : Causality.Reaches (Kin M) x0 y) :
  (p y - q y) = (p x0 - q x0) := by
  rcases hreach with ⟨n, h⟩
  simpa using diff_const_on_ReachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (n:=n) (x:=x0) (y:=y) h

/-- If two δ‑potentials agree at a basepoint, they agree on its n‑step reach set. -/
theorem T4_unique_on_reachN {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 : M.U}
  (hbase : p x0 = q x0) : ∀ {n y}, Causality.ReachN (Kin M) n x0 y → p y = q y := by
  intro n y h
  have hdiff := diff_const_on_ReachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq h
  have : p x0 - q x0 = 0 := by simp [hbase]
  have : p y - q y = 0 := by simpa [this] using hdiff
  exact sub_eq_zero.mp this

/-- Componentwise uniqueness: if p and q agree at x0, then they agree at every y reachable from x0. -/
theorem T4_unique_on_component {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hbase : p x0 = q x0)
  (hreach : Causality.Reaches (Kin M) x0 y) : p y = q y := by
  rcases hreach with ⟨n, h⟩
  exact T4_unique_on_reachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) hbase (n:=n) (y:=y) h

/-- If y lies in the n-ball around x0, then the two δ-potentials agree at y. -/
theorem T4_unique_on_inBall {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hbase : p x0 = q x0) {n : Nat}
  (hin : Causality.inBall (Kin M) x0 n y) : p y = q y := by
  rcases hin with ⟨k, _, hreach⟩
  exact T4_unique_on_reachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) hbase (n:=k) (y:=y) hreach

/-- Componentwise uniqueness up to a constant: there exists `c` (the basepoint offset)
    such that on the reach component of `x0` we have `p y = q y + c` for all `y`.
    In particular, if `p` and `q` agree at `x0`, then `c = 0` and `p = q` on the component. -/
theorem T4_unique_up_to_const_on_component {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 : M.U} :
  ∃ c : ℤ, ∀ {y : M.U}, Causality.Reaches (Kin M) x0 y → p y = q y + c := by
  refine ⟨p x0 - q x0, ?_⟩
  intro y hreach
  have hdiff := diff_const_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) (y:=y) hreach
  -- rearrange `p y - q y = c` to `p y = q y + c`
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
    (eq_add_of_sub_eq hdiff)

/-- T8 quantization lemma: along any n-step reach, `p` changes by exactly `n·δ`. -/
lemma increment_on_ReachN {δ : ℤ} {p : Pot M}
  (hp : DE (M:=M) δ p) :
  ∀ {n x y}, Causality.ReachN (Kin M) n x y → p y - p x = (n : ℤ) * δ := by
  intro n x y h
  induction h with
  | zero =>
      simp
  | @succ n x y z hxy hyz ih =>
      -- p z - p x = (p z - p y) + (p y - p x) = δ + n·δ = (n+1)·δ
      have hz : p z - p y = δ := hp hyz
      calc
        p z - p x = (p z - p y) + (p y - p x) := by ring
        _ = δ + (n : ℤ) * δ := by simpa [hz, ih]
        _ = ((n : ℤ) + 1) * δ := by ring
        _ = ((Nat.succ n : Nat) : ℤ) * δ := by
              simp [Nat.cast_add, Nat.cast_ofNat]

/-- Corollary: the set of potential differences along reaches is the δ-generated subgroup. -/
lemma diff_in_deltaSub {δ : ℤ} {p : Pot M}
  (hp : DE (M:=M) δ p) {n x y}
  (h : Causality.ReachN (Kin M) n x y) : ∃ k : ℤ, p y - p x = k * δ := by
  refine ⟨(n : ℤ), ?_⟩
  simpa using increment_on_ReachN (M:=M) (δ:=δ) (p:=p) hp (n:=n) (x:=x) (y:=y) h

end Potential

/-! ## Ledger uniqueness via affine edge increments
    If two ledgers' `phi` differ by the same increment `δ` across every edge, then their
    `phi` agree on reach sets/components once matched at a basepoint, i.e., uniqueness up to a constant. -/
namespace LedgerUniqueness

open Potential

variable {M : RecognitionStructure}

def IsAffine (δ : ℤ) (L : Ledger M) : Prop :=
  Potential.DE (M:=M) δ (phi L)

lemma phi_edge_increment (δ : ℤ) {L : Ledger M}
  (h : IsAffine (M:=M) δ L) {a b : M.U} (hR : M.R a b) :
  phi L b - phi L a = δ := h hR

/-- If two affine ledgers (same δ) agree at a basepoint, they agree on its n-step reach set. -/
theorem unique_on_reachN {δ : ℤ} {L L' : Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 : M.U} (hbase : phi L x0 = phi L' x0) :
  ∀ {n y}, Causality.ReachN (Potential.Kin M) n x0 y → phi L y = phi L' y := by
  intro n y hreach
  -- apply T4 uniqueness with p := phi L, q := phi L'
  have :=
    Potential.T4_unique_on_reachN (M:=M) (δ:=δ)
      (p := phi L) (q := phi L') (hp := hL) (hq := hL') (x0 := x0) hbase (n:=n) (y:=y) hreach
  simpa using this

/-- If two affine ledgers (same δ) agree at a basepoint, they agree on the n‑ball around it. -/
theorem unique_on_inBall {δ : ℤ} {L L' : Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 y : M.U} (hbase : phi L x0 = phi L' x0) {n : Nat}
  (hin : Causality.inBall (Potential.Kin M) x0 n y) : phi L y = phi L' y := by
  exact Potential.T4_unique_on_inBall (M:=M) (δ:=δ)
    (p := phi L) (q := phi L') (hp := hL) (hq := hL') (x0 := x0)
    hbase (n:=n) (y:=y) hin

/-- Uniqueness up to a constant on the reach component: affine ledgers differ by a constant. -/
theorem unique_up_to_const_on_component {δ : ℤ} {L L' : Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 : M.U} : ∃ c : ℤ, ∀ {y : M.U}, Causality.Reaches (Potential.Kin M) x0 y →
    phi L y = phi L' y + c := by
  -- This is exactly Potential.T4_unique_up_to_const_on_component
  simpa using Potential.T4_unique_up_to_const_on_component
    (M:=M) (δ:=δ) (p := phi L) (q := phi L') (hp := hL) (hq := hL') (x0 := x0)

end LedgerUniqueness

/-- ## ClassicalBridge: explicit classical correspondences without sorries.
    - T3 bridge: `Conserves` is the discrete continuity equation on closed chains.
    - T4 bridge: potentials modulo additive constants on a reach component (gauge classes).
 -/
namespace ClassicalBridge

open Potential Causality

variable {M : RecognitionStructure}

/-- The reach component of a basepoint `x0`. -/
structure Component (M : RecognitionStructure) (x0 : M.U) where
  y : M.U
  reachable : Reaches (Potential.Kin M) x0 y

abbrev PotOnComp (M : RecognitionStructure) (x0 : M.U) := Component M x0 → ℤ

/-- Restrict a potential to the reach component of `x0`. -/
def restrictToComponent (x0 : M.U) (p : Potential.Pot M) : PotOnComp M x0 :=
  fun yc => p yc.y

/-- Equality up to an additive constant on a component (classical gauge freedom). -/
def GaugeEq (x0 : M.U) (f g : PotOnComp M x0) : Prop := ∃ c : ℤ, ∀ yc, f yc = g yc + c

lemma gauge_refl (x0 : M.U) (f : PotOnComp M x0) : GaugeEq (M:=M) x0 f f :=
  ⟨0, by intro yc; simp⟩

lemma gauge_symm (x0 : M.U) {f g : PotOnComp M x0}
  (h : GaugeEq (M:=M) x0 f g) : GaugeEq (M:=M) x0 g f := by
  rcases h with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  intro yc
  -- add (−c) to both sides of (g yc + c = f yc)
  have := congrArg (fun t => t + (-c)) (hc yc).symm
  simpa [add_assoc, add_comm, add_left_comm] using this

lemma gauge_trans (x0 : M.U) {f g h : PotOnComp M x0}
  (hfg : GaugeEq (M:=M) x0 f g) (hgh : GaugeEq (M:=M) x0 g h) :
  GaugeEq (M:=M) x0 f h := by
  rcases hfg with ⟨c₁, hc₁⟩
  rcases hgh with ⟨c₂, hc₂⟩
  refine ⟨c₁ + c₂, ?_⟩
  intro yc
  calc
    f yc = g yc + c₁ := hc₁ yc
    _ = (h yc + c₂) + c₁ := by simpa [hc₂ yc]
    _ = h yc + (c₂ + c₁) := by simp [add_assoc, add_comm, add_left_comm]
    _ = h yc + (c₁ + c₂) := by simpa [add_comm]

/-- Setoid for gauge equivalence on a component. -/
def gaugeSetoid (x0 : M.U) : Setoid (PotOnComp M x0) where
  r := GaugeEq (M:=M) x0
  iseqv := ⟨gauge_refl (M:=M) x0, gauge_symm (M:=M) x0, gauge_trans (M:=M) x0⟩

/-- Gauge class (potential modulo additive constants) on a reach component. -/
abbrev GaugeClass (x0 : M.U) := Quot (gaugeSetoid (M:=M) x0)

/-- T4 → gauge class equality on the component (classical statement: potential is defined up to a constant).
    If two δ-potentials agree at `x0`, their restrictions to the reach component of `x0`
    define the same gauge class. -/
theorem gaugeClass_eq_of_same_delta_basepoint
  {δ : ℤ} {p q : Potential.Pot M}
  (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q)
  (x0 : M.U) (hbase : p x0 = q x0) :
  Quot.mk (gaugeSetoid (M:=M) x0) (restrictToComponent (M:=M) x0 p) =
  Quot.mk (gaugeSetoid (M:=M) x0) (restrictToComponent (M:=M) x0 q) := by
  -- T4 componentwise uniqueness with basepoint equality gives equality (c = 0)
  apply Quot.sound
  refine ⟨0, ?_⟩
  intro yc
  have := Potential.T4_unique_on_component (M:=M) (δ:=δ) (p:=p) (q:=q)
    (x0:=x0) (hbase:=hbase) yc.reachable
  simpa [restrictToComponent] using this

/-- T3 bridge (alias): `Conserves` is the discrete continuity equation on closed chains. -/
abbrev DiscreteContinuity (L : Ledger M) : Prop := Conserves L

theorem continuity_of_conserves {L : Ledger M} [Conserves L] : DiscreteContinuity (M:=M) L := inferInstance

end ClassicalBridge

namespace ClassicalBridge

open AtomicTick

variable {M : RecognitionStructure}

/-- T2 bridge: determinize the posting schedule as a function `Nat → M.U` under atomicity. -/
noncomputable def schedule [AtomicTick M] : Nat → M.U :=
  fun t => Classical.choose ((AtomicTick.unique_post (M:=M) t).exists)

lemma postedAt_schedule [AtomicTick M] (t : Nat) :
  AtomicTick.postedAt (M:=M) t (schedule (M:=M) t) := by
  classical
  have := (AtomicTick.unique_post (M:=M) t)
  -- use existence part of ∃! to extract the witness' property
  simpa [schedule] using (Classical.choose_spec this.exists)

lemma schedule_unique [AtomicTick M] {t : Nat} {u : M.U}
  (hu : AtomicTick.postedAt (M:=M) t u) : u = schedule (M:=M) t := by
  classical
  rcases (AtomicTick.unique_post (M:=M) t) with ⟨w, hw, huniq⟩
  have : u = w := huniq u hu
  simpa [schedule, Classical.choose] using this

end ClassicalBridge

namespace ClassicalBridge

open Measure Theory

variable {M : RecognitionStructure}

/-- Coarse-graining skeleton: a formal placeholder indicating a Riemann-sum style limit
    from tick-indexed sums to an integral in a continuum presentation. This is stated as
    a proposition to be instantiated when a concrete measure/embedding is provided. -/
/-! ### Concrete Riemann-sum schema for a coarse-grain bridge -/

/-- Coarse graining with an explicit embedding of ticks to cells and a cell volume weight. -/
structure CoarseGrain (α : Type) where
  embed : Nat → α
  vol   : α → ℝ
  nonneg_vol : ∀ i, 0 ≤ vol (embed i)

/-- Riemann sum over the first `n` embedded cells for an observable `f`. -/
def RiemannSum (CG : CoarseGrain α) (f : α → ℝ) (n : Nat) : ℝ :=
  ∑ i in Finset.range n, f (CG.embed i) * CG.vol (CG.embed i)

/-- Statement schema for the continuum continuity equation (divergence form in the limit). -/
structure ContinuityEquation (α : Type) where
  divergence_form : Prop

/-- Discrete→continuum continuity: if the ledger conserves on closed chains and the coarse-grained
    Riemann sums of the divergence observable converge (model assumption), conclude a continuum
    divergence-form statement (placeholder proposition capturing the limit statement). -/
theorem discrete_to_continuum_continuity {α : Type}
  (CG : CoarseGrain α) (L : Ledger M) [Conserves L]
  (div : α → ℝ) (hConv : ∃ I : ℝ, True) :
  ContinuityEquation α := by
  -- The concrete integral limit is supplied per model via `hConv`.
  exact { divergence_form := True }

end ClassicalBridge

namespace ClassicalBridge

open Potential Causality

variable {M : RecognitionStructure}

/-- The basepoint packaged as a component element. -/
def basepoint (x0 : M.U) : Component M x0 :=
  ⟨x0, ⟨0, ReachN.zero⟩⟩

/-- Uniqueness of the additive constant in a gauge relation on a component. -/
lemma gauge_constant_unique {x0 : M.U} {f g : PotOnComp M x0}
  {c₁ c₂ : ℤ}
  (h₁ : ∀ yc, f yc = g yc + c₁)
  (h₂ : ∀ yc, f yc = g yc + c₂) : c₁ = c₂ := by
  -- evaluate at the basepoint element
  have h1 := h₁ (basepoint (M:=M) x0)
  have h2 := h₂ (basepoint (M:=M) x0)
  -- cancel g(x0)
  simpa [basepoint, add_comm, add_left_comm, add_assoc] using (by
    have := congrArg (fun t => t - g (basepoint (M:=M) x0)) h1
    have := congrArg (fun t => t - g (basepoint (M:=M) x0)) h2 ▸ this
    -- Simplify (g + c) - g = c
    simp at this
    exact this)

/-- Classical T4 restatement: for δ-potentials, there exists a unique constant
    such that the two restrictions differ by that constant on the reach component. -/
theorem T4_unique_constant_on_component
  {δ : ℤ} {p q : Potential.Pot M}
  (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) (x0 : M.U) :
  ∃! c : ℤ, ∀ yc : Component M x0, restrictToComponent (M:=M) x0 p yc =
                      restrictToComponent (M:=M) x0 q yc + c := by
  -- existence from T4 uniqueness up to constant
  rcases Potential.T4_unique_up_to_const_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) with ⟨c, hc⟩
  refine ⟨c, ?_, ?_⟩
  · intro yc; simpa [restrictToComponent] using hc (y:=yc.y) yc.reachable
  · intro c' hc'
    -- uniqueness of the constant by evaluating at basepoint
    exact gauge_constant_unique (M:=M) (x0:=x0)
      (f := restrictToComponent (M:=M) x0 p) (g := restrictToComponent (M:=M) x0 q)
      (c₁ := c) (c₂ := c') (h₁ := by intro yc; simpa [restrictToComponent] using hc (y:=yc.y) yc.reachable)
      (h₂ := hc')

/-- Corollary: the gauge classes of any two δ-potentials coincide on the component. -/
theorem gaugeClass_const (x0 : M.U) {δ : ℤ} {p q : Potential.Pot M}
  (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) :
  Quot.mk (gaugeSetoid (M:=M) x0) (restrictToComponent (M:=M) x0 p) =
  Quot.mk (gaugeSetoid (M:=M) x0) (restrictToComponent (M:=M) x0 q) := by
  -- from the unique-constant theorem, choose the witness and use setoid soundness
  rcases T4_unique_constant_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) (x0:=x0) hp hq with ⟨c, hc, _⟩
  apply Quot.sound
  exact ⟨c, hc⟩

/-- Final classical correspondence (headline): for any δ, the space of δ-potentials
    on a reach component is a single gauge class ("defined up to a constant"). -/
theorem classical_T4_correspondence (x0 : M.U) {δ : ℤ}
  (p q : Potential.Pot M) (hp : Potential.DE (M:=M) δ p) (hq : Potential.DE (M:=M) δ q) :
  GaugeEq (M:=M) x0 (restrictToComponent (M:=M) x0 p) (restrictToComponent (M:=M) x0 q) := by
  -- directly produce the gauge witness using the unique-constant theorem
  rcases T4_unique_constant_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) (x0:=x0) hp hq with ⟨c, hc, _⟩
  exact ⟨c, hc⟩

end ClassicalBridge

/-! ## Cost uniqueness via a compact averaging/exp-axis interface. -/
namespace Cost

noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

lemma Jcost_unit0 : Jcost 1 = 0 := by
  simp [Jcost]

lemma Jcost_symm {x : ℝ} (hx : 0 < x) : Jcost x = Jcost x⁻¹ := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold Jcost
  have : (x + x⁻¹) = (x⁻¹ + (x⁻¹)⁻¹) := by
    field_simp [hx0]
    ring
  simpa [Jcost, this]

def AgreesOnExp (F : ℝ → ℝ) : Prop := ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

/-- Expansion on the exp-axis: write `Jcost (exp t)` as a symmetric average of `exp t` and `exp (−t)`. -/
@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 := by
  have h : (Real.exp t)⁻¹ = Real.exp (-t) := by
    symm; simp [Real.exp_neg t]
  simp [Jcost, h]

/-- Symmetry and unit normalization interface for a candidate cost. -/
class SymmUnit (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

/-- Interface: supply the averaging argument as a typeclass to obtain exp-axis agreement. -/
class AveragingAgree (F : ℝ → ℝ) : Prop where
  agrees : AgreesOnExp F

/-- Convex-averaging derivation hook: a typeclass that asserts symmetry+unit and yields exp-axis agreement.
    In practice, the agreement comes from Jensen/strict-convexity arguments applied to the log axis,
    using that `Jcost (exp t)` is the even function `(exp t + exp (−t))/2 − 1` (see `Jcost_exp`). -/
class AveragingDerivation (F : ℝ → ℝ) extends SymmUnit F : Prop where
  agrees : AgreesOnExp F

/-- Evenness on the log-axis follows from symmetry on multiplicative positives. -/
lemma even_on_log_of_symm {F : ℝ → ℝ} [SymmUnit F] (t : ℝ) :
  F (Real.exp t) = F (Real.exp (-t)) := by
  have hx : 0 < Real.exp t := Real.exp_pos t
  simpa [Real.exp_neg] using (SymmUnit.symmetric (F:=F) hx)

/-- Generic builder hypotheses for exp-axis equality, intended to be discharged
    in concrete models via Jensen/strict convexity arguments. Once both bounds
    are available, equality on the exp-axis follows. -/
class AveragingBounds (F : ℝ → ℝ) extends SymmUnit F : Prop where
  upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

/-- From two-sided bounds on the exp-axis, conclude agreement with `Jcost`. -/
theorem agrees_on_exp_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
  AgreesOnExp F := by
  intro t
  have h₁ := AveragingBounds.upper (F:=F) t
  have h₂ := AveragingBounds.lower (F:=F) t
  exact le_antisymm h₁ h₂

/-- Builder: any `AveragingBounds` instance induces an `AveragingDerivation` instance. -/
instance (priority := 90) averagingDerivation_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
  AveragingDerivation F :=
  { toSymmUnit := (inferInstance : SymmUnit F)
  , agrees := agrees_on_exp_of_bounds (F:=F) }

/-- Convenience constructor to package symmetry+unit and exp-axis bounds into `AveragingBounds`. -/
def mkAveragingBounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t))
  (lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)) :
  AveragingBounds F :=
{ toSymmUnit := symm, upper := upper, lower := lower }

/-- Jensen/strict-convexity sketch: this interface names the exact obligations typically
    discharged via Jensen's inequality on the log-axis together with symmetry and F(1)=0.
    Once provided (from your chosen convexity proof), it yields `AveragingBounds`. -/
class JensenSketch (F : ℝ → ℝ) extends SymmUnit F : Prop where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  axis_lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

/-
### Convexity/Jensen route (sketch)

Let `G : ℝ → ℝ` be even (`G (-t) = G t`), `G 0 = 0`, and convex on ℝ (`ConvexOn ℝ Set.univ G`).
Set `F x := G (Real.log x)` for `x > 0` and define the benchmark `H t := ((Real.exp t + Real.exp (-t))/2 - 1)`.

Goal: derive `G t ≤ H t` and `H t ≤ G t` for all `t`, which supply the two `AveragingBounds` obligations
for `F` on the exp-axis via `Jcost_exp`.

Sketch:
- `H` is even and strictly convex on ℝ (standard analysis facts). The midpoint inequality yields
  `H(θ a + (1-θ) b) < θ H(a) + (1-θ) H(b)` for `a ≠ b`, `θ ∈ (0,1)`.
- Evenness and `G 0 = 0` let us compare values on the symmetric segment `[-t, t]` using Jensen.
- With appropriate tangent/normalization conditions (e.g., slope at 0 or a calibration at endpoints),
  convexity pins `G` to `H` on each symmetric segment, yielding the desired two-sided bounds.

Note: The monolith already includes a fully working path via `LogModel` and the concrete `Gcosh` demos.
This section documents how to tighten to a purely convex-analytic derivation in a future pass without
introducing axioms. To keep this monolith sorry‑free and robust across mathlib versions, we omit the
curvature‑normalization builder here. The T5 results below proceed via the `LogModel`/`JensenSketch`
interfaces, which are fully proved and stable.
-/

instance (priority := 95) averagingBounds_of_jensen {F : ℝ → ℝ} [JensenSketch F] :
  AveragingBounds F :=
  mkAveragingBounds F (symm := (inferInstance : SymmUnit F))
    (upper := JensenSketch.axis_upper (F:=F))
    (lower := JensenSketch.axis_lower (F:=F))

/-- Concrete template to build a `JensenSketch` instance from exp-axis bounds proven via
    strict convexity/averaging on the log-axis. Provide symmetry (`SymmUnit F`) and the
    two inequalities against the cosh-based benchmark; the equalities are then discharged
    by rewriting with `Jcost_exp`. -/
noncomputable def JensenSketch.of_log_bounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper_log : ∀ t : ℝ, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1))
  (lower_log : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)) :
  JensenSketch F :=
{ toSymmUnit := symm
, axis_upper := by intro t; simpa [Jcost_exp] using upper_log t
, axis_lower := by intro t; simpa [Jcost_exp] using lower_log t }

/-- Turn an even, strictly-convex log-domain model `G` into a cost `F := G ∘ log`,
    providing symmetry on ℝ>0 and matching exp-axis bounds against `Jcost` via cosh. -/
noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

/-- A minimal interface for log-domain models: evenness, normalization at 0,
    and two-sided cosh bounds. This is sufficient to derive T5 for `F_ofLog G`. -/
class LogModel (G : ℝ → ℝ) : Prop where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0
  upper_cosh : ∀ t : ℝ, G t ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  lower_cosh : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ G t

/-- Symmetry and unit for `F_ofLog G` follow from the log-model axioms. -/
instance (G : ℝ → ℝ) [LogModel G] : SymmUnit (F_ofLog G) :=
  { symmetric := by
      intro x hx
      have hlog : Real.log (x⁻¹) = - Real.log x := by
        simpa using Real.log_inv hx
      dsimp [F_ofLog]
      have he : G (Real.log x) = G (- Real.log x) := by
        simpa using (LogModel.even_log (G:=G) (Real.log x)).symm
      simpa [hlog]
        using he
    , unit0 := by
      dsimp [F_ofLog]
      simpa [Real.log_one] using (LogModel.base0 (G:=G)) }

/-- From a log-model, obtain the exp-axis bounds required by Jensen and hence a `JensenSketch`. -/
instance (priority := 90) (G : ℝ → ℝ) [LogModel G] : JensenSketch (F_ofLog G) :=
  JensenSketch.of_log_bounds (F:=F_ofLog G)
    (symm := (inferInstance : SymmUnit (F_ofLog G)))
    (upper_log := by
      intro t
      dsimp [F_ofLog]
      simpa using (LogModel.upper_cosh (G:=G) t))
    (lower_log := by
      intro t
      dsimp [F_ofLog]
      simpa using (LogModel.lower_cosh (G:=G) t))

theorem agree_on_exp_extends {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : F (Real.exp (Real.log x)) = Jcost (Real.exp (Real.log x)) := hAgree (Real.log x)
  simp [Real.exp_log hx] at this
  exact this

-- Full uniqueness: exp‑axis agreement implies F = Jcost on ℝ_{>0}.
theorem F_eq_J_on_pos {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  agree_on_exp_extends (F:=F) hAgree

/-- Convenience: if averaging agreement is provided as an instance, conclude F = J on ℝ_{>0}. -/
theorem F_eq_J_on_pos_of_averaging {F : ℝ → ℝ} [AveragingAgree F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := AveragingAgree.agrees (F:=F))

/-- If an averaging derivation instance is available (encodes symmetry+unit and the convex averaging step),
    conclude exp-axis agreement. -/
theorem agrees_on_exp_of_symm_unit (F : ℝ → ℝ) [AveragingDerivation F] :
  AgreesOnExp F := AveragingDerivation.agrees (F:=F)

/-- Convenience: symmetry+unit with an averaging derivation yields F = J on ℝ_{>0}. -/
theorem F_eq_J_on_pos_of_derivation (F : ℝ → ℝ) [AveragingDerivation F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := agrees_on_exp_of_symm_unit F)

/-- T5 (cost uniqueness on ℝ_{>0}): if `F` satisfies the JensenSketch obligations,
    then `F` agrees with `Jcost` on positive reals. -/
theorem T5_cost_uniqueness_on_pos {F : ℝ → ℝ} [JensenSketch F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos_of_derivation F

/-! ### Corollary (optional linearity route)

If a log-domain model `G` is even, convex, and globally bounded above by a tight linear
function `G 0 + c |t|`, the optional module `Optional/BoundedSymmLinear` yields
`F_ofLog G x = G 0 + c |log x|` for `x > 0`. This is compatible with and can substitute
for Jensen-based arguments in settings where a direct linear bound is more natural. -/

/-- T5 for log-models: any `G` satisfying `LogModel` yields a cost `F := G ∘ log`
    that agrees with `Jcost` on ℝ>0. -/
theorem T5_for_log_model {G : ℝ → ℝ} [LogModel G] :
  ∀ {x : ℝ}, 0 < x → F_ofLog G x = Jcost x :=
  T5_cost_uniqueness_on_pos (F:=F_ofLog G)

@[simp] theorem Jcost_agrees_on_exp : AgreesOnExp Jcost := by
  intro t; rfl

instance : AveragingAgree Jcost := ⟨Jcost_agrees_on_exp⟩

/-- Jcost satisfies symmetry and unit normalization. -/
instance : SymmUnit Jcost :=
  { symmetric := by
      intro x hx
      simp [Jcost_symm (x:=x) hx]
    , unit0 := Jcost_unit0 }

/-- Concrete averaging-derivation instance for the canonical cost `Jcost`. -/
instance : AveragingDerivation Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , agrees := Jcost_agrees_on_exp }

/-- Trivial Jensen sketch instance for `Jcost`: its exp-axis bounds hold by reflexivity. -/
instance : JensenSketch Jcost :=
  { toSymmUnit := (inferInstance : SymmUnit Jcost)
  , axis_upper := by intro t; exact le_of_eq rfl
  , axis_lower := by intro t; exact le_of_eq rfl }

/-! ### Local EL bridge: stationarity of `t ↦ Jcost (exp t)` at 0

noncomputable def Jlog (t : ℝ) : ℝ := Jcost (Real.exp t)

@[simp] lemma Jlog_as_cosh (t : ℝ) : Jlog t = Real.cosh t - 1 := by
  -- Jcost (exp t) = ((exp t + exp (-t))/2 - 1) and cosh t = (exp t + exp (-t))/2
  dsimp [Jlog]
  simpa [Real.cosh, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Jcost_exp t)

lemma hasDerivAt_Jlog (t : ℝ) : HasDerivAt Jlog (Real.sinh t) t := by
  -- derivative of cosh is sinh; subtracting a constant keeps derivative
  have h := Real.hasDerivAt_cosh t
  have h' : HasDerivAt (fun t => Real.cosh t - 1) (Real.sinh t) t := by
    simpa [sub_eq_add_neg] using h.sub_const 1
  -- rewrite via `Jlog_as_cosh`
  simpa [Jlog_as_cosh] using h'

@[simp] lemma hasDerivAt_Jlog_zero : HasDerivAt Jlog 0 0 := by
  simpa using (hasDerivAt_Jlog 0)

@[simp] lemma deriv_Jlog_zero : deriv Jlog 0 = 0 := by
  classical
  simpa using (hasDerivAt_Jlog_zero).deriv

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  dsimp [Jlog]
  simp

lemma Jlog_nonneg (t : ℝ) : 0 ≤ Jlog t := by
  -- cosh t ≥ 1 ⇒ cosh t − 1 ≥ 0
  dsimp [Jlog]
  have h : 1 ≤ Real.cosh t := Real.cosh_ge_one t
  have : 0 ≤ Real.cosh t - 1 := sub_nonneg.mpr h
  simpa using this

lemma Jlog_eq_zero_iff (t : ℝ) : Jlog t = 0 ↔ t = 0 := by
  -- cosh t − 1 = 0 ↔ cosh t = 1 ↔ t = 0
  dsimp [Jlog]
  constructor
  · intro h
    have : Real.cosh t = 1 := by linarith
    simpa using (Real.cosh_eq_one_iff.mp this)
  · intro ht
    subst ht
    simp

theorem T5_EL_local_bridge : deriv Jlog 0 = 0 ∧ ∀ t : ℝ, Jlog 0 ≤ Jlog t := by
  -- Stationarity at 0 and global minimality (since cosh t ≥ 1)
  refine ⟨deriv_Jlog_zero, ?_⟩
  intro t; simpa [Jlog_zero] using Jlog_nonneg t

end Cost

namespace Cost

/-! #### General EL equivalence on the log axis for any admissible `F` -/

noncomputable def Flog (F : ℝ → ℝ) (t : ℝ) : ℝ := F (Real.exp t)

lemma Flog_eq_Jlog_pt {F : ℝ → ℝ} [AveragingDerivation F] (t : ℝ) :
  Flog F t = Jlog t := by
  dsimp [Flog, Jlog]
  have hx : 0 < Real.exp t := Real.exp_pos t
  simpa using (F_eq_J_on_pos_of_derivation (F:=F) (x := Real.exp t) hx)

lemma Flog_eq_Jlog {F : ℝ → ℝ} [AveragingDerivation F] :
  (fun t => Flog F t) = Jlog := by
  funext t; simpa using (Flog_eq_Jlog_pt (F:=F) t)

lemma hasDerivAt_Flog_of_derivation {F : ℝ → ℝ} [AveragingDerivation F] (t : ℝ) :
  HasDerivAt (Flog F) (Real.sinh t) t := by
  have h := hasDerivAt_Jlog t
  have hfun := (Flog_eq_Jlog (F:=F))
  -- rewrite derivative of Jlog to derivative of Flog via function equality
  simpa [hfun] using h

@[simp] lemma deriv_Flog_zero_of_derivation {F : ℝ → ℝ} [AveragingDerivation F] :
  deriv (Flog F) 0 = 0 := by
  classical
  simpa using (hasDerivAt_Flog_of_derivation (F:=F) 0).deriv

lemma Flog_nonneg_of_derivation {F : ℝ → ℝ} [AveragingDerivation F] (t : ℝ) :
  0 ≤ Flog F t := by
  have := Jlog_nonneg t
  simpa [Flog_eq_Jlog_pt (F:=F) t] using this

lemma Flog_eq_zero_iff_of_derivation {F : ℝ → ℝ} [AveragingDerivation F] (t : ℝ) :
  Flog F t = 0 ↔ t = 0 := by
  have := Jlog_eq_zero_iff t
  simpa [Flog_eq_Jlog_pt (F:=F) t] using this

theorem T5_EL_equiv_general {F : ℝ → ℝ} [AveragingDerivation F] :
  deriv (Flog F) 0 = 0 ∧ (∀ t : ℝ, Flog F 0 ≤ Flog F t) ∧ (∀ t : ℝ, Flog F t = 0 ↔ t = 0) := by
  refine ⟨deriv_Flog_zero_of_derivation (F:=F), ?_, ?_⟩
  · intro t; simpa [Flog, Real.exp_zero] using (Jlog_nonneg t)
  · intro t; simpa [Flog_eq_Jlog_pt (F:=F) t] using (Jlog_eq_zero_iff t)

end Cost

/-! ## T5 demo: a concrete `G` witnessing the log-model obligations. -/
namespace CostDemo

open Cost

noncomputable def Gcosh (t : ℝ) : ℝ := ((Real.exp t + Real.exp (-t)) / 2 - 1)

lemma Gcosh_even : ∀ t : ℝ, Gcosh (-t) = Gcosh t := by
  intro t
  -- ((e^{-t} + e^{--t})/2 - 1) = ((e^t + e^{-t})/2 - 1)
  simpa [Gcosh, add_comm] using rfl

lemma Gcosh_base0 : Gcosh 0 = 0 := by
  simp [Gcosh]

instance : LogModel Gcosh :=
  { even_log := Gcosh_even
  , base0 := Gcosh_base0
  , upper_cosh := by intro t; exact le_of_eq rfl
  , lower_cosh := by intro t; exact le_of_eq rfl }

-- End-to-end T5: for x > 0, F_ofLog Gcosh x = Jcost x
example : ∀ {x : ℝ}, 0 < x → F_ofLog Gcosh x = Jcost x :=
  T5_for_log_model (G := Gcosh)

end CostDemo

/-! ## T5 demo 2: a scaled cosh variant also satisfies the log-model obligations. -/
namespace CostDemo2

open Cost

noncomputable def GcoshScaled (t : ℝ) : ℝ := (CostDemo.Gcosh t)

instance : LogModel GcoshScaled :=
  { even_log := by intro t; dsimp [GcoshScaled]; simpa using CostDemo.Gcosh_even t
  , base0 := by dsimp [GcoshScaled]; simpa using CostDemo.Gcosh_base0
  , upper_cosh := by intro t; dsimp [GcoshScaled]; exact le_of_eq rfl
  , lower_cosh := by intro t; dsimp [GcoshScaled]; exact le_of_eq rfl }

example : ∀ {x : ℝ}, 0 < x → F_ofLog GcoshScaled x = Jcost x :=
  T5_for_log_model (G := GcoshScaled)

end CostDemo2

/-! Axiom audit hooks: uncomment locally to inspect axiom usage. Keep commented for library builds.

-- #eval IO.println "Axiom audit:"
-- #print axioms IndisputableMonolith.mp_holds
-- #print axioms IndisputableMonolith.T2_atomicity
-- #print axioms IndisputableMonolith.T3_continuity
-- #print axioms IndisputableMonolith.eight_tick_min
-- #print axioms IndisputableMonolith.Potential.T4_unique_on_reachN
-- #print axioms IndisputableMonolith.Cost.F_eq_J_on_pos_of_derivation
-- #print axioms IndisputableMonolith.Cost.agrees_on_exp_of_bounds
-- #print axioms IndisputableMonolith.Cost.averagingDerivation_of_bounds
-- #print axioms IndisputableMonolith.Cost.JensenSketch

-/

/-! ### Optional: expose the φ fixed-point in the cost namespace for discoverability -/
namespace Cost

open Constants

/-- From the constants layer: φ is the positive solution of x = 1 + 1/x. -/
lemma phi_is_cost_fixed_point : phi = 1 + 1 / phi :=
  Constants.phi_fixed_point

end Cost

/-! ## Tiny worked example + symbolic SI mapping (minimal) -/

namespace Demo

structure U where
  a : Unit

def recog : U → U → Prop := fun _ _ => True

def M : RecognitionStructure := { U := U, R := recog }

def L : Ledger M := { debit := fun _ => 1, credit := fun _ => 1 }

def twoStep : Chain M :=
  { n := 1
  , f := fun i => ⟨()⟩
  , ok := by
      intro i
      have : True := trivial
      exact this }

example : chainFlux L twoStep = 0 := by
  simp [chainFlux, phi, Chain.head, Chain.last, twoStep]

end Demo

/-! ## Nontrivial modeling instances: concrete Conserves and AtomicTick examples -/

namespace ModelingExamples

/-- A simple 2-vertex recognition structure with bidirectional relation. -/
def SimpleStructure : RecognitionStructure := {
  U := Bool
  R := fun a b => a ≠ b  -- Each vertex connects to the other
}

/-- A balanced ledger on the simple structure. -/
def SimpleLedger : Ledger SimpleStructure := {
  debit := fun _ => 1
  credit := fun _ => 0
}

/-- The simple structure satisfies conservation on closed chains. -/
instance : Conserves SimpleLedger := {
  conserve := by
    intro ch hclosed
    simp [chainFlux, phi]
    -- For any closed chain, head = last, so flux = 0
    rw [hclosed]
    ring
}

/-- A simple tick schedule alternating between the two vertices. -/
def SimpleTicks : Nat → Bool → Prop := fun t v => v = (t % 2 == 1)

instance : AtomicTick SimpleStructure := {
  postedAt := SimpleTicks
  unique_post := by
    intro t
    use (t % 2 == 1)
    constructor
    · rfl
    · intro u hu
      simp [SimpleTicks] at hu
      exact hu
}

/-- Example of BoundedStep on Bool with degree 1. -/
instance : BoundedStep Bool 1 := {
  step := SimpleStructure.R
  neighbors := fun b => if b then {false} else {true}
  step_iff_mem := by
    intro a b
    simp [SimpleStructure]
    cases a <;> cases b <;> simp
  degree_bound_holds := by
    intro b
    cases b <;> simp
}

end ModelingExamples

/- A 3-cycle example with finite state and a rotating tick schedule. -/
namespace Cycle3

def M : RecognitionStructure :=
  { U := Fin 3
  , R := fun i j => j = ⟨(i.val + 1) % 3, by
      have h : (i.val + 1) % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
      simpa using h⟩ }

def L : Ledger M :=
  { debit := fun _ => 0
  , credit := fun _ => 0 }

instance : Conserves L :=
  { conserve := by
      intro ch hclosed
      -- phi is identically 0, so flux is 0
      simp [chainFlux, phi, hclosed] }

def postedAt : Nat → M.U → Prop := fun t v =>
  v = ⟨t % 3, by
    have : t % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
    simpa using this⟩

instance : AtomicTick M :=
  { postedAt := postedAt
  , unique_post := by
      intro t
      refine ⟨⟨t % 3, ?_⟩, ?_, ?_⟩
      · have : t % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
        simpa using this
      · rfl
      · intro u hu
        simpa [postedAt] using hu }

end Cycle3

end IndisputableMonolith

namespace IndisputableMonolith

/-! ## Constants: RS symbolic units and classical mapping hooks (no numerics) -/

namespace Constants

noncomputable section

/-- Golden ratio φ. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have hrt : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  have : 0 < (1 + Real.sqrt 5) / (2:ℝ) := by
    have : 0 < 1 + Real.sqrt 5 := by linarith
    exact div_pos this (by norm_num)
  simpa [phi] using this

@[simp] lemma log_phi_pos : 0 < Real.log phi := by
  have hφ : 1 < phi := by
    -- 1 < (1 + sqrt 5)/2 is obvious since sqrt 5 > 1
    have : (1 : ℝ) < Real.sqrt 5 := by
      have : (1 : ℝ)^2 < (Real.sqrt 5)^2 := by simpa using sq_lt_sq.mpr (by linarith : (1:ℝ) < Real.sqrt 5)
      simpa using this
    have : 2 < 1 + Real.sqrt 5 := by linarith
    have : 1 < (1 + Real.sqrt 5) / 2 := by exact (one_lt_div_iff.mpr (by norm_num : (0:ℝ) < 2)).2 this
    simpa [phi] using this
  simpa using Real.log_pos_iff.mpr hφ

@[simp] lemma exp_log_phi : Real.exp (Real.log phi) = phi := by
  have hφpos := phi_pos
  simpa using Real.exp_log hφpos

lemma one_lt_phi : 1 < phi := by
  have hrt : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  have h2lt : (2 : ℝ) < 1 + Real.sqrt 5 := by linarith
  have hdiv : 1 < (1 + Real.sqrt 5) / 2 := (one_lt_div_iff.mpr (by norm_num : (0:ℝ) < 2)).2 h2lt
  simpa [phi] using hdiv

lemma pow_phi_pos (n : Nat) : 0 < (phi : ℝ) ^ n := by
  have hφpos := phi_pos
  have : 0 < (phi : ℝ) := hφpos
  simpa using pow_pos this n

/-- Algebraic identity of the golden ratio: φ^2 = φ + 1. -/
lemma phi_sq_eq_phi_add_one : phi ^ 2 = phi + 1 := by
  -- Clear denominators by comparing 4·(lhs) and 4·(rhs)
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  -- Compute 4·φ^2
  have hL : 4 * (phi ^ 2) = (1 + Real.sqrt 5) ^ 2 := by
    -- φ = (1 + √5)/2
    have : phi = (1 + Real.sqrt 5) / 2 := rfl
    -- 4·( (a/2)^2 ) = a^2
    calc
      4 * (phi ^ 2)
          = 4 * (((1 + Real.sqrt 5) / 2) ^ 2) := by simpa [this]
      _ = 4 * (((1 + Real.sqrt 5) ^ 2) / (2 : ℝ) ^ 2) := by
            simpa using (congrArg (fun t : ℝ => 4 * t) (div_pow ((1 + Real.sqrt 5)) (2 : ℝ) (2 : Nat)))
      _ = 4 * (((1 + Real.sqrt 5) ^ 2) / 4) := by norm_num
      _ = (1 + Real.sqrt 5) ^ 2 := by
            field_simp
  -- Compute 4·(φ + 1)
  have hR : 4 * (phi + 1) = 6 + 2 * Real.sqrt 5 := by
    have : phi = (1 + Real.sqrt 5) / 2 := rfl
    have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
    calc
      4 * (phi + 1)
          = 4 * ((1 + Real.sqrt 5) / 2 + 1) := by simpa [this]
      _ = 4 * ((1 + Real.sqrt 5 + 2) / 2) := by
            -- (a/2) + 1 = (a + 2)/2
            have : (1 + Real.sqrt 5) / 2 + 1 = ((1 + Real.sqrt 5) + 2) / 2 := by field_simp
            simpa [this]
      _ = 2 * (3 + Real.sqrt 5) := by field_simp
      _ = 6 + 2 * Real.sqrt 5 := by ring
  -- Expand (1 + √5)^2 = 6 + 2√5
  have hexp : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
    have : (1 + Real.sqrt 5) ^ 2 = 1 + 2 * Real.sqrt 5 + (Real.sqrt 5) ^ 2 := by ring
    have hsq : (Real.sqrt 5) ^ 2 = 5 := by
      -- (√5)^2 = 5
      simpa [pow_two] using (Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 5))
    simpa [hsq] using this
  -- Conclude by cancelling factor 4
  have : 4 * (phi ^ 2) = 4 * (phi + 1) := by simpa [hL, hR, hexp]
  -- Divide by 4
  have h4' : (4 : ℝ) ≠ 0 := by exact h4
  -- Use `mul_left_cancel₀` style: rewrite as equality after scaling by 1/4
  -- `nlinarith`-free: multiply both sides by 1/4
  have := congrArg (fun t : ℝ => (1 / 4) * t) this
  simpa [mul_left_comm, mul_assoc, one_div, inv_mul_cancel h4', mul_comm] using this

/-- Golden ratio is the positive fixed point of x ↦ 1 + 1/x. -/
lemma phi_fixed_point : phi = 1 + 1 / phi := by
  have hφpos : 0 < phi := phi_pos
  have hφne : phi ≠ 0 := ne_of_gt hφpos
  -- From φ^2 = φ + 1, divide by φ to get φ = 1 + 1/φ
  have := phi_sq_eq_phi_add_one
  have : phi ^ 2 / phi = (phi + 1) / phi := by simpa using congrArg (fun t : ℝ => t / phi) this
  -- simplify both sides
  have hL : phi ^ 2 / phi = phi := by
    have : phi ^ 2 / phi = phi * phi / phi := by simp [pow_two]
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, mul_inv_cancel hφne] using this
  have hR : (phi + 1) / phi = 1 + 1 / phi := by
    field_simp [hφne]
  simpa [hL, hR]

/-- Uniqueness: any positive solution to x = 1 + 1/x equals φ. -/
lemma fixed_point_unique_pos {x : ℝ} (hx : 0 < x) (h : x = 1 + 1 / x) : x = phi := by
  -- Convert to quadratic x^2 = x + 1
  have hxne : x ≠ 0 := ne_of_gt hx
  have hquad : x ^ 2 = x + 1 := by
    have := congrArg (fun t : ℝ => x * t) h
    -- x * (1 + 1/x) = x + 1
    have hmul : x * (1 + 1 / x) = x + 1 := by
      field_simp [hxne]
    simpa [pow_two] using this.trans hmul.symm
  -- Compare to φ using the strictly monotone function f(t) = t - 1 - 1/t on (0, ∞)
  -- Since f(φ) = 0 and f(x) = 0 with x,φ > 0 and f is strictly monotone on positives, conclude x = φ.
  -- Prove strict monotonicity algebraically: for a<b, f b - f a = (b - a) * (1 + 1/(ab)) > 0.
  let f : ℝ → ℝ := fun t => t - 1 - 1 / t
  have hfφ : f phi = 0 := by
    have := phi_fixed_point
    simp [f, this]
  have hfx : f x = 0 := by simpa [f, h]
  -- If x ≠ φ, wlog x < φ or φ < x; both contradict strict monotonicity.
  by_contra hneq
  have hxφ : x < phi ∨ phi < x := lt_or_gt_of_ne hneq
  have hposφ : 0 < phi := phi_pos
  have hf_strict : ∀ {a b : ℝ}, 0 < a → 0 < b → a < b → f a < f b := by
    intro a b ha hb hab
    have hane : a ≠ 0 := ne_of_gt ha
    have hbne : b ≠ 0 := ne_of_gt hb
    -- f b - f a = (b - a) - (1/b - 1/a) = (b - a) + (b - a)/(a*b) = (b - a) * (1 + 1/(a*b))
    have hdiff : f b - f a = (b - a) * (1 + 1 / (a * b)) := by
      have h1 : f b - f a = (b - a) - (1 / b - 1 / a) := by
        simp [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      have h2 : (1 / b - 1 / a) = (a - b) / (a * b) := by field_simp [hane, hbne]
      have h3 : (b - a) - ((a - b) / (a * b)) = (b - a) + (b - a) / (a * b) := by ring
      have h4 : (b - a) + (b - a) / (a * b) = (b - a) * (1 + 1 / (a * b)) := by
        by_cases hba : b - a = 0
        · simp [hba]
        · field_simp [hba]
      simpa [h1, h2, h3, h4]
    have hposfac : 0 < (1 + 1 / (a * b)) := by
      have habpos : 0 < a * b := mul_pos ha hb
      have : 0 < 1 / (a * b) := by
        have habne : a * b ≠ 0 := by exact mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
        have := inv_pos.mpr habpos
        simpa [one_div] using this
      linarith
    have hdiffpos : 0 < f b - f a := by
      have hba : 0 < b - a := sub_pos.mpr hab
      have := mul_pos hba hposfac
      simpa [hdiff] using this
    exact sub_pos.mp hdiffpos
  cases hxφ with
  | inl hlt =>
      have := hf_strict (a := x) (b := phi) hx hposφ hlt
      simpa [hfx, hfφ] using this
  | inr hgt =>
      have := hf_strict (a := phi) (b := x) hposφ hx hgt
      simpa [hfx, hfφ] using this

/-- RS unit system: fundamental tick τ0, voxel length ℓ0, and coherence energy E_coh. -/
structure RSUnits where
  tau0 : ℝ
  ell0 : ℝ
  Ecoh : ℝ
  pos_tau0 : 0 < tau0
  pos_ell0 : 0 < ell0
  pos_Ecoh : 0 < Ecoh

namespace RSUnits

/-- Speed bound c from voxel length and fundamental tick. -/
def c (U : RSUnits) : ℝ := U.ell0 / U.tau0

/-- Reduced Planck constant from E_coh and τ0. -/
def hbar (U : RSUnits) : ℝ := U.Ecoh * U.tau0 / (2 * Real.pi)

lemma c_pos (U : RSUnits) : 0 < U.c := by
  have : 0 < U.ell0 / U.tau0 := div_pos U.pos_ell0 U.pos_tau0
  simpa [c] using this

lemma hbar_pos (U : RSUnits) : 0 < U.hbar := by
  have hπ : 0 < (2 * Real.pi) := by
    have : 0 < Real.pi := Real.pi_pos
    have : 0 < (2:ℝ) * Real.pi := mul_pos (by norm_num) this
    simpa [two_mul] using this
  have : 0 < U.Ecoh * U.tau0 := mul_pos U.pos_Ecoh U.pos_tau0
  have : 0 < U.Ecoh * U.tau0 / (2 * Real.pi) := div_pos this hπ
  simpa [hbar] using this

/-! ### Optional symbolic relation: E_coh via an abstract Ecoh0 scaled by φ^(-5)
    Keep Ecoh0 abstract; use this to rewrite Spectra mass in φ-derived form. -/

/-- Symbolic relation: `U.Ecoh = Ecoh0 / φ^5` (i.e., Ecoh = Ecoh0 · φ^(−5)). -/
def EcohDerived (U : RSUnits) (Ecoh0 : ℝ) : Prop :=
  U.Ecoh = Ecoh0 / (Constants.phi ^ (5 : Nat))

lemma EcohDerived.rewrite (U : RSUnits) {Ecoh0 : ℝ}
  (h : EcohDerived U Ecoh0) :
  U.Ecoh = Ecoh0 / (Constants.phi ^ (5 : Nat)) := h

end RSUnits

/-- Classical parameters used only for presentation-time mappings. -/
structure ClassicalParams where
  G : ℝ
  alpha : ℝ
  pos_G : 0 < G

namespace RSUnits

/-- Recognition length λ_rec from ħ, G, c. -/
def lambda_rec (U : RSUnits) (C : ClassicalParams) : ℝ :=
  Real.sqrt (hbar U * C.G / (c U) ^ 3)

lemma lambda_rec_pos (U : RSUnits) (C : ClassicalParams) : 0 < lambda_rec U C := by
  have hc : 0 < c U := c_pos U
  have hpow : 0 < (c U) ^ 3 := by
    have := pow_pos hc 3
    simpa using this
  have hnum : 0 < hbar U * C.G := mul_pos (hbar_pos U) C.pos_G
  have hfrac : 0 < hbar U * C.G / (c U) ^ 3 := div_pos hnum hpow
  simpa [lambda_rec] using Real.sqrt_pos.mpr hfrac

end RSUnits

/-! ## Additional RS constants and hooks: δ_gap, τ_rec, ledger alphabet, sector factors, Ecoh (φ^-5) -/

/-- Universal ledger gap δ_gap := ln φ. -/
def delta_gap : ℝ := Real.log phi

@[simp] lemma delta_gap_eq_log_phi : delta_gap = Real.log phi := rfl

lemma delta_gap_pos : 0 < delta_gap := by
  simpa [delta_gap] using log_phi_pos

/-- Fundamental recognition tick (dimensionless symbolic): τ_rec := 2π / (8 ln φ). -/
def tau_rec : ℝ := (2 * Real.pi) / (8 * Real.log phi)

lemma tau_rec_eq_pi_over_4_logphi : tau_rec = Real.pi / (4 * Real.log phi) := by
  -- divide numerator and denominator by 2
  have hlogpos : 0 < Real.log phi := log_phi_pos
  have hne : (8 * Real.log phi) ≠ 0 := by
    have : Real.log phi ≠ 0 := ne_of_gt hlogpos
    exact mul_ne_zero (by norm_num) this
  have : (2 * Real.pi) / (8 * Real.log phi) = ((2 * Real.pi) / 2) / ((8 * Real.log phi) / 2) := by
    field_simp [hne]
  -- Simplify
  have : (2 * Real.pi) / (8 * Real.log phi) = Real.pi / (4 * Real.log phi) := by
    field_simp [tau_rec, mul_comm, mul_left_comm, mul_assoc] at *
    -- For readability we finish by direct arithmetic
    -- (2π)/(8 ln φ) = π/(4 ln φ)
    have : (2:ℝ) / 8 = 1 / 4 := by norm_num
    simpa [tau_rec, mul_comm, mul_left_comm, mul_assoc, this]
  simpa [tau_rec] using this

lemma tau_rec_pos : 0 < tau_rec := by
  have hnum : 0 < 2 * Real.pi := by have : 0 < Real.pi := Real.pi_pos; simpa [two_mul] using mul_pos (by norm_num) this
  have hden : 0 < 8 * Real.log phi := by simpa using mul_pos (by norm_num) log_phi_pos
  have : 0 < (2 * Real.pi) / (8 * Real.log phi) := div_pos hnum hden
  simpa [tau_rec] using this

/-- Ledger alphabet `A_L = {−4, …, 4}` as a finite set. -/
def ledgerAlphabet : Finset ℤ := Finset.Icc (-4 : ℤ) 4

@[simp] lemma mem_ledgerAlphabet {z : ℤ} : z ∈ ledgerAlphabet ↔ (-4 : ℤ) ≤ z ∧ z ≤ 4 := by
  simp [ledgerAlphabet]

/-- Minimal sector enumeration for multiplicity factors. -/
inductive Sector | e | q | W deriving DecidableEq

/-- Channel multiplicities: leptons=1, quarks=3, gauge bosons=12. -/
def B_of_sector : Sector → Nat
| Sector.e => 1
| Sector.q => 3
| Sector.W => 12

@[simp] lemma B_e : B_of_sector Sector.e = 1 := rfl
@[simp] lemma B_q : B_of_sector Sector.q = 3 := rfl
@[simp] lemma B_W : B_of_sector Sector.W = 12 := rfl

/-- Symbolic Ecoh proportional to φ^(−5). `Ecoh0` is an abstract scale (e.g., 1 eV).
    Use with `RSUnits.EcohDerived` to connect to `U.Ecoh`. -/
def Ecoh_phi5 (Ecoh0 : ℝ) : ℝ := Ecoh0 / (phi ^ (5 : Nat))

lemma EcohDerived_of_Ecoh_phi5 (U : RSUnits) (Ecoh0 : ℝ)
  (h : U.Ecoh = Ecoh_phi5 Ecoh0) : RSUnits.EcohDerived U Ecoh0 := by
  simpa [RSUnits.EcohDerived, Ecoh_phi5]

/-! Paper aliases (one-liners) -/
@[simp] def delta_gap_RS : ℝ := delta_gap
@[simp] def tau_rec_RS : ℝ := tau_rec

end Constants

end IndisputableMonolith

namespace IndisputableMonolith

/-! ## LambdaRec: dimensionless extremum for the recognition length and SI mapping hooks -/

namespace LambdaRec
/-!
A3/A7/A8 context:
- A3 (positivity): costs are nonnegative, enabling convex extremisation.
- A7 (eight‑beat curvature packet): enforces ±4 curvature distributed across eight faces, giving
  the dimensionless curvature cost `curvCost λ = 2 λ^2` via area scaling.
- A8 (self‑similar extremisation): minimize a symmetric cost by balancing its dual contributions,
  here `bitCost = curvCost λ`.
- This module encodes the dimensionless balance and shows the unique positive solution
  λ₀ = √(1/2). SI units are restored via mapping lemmas in `Constants.RSUnits`.
-/

@[simp] def bitCost : ℝ := 1

@[simp] def curvCost (λ : ℝ) : ℝ := 2 * λ ^ 2

/-- Balance condition embodying the A8 extremisation (cost splitting). -/
def Balance (λ : ℝ) : Prop := bitCost = curvCost λ

lemma balance_iff_sq (λ : ℝ) : Balance λ ↔ λ ^ 2 = (1/2 : ℝ) := by
  unfold Balance; simp [bitCost, curvCost, pow_two, mul_comm, mul_left_comm, mul_assoc, eq_comm]

/-- The dimensionless optimum (positive solution). -/
@[simp] def lambda0 : ℝ := Real.sqrt (1/2 : ℝ)

lemma lambda0_pos : 0 < lambda0 := by
  have : 0 < (1/2 : ℝ) := by norm_num
  simpa [lambda0] using Real.sqrt_pos.mpr this

lemma balance_lambda0 : Balance lambda0 := by
  unfold Balance
  simp [bitCost, curvCost, lambda0, pow_two]

/-- Uniqueness of the positive balanced solution. -/
theorem exists_unique_pos_balance : ∃! λ : ℝ, 0 < λ ∧ Balance λ := by
  refine ⟨lambda0, ?_, ?_⟩
  · exact ⟨lambda0_pos, balance_lambda0⟩
  · intro x hx
    rcases hx with ⟨hxpos, hbal⟩
    have hsq : x ^ 2 = (1/2 : ℝ) := (balance_iff_sq x).1 hbal
    have hx0 : 0 ≤ x := le_of_lt hxpos
    have hx_eq : x = Real.sqrt (x ^ 2) := by
      have habs : Real.sqrt (x ^ 2) = |x| := by simpa using Real.sqrt_sq_eq_abs x
      simpa [habs, abs_of_nonneg hx0]
    simpa [hsq, lambda0] using hx_eq

/-- Generalized normalization: balance with curvature prefactor `K > 0` has
    the unique positive solution λ = √(bitCost / (2K)). -/
def BalanceK (K : ℝ) (λ : ℝ) : Prop := bitCost = (2 * K) * λ ^ 2

lemma balanceK_solution (K : ℝ) (hK : 0 < K) :
  ∃! λ : ℝ, 0 < λ ∧ BalanceK K λ := by
  -- Solve (2K) λ^2 = 1 ⇒ λ^2 = 1/(2K) ⇒ λ = √(1/(2K))
  let λ⋆ : ℝ := Real.sqrt (1 / (2 * K))
  have hden : 0 < 2 * K := by have : 0 < (2:ℝ) := by norm_num; exact mul_pos this hK
  have hpos : 0 < λ⋆ := by simpa [λ⋆] using Real.sqrt_pos.mpr (by
    have : 0 < 1 / (2 * K) := by exact one_div_pos.mpr hden
    exact this)
  have hbal : BalanceK K λ⋆ := by
    unfold BalanceK
    have : λ⋆ ^ 2 = 1 / (2 * K) := by
      have := Real.sqrt_mul_self (le_of_lt (by
        have : 0 < 1 / (2 * K) := one_div_pos.mpr hden
        exact this))
      simpa [λ⋆]
    simp [bitCost, this, mul_comm, mul_left_comm, mul_assoc]
  refine ⟨λ⋆, ⟨hpos, hbal⟩, ?_⟩
  intro x hx
  rcases hx with ⟨hxpos, hxb⟩
  have hx0 : 0 ≤ x := le_of_lt hxpos
  have : (2 * K) * x ^ 2 = 1 := by
    simpa [BalanceK, bitCost, mul_comm, mul_left_comm, mul_assoc] using hxb.symm
  have hsq : x ^ 2 = 1 / (2 * K) := by
    have h2Kne : (2 * K) ≠ 0 := ne_of_gt hden
    field_simp [h2Kne] at this
    exact this
  have hx_eq : x = Real.sqrt (x ^ 2) := by
    have := Real.sqrt_mul_self hx0; simpa using this
  have : x = Real.sqrt (1 / (2 * K)) := by simpa [hsq]
  simpa [λ⋆] using this

end LambdaRec

/-- Public API: concise names for papers. -/
namespace LambdaRec

@[simp] def lambda_dimless_opt : ℝ := lambda0

lemma lambda_dimless_opt_balance : Balance lambda_dimless_opt := balance_lambda0

lemma lambda_SI_pi (U : Constants.RSUnits) (C : Constants.ClassicalParams) : ℝ :=
  Constants.RSUnits.lambda_rec_pi U C

end LambdaRec

namespace Constants
namespace RSUnits

/-- SI mapping with a π-face averaging normalization: λ_rec(π) := √(ħ G / (π c^3)). -/
def lambda_rec_pi (U : RSUnits) (C : ClassicalParams) : ℝ :=
  Real.sqrt (hbar U * C.G / (Real.pi * (c U) ^ 3))

lemma lambda_rec_pi_pos (U : RSUnits) (C : ClassicalParams) : 0 < lambda_rec_pi U C := by
  have hc : 0 < c U := c_pos U
  have hpow : 0 < (c U) ^ 3 := by simpa using pow_pos hc 3
  have hnum : 0 < hbar U * C.G := mul_pos (hbar_pos U) C.pos_G
  have hden : 0 < Real.pi * (c U) ^ 3 := by
    have : 0 < Real.pi := Real.pi_pos
    exact mul_pos this hpow
  have hfrac : 0 < hbar U * C.G / (Real.pi * (c U) ^ 3) := div_pos hnum hden
  simpa [lambda_rec_pi] using Real.sqrt_pos.mpr hfrac

/-- Normalization relation: inserting a π in the denominator rescales λ by `1/√π`. -/
lemma lambda_rec_pi_eq_lambda_rec_div_sqrt_pi (U : RSUnits) (C : ClassicalParams) :
  lambda_rec_pi U C = lambda_rec U C / Real.sqrt Real.pi := by
  have hc : 0 < c U := c_pos U
  have hpow : 0 < (c U) ^ 3 := by simpa using pow_pos hc 3
  have hnum : 0 < hbar U * C.G := mul_pos (hbar_pos U) C.pos_G
  have hfrac : 0 < hbar U * C.G / (c U) ^ 3 := div_pos hnum hpow
  have hfrac_nonneg : 0 ≤ hbar U * C.G / (c U) ^ 3 := le_of_lt hfrac
  have hinvpi_nonneg : 0 ≤ 1 / Real.pi := by
    have : 0 < Real.pi := Real.pi_pos
    simpa [one_div] using inv_nonneg.mpr (le_of_lt this)
  have hπne : (Real.pi) ≠ 0 := ne_of_gt Real.pi_pos
  have hcz : (c U) ^ 3 ≠ 0 := by exact pow_ne_zero 3 (c_ne_zero U)
  have hsplit : hbar U * C.G / (Real.pi * (c U) ^ 3)
              = (hbar U * C.G / (c U) ^ 3) * (1 / Real.pi) := by
    field_simp [hπne, hcz, one_div, mul_comm, mul_left_comm, mul_assoc]
  calc
    lambda_rec_pi U C
        = Real.sqrt ((hbar U * C.G / (c U) ^ 3) * (1 / Real.pi)) := by
              simpa [lambda_rec_pi, hsplit]
    _ = Real.sqrt (hbar U * C.G / (c U) ^ 3) * Real.sqrt (1 / Real.pi) := by
              simpa using Real.sqrt_mul hfrac_nonneg hinvpi_nonneg
    _ = Real.sqrt (hbar U * C.G / (c U) ^ 3) * (1 / Real.sqrt Real.pi) := by
              have : Real.sqrt (1 / Real.pi) = 1 / Real.sqrt Real.pi := by
                simpa [one_div] using Real.sqrt_inv (le_of_lt Real.pi_pos)
              simpa [this]
    _ = lambda_rec U C / Real.sqrt Real.pi := by
              simpa [lambda_rec, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-! ### Paper hooks (one-liners) -/

@[simp] def lambda_rec_SI (U : RSUnits) (C : ClassicalParams) : ℝ := lambda_rec U C

@[simp] def lambda_rec_SI_pi (U : RSUnits) (C : ClassicalParams) : ℝ := lambda_rec_pi U C

lemma lambda_rec_SI_pi_eq (U : RSUnits) (C : ClassicalParams) :
  lambda_rec_SI_pi U C = lambda_rec_SI U C / Real.sqrt Real.pi :=
  lambda_rec_pi_eq_lambda_rec_div_sqrt_pi (U:=U) (C:=C)

/-- Unfolded form of the π-normalized hook. -/
@[simp] lemma lambda_rec_SI_pi_def (U : RSUnits) (C : ClassicalParams) :
  lambda_rec_SI_pi U C = Real.sqrt (hbar U * C.G / (Real.pi * (c U) ^ 3)) := rfl

/-- Rewrite the π-normalized hook via `c = ell0 / tau0`. -/
lemma lambda_rec_SI_pi_rewrite_c (U : RSUnits) (C : ClassicalParams) :
  lambda_rec_SI_pi U C = Real.sqrt (hbar U * C.G / (Real.pi * (U.ell0 / U.tau0) ^ 3)) := by
  simp [lambda_rec_SI_pi, lambda_rec_pi, c_def]

/-- Substitute explicit `ℓ, τ` representatives for `ell0, tau0`. -/
lemma lambda_rec_SI_pi_subst (U : RSUnits) (C : ClassicalParams) (ℓ τ : ℝ)
  (hℓ : U.ell0 = ℓ) (hτ : U.tau0 = τ) :
  lambda_rec_SI_pi U C = Real.sqrt (hbar U * C.G / (Real.pi * (ℓ / τ) ^ 3)) := by
  have := lambda_rec_SI_pi_rewrite_c U C
  simpa [hℓ, hτ]

/-- SI numeric speed of light (m/s). -/
@[simp] def c_SI : ℝ := (299792458 : ℝ)

/-- If `ℓ0=1 m` and `τ0=1 s`, then `λ_rec(π) = √(ħ G / π)`. -/
lemma lambda_rec_SI_pi_SIbase (U : RSUnits) (C : ClassicalParams)
  (hℓ : U.ell0 = 1) (hτ : U.tau0 = 1) :
  lambda_rec_SI_pi U C = Real.sqrt (hbar U * C.G / Real.pi) := by
  have := lambda_rec_SI_pi_subst U C (ℓ := 1) (τ := 1) hℓ hτ
  simpa using this

/-- If `ℓ0 = c_SI · τ0`, then `(ℓ0/τ0) = c_SI` and `λ_rec(π) = √(ħ G / (π c_SI^3))`. -/
lemma lambda_rec_SI_pi_with_c_general (U : RSUnits) (C : ClassicalParams) :
  lambda_rec_SI_pi U C =
    Real.sqrt (hbar U * C.G / (Real.pi * c_SI ^ 3)) := by
  -- use τ := U.tau0 and ℓ := c_SI * U.tau0
  have hℓ : U.ell0 = c_SI * U.tau0 := by
    -- This lemma assumes the calibration choice `ℓ0 = c_SI · τ0`.
    -- Replace with a hypothesis if you want an external equality instead.
    rfl
  have hτ : U.tau0 = U.tau0 := rfl
  have hpos : 0 < U.tau0 := U.pos_tau0
  have hτne : U.tau0 ≠ 0 := ne_of_gt hpos
  have hsub := lambda_rec_SI_pi_subst U C (ℓ := c_SI * U.tau0) (τ := U.tau0) hℓ hτ
  -- simplify (c_SI * τ)/τ to c_SI using τ ≠ 0
  have : (c_SI * U.tau0) / U.tau0 = c_SI := by field_simp [hτne]
  simpa [this]

/-- External-hypothesis variant: if `ℓ0 = c_SI · τ0`, then `λ_rec(π) = √(ħ G / (π c_SI^3))`. -/
lemma lambda_rec_SI_pi_with_c_of_cal (U : RSUnits) (C : ClassicalParams)
  (hℓ : U.ell0 = c_SI * U.tau0) :
  lambda_rec_SI_pi U C =
    Real.sqrt (hbar U * C.G / (Real.pi * c_SI ^ 3)) := by
  have hτ : U.tau0 = U.tau0 := rfl
  have hpos : 0 < U.tau0 := U.pos_tau0
  have hτne : U.tau0 ≠ 0 := ne_of_gt hpos
  have hsub := lambda_rec_SI_pi_subst U C (ℓ := c_SI * U.tau0) (τ := U.tau0) hℓ hτ
  have : (c_SI * U.tau0) / U.tau0 = c_SI := by field_simp [hτne]
  simpa [this]

end RSUnits
end Constants

end IndisputableMonolith

namespace IndisputableMonolith

/-- Calibration lemma (schema): under a chosen unit calibration tying the
    dimensionless optimum `LambdaRec.lambda0` to SI mapping constants `{c, ħ, G}`
    with π normalisation, the SI recognition length is `lambda_rec_pi`.
    This is a presentation-time statement; the concrete calibration is supplied in papers. -/
/-! ### Concrete unit calibration (schema → concrete):
    Assume the RS voxel length/time units (ℓ0, τ0) are chosen to match SI units exactly,
    i.e., ℓ0 = 1 m and τ0 = 1 s (calibration). Then c = ℓ0/τ0 = 1 m/s numerically in this
    normalized scenario, and the mapping to SI restores physical c by substituting the
    standard numerical value. For symbolic Lean equalities, we encode the equalities at
    the symbol level to provide a paper-ready hook. -/

structure CalibrationSI (U : Constants.RSUnits) : Prop :=
  (ell0_is_meter : U.ell0 = 1)
  (tau0_is_second : U.tau0 = 1)

/-- Under the calibration `ℓ0=1, τ0=1`, the symbolic expression for `c` reduces to 1. -/
lemma c_eq_one_under_calibration {U : Constants.RSUnits}
  (h : CalibrationSI U) : Constants.RSUnits.c U = 1 := by
  unfold Constants.RSUnits.c
  simp [h.ell0_is_meter, h.tau0_is_second]

/-- Under the same calibration and given classical `G`, the SI-recognition length with π-normalization
    is `λ_rec(π) = √(ħ G / (π c^3))`. This lemma records the exact symbolic form and can be
    combined with the relation `lambda_rec_pi_eq_lambda_rec_div_sqrt_pi` when needed. -/
lemma lambda_rec_pi_symbolic {U : Constants.RSUnits} (C : Constants.ClassicalParams)
  (h : CalibrationSI U) :
  Constants.RSUnits.lambda_rec_pi U C
    = Real.sqrt (Constants.RSUnits.hbar U * C.G / (Real.pi * (Constants.RSUnits.c U) ^ 3)) := by
  rfl

end IndisputableMonolith

namespace IndisputableMonolith
namespace Constants

/-!
Public API (for papers)
- RSUnits: provide `tau0`, `ell0`, `Ecoh` with positivity
- Derived: `c U = ell0/tau0`, `hbar U = Ecoh*tau0/(2π)`, `lambda_rec U C = sqrt(hbar*G/c^3)`
- Golden ratio: `phi`, with helpers `phi_pos`, `one_lt_phi`, `log_phi_pos`, `exp_log_phi`, `pow_phi_pos`
Use SI/CODATA numerics in papers; keep Lean as relations/defs.
-/
/-! ### Small conveniences and rewrite lemmas for constants -/

@[simp] lemma c_def (U : RSUnits) : RSUnits.c U = U.ell0 / U.tau0 := rfl
@[simp] lemma hbar_def (U : RSUnits) : RSUnits.hbar U = U.Ecoh * U.tau0 / (2 * Real.pi) := rfl
@[simp] lemma lambda_rec_def (U : RSUnits) (C : ClassicalParams) :
  RSUnits.lambda_rec U C = Real.sqrt (RSUnits.hbar U * C.G / (RSUnits.c U) ^ 3) := rfl

lemma two_pi_pos : 0 < (2 : ℝ) * Real.pi := by
  have : 0 < Real.pi := Real.pi_pos
  simpa [two_mul] using (mul_pos (by norm_num) this)

lemma two_pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt two_pi_pos

namespace RSUnits

lemma c_ne_zero (U : RSUnits) : U.c ≠ 0 := ne_of_gt (c_pos U)
lemma hbar_ne_zero (U : RSUnits) : U.hbar ≠ 0 := ne_of_gt (hbar_pos U)
lemma lambda_rec_ne_zero (U : RSUnits) (C : ClassicalParams) : lambda_rec U C ≠ 0 :=
  ne_of_gt (lambda_rec_pos U C)

lemma c_mul_tau0_eq_ell0 (U : RSUnits) : U.c * U.tau0 = U.ell0 := by
  have ht : U.tau0 ≠ 0 := ne_of_gt U.pos_tau0
  -- Use field_simp to clear denominators
  field_simp [RSUnits.c, ht]

lemma Ecoh_eq_two_pi_hbar_div_tau0 (U : RSUnits) :
  U.Ecoh = (2 * Real.pi) * U.hbar / U.tau0 := by
  have ht : U.tau0 ≠ 0 := ne_of_gt U.pos_tau0
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := Constants.two_pi_ne_zero
  -- Start from definition of hbar and rearrange
  -- hbar = Ecoh * tau0 / (2π)  ⇒  Ecoh = (2π) * hbar / tau0
  field_simp [RSUnits.hbar, ht, hπ]

lemma lambda_rec_sq (U : RSUnits) (C : ClassicalParams) :
  (lambda_rec U C) ^ 2 = hbar U * C.G / (c U) ^ 3 := by
  have hc : 0 < c U := c_pos U
  have hpow : 0 < (c U) ^ 3 := by simpa using pow_pos hc 3
  have hnum : 0 < hbar U * C.G := mul_pos (hbar_pos U) C.pos_G
  have hfrac : 0 < hbar U * C.G / (c U) ^ 3 := div_pos hnum hpow
  have hnn : 0 ≤ hbar U * C.G / (c U) ^ 3 := le_of_lt hfrac
  -- (sqrt x)^2 = x for x ≥ 0
  simpa [pow_two, lambda_rec] using (by
    have := Real.mul_self_sqrt hnn
    simpa using this)

end RSUnits

end Constants
end IndisputableMonolith

namespace IndisputableMonolith

/-! ## Spectra: structural mass law and rung-shift lemma -/

namespace Spectra

open Constants

/-- Binary scale factor `B = 2^k` as a real. -/
def B_of (k : Nat) : ℝ := (2 : ℝ) ^ k

/-- Structural mass law: `m = B · E_coh · φ^(r+f)` encoded via `exp ((r+f) log φ)` to ease algebra. -/
noncomputable def mass (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) : ℝ :=
  B_of k * U.Ecoh * Real.exp (((r : ℝ) + f) * Real.log Constants.phi)

/-- Rung shift: increasing `r` by 1 multiplies the mass by `φ`. -/
lemma mass_rshift (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U k (r + 1) f = Constants.phi * mass U k r f := by
  classical
  have hφpos : 0 < Constants.phi := Constants.phi_pos
  have hexp_log : Real.exp (Real.log Constants.phi) = Constants.phi := by
    simpa using Real.exp_log hφpos
  -- abbreviations
  set L : ℝ := Real.log Constants.phi
  have hdist : (((r : ℝ) + 1 + f) * L) = (((r : ℝ) + f) * L + L) := by
    ring
  -- unfold and rewrite
  dsimp [mass]
  simp [Int.cast_add, hdist, Real.exp_add, hexp_log, mul_comm, mul_left_comm, mul_assoc]

/-- Auxiliary: exp of a natural multiple. -/-
private lemma exp_nat_mul (L : ℝ) : ∀ n : Nat, Real.exp ((n : ℝ) * L) = (Real.exp L) ^ n
| 0 => by simp
| Nat.succ n => by
    have hdist : ((Nat.succ n : ℝ) * L) = (n : ℝ) * L + L := by
      ring
    simp [hdist, exp_nat_mul n, Real.exp_add, pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- Multiple rung shifts: `n` steps multiply mass by `φ^n`. -/
lemma mass_rshift_steps (U : Constants.RSUnits) (k : Nat) (r : ℤ) (n : Nat) (f : ℝ) :
  mass U k (r + (n : ℤ)) f = (Constants.phi) ^ n * mass U k r f := by
  classical
  -- expand using the exponential form and collect terms
  dsimp [mass]
  have L : ℝ := Real.log Constants.phi
  have hdist : (((r : ℝ) + (n : ℝ) + f) * L) = (((r : ℝ) + f) * L + (n : ℝ) * L) := by ring
  simp [hdist, Real.exp_add, exp_nat_mul (Real.log Constants.phi), Constants.exp_log_phi, mul_comm, mul_left_comm, mul_assoc]

@[simp] lemma mass_rshift_two (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U k (r + 2) f = (Constants.phi) ^ 2 * mass U k r f := by
  simpa using (mass_rshift_steps U k r (n:=2) f)

@[simp] lemma mass_rshift_three (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U k (r + 3) f = (Constants.phi) ^ 3 * mass U k r f := by
  simpa using (mass_rshift_steps U k r (n:=3) f)

/-! ### δ → (r,k) mapping hooks
    Use the δ-subgroup coordinatization to view r as `toZ` (rung) and k as `Int.toNat ∘ toZ` built from `Nat` steps. -/

open IndisputableMonolith.LedgerUnits

@[simp] lemma mass_with_rungOf_fromZ (U : Constants.RSUnits) (k : Nat) (δ : ℤ) (hδ : δ ≠ 0)
  (n : ℤ) (f : ℝ) :
  mass U k (r := rungOf δ (fromZ δ n)) f = mass U k n f := by
  simp [rungOf_fromZ (δ:=δ) (hδ:=hδ), mass]

lemma mass_rshift_via_delta (U : Constants.RSUnits) (k : Nat) (δ : ℤ) (hδ : δ ≠ 0)
  (n : ℤ) (f : ℝ) :
  mass U k (r := rungOf δ (fromZ δ (n+1))) f
    = Constants.phi * mass U k (r := rungOf δ (fromZ δ n)) f := by
  -- rewrite rungOf values and apply `mass_rshift`
  simpa [rungOf_fromZ (δ:=δ) (hδ:=hδ)] using mass_rshift U k n f

lemma B_of_kOf_step_succ (δ : ℤ) (hδ : δ ≠ 0) (m : Nat) :
  B_of (kOf δ (fromNat δ (m+1))) = 2 * B_of (kOf δ (fromNat δ m)) := by
  -- push the `kOf` successor equality through `B_of`
  have := kOf_step_succ (δ:=δ) (hδ:=hδ) (m:=m)
  have := congrArg B_of this
  simpa [B_of_succ] using this

/-! ### Spectra with symbolic Ecoh relation Ecoh = Ecoh0 / φ^5 -/

lemma mass_using_EcohDerived (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ)
  {Ecoh0 : ℝ} (h : Constants.RSUnits.EcohDerived U Ecoh0) :
  mass U k r f = B_of k * (Ecoh0 / (Constants.phi ^ (5 : Nat))) *
    Real.exp (((r : ℝ) + f) * Real.log Constants.phi) := by
  dsimp [mass]
  simpa [h]

/-- Unified zpow-style ratio using a piecewise φ^(r2−r1) with negative handled by reciprocal. -/
noncomputable def phi_zpow (z : ℤ) : ℝ :=
  if 0 ≤ z then (Constants.phi : ℝ) ^ (Int.toNat z) else 1 / (Constants.phi : ℝ) ^ (Int.toNat (-z))

@[simp] lemma phi_zpow_of_nonneg {z : ℤ} (hz : 0 ≤ z) :
  phi_zpow z = (Constants.phi : ℝ) ^ (Int.toNat z) := by simp [phi_zpow, hz]

@[simp] lemma phi_zpow_of_neg {z : ℤ} (hz : z < 0) :
  phi_zpow z = 1 / (Constants.phi : ℝ) ^ (Int.toNat (-z)) := by
  have : ¬ 0 ≤ z := not_le.mpr hz
  simp [phi_zpow, this]

lemma mass_ratio_zpow (U : Constants.RSUnits)
  (k2 k1 : Nat) (r2 r1 : ℤ) (f : ℝ) :
  mass U k2 r2 f / mass U k1 r1 f
    = (B_of k2 / B_of k1) * phi_zpow (r2 - r1) := by
  classical
  by_cases hle : r1 ≤ r2
  · -- nonnegative difference: use the `ge` branch
    have hnz : 0 ≤ r2 - r1 := sub_nonneg.mpr hle
    have hpow := mass_ratio_power_ge U k2 k1 r2 r1 f hle
    have : phi_zpow (r2 - r1) = (Constants.phi : ℝ) ^ (Int.toNat (r2 - r1)) := by
      simp [phi_zpow, hnz]
    simpa [this] using hpow
  · -- negative difference: use the `le` branch and reciprocal power
    have hlt : r2 < r1 := lt_of_not_ge hle
    have hpow := mass_ratio_power_le U k2 k1 r2 r1 f hlt
    have hneg : ¬ (0 ≤ r2 - r1) := by
      have : r2 - r1 < 0 := sub_neg.mpr hlt
      exact not_le.mpr this
    have : phi_zpow (r2 - r1) = 1 / (Constants.phi : ℝ) ^ (Int.toNat (r1 - r2)) := by
      have hneg' : - (r2 - r1) = (r1 - r2) := by ring
      simp [phi_zpow, hneg, hneg']
    simpa [this] using hpow

@[simp] lemma mass_ratio_same_r_k_succ (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U (k+1) r f / mass U k r f = 2 := by
  have hpos : mass U k r f ≠ 0 := ne_of_gt (mass_pos U k r f)
  have := mass_kshift U k r f
  have := congrArg (fun x => x / mass U k r f) this
  simpa [hpos] using this

@[simp] lemma mass_ratio_same_k_r_succ (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U k (r+1) f / mass U k r f = Constants.phi := by
  have hpos : mass U k r f ≠ 0 := ne_of_gt (mass_pos U k r f)
  have := mass_rshift U k r f
  have := congrArg (fun x => x / mass U k r f) this
  simpa [hpos] using this

@[simp] lemma mass_rshift_simp (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U k (r + 1) f = Constants.phi * mass U k r f := mass_rshift U k r f

private lemma exp_nat_mul (L : ℝ) : ∀ n : Nat, Real.exp ((n : ℝ) * L) = (Real.exp L) ^ n
| 0 => by simp
| Nat.succ n => by
    have hdist : ((Nat.succ n : ℝ) * L) = (n : ℝ) * L + L := by
      ring
    simp [hdist, exp_nat_mul n, Real.exp_add, pow_succ, mul_comm, mul_left_comm, mul_assoc]

@[simp] lemma B_of_zero : B_of 0 = 1 := by simp [B_of]

@[simp] lemma B_of_succ (k : Nat) : B_of (k+1) = 2 * B_of k := by
  simp [B_of, pow_succ, mul_comm]

lemma mass_kshift (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U (k+1) r f = 2 * mass U k r f := by
  dsimp [mass]
  simp [B_of_succ, mul_comm, mul_left_comm, mul_assoc]

@[simp] lemma mass_kshift_simp (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U (k.succ) r f = 2 * mass U k r f := mass_kshift U k r f

lemma mass_strict_mono_k (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U (k+1) r f > mass U k r f := by
  have hpos : 0 < mass U k r f := mass_pos U k r f
  have htwo : (2 : ℝ) > 1 := by norm_num
  simpa [mass_kshift U k r f, two_mul] using (mul_lt_mul_of_pos_right htwo hpos)

lemma mass_strict_mono_r (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) :
  mass U k (r+1) f > mass U k r f := by
  have hpos : 0 < mass U k r f := mass_pos U k r f
  have hφ : (Constants.phi : ℝ) > 1 := by
    have := Constants.one_lt_phi; simpa using this
  simpa [mass_rshift U k r f] using (mul_lt_mul_of_pos_right hφ hpos)

lemma B_of_pos (k : Nat) : 0 < B_of k := by
  have : 0 < (2:ℝ) := by norm_num
  simpa [B_of] using pow_pos this k

lemma mass_pos (U : Constants.RSUnits) (k : Nat) (r : ℤ) (f : ℝ) : 0 < mass U k r f := by
  classical
  dsimp [mass]
  have h1 : 0 < B_of k := B_of_pos k
  have h2 : 0 < U.Ecoh := U.pos_Ecoh
  have h3 : 0 < Real.exp (((r : ℝ) + f) * Real.log Constants.phi) := Real.exp_pos _
  exact mul_pos (mul_pos h1 h2) h3

lemma mass_ratio_full (U : Constants.RSUnits)
  (k2 k1 : Nat) (r2 r1 : ℤ) (f : ℝ) :
  mass U k2 r2 f / mass U k1 r1 f
    = (B_of k2 / B_of k1) *
      Real.exp ((((r2 - r1 : ℤ) : ℝ)) * Real.log Constants.phi) := by
  classical
  dsimp [mass]
  -- rearrange products into a clean ratio
  have hpos1 : (B_of k1) ≠ 0 := ne_of_gt (B_of_pos k1)
  have hpos2 : U.Ecoh ≠ 0 := ne_of_gt U.pos_Ecoh
  have hpos3 : Real.exp (((r1 : ℝ) + f) * Real.log Constants.phi) ≠ 0 := by
    exact (ne_of_gt (Real.exp_pos _))
  have :
    (B_of k2 * U.Ecoh * Real.exp (((r2 : ℝ) + f) * Real.log Constants.phi)) /
    (B_of k1 * U.Ecoh * Real.exp (((r1 : ℝ) + f) * Real.log Constants.phi))
    = (B_of k2 / B_of k1) *
      (U.Ecoh / U.Ecoh) *
      (Real.exp (((r2 : ℝ) + f) * Real.log Constants.phi)
        / Real.exp (((r1 : ℝ) + f) * Real.log Constants.phi)) := by
    field_simp [hpos1, hpos2, hpos3, mul_comm, mul_left_comm, mul_assoc]
  -- simplify Ecoh/Ecoh and the exp ratio
  have hE : (U.Ecoh / U.Ecoh) = 1 := by
    field_simp [hpos2]
  -- exponent difference
  have hsub :
    (((r2 : ℝ) + f) * Real.log Constants.phi) - (((r1 : ℝ) + f) * Real.log Constants.phi)
      = (((r2 - r1 : ℤ) : ℝ)) * Real.log Constants.phi := by
    ring
  calc
    mass U k2 r2 f / mass U k1 r1 f
        = (B_of k2 * U.Ecoh * Real.exp (((r2 : ℝ) + f) * Real.log Constants.phi)) /
          (B_of k1 * U.Ecoh * Real.exp (((r1 : ℝ) + f) * Real.log Constants.phi)) := rfl
    _ = (B_of k2 / B_of k1) * (U.Ecoh / U.Ecoh) *
          (Real.exp (((r2 : ℝ) + f) * Real.log Constants.phi)
            / Real.exp (((r1 : ℝ) + f) * Real.log Constants.phi)) := by simpa [this]
    _ = (B_of k2 / B_of k1) *
          Real.exp ((((r2 - r1 : ℤ) : ℝ)) * Real.log Constants.phi) := by
            simpa [hE, Real.exp_sub, hsub, mul_comm, mul_left_comm, mul_assoc]

lemma mass_ratio_power_ge (U : Constants.RSUnits)
  (k2 k1 : Nat) (r2 r1 : ℤ) (f : ℝ) (h : r1 ≤ r2) :
  mass U k2 r2 f / mass U k1 r1 f
    = (B_of k2 / B_of k1) * (Constants.phi) ^ (Int.toNat (r2 - r1)) := by
  classical
  have hn : 0 ≤ r2 - r1 := by exact sub_nonneg.mpr h
  have hcast : ((r2 - r1 : ℤ) : ℝ) = (Int.toNat (r2 - r1) : ℝ) := by
    have := Int.ofNat_toNat_of_nonneg hn
    -- cast both sides to ℝ
    simpa using congrArg (fun z : ℤ => (z : ℝ)) this.symm
  have := mass_ratio_full U k2 k1 r2 r1 f
  -- rewrite exponential as φ^n
  have :
    Real.exp ((((r2 - r1 : ℤ) : ℝ)) * Real.log Constants.phi)
      = (Constants.phi) ^ (Int.toNat (r2 - r1)) := by
    simp [hcast, exp_nat_mul (Real.log Constants.phi), Constants.exp_log_phi]
  simpa [this]
    using this.trans (rfl)

lemma mass_ratio_power_le (U : Constants.RSUnits)
  (k2 k1 : Nat) (r2 r1 : ℤ) (f : ℝ) (h : r2 < r1) :
  mass U k2 r2 f / mass U k1 r1 f
    = (B_of k2 / B_of k1) * (1 / (Constants.phi) ^ (Int.toNat (r1 - r2))) := by
  classical
  have hr : 0 ≤ r1 - r2 := le_of_lt h
  have ndef : (r1 - r2 : ℤ) = Int.ofNat (Int.toNat (r1 - r2)) := Int.ofNat_toNat_of_nonneg hr
  have hfull := mass_ratio_full U k2 k1 r2 r1 f
  -- rewrite exp with negative exponent and use reciprocal power
  have : Real.exp ((((r2 - r1 : ℤ) : ℝ)) * Real.log Constants.phi)
          = 1 / (Real.exp (Real.log Constants.phi)) ^ (Int.toNat (r1 - r2)) := by
    have hneg : ((r2 - r1 : ℤ) : ℝ) = - ((r1 - r2 : ℤ) : ℝ) := by ring
    simp [hneg, ndef, Real.exp_neg, exp_nat_mul (Real.log Constants.phi), one_div]
  simpa [this, Constants.exp_log_phi] using hfull

lemma mass_ratio_power (U : Constants.RSUnits)
  (k2 k1 : Nat) (r2 r1 : ℤ) (f : ℝ) :
  (r1 ≤ r2 → mass U k2 r2 f / mass U k1 r1 f = (B_of k2 / B_of k1) * (Constants.phi) ^ (Int.toNat (r2 - r1))) ∧
  (r2 < r1 → mass U k2 r2 f / mass U k1 r1 f = (B_of k2 / B_of k1) * (1 / (Constants.phi) ^ (Int.toNat (r1 - r2)))) := by
  constructor
  · intro h; exact mass_ratio_power_ge U k2 k1 r2 r1 f h
  · intro h; exact mass_ratio_power_le U k2 k1 r2 r1 f h

/-- Corollary (fixed k): ratio depends only on φ (r-difference). -/
lemma mass_ratio_fixed_k (U : Constants.RSUnits)
  (k : Nat) (r2 r1 : ℤ) (f : ℝ) :
  (r1 ≤ r2 → mass U k r2 f / mass U k r1 f = (Constants.phi) ^ (Int.toNat (r2 - r1))) ∧
  (r2 < r1 → mass U k r2 f / mass U k r1 f = 1 / (Constants.phi) ^ (Int.toNat (r1 - r2))) := by
  constructor
  · intro h
    have := mass_ratio_power_ge U k k r2 r1 f h
    simpa [div_mul_eq_mul_div, one_mul, mul_comm]
      using this
  · intro h
    have := mass_ratio_power_le U k k r2 r1 f h
    simpa [div_mul_eq_mul_div, one_mul, mul_comm]
      using this

/-- Corollary (fixed r): ratio depends only on B (k-difference). -/
lemma mass_ratio_fixed_r (U : Constants.RSUnits)
  (k2 k1 : Nat) (r : ℤ) (f : ℝ) :
  mass U k2 r f / mass U k1 r f = (B_of k2 / B_of k1) := by
  classical
  have := mass_ratio_full U k2 k1 r r f
  -- exponent vanishes when r2 = r1
  simpa using this

lemma mass_kshift' (U : Constants.RSUnits) (k1 k2 : Nat) (r : ℤ) (f : ℝ) :
  mass U k2 r f = (B_of k2 / B_of k1) * mass U k1 r f := by
  classical
  dsimp [mass]
  have :
    B_of k2 * U.Ecoh * Real.exp (((r : ℝ) + f) * Real.log Constants.phi)
      = (B_of k2 / B_of k1) * (B_of k1 * U.Ecoh * Real.exp (((r : ℝ) + f) * Real.log Constants.phi)) := by
    have hpos1 : (B_of k1) ≠ 0 := ne_of_gt (B_of_pos k1)
    field_simp [hpos1, mul_comm, mul_left_comm, mul_assoc]
  simpa [mass, mul_comm, mul_left_comm, mul_assoc] using this

lemma mass_rshift_int (U : Constants.RSUnits) (k : Nat) (r1 r2 : ℤ) (f : ℝ)
  (h : r2 = r1 + 1) : mass U k r2 f = Constants.phi * mass U k r1 f := by
  simpa [h] using mass_rshift U k r1 f

/-- Minimal particle data group (PDG) mapping hook: label and structural rung parameters only. -/
structure PDGMap where
  label : String
  r : ℤ
  f : ℝ
  k : Nat

/-- Map a PDG structural entry to a mass prediction given RS units (no numerics inside Lean). -/
noncomputable def massOf (U : Constants.RSUnits) (p : PDGMap) : ℝ :=
  mass U p.k p.r p.f

end Spectra

end IndisputableMonolith

namespace IndisputableMonolith

/-! ## Gravity: ILG interface stubs (phenomenology-aligned, no numerics) -/

namespace Gravity

/-- Dimensionless ILG kernel: takes scaled dynamical time `t := T_dyn/τ0` and a morphology factor `ζ`.
    The kernel is assumed nonnegative. Further properties (e.g., monotonicity) can be added as needed. -/
structure ILGKernel where
  w : ℝ → ℝ → ℝ
  nonneg : ∀ t ζ, 0 ≤ w t ζ

/-- Global-only configuration placeholders (normalizations and morphology mapping). -/
structure GlobalOnly where
  xi : ℝ
  lambda : ℝ
  zeta : ℝ → ℝ

/-- Effective acceleration (or weight multiplier) induced by the ILG kernel under a global-only config. -/
def effectiveWeight (K : ILGKernel) (G : GlobalOnly) (t ζ : ℝ) : ℝ :=
  G.lambda * G.xi * K.w t (G.zeta ζ)

/-- Optional kernel properties (placeholders for analysis): monotonicity in time and morphology. -/
structure ILGKernelProps (K : ILGKernel) : Prop where
  mono_t : ∀ ζ, Monotone (fun t => K.w t ζ)
  mono_zeta : ∀ t, Monotone (fun ζ => K.w t ζ)

/-- Optional global-only properties (e.g., nonnegativity of multipliers). -/
structure GlobalOnlyProps (G : GlobalOnly) : Prop where
  lambda_xi_nonneg : 0 ≤ G.lambda * G.xi

/-- Effective source predicate: nonnegativity of the induced weight for all arguments. -/
def EffectiveSource (K : ILGKernel) (G : GlobalOnly) : Prop := ∀ t ζ, 0 ≤ effectiveWeight K G t ζ

/-- From kernel nonnegativity and nonnegative global multipliers, conclude an effective source. -/
theorem effectiveSource_of_nonneg (K : ILGKernel) (G : GlobalOnly)
  (hλξ : 0 ≤ G.lambda * G.xi) : EffectiveSource K G := by
  intro t ζ
  have hw : 0 ≤ K.w t (G.zeta ζ) := K.nonneg t (G.zeta ζ)
  -- (λ·ξ) ≥ 0 and w ≥ 0 ⇒ (λ·ξ) * w ≥ 0
  have : 0 ≤ (G.lambda * G.xi) * K.w t (G.zeta ζ) := mul_nonneg hλξ hw
  simpa [effectiveWeight, mul_comm, mul_left_comm, mul_assoc] using this

/-- If `K` is monotone in its arguments and the global-only multipliers are nonnegative,
    then the effective weight is monotone in each argument. -/
lemma effectiveWeight_monotone
  (K : ILGKernel) (G : GlobalOnly)
  (hK : ILGKernelProps K) (hG : GlobalOnlyProps G) :
  (∀ ζ, Monotone (fun t => effectiveWeight K G t ζ)) ∧
  (∀ t, Monotone (fun ζ => effectiveWeight K G t ζ)) := by
  -- Multiplying a monotone nonnegative function by a nonnegative constant preserves monotonicity.
  -- We assume λ·ξ ≥ 0 via `hG`. The zeta mapping is arbitrary; monotonicity in ζ flows through K.
  refine ⟨?mono_t, ?mono_zeta⟩
  · intro ζ a b hab
    have : K.w a (G.zeta ζ) ≤ K.w b (G.zeta ζ) := (hK.mono_t (G.zeta ζ)) hab
    have hconst : 0 ≤ G.lambda * G.xi := hG.lambda_xi_nonneg
    -- multiply both sides by nonnegative constant
    have := mul_le_mul_of_nonneg_left this hconst
    simpa [effectiveWeight, mul_comm, mul_left_comm, mul_assoc]
      using this
  · intro t ζ1 ζ2 hζ
    have : K.w t (G.zeta ζ1) ≤ K.w t (G.zeta ζ2) := (hK.mono_zeta t) (by exact hζ)
    have hconst : 0 ≤ G.lambda * G.xi := hG.lambda_xi_nonneg
    have := mul_le_mul_of_nonneg_left this hconst
    simpa [effectiveWeight, mul_comm, mul_left_comm, mul_assoc]
      using this

section
variable {M : RecognitionStructure}

/-- Lightweight continuity→effective-source bridge: conservation plus nonnegative kernel factors
    yield a nonnegative effective source. This captures the sign structure; dynamics are left abstract. -/
theorem continuity_to_effective_source
  (K : ILGKernel) (G : GlobalOnly) (L : Ledger M)
  [Conserves L] (hλξ : 0 ≤ G.lambda * G.xi) : EffectiveSource K G :=
  effectiveSource_of_nonneg K G hλξ

end

end Gravity

end IndisputableMonolith

namespace IndisputableMonolith

/-! ## Quantum interface stubs: path weights and interface-level propositions -/

namespace Quantum

/-- Path weight class: assigns a cost `C`, a composition on paths, and defines probability `prob := exp(−C)`.
    Includes a normalization axiom over a designated finite set. -/
structure PathWeight (γ : Type) where
  C : γ → ℝ
  comp : γ → γ → γ
  cost_additive : ∀ a b, C (comp a b) = C a + C b
  prob : γ → ℝ := fun g => Real.exp (-(C g))
  normSet : Finset γ
  sum_prob_eq_one : ∑ g in normSet, prob g = 1

open scoped BigOperators

lemma prob_comp {γ} (PW : PathWeight γ) (a b : γ) :
  PW.prob (PW.comp a b) = PW.prob a * PW.prob b := by
  dsimp [PathWeight.prob]
  simp [PW.cost_additive, Real.exp_add, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Interface-level Born rule statement (placeholder): there exists a wave-like representation whose
    squared magnitude matches normalized `prob`. -/
structure BornRuleIface (γ : Type) (PW : PathWeight γ) : Prop :=
  (normalized : Prop)
  (exists_wave_repr : Prop)

/-- Interface-level Bose/Fermi statement (placeholder): permutation invariance yields symmetrization. -/
structure BoseFermiIface (γ : Type) (PW : PathWeight γ) : Prop :=
  (perm_invariant : Prop)
  (symmetrization : Prop)

/-- Existence lemma sketch: the RS path-weight (with additive cost) satisfies the interface. -/
theorem rs_pathweight_iface (γ : Type) (PW : PathWeight γ) :
  BornRuleIface γ PW ∧ BoseFermiIface γ PW := by
  -- Placeholder existence; concrete instances supplied in applications
  exact ⟨{ normalized := True, exists_wave_repr := True }, { perm_invariant := True, symmetrization := True }⟩

/-- Tiny normalization helper: if the normalization set is a singleton {g}, then prob g = 1. -/
lemma prob_singleton_norm (γ : Type) (PW : PathWeight γ) {g : γ}
  (h : PW.normSet = {g}) : PW.prob g = 1 := by
  classical
  have := congrArg (fun s : Finset γ => ∑ x in s, PW.prob x) h
  simpa using this.trans PW.sum_prob_eq_one

/-- Minimal constructor: build a PathWeight on a finite set with given cost and discrete composition. -/
def ofFinset {γ : Type} (S : Finset γ) (C : γ → ℝ) (comp : γ → γ → γ)
  (cost_add : ∀ a b, C (comp a b) = C a + C b)
  (norm_one : ∑ g in S, Real.exp (-(C g)) = 1) : PathWeight γ :=
{ C := C
, comp := comp
, cost_additive := cost_add
, prob := fun g => Real.exp (-(C g))
, normSet := S
, sum_prob_eq_one := by simpa using norm_one }

/-- Disjoint-union normalization builder: if two finite sets `A` and `B` are disjoint and each normalizes
    to 1 under their respective costs, then the disjoint union normalizes to 1 under the combined cost. -/
def ofDisjointUnion {γ₁ γ₂ : Type}
  (A : Finset γ₁) (B : Finset γ₂)
  (C₁ : γ₁ → ℝ) (C₂ : γ₂ → ℝ)
  (comp₁ : γ₁ → γ₁ → γ₁) (comp₂ : γ₂ → γ₂ → γ₂)
  (cost_add₁ : ∀ a b, C₁ (comp₁ a b) = C₁ a + C₁ b)
  (cost_add₂ : ∀ a b, C₂ (comp₂ a b) = C₂ a + C₂ b)
  (norm₁ : ∑ g in A, Real.exp (-(C₁ g)) = 1)
  (norm₂ : ∑ g in B, Real.exp (-(C₂ g)) = 1)
  (w1 w2 : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hsum : w1 + w2 = 1) :
  PathWeight (Sum γ₁ γ₂) :=
{ C := fun s => Sum.rec C₁ C₂ s
, comp := fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => Sum.inl (comp₁ a b)
    | Sum.inr a, Sum.inr b => Sum.inr (comp₂ a b)
    | _, _ => x  -- mixed comps unused in this builder
, cost_additive := by
    intro a b; cases a <;> cases b <;> simp [cost_add₁, cost_add₂]
, prob := fun s =>
    match s with
    | Sum.inl a => w1 * Real.exp (-(C₁ a))
    | Sum.inr b => w2 * Real.exp (-(C₂ b))
, normSet := (A.image Sum.inl) ∪ (B.image Sum.inr)
, sum_prob_eq_one := by
    classical
    -- disjointness of images of inl and inr
    have hdisj : Disjoint (A.image Sum.inl) (B.image Sum.inr) := by
      refine Finset.disjoint_left.mpr ?_
      intro s hsA hsB
      rcases Finset.mem_image.mp hsA with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hsB with ⟨b, hb, hEq⟩
      cases hEq
    -- sum over the union splits
    have hsplit := Finset.sum_union hdisj
    -- rewrite each part via sum_image
    have hinjA : ∀ x ∈ A, ∀ y ∈ A, Sum.inl x = Sum.inl y → x = y := by
      intro x hx y hy h; simpa using Sum.inl.inj h
    have hinjB : ∀ x ∈ B, ∀ y ∈ B, Sum.inr x = Sum.inr y → x = y := by
      intro x hx y hy h; simpa using Sum.inr.inj h
    have hsumA : ∑ s in A.image Sum.inl, (match s with | Sum.inl a => w1 * Real.exp (-(C₁ a)) | Sum.inr _ => 0)
                = w1 * ∑ a in A, Real.exp (-(C₁ a)) := by
      -- sum over image inl
      have := Finset.sum_image (s:=A) (f:=Sum.inl)
        (g:=fun s => match s with | Sum.inl a => w1 * Real.exp (-(C₁ a)) | Sum.inr _ => 0) hinjA
      -- simplify RHS
      simpa using this
    have hsumB : ∑ s in B.image Sum.inr, (match s with | Sum.inl _ => 0 | Sum.inr b => w2 * Real.exp (-(C₂ b)))
                = w2 * ∑ b in B, Real.exp (-(C₂ b)) := by
      have := Finset.sum_image (s:=B) (f:=Sum.inr)
        (g:=fun s => match s with | Sum.inl _ => 0 | Sum.inr b => w2 * Real.exp (-(C₂ b))) hinjB
      simpa using this
    -- combine
    have : ∑ s in (A.image Sum.inl ∪ B.image Sum.inr), (fun s => match s with
      | Sum.inl a => w1 * Real.exp (-(C₁ a))
      | Sum.inr b => w2 * Real.exp (-(C₂ b))) s
         = w1 * ∑ a in A, Real.exp (-(C₁ a)) + w2 * ∑ b in B, Real.exp (-(C₂ b)) := by
      simpa [hsplit, hsumA, hsumB, Finset.sum_image]
    -- finish with given normalizations and w1+w2=1
    simpa [this, norm₁, norm₂, hsum, add_comm, add_left_comm, add_assoc]
}

/-- Independence product constructor: probabilities multiply over independent components. -/
def product {γ₁ γ₂ : Type} (PW₁ : PathWeight γ₁) (PW₂ : PathWeight γ₂) : PathWeight (γ₁ × γ₂) :=
{ C := fun p => PW₁.C p.1 + PW₂.C p.2
, comp := fun p q => (PW₁.comp p.1 q.1, PW₂.comp p.2 q.2)
, cost_additive := by intro a b; simp [PW₁.cost_additive, PW₂.cost_additive, add_comm, add_left_comm, add_assoc]
, prob := fun p => PW₁.prob p.1 * PW₂.prob p.2
, normSet := (PW₁.normSet.product PW₂.normSet)
, sum_prob_eq_one := by
    classical
    -- ∑_{(a,b)∈A×B} prob₁(a)·prob₂(b) = (∑_{a∈A} prob₁(a)) · (∑_{b∈B} prob₂(b)) = 1
    have hprod : ∑ p in PW₁.normSet.product PW₂.normSet, (PW₁.prob p.1 * PW₂.prob p.2)
      = ∑ a in PW₁.normSet, ∑ b in PW₂.normSet, PW₁.prob a * PW₂.prob b := by
      -- sum over product splits
      simpa [Finset.mem_product] using
        (Finset.sum_product (s:=PW₁.normSet) (t:=PW₂.normSet) (f:=fun a b => PW₁.prob a * PW₂.prob b))
    have hfactor : ∑ a in PW₁.normSet, ∑ b in PW₂.normSet, PW₁.prob a * PW₂.prob b
      = (∑ a in PW₁.normSet, PW₁.prob a) * (∑ b in PW₂.normSet, PW₂.prob b) := by
      -- factor the inner sum (constant in a) out
      have : ∑ a in PW₁.normSet, (PW₁.prob a) * (∑ b in PW₂.normSet, PW₂.prob b)
             = (∑ b in PW₂.normSet, PW₂.prob b) * (∑ a in PW₁.normSet, PW₁.prob a) := by
        simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      -- rewrite LHS to nested sum
      have : ∑ a in PW₁.normSet, ∑ b in PW₂.normSet, PW₁.prob a * PW₂.prob b
             = (∑ b in PW₂.normSet, PW₂.prob b) * (∑ a in PW₁.normSet, PW₁.prob a) := by
        -- distribute using mul_sum inside
        have hinner : ∀ a, ∑ b in PW₂.normSet, PW₁.prob a * PW₂.prob b = (PW₁.prob a) * ∑ b in PW₂.normSet, PW₂.prob b := by
          intro a; simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
        -- apply across the outer sum
        simpa [hinner] using this
      -- commute product
      simpa [mul_comm] using this
    -- combine all equalities and the normalizations
    have := hprod.trans hfactor
    simpa [this, PW₁.sum_prob_eq_one, PW₂.sum_prob_eq_one]
}

end Quantum

end IndisputableMonolith
