/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PhysicalDeletionGeometry

/-!
# Uniform polynomial bounds for physical deletion constants

The actual slope grid and parent enlargement introduce only a fixed power of the packet
width parameter. The exponent depends on the maximum number of chain edges, never on the
frequency or the number of occupied cubes.
-/

@[expose] public section

noncomputable section

namespace FalconerPacking

/-- The integer enlargement of the finite slope grid has a uniform polynomial bound. -/
theorem physical_slope_grid_enlargement_le {L : ℝ} (hL : 1 ≤ L) (u : ℕ) :
    ((Nat.ceil (4 * L ^ u + 2) + 1 : ℕ) : ℝ) ≤ 8 * L ^ u := by
  have hp : 1 ≤ L ^ u := one_le_pow₀ hL
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 * L ^ u + 2 by positivity)
  push_cast
  linarith

/-- The chosen finite grid contains each tested physical tube at its literal dyadic width. -/
theorem physical_test_width_le_grid {L : ℝ} (hL : 1 ≤ L) (K j : ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    L ^ (4 * K + 20) * ((2 : ℝ) ^ n)⁻¹ / 2 ≤
      L ^ (4 * K + 20) *
        ((2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ m)⁻¹) /
          ((2 : ℕ) ^ (n - m) : ℝ)) := by
  rw [enlarged_dyadic_grid_scale hmn]
  have hp : 1 ≤ L ^ (2 * (j + 1) + 2) := one_le_pow₀ hL
  have hbase : ((2 : ℝ) ^ n)⁻¹ / 2 ≤
      2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n)⁻¹ := by
    nlinarith [show 0 < ((2 : ℝ) ^ n)⁻¹ by positivity]
  have h := mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ L ^ (4 * K + 20) from pow_nonneg (zero_le_one.trans hL) _)
  simpa only [mul_div_assoc] using h

/-- Actual dyadic geometry supplies the angular-width hypothesis of conditional deletion. -/
theorem physical_angular_uncertainty_le
    {L R δ w C D : ℝ} (hL : 1 ≤ L) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (K j s e : ℕ) {m n : ℕ} (hmn : m ≤ n)
    (hw : w ≤ L * (((2 : ℝ) ^ n)⁻¹ / ((2 : ℝ) ^ m)⁻¹))
    (hangle : ((2 : ℝ) ^ min s e)⁻¹ ≤
      ((2 : ℝ) ^ n)⁻¹ / ((2 : ℝ) ^ m)⁻¹) :
    let ρ := ((2 : ℝ) ^ n)⁻¹ / ((2 : ℝ) ^ m)⁻¹
    let Λ := 2 * L ^ (2 * (j + 1) + 2)
    let b := Λ * ((2 : ℝ) ^ m)⁻¹
    let M := (2 : ℕ) ^ (n - m)
    let Z := Nat.ceil (4 * L ^ (4 * K + 20) + 2) + 1
    let ε := 2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s e) * D
    8 * R * (((Z : ℝ) + 1) * (b / M) + 2 * ε + D / M) / δ ^ 2 ≤
      (8 * R / δ ^ 2 *
        (((Z : ℝ) + 1) * Λ + 2 * (2 + C) * L + (4 * Real.pi + 1) * D)) * ρ := by
  dsimp only
  apply enlarged_grid_angular_uncertainty_le hR
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
    (by positivity) (by positivity)
    (by simpa only [Nat.cast_pow] using inv_dyadic_grid_eq_ratio hmn)
  simpa only [div_eq_mul_inv] using physical_pair_uncertainty_le hC hD hw hangle

/-- A single polynomial bounds the angular uncertainty and the complete finite-grid cost.
The two costs include the actual parent enlargement and the grid's integer ceiling. -/
theorem exists_physical_deletion_constants {R δ C D : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hC : 0 ≤ C) (hD : 0 ≤ D) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 2 ≤ L → ∀ j : ℕ, j ≤ K →
      let Λ := 2 * L ^ (2 * (j + 1) + 2)
      let E := L ^ (4 * K + 20)
      let Z := ((Nat.ceil (4 * E + 2) + 1 : ℕ) : ℝ)
      let G := 8 * R / δ ^ 2 *
        ((Z + 1) * Λ + 2 * (2 + C) * L + (4 * Real.pi + 1) * D)
      0 < G ∧ G ≤ c * L ^ (20 * K + 100) ∧
        20 * (2 * Z + 1) ^ 2 * (12 * G) * Λ ≤ c * L ^ (20 * K + 100) ∧
        49 * Λ ^ 2 ≤ c * L ^ (20 * K + 100) := by
  let u := 4 * K + 20
  let v := 2 * K + 4
  let c₀ := 8 * R / δ ^ 2 * (18 + 2 * (2 + C) + (4 * Real.pi + 1) * D)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨max (138720 * c₀) 196, lt_of_lt_of_le (by positivity)
    (le_max_left _ _), fun L hL j hj ↦ ?_⟩
  dsimp only
  let Λ := 2 * L ^ (2 * (j + 1) + 2)
  let Z := ((Nat.ceil (4 * L ^ u + 2) + 1 : ℕ) : ℝ)
  let G := 8 * R / δ ^ 2 *
    ((Z + 1) * Λ + 2 * (2 + C) * L + (4 * Real.pi + 1) * D)
  change 0 < G ∧ G ≤ _ ∧ 20 * (2 * Z + 1) ^ 2 * (12 * G) * Λ ≤ _ ∧ 49 * Λ ^ 2 ≤ _
  have hL₁ : 1 ≤ L := by linarith
  have hL₀ : 0 < L := by linarith
  have hu : 1 ≤ L ^ u := one_le_pow₀ hL₁
  have hv : 1 ≤ L ^ v := one_le_pow₀ hL₁
  have hΛ : Λ ≤ 2 * L ^ v := by
    dsimp [Λ]
    gcongr
    dsimp [v]
    omega
  have hΛ₀ : 0 < Λ := by dsimp [Λ]; positivity
  have hZ : Z ≤ 8 * L ^ u := physical_slope_grid_enlargement_le hL₁ u
  have hZ₀ : 0 ≤ Z := by dsimp [Z]; positivity
  have hZ₁ : Z + 1 ≤ 9 * L ^ u := by linarith
  have hZ₂ : 2 * Z + 1 ≤ 17 * L ^ u := by linarith
  have hG₀ : 0 < G := by dsimp [G]; positivity
  have hprod : (Z + 1) * Λ ≤ 18 * L ^ (u + v) := by
    calc
      _ ≤ (9 * L ^ u) * (2 * L ^ v) :=
        mul_le_mul hZ₁ hΛ hΛ₀.le (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hLuv : L ≤ L ^ (u + v) := by
    calc
      L = L ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hL₁ (by dsimp [u, v]; omega)
  have h1uv : 1 ≤ L ^ (u + v) := one_le_pow₀ hL₁
  have hG : G ≤ c₀ * L ^ (u + v) := by
    have hterm₁ := mul_le_mul_of_nonneg_left hLuv (show 0 ≤ 2 * (2 + C) by positivity)
    have hterm₂ := mul_le_mul_of_nonneg_left h1uv
      (show 0 ≤ (4 * Real.pi + 1) * D by positivity)
    dsimp [G, c₀]
    apply (mul_le_mul_of_nonneg_left (show
      (Z + 1) * Λ + 2 * (2 + C) * L + (4 * Real.pi + 1) * D ≤
        (18 + 2 * (2 + C) + (4 * Real.pi + 1) * D) * L ^ (u + v) by
          nlinarith) (by positivity : 0 ≤ 8 * R / δ ^ 2)).trans_eq
    ring
  have hp₁ : L ^ (u + v) ≤ L ^ (20 * K + 100) :=
    pow_le_pow_right₀ hL₁ (by dsimp [u, v]; omega)
  have hp₂ : L ^ (3 * u + 2 * v) ≤ L ^ (20 * K + 100) :=
    pow_le_pow_right₀ hL₁ (by dsimp [u, v]; omega)
  have hp₃ : L ^ (2 * v) ≤ L ^ (20 * K + 100) :=
    pow_le_pow_right₀ hL₁ (by dsimp [u, v]; omega)
  have hc : c₀ ≤ max (138720 * c₀) 196 :=
    (show c₀ ≤ 138720 * c₀ by linarith).trans (le_max_left _ _)
  refine ⟨hG₀, hG.trans (mul_le_mul hc hp₁ (by positivity) (by positivity)), ?_, ?_⟩
  · calc
      _ ≤ 20 * (17 * L ^ u) ^ 2 * (12 * (c₀ * L ^ (u + v))) * (2 * L ^ v) := by
        gcongr
      _ = 138720 * c₀ * L ^ (3 * u + 2 * v) := by
        simp only [pow_add, pow_mul, mul_pow]
        ring
      _ ≤ max (138720 * c₀) 196 * L ^ (20 * K + 100) :=
        mul_le_mul (le_max_left _ _) hp₂ (by positivity) (by positivity)
  · calc
      _ ≤ 49 * (2 * L ^ v) ^ 2 := by gcongr
      _ = 196 * L ^ (2 * v) := by rw [Nat.mul_comm 2 v, pow_mul]; ring
      _ ≤ max (138720 * c₀) 196 * L ^ (20 * K + 100) :=
        mul_le_mul (le_max_right _ _) hp₃ (by positivity) (by positivity)

end FalconerPacking
