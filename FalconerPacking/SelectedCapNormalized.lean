/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SelectedCapGridEmbedding
import FalconerPacking.SelectedCapCoefficients

/-!
# The normalized selected-cap scale bound

The exact geometric coefficients simplify to a polynomial main term and an arbitrarily
small inverse-power tail. The finite overlap and every averaging area remain explicit.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Classical
open scoped ENNReal

namespace FalconerPacking

/-- The main inflation coefficient, with values in the extended nonnegative reals. -/
theorem selected_cap_main_coefficient_ennreal {a b L : ℝ} {Λ : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (j : ℕ)
    (hΛ : (Λ : ℝ) ≤ 49 * L ^ (4 * j + 4)) :
    (ENNReal.ofReal (L ^ (2 * j + 2) * a) ^ 2)⁻¹ *
        ENNReal.ofReal ((a * b)⁻¹) *
        (ENNReal.ofReal (L * (L ^ (2 * j + 2) * a)) ^ 2 *
          ENNReal.ofReal Real.pi) * Λ * ENNReal.ofReal (a / b) *
        ENNReal.ofReal (L ^ (2 * j + 4) * b) ^ 2 ≤
      ENNReal.ofReal (49 * Real.pi * L ^ (8 * j + 14)) := by
  have h := ENNReal.ofReal_le_ofReal (selected_cap_main_coefficient_le ha hb hL j hΛ)
  simpa (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_natCast,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The kernel tail, including the inverse child area. -/
theorem selected_cap_kernel_tail_ennreal {a b L : ℝ} {Λ : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hL : 1 ≤ L)
    (j K p n : ℕ) (hj : j < K) (hn : p + 4 * K + 20 ≤ n)
    (hΛ : (Λ : ℝ) ≤ 49 * L ^ (4 * j + 4)) :
    (ENNReal.ofReal (L ^ (2 * j + 2) * a) ^ 2)⁻¹ *
        ENNReal.ofReal ((a * b)⁻¹) *
        (ENNReal.ofReal (L * (L ^ (2 * j + 2) * a)) ^ 2 *
          ENNReal.ofReal Real.pi) * Λ / ENNReal.ofReal ((1 + L / 2) ^ n) ≤
      ENNReal.ofReal (49 * Real.pi * 2 ^ n * (a ^ 2)⁻¹ * (L ^ p)⁻¹) := by
  have hb := ha.trans_le hab
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have h := ENNReal.ofReal_le_ofReal
    (selected_cap_kernel_tail_le ha hab hL j K p n hj hn hΛ)
  simpa (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_natCast,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The localization tail has the same arbitrary inverse-power decay. -/
theorem selected_cap_local_tail_ennreal {a L : ℝ} {Λ : ℕ}
    (ha : 0 < a) (hL : 1 ≤ L) (j p n : ℕ) (hp : p ≤ 2 * n)
    (hΛ : (Λ : ℝ) ≤ 49 * L ^ (4 * j + 4)) :
    (ENNReal.ofReal (L ^ (2 * j + 2) * a) ^ 2)⁻¹ * Λ /
        ENNReal.ofReal ((1 + L) ^ (2 * n)) ≤
      ENNReal.ofReal (49 * (a ^ 2)⁻¹ * (L ^ p)⁻¹) := by
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have h := ENNReal.ofReal_le_ofReal (selected_cap_local_tail_le ha hL j p n hp hΛ)
  simpa (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_natCast] using h

/-- The three geometric estimates combine without requiring finiteness of the energies. -/
theorem selected_cap_normalized_coefficient_bound
    {a b L C₁ C₂ C₃ k S : ℝ} {Λ : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hL : 1 ≤ L)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hk : 0 ≤ k) (hS : 0 ≤ S) (j K p n : ℕ) (hj : j < K)
    (hn : p + 4 * K + 20 ≤ n)
    (hΛ : (Λ : ℝ) ≤ 49 * L ^ (4 * j + 4))
    (B : ℕ) (H M X Y : ℝ≥0∞) :
    let s := L ^ (2 * j + 2) * a
    let W := ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi
    let mainCoeff := ENNReal.ofReal k *
      (ENNReal.ofReal ((a * b)⁻¹) * 81 * ENNReal.ofReal S *
        (W * (Λ * (H * ENNReal.ofReal (a / b) * M))))
    let tailCoeff := ENNReal.ofReal k *
      (ENNReal.ofReal ((a * b)⁻¹ * C₃ / (1 + L / 2) ^ n) * (W * (Λ * M)))
    (ENNReal.ofReal s ^ 2)⁻¹ * (9 * B : ℝ≥0∞) *
        (ENNReal.ofReal (C₁ ^ 2) *
            (mainCoeff * (ENNReal.ofReal (L ^ (2 * j + 4) * b) ^ 2 * X) +
              tailCoeff * Y) +
          ENNReal.ofReal ((C₂ / (1 + L) ^ n) ^ 2) * (Λ * M) * Y) ≤
      ENNReal.ofReal (9 * C₁ ^ 2 * k * 81 * S * 49 * Real.pi) * B *
          ENNReal.ofReal (L ^ (8 * j + 14)) * H * M * X +
        ENNReal.ofReal (9 * (C₁ ^ 2 * k * C₃ * 49 * Real.pi * 2 ^ n + C₂ ^ 2 * 49)) *
          B * ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ p)⁻¹) * M * Y := by
  have hb := ha.trans_le hab
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hm := selected_cap_main_coefficient_ennreal ha hb hL₀ j hΛ
  have ht := selected_cap_kernel_tail_ennreal ha hab hL j K p n hj hn hΛ
  have hl := selected_cap_local_tail_ennreal ha hL j p n (by omega) hΛ
  dsimp only
  have hsum := add_le_add (add_le_add
    (mul_le_mul_right hm
      ((9 * B : ℝ≥0∞) * ENNReal.ofReal (C₁ ^ 2) * ENNReal.ofReal k * 81 *
        ENNReal.ofReal S * H * M * X))
    (mul_le_mul_right ht
      ((9 * B : ℝ≥0∞) * ENNReal.ofReal (C₁ ^ 2) * ENNReal.ofReal k *
        ENNReal.ofReal C₃ * M * Y)))
    (mul_le_mul_right hl
      ((9 * B : ℝ≥0∞) * ENNReal.ofReal (C₂ ^ 2) * M * Y))
  convert hsum using 1 <;> first | rfl | skip
  all_goals
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_add, div_eq_mul_inv, mul_pow, pow_mul,
      ENNReal.inv_pow]
    norm_num
    ring

/-- A fixed overlap constant for the prescribed enlarged grid squares. -/
theorem selected_cap_grid_overlap_constant_le {L : ℝ} (hL : 1 ≤ L) (j : ℕ) :
    (((2 * ⌈L ^ (2 * j + 2)⌉₊ + 3) ^ 2 : ℕ) : ℝ) ≤ 49 * L ^ (4 * j + 4) := by
  have ht : 1 ≤ L ^ (2 * j + 2) := one_le_pow₀ hL
  have hceil := Nat.ceil_lt_add_one (le_trans (by norm_num) ht)
  have hbase : 0 ≤ 2 * (⌈L ^ (2 * j + 2)⌉₊ : ℝ) + 3 := by positivity
  have hu : 2 * (⌈L ^ (2 * j + 2)⌉₊ : ℝ) + 3 ≤ 7 * L ^ (2 * j + 2) := by linarith
  have hsq := (sq_le_sq₀ hbase (by positivity : 0 ≤ 7 * L ^ (2 * j + 2))).mpr hu
  push_cast
  calc
    _ ≤ (7 * L ^ (2 * j + 2)) ^ 2 := hsq
    _ = _ := by simp only [pow_add, pow_mul]; ring

/-- The concrete normalized embedding has polynomial inflation and an arbitrary tail order.
The constant depends only on the number of levels and the requested tail order. -/
theorem selected_cap_normalized_grid_embedding (pwr K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {κ : Type*} (I : Finset (Fin 2 → ℤ)) (J : Finset κ)
        (selection : (Fin 2 → ℤ) → Finset κ), (∀ i ∈ I, selection i ⊆ J) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (O V : κ → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (p : EuclideanSpace ℝ (Fin 2)) (a b L C₀ : ℝ) (j : ℕ),
        0 < a → a ≤ b → 8 ≤ L → 0 ≤ C₀ → 2 * (5 + 7 * C₀) ≤ L → j < K →
      ∀ (B : ℕ) (H : ℝ≥0∞)
        (ξ : κ → EuclideanSpace ℝ (Fin 2))
        (f : κ → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
        (∀ θ ∈ J, ∀ y i, |(V θ y) i - (O θ y) i| ≤ C₀ * (a / b) * ‖y‖) →
        (∀ k ∈ I, ∀ i, |(gridSquareCenter a k) i - p i| ≤ b / 2) →
        let E := enlargedGridSquare a (L ^ (2 * j + 2))
        let P := frameRectangle (LinearIsometryEquiv.refl ℝ _) p
          (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)
        (∀ i ∈ I, ∀ θ ∈ selection i,
          σ (frameRectangle (V θ) (gridSquareCenter a i)
            (L ^ (4 * K + 20) * a / 2) (L ^ (4 * K + 20) * b / 2) ∩ P) ≤
              H * ENNReal.ofReal (a / b) * σ P) →
        (∀ θ ∈ J, Function.support (fun z ↦ 𝓕 (f θ) z) ⊆ ball (ξ θ) a⁻¹) →
        (∀ z, (J.filter (fun θ ↦ z ∈ ball (ξ θ) a⁻¹)).card ≤ B) →
        (∀ θ ∈ J, ∀ z ∈ Function.support
          (𝓕 (f θ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
          |(O θ (z - ξ θ)) 0| ≤ a⁻¹ ∧ |(O θ (z - ξ θ)) 1| ≤ b⁻¹) →
        (∑ i ∈ I, σ (E i) *
          ∫⁻ x, ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2
            ∂((volume (E i))⁻¹ • volume.restrict (E i))) ≤
          ENNReal.ofReal C * B *
            (ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P *
                (∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2
                  ∂((volume P)⁻¹ • volume.restrict P)) +
              ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P *
                ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
  let n := pwr + 4 * K + 20
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, he⟩ := selected_cap_grid_embedding n
  let k := ∫ x, ‖unitReproducingKernel x‖
  let S := SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
    SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel
  have hk : 0 ≤ k := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hS : 0 ≤ S := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  let Cm := 9 * C₁ ^ 2 * k * 81 * S * 49 * Real.pi
  let Ct := 9 * (C₁ ^ 2 * k * C₃ * 49 * Real.pi * 2 ^ n + C₂ ^ 2 * 49)
  let C := 1 + Cm + Ct
  have hm : 0 ≤ Cm := by dsimp [Cm]; positivity
  have ht : 0 ≤ Ct := by dsimp [Ct]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hmC : ENNReal.ofReal Cm ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  have htC : ENNReal.ofReal Ct ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro κ I J selection hselection σ hσ O V p a b L C₀ j
    ha hab hL hC₀ hsize hj B H ξ f hframe hcenters
  dsimp only
  intro htest hballs hB hrect
  let E := enlargedGridSquare a (L ^ (2 * j + 2))
  let P := frameRectangle (LinearIsometryEquiv.refl ℝ _) p
    (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)
  let X := ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2 ∂((volume P)⁻¹ • volume.restrict P)
  let Y := ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2
  have h := he I J selection hselection σ O V p a b L C₀ j K
    ha hab hL hC₀ hsize hj B H ξ f hframe hcenters htest hballs hB hrect
  have hkernel : ENNReal.ofReal k = ∫⁻ x, ‖unitReproducingKernel x‖ₑ :=
    ofReal_integral_norm_eq_lintegral_enorm unitReproducingKernel.integrable
  dsimp only at h
  rw [← hkernel] at h
  have hc := selected_cap_normalized_coefficient_bound ha hab (by linarith : 1 ≤ L)
    hC₁.le hC₂.le hC₃.le hk hS j K pwr n hj le_rfl
    (selected_cap_grid_overlap_constant_le (by linarith) j) B H (σ P) X Y
  apply h.trans (hc.trans ?_)
  change ENNReal.ofReal Cm * B * ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P * X +
      ENNReal.ofReal Ct * B * ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P * Y ≤ _
  calc
    _ ≤ ENNReal.ofReal C * B * ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P * X +
        ENNReal.ofReal C * B * ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P * Y := by
      gcongr
    _ = _ := by ring

end FalconerPacking
