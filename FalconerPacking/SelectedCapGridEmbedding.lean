/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SelectedCapEmbedding

/-!
# Normalized square averages in the selected-cap estimate

The geometric squares have their actual Lebesgue areas. Their normalized averages are
therefore related to the localized ball estimate by exact measure identities.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Classical
open scoped ENNReal

namespace FalconerPacking

/-- The area of a coordinate square of side s is exactly s squared. -/
theorem volume_coordinateSquare (q : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    volume (frameRectangle (LinearIsometryEquiv.refl ℝ _) q (s / 2) (s / 2)) =
      ENNReal.ofReal s ^ 2 := by
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    (measurableSet_frameRectangle _ _ _ _).nullMeasurableSet]
  have he : WithLp.toLp 2 ⁻¹'
      frameRectangle (LinearIsometryEquiv.refl ℝ _) q (s / 2) (s / 2) =
      Set.pi univ (fun i : Fin 2 ↦ closedBall (q i) (s / 2)) := by
    ext x
    simp [frameRectangle, Fin.forall_fin_two, mem_closedBall, Real.dist_eq]
  rw [he, volume_pi_pi]
  simp only [Real.volume_closedBall, show 2 * (s / 2) = s by ring,
    Fin.prod_univ_two, pow_two]

/-- Every positive-side coordinate square is contained in the open ball of its side length. -/
theorem coordinateSquare_subset_ball (q : EuclideanSpace ℝ (Fin 2)) {s : ℝ} (hs : 0 < s) :
    frameRectangle (LinearIsometryEquiv.refl ℝ _) q (s / 2) (s / 2) ⊆ ball q s := by
  intro x hx
  have h₀ : |(x - q) 0| ≤ s / 2 := hx.1
  have h₁ : |(x - q) 1| ≤ s / 2 := hx.2
  have hnorm := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 ↦ ℝ) (x - q)
  simp only [Fin.sum_univ_two, Real.norm_eq_abs] at hnorm
  have hs₀ := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h₀
  have hs₁ := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h₁
  rw [mem_ball, dist_eq_norm]
  nlinarith [norm_nonneg (x - q)]

/-- Normalized square integrals have their exact area factor and are bounded by the
corresponding localized ball integral. -/
theorem normalized_coordinateSquare_lintegral_le_ball
    (q : EuclideanSpace ℝ (Fin 2)) {s : ℝ} (hs : 0 < s)
    (F : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    (∫⁻ x, F x ∂((volume
      (frameRectangle (LinearIsometryEquiv.refl ℝ _) q (s / 2) (s / 2)))⁻¹ •
        volume.restrict (frameRectangle (LinearIsometryEquiv.refl ℝ _) q (s / 2) (s / 2)))) ≤
      (ENNReal.ofReal s ^ 2)⁻¹ * ∫⁻ x in ball q s, F x := by
  rw [volume_coordinateSquare, lintegral_smul_measure, smul_eq_mul]
  gcongr
  exact coordinateSquare_subset_ball q hs

/-- Multiplying a normalized square average by its actual area restores the integral. -/
theorem lintegral_coordinateSquare_eq_area_mul_average
    (q : EuclideanSpace ℝ (Fin 2)) {s : ℝ} (hs : 0 < s)
    (F : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    (∫⁻ x in frameRectangle (LinearIsometryEquiv.refl ℝ _) q (s / 2) (s / 2), F x) =
      ENNReal.ofReal s ^ 2 *
        (∫⁻ x, F x ∂((volume
          (frameRectangle (LinearIsometryEquiv.refl ℝ _) q (s / 2) (s / 2)))⁻¹ •
          volume.restrict
            (frameRectangle (LinearIsometryEquiv.refl ℝ _) q (s / 2) (s / 2)))) := by
  rw [volume_coordinateSquare, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

/-- Concrete grid geometry and exact square normalization in the selected-cap estimate.
The displayed coefficients retain the powers and area factors for subsequent scalar estimates. -/
theorem selected_cap_grid_embedding (m : ℕ) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ {κ : Type*} (I : Finset (Fin 2 → ℤ)) (J : Finset κ)
        (selection : (Fin 2 → ℤ) → Finset κ), (∀ i ∈ I, selection i ⊆ J) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (O V : κ → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (p : EuclideanSpace ℝ (Fin 2)) (a b L C₀ : ℝ) (j K : ℕ),
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
        let s := L ^ (2 * j + 2) * a
        let Λ : ℕ := (2 * ⌈L ^ (2 * j + 2)⌉₊ + 3) ^ 2
        let W := ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi
        let K₀ := ∫⁻ x, ‖unitReproducingKernel x‖ₑ
        let mainCoeff := K₀ * (ENNReal.ofReal ((a * b)⁻¹) * 81 *
          ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
            SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) *
          (W * (Λ * (H * ENNReal.ofReal (a / b) * σ P))))
        let tailCoeff := K₀ * (ENNReal.ofReal ((a * b)⁻¹ * C₃ / (1 + L / 2) ^ m) *
          (W * (Λ * σ P)))
        (∑ i ∈ I, σ (E i) *
          ∫⁻ x, ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2
            ∂((volume (E i))⁻¹ • volume.restrict (E i))) ≤
          (ENNReal.ofReal s ^ 2)⁻¹ * (9 * B : ℝ≥0∞) *
            (ENNReal.ofReal (C₁ ^ 2) *
                (mainCoeff * (ENNReal.ofReal (L ^ (2 * j + 4) * b) ^ 2 *
                    ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2
                      ∂((volume P)⁻¹ • volume.restrict P)) +
                  tailCoeff * ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2) +
              ENNReal.ofReal ((C₂ / (1 + L) ^ m) ^ 2) *
                (Λ * σ P) * ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, he⟩ := selected_cap_embedding m
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro κ I J selection hselection σ hσ O V p a b L C₀ j K
    ha hab hL hC₀ hsize hj B H ξ f hframe hcenters
  dsimp only
  intro htest hballs hB hrect
  let s := L ^ (2 * j + 2) * a
  let t := L ^ (2 * j + 3)
  let E := enlargedGridSquare a (L ^ (2 * j + 2))
  let P := frameRectangle (LinearIsometryEquiv.refl ℝ _) p
    (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)
  let Λ : ℕ := (2 * ⌈L ^ (2 * j + 2)⌉₊ + 3) ^ 2
  have hL₀ : 0 < L := by linarith
  have hL₁ : 1 ≤ L := by linarith
  have hs : 0 < s := mul_pos (pow_pos hL₀ _) ha
  have ht : 1 ≤ t := one_le_pow₀ hL₁
  have hs_t : L * s = t * a := by
    dsimp [s, t]
    rw [show 2 * j + 3 = (2 * j + 2) + 1 by omega, pow_succ L (2 * j + 2)]
    ring
  have hs_inv : s⁻¹ ≤ a⁻¹ := by
    apply (inv_le_inv₀ hs ha).mpr
    dsimp [s]
    nlinarith [one_le_pow₀ hL₁ (n := 2 * j + 2)]
  have hpowers : L ^ (2 * j + 2) ≤ t := pow_le_pow_right₀ hL₁ (by omega)
  have hsub (k) (hk : k ∈ I) : E k ⊆ P := by
    apply Set.Subset.trans _ (enlargedGridSquare_subset_parent ha hab (by linarith) j
      (hcenters k hk))
    intro x hx
    apply (mem_enlargedGridSquare_iff a t k x).mpr
    intro i
    exact ((mem_enlargedGridSquare_iff a _ k x).mp hx i).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hpowers ha.le])
  have hEball (k) (_hk : k ∈ I) (x) (hx : x ∈ E k) :
      ‖x - gridSquareCenter a k‖ ≤ t * a :=
    (norm_sub_gridSquareCenter_le hx).trans (mul_le_mul_of_nonneg_right hpowers ha.le)
  have hmargin (k) (hk : k ∈ I) (x) (hx : x ∈ ball (gridSquareCenter a k) (L * s))
      (y) (hy : y ∉ P) : 2 * b * (L / 2) ≤ dist x y := by
    have hxcoord (i : Fin 2) : |x i - (gridSquareCenter a k) i| ≤ (2 * t) * a / 2 := by
      have hnorm := PiLp.norm_apply_le (x - gridSquareCenter a k) i
      change |x i - (gridSquareCenter a k) i| ≤ ‖x - gridSquareCenter a k‖ at hnorm
      have hdist : ‖x - gridSquareCenter a k‖ < L * s := by
        simpa only [mem_ball, dist_eq_norm] using hx
      rw [hs_t] at hdist
      nlinarith
    have hh := dist_le_margin_of_square_enlargement ha.le hab (by positivity : 0 ≤ 2 * t)
      (embedding_ball_parent_margin_powers hL j) (hcenters k hk) hxcoord hy
    nlinarith
  have hD : (5 + 7 * C₀) * t ≤ L ^ (4 * K + 20) / 2 := by
    have hd := embedding_tested_tube_size hL₁ hsize j K hj
    dsimp [t]
    nlinarith
  have h := he I J selection hselection σ E (gridSquareCenter a) O V P
    a b t C₀ (L ^ (4 * K + 20) / 2) a⁻¹ s L (L / 2)
    ha hab ht hC₀ hD (inv_pos.mpr ha) hs hs_inv hL₀ (by positivity) hs_t.le
    Λ B (H * ENNReal.ofReal (a / b) * σ P) ξ f hframe
    (fun i _ ↦ measurableSet_enlargedGridSquare _ _ _) (measurableSet_frameRectangle _ _ _ _)
    hsub (fun x ↦ card_enlargedGridSquare_overlap_le ha I x) hEball
    (by simpa only [div_mul_eq_mul_div] using htest) hmargin hballs hB hrect
  have hparent : ∀ θ, (∫⁻ x in P, ‖f θ x‖ₑ ^ 2) =
      ENNReal.ofReal (L ^ (2 * j + 4) * b) ^ 2 *
        ∫⁻ x, ‖f θ x‖ₑ ^ 2 ∂((volume P)⁻¹ • volume.restrict P) := by
    intro θ
    exact lintegral_coordinateSquare_eq_area_mul_average p
      (mul_pos (pow_pos hL₀ _) (ha.trans_le hab)) _
  simp_rw [hparent] at h
  rw [← Finset.mul_sum] at h
  have hnorm : (∑ i ∈ I, σ (E i) *
      ∫⁻ x, ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2
            ∂((volume (E i))⁻¹ • volume.restrict (E i))) ≤
      (ENNReal.ofReal s ^ 2)⁻¹ *
        ∑ i ∈ I, σ (E i) * ∫⁻ x in ball (gridSquareCenter a i) s,
          ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hn := normalized_coordinateSquare_lintegral_le_ball (gridSquareCenter a i) hs
      (fun x ↦ ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2)
    have hh := mul_le_mul_right hn (σ (E i))
    simpa only [E, enlargedGridSquare, s, mul_assoc, mul_left_comm, mul_comm] using hh
  apply hnorm.trans
  simpa only [mul_assoc] using mul_le_mul_right h ((ENNReal.ofReal s ^ 2)⁻¹)

end FalconerPacking
