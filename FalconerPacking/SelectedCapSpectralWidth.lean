/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SelectedCapNormalized

/-!
# Fixed spectral enlargement in the selected-cap estimate

Only the reproducing kernel is rescaled. The physical squares, selected tube tests,
and source measure keep their original scales.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Classical
open scoped ENNReal

namespace FalconerPacking

/-- A fixed Fourier-width enlargement changes only the uniform constants. -/
theorem selected_cap_embedding_spectral_width (F : ℝ) (hF : 1 ≤ F) (m : ℕ) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ {ι κ : Type*} (I : Finset ι) (J : Finset κ) (selection : ι → Finset κ),
        (∀ i ∈ I, selection i ⊆ J) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
        (q : ι → EuclideanSpace ℝ (Fin 2))
        (O V : κ → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (P : Set (EuclideanSpace ℝ (Fin 2)))
        (a b t C₀ D r s L R : ℝ), 0 < a → a ≤ b →
        1 ≤ t → 0 ≤ C₀ → (5 + 7 * C₀) * t ≤ D → 0 < r → 0 < s →
        s⁻¹ ≤ r → 0 < L → 0 ≤ R → L * s ≤ t * a →
      ∀ (Λ B : ℕ) (A : ℝ≥0∞)
        (ξ : κ → EuclideanSpace ℝ (Fin 2))
        (f : κ → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
        (∀ θ ∈ J, ∀ y i, |(V θ y) i - (O θ y) i| ≤ C₀ * (a / b) * ‖y‖) →
        (∀ i ∈ I, MeasurableSet (E i)) → MeasurableSet P →
        (∀ i ∈ I, E i ⊆ P) →
        (∀ x, (I.filter fun i ↦ x ∈ E i).card ≤ Λ) →
        (∀ i ∈ I, ∀ x ∈ E i, ‖x - q i‖ ≤ t * a) →
        (∀ i ∈ I, ∀ θ ∈ selection i,
          σ (frameRectangle (V θ) (q i) (D * a) (D * b) ∩ P) ≤ A) →
        (∀ i ∈ I, ∀ x ∈ ball (q i) (L * s), ∀ y ∉ P, 2 * b * R ≤ dist x y) →
        (∀ θ ∈ J, Function.support (fun z ↦ 𝓕 (f θ) z) ⊆ ball (ξ θ) r) →
        (∀ z, (J.filter (fun θ ↦ z ∈ ball (ξ θ) r)).card ≤ B) →
        (∀ θ ∈ J, ∀ z ∈ Function.support
          (𝓕 (f θ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
          |(O θ (z - ξ θ)) 0| ≤ F / a ∧ |(O θ (z - ξ θ)) 1| ≤ F / b) →
        let W := ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi
        let K := ∫⁻ x, ‖unitReproducingKernel x‖ₑ
        let mainCoeff := K * (ENNReal.ofReal ((a * b)⁻¹) * 81 *
          ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
            SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) * (W * (Λ * A)))
        let tailCoeff := K * (ENNReal.ofReal ((a * b)⁻¹ * C₃ / (1 + R) ^ m) *
          (W * (Λ * σ P)))
        (∑ i ∈ I, σ (E i) * ∫⁻ x in ball (q i) s,
          ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2) ≤
          (9 * B : ℝ≥0∞) *
            (ENNReal.ofReal (C₁ ^ 2) *
                (mainCoeff * (∑ θ ∈ J, ∫⁻ x in P, ‖f θ x‖ₑ ^ 2) +
                  tailCoeff * ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2) +
              ENNReal.ofReal ((C₂ / (1 + L) ^ m) ^ 2) *
                (Λ * σ P) * ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, he⟩ := selected_cap_embedding m
  have hF₀ : 0 < F := lt_of_lt_of_le zero_lt_one hF
  refine ⟨F * C₁, F * C₂, C₃, mul_pos hF₀ hC₁, mul_pos hF₀ hC₂, hC₃, ?_⟩
  intro ι κ I J selection hselection σ hσ E q O V P a b t C₀ D r s L R
    ha hab ht hC₀ hD hr hs hsr hL hR hsize Λ B A ξ f
    hframe hE hP hsub hover hEball htest hmargin hballs hB hrect
  have hb := ha.trans_le hab
  have hta : F * t * (a / F) = t * a := by field_simp
  have hDa : F * D * (a / F) = D * a := by field_simp
  have hDb : F * D * (b / F) = D * b := by field_simp
  have hratio : a / F / (b / F) = a / b := by field_simp
  have hrad : 2 * (b / F) * (F * R) = 2 * b * R := by field_simp
  have hia : (a / F)⁻¹ = F / a := by field_simp
  have hib : (b / F)⁻¹ = F / b := by field_simp
  have h := he I J selection hselection σ E q O V P
    (a / F) (b / F) (F * t) C₀ (F * D) r s L (F * R)
    (div_pos ha hF₀) (div_le_div_of_nonneg_right hab hF₀.le)
    (one_le_mul_of_one_le_of_one_le hF ht) hC₀
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hD hF₀.le) hr hs hsr hL (mul_nonneg hF₀.le hR)
    (by simpa only [hta] using hsize) Λ B A ξ f
    (by simpa only [hratio] using hframe) hE hP hsub hover
    (by simpa only [hta] using hEball)
    (by simpa only [hDa, hDb] using htest)
    (by simpa only [hrad] using hmargin) hballs hB
    (by simpa only [hia, hib] using hrect)
  have hdet : ((a / F) * (b / F))⁻¹ = F ^ 2 * (a * b)⁻¹ := by field_simp
  have htail : ((a / F) * (b / F))⁻¹ * C₃ / (1 + F * R) ^ m ≤
      F ^ 2 * ((a * b)⁻¹ * C₃ / (1 + R) ^ m) := by
    rw [hdet]
    calc
      _ ≤ (F ^ 2 * (a * b)⁻¹) * C₃ / (1 + R) ^ m := by
        gcongr
        nlinarith [mul_nonneg (sub_nonneg.mpr hF) hR]
      _ = _ := by ring
  have hlocal : (C₂ / (1 + L) ^ m) ^ 2 ≤ ((F * C₂) / (1 + L) ^ m) ^ 2 := by
    gcongr
    nlinarith [mul_nonneg (sub_nonneg.mpr hF) hC₂.le]
  have htailE := ENNReal.ofReal_le_ofReal htail
  have hlocalE := ENNReal.ofReal_le_ofReal hlocal
  dsimp only at h ⊢
  apply h.trans
  have hc := add_le_add
    (mul_le_mul_right (add_le_add (le_refl
      ((∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
        (ENNReal.ofReal (((a / F) * (b / F))⁻¹) * 81 *
          ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
            SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) *
          ((ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi) * (Λ * A))) *
        ∑ θ ∈ J, ∫⁻ x in P, ‖f θ x‖ₑ ^ 2))
      (mul_le_mul_right htailE
        ((∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
          ((ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi) * (Λ * σ P)) *
          ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2)))
      (ENNReal.ofReal (C₁ ^ 2)))
    (mul_le_mul_right hlocalE ((Λ * σ P) * ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2))
  have hh := mul_le_mul_right hc (9 * B : ℝ≥0∞)
  convert hh using 1
  all_goals
    simp (disch := positivity) only [hdet, ENNReal.ofReal_mul, ENNReal.ofReal_pow]
    ring

/-- Actual normalized grid-square averages with a fixed enlarged Fourier rectangle. -/
theorem selected_cap_grid_embedding_spectral_width (F : ℝ) (hF : 1 ≤ F) (m : ℕ) :
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
        (∀ θ ∈ J, Function.support (fun z ↦ 𝓕 (f θ) z) ⊆ ball (ξ θ) (F / a)) →
        (∀ z, (J.filter (fun θ ↦ z ∈ ball (ξ θ) (F / a))).card ≤ B) →
        (∀ θ ∈ J, ∀ z ∈ Function.support
          (𝓕 (f θ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
          |(O θ (z - ξ θ)) 0| ≤ (F / a) ∧ |(O θ (z - ξ θ)) 1| ≤ F / b) →
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
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, he⟩ := selected_cap_embedding_spectral_width F hF m
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
  have hF₀ : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hL₀ : 0 < L := by linarith
  have hL₁ : 1 ≤ L := by linarith
  have hs : 0 < s := mul_pos (pow_pos hL₀ _) ha
  have ht : 1 ≤ t := one_le_pow₀ hL₁
  have hs_t : L * s = t * a := by
    dsimp [s, t]
    rw [show 2 * j + 3 = (2 * j + 2) + 1 by omega, pow_succ L (2 * j + 2)]
    ring
  have hs_inv : s⁻¹ ≤ F / a := by
    calc
      _ ≤ a⁻¹ := by
        apply (inv_le_inv₀ hs ha).mpr
        dsimp [s]
        nlinarith [one_le_pow₀ hL₁ (n := 2 * j + 2)]
      _ ≤ F / a := by
        rw [inv_eq_one_div]
        exact div_le_div_of_nonneg_right hF ha.le
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
    a b t C₀ (L ^ (4 * K + 20) / 2) (F / a) s L (L / 2)
    ha hab ht hC₀ hD (div_pos hF₀ ha) hs hs_inv hL₀ (by positivity) hs_t.le
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
