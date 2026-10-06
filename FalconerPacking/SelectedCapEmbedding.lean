/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SelectedCapGeometry
public import FalconerPacking.AnisotropicKernelPotential

/-!
# Weighted embedding from selected tube tests

All kernel-potential hypotheses are discharged from selected tube tests, bounded overlap,
and geometric support margins. The averaging components here are actual ball restrictions
of volume; their common area is retained explicitly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Classical
open scoped ENNReal

namespace FalconerPacking

/-- One retained Fourier label obeys weighted embedding from the selected tests alone.
The rectangle mass and the anisotropic support margin are conclusions of the proof. -/
theorem selected_cap_weighted_embedding (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι κ : Type*} (I : Finset ι) (selection : ι → Finset κ) (θ : κ)
        (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
        (q : ι → EuclideanSpace ℝ (Fin 2))
        (O V : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (P : Set (EuclideanSpace ℝ (Fin 2)))
        (a b t C₀ D s L R : ℝ), 0 < a → a ≤ b →
        1 ≤ t → 0 ≤ C₀ → (5 + 7 * C₀) * t ≤ D → 0 < s → 0 < L → 0 ≤ R →
        L * s ≤ t * a →
      ∀ (Λ : ℕ) (A : ℝ≥0∞)
        (ξ₀ : EuclideanSpace ℝ (Fin 2))
        (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
        (∀ y i, |(V y) i - (O y) i| ≤ C₀ * (a / b) * ‖y‖) →
        (∀ i ∈ I, MeasurableSet (E i)) → MeasurableSet P →
        (∀ i ∈ I, E i ⊆ P) →
        (∀ x, (I.filter fun i ↦ x ∈ E i).card ≤ Λ) →
        (∀ i ∈ I, ∀ x ∈ E i, ‖x - q i‖ ≤ t * a) →
        (∀ i ∈ I, θ ∈ selection i →
          σ (frameRectangle V (q i) (D * a) (D * b) ∩ P) ≤ A) →
        (∀ i ∈ I, ∀ x ∈ ball (q i) (L * s), ∀ y ∉ P, 2 * b * R ≤ dist x y) →
        (∀ ξ ∈ Function.support (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
          |(O (ξ - ξ₀)) 0| ≤ a⁻¹ ∧ |(O (ξ - ξ₀)) 1| ≤ b⁻¹) →
        let W := ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi
        (∫⁻ x, ‖f x‖ₑ ^ 2 ∂selectedCapMeasure I selection (fun i ↦ σ (E i))
          (fun i ↦ volume.restrict (ball (q i) (L * s))) θ) ≤
          (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
            ((ENNReal.ofReal ((a * b)⁻¹) * 81 *
                ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
                  SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) * (W * (Λ * A))) *
                (∫⁻ x in P, ‖f x‖ₑ ^ 2) +
              (ENNReal.ofReal ((a * b)⁻¹ * C / (1 + R) ^ m) *
                (W * (Λ * σ P))) * ∫⁻ x, ‖f x‖ₑ ^ 2) := by
  obtain ⟨C, hC, he⟩ := anisotropic_weighted_embedding m
  refine ⟨C, hC, ?_⟩
  intro ι κ I selection θ σ hσ E q O V P a b t C₀ D s L R ha hab
    ht hC₀ hD hs hL hR hsize Λ A ξ₀ f hframe hE hP hsub hover hEball htest hmargin hf
  dsimp only
  let W := ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi
  let μ := fun i ↦ volume.restrict (ball (q i) (L * s))
  let τ := selectedCapMeasure I selection (fun i ↦ σ (E i)) μ θ
  let F := orientedRectangleDilation O a b ha (ha.trans_le hab)
  have hW₀ : W ≠ 0 := by dsimp [W]; positivity
  have hWtop : W ≠ ∞ := by dsimp [W]; finiteness
  have hmass (i : ι) (_hi : i ∈ I) : μ i univ ≤ W := by
    simp [μ, W, EuclideanSpace.volume_ball_fin_two]
  have htotal : τ univ ≤ W * (Λ * σ P) :=
    (selectedCapMeasure_univ_le I selection (fun i ↦ σ (E i)) μ θ W hmass).trans
      (mul_le_mul_right (sum_measure_le_mul_of_multiplicity σ I E hP hE hsub Λ hover) _)
  haveI : IsFiniteMeasure τ := ⟨lt_of_le_of_lt htotal (by dsimp [W]; finiteness)⟩
  have hrect (c : EuclideanSpace ℝ (Fin 2)) :
      τ (frameRectangle O c a b) ≤ W * (Λ * A) := by
    apply selectedCapMeasure_frameRectangle_le σ I selection θ E
      (fun i ↦ ball (q i) (L * s)) q μ O V P ha hab ht hC₀ hD Λ A W hW₀ hWtop
      hframe hE hP hsub hover hEball ?_ hmass ?_ htest c
    · intro i hi x hx
      exact (show ‖x - q i‖ < L * s by
        simpa only [mem_ball, dist_eq_norm] using hx).le.trans hsize
    · intro i hi
      simp [μ, Measure.restrict_apply, measurableSet_ball.compl]
  have hgrid (k : Fin 2 → ℤ) : τ (F ⁻¹' dyadicCube 0 k) ≤ W * (Λ * A) :=
    (measure_mono (orientedDilation_preimage_unitCube_subset O a b ha (ha.trans_le hab) k)).trans
      (hrect (F.symm (gridSquareCenter 1 k)))
  have htail (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∉ P) :
      ∀ᵐ x ∂τ, R ≤ ‖F (x - y)‖ := by
    apply ae_selectedCapMeasure I selection (fun i ↦ σ (E i)) μ θ
    intro i hi _hθ
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hdist := hmargin i hi x hx y hy
    have hn := norm_le_twice_width_mul_orientedDilation O a b ha hab (x - y)
    rw [dist_eq_norm] at hdist
    have hb : 0 < b := ha.trans_le hab
    dsimp only [F]
    nlinarith
  have hdual : ∀ ξ ∈ Function.support (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
      ∀ i, |(F.symm.toContinuousLinearMap.adjoint (ξ - ξ₀)) i| ≤ 1 := by
    intro ξ hξ
    exact (orientedRectangleDilation_dual_mem_square_iff O a b ha (ha.trans_le hab)
      (ξ - ξ₀)).mpr (hf ξ hξ)
  have h := he τ F ξ₀ f (W * (Λ * A)) P R hP hR hdual hgrid htail
  rw [orientedRectangleDilation_abs_det] at h
  apply h.trans
  gcongr
  exact Measure.restrict_le_self

/-- The full finite selected-cap estimate combines local Fourier orthogonality with
selected tube tests. Every overlap and common averaging-area factor is explicit. -/
theorem selected_cap_embedding (m : ℕ) :
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
          |(O θ (z - ξ θ)) 0| ≤ a⁻¹ ∧ |(O θ (z - ξ θ)) 1| ≤ b⁻¹) →
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
  obtain ⟨C₁, C₂, hC₁, hC₂, hlocal⟩ := weighted_selected_fourier_ball_sum m
  obtain ⟨C₃, hC₃, hcap⟩ := selected_cap_weighted_embedding m
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro ι κ I J selection hselection σ hσ E q O V P a b t C₀ D r s L R
    ha hab ht hC₀ hD hr hs hsr hL hR hsize Λ B A ξ f
    hframe hE hP hsub hover hEball htest hmargin hballs hB hrect
  dsimp only
  have hweight := sum_measure_le_mul_of_multiplicity σ I E hP hE hsub Λ hover
  have h := hlocal I J selection hselection f ξ q (fun i ↦ σ (E i))
    B r s L hr hs hsr hL.le hballs hB
  apply h.trans
  apply mul_le_mul_right
  apply add_le_add
  · apply mul_le_mul_right
    calc
      _ ≤ ∑ θ ∈ J, (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
          ((ENNReal.ofReal ((a * b)⁻¹) * 81 *
              ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
                SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) *
              ((ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi) * (Λ * A))) *
              (∫⁻ x in P, ‖f θ x‖ₑ ^ 2) +
            (ENNReal.ofReal ((a * b)⁻¹ * C₃ / (1 + R) ^ m) *
              ((ENNReal.ofReal (L * s) ^ 2 * ENNReal.ofReal Real.pi) * (Λ * σ P))) *
                ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
        apply Finset.sum_le_sum
        intro θ hθ
        exact hcap I selection θ σ E q (O θ) (V θ) P a b t C₀ D s L R
          ha hab ht hC₀ hD hs hL hR hsize Λ A (ξ θ) (f θ)
          (hframe θ hθ) hE hP hsub hover hEball
          (fun i hi hθi ↦ htest i hi θ hθi) hmargin (hrect θ hθ)
      _ = _ := by
        simp_rw [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  · gcongr

end FalconerPacking
