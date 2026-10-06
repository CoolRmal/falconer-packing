/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourceWavePackets
public import FalconerPacking.OrientedReproducingKernel
public import FalconerPacking.UniformSchwartzFourier

/-!
# Uniform Schwartz bounds after normalization of actual spatial strips

Only the transverse coordinate is rescaled. The normalized strip cutoffs have a common
compact support and uniform derivatives of every order, independently of width and orientation.
This retains the distinct transverse and longitudinal Fourier scales.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Bornology FourierTransform
open scoped ContDiff RealInnerProductSpace

namespace FalconerPacking

/-- Synthesis from normalized transverse and unscaled longitudinal coordinates. -/
def spatialStripSynthesis
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (hw : 0 < w) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (orientedRectangleDilation O w 1 hw zero_lt_one).symm

theorem spatialStripSynthesis_coordinates
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (hw : 0 < w) (x : EuclideanSpace ℝ (Fin 2)) :
    O (spatialStripSynthesis O w hw x) = WithLp.toLp 2 ![w * x 0, x 1] := by
  ext i
  fin_cases i <;>
    simp [spatialStripSynthesis, orientedRectangleDilation,
      euclideanCoordinateDilation_symm_apply]

theorem norm_spatialStripSynthesis_le_one
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {w : ℝ} (hw : 0 < w) (hw₁ : w ≤ 1) :
    ‖(spatialStripSynthesis O w hw).toContinuousLinearMap‖ ≤ 1 := by
  apply (spatialStripSynthesis O w hw).toContinuousLinearMap.opNorm_le_bound
    (M := 1) (by norm_num)
  intro x
  change ‖spatialStripSynthesis O w hw x‖ ≤ 1 * ‖x‖
  rw [one_mul]
  have hsq : ‖spatialStripSynthesis O w hw x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← O.norm_map, spatialStripSynthesis_coordinates]
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [sq_nonneg (x 0), mul_nonneg hw.le (sub_nonneg.mpr hw₁)]
  nlinarith [norm_nonneg x, norm_nonneg (spatialStripSynthesis O w hw x)]

/-- The physical strip center in the chosen frame. -/
def spatialStripCenter
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (j : ℤ) : EuclideanSpace ℝ (Fin 2) :=
  O.symm (WithLp.toLp 2 ![w * j, 0])

/-- The actual compact cutoff, evaluated in normalized strip coordinates. -/
def normalizedSpatialStripFunction
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (hw : 0 < w) (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  χ (spatialStripCenter O w j + spatialStripSynthesis O w hw x) * stripPartitionBump (x 0)

theorem contDiff_normalizedSpatialStripFunction
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (hw : 0 < w) (j : ℤ) :
    ContDiff ℝ ∞ (normalizedSpatialStripFunction χ O w hw j) :=
  ((χ.smooth ⊤).comp (contDiff_const.add (spatialStripSynthesis O w hw).contDiff)).mul
    (contDiff_stripPartitionBump.comp (by fun_prop))

/-- Normalization confines the transverse coordinate to one and the longitudinal coordinate
to the support radius of the original cutoff. -/
theorem support_normalizedSpatialStripFunction_subset
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (hw : 0 < w) (j : ℤ) :
    Function.support (normalizedSpatialStripFunction χ O w hw j) ⊆
      closedBall 0 (1 + sourceCutoffRadius χ hχ) := by
  intro x hx
  have hn := mul_ne_zero_iff.mp hx
  have hx₀ : |x 0| ≤ 1 := by
    have hb := support_stripPartitionBump hn.2
    exact (abs_lt.mpr hb).le
  have hsource := support_subset_sourceCutoffRadius χ hχ hn.1
  rw [mem_closedBall, dist_zero_right] at hsource
  have hc : O (spatialStripCenter O w j + spatialStripSynthesis O w hw x) =
      WithLp.toLp 2 ![w * j + w * x 0, x 1] := by
    rw [map_add, spatialStripCenter, O.apply_symm_apply, spatialStripSynthesis_coordinates]
    ext i
    fin_cases i <;> simp
  have hx₁ : |x 1| ≤ sourceCutoffRadius χ hχ := by
    have hp := PiLp.norm_apply_le
      (O (spatialStripCenter O w j + spatialStripSynthesis O w hw x)) 1
    rw [O.norm_map, hc] at hp
    have hp' : |x 1| ≤ ‖spatialStripCenter O w j + spatialStripSynthesis O w hw x‖ := by
      simpa using hp
    exact hp'.trans hsource
  rw [mem_closedBall, dist_zero_right]
  have hs : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have hR := (sourceCutoffRadius_pos χ hχ).le
  have h₀ := sq_le_sq₀ (abs_nonneg (x 0)) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr hx₀
  have h₁ := sq_le_sq₀ (abs_nonneg (x 1)) hR |>.mpr hx₁
  simp only [sq_abs, one_pow] at h₀ h₁
  nlinarith [norm_nonneg x]

theorem hasCompactSupport_normalizedSpatialStripFunction
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (hw : 0 < w) (j : ℤ) :
    HasCompactSupport (normalizedSpatialStripFunction χ O w hw j) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
    (support_normalizedSpatialStripFunction_subset χ hχ O w hw j)

/-- A contracting affine change of variables does not enlarge a Schwartz derivative bound. -/
theorem norm_iteratedFDeriv_affine_schwartz_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) (hA : ‖A‖ ≤ 1)
    (z x : EuclideanSpace ℝ (Fin 2)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun u ↦ χ (z + A u)) x‖ ≤ SchwartzMap.seminorm ℝ 0 n χ := by
  have hc : ContDiff ℝ ∞ (fun u ↦ χ (z + u)) :=
    (χ.smooth ⊤).comp (contDiff_const.add contDiff_id)
  rw [show (fun u ↦ χ (z + A u)) = (fun u ↦ χ (z + u)) ∘ A from rfl,
    A.iteratedFDeriv_comp_right hc x (by exact_mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    iteratedFDeriv_comp_add_left]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg A) hA)).trans
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ n _)

/-- The normalized physical strip family has uniform derivatives of every order. -/
theorem exists_normalizedSpatialStripFunction_derivative_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (w : ℝ) (hw : 0 < w), w ≤ 1 → ∀ (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)),
        ‖iteratedFDeriv ℝ n (normalizedSpatialStripFunction χ O w hw j) x‖ ≤ C := by
  let b : SchwartzMap ℝ ℝ :=
    hasCompactSupport_stripPartitionBump.toSchwartzMap contDiff_stripPartitionBump
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i χ * SchwartzMap.seminorm ℝ 0 (n - i) b
  refine ⟨C, Finset.sum_nonneg (fun _ _ ↦ by positivity), ?_⟩
  intro O w hw hw₁ j x
  have hproj : ‖(EuclideanSpace.proj (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 := by
    apply (EuclideanSpace.proj (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).opNorm_le_bound (by norm_num)
    intro v
    simpa using PiLp.norm_apply_le v 0
  have hfirst : ContDiff ℝ ∞ (fun u ↦
      χ (spatialStripCenter O w j + spatialStripSynthesis O w hw u)) :=
    (χ.smooth ⊤).comp (contDiff_const.add (spatialStripSynthesis O w hw).contDiff)
  have hsecond : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 2) ↦
      stripPartitionBump (u 0)) := contDiff_stripPartitionBump.comp (by fun_prop)
  apply (norm_iteratedFDeriv_mul_le hfirst hsecond x
    (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)).trans
  apply Finset.sum_le_sum
  intro i hi
  have hfirstbound := norm_iteratedFDeriv_affine_schwartz_le χ
    (spatialStripSynthesis O w hw).toContinuousLinearMap
    (norm_spatialStripSynthesis_le_one O hw hw₁) (spatialStripCenter O w j) x i
  have hsecondbound : ‖iteratedFDeriv ℝ (n - i)
      (fun u : EuclideanSpace ℝ (Fin 2) ↦ stripPartitionBump (u 0)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 (n - i) b := by
    change ‖iteratedFDeriv ℝ (n - i)
      ((b : ℝ → ℝ) ∘ (EuclideanSpace.proj (0 : Fin 2) :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) x‖ ≤ _
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (b.smooth ⊤) x
      (show (n - i : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hproj)).trans
      (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ b (n - i) _)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfirstbound (Nat.cast_nonneg _))
    hsecondbound (norm_nonneg _) (by positivity)

/-- The normalized cutoff is bundled using its proved compact support and smoothness. -/
def normalizedSpatialStrip
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (hw : 0 < w) (j : ℤ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  ((hasCompactSupport_normalizedSpatialStripFunction χ hχ O w hw j).comp_left
    Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (contDiff_normalizedSpatialStripFunction χ O w hw j))

@[simp]
theorem normalizedSpatialStrip_apply
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ℝ) (hw : 0 < w) (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    normalizedSpatialStrip χ hχ O w hw j x = normalizedSpatialStripFunction χ O w hw j x := rfl

/-- Uniform Schwartz boundedness of the actual normalized strip family. -/
theorem isVonNBounded_normalizedSpatialStrip {ι : Type*}
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (O : ι → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hw₁ : ∀ i, w i ≤ 1) (j : ι → ℤ) :
    IsVonNBounded ℝ (range (fun i ↦ normalizedSpatialStrip χ hχ (O i) (w i) (hw i) (j i))) := by
  apply isVonNBounded_schwartz_range_of_derivatives _ (1 + sourceCutoffRadius χ hχ)
  · intro i
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    apply support_normalizedSpatialStripFunction_subset χ hχ (O i) (w i) (hw i) (j i)
    simpa only [Function.mem_support, normalizedSpatialStrip_apply, ne_eq,
      Complex.ofReal_eq_zero] using hx
  · intro n
    obtain ⟨C, hC, hc⟩ := exists_normalizedSpatialStripFunction_derivative_bound χ n
    refine ⟨C, hC, fun i x ↦ ?_⟩
    change ‖iteratedFDeriv ℝ n
      (Complex.ofRealLI ∘ normalizedSpatialStripFunction χ (O i) (w i) (hw i) (j i)) x‖ ≤ C
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (contDiff_normalizedSpatialStripFunction χ (O i) (w i) (hw i) (j i)).contDiffAt
      (by exact_mod_cast le_top)]
    exact hc (O i) (w i) (hw i) (hw₁ i) (j i) x

/-- Uniform rapid Fourier decay in the normalized, genuinely anisotropic coordinates. -/
theorem exists_normalizedSpatialStrip_fourier_decay
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (w : ℝ) (hw : 0 < w), w ≤ 1 → ∀ (j : ℤ) (ξ : EuclideanSpace ℝ (Fin 2)),
        ‖(𝓕 (normalizedSpatialStrip χ hχ O w hw j)) ξ‖ ≤ C / (1 + ‖ξ‖) ^ m := by
  let I := {p : ((EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) × ℝ) × ℤ //
    0 < p.1.2 ∧ p.1.2 ≤ 1}
  let F (p : I) := normalizedSpatialStrip χ hχ p.1.1.1 p.1.1.2 p.2.1 p.1.2
  have hF : IsVonNBounded ℝ (range F) :=
    isVonNBounded_normalizedSpatialStrip χ hχ (fun p : I ↦ p.1.1.1)
      (fun p : I ↦ p.1.1.2) (fun p ↦ p.2.1) (fun p ↦ p.2.2) (fun p ↦ p.1.2)
  have hfourier : IsVonNBounded ℝ (range (fun p : I ↦
      (𝓕 (F p) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ))) := by
    simpa only [← range_comp, Function.comp_def, fourierCLM_apply] using
      hF.image (fourierCLM ℝ (SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ))
  obtain ⟨C, hC, hc⟩ := exists_uniform_schwartz_decay _ hfourier m
  exact ⟨C, hC, fun O w hw hw₁ j ξ ↦ hc ⟨((O, w), j), hw, hw₁⟩ ξ⟩

/-- Actual complex spatial strip cutoff, before application to a source convolution. -/
def spatialStripCutoff
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  ((hasCompactSupport_smoothStripPacket χ hχ w e j).comp_left
    Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (contDiff_smoothStripPacket χ w e j))

@[simp]
theorem spatialStripCutoff_apply
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    spatialStripCutoff χ hχ w e j x = (smoothStripPacket χ w e j x : ℂ) := rfl

/-- The normalization exactly equals the original physical cutoff; it is not a surrogate
function with merely comparable derivative bounds. -/
theorem spatialStripCutoff_eq_normalized
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2)) (he : ∀ x, ⟪e, x⟫ = O x 0)
    (w : ℝ) (hw : 0 < w) (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    spatialStripCutoff χ hχ w e j x =
      normalizedSpatialStrip χ hχ O w hw j
        ((spatialStripSynthesis O w hw).symm (x - spatialStripCenter O w j)) := by
  let u := (spatialStripSynthesis O w hw).symm (x - spatialStripCenter O w j)
  have hx : spatialStripCenter O w j + spatialStripSynthesis O w hw u = x := by
    simp [u]
  have hu : ⟪e, x⟫ = w * j + w * u 0 := by
    rw [he, ← hx, map_add, spatialStripCenter, O.apply_symm_apply,
      spatialStripSynthesis_coordinates]
    simp
  change (smoothStripPacket χ w e j x : ℂ) =
    (normalizedSpatialStripFunction χ O w hw j u : ℂ)
  rw [normalizedSpatialStripFunction, hx, smoothStripPacket, smoothStripWeight, hu]
  congr 3
  field_simp
  ring

end FalconerPacking
