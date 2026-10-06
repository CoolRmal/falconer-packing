/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AffineDistanceL1
public import FalconerPacking.AngularTruncation

/-!
# Whole-pin affine comparison by angular truncation

Absolute continuity of the two radial laws identifies the full affine densities before
any truncation. Their integrals are one, giving a bound of two on the discarded pins.
Only the retained restriction needs bounded angular densities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- Absolute continuity of the radial law alone identifies the full affine density for
almost every pin; no bounded angular density is required. -/
theorem ae_map_affineDistance_eq_withDensity_of_radial_ac
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (ν : Measure (EuclideanSpace ℝ (Fin 2)))
    (b : EuclideanSpace ℝ (Fin 2))
    (hac : ν.map (radialAngle b) ≪ radialAngularMeasure) (hsep : ∀ᵐ y ∂ν, b ≠ y) :
    ∀ᵐ y ∂ν, μ.map (fun x ↦ affineDistance b x y) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (affineDistanceDensity μ b y t)) := by
  letI : IsProbabilityMeasure (μ.map (fun x ↦ x - b)) :=
    inferInstance
  have ha := ae_memLp_charFun_on_line (μ.map (fun x ↦ x - b)) hs hs₂
    (hfr.map_sub_const b)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at ha
  have hb := ae_of_ae_map (by fun_prop : AEMeasurable (radialAngle b) ν) (hac.ae_le ha)
  filter_upwards [hb, hsep] with y hy hy'
  exact map_affineDistance_eq_withDensity μ b hy' hy

/-- An actual affine density of a probability law has integral exactly one. -/
theorem lintegral_affineDistanceDensity_eq_one
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (b y : EuclideanSpace ℝ (Fin 2))
    (hd : μ.map (fun x ↦ affineDistance b x y) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (affineDistanceDensity μ b y t))) :
    ∫⁻ t : ℝ, ENNReal.ofReal (affineDistanceDensity μ b y t) = 1 := by
  have he := congrArg (fun σ : Measure ℝ ↦ σ univ) hd
  rw [Measure.map_apply (by unfold affineDistance; fun_prop) MeasurableSet.univ,
    preimage_univ, measure_univ, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ] at he
  exact he.symm

/-- The L¹ distance between the actual affine densities of two probability laws is at most two. -/
theorem lintegral_affineDistanceDensity_sub_abs_le_two
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (b c y : EuclideanSpace ℝ (Fin 2))
    (hb : μ.map (fun x ↦ affineDistance b x y) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (affineDistanceDensity μ b y t)))
    (hc : μ.map (fun x ↦ affineDistance c x y) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (affineDistanceDensity μ c y t))) :
    (∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
      affineDistanceDensity μ b y t|) ≤ 2 := by
  calc
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal (affineDistanceDensity μ c y t) +
        ENNReal.ofReal (affineDistanceDensity μ b y t) := by
      apply lintegral_mono
      intro t
      dsimp only
      have hb₀ := affineDistanceDensity_nonneg μ b y t
      have hc₀ := affineDistanceDensity_nonneg μ c y t
      rw [← ENNReal.ofReal_add hc₀ hb₀]
      apply ENNReal.ofReal_le_ofReal
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = 2 := by
      rw [lintegral_add_left (by fun_prop),
        lintegral_affineDistanceDensity_eq_one μ c y hc,
        lintegral_affineDistanceDensity_eq_one μ b y hb]
      norm_num

/-- A measurable pin restriction costs at most twice its discarded mass. -/
theorem lintegral_affineDistanceDensity_sub_abs_restrict_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (ν : Measure (EuclideanSpace ℝ (Fin 2)))
    (b c : EuclideanSpace ℝ (Fin 2))
    (hb : ν.map (radialAngle b) ≪ radialAngularMeasure)
    (hc : ν.map (radialAngle c) ≪ radialAngularMeasure)
    (hsep : ∀ᵐ y ∂ν, b ≠ y ∧ c ≠ y) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    (∫⁻ y in S, ∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
      affineDistanceDensity μ b y t| ∂volume ∂ν) ≤ 2 * ν S := by
  have hbd := ae_map_affineDistance_eq_withDensity_of_radial_ac μ hs hs₂ hfr ν b hb
    (hsep.mono fun _ h ↦ h.1)
  have hcd := ae_map_affineDistance_eq_withDensity_of_radial_ac μ hs hs₂ hfr ν c hc
    (hsep.mono fun _ h ↦ h.2)
  have htwo : ∀ᵐ y ∂ν, (∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
      affineDistanceDensity μ b y t|) ≤ 2 := by
    filter_upwards [hbd, hcd] with y hy hy'
    exact lintegral_affineDistanceDensity_sub_abs_le_two μ b c y hy hy'
  simpa only [lintegral_const, Measure.restrict_apply_univ] using
    lintegral_mono_ae (ae_restrict_of_ae htwo : ∀ᵐ y ∂ν.restrict S, _)

/-- Angular truncation gives the whole-pin weighted affine comparison. The moment terms
are those of the actual radial laws, and no independence of the two angles is assumed. -/
theorem affineDistanceDensity_truncated_L1_bound
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {s C δ r m q : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hC : 1 ≤ C) (hm : 0 < m) (hm₁ : m ≤ 1)
    (hfr : IsFrostman μ s (C / m))
    (b c : EuclideanSpace ℝ (Fin 2)) (A : ℝ≥0∞)
    (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hrδ : r ≤ δ / 16)
    (hbc : dist b c ≤ r) (hsource : ∀ᵐ x ∂μ, dist x b ≤ r)
    (hsep : ∀ᵐ y ∂ν, δ ≤ dist b y)
    (ρb ρc : ℝ → ℝ≥0∞) (hρb : Measurable ρb) (hρc : Measurable ρc)
    (hbmap : ν.map (radialAngle b) = radialAngularMeasure.withDensity ρb)
    (hcmap : ν.map (radialAngle c) = radialAngularMeasure.withDensity ρc) :
    ENNReal.ofReal m *
      (∫⁻ y, ∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
        affineDistanceDensity μ b y t| ∂volume ∂ν) ≤
      (ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A * ENNReal.ofReal C) ^
          (1 / 2 : ℝ) * ENNReal.ofReal m ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((1 + 8 / δ) ^ (s - 1 / 2)) *
          ENNReal.ofReal (r ^ (s - 1 / 2)) +
      2 * ENNReal.ofReal m * A ^ (1 - q) *
        ((∫⁻ θ, ρb θ ^ q ∂radialAngularMeasure) +
          ∫⁻ θ, ρc θ ^ q ∂radialAngularMeasure) := by
  obtain ⟨S, hS, hbS, hcS, hbad⟩ := correlated_density_truncation ν radialAngularMeasure
    (by fun_prop) (by fun_prop) hρb hρc hbmap hcmap hA hAt hq
  have hbdom : (ν.restrict S).map (radialAngle b) ≤ A • (volume : Measure ℝ) :=
    hbS.trans (smul_le_smul_left A (show radialAngularMeasure ≤ volume from
      Measure.restrict_le_self))
  have hcdom : (ν.restrict S).map (radialAngle c) ≤ A • (volume : Measure ℝ) :=
    hcS.trans (smul_le_smul_left A (show radialAngularMeasure ≤ volume from
      Measure.restrict_le_self))
  have hgood := affineDistanceDensity_weighted_L1_bound μ hs hs₂ hC hm hm₁ hfr
    (ν.restrict S) b c A hδ hδ₁ hr hrδ hbc hsource (ae_restrict_of_ae hsep) hbdom hcdom
  have hmass : (ν.restrict S) univ ≤ 1 := by
    rw [Measure.restrict_apply_univ]
    exact prob_le_one
  have hgood' : ENNReal.ofReal m *
      (∫⁻ y in S, ∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
        affineDistanceDensity μ b y t| ∂volume ∂ν) ≤
      (ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A * ENNReal.ofReal C) ^
          (1 / 2 : ℝ) * ENNReal.ofReal m ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((1 + 8 / δ) ^ (s - 1 / 2)) *
          ENNReal.ofReal (r ^ (s - 1 / 2)) := by
    refine hgood.trans ?_
    have hh : ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A *
        ENNReal.ofReal C * (ν.restrict S) univ ≤
        ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A * ENNReal.ofReal C := by
      simpa only [mul_one] using mul_le_mul_right hmass
        (ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A * ENNReal.ofReal C)
    exact mul_le_mul' (mul_le_mul' (mul_le_mul'
      (ENNReal.rpow_le_rpow hh (by norm_num)) le_rfl) le_rfl) le_rfl
  have hb : ν.map (radialAngle b) ≪ radialAngularMeasure := by
    rw [hbmap]
    exact withDensity_absolutelyContinuous _ _
  have hc : ν.map (radialAngle c) ≪ radialAngularMeasure := by
    rw [hcmap]
    exact withDensity_absolutelyContinuous _ _
  have hsep' : ∀ᵐ y ∂ν, b ≠ y ∧ c ≠ y := by
    filter_upwards [hsep] with y hy
    have hcsep := half_separation_le_dist_center hy hbc (by linarith)
    exact ⟨dist_pos.mp (hδ.trans_le hy),
      dist_pos.mp (lt_of_lt_of_le (by linarith : 0 < δ / 2) hcsep)⟩
  have hbad' := lintegral_affineDistanceDensity_sub_abs_restrict_le μ hs hs₂ hfr
    ν b c hb hc hsep' Sᶜ
  have hbad'' := mul_le_mul_right (hbad'.trans (mul_le_mul_right hbad 2)) (ENNReal.ofReal m)
  rw [← lintegral_add_compl (fun y ↦ ∫⁻ t : ℝ, ENNReal.ofReal
    |affineDistanceDensity μ c y t - affineDistanceDensity μ b y t|) hS, mul_add]
  exact add_le_add hgood' (hbad''.trans_eq (by ring))

end FalconerPacking
