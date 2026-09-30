/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialAngleGeometry
import FalconerPacking.CorrelatedFourierEnergy

/-!
# Two angular charts for correlated projection estimates

The principal angle chart has a cut at ±π. A simultaneous half-turn puts pairs crossing
that cut into a common short chart. The change of chart is two translations, preserves
bounded angular densities up to a factor two, and negates both projection directions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace FalconerPacking

/-- The other principal angle chart, obtained by a half-turn. -/
def halfTurnAngle (t : ℝ) : ℝ := if 0 < t then t - Real.pi else t + Real.pi

@[fun_prop]
theorem measurable_halfTurnAngle : Measurable halfTurnAngle := by
  unfold halfTurnAngle
  exact Measurable.ite measurableSet_Ioi (measurable_id.sub_const _)
    (measurable_id.add_const _)

theorem halfTurnAngle_mem {t : ℝ} (ht : t ∈ Icc (-Real.pi) Real.pi) :
    halfTurnAngle t ∈ Icc (-Real.pi) Real.pi := by
  unfold halfTurnAngle
  split_ifs with h <;> constructor <;> linarith [ht.1, ht.2, Real.pi_pos]

/-- The half-turn reverses the corresponding unit vector. -/
theorem angularDirection_halfTurnAngle (t : ℝ) :
    angularDirection (halfTurnAngle t) = -angularDirection t := by
  unfold halfTurnAngle angularDirection
  split_ifs <;> simp [Real.cos_sub_pi, Real.sin_sub_pi, Real.cos_add_pi, Real.sin_add_pi, add_comm]

/-- A pair crossing the principal cut has a short difference in the half-turn chart. -/
theorem halfTurnAngle_sub_le_pi {θ φ : ℝ}
    (hθ : θ ∈ Icc (-Real.pi) Real.pi) (hφ : φ ∈ Icc (-Real.pi) Real.pi)
    (hcut : Real.pi < |φ - θ|) :
    |halfTurnAngle φ - halfTurnAngle θ| ≤ Real.pi := by
  rcases lt_abs.1 hcut with h | h
  all_goals
    unfold halfTurnAngle
    split_ifs <;> rw [abs_le] <;> constructor <;>
      linarith [hθ.1, hθ.2, hφ.1, hφ.2, Real.pi_pos]

/-- On the crossing piece the half-turn angle difference is controlled by the original chord. -/
theorem halfTurnAngle_sub_le_chord {θ φ : ℝ}
    (hθ : θ ∈ Icc (-Real.pi) Real.pi) (hφ : φ ∈ Icc (-Real.pi) Real.pi)
    (hcut : Real.pi < |φ - θ|) :
    |halfTurnAngle φ - halfTurnAngle θ| ≤
      (Real.pi / 2) * ‖angularDirection φ - angularDirection θ‖ := by
  have h := abs_sub_le_pi_div_two_mul_chord (halfTurnAngle_sub_le_pi hθ hφ hcut)
  simpa only [angularDirection_halfTurnAngle, neg_sub_neg, norm_sub_rev] using h

/-- The half-turn is a union of two translations, so its Lebesgue pushforward is bounded. -/
theorem map_halfTurnAngle_volume_le :
    (volume : Measure ℝ).map halfTurnAngle ≤ (2 : ℝ≥0∞) • (volume : Measure ℝ) := by
  apply Measure.le_iff.2
  intro S hS
  rw [Measure.map_apply measurable_halfTurnAngle hS, Measure.smul_apply, smul_eq_mul]
  have hsub : halfTurnAngle ⁻¹' S ⊆
      (fun t : ℝ ↦ t + -Real.pi) ⁻¹' S ∪ (fun t : ℝ ↦ t + Real.pi) ⁻¹' S := by
    intro t ht
    by_cases h : 0 < t
    · exact Or.inl (by simpa [halfTurnAngle, h, sub_eq_add_neg] using ht)
    · exact Or.inr (by simpa [halfTurnAngle, h] using ht)
  have hneg : volume ((fun t : ℝ ↦ t + -Real.pi) ⁻¹' S) = volume S :=
    (measurePreserving_add_right (volume : Measure ℝ) (-Real.pi)).measure_preimage
      hS.nullMeasurableSet
  have hpos : volume ((fun t : ℝ ↦ t + Real.pi) ⁻¹' S) = volume S :=
    (measurePreserving_add_right (volume : Measure ℝ) Real.pi).measure_preimage hS.nullMeasurableSet
  calc
    volume (halfTurnAngle ⁻¹' S) ≤
        volume ((fun t : ℝ ↦ t + -Real.pi) ⁻¹' S ∪
          (fun t : ℝ ↦ t + Real.pi) ⁻¹' S) := measure_mono hsub
    _ ≤ volume ((fun t : ℝ ↦ t + -Real.pi) ⁻¹' S) +
        volume ((fun t : ℝ ↦ t + Real.pi) ⁻¹' S) := measure_union_le _ _
    _ = _ := by rw [hneg, hpos, two_mul]

/-- Changing the chart preserves angular domination with at most a factor two. -/
theorem map_halfTurnAngle_le {ν : Measure ℝ} {A : ℝ≥0∞}
    (hν : ν ≤ A • (volume : Measure ℝ)) :
    ν.map halfTurnAngle ≤ (2 * A) • (volume : Measure ℝ) := by
  calc
    ν.map halfTurnAngle ≤ (A • (volume : Measure ℝ)).map halfTurnAngle :=
      Measure.map_mono hν measurable_halfTurnAngle
    _ = A • ((volume : Measure ℝ).map halfTurnAngle) := Measure.map_smul _ _ _
    _ ≤ A • ((2 : ℝ≥0∞) • (volume : Measure ℝ)) := by
      apply Measure.le_iff'.2
      intro S
      simpa only [Measure.smul_apply, smul_eq_mul, mul_comm A] using
        mul_le_mul_left (Measure.le_iff'.1 map_halfTurnAngle_volume_le S) A
    _ = _ := by rw [smul_smul, mul_comm A]

/-- The density bound is preserved when the angles depend on another measurable parameter. -/
theorem map_halfTurnAngle_comp_le
    {α : Type*} [MeasurableSpace α] {κ : Measure α} {θ : α → ℝ} {A : ℝ≥0∞}
    (hθ : Measurable θ) (hdom : κ.map θ ≤ A • (volume : Measure ℝ)) :
    κ.map (halfTurnAngle ∘ θ) ≤ (2 * A) • (volume : Measure ℝ) := by
  rw [← Measure.map_map measurable_halfTurnAngle hθ]
  exact map_halfTurnAngle_le hdom

/-- Reversing both directions and the translation conjugates the Fourier difference. -/
theorem shifted_charFun_halfTurn (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsFiniteMeasure μ] (θ φ v τ : ℝ) :
    ‖Complex.exp (Complex.I * (τ * (-v))) *
        charFun μ (τ • angularDirection (halfTurnAngle φ)) -
      charFun μ (τ • angularDirection (halfTurnAngle θ))‖ₑ ^ 2 =
    ‖Complex.exp (Complex.I * (τ * v)) * charFun μ (τ • angularDirection φ) -
      charFun μ (τ • angularDirection θ)‖ₑ ^ 2 := by
  have he : Complex.exp (Complex.I * (τ * (-v))) =
      conj (Complex.exp (Complex.I * (τ * v))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [he, angularDirection_halfTurnAngle, angularDirection_halfTurnAngle,
    smul_neg, smul_neg, charFun_neg, charFun_neg, ← map_mul, ← map_sub, RCLike.enorm_conj]

/-- A literal-chart comparison transfers to circular closeness with exactly a factor three.
This preserves any uniform dependence already established for its constant `B`. -/
theorem circular_correlated_shifted_charFun_energy_bound_of_chart
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] {s B r : ℝ}
    {α : Type*} [MeasurableSpace α]
    (hbound : ∀ (ν : Measure α) [SFinite ν] (θ φ v : α → ℝ) (A : ℝ≥0∞),
      Measurable θ → Measurable φ → Measurable v →
      ν.map θ ≤ A • (volume : Measure ℝ) → ν.map φ ≤ A • (volume : Measure ℝ) →
      (∀ᵐ z ∂ν, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
      (∀ᵐ z ∂ν, |φ z - θ z| ≤ r) → (∀ᵐ z ∂ν, |v z| ≤ r ^ 2) →
      ∫⁻ z, ∫⁻ τ : ℝ,
        ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (φ z)) -
          charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂ν ≤
        A * ENNReal.ofReal (B * r ^ (2 * s - 2)))
    (κ : Measure α) [SFinite κ] (θ φ v : α → ℝ) (A : ℝ≥0∞)
    (hθ : Measurable θ) (hφ : Measurable φ) (hv : Measurable v)
    (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi)
    (hclose : ∀ᵐ z ∂κ,
      (Real.pi / 2) * ‖angularDirection (φ z) - angularDirection (θ z)‖ ≤ r)
    (hshift : ∀ᵐ z ∂κ, |v z| ≤ r ^ 2) :
    ∫⁻ z, ∫⁻ τ : ℝ,
      ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (φ z)) -
        charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
      A * ENNReal.ofReal (3 * B * r ^ (2 * s - 2)) := by
  let S : Set α := {z | |φ z - θ z| ≤ Real.pi}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hθS : (κ.restrict S).map θ ≤ A • (volume : Measure ℝ) :=
    (Measure.map_mono Measure.restrict_le_self hθ).trans hθdom
  have hφS : (κ.restrict S).map φ ≤ A • (volume : Measure ℝ) :=
    (Measure.map_mono Measure.restrict_le_self hφ).trans hφdom
  have hθSc : (κ.restrict Sᶜ).map θ ≤ A • (volume : Measure ℝ) :=
    (Measure.map_mono Measure.restrict_le_self hθ).trans hθdom
  have hφSc : (κ.restrict Sᶜ).map φ ≤ A • (volume : Measure ℝ) :=
    (Measure.map_mono Measure.restrict_le_self hφ).trans hφdom
  have hgood := hbound (κ.restrict S) θ φ v A hθ hφ hv hθS hφS
    (ae_restrict_of_ae hrange) (show ∀ᵐ z ∂κ.restrict S, |φ z - θ z| ≤ r from by
      filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hclose] with z hz hzr
      exact (abs_sub_le_pi_div_two_mul_chord hz).trans hzr)
    (ae_restrict_of_ae hshift)
  have hbad := hbound (κ.restrict Sᶜ)
    (halfTurnAngle ∘ θ) (halfTurnAngle ∘ φ) (fun z ↦ -v z) (2 * A)
    (measurable_halfTurnAngle.comp hθ) (measurable_halfTurnAngle.comp hφ) hv.neg
    (map_halfTurnAngle_comp_le hθ hθSc) (map_halfTurnAngle_comp_le hφ hφSc)
    (show ∀ᵐ z ∂κ.restrict Sᶜ,
      (halfTurnAngle ∘ θ) z ∈ Icc (-Real.pi) Real.pi ∧
        (halfTurnAngle ∘ φ) z ∈ Icc (-Real.pi) Real.pi from by
      filter_upwards [ae_restrict_of_ae hrange] with z hz
      exact ⟨halfTurnAngle_mem hz.1, halfTurnAngle_mem hz.2⟩)
    (show ∀ᵐ z ∂κ.restrict Sᶜ,
      |(halfTurnAngle ∘ φ) z - (halfTurnAngle ∘ θ) z| ≤ r from by
      filter_upwards [ae_restrict_mem hS.compl, ae_restrict_of_ae hrange,
        ae_restrict_of_ae hclose] with z hz hzrange hzclose
      exact (halfTurnAngle_sub_le_chord hzrange.1 hzrange.2 (lt_of_not_ge hz)).trans hzclose)
    (show ∀ᵐ z ∂κ.restrict Sᶜ, |-v z| ≤ r ^ 2 from by
      simpa only [abs_neg] using (ae_restrict_of_ae hshift :
        ∀ᵐ z ∂κ.restrict Sᶜ, |v z| ≤ r ^ 2))
  simp only [Function.comp_apply, Complex.ofReal_neg, shifted_charFun_halfTurn] at hbad
  rw [← Measure.restrict_add_restrict_compl (μ := κ) hS, lintegral_add_measure]
  refine (add_le_add hgood hbad).trans_eq ?_
  rw [show 3 * B * r ^ (2 * s - 2) = 3 * (B * r ^ (2 * s - 2)) by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat]
  ring

/-- The full correlated Fourier comparison only needs circular closeness of the directions.
The angle maps themselves may cross the principal cut at ±π. -/
theorem exists_circular_correlated_shifted_charFun_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ v : α → ℝ) (A : ℝ≥0∞),
        Measurable θ → Measurable φ → Measurable v →
        κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ,
          (Real.pi / 2) * ‖angularDirection (φ z) - angularDirection (θ z)‖ ≤ r) →
        (∀ᵐ z ∂κ, |v z| ≤ r ^ 2) →
          ∫⁻ z, ∫⁻ τ : ℝ,
            ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (φ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B, hB, hbound⟩ := exists_correlated_shifted_charFun_energy_bound μ hs hs₂ hfr
  refine ⟨3 * B, by positivity, ?_⟩
  intro r hr hsource α _ κ _ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hshift
  exact circular_correlated_shifted_charFun_energy_bound_of_chart μ
    (hbound r hr hsource) κ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hshift

/-- The comparison applies to actual radial angles at nearby centers, including pairs
straddling the principal branch cut. The separation and displacement imply the angle bound. -/
theorem exists_radial_correlated_shifted_charFun_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r d : ℝ, 0 < r → 0 < d → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ (b c : EuclideanSpace ℝ (Fin 2)), Real.pi * dist b c ≤ r * d →
      ∀ (κ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite κ]
        (v : EuclideanSpace ℝ (Fin 2) → ℝ) (A : ℝ≥0∞), Measurable v →
        κ.map (radialAngle b) ≤ A • (volume : Measure ℝ) →
        κ.map (radialAngle c) ≤ A • (volume : Measure ℝ) →
        (∀ᵐ y ∂κ, d ≤ dist b y ∧ d ≤ dist c y) →
        (∀ᵐ y ∂κ, |v y| ≤ r ^ 2) →
          ∫⁻ y, ∫⁻ τ : ℝ,
            ‖Complex.exp (Complex.I * (τ * v y)) *
                charFun μ (τ • angularDirection (radialAngle c y)) -
              charFun μ (τ • angularDirection (radialAngle b y))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_circular_correlated_shifted_charFun_energy_bound μ hs hs₂ hfr
  refine ⟨B, hB, ?_⟩
  intro r d hr hd hsource b c hdisp κ _ v A hv hbdom hcdom hsep hshift
  apply hbound r hr hsource κ (radialAngle b) (radialAngle c) v A
    measurable_radialAngle.of_uncurry_left measurable_radialAngle.of_uncurry_left
    hv hbdom hcdom _ _ hshift
  · exact ae_of_all κ fun y ↦
      ⟨⟨(radialAngle_mem b y).1.le, (radialAngle_mem b y).2⟩,
        ⟨(radialAngle_mem c y).1.le, (radialAngle_mem c y).2⟩⟩
  · filter_upwards [hsep] with y hy
    simpa only [norm_sub_rev] using radialAngle_chord_le_of_separation hd hy.1 hy.2 hdisp

end FalconerPacking
