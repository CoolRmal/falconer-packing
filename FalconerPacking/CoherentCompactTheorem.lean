/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CoherentBorelParameters
public import FalconerPacking.RadialProjectionTheorem
public import FalconerPacking.RadialMomentCenters
public import FalconerPacking.AffineDistance
public import FalconerPacking.CoherentDyadicStep
public import FalconerPacking.DyadicAffineGeometry

/-!
# The coherent compact-source distance theorem

The radial theorem supplies one fixed family of centers with a common moment bound.
Finite dyadic affine approximations then converge through summable density comparisons.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerPacking

/-- Compact Frostman source and pin probabilities supply the fixed centers and finite radial
moment needed simultaneously at all dyadic levels. -/
theorem exists_compact_dyadic_radial_centers
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {K L : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (hL : IsCompact L)
    (hμK : (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0)
    (hνL : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Lᶜ = 0)
    {s t Cμ Cν : ℝ} (hs : 1 < s) (ht : 1 < t)
    (hμ : IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) s Cμ)
    (hν : IsFrostman (ν : Measure (EuclideanSpace ℝ (Fin 2))) t Cν) :
    ∃ (q : ℝ) (B : ℝ≥0∞)
      (c : ℕ → (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)),
      1 < q ∧ B < ∞ ∧
      (∀ n k, 0 < (μ : Measure (EuclideanSpace ℝ (Fin 2))) (dyadicCube n k) →
        c n k ∈ dyadicCube n k ∩ K ∧
        (ν : Measure (EuclideanSpace ℝ (Fin 2))).map (radialAngle (c n k)) =
          radialAngularMeasure.withDensity
            (radialProjectionDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) (c n k))) ∧
      (∀ n (I : Finset (Fin 2 → ℤ)),
        ∑ k ∈ I, (μ : Measure (EuclideanSpace ℝ (Fin 2))) (dyadicCube n k) *
          (∫⁻ θ, radialProjectionDensity
            (ν : Measure (EuclideanSpace ℝ (Fin 2))) (c n k) θ ^ q
              ∂radialAngularMeasure) ≤ B) ∧
      (∀ n, Measurable (dyadicCenterMap n (c n))) ∧
      ∀ n, ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))),
        dyadicCenterMap n (c n) x ∈ K ∧
          dist x (dyadicCenterMap n (c n) x) ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
  obtain ⟨Mμ, _, hMμ⟩ := exists_ae_norm_le_of_compact_conull
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) hK hμK
  obtain ⟨Mν, _, hMν⟩ := exists_ae_norm_le_of_compact_conull
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) hL hνL
  obtain ⟨q, hq, _, hac, hmoment⟩ := exists_radialProjection_density_moment μ ν
    ht hs (lt_of_lt_of_le zero_lt_one (le_max_left 1 Cν))
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 Cμ))
    (hν.mono_constant (le_max_right 1 Cν))
    (hμ.mono_constant (le_max_right 1 Cμ)) hMν hMμ
  obtain ⟨c, hc, hsum, hmeas, hgeom⟩ := exists_dyadic_radial_moment_centers
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) hμK q hac
  exact ⟨q, _, c, hq, hmoment, hc, hsum, hmeas, hgeom⟩

/-- Actual integrable affine densities with summable successive errors give a positive-length
pinned distance set. This converts the explicit densities into the existing `L¹` limit theorem. -/
theorem exists_pin_of_integrable_affine_comparisons
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {E F : Set (EuclideanSpace ℝ (Fin 2))}
    (c : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (r : ℕ → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin 2) × ℝ → ℝ)
    (e : ℕ → ℝ≥0∞) {δ : ℝ}
    (hμE : 0 < (μ : Measure (EuclideanSpace ℝ (Fin 2))) E)
    (hνF : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Fᶜ = 0)
    (hδ : 0 < δ) (hc : ∀ n, Measurable (c n))
    (hr : Tendsto r atTop (𝓝 0)) (hrhalf : ∀ n, r n ≤ δ / 2)
    (hsource : ∀ n, ∀ᵐ p ∂((ν : Measure (EuclideanSpace ℝ (Fin 2))).prod
        (μ : Measure (EuclideanSpace ℝ (Fin 2)))), dist p.2 (c n p.2) ≤ r n)
    (hsep : ∀ n, ∀ᵐ p ∂((ν : Measure (EuclideanSpace ℝ (Fin 2))).prod
        (μ : Measure (EuclideanSpace ℝ (Fin 2)))), δ ≤ dist (c n p.2) p.1)
    (hf : ∀ n, Integrable (f n)
      ((ν : Measure (EuclideanSpace ℝ (Fin 2))).prod volume))
    (hdensity : ∀ n,
      (((ν : Measure (EuclideanSpace ℝ (Fin 2))).prod
        (μ : Measure (EuclideanSpace ℝ (Fin 2)))).map (affineJointDistanceMap (c n))) =
      ((ν : Measure (EuclideanSpace ℝ (Fin 2))).prod volume).withDensity
        (fun p ↦ ENNReal.ofReal (f n p)))
    (he : (∑' n, e n) < ∞)
    (hstep : ∀ n, (∫⁻ p, ENNReal.ofReal |f n p - f (n + 1) p|
      ∂((ν : Measure (EuclideanSpace ℝ (Fin 2))).prod volume)) ≤ e n) :
    ∃ y ∈ F, 0 < volume (pinnedDistances E y) := by
  let g n := (hf n).toL1 (f n)
  apply exists_mem_volume_pinnedDistances_pos_of_coherent_affineDistance
    μ ν c r g (Z := e) (K := 1) (eta := 1) hμE hνF hδ hc hr hsource hsep hrhalf
  · intro n
    rw [finiteMeasureOfL1Density_toMeasure]
    exact (hdensity n).trans (withDensity_congr_ae
      ((hf n).coeFn_toL1.mono fun p hp ↦ congrArg ENNReal.ofReal hp.symm))
  · exact ENNReal.one_ne_top
  · simpa only [ENNReal.rpow_one] using he.ne
  · intro n
    rw [one_mul, ENNReal.rpow_one, Integrable.edist_toL1_toL1]
    simpa only [edist_dist, Real.dist_eq] using hstep n

/-- Separated compact Frostman probabilities give a positive-length pinned distance set
when the source covering exponent is strictly below twice its Frostman exponent minus one. -/
theorem exists_pin_of_compact_frostman_upperBox
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {K L : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (hL : IsCompact L)
    (hμK : (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0)
    (hνL : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Lᶜ = 0)
    {s u Cμ Cν δ : ℝ} (hs : 1 < s) (hs₂ : s ≤ 2)
    (hCμ : 1 ≤ Cμ)
    (hμ : IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) s Cμ)
    (hν : IsFrostman (ν : Measure (EuclideanSpace ℝ (Fin 2))) s Cν)
    (hbox : HasUpperBoxBound K u) (hgap : u < 2 * s - 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hsep : ∀ x ∈ K, ∀ y ∈ L, δ ≤ dist x y) :
    ∃ y ∈ L, 0 < volume (pinnedDistances K y) := by
  classical
  let m := (μ : Measure (EuclideanSpace ℝ (Fin 2)))
  let v := (ν : Measure (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨q, B, c, hq, hB, hc, hmoment, hmeas, hgeom⟩ :=
    exists_compact_dyadic_radial_centers μ ν hK hL hμK hνL hs hs hμ hν
  obtain ⟨Cbox, I, hCbox, hI, hcard, hIae⟩ :=
    exists_positive_mass_cube_family m hμK hbox
  have hcover (n : ℕ) : ∀ᵐ x ∂m, x ∈ ⋃ k ∈ I n, dyadicCube n k :=
    (hIae n).mono fun x hx ↦ mem_iUnion₂.mpr
      ⟨cubeIndex n x, hx, mem_dyadicCube_cubeIndex n x⟩
  have hcenter (n : ℕ) (k : Fin 2 → ℤ) (hk : 0 < m (dyadicCube n k)) :
      c n k ∈ dyadicCube n k := (hc n k hk).1.1
  have hrad (n : ℕ) (k : Fin 2 → ℤ) (hk : 0 < m (dyadicCube n k)) :
      v.map (radialAngle (c n k)) =
        radialAngularMeasure.withDensity (radialProjectionDensity v (c n k)) := (hc n k hk).2
  have hsepcenter (n : ℕ) (k : Fin 2 → ℤ) (hk : 0 < m (dyadicCube n k)) :
      ∀ᵐ y ∂v, δ ≤ dist (c n k) y :=
    (ae_iff.mpr hνL).mono fun y hy ↦ hsep (c n k) (hc n k hk).1.2 y hy
  have hradac (n : ℕ) (k : Fin 2 → ℤ) (hk : 0 < m (dyadicCube n k)) :
      v.map (radialAngle (c n k)) ≪ (volume : Measure ℝ) := by
    rw [hrad n k hk]
    exact (withDensity_absolutelyContinuous _ _).trans
      (show radialAngularMeasure ≪ (volume : Measure ℝ) from
        Measure.absolutelyContinuous_restrict)
  have hcenterne (n : ℕ) (k : Fin 2 → ℤ) (hk : 0 < m (dyadicCube n k)) :
      ∀ᵐ y ∂v, c n k ≠ y :=
    (hsepcenter n k hk).mono fun _ hy ↦ dist_pos.mp (hδ.trans_le hy)
  let f n := dyadicAffineDensity m n (I n) (c n)
  have hdensity (n : ℕ) : (v.prod m).map (dyadicAffineMap n (c n)) =
      (v.prod volume).withDensity (fun p ↦ ENNReal.ofReal (f n p)) :=
    map_dyadicAffineMap_eq_withDensity m v hs hs₂ hμ n (I n) (c n) (hcover n)
      (fun k _ hk ↦ hradac n k (pos_iff_ne_zero.mpr hk))
      (fun k _ hk ↦ hcenterne n k (pos_iff_ne_zero.mpr hk))
  have hf (n : ℕ) : Integrable (f n) (v.prod volume) :=
    (integrable_dyadicAffineDensity_of_density m v n (I n) (c n) (hdensity n)).1
  let e (n : ℕ) := ∑ k ∈ I (n + 1), m (dyadicCube (n + 1) k) * ∫⁻ y, ∫⁻ t : ℝ,
    ENNReal.ofReal |affineDistanceDensity
      (normalizedRestrict m (dyadicCube (n + 1) k)) (c (n + 1) k) y t -
    affineDistanceDensity (normalizedRestrict m (dyadicCube (n + 1) k))
      (c n (ancestor 1 k)) y t| ∂volume ∂v
  have hstep (n : ℕ) :
      (∫⁻ p, ENNReal.ofReal |f n p - f (n + 1) p| ∂v.prod volume) ≤ e n := by
    have hp (k : Fin 2 → ℤ) (hk : m (dyadicCube (n + 1) k) ≠ 0) :
        0 < m (dyadicCube n (ancestor 1 k)) :=
      (pos_iff_ne_zero.mpr hk).trans_le (measure_mono (dyadicCube_subset_parent n k))
    have h := dyadicAffineDensity_succ_sub_L1_le m v hs hs₂ hμ n (I (n + 1))
      (c n) (c (n + 1)) (measurable_dyadicAffineDensity m n (I n) (c n))
      (dyadicAffineDensity_nonneg m n (I n) (c n)) (hdensity n) (hcover (n + 1))
      (fun k _ hk ↦ hradac n _ (hp k hk))
      (fun k _ hk ↦ hcenterne n _ (hp k hk))
    change (∫⁻ p, ENNReal.ofReal |f (n + 1) p - f n p| ∂v.prod volume) ≤ e n at h
    conv_lhs at h =>
      arg 2
      ext p
      rw [abs_sub_comm]
    exact h
  obtain ⟨n₀, hn₀⟩ := exists_dyadic_cube_diameter_le_separation hδ
  have hcard' (n : ℕ) : ((I (n + 1)).card : ℝ) ≤
      (4 * Cbox * (2 : ℝ) ^ u) * (2 : ℝ) ^ (u * ((n : ℝ) + 1)) := by
    refine (hcard (n + 1)).trans_eq ?_
    push_cast
    rw [show ((n : ℝ) + 1 + 1) * u = u + u * ((n : ℝ) + 1) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring
  have he : (∑' n, e (n + n₀)) < ∞ := by
    apply lt_top_iff_ne_top.mpr
    apply tsum_coherent_errors_from_ne_top (by positivity) hgap hq
      (coherentAffineCoefficient_ne_top s Cμ δ) hB.ne n₀
      (fun n ↦ (I (n + 1)).card) e (fun n _ ↦ hcard' n)
    intro n hn
    exact sum_dyadic_affine_errors_le m v hs hs₂ hCμ hμ hδ hδ₁ hq.le c hcenter
      hrad hsepcenter B hmoment n (I (n + 1))
      (fun k hk ↦ (hI (n + 1) k).mp hk) (hn₀ n hn)
      (coherentAngularCutoff s u n)
      (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
  have hmassK : m K = 1 := by
    have h := measure_add_measure_compl (μ := m) hK.measurableSet
    have hmcompl : m Kᶜ = 0 := hμK
    simpa only [hmcompl, add_zero, measure_univ] using h
  have hproduct (n : ℕ) := ae_joint_dyadic_center_geometry m v hνL hsep
    (fun j ↦ dyadicCenterMap j (c j)) hmeas hgeom (n + n₀)
  apply exists_pin_of_integrable_affine_comparisons μ ν
    (fun n ↦ dyadicCenterMap (n + n₀) (c (n + n₀)))
    (fun n ↦ Real.sqrt 2 / (2 : ℝ) ^ (n + n₀)) (fun n ↦ f (n + n₀))
    (fun n ↦ e (n + n₀)) (by rw [hmassK]; exact zero_lt_one) hνL hδ
    (fun n ↦ hmeas (n + n₀)) (tendsto_shifted_dyadic_cube_diameter n₀)
    (fun n ↦ (hn₀ (n + n₀) (by omega)).trans (by linarith))
    (fun n ↦ (hproduct n).1) (fun n ↦ (hproduct n).2)
    (fun n ↦ hf (n + n₀)) (fun n ↦ hdensity (n + n₀)) he
  intro n
  simpa only [Nat.add_right_comm n 1 n₀] using hstep (n + n₀)

end FalconerPacking
