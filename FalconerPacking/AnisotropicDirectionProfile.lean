/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircleCapGeometry
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!+# Smooth extension of the anisotropically rescaled direction map

The quotient of the direction displacement by the angular scale extends smoothly to scale zero.
Rationalizing its radial coordinate exposes this extension and gives uniform derivatives on
every compact rectangle separated from the zero radial coordinate.
-/

@[expose] public section

noncomputable section

open Set Metric
open scoped ContDiff

namespace FalconerPacking

/-- The norm of the frequency vector in radial units. -/
def anisotropicDirectionNorm (p : ℝ × EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.sqrt ((p.2 1) ^ 2 + p.1 ^ 2 * (p.2 0) ^ 2)

/-- The smoothly extended direction displacement divided by the angular scale. -/
def anisotropicDirectionProfile (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p.2 0 / anisotropicDirectionNorm p,
    -(p.1 * (p.2 0) ^ 2) /
      (anisotropicDirectionNorm p * (anisotropicDirectionNorm p + p.2 1))]

theorem anisotropicDirectionNorm_pos {p : ℝ × EuclideanSpace ℝ (Fin 2)}
    (hp : 0 < p.2 1) : 0 < anisotropicDirectionNorm p := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (p.1 * p.2 0)]

/-- The rationalized direction profile is smooth even when its scale parameter is zero. -/
theorem contDiffAt_anisotropicDirectionProfile {p : ℝ × EuclideanSpace ℝ (Fin 2)}
    (hp : 0 < p.2 1) : ContDiffAt ℝ ∞ anisotropicDirectionProfile p := by
  have h₀ : ContDiffAt ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 2) ↦ q.2 0) p := by
    fun_prop
  have h₁ : ContDiffAt ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin 2) ↦ q.2 1) p := by
    fun_prop
  have hnorm : ContDiffAt ℝ ∞ anisotropicDirectionNorm p :=
    ((h₁.pow 2).add ((contDiffAt_fst.pow 2).mul (h₀.pow 2))).sqrt
      (by nlinarith [sq_nonneg (p.1 * p.2 0)])
  have hpos := anisotropicDirectionNorm_pos hp
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · exact h₀.div hnorm hpos.ne'
  · exact (contDiffAt_fst.mul (h₀.pow 2)).neg.div
      (hnorm.mul (hnorm.add h₁)) (mul_pos hpos (by linarith)).ne'

/-- The direction displacement identity includes the limiting zero-scale case. -/
theorem anisotropicDirectionProfile_identity (ε : ℝ) (z : EuclideanSpace ℝ (Fin 2))
    (hz : 0 < z 1) :
    ‖(WithLp.toLp 2 ![ε * z 0, z 1] : EuclideanSpace ℝ (Fin 2))‖⁻¹ •
        WithLp.toLp 2 ![ε * z 0, z 1] =
      WithLp.toLp 2 ![0, 1] + ε • anisotropicDirectionProfile (ε, z) := by
  have hq := anisotropicDirectionNorm_pos (p := (ε, z)) hz
  have hs : anisotropicDirectionNorm (ε, z) ^ 2 = (z 1) ^ 2 + ε ^ 2 * (z 0) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hn : ‖(WithLp.toLp 2 ![ε * z 0, z 1] : EuclideanSpace ℝ (Fin 2))‖ =
      anisotropicDirectionNorm (ε, z) := by
    have he := EuclideanSpace.real_norm_sq_eq
      (WithLp.toLp 2 ![ε * z 0, z 1] : EuclideanSpace ℝ (Fin 2))
    rw [Fin.sum_univ_two] at he
    change _ = (ε * z 0) ^ 2 + (z 1) ^ 2 at he
    nlinarith [norm_nonneg (WithLp.toLp 2 ![ε * z 0, z 1] : EuclideanSpace ℝ (Fin 2))]
  rw [hn]
  ext i
  fin_cases i
  · change (anisotropicDirectionNorm (ε, z))⁻¹ * (ε * z 0) =
      0 + ε * (z 0 / anisotropicDirectionNorm (ε, z))
    ring
  · change (anisotropicDirectionNorm (ε, z))⁻¹ * z 1 =
      1 + ε * (-(ε * (z 0) ^ 2) /
        (anisotropicDirectionNorm (ε, z) * (anisotropicDirectionNorm (ε, z) + z 1)))
    have he : anisotropicDirectionNorm (ε, z) + z 1 ≠ 0 := by positivity
    field_simp
    nlinarith

/-- All joint parameter derivatives are uniformly bounded on fixed separated rectangles. -/
theorem anisotropicDirectionProfile_derivative_bound {c : ℝ} (hc : 0 < c)
    (M : ℝ) (m : ℕ) :
    ∃ C > 0, ∀ p : ℝ × EuclideanSpace ℝ (Fin 2), ‖p‖ ≤ M → c ≤ p.2 1 →
      ‖iteratedFDeriv ℝ m anisotropicDirectionProfile p‖ ≤ C := by
  let Ω := {p : ℝ × EuclideanSpace ℝ (Fin 2) | 0 < p.2 1}
  have hΩ : IsOpen Ω := isOpen_lt continuous_const (by fun_prop)
  have hf : ContDiffOn ℝ ∞ anisotropicDirectionProfile Ω :=
    fun p hp ↦ (contDiffAt_anisotropicDirectionProfile hp).contDiffWithinAt
  have hcont : ContinuousOn (iteratedFDeriv ℝ m anisotropicDirectionProfile) Ω := by
    apply (hf.continuousOn_iteratedFDerivWithin (mod_cast le_top) hΩ.uniqueDiffOn).congr
    intro p hp
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
      ((contDiffAt_anisotropicDirectionProfile hp).of_le (mod_cast le_top)) hp).symm
  let K := closedBall (0 : ℝ × EuclideanSpace ℝ (Fin 2)) M ∩ {p | c ≤ p.2 1}
  have hK : IsCompact K := (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const (by fun_prop))
  have hsub : K ⊆ Ω := fun p hp ↦ hc.trans_le hp.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro p hp hpc
  exact (hC p ⟨by simpa only [mem_closedBall, dist_zero_right] using hp, hpc⟩).trans
    (by linarith [le_max_left C 0])

end FalconerPacking
