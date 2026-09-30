/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.GeometricCapacity
import FalconerPacking.RadialProjectionKernel

/-!
# Frostman measures do not charge lines

A planar Frostman measure of exponent greater than one vanishes on every Lipschitz curve
parametrized by the real line. In particular the branch cut and diagonal of any fixed radial
angle map are null, so that map is continuous almost everywhere for the Frostman measure.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FalconerPacking

/-- A Frostman measure of exponent greater than one vanishes on every real Lipschitz curve. -/
theorem measure_range_eq_zero_of_isFrostman_lipschitz
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ}
    (hs : 1 < s) (hfr : IsFrostman μ s C)
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} {L : ℝ≥0} (hf : LipschitzWith L f) :
    μ (range f) = 0 := by
  by_contra hpos
  have hlo := le_dimH_of_isFrostman_measure_pos (by linarith : 0 < s) hfr
    (pos_iff_ne_zero.2 hpos)
  have hup : dimH (range f) ≤ 1 := by simpa only [Real.dimH_univ] using hf.dimH_range_le
  exact (ENNReal.one_lt_ofReal.2 hs).not_ge (hlo.trans hup)

/-- Every parametrized affine line, including a degenerate line consisting of one point, is null. -/
theorem measure_affine_line_eq_zero_of_isFrostman
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ}
    (hs : 1 < s) (hfr : IsFrostman μ s C)
    (a v : EuclideanSpace ℝ (Fin 2)) :
    μ (range (fun t : ℝ ↦ a + t • v)) = 0 := by
  apply measure_range_eq_zero_of_isFrostman_lipschitz hs hfr (L := ‖v‖₊)
  apply LipschitzWith.of_dist_le_mul
  intro t u
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
    Real.norm_eq_abs, coe_nnnorm, mul_comm]
  exact le_rfl

/-- The diagonal is null for every positive-exponent Frostman measure. -/
theorem ae_ne_of_isFrostman
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ}
    (hs : 0 < s) (hfr : IsFrostman μ s C) (x : EuclideanSpace ℝ (Fin 2)) :
    ∀ᵐ y ∂μ, y ≠ x := by
  simpa only [ae_iff, not_not, setOf_eq_eq_singleton] using
    measure_singleton_eq_zero_of_isFrostman hs hfr x

/-- The real-axis preimage of the radial coordinate is contained in one actual affine line. -/
theorem mem_affine_line_of_radialCoordinate_im_eq_zero
    (x y : EuclideanSpace ℝ (Fin 2))
    (him : (Complex.orthonormalBasisOneI.repr.symm (x - y)).im = 0) :
    y ∈ range (fun t : ℝ ↦ x + t • Complex.orthonormalBasisOneI.repr (1 : ℂ)) := by
  let z := Complex.orthonormalBasisOneI.repr.symm (x - y)
  have hz : (z.re : ℂ) = z := by
    simpa only [z, him, Complex.ofReal_zero, zero_mul, add_zero] using Complex.re_add_im z
  have hvec : z.re • Complex.orthonormalBasisOneI.repr (1 : ℂ) = x - y := by
    rw [← map_smul, Complex.real_smul, mul_one, hz]
    exact Complex.orthonormalBasisOneI.repr.apply_symm_apply (x - y)
  refine ⟨-z.re, ?_⟩
  dsimp only
  rw [neg_smul, hvec]
  abel

/-- Outside the affine line containing its cut, the principal radial angle is continuous. -/
theorem continuousAt_radialAngle_of_not_mem_affine_line
    {x y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∉ range (fun t : ℝ ↦ x + t • Complex.orthonormalBasisOneI.repr (1 : ℂ))) :
    ContinuousAt (radialAngle x) y := by
  have him : (Complex.orthonormalBasisOneI.repr.symm (x - y)).im ≠ 0 :=
    fun h ↦ hy (mem_affine_line_of_radialCoordinate_im_eq_zero x y h)
  have harg := Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inr him))
  have hc : Continuous (fun y ↦ Complex.orthonormalBasisOneI.repr.symm (x - y)) := by
    fun_prop
  exact harg.comp (f := fun z ↦ Complex.orthonormalBasisOneI.repr.symm (x - z))
    hc.continuousAt

/-- For every fixed pin, the principal radial angle is continuous almost everywhere under
an exponent-greater-than-one Frostman measure. This includes its branch cut and diagonal. -/
theorem ae_continuousAt_radialAngle_of_isFrostman
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ}
    (hs : 1 < s) (hfr : IsFrostman μ s C) (x : EuclideanSpace ℝ (Fin 2)) :
    ∀ᵐ y ∂μ, ContinuousAt (radialAngle x) y := by
  have hline := measure_affine_line_eq_zero_of_isFrostman hs hfr x
    (Complex.orthonormalBasisOneI.repr (1 : ℂ))
  have hout : ∀ᵐ y ∂μ,
      y ∉ range (fun t : ℝ ↦ x + t • Complex.orthonormalBasisOneI.repr (1 : ℂ)) := by
    simpa only [ae_iff, not_not, setOf_mem_eq] using hline
  exact hout.mono fun _ hy ↦ continuousAt_radialAngle_of_not_mem_affine_line hy

end FalconerPacking
