/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AffineDistanceTruncation
import FalconerPacking.DyadicComparisonSums

/-!
# Summable whole-pin coherent comparison errors

Regrouping the parent moments and summing square-root child masses produces the finite
comparison bound. The strict covering gap then gives two geometric series after the
angular threshold is chosen as a fixed power of the dyadic scale.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- Summing the whole-pin child bounds costs one square root of the number of children and
twice the moment bound, once for children and once for their parents. -/
theorem sum_coherent_child_errors_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (n : ℕ) (I : Finset (Fin 2 → ℤ)) (E : (Fin 2 → ℤ) → ℝ≥0∞)
    (H : ℕ → (Fin 2 → ℤ) → ℝ≥0∞) (L A B : ℝ≥0∞) (q : ℝ)
    (hH : ∀ j (J : Finset (Fin 2 → ℤ)),
      ∑ k ∈ J, μ (dyadicCube j k) * H j k ≤ B)
    (hE : ∀ k ∈ I, E k ≤ L * μ (dyadicCube (n + 1) k) ^ (1 / 2 : ℝ) +
      2 * A ^ (1 - q) * μ (dyadicCube (n + 1) k) *
        (H (n + 1) k + H n (ancestor 1 k))) :
    ∑ k ∈ I, E k ≤ L * (I.card : ℝ≥0∞) ^ (1 / 2 : ℝ) + 4 * B * A ^ (1 - q) := by
  have hparent := (sum_dyadic_child_parent_weight_le μ n I (H n)).trans
    (hH n (I.image (ancestor 1)))
  calc
    _ ≤ ∑ k ∈ I, (L * μ (dyadicCube (n + 1) k) ^ (1 / 2 : ℝ) +
        2 * A ^ (1 - q) * μ (dyadicCube (n + 1) k) *
          (H (n + 1) k + H n (ancestor 1 k))) := Finset.sum_le_sum hE
    _ = L * (∑ k ∈ I, μ (dyadicCube (n + 1) k) ^ (1 / 2 : ℝ)) +
        2 * A ^ (1 - q) * ((∑ k ∈ I, μ (dyadicCube (n + 1) k) * H (n + 1) k) +
          ∑ k ∈ I, μ (dyadicCube (n + 1) k) * H n (ancestor 1 k)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ L * (I.card : ℝ≥0∞) ^ (1 / 2 : ℝ) + 2 * A ^ (1 - q) * (B + B) :=
      add_le_add (mul_le_mul_right (sum_sqrt_dyadic_mass_le μ (n + 1) I) L)
        (mul_le_mul_right (add_le_add (hH (n + 1) I) hparent) _)
    _ = _ := by ring

/-- The cutoff selected from the strict covering gap. -/
def coherentAngularCutoff (s u : ℝ) (n : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (((2 * s - 1 - u) / 2) * (n : ℝ))

/-- The retained and discarded comparison terms after simplifying their scale exponents. -/
def coherentStepMajorant (s u q : ℝ) (K B : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  K * (2 : ℝ≥0∞) ^ ((-(2 * s - 1 - u) / 4) * (n : ℝ)) +
    4 * B * (2 : ℝ≥0∞) ^ (((2 * s - 1 - u) * (1 - q) / 2) * (n : ℝ))

/-- The error majorant has an explicit sum of two geometric series. -/
theorem tsum_coherentStepMajorant (s u q : ℝ) (K B : ℝ≥0∞) :
    ∑' n, coherentStepMajorant s u q K B n =
      K * (1 - (2 : ℝ≥0∞) ^ (-(2 * s - 1 - u) / 4))⁻¹ +
        4 * B * (1 - (2 : ℝ≥0∞) ^ ((2 * s - 1 - u) * (1 - q) / 2))⁻¹ := by
  simp_rw [coherentStepMajorant, ENNReal.rpow_mul, ENNReal.rpow_natCast]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    ENNReal.tsum_geometric, ENNReal.tsum_geometric]

/-- Both error series are finite under precisely the strict covering gap and `q>1`. -/
theorem tsum_coherentStepMajorant_ne_top {s u q : ℝ} {K B : ℝ≥0∞}
    (hgap : u < 2 * s - 1) (hq : 1 < q) (hK : K ≠ ∞) (hB : B ≠ ∞) :
    (∑' n, coherentStepMajorant s u q K B n) ≠ ∞ := by
  have hfirst : (2 : ℝ≥0∞) ^ (-(2 * s - 1 - u) / 4) < 1 :=
    ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsecond : (2 : ℝ≥0∞) ^ ((2 * s - 1 - u) * (1 - q) / 2) < 1 := by
    apply ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith))
      (by norm_num)
  rw [tsum_coherentStepMajorant]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top hK (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hfirst).ne'),
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hB)
        (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hsecond).ne')⟩

/-- The geometric source radius contributes its exact power of the dyadic scale. -/
theorem coherent_radius_rpow (p : ℝ) (n : ℕ) :
    ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ p) =
      ENNReal.ofReal ((Real.sqrt 2) ^ p) * (2 : ℝ≥0∞) ^ (-p * (n : ℝ)) := by
  have he : (Real.sqrt 2 / (2 : ℝ) ^ n) ^ p =
      (Real.sqrt 2) ^ p * (2 : ℝ) ^ (-p * (n : ℝ)) := by
    rw [Real.div_rpow (Real.sqrt_nonneg _) (by positivity),
      ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring
  rw [he, ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hpow := ENNReal.ofReal_rpow_of_pos (p := -p * (n : ℝ))
    (by norm_num : (0 : ℝ) < 2)
  simpa using hpow.symm

/-- The fixed coefficient after using the covering-number bound. -/
def coherentStepCoefficient (s u : ℝ) (K Cbox : ℝ≥0∞) : ℝ≥0∞ :=
  K * Cbox ^ (1 / 2 : ℝ) * ENNReal.ofReal ((Real.sqrt 2) ^ (s - 1 / 2)) *
    (2 : ℝ≥0∞) ^ (u / 2)

/-- Every factor in the fixed coefficient is finite when the original constants are finite. -/
theorem coherentStepCoefficient_ne_top (s u : ℝ) {K Cbox : ℝ≥0∞}
    (hK : K ≠ ∞) (hbox : Cbox ≠ ∞) : coherentStepCoefficient s u K Cbox ≠ ∞ := by
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hbox)) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))

/-- Combining the cutoff, curvature radius, and covering bound leaves the quarter-gap decay. -/
theorem coherent_retained_scale_identity (s u : ℝ) (K Cbox : ℝ≥0∞) (n : ℕ) :
    K * coherentAngularCutoff s u n ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2)) *
          (Cbox * (2 : ℝ≥0∞) ^ (u * ((n : ℝ) + 1))) ^ (1 / 2 : ℝ) =
      coherentStepCoefficient s u K Cbox *
        (2 : ℝ≥0∞) ^ ((-(2 * s - 1 - u) / 4) * (n : ℝ)) := by
  rw [coherentAngularCutoff, coherent_radius_rpow,
    ENNReal.mul_rpow_of_nonneg Cbox _ (by norm_num)]
  simp_rw [← ENNReal.rpow_mul]
  let a := (((2 * s - 1 - u) / 2) * (n : ℝ)) * (1 / 2)
  let b := -(s - 1 / 2) * (n : ℝ)
  let c := (u * ((n : ℝ) + 1)) * (1 / 2)
  have he : a + b + c = u / 2 + (-(2 * s - 1 - u) / 4) * (n : ℝ) := by
    dsimp only [a, b, c]
    ring
  calc
    _ = (K * Cbox ^ (1 / 2 : ℝ) * ENNReal.ofReal ((Real.sqrt 2) ^ (s - 1 / 2))) *
        ((2 : ℝ≥0∞) ^ a * (2 : ℝ≥0∞) ^ b * (2 : ℝ≥0∞) ^ c) := by ring
    _ = (K * Cbox ^ (1 / 2 : ℝ) * ENNReal.ofReal ((Real.sqrt 2) ^ (s - 1 / 2))) *
        (2 : ℝ≥0∞) ^ (a + b + c) := by
      rw [ENNReal.rpow_add (a + b) c (by norm_num) (by norm_num),
        ENNReal.rpow_add a b (by norm_num) (by norm_num)]
    _ = _ := by
      rw [he, ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      unfold coherentStepCoefficient
      ring

/-- The discarded term has the geometric decay supplied by the angular moment exponent. -/
theorem coherent_discarded_scale_identity (s u q : ℝ) (n : ℕ) :
    coherentAngularCutoff s u n ^ (1 - q) =
      (2 : ℝ≥0∞) ^ (((2 * s - 1 - u) * (1 - q) / 2) * (n : ℝ)) := by
  rw [coherentAngularCutoff, ← ENNReal.rpow_mul]
  congr 1
  ring

/-- A real covering-number estimate supplies the explicit summable comparison majorant. -/
theorem coherent_cardinality_step_le
    (s u q Cbox : ℝ) (hbox : 0 ≤ Cbox) (K B : ℝ≥0∞) (n N : ℕ)
    (hcard : (N : ℝ) ≤ Cbox * (2 : ℝ) ^ (u * ((n : ℝ) + 1))) :
    K * coherentAngularCutoff s u n ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2)) *
          (N : ℝ≥0∞) ^ (1 / 2 : ℝ) + 4 * B * coherentAngularCutoff s u n ^ (1 - q) ≤
      coherentStepMajorant s u q (coherentStepCoefficient s u K (ENNReal.ofReal Cbox)) B n := by
  have hcard' : (N : ℝ≥0∞) ≤ ENNReal.ofReal Cbox *
      (2 : ℝ≥0∞) ^ (u * ((n : ℝ) + 1)) := by
    have h := ENNReal.ofReal_le_ofReal hcard
    rw [ENNReal.ofReal_natCast, ENNReal.ofReal_mul hbox,
      ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    simpa using h
  calc
    _ ≤ K * coherentAngularCutoff s u n ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2)) *
          (ENNReal.ofReal Cbox * (2 : ℝ≥0∞) ^ (u * ((n : ℝ) + 1))) ^ (1 / 2 : ℝ) +
        4 * B * coherentAngularCutoff s u n ^ (1 - q) :=
      add_le_add (mul_le_mul_right
        (ENNReal.rpow_le_rpow hcard' (by norm_num : (0 : ℝ) ≤ 1 / 2)) _) le_rfl
    _ = _ := by
      rw [coherent_retained_scale_identity, coherent_discarded_scale_identity]
      rfl

/-- The numerical coherent error sequence has finite sum under the strict dimension gap. -/
theorem tsum_coherent_errors_ne_top
    {s u q Cbox : ℝ} (hbox : 0 ≤ Cbox) (hgap : u < 2 * s - 1) (hq : 1 < q)
    {K B : ℝ≥0∞} (hK : K ≠ ∞) (hB : B ≠ ∞)
    (N : ℕ → ℕ) (E : ℕ → ℝ≥0∞)
    (hcard : ∀ n, (N n : ℝ) ≤ Cbox * (2 : ℝ) ^ (u * ((n : ℝ) + 1)))
    (hE : ∀ n, E n ≤ K * coherentAngularCutoff s u n ^ (1 / 2 : ℝ) *
      ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2)) *
        (N n : ℝ≥0∞) ^ (1 / 2 : ℝ) + 4 * B * coherentAngularCutoff s u n ^ (1 - q)) :
    (∑' n, E n) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (tsum_coherentStepMajorant_ne_top hgap hq
      (coherentStepCoefficient_ne_top s u hK ENNReal.ofReal_ne_top) hB)
  exact ENNReal.tsum_le_tsum fun n ↦ (hE n).trans
    (coherent_cardinality_step_le s u q Cbox hbox K B n (N n) (hcard n))

/-- The summability conclusion can start at any sufficiently fine scale; no bound is
required for the finitely many earlier comparison errors. -/
theorem tsum_coherent_errors_from_ne_top
    {s u q Cbox : ℝ} (hbox : 0 ≤ Cbox) (hgap : u < 2 * s - 1) (hq : 1 < q)
    {K B : ℝ≥0∞} (hK : K ≠ ∞) (hB : B ≠ ∞)
    (n₀ : ℕ) (N : ℕ → ℕ) (E : ℕ → ℝ≥0∞)
    (hcard : ∀ n, n₀ ≤ n → (N n : ℝ) ≤ Cbox * (2 : ℝ) ^ (u * ((n : ℝ) + 1)))
    (hE : ∀ n, n₀ ≤ n → E n ≤ K * coherentAngularCutoff s u n ^ (1 / 2 : ℝ) *
      ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2)) *
        (N n : ℝ≥0∞) ^ (1 / 2 : ℝ) + 4 * B * coherentAngularCutoff s u n ^ (1 - q)) :
    (∑' n, E (n + n₀)) ≠ ∞ := by
  let F := coherentStepMajorant s u q
    (coherentStepCoefficient s u K (ENNReal.ofReal Cbox)) B
  have hsum : (∑' n, F n) ≠ ∞ := tsum_coherentStepMajorant_ne_top hgap hq
    (coherentStepCoefficient_ne_top s u hK ENNReal.ofReal_ne_top) hB
  apply ne_top_of_le_ne_top hsum
  calc
    _ ≤ ∑' n, F (n + n₀) := ENNReal.tsum_le_tsum fun n ↦
      (hE (n + n₀) (by omega)).trans
        (coherent_cardinality_step_le s u q Cbox hbox K B (n + n₀) (N (n + n₀))
          (hcard (n + n₀) (by omega)))
    _ ≤ ∑' n, F n := ENNReal.tsum_comp_le_tsum_of_injective
      (fun _ _ h ↦ Nat.add_right_cancel h) F

/-- Combining the child comparison, parent regrouping, covering estimate and geometric
summation gives the exact finite sum required for the coherent density limit. -/
theorem tsum_sum_coherent_child_errors_ne_top
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {s u q Cbox : ℝ} (hbox : 0 ≤ Cbox) (hgap : u < 2 * s - 1) (hq : 1 < q)
    {K B : ℝ≥0∞} (hK : K ≠ ∞) (hB : B ≠ ∞)
    (n₀ : ℕ) (I : ℕ → Finset (Fin 2 → ℤ)) (E H : ℕ → (Fin 2 → ℤ) → ℝ≥0∞)
    (hH : ∀ j (J : Finset (Fin 2 → ℤ)),
      ∑ k ∈ J, μ (dyadicCube j k) * H j k ≤ B)
    (hcard : ∀ n, n₀ ≤ n → ((I n).card : ℝ) ≤
      Cbox * (2 : ℝ) ^ (u * ((n : ℝ) + 1)))
    (hE : ∀ n, n₀ ≤ n → ∀ k ∈ I n, E n k ≤
      K * coherentAngularCutoff s u n ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2)) *
          μ (dyadicCube (n + 1) k) ^ (1 / 2 : ℝ) +
      2 * coherentAngularCutoff s u n ^ (1 - q) * μ (dyadicCube (n + 1) k) *
        (H (n + 1) k + H n (ancestor 1 k))) :
    (∑' n, ∑ k ∈ I (n + n₀), E (n + n₀) k) ≠ ∞ := by
  apply tsum_coherent_errors_from_ne_top hbox hgap hq hK hB n₀
    (fun n ↦ (I n).card) (fun n ↦ ∑ k ∈ I n, E n k) hcard
  intro n hn
  exact sum_coherent_child_errors_le μ n (I n) (E n) H
    (K * coherentAngularCutoff s u n ^ (1 / 2 : ℝ) *
      ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2)))
    (coherentAngularCutoff s u n) B q hH (hE n hn)

end FalconerPacking
