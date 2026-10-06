/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.InitialRetainedEnergy

/-!
# Actual Schwartz sources selected by the pin cube

A finite dyadic partition gives a jointly measurable source family. Its nonnegative
observables integrate exactly as the sum of the cell integrals, with no count of cells.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical SchwartzMap
open scoped ENNReal

namespace FalconerPacking

/-- The source assigned to the pin's unique dyadic cube, and zero outside the finite family. -/
def dyadicSchwartzFamily (n : ℕ) (I : Finset (Fin 2 → ℤ))
    (f : (Fin 2 → ℤ) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  ∑ Q ∈ I, if y ∈ dyadicCube n Q then f Q else 0

theorem dyadicSchwartzFamily_of_mem {n : ℕ} {I : Finset (Fin 2 → ℤ)}
    (f : (Fin 2 → ℤ) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {Q : Fin 2 → ℤ} (hQ : Q ∈ I) {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ dyadicCube n Q) : dyadicSchwartzFamily n I f y = f Q := by
  unfold dyadicSchwartzFamily
  rw [Finset.sum_eq_single_of_mem Q hQ]
  · simp only [if_pos hy]
  · intro P _ hPQ
    exact if_neg (fun hyP ↦ Set.disjoint_left.mp (dyadicCube_disjoint hPQ) hyP hy)

theorem dyadicSchwartzFamily_of_notMem {n : ℕ} {I : Finset (Fin 2 → ℤ)}
    (f : (Fin 2 → ℤ) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : ∀ Q ∈ I, y ∉ dyadicCube n Q) :
    dyadicSchwartzFamily n I f y = 0 := by
  apply Finset.sum_eq_zero
  intro Q hQ
  exact if_neg (hy Q hQ)

/-- Joint measurability follows from the actual finite cube choices and Schwartz continuity. -/
theorem measurable_dyadicSchwartzFamily (n : ℕ) (I : Finset (Fin 2 → ℤ))
    (f : (Fin 2 → ℤ) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      dyadicSchwartzFamily n I f p.1 p.2) := by
  have he (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
      dyadicSchwartzFamily n I f p.1 p.2 =
        ∑ Q ∈ I, (dyadicCube n Q ×ˢ univ).indicator (fun p ↦ f Q p.2) p := by
    simp only [dyadicSchwartzFamily, sum_apply, indicator_apply, mem_prod, mem_univ, and_true]
    apply Finset.sum_congr rfl
    intro Q _
    split_ifs <;> rfl
  simp_rw [he]
  exact Finset.measurable_sum I (fun Q _ ↦
    ((f Q).continuous.measurable.comp measurable_snd).indicator
      ((measurableSet_dyadicCube n Q).prod MeasurableSet.univ))

/-- Every nonnegative observable vanishing at the zero source has exact cellwise integration. -/
theorem lintegral_dyadicSchwartzFamily
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ) (I : Finset (Fin 2 → ℤ))
    (f : (Fin 2 → ℤ) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (Φ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (hzero : ∀ y, Φ 0 y = 0) (hΦ : ∀ Q ∈ I, Measurable (Φ (f Q))) :
    (∫⁻ y, Φ (dyadicSchwartzFamily n I f y) y ∂σ) =
      ∑ Q ∈ I, ∫⁻ y in dyadicCube n Q, Φ (f Q) y ∂σ := by
  have he (y : EuclideanSpace ℝ (Fin 2)) : Φ (dyadicSchwartzFamily n I f y) y =
      ∑ Q ∈ I, (dyadicCube n Q).indicator (Φ (f Q)) y := by
    by_cases hy : ∃ Q ∈ I, y ∈ dyadicCube n Q
    · obtain ⟨Q, hQ, hyQ⟩ := hy
      rw [dyadicSchwartzFamily_of_mem f hQ hyQ, Finset.sum_eq_single_of_mem Q hQ]
      · exact (indicator_of_mem hyQ _).symm
      · intro P _ hPQ
        exact indicator_of_notMem
          (fun hyP ↦ Set.disjoint_left.mp (dyadicCube_disjoint hPQ) hyP hyQ) _
    · have hy' : ∀ Q ∈ I, y ∉ dyadicCube n Q := by simpa only [not_exists, not_and] using hy
      rw [dyadicSchwartzFamily_of_notMem f hy', hzero]
      symm
      apply Finset.sum_eq_zero
      intro Q hQ
      exact indicator_of_notMem (hy' Q hQ) _
  simp_rw [he]
  rw [lintegral_finsetSum I (fun Q hQ ↦ (hΦ Q hQ).indicator (measurableSet_dyadicCube n Q))]
  exact Finset.sum_congr rfl (fun Q _ ↦ lintegral_indicator (measurableSet_dyadicCube n Q) _)

/-- The finite choice preserves every common spatial support bound. -/
theorem support_dyadicSchwartzFamily_subset (n : ℕ) (I : Finset (Fin 2 → ℤ))
    (f : (Fin 2 → ℤ) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {X : Set (EuclideanSpace ℝ (Fin 2))} (hf : ∀ Q ∈ I, Function.support (f Q) ⊆ X)
    (y : EuclideanSpace ℝ (Fin 2)) : Function.support (dyadicSchwartzFamily n I f y) ⊆ X := by
  by_cases hy : ∃ Q ∈ I, y ∈ dyadicCube n Q
  · obtain ⟨Q, hQ, hyQ⟩ := hy
    rw [dyadicSchwartzFamily_of_mem f hQ hyQ]
    exact hf Q hQ
  · have hy' : ∀ Q ∈ I, y ∉ dyadicCube n Q := by simpa only [not_exists, not_and] using hy
    rw [dyadicSchwartzFamily_of_notMem f hy']
    simp

end FalconerPacking
