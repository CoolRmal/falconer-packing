/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicInitialReconstruction

/-!
# Initial reconstruction for the actual remote strips of a pin cell

The remote selection is the complement of meeting the fourfold source packet strip.
For all sufficiently large annuli its margin discharges every remote-decay hypothesis.
-/

noncomputable section

open MeasureTheory Set Function Filter Classical
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The actual remote strips of a pin cell, within the constructed finite packet family. -/
def initialCellRemoteIndices
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (w : ℝ) (N j : ℕ) (Q : Set (EuclideanSpace ℝ (Fin 2))) : Finset ℤ :=
  (sourceWavePacketIndices χ hχ w).filter fun k ↦
    Disjoint Q (packetSourceStrip (sourceWavePacketNormal N j) (w * k) (4 * w))

theorem initialCellRemoteIndices_subset
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (w : ℝ) (N j : ℕ) (Q : Set (EuclideanSpace ℝ (Fin 2))) :
    initialCellRemoteIndices χ hχ w N j Q ⊆ sourceWavePacketIndices χ hχ w :=
  Finset.filter_subset _ _

theorem mem_initialCellRemoteIndices_iff
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (w : ℝ) (N j : ℕ) (Q : Set (EuclideanSpace ℝ (Fin 2))) (k : ℤ) :
    k ∈ initialCellRemoteIndices χ hχ w N j Q ↔
      k ∈ sourceWavePacketIndices χ hχ w ∧
        ¬(Q ∩ packetSourceStrip (sourceWavePacketNormal N j) (w * k) (4 * w)).Nonempty := by
  rw [initialCellRemoteIndices, Finset.mem_filter]
  simp only [Set.disjoint_iff_inter_eq_empty, Set.not_nonempty_iff_eq_empty]

/-- Every pin of the cell has the required transverse margin from each actual remote strip. -/
theorem initialCellRemoteIndices_margin
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {w : ℝ} (hw : 0 < w) (N j : ℕ) (Q : Set (EuclideanSpace ℝ (Fin 2)))
    {L : ℝ} (hsmall : L * (16 * Real.pi / N) ≤ w)
    {k : ℤ} (hk : k ∈ initialCellRemoteIndices χ hχ w N j Q)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Q) :
    w + w + L * (16 * Real.pi / N) ≤
      |⟪sourceWavePacketNormal N j, y⟫ - w * k| := by
  have hd := (Finset.mem_filter.mp hk).2
  have hf := Set.disjoint_left.mp hd hy
  change ¬ |⟪sourceWavePacketNormal N j, y⟫ - w * k| ≤ 4 * w at hf
  have hfar := lt_of_not_ge hf
  linarith

/-- The extra angular margin is eventually smaller than the actual physical strip width. -/
theorem eventually_dyadic_initial_angular_margin (J : ℕ) (L : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      L * (16 * Real.pi / (64 * 2 ^ (2 * J * n) : ℕ)) ≤
        (2 : ℝ) ^ n / ((2 : ℝ) ^ n) ^ (2 * J) := by
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    (eventually_ge_atTop (L * Real.pi / 4))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp ht
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have h := hn₀ n hn
  have he : ((64 * 2 ^ (2 * J * n) : ℕ) : ℝ) = 64 * ((2 : ℝ) ^ n) ^ (2 * J) := by
    push_cast
    rw [← pow_mul]
    congr 2
    ring
  rw [he]
  have hm := div_le_div_of_nonneg_right h (by positivity : 0 ≤ ((2 : ℝ) ^ n) ^ (2 * J))
  have he' : L * (16 * Real.pi / (64 * ((2 : ℝ) ^ n) ^ (2 * J))) =
      (L * Real.pi / 4) / ((2 : ℝ) ^ n) ^ (2 * J) := by ring
  rw [he']
  exact hm

/-- The full initial reconstruction theorem for the actual remote-cell selection.
Its only pin hypotheses are membership in the cell and the fixed bounded pin region. -/
theorem exists_initial_cell_reconstruction_rapid
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) {J : ℕ} (hJ : 0 < J) (L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M),
        (∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1) → ∀ n ≥ n₀,
        let N := 64 * 2 ^ (2 * J * n)
        let hN : 0 < N := by dsimp only [N]; positivity
        let w := (2 : ℝ) ^ n / ((2 : ℝ) ^ n) ^ (2 * J)
        let ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ := 𝓕 (dyadicAnnularKernel (4 * J) n)
        let hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) n
        let hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * J) n
        ∀ (G : Finset ℕ), G ⊆ Finset.range N → ∀ Q : Set (EuclideanSpace ℝ (Fin 2)),
          ∀ y ∈ Q, sourceCutoffRadius χ hχ + ‖y‖ ≤ L →
            ∀ r : ℝ, (2 : ℝ) ^ (4 * J * n) ≤ r →
              ‖pinnedSpectralCircleAverage
                (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G
                  (fun j ↦ initialCellRemoteIndices χ hχ w N j Q)) y r -
                circleSpectralExtension r
                  (initialCommonSourceSpectrum μ ψ hψ hzero N hN G) y‖ ≤
                C * μ.real univ / ((2 : ℝ) ^ n) ^ q := by
  obtain ⟨C, hC, hc⟩ := exists_dyadic_initial_reconstruction_rapid χ hχ hχone hJ L hδ q
  obtain ⟨n₀, hn₀⟩ := eventually_dyadic_initial_angular_margin J L
  refine ⟨C, hC, n₀, ?_⟩
  intro μ _ M hμ hnear n hn
  dsimp only
  intro G hG Q y hy hyL r hr
  apply hc μ M hμ hnear n G hG _
    (fun j ↦ initialCellRemoteIndices_subset χ hχ _ _ j Q) y hyL ?_ r hr
  intro j _ k hk
  exact initialCellRemoteIndices_margin χ hχ (by positivity) _ j Q (hn₀ n hn) hk hy

end FalconerPacking
