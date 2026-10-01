/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InitialSpectralReconstruction
import FalconerPacking.DyadicSpectralNorms

/-!
# Arbitrarily rapid initial reconstruction on concrete dyadic packet grids

The packet integer is independent of the regularization block length. Passing from the
index `n` to a multiple of `n` therefore preserves the result without linking the two choices.
-/

noncomputable section

open MeasureTheory Set Function FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The concrete width has the same reciprocal polynomial scale as the standard grid. -/
theorem dyadic_initial_width_bounds {J : ℕ} (hJ : 0 < J) {x : ℝ} (hx : 1 ≤ x) :
    0 < x / x ^ (2 * J) ∧ x / x ^ (2 * J) ≤ 1 ∧
      (64 * x ^ (2 * J))⁻¹ ≤ x / x ^ (2 * J) ∧
      (x / x ^ (2 * J))⁻¹ ≤ x ^ (2 * J) := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : x ≤ x ^ (2 * J) := by
    simpa only [pow_one] using pow_le_pow_right₀ hx (by omega : 1 ≤ 2 * J)
  refine ⟨by positivity, (div_le_one (by positivity)).mpr hp, ?_, ?_⟩
  · rw [mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith : (64 : ℝ)⁻¹ ≤ x) (by positivity)
  · rw [inv_div]
    exact div_le_self (by positivity) hx

/-- Both remote-error denominators grow at least linearly in the base dyadic scale. -/
theorem dyadic_initial_decay_parameters {J : ℕ} {x r : ℝ}
    (hx : 0 < x) (hr : x ^ (4 * J) ≤ r) :
    x / 64 ≤ r * (64 * x ^ (2 * J))⁻¹ * (x / x ^ (2 * J)) ∧
      x / 64 ≤ 1 + (x / x ^ (2 * J)) * r * (2 * Real.pi / (64 * x ^ (2 * J))) := by
  have he : x ^ (4 * J) * (64 * x ^ (2 * J))⁻¹ * (x / x ^ (2 * J)) = x / 64 := by
    have hp : x ^ (4 * J) = (x ^ (2 * J)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    rw [hp]
    field_simp
  have hbase : x / 64 ≤ r * (64 * x ^ (2 * J))⁻¹ * (x / x ^ (2 * J)) := by
    rw [← he]
    gcongr
  refine ⟨hbase, ?_⟩
  have hπ : 1 ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have ht : 0 ≤ r * (64 * x ^ (2 * J))⁻¹ * (x / x ^ (2 * J)) :=
    (by positivity : 0 ≤ x / 64).trans hbase
  have hm := mul_le_mul_of_nonneg_right hπ ht
  rw [one_mul] at hm
  have hid : (x / x ^ (2 * J)) * r * (2 * Real.pi / (64 * x ^ (2 * J))) =
      (2 * Real.pi) * (r * (64 * x ^ (2 * J))⁻¹ * (x / x ^ (2 * J))) := by ring
  rw [hid]
  linarith

/-- Any positive decay denominator above `x/64` gives the same simple power bound. -/
theorem inv_pow_le_dyadic_initial_bound {x b : ℝ} (hx : 0 < x)
    (hb : x / 64 ≤ b) (m : ℕ) : b⁻¹ ^ m ≤ 64 ^ m / x ^ m := by
  have hb₀ : 0 < b := (by positivity : 0 < x / 64).trans_le hb
  have hi : b⁻¹ ≤ 64 / x := by
    rw [← inv_div]
    exact (inv_le_inv₀ hb₀ (by positivity)).mpr hb
  exact (pow_le_pow_left₀ (by positivity) hi m).trans_eq (div_pow _ _ _)

/-- The complete physical strip grid has a polynomial bound independent of selections. -/
theorem card_initial_strip_grid_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {J : ℕ} (hJ : 0 < J) {x : ℝ} (hx : 1 ≤ x) :
    ((sourceWavePacketIndices χ hχ (x / x ^ (2 * J))).card : ℝ) ≤
      (2 * sourceCutoffRadius χ hχ + 3) * x ^ (2 * J) := by
  have hw := dyadic_initial_width_bounds hJ hx
  apply (card_sourceWavePacketIndices_le χ hχ hw.1).trans
  have hp : 1 ≤ x ^ (2 * J) := one_le_pow₀ hx
  have ha : 0 ≤ 2 * sourceCutoffRadius χ hχ :=
    mul_nonneg (by norm_num) (sourceCutoffRadius_pos χ hχ).le
  have hm := mul_le_mul_of_nonneg_left hw.2.2.2 ha
  rw [← div_eq_mul_inv] at hm
  nlinarith

theorem dyadic_initial_power_ratio {x : ℝ} (hx : 1 ≤ x) {p q m : ℕ}
    (h : p + q ≤ m) : x ^ p / x ^ m ≤ 1 / x ^ q := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul, ← pow_add]
  exact pow_le_pow_right₀ hx h

/-- The error is arbitrarily small compared with powers of the base dyadic scale, uniformly
over the actual retained packet family and every pin satisfying its remote-strip margins. -/
theorem exists_dyadic_initial_reconstruction_rapid
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) {J : ℕ} (hJ : 0 < J) (L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M),
        (∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1) → ∀ n : ℕ,
        let N := 64 * 2 ^ (2 * J * n)
        let hN : 0 < N := by dsimp only [N]; positivity
        let w := (2 : ℝ) ^ n / ((2 : ℝ) ^ n) ^ (2 * J)
        let ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ := 𝓕 (dyadicAnnularKernel (4 * J) n)
        let hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) n
        let hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * J) n
        ∀ (G : Finset ℕ), G ⊆ Finset.range N → ∀ remote : ℕ → Finset ℤ,
          (∀ j, remote j ⊆ sourceWavePacketIndices χ hχ w) →
          ∀ y : EuclideanSpace ℝ (Fin 2), sourceCutoffRadius χ hχ + ‖y‖ ≤ L →
            (∀ j ∈ Finset.range N \ G, ∀ k ∈ remote j,
              w + w + L * (16 * Real.pi / N) ≤
                |⟪sourceWavePacketNormal N j, y⟫ - w * k|) →
            ∀ r : ℝ, (2 : ℝ) ^ (4 * J * n) ≤ r →
              ‖pinnedSpectralCircleAverage
                (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote) y r -
                circleSpectralExtension r
                  (initialCommonSourceSpectrum μ ψ hψ hzero N hN G) y‖ ≤
                C * μ.real univ / ((2 : ℝ) ^ n) ^ q := by
  let m := q + 12 * J
  obtain ⟨C₁, C₂, hC₁, hC₂, hc⟩ :=
    exists_initial_spectral_reconstruction_bound χ hχ hχone m L
  obtain ⟨K₀, K₁, hK₀, hK₁, hK⟩ := exists_standard_dyadic_kernel_real_bounds J m
  let F := ((2 : ℝ) ^ (8 * J) + 1) * ∫ ξ, ‖unitFrequencyCutoff ξ‖
  have hF : 0 ≤ F := mul_nonneg (by positivity) (integral_nonneg fun _ ↦ norm_nonneg _)
  let A := 2 * sourceCutoffRadius χ hχ + 3
  have hA : 0 < A := by dsimp [A]; linarith [sourceCutoffRadius_pos χ hχ]
  let B₀ := 2 * K₁ / δ ^ m
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  let B₁ := 64 ^ m * (C₁ * K₀ + C₂ * F)
  have hB₁ : 0 < B₁ := by dsimp [B₁]; positivity
  refine ⟨64 * B₀ + 64 * A * B₁, by positivity, ?_⟩
  intro μ _ M hμ hnear n
  dsimp only
  intro G hG remote hsubset y hy hremote r hr
  let x : ℝ := 2 ^ n
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let N := 64 * 2 ^ (2 * J * n)
  have hN : 0 < N := by dsimp [N]; positivity
  let w := x / x ^ (2 * J)
  have hNreal : (N : ℝ) = 64 * x ^ (2 * J) := by
    dsimp [N, x]
    push_cast
    rw [← pow_mul]
    congr 2
    ring
  have hRreal : (2 : ℝ) ^ (4 * J * n) = x ^ (4 * J) := by
    dsimp [x]
    rw [← pow_mul]
    congr 1
    ring
  have hw := dyadic_initial_width_bounds hJ hx
  have hscale := dyadic_initial_decay_parameters hx₀ (hRreal ▸ hr)
  have hw₀ : 0 < w := hw.1
  have hr₀ : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hpow := inv_pow_le_dyadic_initial_bound hx₀ hscale.1 m
  have htailpow := inv_pow_le_dyadic_initial_bound hx₀ hscale.2 m
  have hμ₀ : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
  have hbase := hc μ M hμ (𝓕 (dyadicAnnularKernel (4 * J) n))
    (hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) n)
    (fourier_dyadicAnnularKernel_eventually_zero (4 * J) n) N hN w w hw.1 hw.2.1
    (hNreal ▸ hw.2.2.1) hw.2.1 G remote δ hnear y hy hremote r
    (lt_of_lt_of_le (by positivity) hr)
  have hcut (j : ℕ) : 2 * (∫ z in {z | δ ≤ ‖z‖},
      ‖(𝓕⁻ (dyadicAngularCap (4 * J) n N hN j)) z‖) * μ.real univ ≤
      B₀ / x ^ m * μ.real univ := by
    have hh := (hK n j).2 δ hδ
    have he : (2 : ℝ) ^ (2 * J * n) = x ^ (2 * J) := by
      dsimp [x]
      rw [← pow_mul]
      congr 1
      ring
    rw [he] at hh
    have hp : x ≤ x ^ (2 * J) := by
      simpa only [pow_one] using pow_le_pow_right₀ hx (by omega : 1 ≤ 2 * J)
    apply mul_le_mul_of_nonneg_right _ hμ₀
    apply (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)).trans
    have ht : K₁ / (x ^ (2 * J) * δ) ^ m ≤ K₁ / (x * δ) ^ m := by gcongr
    apply (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    dsimp [B₀]
    rw [mul_pow]
    ring
  have hpacket (j : ℕ) (hj : j < N) :
      C₁ * (r * (N : ℝ)⁻¹ * w)⁻¹ ^ m *
          (μ.real univ * ∫ z, ‖(𝓕⁻ (dyadicAngularCap (4 * J) n N hN j)) z‖) +
        (w * C₂ / (1 + w * r * (2 * Real.pi / N)) ^ m) * μ.real univ *
          (∫ ξ, ‖dyadicAngularCap (4 * J) n N hN j ξ‖) ≤
        B₁ * x ^ (8 * J) / x ^ m * μ.real univ := by
    have hk := (hK n j).1
    have hf := integral_norm_dyadicAngularCap_le (4 * J) n N hN hj
    have he : (2 : ℝ) ^ (2 * (4 * J) * n) = x ^ (8 * J) := by
      dsimp [x]
      rw [← pow_mul]
      congr 1
      ring
    change (∫ ξ, ‖dyadicAngularCap (4 * J) n N hN j ξ‖) ≤
      ((2 : ℝ) ^ (2 * (4 * J)) + 1) * (∫ ξ, ‖unitFrequencyCutoff ξ‖) *
        (2 : ℝ) ^ (2 * (4 * J) * n) at hf
    rw [he, show 2 * (4 * J) = 8 * J by omega] at hf
    have ht : w * C₂ / (1 + w * r * (2 * Real.pi / N)) ^ m ≤
        C₂ * 64 ^ m / x ^ m := by
      rw [div_eq_mul_inv, ← inv_pow, hNreal]
      apply (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hC₂.le hw.2.1) (by positivity)).trans
      exact (mul_le_mul_of_nonneg_left htailpow hC₂.le).trans_eq (by ring)
    have h₁ : C₁ * (r * (N : ℝ)⁻¹ * w)⁻¹ ^ m *
        (μ.real univ * ∫ z, ‖(𝓕⁻ (dyadicAngularCap (4 * J) n N hN j)) z‖) ≤
        C₁ * (64 ^ m / x ^ m) * (μ.real univ * K₀) := by
      rw [hNreal]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC₁.le)
        (mul_le_mul_of_nonneg_left hk hμ₀)
        (mul_nonneg hμ₀ (integral_nonneg fun _ ↦ norm_nonneg _)) (by positivity)
    have h₂ := mul_le_mul (mul_le_mul_of_nonneg_right ht hμ₀) hf
      (integral_nonneg fun _ ↦ norm_nonneg _) (by positivity)
    have hp : 1 ≤ x ^ (8 * J) := one_le_pow₀ hx
    have h₁' := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ C₁ * (64 ^ m / x ^ m) * (μ.real univ * K₀) by positivity)
    rw [mul_one] at h₁'
    exact (add_le_add (h₁.trans h₁') h₂).trans_eq (by dsimp [B₁, F]; ring)
  -- Finite packet counts and the choice of derivative order absorb all polynomial factors.
  apply hbase.trans
  have hcardG : (G.card : ℝ) ≤ 64 * x ^ (2 * J) := by
    have hh := Finset.card_le_card hG
    rw [Finset.card_range] at hh
    exact hNreal ▸ (by exact_mod_cast hh)
  have hcardBad : ((Finset.range N \ G).card : ℝ) ≤ 64 * x ^ (2 * J) := by
    have hh := Finset.card_le_card (Finset.sdiff_subset : Finset.range N \ G ⊆ Finset.range N)
    rw [Finset.card_range] at hh
    exact hNreal ▸ (by exact_mod_cast hh)
  have hcardRemote (j : ℕ) : ((remote j).card : ℝ) ≤ A * x ^ (2 * J) := by
    have hh : ((remote j).card : ℝ) ≤ ((sourceWavePacketIndices χ hχ w).card : ℝ) := by
      exact Nat.cast_le.mpr (Finset.card_le_card
        (show remote j ⊆ sourceWavePacketIndices χ hχ w from hsubset j))
    exact hh.trans (card_initial_strip_grid_le χ hχ hJ hx)
  have hcutSum : (∑ j ∈ G, 2 * (∫ z in {z | δ ≤ ‖z‖},
      ‖(𝓕⁻ (dyadicAngularCap (4 * J) n N hN j)) z‖) * μ.real univ) ≤
      64 * B₀ * μ.real univ / x ^ q := by
    apply (Finset.sum_le_sum fun j _ ↦ hcut j).trans
    rw [Finset.sum_const, nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right hcardG (by positivity)).trans
    have hrati := dyadic_initial_power_ratio hx (p := 2 * J) (q := q) (m := m)
      (by dsimp [m]; omega)
    have hh := mul_le_mul_of_nonneg_left hrati
      (show 0 ≤ 64 * B₀ * μ.real univ by positivity)
    convert hh using 1 <;> ring
  have hpacketSum : (∑ j ∈ Finset.range N \ G, ∑ _k ∈ remote j,
      (C₁ * (r * (N : ℝ)⁻¹ * w)⁻¹ ^ m *
          (μ.real univ * ∫ z, ‖(𝓕⁻ (dyadicAngularCap (4 * J) n N hN j)) z‖) +
        (w * C₂ / (1 + w * r * (2 * Real.pi / N)) ^ m) * μ.real univ *
          ∫ ξ, ‖dyadicAngularCap (4 * J) n N hN j ξ‖)) ≤
      64 * A * B₁ * μ.real univ / x ^ q := by
    apply (Finset.sum_le_sum fun j hj ↦ Finset.sum_le_sum fun _ _ ↦
      hpacket j (Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1)).trans
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply (Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_right (hcardRemote j) (by positivity)).trans
    rw [Finset.sum_const, nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right hcardBad (by positivity)).trans
    have hrati := dyadic_initial_power_ratio hx (p := 12 * J) (q := q) (m := m)
      (by dsimp [m]; omega)
    have hh := mul_le_mul_of_nonneg_left hrati
      (show 0 ≤ 64 * A * B₁ * μ.real univ by positivity)
    convert hh using 1 <;> ring
  exact (add_le_add hcutSum hpacketSum).trans_eq (by ring)

end FalconerPacking
