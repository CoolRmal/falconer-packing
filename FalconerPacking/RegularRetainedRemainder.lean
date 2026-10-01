/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RegularInheritedEnergy
import FalconerPacking.RetainedShellRemainder
import FalconerPacking.AnnularScaleSchedule

/-!
# The actual retained remainder on a regular pin component

The padded regular profile determines every spatial and angular scale. The physical width,
angular uncertainty, regular conditional energy, actual packet count, and exact full-minus-
retained density identity are all discharged in the final estimate.
-/

noncomputable section

open MeasureTheory Set Classical FourierTransform Filter
open scoped ENNReal

namespace FalconerPacking

/-- Admissible padded block chains supply both physical deletion scale inequalities.
The auxiliary angular frequency may use the upper edge of the entire annulus. -/
theorem regular_packet_chain_deletion_scales
    {J T k n F : ℕ} (hT : 0 < T) (hn : n ≤ 4 * J * k)
    (hF : T * (4 * J * k) ≤ F) {l : List ℕ}
    (hl : List.IsChain (fun n m ↦ m < n ∧ Admissible (4 * J * k) m n) (n :: l))
    (hend : chainEnd n l = 0) :
    let d := fun j ↦ T * profileChainDepth n l j
    let e := blockProfileChainAngle F T n l
    let s := 6 + 2 * (J * T) * k
    let x := (2 : ℝ) ^ k
    let L := x ^ T
    let w := x / x ^ (2 * (J * T))
    Antitone d ∧ ∀ j : ℕ,
      w ≤ L * (((2 : ℝ) ^ d j)⁻¹ / ((2 : ℝ) ^ d (j + 1))⁻¹) ∧
      ((2 : ℝ) ^ min s (e (j + 1)))⁻¹ ≤
        ((2 : ℝ) ^ d j)⁻¹ / ((2 : ℝ) ^ d (j + 1))⁻¹ := by
  dsimp only
  have hd : Antitone (fun j ↦ T * profileChainDepth n l j) :=
    fun i j hij ↦ Nat.mul_le_mul_left T
      (antitone_profileChainDepth (hl.imp fun _ _ h ↦ h.1) hij)
  refine ⟨hd, fun j ↦ ?_⟩
  have hs : Real.sqrt ((2 : ℝ) ^ (T * (4 * J * k))) ≤
      (2 : ℝ) ^ (6 + 2 * (J * T) * k) := by
    have h := (standard_fourfold_angular_grid_bounds (J * T) k).2.1
    rw [annular_profile_depth_eq] at h
    convert h using 1
    rw [pow_add]
    norm_num
  obtain ⟨ha, hab, hb₁, hcurv, he, _⟩ :=
    blockProfileChain_scales_all_edges (F := T * (4 * J * k)) le_rfl hn hl hend hs j
  have hb : 0 < ((2 : ℝ) ^ (T * profileChainDepth n l (j + 1)))⁻¹ := by positivity
  have hratio := standard_angle_le_spatial_ratio (by positivity) ha hb hb₁ hcurv le_rfl
  have hw := annular_packet_width_le hT J k
  rw [annular_profile_depth_eq] at hw
  have hL : (2 : ℝ) ^ (T * k) = ((2 : ℝ) ^ k) ^ T := by
    rw [← pow_mul, Nat.mul_comm T k]
  rw [hL] at hw
  refine ⟨hw.trans (mul_le_mul_of_nonneg_left hratio (by positivity)), ?_⟩
  apply effective_dyadic_angle_le_spatial_ratio (6 + 2 * (J * T) * k)
    (blockProfileChainAngle F T n l (j + 1)) (by positivity) ha hb hb₁ hcurv hs
  rw [← he]
  apply pow_le_pow_right₀ (by norm_num)
  exact Nat.sub_le_sub_right hF _


/-- A regularized component has the literal retained-remainder bound, with constants chosen
before the component, its profile, its admissible chain, and its shell index. -/
theorem exists_regular_retained_remainder_decay
    {J T : ℕ} (hJ : 0 < J) (hT : 0 < T) (K : ℕ)
    {ζ q D₁ D₂ : ℝ} (hζ : 0 ≤ ζ) (hζ₄ : ζ ≤ 1 / 4) (hq : 1 ≤ q) (hD₂ : 0 ≤ D₂)
    (hsource : (4 * K + 9 : ℝ) - (q - 1) * D₁ ≤ -1)
    (hpin : (4 * K + 9 : ℝ) + D₁ - D₂ ≤ -1)
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1)
    {X Y : Set (EuclideanSpace ℝ (Fin 2))}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hμX : μ Xᶜ = 0)
    (hXR : ∀ x ∈ X, ‖x‖ ≤ R) (hYR : ∀ y ∈ Y, ‖y‖ ≤ R)
    (hsep : ∀ y ∈ Y, ∀ x ∈ X, δ ≤ (y - x) 0) :
    ∃ G b c : ℝ, 0 < G ∧ 0 < b ∧ 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
        (A : Finset (Fin 2 → ℤ)) (er : ℕ → ℕ),
      let N := 4 * J * k
      let σ := normalizedRestrict ν (finiteDyadicUnion (T * N) A)
      let n₀ := Nat.floor ((1 - ζ) * N)
      ν (finiteDyadicUnion (T * N) A) ≠ 0 →
      (∀ j < N, er j ≤ 2 * T) →
      FiniteTreeRegular A (fun a ↦ σ.real (dyadicCube (T * N) a)) (ancestor T) N er →
      (∀ a ∈ A, ∀ a' ∈ A, ancestor (T * N) a = ancestor (T * N) a') →
      ∀ l : List ℕ, l.length ≤ K →
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n₀ :: l) →
      chainEnd n₀ l = 0 →
      ∀ (I : Finset (Fin 2 → ℤ)) (F : ℕ), T * N ≤ F →
      σ Yᶜ = 0 → (∀ᵐ y ∂σ, μ.map (radialAngle y) ≪ radialAngularMeasure) →
      (∀ Q ∈ I, 0 < σ (dyadicCube (T * n₀) Q)) →
      σ (finiteDyadicUnion (T * n₀) I)ᶜ = 0 →
      let d := fun j ↦ T * profileChainDepth n₀ l j
      let e := blockProfileChainAngle F T n₀ l
      let s := 6 + 2 * (J * T) * k
      let x := (2 : ℝ) ^ k
      let L := x ^ T
      let w := x / x ^ (2 * (J * T))
      let profile := fun j ↦ 4 * (profileChainDepth n₀ l j + 1 : ℝ≥0∞) *
        (2 : ℝ≥0∞) ^ (3 * (N : ℝ) + 3 * T + T *
          edgeCost (regularBlockProfile T N er)
            (profileChainDepth n₀ l (j + 1)) (profileChainDepth n₀ l j))
      let H := fun j ↦ ENNReal.ofReal (G * L ^ (20 * K + 100)) * profile j *
        (ENNReal.ofReal L) ^ D₂
      let ψ := 𝓕 (dyadicAnnularKernel (4 * (J * T)) k)
      let hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * (J * T)) k
      let hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * (J * T)) k
      (∫⁻ y, ∫⁻ r, ‖complexDistanceDensity
          (compactAnnularSource μ hμ (χ.postcompCLM Complex.ofRealCLM)
            (hasCompactSupport_complex_source_cutoff χ hχ) (4 * (J * T)) (k + 1)) y r -
        complexDistanceDensity
          (retainedPinSource μ hμ ψ hψ hzero χ hχ σ d e s F K L H I w y) y r‖ₑ
          ∂volume ∂σ) ≤
        (ENNReal.ofReal b * (∫⁻ y, ∫⁻ θ,
          radialProjectionDensity μ y θ ^ q ∂radialAngularMeasure ∂σ) + ENNReal.ofReal c) *
          (2 : ℝ≥0∞) ^ (-(k : ℝ)) := by
  obtain ⟨G, C₀, C₁, hG, hC₀, hC₁, hbound⟩ := exists_inherited_deleted_shell_decay
    (Nat.mul_pos hJ hT) hT K μ hR hδ hμ χ hχ hχone hX hY hμX hXR hYR hsep
  let B₀ := C₀ * (13 * (3072 / δ + 4 * Real.pi) + 1) * 49 * K
  let B₁ := C₁ * 64 * (2 * sourceCutoffRadius χ hχ + 3)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have hB₁ : 0 ≤ B₁ := by
    dsimp [B₁]
    have := (sourceCutoffRadius_pos χ hχ).le
    positivity
  refine ⟨G, 8 * B₀ + 1, B₀ + B₁ + 1, hG, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_initial_profile_cube_le_packet_width hJ hT hζ₄,
    eventually_ge_atTop 1] with k hwidth hk
  intro ν _ A er
  dsimp only
  intro hA he hreg hroot l _hlen hl hend I F hF hσY hac hI hcover
  let N := 4 * J * k
  let σ := normalizedRestrict ν (finiteDyadicUnion (T * N) A)
  let n₀ := Nat.floor ((1 - ζ) * N)
  let ℓ := profileChainDepth n₀ l
  let d := fun j ↦ T * ℓ j
  let e := blockProfileChainAngle F T n₀ l
  let s := 6 + 2 * (J * T) * k
  let L := ((2 : ℝ) ^ k) ^ T
  let w := (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * (J * T))
  let profile := fun j ↦ 4 * (ℓ j + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
    (3 * (N : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T N er) (ℓ (j + 1)) (ℓ j))
  let H := fun j ↦ ENNReal.ofReal (G * L ^ (20 * K + 100)) * profile j *
    (ENNReal.ofReal L) ^ D₂
  haveI : IsProbabilityMeasure σ := isProbabilityMeasure_normalizedRestrict
    (measurableSet_finiteDyadicUnion _ _) hA (measure_ne_top ν _)
  have hn₀ : n₀ ≤ N := (initial_profile_depth_bounds hζ (by linarith) N T).2.1
  have hℓ : Antitone ℓ := antitone_profileChainDepth (hl.imp fun _ _ h ↦ h.1)
  have hL : 1 ≤ L := one_le_pow₀ (one_le_pow₀ (by norm_num))
  obtain ⟨hd, hscales⟩ := regular_packet_chain_deletion_scales hT hn₀ hF hl hend
  have hp (j : ℕ) (_hj : j < K) : 1 ≤ profile j ∧ profile j ≠ ∞ :=
    regular_profile_energy_one_le_and_ne_top hT er (hℓ (Nat.le_succ j))
  have henergy (j : ℕ) (_hj : j < K)
      (P : Fin 2 → ℤ) (hP : P ∈ I.image (ancestor (d 0 - d (j + 1)))) :
      truncEnergy (normalizedRestrict σ
        (enlargedGridSquare ((2 : ℝ) ^ d (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P))
        (dyadicRadius (d j)) (dyadicRadius (d (j + 1))) ≤ profile j := by
    exact regular_component_inherited_parent_energy ν hT he hA hreg hroot ℓ hℓ hn₀
      I hI hL j hP
  have hactual := hbound σ hσY hac k hk d e hd F H I q D₁ D₂ profile hq hD₂
    hsource hpin hwidth hp (fun j _ ↦ (hscales j).1) (fun j _ ↦ (hscales j).2)
    (fun _ _ ↦ rfl) (fun j hj P hP _ ↦ henergy j hj P hP)
  rw [lintegral_compactAnnularDensity_sub_retained_eq_deleted μ hμ χ hχ σ d e s F K L H I
    Y (show 0 < w by dsimp [w]; positivity) (4 * (J * T)) k hσY hcover]
  apply hactual.trans
  apply mul_le_mul' _ le_rfl
  let M := ∫⁻ y, ∫⁻ θ, radialProjectionDensity μ y θ ^ q ∂radialAngularMeasure ∂σ
  change ENNReal.ofReal B₀ * (8 * M + 1) + ENNReal.ofReal B₁ ≤
    ENNReal.ofReal (8 * B₀ + 1) * M + ENNReal.ofReal (B₀ + B₁ + 1)
  calc
    _ = ENNReal.ofReal (8 * B₀) * M + ENNReal.ofReal (B₀ + B₁) := by
      have hm : ENNReal.ofReal (8 * B₀) = 8 * ENNReal.ofReal B₀ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat]
      rw [hm, ENNReal.ofReal_add hB₀ hB₁]
      ring
    _ ≤ _ := by
      apply add_le_add
      · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
      · exact ENNReal.ofReal_le_ofReal (by linarith)


/-- The literal constructed thresholds are eventually at least one, uniformly in every
profile factor at least one. This also supplies the lower threshold input of the good branch. -/
theorem eventually_regular_threshold_ge_one {G D₂ : ℝ} (hG : 0 < G) (hD₂ : 0 ≤ D₂)
    {T : ℕ} (hT : 0 < T) (K : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ profile : ℝ≥0∞, 1 ≤ profile →
      1 ≤ ENNReal.ofReal (G * (((2 : ℝ) ^ k) ^ T) ^ (20 * K + 100)) * profile *
        (ENNReal.ofReal (((2 : ℝ) ^ k) ^ T)) ^ D₂ := by
  have hgrowth := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    (eventually_ge_atTop (1 / G))
  filter_upwards [hgrowth] with k hk
  intro profile hp
  have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hg : 1 ≤ G * (2 : ℝ) ^ k := by
    have h := (div_le_iff₀ hG).mp hk
    simpa only [mul_comm] using h
  have hpow : (2 : ℝ) ^ k ≤ (((2 : ℝ) ^ k) ^ T) ^ (20 * K + 100) := by
    rw [← pow_mul]
    simpa only [pow_one] using pow_le_pow_right₀ hbase
      (show 1 ≤ T * (20 * K + 100) from
        Nat.succ_le_iff.mpr (Nat.mul_pos hT (by omega)))
  have hfirst : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (G * (((2 : ℝ) ^ k) ^ T) ^ (20 * K + 100)) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (hg.trans (mul_le_mul_of_nonneg_left hpow hG.le))
  have hL : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (((2 : ℝ) ^ k) ^ T) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (one_le_pow₀ hbase : (1 : ℝ) ≤ ((2 : ℝ) ^ k) ^ T)
  apply one_le_mul (one_le_mul hfirst hp)
  simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_le hL hD₂

end FalconerPacking
