/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PacketPairMultiplicity
import FalconerPacking.DeletedPacketSum
import FalconerPacking.BallOverlap

/-!
# From actual packet pair multiplicity to deletion mass

The source strips and the pin-dependent deleted sets determine actual measurable pair sets.
Their product masses sum with only the proved packet overlap factor on separated supports.
-/

noncomputable section

open MeasureTheory Set Classical FourierTransform Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace FalconerPacking

/-- Actual enlarged-strip pair masses have only the quantitative separated-pair overlap loss. -/
theorem sum_packet_product_mass_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    {X Y : Set (EuclideanSpace ℝ (Fin 2))} (hX : MeasurableSet X)
    {N : ℕ} (hN : 0 < N) (J : Finset ℤ) {w C δ : ℝ}
    (hw : 0 < w) (hC : 2 ≤ C) (hδ : 0 < δ)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ ‖y - x‖)
    (P : ℕ × ℤ → Set (EuclideanSpace ℝ (Fin 2)))
    (hP : ∀ i ∈ (Finset.range N) ×ˢ J, MeasurableSet (P i))
    (hPY : ∀ i ∈ (Finset.range N) ×ˢ J, P i ⊆ Y)
    (hPT : ∀ i ∈ (Finset.range N) ×ˢ J, P i ⊆
      packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (C * w)) :
    (∑ i ∈ (Finset.range N) ×ˢ J, ν (P i) *
      μ (X ∩ packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (2 * w))) ≤
      (Nat.ceil ((2 * C + 1) * (8 * C * w * N / δ + 4 * Real.pi)) : ℝ≥0∞) *
      (ν.prod μ) (⋃ i ∈ (Finset.range N) ×ˢ J,
        P i ×ˢ (X ∩ packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (2 * w))) := by
  let I := (Finset.range N) ×ˢ J
  let S (i : ℕ × ℤ) := P i ×ˢ
    (X ∩ packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (2 * w))
  let U := ⋃ i ∈ I, S i
  let B := Nat.ceil ((2 * C + 1) * (8 * C * w * N / δ + 4 * Real.pi))
  have hS : ∀ i ∈ I, MeasurableSet (S i) := fun i hi ↦
    (hP i hi).prod (hX.inter (measurableSet_packetSourceStrip _ _ _))
  have hU : MeasurableSet U := Finset.measurableSet_biUnion I hS
  have hcount (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
      (I.filter (fun i ↦ p ∈ S i)).card ≤ B := by
    by_cases hp : p ∈ U
    · obtain ⟨i, hi, hy, hx⟩ := mem_iUnion₂.mp hp
      have hxy := hsep p.2 hx.1 p.1 (hPY i hi hy)
      have hsub : I.filter (fun i ↦ p ∈ S i) ⊆
          I.filter (fun i ↦
            p.2 ∈ packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (C * w) ∧
            p.1 ∈ packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (C * w)) := by
        intro i hi
        obtain ⟨hi, hy, hx⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨hi, ?_, hPT i hi hy⟩
        have ht : |⟪sourceWavePacketNormal N i.1, p.2⟫ - w * i.2| ≤ 2 * w := hx.2
        exact ht.trans (mul_le_mul_of_nonneg_right hC hw.le)
      have hreal := card_packet_pair_strips_le hN J hw (by linarith : 0 ≤ C)
        hδ p.2 p.1 hxy
      have hnat : ((I.filter (fun i ↦
          p.2 ∈ packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (C * w) ∧
          p.1 ∈ packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (C * w))).card) ≤ B := by
        exact_mod_cast hreal.trans (Nat.le_ceil _)
      exact (Finset.card_le_card hsub).trans hnat
    · have he : I.filter (fun i ↦ p ∈ S i) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        exact fun i hi hpS ↦ hp (mem_iUnion₂.mpr ⟨i, hi, hpS⟩)
      simp only [he, Finset.card_empty, zero_le]
  have h := sum_measure_le_mul_of_multiplicity (ν.prod μ) I S hU hS
    (fun i hi p hp ↦ mem_iUnion₂.mpr ⟨i, hi, hp⟩) B (fun p ↦ by
      convert hcount p using 1
      congr 1
      ext i
      simp only [Finset.mem_filter])
  simpa only [S, Measure.prod_prod] using h

/-- The actual deleted packet density has a product-mass bound with the concrete overlap
factor. The two kernel bounds refer to the constructed inverse cap multipliers. -/
theorem lintegral_enorm_deleted_sourceWavePackets_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1)
    {X Y : Set (EuclideanSpace ℝ (Fin 2))} (hX : MeasurableSet X) (hμX : μ Xᶜ = 0)
    {N : ℕ} (hN : 0 < N) (J : Finset ℤ) {w C δ : ℝ}
    (hw : 0 < w) (hC : 2 ≤ C) (hδ : 0 < δ)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ ‖y - x‖)
    (P : ℕ × ℤ → Set (EuclideanSpace ℝ (Fin 2)))
    (hP : ∀ i ∈ (Finset.range N) ×ˢ J, MeasurableSet (P i))
    (hPY : ∀ i ∈ (Finset.range N) ×ˢ J, P i ⊆ Y)
    (hPT : ∀ i ∈ (Finset.range N) ×ˢ J, P i ⊆
      packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (C * w))
    {K₀ ε : ℝ≥0∞}
    (hK : ∀ j < N, (∫⁻ z, ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖ₑ) ≤ K₀)
    (hε : ∀ j < N, (∫⁻ z in {z | w ≤ |⟪sourceWavePacketNormal N j, z⟫|},
      ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖ₑ) ≤ ε) :
    (∫⁻ y, ∫⁻ t, ‖complexDistanceDensity
      (deletedPacketSum ((Finset.range N) ×ˢ J) P
        (fun i ↦ sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w i.1 i.2) y) y t‖ₑ
        ∂volume ∂ν) ≤
      K₀ * ((Nat.ceil ((2 * C + 1) * (8 * C * w * N / δ + 4 * Real.pi)) : ℝ≥0∞) *
        (ν.prod μ) (⋃ i ∈ (Finset.range N) ×ˢ J,
          P i ×ˢ (X ∩ packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (2 * w)))) +
      ε * μ univ * (((Finset.range N) ×ˢ J).card * ν univ) := by
  let I := (Finset.range N) ×ˢ J
  let S (i : ℕ × ℤ) := X ∩
    packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (2 * w)
  have hlocal (i : ℕ × ℤ) (hi : i ∈ I) :
      (∫⁻ x, ‖sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w i.1 i.2 x‖ₑ) ≤
        K₀ * μ (S i) + ε * μ univ := by
    have hij : i.1 < N := Finset.mem_range.mp (Finset.mem_product.mp hi).1
    have he : μ (packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (2 * w)) =
        μ (S i) := by
      dsimp only [S]
      rw [inter_comm, measure_inter_conull hμX]
    exact (lintegral_enorm_sourceWavePacket_le μ hμ ψ hψ hzero χ hχ hχone N hN
      hw i.1 i.2).trans (by rw [he]; gcongr <;> first | exact hK i.1 hij | exact hε i.1 hij)
  have hpin : ∑ i ∈ I, ν (P i) ≤ I.card * ν univ := by
    calc
      _ ≤ ∑ _i ∈ I, ν univ := Finset.sum_le_sum fun i _ ↦ measure_mono (subset_univ _)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ ∑ i ∈ I, ν (P i) *
        ∫⁻ x, ‖sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w i.1 i.2 x‖ₑ :=
      lintegral_enorm_pinned_deletedPacketSum_le ν I P hP _
    _ ≤ ∑ i ∈ I, ν (P i) * (K₀ * μ (S i) + ε * μ univ) :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul' le_rfl (hlocal i hi)
    _ = K₀ * (∑ i ∈ I, ν (P i) * μ (S i)) + ε * μ univ * (∑ i ∈ I, ν (P i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul' le_rfl (sum_packet_product_mass_le μ ν hX hN J hw hC hδ hsep P hP hPY hPT))
      (mul_le_mul' le_rfl hpin)

end FalconerPacking
