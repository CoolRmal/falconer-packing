/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.NormalizedAngularDerivatives
public import FalconerPacking.AnisotropicDirectionProfile
public import FalconerPacking.LocalCompositionBounds

/-!+# Uniform angular-symbol derivatives in anisotropic coordinates

The normalized bump extension is composed with the smooth rescaled direction profile. The
resulting derivative constants are uniform over all grids, caps, and orthonormal orientations.
-/

@[expose] public section

noncomputable section

open Set Function Classical Filter
open scoped ContDiff Topology

namespace FalconerPacking

/-- A joint smooth extension of the anisotropically rescaled angular multiplier. -/
def rescaledAngularExtension (N : ℕ) (hN : 0 < N) (j : ℕ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (p : ℝ × EuclideanSpace ℝ (Fin 2)) : ℝ :=
  normalizedAngularAmbientWeight N hN j
    ((2 * Real.pi / N) • (ρ • O (anisotropicDirectionProfile p)) +
      O (WithLp.toLp 2 ![0, 1]))

theorem contDiffAt_rescaledAngularExtension (N : ℕ) (hN : 0 < N) (j : ℕ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    {p : ℝ × EuclideanSpace ℝ (Fin 2)} (hp : 0 < p.2 1) :
    ContDiffAt ℝ ∞ (rescaledAngularExtension N hN j O ρ) p :=
  (contDiff_normalizedAngularAmbientWeight N hN j).contDiffAt.comp p
    ((((O.toContinuousLinearEquiv.contDiff.contDiffAt.comp p
      (contDiffAt_anisotropicDirectionProfile hp)).const_smul ρ).const_smul _).add
        contDiffAt_const)

private theorem derivative_scaled_isometry_profile
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (ρ : ℝ) (m : ℕ)
    {p : ℝ × EuclideanSpace ℝ (Fin 2)} (hp : 0 < p.2 1) :
    ‖iteratedFDeriv ℝ m (fun q ↦ ρ • O (anisotropicDirectionProfile q)) p‖ =
      |ρ| * ‖iteratedFDeriv ℝ m anisotropicDirectionProfile p‖ := by
  have hcf := (contDiffAt_anisotropicDirectionProfile hp).of_le (m := m) (mod_cast le_top)
  have hco : ContDiffAt ℝ m (O ∘ anisotropicDirectionProfile) p := by
    exact O.toContinuousLinearEquiv.contDiff.contDiffAt.comp p hcf
  change ‖iteratedFDeriv ℝ m (fun q ↦ ρ • (O ∘ anisotropicDirectionProfile) q) p‖ = _
  rw [iteratedFDeriv_const_smul_apply' (a := ρ) hco, norm_smul, Real.norm_eq_abs,
    O.norm_iteratedFDeriv_comp_left]

/-- Joint derivatives are uniformly bounded, including as the angular scale tends to zero. -/
theorem rescaledAngularExtension_derivative_bound {c : ℝ} (hc : 0 < c)
    (M : ℝ) {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    ∃ C > 0, ∀ (N : ℕ) (hN : 0 < N) (j : ℕ)
      (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
      (p : ℝ × EuclideanSpace ℝ (Fin 2)), |ρ| ≤ K → ‖p‖ ≤ M → c ≤ p.2 1 →
      ‖iteratedFDeriv ℝ m (rescaledAngularExtension N hN j O ρ) p‖ ≤ C := by
  choose F hF hFb using normalizedAngularAmbientWeight_rescaled_derivative_bound
  choose G hG hGb using fun k ↦ anisotropicDirectionProfile_derivative_bound hc M k
  let B := 1 + ∑ k ∈ Finset.range (m + 1), F k
  let D := 1 + K * ∑ k ∈ Finset.range (m + 1), G k
  have hB : 0 < B := by
    have h := Finset.sum_nonneg (s := Finset.range (m + 1)) (fun k _ ↦ (hF k).le)
    dsimp [B]
    linarith
  have hD : 1 ≤ D := by
    have h := Finset.sum_nonneg (s := Finset.range (m + 1)) (fun k _ ↦ (hG k).le)
    dsimp [D]
    nlinarith
  refine ⟨m.factorial * B * D ^ m + 1, by positivity, ?_⟩
  intro N hN j O ρ p hρ hp hpc
  let f (x : EuclideanSpace ℝ (Fin 2)) := normalizedAngularAmbientWeight N hN j
    ((2 * Real.pi / N) • x + O (WithLp.toLp 2 ![0, 1]))
  let g (q : ℝ × EuclideanSpace ℝ (Fin 2)) := ρ • O (anisotropicDirectionProfile q)
  have hf : ContDiff ℝ ∞ f := (contDiff_normalizedAngularAmbientWeight N hN j).comp
    ((contDiff_const_smul (2 * Real.pi / (N : ℝ))).add contDiff_const)
  have hg : ContDiffAt ℝ ∞ g p :=
    (O.toContinuousLinearEquiv.contDiff.contDiffAt.comp p
      (contDiffAt_anisotropicDirectionProfile (hc.trans_le hpc))).const_smul ρ
  apply (norm_iteratedFDeriv_comp_le_at hf hg m (C := B) (D := D) ?_ ?_).trans
    (show m.factorial * B * D ^ m ≤ m.factorial * B * D ^ m + 1 by linarith)
  · intro k hk
    have he := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m + 1)) ↦ (hF i).le)
      (show k ∈ Finset.range (m + 1) by simpa using Nat.lt_succ_of_le hk)
    exact (hFb k N hN j _ _).trans (by dsimp [B]; linarith)
  · intro k hk hkm
    change ‖iteratedFDeriv ℝ k (fun q ↦ ρ • O (anisotropicDirectionProfile q)) p‖ ≤ _
    rw [derivative_scaled_isometry_profile O ρ k (hc.trans_le hpc)]
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m + 1)) ↦ (hG i).le)
      (show k ∈ Finset.range (m + 1) by simpa using Nat.lt_succ_of_le hkm)
    apply (mul_le_mul hρ (hGb k p hp hpc) (norm_nonneg _) hK).trans
    apply le_trans (show K * G k ≤ D by dsimp [D]; nlinarith)
    exact le_self_pow₀ hD (by omega)

/-- At the matching scale, the extension is exactly the original angular multiplier. -/
theorem rescaledAngularExtension_eq_weight (N : ℕ) (hN : 0 < N) (j : ℕ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (ε ρ : ℝ)
    (hscale : (2 * Real.pi / N) * ρ = ε)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : 0 < z 1) :
    rescaledAngularExtension N hN j O ρ (ε, z) =
      angularCapWeight N hN j (O (WithLp.toLp 2 ![ε * z 0, z 1])) := by
  let ξ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![ε * z 0, z 1]
  have hξ : ξ ≠ 0 := by
    intro he
    have he₁ := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) he
    change z 1 = 0 at he₁
    linarith
  have he := congrArg O (anisotropicDirectionProfile_identity ε z hz)
  simp only [map_smul, map_add] at he
  have he' : ‖O ξ‖⁻¹ • O ξ = (2 * Real.pi / N) •
      (ρ • O (anisotropicDirectionProfile (ε, z))) + O (WithLp.toLp 2 ![0, 1]) := by
    rw [LinearIsometryEquiv.norm_map, smul_smul, hscale]
    exact he.trans (add_comm _ _)
  change normalizedAngularAmbientWeight N hN j _ = _
  rw [← he']
  exact normalizedAngularAmbientWeight_direction N hN j (O.map_ne_zero_iff.mpr hξ)

/-- The actual angular weight has uniform derivatives in tangential/radial coordinates. -/
theorem angularCapWeight_anisotropic_derivative_bound {c : ℝ} (hc : 0 < c)
    (M : ℝ) {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    ∃ C > 0, ∀ (N : ℕ) (hN : 0 < N) (j : ℕ)
      (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (ε ρ : ℝ)
      (z : EuclideanSpace ℝ (Fin 2)), (2 * Real.pi / N) * ρ = ε → |ρ| ≤ K →
      ‖(ε, z)‖ ≤ M → c ≤ z 1 →
      ‖iteratedFDeriv ℝ m
        (fun w ↦ angularCapWeight N hN j (O (WithLp.toLp 2 ![ε * w 0, w 1]))) z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := rescaledAngularExtension_derivative_bound hc M hK m
  refine ⟨C, hC, ?_⟩
  intro N hN j O ε ρ z hscale hρ hz hzc
  have hpos : 0 < z 1 := hc.trans_le hzc
  have he : (fun w ↦ angularCapWeight N hN j (O (WithLp.toLp 2 ![ε * w 0, w 1])))
      =ᶠ[𝓝 z] (fun w ↦ rescaledAngularExtension N hN j O ρ (ε, w)) := by
    have ho : IsOpen {w : EuclideanSpace ℝ (Fin 2) | 0 < w 1} :=
      isOpen_lt continuous_const (by fun_prop)
    filter_upwards [ho.mem_nhds hpos] with w hw
    exact (rescaledAngularExtension_eq_weight N hN j O ε ρ hscale w hw).symm
  rw [(he.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  exact (norm_iteratedFDeriv_fix_parameter_le_at ε
    (contDiffAt_rescaledAngularExtension N hN j O ρ hpos) m).trans
      (hbound N hN j O ρ (ε, z) hρ hz hzc)

end FalconerPacking
